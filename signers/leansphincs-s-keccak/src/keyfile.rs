//! The key file of a [`CachedKey`] (version 1): the key generated once, its node cache, and the secret seed.
//!
//! ```text
//! offset         length          field
//! 0              8               magic "LS-SKKEY"
//! 8              4               format version, u32 little endian: 1
//! 12             1               tier: 0 custom, 1 light, 2 standard, 3 full
//! 13             1               b, the kept subtree's height (0..=26)
//! 14             1               cache plan: 0 none, 1 top levels c..b, 2 level c only, 3 whole subtree
//! 15             1               c (0 for none and whole subtree)
//! 16             8               s, u64 little endian: the kept subtree holds leaves s 2^b .. (s + 1) 2^b
//! 24             8               cache budget in bytes, u64 little endian
//! 32             16              P
//! 48             16              root
//! 64             16              the kept subtree's root (level b)
//! 80             32              the seed S (secret)
//! 112            16 (26 - b)     surrogates, levels b..25
//! 112+16(26-b)   16 nodes        the cache: the plan's levels from the lowest, each level's nodes from the left
//! end - 32       32              keccak256 of every byte before it
//! ```
//!
//! `nodes` is the plan's node count ([`CachePlan::nodes`]): `2^(b-c+1) - 1` for top levels `c..b`, `2^(b-c)` for level
//! `c` only, `2^(b+1) - 1` for the whole subtree, 0 for none. The longest key file, a full key caching its whole tree,
//! is [`MAX_KEY_FILE_LEN`] bytes (about 2 GiB).
//!
//! The magic differs from the leanSphincs-23 key file's (`"LS23KKEY"`, same layout at `h = 25`): `lssk` refuses a
//! leanSphincs-23 key file as not a key file, before reading anything else, and `ls23k` refuses this one. The two
//! schemes derive their secrets alike, so one seed must never serve both (spec section 9).
//!
//! # Writing
//!
//! [`KeyFileWriter`] never leaves a partial key file at the key file's path. [`KeyFileWriter::create`] makes a uniquely
//! named temporary file beside it (`O_EXCL`, mode `0600`) before the keygen, so that a missing or read-only directory,
//! or an existing key file without `force`, fails before the work. [`KeyFileWriter::commit`] streams the key into it
//! ([`CachedKey::write_to`], which makes no copy of the cache), syncs it to disk, publishes it under the key file's name
//! and syncs the directory. Without `force` it publishes with a hard link, which fails if the name exists (so a key
//! file is never replaced, even by a concurrent writer), then removes the temporary name. With `force` it renames the
//! temporary file over the old key file, which stays whole until then. Any error removes the temporary file, and only
//! the one this writer created. A crash between its creation and the publish (a kill, a power loss) can leave it
//! behind: a hidden `.<name>.<pid>.<n>.tmp` beside the key file, mode `0600`, which holds the seed
//! ([`KeyFileWriter::stale_temporaries`] lists them). Nothing partial is ever at the key file's own path.
//!
//! # Loading, and what it proves
//!
//! Loading fails closed, in this order:
//!
//! 1. the path must be a regular file (a FIFO or a device is not opened) of at most [`MAX_KEY_FILE_LEN`] bytes, and it
//!    is read through a bound of the length it has when opened;
//! 2. the magic and the minimum length, then the checksum, before any other header field is trusted (a corrupt header
//!    reads as a checksum mismatch);
//! 3. the version, `b`, the plan and the exact length;
//! 4. bound to the seed: `P` must be the seed's, `s` the position `P` selects, and the surrogates the seed's;
//! 5. self-consistent: the plan must be the one the budget selects (and a preset tier must match `b` and the budget),
//!    every cached node the hash of its two children below (where they are cached), the cache's top level must hash up
//!    to the kept subtree's root, and that root must fold up through the surrogates to the stored root.
//!
//! That costs at most the cache's node count plus `2 (26 - b) + 1` keccak256 calls (one permutation each). The cache
//! is read straight into place, and checked without a second copy of it.
//!
//! Loading does not prove that the root, the kept subtree's root and the cache are the seed's: binding them to it would
//! cost a keygen. A file whose cache was edited consistently (some nodes changed, then every level above them, the kept
//! subtree's root and the root recomputed, and the file re-checksummed) loads and reports its own root. The checksum is
//! not a MAC, but it covers the seed: only someone who holds the seed, and so can sign anyway, can re-seal a file.
//! Signing re-checks what it recomputes, and [`sign_with_cache`] verifies every signature under the key's public key
//! before returning it, so a returned signature always verifies under the root the key file holds. Whether that root
//! is the registered key is for the caller to check: compare the key words that `lssk keygen`, `sign-key` and `info`
//! print with the registered `pkRoot`.

use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use tiny_keccak::{Hasher, Keccak};

use crate::*;

pub const KEY_FILE_MAGIC: [u8; 8] = *b"LS-SKKEY";
pub const KEY_FILE_VERSION: u32 = 1;
/// The bytes before the surrogates.
pub const KEY_FILE_HEADER_LEN: usize = 112;
pub const KEY_FILE_CHECKSUM_LEN: usize = 32;
/// The shortest key file: a full key with no cache.
const KEY_FILE_MIN_LEN: usize = KEY_FILE_HEADER_LEN + KEY_FILE_CHECKSUM_LEN;
/// The longest key file: a full key caching its whole tree, `2^27 - 1` nodes.
pub const MAX_KEY_FILE_LEN: usize = KEY_FILE_HEADER_LEN + N * ((1 << (H + 1)) - 1) + KEY_FILE_CHECKSUM_LEN;

const _: () = assert!(MAX_KEY_FILE_LEN == 2_147_483_776);

/// The length of the key file of a key keeping a subtree of height `b` with cache plan `plan`.
pub fn key_file_len(b: usize, plan: CachePlan) -> usize {
    KEY_FILE_HEADER_LEN + N * (H - b) + N * plan.nodes(b) as usize + KEY_FILE_CHECKSUM_LEN
}

/// Why a key file could not be written or loaded, or a cached key could not sign.
#[derive(Debug)]
pub enum KeyError {
    Io(io::Error),
    /// The key file exists and overwriting it was not asked for.
    Exists(PathBuf),
    /// The path is not a regular file (a FIFO, a device, a directory).
    NotARegularFile,
    /// The file is longer than any key file ([`MAX_KEY_FILE_LEN`]).
    TooLarge {
        actual: u64,
    },
    NotAKeyFile,
    UnsupportedVersion(u32),
    Length {
        expected: usize,
        actual: usize,
    },
    Checksum,
    /// A header field is out of range or disagrees with the others.
    Header(&'static str),
    /// `P` is not the seed's.
    PublicParam,
    /// `s` is not the position `P` selects.
    Position,
    /// The surrogate of this level is not the seed's.
    Surrogate {
        level: usize,
    },
    /// The node at this level and tree-wide index does not match its recomputation.
    Cache {
        level: usize,
        index: u64,
    },
    /// The kept subtree's root does not fold up to the stored root.
    Root,
    /// The signature does not verify under the key's public key: the key's root or cache is not its seed's.
    Signature,
}

/// I/O errors compare by kind.
impl PartialEq for KeyError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (KeyError::Io(a), KeyError::Io(b)) => a.kind() == b.kind(),
            (KeyError::Exists(a), KeyError::Exists(b)) => a == b,
            (KeyError::TooLarge { actual: a }, KeyError::TooLarge { actual: b }) => a == b,
            (KeyError::UnsupportedVersion(a), KeyError::UnsupportedVersion(b)) => a == b,
            (KeyError::Length { expected: a, actual: x }, KeyError::Length { expected: b, actual: y }) => {
                (a, x) == (b, y)
            }
            (KeyError::Header(a), KeyError::Header(b)) => a == b,
            (KeyError::Surrogate { level: a }, KeyError::Surrogate { level: b }) => a == b,
            (KeyError::Cache { level: a, index: x }, KeyError::Cache { level: b, index: y }) => (a, x) == (b, y),
            (a, b) => {
                std::mem::discriminant(a) == std::mem::discriminant(b)
                    && matches!(
                        a,
                        KeyError::NotARegularFile
                            | KeyError::NotAKeyFile
                            | KeyError::Checksum
                            | KeyError::PublicParam
                            | KeyError::Position
                            | KeyError::Root
                            | KeyError::Signature
                    )
            }
        }
    }
}

impl fmt::Display for KeyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KeyError::Io(err) => write!(f, "key file: {err}"),
            KeyError::Exists(path) => write!(f, "key file {} exists: refusing to overwrite it", path.display()),
            KeyError::NotARegularFile => {
                write!(f, "not a regular file (a key file is never a FIFO, a device or a directory)")
            }
            KeyError::TooLarge { actual } => {
                write!(
                    f,
                    "{actual} bytes is longer than any key file ({MAX_KEY_FILE_LEN} bytes at most): not a key file"
                )
            }
            KeyError::NotAKeyFile => write!(f, "not a leanSphincs-S-keccak key file (bad magic)"),
            KeyError::UnsupportedVersion(v) => {
                write!(f, "key file format version {v} is not supported (this signer reads version {KEY_FILE_VERSION})")
            }
            KeyError::Length { expected, actual } => {
                write!(f, "key file is {actual} bytes, its header says {expected}: truncated or extended")
            }
            KeyError::Checksum => write!(f, "key file checksum mismatch: the file is corrupt, truncated or extended"),
            KeyError::Header(what) => write!(f, "bad key file header: {what}"),
            KeyError::PublicParam => write!(f, "the key file's P is not its seed's: wrong seed or corrupt file"),
            KeyError::Position => write!(f, "the key file's subtree position s is not the one P selects"),
            KeyError::Surrogate { level } => write!(f, "the key file's surrogate at level {level} is not its seed's"),
            KeyError::Cache { level, index } => {
                write!(f, "node {index} at level {level} does not match its recomputation: the node cache is corrupt")
            }
            KeyError::Root => write!(f, "the key file's root is not the one its cache and surrogates reach"),
            KeyError::Signature => write!(
                f,
                "refusing to output a signature that does not verify under the key file's public key: the file's root \
                 or node cache is not its seed's"
            ),
        }
    }
}

impl std::error::Error for KeyError {}

impl From<io::Error> for KeyError {
    fn from(err: io::Error) -> Self {
        KeyError::Io(err)
    }
}

/// Why a key file that loads should not be kept as it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeyFileWarning {
    /// Group or others have some access to it (`mode`: its permission bits), and it holds the seed.
    Accessible { mode: u32 },
    /// Another user owns it.
    Owner { owner: u32, user: u32 },
}

impl fmt::Display for KeyFileWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KeyFileWarning::Accessible { mode } => {
                write!(f, "group or others can access it (mode {mode:04o}) and it holds the secret seed: chmod 600 it")
            }
            KeyFileWarning::Owner { owner, user } => {
                write!(f, "it is owned by uid {owner}, not by this user (uid {user})")
            }
        }
    }
}

fn tier_code(tier: Tier) -> u8 {
    match tier {
        Tier::Custom { .. } => 0,
        Tier::Light => 1,
        Tier::Standard => 2,
        Tier::Full => 3,
    }
}

fn plan_code(plan: CachePlan) -> (u8, u8) {
    match plan {
        CachePlan::None => (0, 0),
        CachePlan::Top(c) => (1, c as u8),
        CachePlan::Level(c) => (2, c as u8),
        CachePlan::Whole => (3, 0),
    }
}

fn plan_of_code(code: u8, c: u8) -> Option<CachePlan> {
    match (code, c as usize) {
        (0, 0) => Some(CachePlan::None),
        (1, c) => Some(CachePlan::Top(c)),
        (2, c) => Some(CachePlan::Level(c)),
        (3, 0) => Some(CachePlan::Whole),
        _ => None,
    }
}

fn finish(hasher: Keccak) -> [u8; 32] {
    let mut out = [0u8; 32];
    hasher.finalize(&mut out);
    out
}

/// A writer that also absorbs what it writes into the checksum.
struct Checksummed<W> {
    inner: W,
    hasher: Keccak,
}

impl<W: Write> Write for Checksummed<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let written = self.inner.write(buf)?;
        self.hasher.update(&buf[..written]);
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

/// Absorbs bytes into the checksum and nowhere else.
struct Absorb<'a>(&'a mut Keccak);

impl Write for Absorb<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.update(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `b` and the plan the header gives, if its version is this one's and they give a key file of `len` bytes.
fn layout(header: &[u8; KEY_FILE_HEADER_LEN], len: usize) -> Result<(usize, CachePlan), KeyError> {
    let version = u32::from_le_bytes(header[8..12].try_into().unwrap());
    if version != KEY_FILE_VERSION {
        return Err(KeyError::UnsupportedVersion(version));
    }
    let b = header[13] as usize;
    if b > H {
        return Err(KeyError::Header("b is above 26"));
    }
    let plan = plan_of_code(header[14], header[15])
        .filter(|plan| plan.fits(b))
        .ok_or(KeyError::Header("the cache plan does not exist for this b"))?;
    let expected = key_file_len(b, plan);
    if len != expected {
        return Err(KeyError::Length { expected, actual: len });
    }
    Ok((b, plan))
}

/// Reads a key file of `len` bytes from `r`, which must hold that many, and checks it (module doc).
fn read_key(r: &mut impl Read, len: usize) -> Result<CachedKey, KeyError> {
    let mut header = [0u8; KEY_FILE_HEADER_LEN];
    let head = len.min(KEY_FILE_HEADER_LEN);
    r.read_exact(&mut header[..head])?;
    if head >= KEY_FILE_MAGIC.len() && header[..KEY_FILE_MAGIC.len()] != KEY_FILE_MAGIC {
        return Err(KeyError::NotAKeyFile);
    }
    if len < KEY_FILE_MIN_LEN {
        return Err(KeyError::Length { expected: KEY_FILE_MIN_LEN, actual: len });
    }
    if len > MAX_KEY_FILE_LEN {
        return Err(KeyError::TooLarge { actual: len as u64 });
    }
    // The checksum decides before any header field is trusted. Where the header gives a layout of this length, the
    // surrogates and the cache are read straight into place as they are hashed; otherwise the body is only hashed, so
    // that a corrupt header reads as a checksum mismatch.
    let mut hasher = Keccak::v256();
    hasher.update(&header);
    let layout = layout(&header, len);
    let body = match layout {
        Ok((b, plan)) => {
            let mut read_nodes = |count: usize| -> io::Result<Vec<Digest>> {
                let mut nodes = vec![[0u8; N]; count];
                r.read_exact(nodes.as_flattened_mut())?;
                hasher.update(nodes.as_flattened());
                Ok(nodes)
            };
            let surrogates = read_nodes(H - b)?;
            let cache = plan.levels(b).map(|level| read_nodes(1 << (b - level))).collect::<io::Result<Vec<_>>>()?;
            Some((surrogates, cache))
        }
        Err(_) => {
            let rest = (len - KEY_FILE_MIN_LEN) as u64;
            if io::copy(&mut r.by_ref().take(rest), &mut Absorb(&mut hasher))? != rest {
                return Err(io::Error::from(io::ErrorKind::UnexpectedEof).into());
            }
            None
        }
    };
    let mut checksum = [0u8; KEY_FILE_CHECKSUM_LEN];
    r.read_exact(&mut checksum)?;
    if finish(hasher) != checksum {
        return Err(KeyError::Checksum);
    }
    let (b, plan) = layout?;
    let (surrogates, cache) = body.expect("read with its layout");

    let word = |at: usize| u64::from_le_bytes(header[at..at + 8].try_into().unwrap());
    let (s, cache_bytes) = (word(16), word(24));
    let tier = match header[12] {
        0 => Tier::Custom { b, cache_bytes },
        code => {
            Tier::PRESETS.into_iter().find(|&tier| tier_code(tier) == code).ok_or(KeyError::Header("unknown tier"))?
        }
    };
    if (tier.b(), tier.cache_bytes()) != (b, cache_bytes) {
        return Err(KeyError::Header("the tier preset does not match b and the cache budget"));
    }
    if tier.plan() != plan {
        return Err(KeyError::Header("the cache plan is not the one the budget selects"));
    }
    let digest = |at: usize| -> Digest { header[at..at + N].try_into().unwrap() };
    let (public_param, root, subtree_root) = (digest(32), digest(48), digest(64));
    let master: MasterSecret = header[80..80 + MASTER_SECRET_LEN].try_into().unwrap();
    let key = CachedKey { tier, b, s, plan, public_param, root, subtree_root, surrogates, master, cache };
    key.check()?;
    Ok(key)
}

/// A key file must be a regular file no longer than [`MAX_KEY_FILE_LEN`].
fn check_regular(meta: &fs::Metadata) -> Result<(), KeyError> {
    if !meta.is_file() {
        return Err(KeyError::NotARegularFile);
    }
    if meta.len() > MAX_KEY_FILE_LEN as u64 {
        return Err(KeyError::TooLarge { actual: meta.len() });
    }
    Ok(())
}

fn changed_while_read() -> KeyError {
    KeyError::Io(io::Error::other("the file changed while it was read"))
}

#[cfg(unix)]
fn effective_uid() -> u32 {
    unsafe extern "C" {
        safe fn geteuid() -> u32;
    }
    geteuid()
}

/// The [`KeyFileWarning`]s of a key file's metadata.
#[cfg(unix)]
fn permission_warnings(meta: &fs::Metadata) -> Vec<KeyFileWarning> {
    use std::os::unix::fs::MetadataExt;
    let mut warnings = Vec::new();
    let mode = meta.mode() & 0o777;
    if mode & 0o077 != 0 {
        warnings.push(KeyFileWarning::Accessible { mode });
    }
    let (owner, user) = (meta.uid(), effective_uid());
    if owner != user {
        warnings.push(KeyFileWarning::Owner { owner, user });
    }
    warnings
}

#[cfg(not(unix))]
fn permission_warnings(_: &fs::Metadata) -> Vec<KeyFileWarning> {
    Vec::new()
}

impl CachedKey {
    /// Streams the key file (module doc) into `out`, computing the checksum as it goes: no copy of the cache is made.
    pub fn write_to(&self, out: &mut impl Write) -> io::Result<()> {
        let mut sum = Checksummed { inner: &mut *out, hasher: Keccak::v256() };
        sum.write_all(&KEY_FILE_MAGIC)?;
        sum.write_all(&KEY_FILE_VERSION.to_le_bytes())?;
        let (plan, c) = plan_code(self.plan);
        sum.write_all(&[tier_code(self.tier), self.b as u8, plan, c])?;
        sum.write_all(&self.s.to_le_bytes())?;
        sum.write_all(&self.tier.cache_bytes().to_le_bytes())?;
        sum.write_all(&self.public_param)?;
        sum.write_all(&self.root)?;
        sum.write_all(&self.subtree_root)?;
        sum.write_all(&self.master)?;
        sum.write_all(self.surrogates.as_flattened())?;
        for level in &self.cache {
            sum.write_all(level.as_flattened())?;
        }
        let checksum = finish(sum.hasher);
        out.write_all(&checksum)
    }

    /// The key file (module doc), in memory.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(key_file_len(self.b, self.plan));
        self.write_to(&mut out).expect("a Vec takes every write");
        debug_assert_eq!(out.len(), key_file_len(self.b, self.plan));
        out
    }

    /// Reads a key file and checks it (module doc): `Err` on any mismatch.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, KeyError> {
        read_key(&mut &bytes[..], bytes.len())
    }

    /// Checks the key against its seed and its cache against its root (module doc).
    fn check(&self) -> Result<(), KeyError> {
        let (pp, b) = (&self.public_param, self.b);
        if derive_public_param(&self.master) != *pp {
            return Err(KeyError::PublicParam);
        }
        if subtree_position(pp, b) != self.s {
            return Err(KeyError::Position);
        }
        let surrogates = derive_surrogates(pp, &self.master, b);
        if let Some(t) = (0..H - b).find(|&t| surrogates[t] != self.surrogates[t]) {
            return Err(KeyError::Surrogate { level: b + t });
        }
        let start = self.plan.levels(b).start;
        if let Some(lowest) = self.cache.first() {
            // Hash the lowest cached level up to the kept subtree's root. A cached level is compared node by node with
            // the hashes of the level below; only the levels above a `level c only` cache are computed and kept, half
            // the cache at most.
            let mut computed: Vec<Digest>;
            let mut below: &[Digest] = lowest;
            for level in start + 1..=b {
                let first = self.s << (b - level);
                let node = |j: usize| xmss_node(pp, level, first + j as u64, &below[2 * j], &below[2 * j + 1]);
                if let Some(cached) = self.cache.get(level - start) {
                    if let Some(j) = (0..cached.len()).find(|&j| node(j) != cached[j]) {
                        return Err(KeyError::Cache { level, index: first + j as u64 });
                    }
                    below = cached;
                } else {
                    computed = (0..below.len() / 2).map(node).collect();
                    below = &computed;
                }
            }
            if below[0] != self.subtree_root {
                return Err(KeyError::Cache { level: b, index: self.s });
            }
        }
        if fold_surrogates(pp, b, self.s, self.subtree_root, &self.surrogates) != self.root {
            return Err(KeyError::Root);
        }
        Ok(())
    }

    /// Writes the key file at `path` with mode `0600` ([`KeyFileWriter`]): an existing file is an error unless
    /// `force`, in which case the new file replaces it whole.
    pub fn write(&self, path: &Path, force: bool) -> Result<(), KeyError> {
        KeyFileWriter::create(path, force)?.commit(self)
    }

    /// Reads and checks the key file at `path` ([`load_with_warnings`](Self::load_with_warnings), the warnings
    /// dropped).
    pub fn load(path: &Path) -> Result<Self, KeyError> {
        Self::load_with_warnings(path).map(|(key, _)| key)
    }

    /// Reads and checks the key file at `path` (module doc), and says if group or others can access it or another
    /// user owns it (Unix).
    pub fn load_with_warnings(path: &Path) -> Result<(Self, Vec<KeyFileWarning>), KeyError> {
        // Stat before opening: opening a FIFO would wait for a writer.
        check_regular(&fs::metadata(path)?)?;
        let file = fs::File::open(path)?;
        // The file opened may not be the one the stat saw.
        let meta = file.metadata()?;
        check_regular(&meta)?;
        let warnings = permission_warnings(&meta);
        let len = meta.len() as usize;
        // Never more than the length it had when opened, and one byte more to tell that it grew.
        let mut reader = BufReader::new(file.take(len as u64 + 1));
        let key = read_key(&mut reader, len).map_err(|err| match err {
            KeyError::Io(err) if err.kind() == io::ErrorKind::UnexpectedEof => changed_while_read(),
            err => err,
        })?;
        if reader.read(&mut [0u8; 1])? != 0 {
            return Err(changed_while_read());
        }
        Ok((key, warnings))
    }
}

/// Names of the temporary files of this process: with the process id, unique among live processes.
static NEXT_TEMPORARY: AtomicU64 = AtomicU64::new(0);

/// The directory a path names a file in.
fn parent_dir(path: &Path) -> &Path {
    match path.parent() {
        Some(dir) if !dir.as_os_str().is_empty() => dir,
        _ => Path::new("."),
    }
}

/// Writes one key file without ever leaving a partial one at its path (module doc): [`create`](Self::create) before
/// the keygen, [`commit`](Self::commit) after it. Dropping the writer without committing removes its temporary file.
pub struct KeyFileWriter {
    path: PathBuf,
    force: bool,
    /// The temporary file, while this writer owns it.
    tmp: Option<PathBuf>,
    file: Option<fs::File>,
    /// Test only: the temporary file takes this many bytes, then every write fails.
    #[cfg(test)]
    fail_after: Option<usize>,
}

impl KeyFileWriter {
    /// Checks `path` and creates the temporary file beside it: `Err` if `path` names no file, exists (unless `force`)
    /// or is a directory, or if its directory is missing or not writable.
    pub fn create(path: &Path, force: bool) -> Result<Self, KeyError> {
        let invalid = |what: &str| KeyError::Io(io::Error::new(io::ErrorKind::InvalidInput, what.to_string()));
        let name = path.file_name().ok_or_else(|| invalid("the key file path names no file"))?;
        if path.as_os_str().as_encoded_bytes().ends_with(b"/") {
            return Err(invalid("the key file path ends with a slash"));
        }
        match fs::symlink_metadata(path) {
            Ok(_) if !force => return Err(KeyError::Exists(path.to_path_buf())),
            Ok(meta) if meta.is_dir() => {
                return Err(io::Error::new(io::ErrorKind::IsADirectory, "the key file path is a directory").into());
            }
            Ok(_) => {}
            Err(err) if err.kind() == io::ErrorKind::NotFound => {}
            Err(err) => return Err(err.into()),
        }
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        std::os::unix::fs::OpenOptionsExt::mode(&mut options, 0o600);
        for _ in 0..1000 {
            let mut tmp_name = OsString::from(".");
            tmp_name.push(name);
            tmp_name.push(format!(".{}.{}.tmp", std::process::id(), NEXT_TEMPORARY.fetch_add(1, Ordering::Relaxed)));
            let tmp = path.with_file_name(tmp_name);
            match options.open(&tmp) {
                Ok(file) => {
                    return Ok(Self {
                        path: path.to_path_buf(),
                        force,
                        tmp: Some(tmp),
                        file: Some(file),
                        #[cfg(test)]
                        fail_after: None,
                    });
                }
                // Left by a crashed process that had this process id: try the next name.
                Err(err) if err.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(err) => return Err(err.into()),
            }
        }
        Err(io::Error::new(io::ErrorKind::AlreadyExists, "no free temporary file name beside the key file").into())
    }

    /// The temporary file (mode `0600`) this writer owns until it commits.
    pub fn temporary_path(&self) -> Option<&Path> {
        self.tmp.as_deref()
    }

    /// Temporary key files beside the key file that this writer did not create: what a crash while writing the same
    /// key file left. They hold a seed.
    pub fn stale_temporaries(&self) -> Vec<PathBuf> {
        let Some(name) = self.path.file_name() else { return Vec::new() };
        let mut prefix = OsString::from(".");
        prefix.push(name);
        prefix.push(".");
        let ours = self.tmp.as_deref().and_then(Path::file_name);
        let Ok(entries) = fs::read_dir(parent_dir(&self.path)) else { return Vec::new() };
        let mut stale: Vec<PathBuf> = entries
            .filter_map(Result::ok)
            .filter(|entry| {
                let file_name = entry.file_name();
                let bytes = file_name.as_encoded_bytes();
                bytes.starts_with(prefix.as_encoded_bytes())
                    && bytes.ends_with(b".tmp")
                    && Some(file_name.as_os_str()) != ours
            })
            .map(|entry| self.path.with_file_name(entry.file_name()))
            .collect();
        stale.sort();
        stale
    }

    /// Where the key file's bytes go.
    fn sink<'a>(&self, file: &'a fs::File) -> Box<dyn Write + 'a> {
        #[cfg(test)]
        if let Some(left) = self.fail_after {
            return Box::new(tests::FailAfter { inner: file, left });
        }
        Box::new(file)
    }

    /// Streams `key` into the temporary file, syncs it, publishes it at the key file's path (a hard link without
    /// `force`, a rename with it) and syncs the directory. On any error the temporary file is removed, and without
    /// `force` an existing file at the path (one created since [`create`](Self::create)) is left alone.
    pub fn commit(mut self, key: &CachedKey) -> Result<(), KeyError> {
        let file = self.file.take().expect("a writer commits once");
        {
            let mut out = BufWriter::new(self.sink(&file));
            key.write_to(&mut out)?;
            out.flush()?;
        }
        file.sync_all()?;
        drop(file);
        let tmp = self.tmp.clone().expect("the temporary file");
        if self.force {
            fs::rename(&tmp, &self.path)?;
            self.tmp = None;
        } else {
            match fs::hard_link(&tmp, &self.path) {
                Ok(()) => {}
                Err(err) if err.kind() == io::ErrorKind::AlreadyExists => {
                    return Err(KeyError::Exists(self.path.clone()));
                }
                Err(err) => {
                    let hint = "(on a filesystem without hard links, write with force: it publishes by rename)";
                    return Err(io::Error::new(err.kind(), format!("publishing with a hard link: {err} {hint}")).into());
                }
            }
            fs::remove_file(&tmp)?;
            self.tmp = None;
        }
        #[cfg(unix)]
        fs::File::open(parent_dir(&self.path))?.sync_all()?;
        Ok(())
    }
}

impl Drop for KeyFileWriter {
    fn drop(&mut self) {
        drop(self.file.take());
        if let Some(tmp) = self.tmp.take() {
            let _ = fs::remove_file(tmp);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(x: u8) -> MasterSecret {
        std::array::from_fn(|i| x.wrapping_mul(53).wrapping_add(i as u8))
    }

    /// A writer that takes `left` bytes, then fails every write: a full disk.
    pub(super) struct FailAfter<W> {
        pub(super) inner: W,
        pub(super) left: usize,
    }

    impl<W: Write> Write for FailAfter<W> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            if self.left == 0 {
                return Err(io::Error::new(io::ErrorKind::StorageFull, "injected failure"));
            }
            let written = self.inner.write(&buf[..buf.len().min(self.left)])?;
            self.left -= written;
            Ok(written)
        }

        fn flush(&mut self) -> io::Result<()> {
            self.inner.flush()
        }
    }

    /// A fresh, empty directory for one test.
    fn test_dir(what: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("lssk-keyfile-{what}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn entries(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> =
            fs::read_dir(dir).unwrap().map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned()).collect();
        names.sort();
        names
    }

    /// Small keys with every kind of plan: none, top levels, level only, whole subtree.
    fn small_keys() -> Vec<CachedKey> {
        [(5usize, 0u64), (5, 7), (6, 8), (4, 31), (0, 1), (2, 3)]
            .into_iter()
            .map(|(b, nodes)| keygen_cached(&seed(b as u8), Tier::Custom { b, cache_bytes: N as u64 * nodes }, 4))
            .collect()
    }

    #[test]
    fn plans_of_the_small_keys() {
        let plans: Vec<CachePlan> = small_keys().iter().map(|key| key.plan).collect();
        assert_eq!(
            plans,
            [
                CachePlan::None,
                CachePlan::Top(3),
                CachePlan::Level(3),
                CachePlan::Whole,
                CachePlan::Whole,
                CachePlan::Top(1)
            ]
        );
    }

    #[test]
    fn roundtrip() {
        assert_eq!(key_file_len(H, CachePlan::Whole), MAX_KEY_FILE_LEN);
        assert_eq!(key_file_len(H, CachePlan::None), KEY_FILE_MIN_LEN);
        for key in small_keys() {
            let bytes = key.to_bytes();
            assert_eq!(bytes.len(), key_file_len(key.b, key.plan));
            assert_eq!(bytes[..8], *b"LS-SKKEY");
            assert_eq!(bytes[8..12], [1, 0, 0, 0]);
            assert_eq!(bytes[80..112], key.master, "the seed");
            assert_eq!(bytes[bytes.len() - 32..], keccak256(&bytes[..bytes.len() - 32]));
            assert_eq!(CachedKey::from_bytes(&bytes).unwrap(), key);
        }
        let key = keygen_cached(&seed(1), Tier::Light, 8);
        let bytes = key.to_bytes();
        assert_eq!(bytes.len(), 112 + 16 * 13 + 16 * 1024 + 32);
        assert_eq!(bytes[12..16], [1, 13, 2, 3], "light, b = 13, level 3 only");
        assert_eq!(bytes[24..32], 16384u64.to_le_bytes());
        assert_eq!(CachedKey::from_bytes(&bytes).unwrap(), key);
    }

    /// Every flipped bit, truncation or extension is rejected.
    #[test]
    fn every_corruption_is_rejected() {
        for key in small_keys() {
            let bytes = key.to_bytes();
            for i in 0..bytes.len() {
                for bit in 0..8 {
                    let mut bad = bytes.clone();
                    bad[i] ^= 1 << bit;
                    assert!(CachedKey::from_bytes(&bad).is_err(), "byte {i} bit {bit}, {:?}", key.plan);
                }
            }
            for len in 0..bytes.len() {
                assert!(CachedKey::from_bytes(&bytes[..len]).is_err(), "truncated to {len}");
            }
            for extra in [1, 16, 32] {
                let mut long = bytes.clone();
                long.resize(bytes.len() + extra, 0);
                assert_eq!(CachedKey::from_bytes(&long).unwrap_err(), KeyError::Checksum, "{extra} more bytes");
            }
        }
    }

    /// The checksum is checked right after the magic and the length bounds, before the header is trusted: a flipped
    /// bit anywhere past the magic, the version, `b` and the plan included, reads as a checksum mismatch. (It used to
    /// read as an unsupported version, a truncated file or a bad header.)
    #[test]
    fn the_checksum_is_checked_before_the_header() {
        for key in small_keys() {
            let bytes = key.to_bytes();
            for i in 8..bytes.len() {
                for bit in 0..8 {
                    let mut bad = bytes.clone();
                    bad[i] ^= 1 << bit;
                    assert_eq!(CachedKey::from_bytes(&bad).unwrap_err(), KeyError::Checksum, "byte {i} bit {bit}");
                }
            }
            for i in 0..8 {
                let mut bad = bytes.clone();
                bad[i] ^= 0x10;
                assert_eq!(CachedKey::from_bytes(&bad).unwrap_err(), KeyError::NotAKeyFile, "byte {i}");
            }
        }
    }

    /// A leanSphincs-23 key file (`ls23k`'s magic `"LS23KKEY"`, version 1, the same header at `h = 25`) is not a key
    /// file here, whatever follows the magic: a genuine one's layout, a re-checksummed copy of one of ours, or a
    /// truncated one. The magic is checked before the length or the checksum.
    #[test]
    fn a_leansphincs23_key_file_is_refused() {
        // The shape of an ls23k Light key file: b = 13, level 3 only, 12 surrogates, 1024 nodes.
        let mut ls23k_light = vec![0u8; 112 + 16 * 12 + 16 * 1024 + 32];
        ls23k_light[..8].copy_from_slice(b"LS23KKEY");
        ls23k_light[8..16].copy_from_slice(&[1, 0, 0, 0, 1, 13, 2, 3]);
        let n = ls23k_light.len();
        let checksum = keccak256(&ls23k_light[..n - 32]);
        ls23k_light[n - 32..].copy_from_slice(&checksum);
        assert_eq!(CachedKey::from_bytes(&ls23k_light).unwrap_err(), KeyError::NotAKeyFile);
        for key in small_keys() {
            let mut bytes = key.to_bytes();
            bytes[..8].copy_from_slice(b"LS23KKEY");
            let n = bytes.len();
            let checksum = keccak256(&bytes[..n - 32]);
            bytes[n - 32..].copy_from_slice(&checksum);
            assert_eq!(CachedKey::from_bytes(&bytes).unwrap_err(), KeyError::NotAKeyFile, "{:?}", key.plan);
            assert_eq!(CachedKey::from_bytes(&bytes[..20]).unwrap_err(), KeyError::NotAKeyFile);
        }
        let err = KeyError::NotAKeyFile.to_string();
        assert!(err.contains("leanSphincs-S-keccak"), "{err}");
    }

    /// An edit of the key file's bytes before the checksum.
    type Edit = fn(&mut Vec<u8>);

    /// Single-field edits that keep the checksum valid (it is not a MAC) are caught by the checks behind it. (Not every
    /// consistent edit is: a cache edited consistently, with every level above it, the kept subtree's root and the root
    /// recomputed, loads; see the module doc, and `returned_signatures_verify_under_the_keys_root` in `tiers`.)
    #[test]
    fn consistent_checksum_edits_are_rejected() {
        let resealed = |key: &CachedKey, edit: &dyn Fn(&mut Vec<u8>)| {
            let mut bytes = key.to_bytes();
            bytes.truncate(bytes.len() - 32);
            edit(&mut bytes);
            let checksum = keccak256(&bytes);
            bytes.extend_from_slice(&checksum);
            CachedKey::from_bytes(&bytes)
        };
        for key in small_keys() {
            let (b, nodes) = (key.b, key.cache_nodes() as usize);
            let cache_at = 112 + 16 * (H - b);
            assert_eq!(resealed(&key, &|_| {}).unwrap(), key);
            let preset = "the tier preset does not match b and the cache budget";
            let cases: [(&str, Edit, KeyError); 9] = [
                ("version", |f| f[8] = 2, KeyError::UnsupportedVersion(2)),
                ("magic", |f| f[0] ^= 0x20, KeyError::NotAKeyFile),
                ("seed", |f| f[80 + 31] ^= 1, KeyError::PublicParam),
                ("P", |f| f[32] ^= 0x80, KeyError::PublicParam),
                ("root", |f| f[48 + 15] ^= 1, KeyError::Root),
                ("tier", |f| f[12] = 9, KeyError::Header("unknown tier")),
                ("tier preset", |f| f[12] = 1, KeyError::Header(preset)),
                ("b", |f| f[13] = 27, KeyError::Header("b is above 26")),
                ("plan code", |f| f[14] = 4, KeyError::Header("the cache plan does not exist for this b")),
            ];
            for (what, edit, expected) in cases {
                assert_eq!(resealed(&key, &edit).unwrap_err(), expected, "{what}, {:?}", key.plan);
            }
            if b < H {
                let err = resealed(&key, &|f| f[16] ^= 1).unwrap_err();
                assert_eq!(err, KeyError::Position, "{:?}", key.plan);
                let err = resealed(&key, &|f| f[112 + 16 * (H - b - 1)] ^= 4).unwrap_err();
                assert_eq!(err, KeyError::Surrogate { level: H - 1 });
            }
            // The budget can only move within the plan it selects.
            let budget = |bytes: u64| move |f: &mut Vec<u8>| f[24..32].copy_from_slice(&bytes.to_le_bytes());
            let more = key.tier.cache_bytes() + 15 - key.tier.cache_bytes() % 16;
            assert_eq!(resealed(&key, &budget(more)).unwrap().plan, key.plan);
            if key.plan != CachePlan::Whole {
                let err = resealed(&key, &budget(u64::MAX)).unwrap_err();
                assert_eq!(err, KeyError::Header("the cache plan is not the one the budget selects"));
            }
            // The first node of the lowest cached level, caught at the next cached level (or at the kept subtree's root);
            // the last node of the highest.
            if nodes > 0 {
                let above = match key.plan {
                    CachePlan::Level(_) => b,
                    plan => (plan.levels(b).start + 1).min(b),
                };
                let err = resealed(&key, &|f| f[cache_at + 5] ^= 1).unwrap_err();
                assert_eq!(err, KeyError::Cache { level: above, index: key.s << (b - above) }, "{:?}", key.plan);
                let err = resealed(&key, &|f| f[cache_at + 16 * nodes - 1] ^= 1).unwrap_err();
                assert_eq!(err, KeyError::Cache { level: b, index: key.s }, "{:?}", key.plan);
            }
            let err = resealed(&key, &|f| f[64] ^= 1).unwrap_err();
            let expected = if nodes == 0 { KeyError::Root } else { KeyError::Cache { level: b, index: key.s } };
            assert_eq!(err, expected, "the kept subtree's root, {:?}", key.plan);
        }
    }

    #[test]
    fn write_refuses_to_overwrite_and_is_private() {
        let dir = test_dir("write");
        let path = dir.join("key.lssk");
        let first = keygen_cached(&seed(1), Tier::Custom { b: 3, cache_bytes: 0 }, 2);
        let second = keygen_cached(&seed(2), Tier::Custom { b: 4, cache_bytes: 1 << 10 }, 2);
        first.write(&path, false).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(fs::metadata(&path).unwrap().permissions().mode() & 0o777, 0o600);
        }
        assert_eq!(second.write(&path, false).unwrap_err(), KeyError::Exists(path.clone()));
        assert_eq!(CachedKey::load(&path).unwrap(), first, "the refused write left the file alone");
        second.write(&path, true).unwrap();
        assert_eq!(CachedKey::load(&path).unwrap(), second);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(fs::metadata(&path).unwrap().permissions().mode() & 0o777, 0o600);
        }
        assert_eq!(entries(&dir), ["key.lssk"], "no temporary file is left");
        fs::write(&path, b"LS-SKKEY\x01\0\0\0").unwrap();
        assert!(matches!(CachedKey::load(&path), Err(KeyError::Length { .. })));
        assert!(matches!(CachedKey::load(&dir.join("missing")), Err(KeyError::Io(_))));
        fs::remove_dir_all(&dir).unwrap();
    }

    /// A write that fails part way (a full disk, injected after every few bytes, the seed's included) leaves no file
    /// at the key file's path and no temporary file: nothing that holds the seed. With `force` the old key file stays
    /// whole. (The write used to go straight to the key file's path, where a crash left a partial file holding the
    /// seed; now only the temporary file is ever partial, and every error removes it.)
    #[test]
    fn a_failed_write_leaves_no_partial_file() {
        let dir = test_dir("partial");
        let path = dir.join("k");
        let (old, key) = (keygen_cached(&seed(3), Tier::Custom { b: 2, cache_bytes: 0 }, 2), small_keys().remove(3));
        let len = key_file_len(key.b, key.plan);
        for force in [false, true] {
            if force {
                old.write(&path, false).unwrap();
            }
            for fail_after in [0, 50, 100, 112, 500, len - 32, len - 1] {
                let mut writer = KeyFileWriter::create(&path, force).unwrap();
                let tmp = writer.temporary_path().unwrap().to_path_buf();
                assert!(
                    tmp.exists() && tmp.parent() == path.parent(),
                    "the temporary file is made beside the key file"
                );
                writer.fail_after = Some(fail_after);
                let err = writer.commit(&key).unwrap_err();
                assert!(matches!(&err, KeyError::Io(e) if e.kind() == io::ErrorKind::StorageFull), "{err}");
                assert!(!tmp.exists(), "{fail_after}: the temporary file is removed");
                if force {
                    assert_eq!(entries(&dir), ["k"], "{fail_after}");
                    assert_eq!(CachedKey::load(&path).unwrap(), old, "{fail_after}: the old key file is whole");
                } else {
                    assert!(entries(&dir).is_empty(), "{fail_after}: nothing at the key file's path");
                }
            }
            // A writer dropped without committing (the keygen panicked, say) removes its temporary file too.
            drop(KeyFileWriter::create(&path, force).unwrap());
            assert_eq!(entries(&dir).len(), force as usize);
        }
        // The same writer with room to finish writes the key file.
        fs::remove_file(&path).unwrap();
        let mut writer = KeyFileWriter::create(&path, false).unwrap();
        writer.fail_after = Some(len);
        writer.commit(&key).unwrap();
        assert_eq!(CachedKey::load(&path).unwrap(), key);
        assert_eq!(entries(&dir), ["k"]);
        fs::remove_dir_all(&dir).unwrap();
    }

    /// The path is checked when the writer is created, before the keygen: an existing key file (without `force`), a
    /// directory, a missing directory, a path that names no file. Nothing is created then.
    #[test]
    fn the_path_is_checked_before_the_keygen() {
        let dir = test_dir("early");
        let path = dir.join("k");
        fs::write(&path, b"someone's file").unwrap();
        assert_eq!(KeyFileWriter::create(&path, false).err(), Some(KeyError::Exists(path.clone())));
        fs::create_dir(dir.join("sub")).unwrap();
        let is_a_dir = KeyFileWriter::create(&dir.join("sub"), true).err().unwrap();
        assert!(matches!(&is_a_dir, KeyError::Io(e) if e.kind() == io::ErrorKind::IsADirectory), "{is_a_dir}");
        assert_eq!(KeyFileWriter::create(&dir.join("sub"), false).err(), Some(KeyError::Exists(dir.join("sub"))));
        let missing = KeyFileWriter::create(&dir.join("no/k"), false).err().unwrap();
        assert!(matches!(&missing, KeyError::Io(e) if e.kind() == io::ErrorKind::NotFound), "{missing}");
        for bad in [dir.join(".."), PathBuf::from(format!("{}/k/", dir.display()))] {
            let err = KeyFileWriter::create(&bad, true).err().unwrap();
            assert!(matches!(&err, KeyError::Io(e) if e.kind() == io::ErrorKind::InvalidInput), "{err}");
        }
        assert_eq!(entries(&dir), ["k", "sub"]);
        assert_eq!(fs::read(&path).unwrap(), b"someone's file");
        fs::remove_dir_all(&dir).unwrap();
    }

    /// A key file created at the path after the writer was (a concurrent keygen) is never replaced without `force`,
    /// and the losing writer removes only its own temporary file. Two writers of one process get distinct temporary
    /// files, so neither removes the other's. A temporary file a crash left behind is listed, not removed.
    #[test]
    fn concurrent_writers_never_clobber() {
        let dir = test_dir("race");
        let path = dir.join("k");
        let (a, b) = (small_keys().remove(0), small_keys().remove(1));
        let first = KeyFileWriter::create(&path, false).unwrap();
        let second = KeyFileWriter::create(&path, false).unwrap();
        assert_ne!(first.temporary_path(), second.temporary_path());
        second.commit(&b).unwrap();
        assert_eq!(first.commit(&a).unwrap_err(), KeyError::Exists(path.clone()));
        assert_eq!(CachedKey::load(&path).unwrap(), b);
        assert_eq!(entries(&dir), ["k"]);
        let first = KeyFileWriter::create(&path, true).unwrap();
        let second = KeyFileWriter::create(&path, true).unwrap();
        first.commit(&a).unwrap();
        second.commit(&b).unwrap();
        assert_eq!(CachedKey::load(&path).unwrap(), b);
        assert_eq!(entries(&dir), ["k"]);
        // What a crash leaves.
        let crashed = KeyFileWriter::create(&path, true).unwrap();
        let left = crashed.temporary_path().unwrap().to_path_buf();
        std::mem::forget(crashed);
        let writer = KeyFileWriter::create(&path, true).unwrap();
        assert_eq!(writer.stale_temporaries(), std::slice::from_ref(&left));
        writer.commit(&a).unwrap();
        assert!(left.exists());
        fs::remove_dir_all(&dir).unwrap();
    }

    /// Loading opens only a regular file no longer than any key file, and checks the length before reading: a FIFO
    /// (which used to block forever), a device, a directory, and a file longer than `MAX_KEY_FILE_LEN` (which used to
    /// be read whole before its magic was looked at) are refused at once.
    #[test]
    fn load_refuses_what_is_not_a_key_file_before_reading_it() {
        let dir = test_dir("load");
        let refused = |path: PathBuf| {
            let (tx, rx) = std::sync::mpsc::channel();
            std::thread::spawn(move || tx.send(CachedKey::load(&path).map(|_| ())).unwrap());
            rx.recv_timeout(std::time::Duration::from_secs(20)).expect("load returned")
        };
        assert_eq!(refused(dir.clone()), Err(KeyError::NotARegularFile));
        #[cfg(unix)]
        {
            if Path::new("/dev/zero").exists() {
                assert_eq!(refused("/dev/zero".into()), Err(KeyError::NotARegularFile));
            }
            let fifo = dir.join("fifo");
            if std::process::Command::new("mkfifo").arg(&fifo).status().is_ok_and(|status| status.success()) {
                assert_eq!(refused(fifo), Err(KeyError::NotARegularFile));
            }
        }
        let big = dir.join("big");
        let file = fs::File::create(&big).unwrap();
        file.set_len(MAX_KEY_FILE_LEN as u64 + 1).unwrap();
        assert_eq!(refused(big.clone()), Err(KeyError::TooLarge { actual: MAX_KEY_FILE_LEN as u64 + 1 }));
        // At the bound, the magic is read first.
        file.set_len(MAX_KEY_FILE_LEN as u64).unwrap();
        assert_eq!(refused(big.clone()), Err(KeyError::NotAKeyFile));
        drop(file);
        fs::remove_dir_all(&dir).unwrap();
    }

    /// A key file that group or others can access loads with a warning (it holds the seed); a `0600` one without.
    #[cfg(unix)]
    #[test]
    fn a_readable_key_file_loads_with_a_warning() {
        use std::os::unix::fs::PermissionsExt;
        let dir = test_dir("mode");
        let path = dir.join("k");
        let key = small_keys().remove(0);
        key.write(&path, false).unwrap();
        assert_eq!(CachedKey::load_with_warnings(&path).unwrap(), (key.clone(), vec![]));
        for mode in [0o644, 0o640, 0o604, 0o660, 0o400 | 0o020] {
            fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
            let (loaded, warnings) = CachedKey::load_with_warnings(&path).unwrap();
            assert_eq!((loaded, warnings), (key.clone(), vec![KeyFileWarning::Accessible { mode }]), "{mode:o}");
        }
        fs::set_permissions(&path, fs::Permissions::from_mode(0o400)).unwrap();
        assert_eq!(CachedKey::load_with_warnings(&path).unwrap().1, []);
        let warning = KeyFileWarning::Accessible { mode: 0o644 }.to_string();
        assert!(warning.contains("0644") && warning.contains("chmod 600"), "{warning}");
        fs::remove_dir_all(&dir).unwrap();
    }
}
