// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

//! `lsk`: the leanSphincs-keccak signer (the proposal at its own parameters), for the Forge FFI tests and the
//! cross-checks, and the one-signer tiers.
//!
//! ```text
//! lsk sign   <seed_hex64> <b> <msg_hex64>                         0x || hex(abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig))
//! lsk kat    <seed_hex64> <b> <msg_hex64>                         one JSON object: key, signature and digest fields
//! lsk verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>    true | false
//!
//! lsk keygen (--seed-file <path> | --seed-stdin) (--tier light|standard|full | --b N --cache-bytes N) -o <keyfile>
//!            [--force] [--threads N]                              0x || hex(abi.encode(bytes32 pkSeed, bytes32 pkRoot))
//! lsk sign-key <keyfile> <msg_hex64>                              what `sign` prints for the key's seed and b
//! lsk info     <keyfile>                                          one JSON object: tier, plan, key words, costs
//! ```
//!
//! `b` is the height of the kept subtree (`0..=26`; `26` is a full key, about 1.52e10 keccak256 calls, 1.56e10 Keccak-f
//! permutations). The key words are high-aligned, as the on-chain verifier takes them (spec sections 12 and 13):
//! `pkSeed = P || 0^16`, `pkRoot = root || 0^16`.
//! Hex arguments are accepted with or without `0x`. `verify` mirrors the verifier: a signature that is not 5684 bytes or
//! a key word with nonzero low 128 bits (where the contract reverts) prints `false`, with the contract's revert reason
//! on stderr; like the contract, it checks the length first.
//!
//! `sign` and `kat` take the seed on the command line, where every local user can read it (the process list) and the
//! shell history keeps it: they are for test vectors and the FFI tests. They regenerate the kept subtree on every run.
//!
//! `keygen` generates a key once for a one-signer tier (`light`: `b = 13`, 16 KiB of node cache; `standard`: `b = 20`,
//! 1 MiB; `full`: `b = 26`, 16 MiB) or any `b` and budget, and writes it with its node cache to a key file. It reads the
//! seed from `--seed-file` (a file that group and others cannot access, as ssh requires of a private key) or from
//! standard input (`--seed-stdin`): 64 hex digits, `0x` optional, one trailing newline allowed. It checks the output
//! path before the keygen, and writes the key file with mode 0600 through a temporary file beside it, never over an
//! existing file without `--force` (see the `keyfile` module). `sign-key` signs from that file, recomputing only what
//! is not cached, verifies the signature under the file's public key, and prints the same bytes as `sign` (nothing at
//! all on a failure). Check the key words that `keygen`, `sign-key` and `info` print against the registered key: a key
//! file proves its key words are consistent with its cache and its seed's `P`, not that they are the seed's root.
//! `keygen` and `sign-key` print a summary (keccak256 calls, Keccak-f permutations, wall time) on stderr, and `sign-key`
//! and `info` warn there when group or others can access the key file or another user owns it. `info` prints no secret.
//! `sign-key` and `info` refuse the key files of the other leanSphincs variants (`lssk`, `lsfk`, `ls23k`), and their
//! signers refuse this one: the magics differ. With `LSK_RSS` set, every command also prints `VmHWM` at exit, a lower
//! bound on its peak resident set size. No error message repeats an argument's value: any of them may be a secret put
//! in the wrong place.
//!
//! One seed is one key: never use a seed with two different `b` (two tiers, a tier and a custom `b`, or `keygen` and
//! `sign` at another `b`). Keys from one seed share `P` and every one-time key. Where their kept subtrees overlap
//! (always, against a full key), a signature of one becomes a signature of the other from public data alone, so the
//! stronger key falls to the weaker one's lifetime. Nor use a seed for two leanSphincs variants (leanSphincs,
//! leanSphincs-S, leanSphincs-f, leanSphincs-23): they derive the same one-time keys and sign different encodings with
//! them (the spec, "Key separation"). Use a fresh seed for every key. The signer keeps no count of the signatures made:
//! keeping under the tier's rated lifetime is the caller's job.

use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use leansphincs_keccak::*;

const USAGE: &str = "usage:
  lsk sign     <seed_hex64> <b> <msg_hex64>
  lsk kat      <seed_hex64> <b> <msg_hex64>
  lsk verify   <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>
  lsk keygen   (--seed-file <path> | --seed-stdin) (--tier light|standard|full | --b N --cache-bytes N)
               -o <keyfile> [--force] [--threads N]
  lsk sign-key <keyfile> <msg_hex64>
  lsk info     <keyfile>
notes:
  sign and kat take the seed on the command line, where other local users and the shell history see it: test vectors
  only. keygen reads it from a file that group and others cannot access, or from standard input (64 hex digits).
  One seed, one key: never use a seed with two different b (another tier, or sign at another b), nor for two
  leanSphincs variants (leanSphincs, -S, -f, -23); signatures of one key convert into signatures of the other. Use a
  fresh seed for every key.";

/// Hex, with or without `0x`. An error names the field (`what`) and never repeats the value, which may be a secret.
fn parse_hex(s: &str, what: &str) -> Result<Vec<u8>, String> {
    let prefix = if s.starts_with("0x") || s.starts_with("0X") { 2 } else { 0 };
    let digits = &s[prefix..];
    if let Some((i, _)) = digits.char_indices().find(|(_, c)| !c.is_ascii_hexdigit()) {
        return Err(format!("{what}: not a hex digit at character {}", prefix + digits[..i].chars().count() + 1));
    }
    if digits.len() % 2 != 0 {
        return Err(format!("{what}: odd number of hex digits ({})", digits.len()));
    }
    Ok((0..digits.len()).step_by(2).map(|i| u8::from_str_radix(&digits[i..i + 2], 16).unwrap()).collect())
}

fn parse_fixed<const L: usize>(s: &str, what: &str) -> Result<[u8; L], String> {
    let bytes = parse_hex(s, what)?;
    bytes.try_into().map_err(|b: Vec<u8>| format!("{what}: expected {L} bytes, got {}", b.len()))
}

fn parse_b(s: &str) -> Result<usize, String> {
    match s.parse::<usize>() {
        Ok(b) if b <= H => Ok(b),
        _ => Err(format!("b: expected an integer in 0..={H}")),
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(2 + 2 * bytes.len());
    out.push_str("0x");
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// A 16-byte value as the high half of an EVM word: `value || 0^16`.
fn high_word(value: &[u8; N]) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[..N].copy_from_slice(value);
    word
}

/// `(pkSeed, pkRoot)` as the verifier takes them: `P || 0^16` and `root || 0^16`.
fn key_words(pk: &PublicKey) -> ([u8; 32], [u8; 32]) {
    (high_word(&pk.public_param), high_word(&pk.root))
}

fn u256_word(x: usize) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[24..].copy_from_slice(&(x as u64).to_be_bytes());
    word
}

/// `abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)`: the two words, the offset of `sig` (`0x60`), then its
/// length and its bytes, zero-padded to a whole word.
fn abi_encode(pk_seed: &[u8; 32], pk_root: &[u8; 32], sig: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(4 * 32 + sig.len().next_multiple_of(32));
    out.extend_from_slice(pk_seed);
    out.extend_from_slice(pk_root);
    out.extend_from_slice(&u256_word(0x60));
    out.extend_from_slice(&u256_word(sig.len()));
    out.extend_from_slice(sig);
    out.resize(out.len().next_multiple_of(32), 0);
    out
}

fn sign_args(args: &[String]) -> Result<(MasterSecret, usize, Message), String> {
    let [seed, b, msg] = args else { return Err(USAGE.into()) };
    Ok((parse_fixed(seed, "seed")?, parse_b(b)?, parse_fixed(msg, "message")?))
}

/// Where `keygen` reads the seed: never the command line.
#[derive(Debug, PartialEq)]
enum SeedSource {
    File(PathBuf),
    Stdin,
}

/// `keygen`'s arguments.
struct KeygenArgs {
    seed: SeedSource,
    tier: Tier,
    out: PathBuf,
    force: bool,
    threads: usize,
}

fn keygen_args(args: &[String]) -> Result<KeygenArgs, String> {
    let (mut seed, mut tier, mut b, mut cache_bytes, mut out, mut force, mut threads) =
        (None, None, None, None, None, false, None);
    let mut flags = args.iter().enumerate();
    while let Some((position, flag)) = flags.next() {
        let mut value = || flags.next().map(|(_, value)| value).ok_or(format!("{flag}: missing value"));
        match flag.as_str() {
            "--seed-file" | "--seed-stdin" => {
                if seed.is_some() {
                    return Err(format!("keygen: give one of --seed-file and --seed-stdin\n{USAGE}"));
                }
                seed = Some(match flag.as_str() {
                    "--seed-stdin" => SeedSource::Stdin,
                    _ => SeedSource::File(PathBuf::from(value()?)),
                });
            }
            "--tier" => tier = Some(Tier::preset(value()?).ok_or("--tier: expected light, standard or full")?),
            "--b" => b = Some(parse_b(value()?)?),
            "--cache-bytes" => {
                cache_bytes = Some(value()?.parse::<u64>().map_err(|_| "--cache-bytes: expected a number of bytes")?);
            }
            "-o" | "--out" => out = Some(PathBuf::from(value()?)),
            "--force" => force = true,
            "--threads" => {
                let n = value()?.parse::<usize>().ok().filter(|n| (1..=MAX_THREADS).contains(n));
                threads = Some(n.ok_or(format!("--threads: expected an integer in 1..={MAX_THREADS}"))?);
            }
            option if option.starts_with('-') => {
                let name = option.split('=').next().unwrap_or(option);
                return Err(if name.len() <= 32 {
                    format!("keygen: unknown option {name}\n{USAGE}")
                } else {
                    format!("keygen: unknown option at argument {} (not repeated here)\n{USAGE}", position + 1)
                });
            }
            _ => {
                return Err(format!(
                    "keygen: unexpected argument {} (not repeated here: it may be a secret). keygen does not take the \
                     seed on the command line, where other local users and the shell history see it: give \
                     --seed-file <path> or --seed-stdin\n{USAGE}",
                    position + 1
                ));
            }
        }
    }
    let seed = seed.ok_or(format!("keygen: give the seed with --seed-file <path> or --seed-stdin\n{USAGE}"))?;
    let tier = match (tier, b, cache_bytes) {
        (Some(tier), None, None) => tier,
        (None, Some(b), Some(cache_bytes)) => Tier::Custom { b, cache_bytes },
        _ => return Err(format!("keygen: give either --tier or both --b and --cache-bytes\n{USAGE}")),
    };
    let out = out.ok_or(format!("keygen: -o <keyfile> is required\n{USAGE}"))?;
    let threads = threads.unwrap_or_else(|| available_threads().min(MAX_THREADS));
    Ok(KeygenArgs { seed, tier, out, force, threads })
}

/// The longest seed text read: 64 hex digits, `0x` and a line ending, with room to spare.
const SEED_TEXT_MAX: u64 = 128;

/// At most `SEED_TEXT_MAX + 1` bytes of `r`.
fn read_bounded(r: impl Read) -> io::Result<Vec<u8>> {
    let mut text = Vec::new();
    r.take(SEED_TEXT_MAX + 1).read_to_end(&mut text)?;
    Ok(text)
}

/// The seed in `text`: 64 hex digits, `0x` optional, one trailing newline allowed.
fn parse_seed_text(text: &[u8], what: &str) -> Result<MasterSecret, String> {
    if text.len() as u64 > SEED_TEXT_MAX {
        return Err(format!("{what}: too long for a seed (64 hex digits)"));
    }
    let text = std::str::from_utf8(text).map_err(|_| format!("{what}: the seed is not text (64 hex digits)"))?;
    let text = text.strip_suffix('\n').unwrap_or(text);
    let text = text.strip_suffix('\r').unwrap_or(text);
    parse_fixed(text, &format!("{what}: seed"))
}

/// `keygen`'s seed, from a file that group and others cannot access, or from standard input.
fn read_seed(source: &SeedSource, stdin: &mut dyn Read) -> Result<MasterSecret, String> {
    match source {
        SeedSource::Stdin => {
            let text = read_bounded(stdin).map_err(|err| format!("--seed-stdin: {err}"))?;
            parse_seed_text(&text, "--seed-stdin")
        }
        SeedSource::File(path) => {
            let what = format!("--seed-file {}", path.display());
            let file = fs::File::open(path).map_err(|err| format!("{what}: {err}"))?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::MetadataExt;
                let mode = file.metadata().map_err(|err| format!("{what}: {err}"))?.mode() & 0o777;
                if mode & 0o077 != 0 {
                    return Err(format!(
                        "{what}: group or others can access it (mode {mode:04o}); refusing to read a seed from it: \
                         chmod 600 it"
                    ));
                }
            }
            let text = read_bounded(file).map_err(|err| format!("{what}: {err}"))?;
            parse_seed_text(&text, &what)
        }
    }
}

/// Loads a key file; its warnings go to stderr.
fn load_key(path: &str) -> Result<CachedKey, String> {
    let (key, warnings) = CachedKey::load_with_warnings(Path::new(path)).map_err(|err| format!("{path}: {err}"))?;
    for warning in warnings {
        eprintln!("lsk: warning: {path}: {warning}");
    }
    Ok(key)
}

/// `tier light, b = 13, plan level 3 only (1024 nodes, 16384 B of a 16384 B budget)`.
fn describe(key: &CachedKey) -> String {
    let (tier, b) = (key.tier(), key.b());
    let nodes = key.cache_nodes();
    format!(
        "tier {}, b = {b}, s = {}, plan {} ({nodes} nodes, {} B of a {} B budget)",
        tier.name(),
        key.s(),
        key.plan().describe(b),
        nodes * N as u64,
        tier.cache_bytes()
    )
}

fn run(args: &[String], stdin: &mut dyn Read) -> Result<String, String> {
    let (command, rest) = args.split_first().ok_or(USAGE)?;
    match command.as_str() {
        "sign" => {
            let (seed, b, m) = sign_args(rest)?;
            let (sk, pk) = key_gen(&seed, b);
            let sig = sign(&sk, &m);
            let (pk_seed, pk_root) = key_words(&pk);
            Ok(hex(&abi_encode(&pk_seed, &pk_root, &sig.to_bytes())))
        }
        "kat" => {
            let (seed, b, m) = sign_args(rest)?;
            let (sk, pk) = key_gen(&seed, b);
            let sig = sign(&sk, &m);
            let (idx, u) = message_digest(&pk.public_param, &sig.randomizer, &m);
            let (pk_seed, pk_root) = key_words(&pk);
            let indices: Vec<String> = u.iter().map(u32::to_string).collect();
            Ok(format!(
                "{{\"scheme\":\"leanSphincs-keccak\",\"seed\":\"{}\",\"b\":{b},\"message\":\"{}\",\"pkSeed\":\"{}\",\
                 \"pkRoot\":\"{}\",\"sig\":\"{}\",\"idx\":{idx},\"counter\":{},\"randomizer\":\"{}\",\"fors_indices\":[{}]}}",
                hex(&seed),
                hex(&m),
                hex(&pk_seed),
                hex(&pk_root),
                hex(&sig.to_bytes()),
                sig.counter,
                hex(&sig.randomizer),
                indices.join(",")
            ))
        }
        "verify" => {
            let [pk_seed, pk_root, msg, sig] = rest else { return Err(USAGE.into()) };
            let (pk_seed, pk_root) = (parse_fixed(pk_seed, "pkSeed")?, parse_fixed(pk_root, "pkRoot")?);
            let (m, sig) = (parse_fixed(msg, "message")?, parse_hex(sig, "sig")?);
            match verify_words(&pk_seed, &pk_root, &m, &sig) {
                Ok(valid) => Ok(valid.to_string()),
                Err(reason) => {
                    eprintln!("{reason}");
                    Ok("false".into())
                }
            }
        }
        "keygen" => {
            let KeygenArgs { seed, tier, out, force, threads } = keygen_args(rest)?;
            let write_error = |err: KeyError| match err {
                KeyError::Exists(_) => format!("{err} (pass --force to replace it)"),
                err => format!("{}: {err}", out.display()),
            };
            // The output path first: a missing or unwritable directory, or an existing key file, fails before the work.
            let writer = KeyFileWriter::create(&out, force).map_err(write_error)?;
            for stale in writer.stale_temporaries() {
                eprintln!(
                    "lsk keygen: warning: {} is the temporary file of another keygen to this path, interrupted (unless \
                     one is still running), and holds a seed: delete it",
                    stale.display()
                );
            }
            let seed = read_seed(&seed, stdin)?;
            let (start, before) = (Instant::now(), work());
            let key = keygen_cached(&seed, tier, threads);
            let (spent, seconds) = (work() - before, start.elapsed().as_secs_f64());
            writer.commit(&key).map_err(write_error)?;
            eprintln!(
                "lsk keygen: {}; {} keccak256 calls ({} Keccak-f permutations), {seconds:.2} s on {threads} threads; \
                 wrote {} ({} B)",
                describe(&key),
                spent.calls,
                spent.permutations,
                out.display(),
                key_file_len(key.b(), key.plan())
            );
            eprintln!(
                "lsk keygen: one seed, one key: never use this seed with another b (another tier, or `lsk sign` at \
                 another b), nor with another leanSphincs variant"
            );
            let (pk_seed, pk_root) = key_words(&key.public_key());
            Ok(hex(&[pk_seed, pk_root].concat()))
        }
        "sign-key" => {
            let [path, msg] = rest else { return Err(USAGE.into()) };
            let m = parse_fixed(msg, "message")?;
            let (start, before) = (Instant::now(), work());
            let key = load_key(path)?;
            let load = work() - before;
            let (sig, cost) = sign_with_cache_cost(&key, &m).map_err(|err| format!("{path}: {err}"))?;
            eprintln!(
                "lsk sign-key: {}; {} keccak256 calls, {} Keccak-f permutations (auth path {} calls, {} permutations; {} \
                 randomizer attempts), {} calls ({} permutations) to verify the signature under the key, and {} calls \
                 ({} permutations) to load and check the key, {:.3} s",
                describe(&key),
                cost.total.calls,
                cost.total.permutations,
                cost.auth_path.calls,
                cost.auth_path.permutations,
                cost.attempts,
                cost.verify.calls,
                cost.verify.permutations,
                load.calls,
                load.permutations,
                start.elapsed().as_secs_f64()
            );
            let (pk_seed, pk_root) = key_words(&key.public_key());
            Ok(hex(&abi_encode(&pk_seed, &pk_root, &sig.to_bytes())))
        }
        "info" => {
            let [path] = rest else { return Err(USAGE.into()) };
            let key = load_key(path)?;
            let (tier, b, plan) = (key.tier(), key.b(), key.plan());
            let (pk_seed, pk_root) = key_words(&key.public_key());
            Ok(format!(
                "{{\"scheme\":\"leanSphincs-keccak\",\"format_version\":{KEY_FILE_VERSION},\"tier\":\"{}\",\"b\":{b},\
                 \"s\":{},\"plan\":\"{}\",\"cache_nodes\":{},\"cache_bytes\":{},\"cache_budget_bytes\":{},\
                 \"file_bytes\":{},\"pkSeed\":\"{}\",\"pkRoot\":\"{}\",\"auth_path_calls\":{},\
                 \"auth_path_permutations\":{},\"mean_randomizer_attempts\":{},\"keygen_calls\":{},\
                 \"keygen_permutations\":{}}}",
                tier.name(),
                key.s(),
                plan.describe(b),
                key.cache_nodes(),
                key.cache_nodes() * N as u64,
                tier.cache_bytes(),
                key_file_len(b, plan),
                hex(&pk_seed),
                hex(&pk_root),
                plan.auth_path_calls(b),
                plan.auth_path_permutations(b),
                1u64 << (H - b),
                keygen_calls(b),
                keygen_permutations(b)
            ))
        }
        _ => Err(USAGE.into()),
    }
}

/// `VmHWM` of `/proc/self/status` (Linux): the resident set's high-water mark as the kernel recorded it. It can miss a
/// short-lived peak, so it is a lower bound on the true peak.
fn peak_rss() -> Option<String> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
    Some(line["VmHWM:".len()..].trim().to_string())
}

/// The verifier's `verify(pkSeed, pkRoot, message, sig)`: `Err` with the contract's revert reason, in the contract's
/// order (the length first, then the key words), or whether a well-formed signature is valid.
fn verify_words(pk_seed: &[u8; 32], pk_root: &[u8; 32], m: &Message, sig: &[u8]) -> Result<bool, &'static str> {
    let sig = Signature::from_bytes(sig).ok_or("Invalid sig length")?;
    if pk_seed[N..] != [0; 32 - N] || pk_root[N..] != [0; 32 - N] {
        return Err("Invalid public key");
    }
    let pk = PublicKey { root: pk_root[..N].try_into().unwrap(), public_param: pk_seed[..N].try_into().unwrap() };
    Ok(verify(&pk, m, &sig).is_ok())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = run(&args, &mut io::stdin().lock());
    if std::env::var_os("LSK_RSS").is_some() {
        let rss = peak_rss().unwrap_or_else(|| "unknown".into());
        eprintln!("lsk: VmHWM at exit {rss} (a lower bound on the peak resident set size)");
    }
    match result {
        Ok(out) => {
            println!("{out}");
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(v: &[&str]) -> Vec<String> {
        v.iter().map(|s| s.to_string()).collect()
    }

    /// `run` with no standard input.
    fn run0(v: &[&str]) -> Result<String, String> {
        run(&args(v), &mut io::empty())
    }

    /// A fresh, empty directory for one test.
    fn test_dir(what: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("lsk-cli-{what}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// A seed file with mode `mode`.
    fn seed_file(path: &Path, text: &str, mode: u32) {
        let _ = fs::remove_file(path);
        fs::write(path, text).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
        }
        let _ = mode;
    }

    #[test]
    fn hex_with_or_without_prefix() {
        assert_eq!(parse_hex("0x00ff10", "x").unwrap(), [0, 255, 16]);
        assert_eq!(parse_hex("00FF10", "x").unwrap(), [0, 255, 16]);
        assert_eq!(parse_hex("0x", "x").unwrap(), [0u8; 0]);
        assert_eq!(parse_hex("0x0", "x").unwrap_err(), "x: odd number of hex digits (1)");
        assert_eq!(parse_hex("0xzz", "x").unwrap_err(), "x: not a hex digit at character 3");
        assert_eq!(parse_hex("0xé0", "x").unwrap_err(), "x: not a hex digit at character 3");
        assert_eq!(parse_hex("abé0", "x").unwrap_err(), "x: not a hex digit at character 3");
        assert!(parse_fixed::<32>(&"11".repeat(31), "seed").is_err());
        assert_eq!(parse_fixed::<2>("0xabcd", "x").unwrap(), [0xab, 0xcd]);
        assert_eq!(hex(&[0, 0xab]), "0x00ab");
        assert!(parse_b("26").is_ok() && parse_b("27").is_err() && parse_b("-1").is_err());
    }

    /// The head is two key words and the offset `0x60`; the tail is the length and the padded signature.
    #[test]
    fn abi_encoding_layout() {
        let sig: Vec<u8> = (0..SIG_SIZE).map(|i| (i % 251) as u8 + 1).collect();
        let (pk_seed, pk_root) = ([0xaau8; 32], [0xbbu8; 32]);
        let out = abi_encode(&pk_seed, &pk_root, &sig);
        assert_eq!(out.len(), 4 * 32 + 5696);
        assert_eq!(out[..32], pk_seed);
        assert_eq!(out[32..64], pk_root);
        assert_eq!(out[64..96], u256_word(0x60));
        assert_eq!(out[95], 0x60);
        assert_eq!(out[96..128], u256_word(5684));
        assert_eq!(out[126..128], [0x16, 0x34]);
        assert_eq!(out[128..128 + SIG_SIZE], sig[..]);
        assert!(out[128 + SIG_SIZE..].iter().all(|&b| b == 0));
    }

    #[test]
    fn key_words_are_high_aligned() {
        let pk = PublicKey { root: [1; N], public_param: [2; N] };
        let (pk_seed, pk_root) = key_words(&pk);
        assert_eq!(pk_seed[..N], [2; N]);
        assert_eq!(pk_root[..N], [1; N]);
        assert_eq!(pk_seed[N..], [0; N]);
        assert_eq!(pk_root[N..], [0; N]);
    }

    /// `sign` output decodes back to a key and a signature that `verify` accepts, and `verify` mirrors the verifier's
    /// rejections.
    #[test]
    fn sign_then_verify_roundtrip() {
        let (seed, msg) = (format!("0x{}", "42".repeat(32)), "ab".repeat(32));
        let encoded = parse_hex(&run0(&["sign", &seed, "6", &msg]).unwrap(), "out").unwrap();
        let (pk_seed, pk_root, sig) = (hex(&encoded[..32]), hex(&encoded[32..64]), hex(&encoded[128..128 + SIG_SIZE]));
        assert_eq!(run0(&["verify", &pk_seed, &pk_root, &msg, &sig]).unwrap(), "true");
        let other_msg = format!("cd{}", "ab".repeat(31));
        assert_eq!(run0(&["verify", &pk_seed, &pk_root, &other_msg, &sig]).unwrap(), "false");
        let short = hex(&encoded[128..128 + SIG_SIZE - 1]);
        assert_eq!(run0(&["verify", &pk_seed, &pk_root, &msg, &short]).unwrap(), "false");
        let mut low = parse_hex(&pk_root, "pkRoot").unwrap();
        low[31] = 1;
        assert_eq!(run0(&["verify", &pk_seed, &hex(&low), &msg, &sig]).unwrap(), "false");
        // The revert reasons, in the contract's order: a wrong length wins over a dirty key word.
        let words = |s: &str| -> [u8; 32] { parse_fixed(s, "word").unwrap() };
        let (seed_w, root_w, low_w) = (words(&pk_seed), words(&pk_root), words(&hex(&low)));
        let (m, sig_bytes) = (parse_fixed(&msg, "message").unwrap(), &encoded[128..128 + SIG_SIZE]);
        assert_eq!(verify_words(&seed_w, &root_w, &m, sig_bytes), Ok(true));
        assert_eq!(verify_words(&seed_w, &root_w, &m, &sig_bytes[1..]), Err("Invalid sig length"));
        assert_eq!(verify_words(&seed_w, &low_w, &m, sig_bytes), Err("Invalid public key"));
        assert_eq!(verify_words(&low_w, &root_w, &m, sig_bytes), Err("Invalid public key"));
        assert_eq!(verify_words(&seed_w, &low_w, &m, &sig_bytes[1..]), Err("Invalid sig length"));
        let kat = run0(&["kat", &seed, "6", &msg]).unwrap();
        assert!(kat.starts_with("{\"scheme\":\"leanSphincs-keccak\""));
        assert!(kat.contains(&format!("\"pkSeed\":\"{pk_seed}\"")) && kat.contains(&format!("\"sig\":\"{sig}\"")));
        assert!(run0(&["sign", &seed, "27", &msg]).is_err());
        assert!(run0(&["nope"]).is_err());
    }

    /// `keygen` prints the key words `sign` starts with, `sign-key` prints what `sign` prints, `info` gives no secret,
    /// and an existing key file is not overwritten without `--force`. The seed comes from standard input or from a
    /// private file.
    #[test]
    fn keygen_then_sign_key() {
        let dir = test_dir("keygen");
        let (seed, msg) = ("5a".repeat(32), format!("0x{}", "c3".repeat(32)));
        let seed_path = dir.join("seed");
        seed_file(&seed_path, &format!("0x{seed}\n"), 0o600);
        for (b, flags, plan) in [
            ("6", vec!["--b", "6", "--cache-bytes", "100"], "level 4 only"),
            ("13", vec!["--tier", "light"], "level 3 only"),
            ("9", vec!["--b", "9", "--cache-bytes", "0", "--threads", "3"], "none"),
        ] {
            let path = dir.join(format!("key-{b}"));
            let path = path.to_str().unwrap();
            let keygen = [&["keygen", "--seed-stdin"][..], &flags, &["-o", path]].concat();
            let words = run(&args(&keygen), &mut seed.as_bytes()).unwrap();
            let signed = run0(&["sign", &seed, b, &msg]).unwrap();
            assert_eq!(words.len(), 2 + 128);
            assert!(signed.starts_with(&words), "b = {b}: the key words");
            assert_eq!(run0(&["sign-key", path, &msg]).unwrap(), signed, "b = {b}");
            let info = run0(&["info", path]).unwrap();
            assert!(info.contains(&format!("\"b\":{b},")) && info.contains(&format!("\"plan\":\"{plan}\"")), "{info}");
            assert!(info.contains(&format!("\"pkSeed\":\"{}\"", &words[..66])), "{info}");
            assert!(!info.contains(&seed), "info prints no secret");
            let again = run(&args(&keygen), &mut seed.as_bytes()).unwrap_err();
            assert!(again.contains("refusing to overwrite") && again.contains("--force"), "{again}");
            let forced =
                [&["keygen", "--seed-file", seed_path.to_str().unwrap()][..], &flags, &["-o", path, "--force"]];
            assert_eq!(run0(&forced.concat()).unwrap(), words);
        }
        let bad = |extra: &[&str]| run0(&[&["keygen", "--seed-stdin"][..], extra].concat()).unwrap_err();
        assert!(bad(&["--tier", "light", "--b", "3", "-o", "x"]).contains("either --tier or both"));
        assert!(bad(&["--b", "3", "-o", "x"]).contains("either --tier or both"));
        assert!(bad(&["--tier", "huge", "-o", "x"]).contains("--tier"));
        assert!(bad(&["--tier", "light"]).contains("-o <keyfile> is required"));
        assert!(bad(&["--b", "27", "--cache-bytes", "0", "-o", "x"]).contains("b: expected"));
        assert!(bad(&["--tier", "light", "-o", "x", "--threads", "0"]).contains("--threads"));
        assert!(bad(&["--tier"]).contains("missing value"));
        assert!(
            bad(&["--tier", "light", "-o", "x", "--seed-file", "s"]).contains("one of --seed-file and --seed-stdin")
        );
        let no_seed = run0(&["keygen", "--tier", "light", "-o", "x"]).unwrap_err();
        assert!(no_seed.contains("--seed-file <path> or --seed-stdin"), "{no_seed}");
        let missing = dir.join("missing");
        assert!(run0(&["sign-key", missing.to_str().unwrap(), &msg]).is_err());
        fs::write(&missing, b"not a key").unwrap();
        let err = run0(&["info", missing.to_str().unwrap()]).unwrap_err();
        assert!(err.contains("not a leanSphincs-keccak key file"), "{err}");
        // A key file of another leanSphincs variant (here one of ours under its magic, re-checksummed) is refused by
        // `info` and `sign-key` alike.
        let ours = fs::read(dir.join("key-6")).unwrap();
        let sibling = dir.join("sibling");
        for magic in [b"LS-SKKEY", b"LS-FKKEY", b"LS23KKEY"] {
            let mut file = ours.clone();
            file[..8].copy_from_slice(magic);
            let n = file.len();
            let checksum = keccak256(&file[..n - 32]);
            file[n - 32..].copy_from_slice(&checksum);
            fs::write(&sibling, &file).unwrap();
            let sibling = sibling.to_str().unwrap();
            for err in [run0(&["info", sibling]).unwrap_err(), run0(&["sign-key", sibling, &msg]).unwrap_err()] {
                assert!(err.contains("not a leanSphincs-keccak key file"), "{err}");
            }
        }
        fs::remove_file(&sibling).unwrap();
        assert_eq!(
            fs::read_dir(&dir).unwrap().count(),
            5,
            "three key files, the seed file and `missing`: no temporary"
        );
        fs::remove_dir_all(&dir).unwrap();
    }

    /// No error repeats a seed: not a seed given on `keygen`'s command line (which it refuses), not a malformed one,
    /// not one in the wrong place, and not the contents of a seed file. A seed file that group or others can access is
    /// refused. (Errors used to print the whole argument: `bad hex: <seed>`, and `keygen` took the seed on argv.)
    #[test]
    fn errors_never_repeat_a_seed() {
        let dir = test_dir("echo");
        let seed = "7e".repeat(32);
        let leaks =
            |err: &str, secret: &str| (0..secret.len().saturating_sub(15)).any(|i| err.contains(&secret[i..i + 16]));
        let msg = "00".repeat(32);
        let out = dir.join("k");
        let out = out.to_str().unwrap();
        let typos = [format!("{}g", &seed[..63]), seed[..63].to_string(), format!("{seed}00"), format!("0x{seed}z")];
        for typo in &typos {
            for err in [
                run0(&["sign", typo, "6", &msg]).unwrap_err(),
                run0(&["kat", typo, "6", &msg]).unwrap_err(),
                run(
                    &args(&["keygen", "--seed-stdin", "--b", "2", "--cache-bytes", "0", "-o", out]),
                    &mut typo.as_bytes(),
                )
                .unwrap_err(),
            ] {
                assert!(err.starts_with("seed: ") || err.starts_with("--seed-stdin: seed: "), "{err}");
                assert!(!leaks(&err, typo), "{err}");
            }
        }
        // The seed where keygen used to take it, or anywhere else on its command line, is refused and not repeated.
        for argv in [
            vec!["keygen", seed.as_str(), "--tier", "light", "-o", out],
            vec!["keygen", "--tier", "light", seed.as_str(), "-o", out],
            vec!["keygen", "--seed-stdin", "--tier", "light", "-o", out, seed.as_str()],
        ] {
            let err = run(&args(&argv), &mut seed.as_bytes()).unwrap_err();
            assert!(err.contains("not repeated here") && err.contains("--seed-file <path> or --seed-stdin"), "{err}");
            assert!(!leaks(&err, &seed), "{err}");
        }
        let long_option = format!("--seed={seed}");
        let err = run0(&["keygen", &long_option, "--tier", "light", "-o", out]).unwrap_err();
        assert!(err.contains("unknown option --seed\n") && !leaks(&err, &seed), "{err}");
        let err = run0(&["sign", &msg, &seed, "6"]).unwrap_err();
        assert!(err.starts_with("b: expected") && !leaks(&err, &seed), "{err}");
        // Seed files: private ones are read; others are refused unread.
        let seed_path = dir.join("seed");
        let keygen = |path: &Path| {
            let argv = ["keygen", "--seed-file", path.to_str().unwrap(), "--b", "2", "--cache-bytes", "0", "-o", out];
            run0(&argv)
        };
        seed_file(&seed_path, &format!("{seed}\r\n"), 0o600);
        assert!(keygen(&seed_path).is_ok());
        fs::remove_file(out).unwrap();
        #[cfg(unix)]
        for mode in [0o644, 0o640, 0o604, 0o620] {
            seed_file(&seed_path, &seed, mode);
            let err = keygen(&seed_path).unwrap_err();
            assert!(err.contains(&format!("mode {mode:04o}")) && err.contains("chmod 600"), "{err}");
            assert!(!leaks(&err, &seed) && !Path::new(out).exists(), "{err}");
        }
        for (text, why) in [
            (format!("{}x\n", &seed[..63]), "not a hex digit"),
            (format!("{seed}\n\n"), "not a hex digit"),
            (format!("{seed} {seed}"), "too long"),
            (seed[..62].to_string(), "expected 32 bytes"),
        ] {
            seed_file(&seed_path, &text, 0o600);
            let err = keygen(&seed_path).unwrap_err();
            assert!(err.contains(why) && !leaks(&err, &seed), "{err}");
        }
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 1, "only the seed file: no key file, no temporary file");
        fs::remove_dir_all(&dir).unwrap();
    }

    /// `--threads` is bounded: absurd values are refused before any work (they used to overflow in `chunk_bits`,
    /// panicking with overflow checks on, or spawn up to `2^b` threads).
    #[test]
    fn keygen_threads_are_bounded() {
        let parsed = |threads: &str| {
            keygen_args(&args(&["--seed-stdin", "--tier", "light", "-o", "k", "--threads", threads])).map(|a| a.threads)
        };
        assert_eq!(parsed("1"), Ok(1));
        assert_eq!(parsed(&MAX_THREADS.to_string()), Ok(MAX_THREADS));
        for absurd in
            ["0", "1025", "1048576", "4611686018427387904", "18446744073709551615", "18446744073709551616", "-1"]
        {
            assert_eq!(parsed(absurd), Err(format!("--threads: expected an integer in 1..={MAX_THREADS}")), "{absurd}");
        }
        let defaults = keygen_args(&args(&["--seed-stdin", "--tier", "light", "-o", "k"])).ok().unwrap();
        assert!((1..=MAX_THREADS).contains(&defaults.threads));
        assert_eq!(defaults.seed, SeedSource::Stdin);
    }
}
