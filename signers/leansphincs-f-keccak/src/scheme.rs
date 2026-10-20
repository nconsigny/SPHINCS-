//! The XMSS tree (full or pruned), the message digest, and `Gen`, `Sign`, `Ver`.
//!
//! A pruned key keeps one subtree of height `b` and replaces the `h - b` siblings above it by
//! pseudorandom surrogate nodes; the signer grinds its randomizer until the leaf index lands in the
//! kept subtree. A full key is the pruned key with `b = h`.

use crate::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PublicKey {
    pub root: Digest,
    pub public_param: PublicParam,
}

impl PublicKey {
    pub fn to_bytes(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0u8; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub randomizer: Randomizer,
    pub fors: ForsOpening,
    pub counter: u32,
    pub wots: [Digest; V],
    pub path: [Digest; H],
}

impl Signature {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SIG_SIZE);
        out.extend_from_slice(&self.randomizer);
        for kappa in 0..K {
            out.extend_from_slice(&self.fors.secrets[kappa]);
            for node in &self.fors.paths[kappa] {
                out.extend_from_slice(node);
            }
        }
        out.extend_from_slice(&self.counter.to_le_bytes());
        for value in &self.wots {
            out.extend_from_slice(value);
        }
        for node in &self.path {
            out.extend_from_slice(node);
        }
        debug_assert_eq!(out.len(), SIG_SIZE);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != SIG_SIZE {
            return None;
        }
        let mut at = 0;
        let mut take = |len: usize| {
            at += len;
            &bytes[at - len..at]
        };
        let randomizer = take(RANDOMIZER_LEN).try_into().unwrap();
        let mut fors = ForsOpening { secrets: [[0; N]; K], paths: [[[0; N]; A]; K] };
        for kappa in 0..K {
            fors.secrets[kappa] = take(N).try_into().unwrap();
            for level in 0..A {
                fors.paths[kappa][level] = take(N).try_into().unwrap();
            }
        }
        let counter = u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap());
        let wots = std::array::from_fn(|_| take(N).try_into().unwrap());
        let path = std::array::from_fn(|_| take(N).try_into().unwrap());
        Some(Self { randomizer, fors, counter, wots, path })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VerifyError {
    /// The counter does not encode the FORS tops into a codeword.
    InadmissibleEncoding,
    RootMismatch,
}

/// The message digest, one call: `P | address(MSG, hi = 0, lo = 0) | m | rho` (80 bytes, one keccak
/// permutation), untruncated. `P` binds the key, so the root is not hashed.
pub fn digest_block(pp: &PublicParam, rho: &Randomizer, m: &Message) -> [u8; 32] {
    let mut payload = [0u8; MESSAGE_LEN + RANDOMIZER_LEN];
    payload[..MESSAGE_LEN].copy_from_slice(m);
    payload[MESSAGE_LEN..].copy_from_slice(rho);
    th_full(pp, &tweak(TWEAK_MSG, 0, 0), &payload)
}

/// The leaf index alone (what grinding computes; the same single call).
pub fn digest_index(pp: &PublicParam, rho: &Randomizer, m: &Message) -> u64 {
    index_of_block(&digest_block(pp, rho, m))
}

/// The leaf index: the low `h` bits of the last 64-bit word (bytes 24..32) of the digest.
pub fn index_of_block(d: &[u8; 32]) -> u64 {
    u64::from_le_bytes(d[24..32].try_into().unwrap()) & ((1 << H) - 1)
}

/// FORS indices per 64-bit word of the digest: seven 9-bit fields, bits 0..63.
const INDICES_PER_WORD: usize = 7;

// The FORS indices fill words 0..3 without crossing a word boundary, and the leaf index has word 3 to itself.
const _: () = assert!(INDICES_PER_WORD * A <= 64 && K.div_ceil(INDICES_PER_WORD) <= 3 && H <= 64);

/// The `k` FORS indices of a digest. No field lies across two 64-bit words: FORS index `kappa` is in
/// little-endian word `kappa / 7` (bytes `8 w .. 8 w + 8`), at bit `a * (kappa % 7)`.
pub fn fors_indices_of_block(d: &[u8; 32]) -> [u32; K] {
    std::array::from_fn(|kappa| {
        let word = &d[8 * (kappa / INDICES_PER_WORD)..][..8];
        (u64::from_le_bytes(word.try_into().unwrap()) >> (A * (kappa % INDICES_PER_WORD)) & ((1 << A) - 1)) as u32
    })
}

/// The message digest, from one call, read as the leaf index (word 3) and the `k` FORS indices (words 0, 1, 2).
pub fn message_digest(pp: &PublicParam, rho: &Randomizer, m: &Message) -> (u64, [u32; K]) {
    let d = digest_block(pp, rho, m);
    (index_of_block(&d), fors_indices_of_block(&d))
}

pub fn xmss_node(pp: &PublicParam, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, level as u32, j as u32), &[*left, *right])
}

/// The XMSS tree of a key: the kept subtree's levels and the surrogates above it.
#[derive(Clone, Debug)]
pub struct XmssTree {
    /// Height of the kept subtree; `b = h` is a full key.
    pub b: usize,
    /// The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b`.
    pub s: u64,
    /// The kept subtree, level 0 being its `2^b` leaves.
    levels: Vec<Vec<Digest>>,
    /// The siblings of the path at levels `b..h`, surrogates (no secret below them) unless `b = h`.
    pub surrogates: Vec<Digest>,
    pub root: Digest,
}

impl XmssTree {
    pub fn from_leaves(pp: &PublicParam, b: usize, s: u64, leaves: Vec<Digest>, surrogates: Vec<Digest>) -> Self {
        assert!(b <= H && s < 1 << (H - b));
        assert_eq!(leaves.len(), 1 << b);
        assert_eq!(surrogates.len(), H - b);
        let mut levels = vec![leaves];
        for level in 1..=b {
            let below = &levels[level - 1];
            let first = s << (b - level);
            let up = (0..below.len() / 2)
                .map(|j| xmss_node(pp, level, first + j as u64, &below[2 * j], &below[2 * j + 1]))
                .collect();
            levels.push(up);
        }
        let root = fold_surrogates(pp, b, s, levels[b][0], &surrogates);
        Self { b, s, levels, surrogates, root }
    }

    pub fn contains(&self, idx: u64) -> bool {
        idx >> self.b == self.s
    }

    /// Level `level` of the kept subtree (`0..=b`), its `2^(b - level)` nodes from the left.
    pub fn level(&self, level: usize) -> &[Digest] {
        &self.levels[level]
    }

    /// The authentication path of leaf `idx`, which must be kept.
    pub fn path(&self, idx: u64) -> [Digest; H] {
        assert!(self.contains(idx));
        let local = (idx - (self.s << self.b)) as usize;
        std::array::from_fn(|level| {
            if level < self.b { self.levels[level][(local >> level) ^ 1] } else { self.surrogates[level - self.b] }
        })
    }
}

/// The XMSS root of a key keeping subtree `s` of height `b`: the kept subtree's root `top`, folded up through the
/// surrogates (bit `level - b` of `s` picks the side).
pub fn fold_surrogates(pp: &PublicParam, b: usize, s: u64, top: Digest, surrogates: &[Digest]) -> Digest {
    debug_assert_eq!(surrogates.len(), H - b);
    surrogates.iter().enumerate().fold(top, |node, (t, sibling)| {
        let level = b + t;
        let j = s >> t;
        let (left, right) = if j & 1 == 0 { (node, *sibling) } else { (*sibling, node) };
        xmss_node(pp, level + 1, j >> 1, &left, &right)
    })
}

/// `Tree.fold`: the root a leaf and its path reach.
pub fn tree_fold(pp: &PublicParam, idx: u64, leaf: Digest, path: &[Digest; H]) -> Digest {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let (left, right) = if (idx >> level) & 1 == 0 { (current, *sibling) } else { (*sibling, current) };
        xmss_node(pp, level + 1, idx >> (level + 1), &left, &right)
    })
}

/// A non-threshold secret key.
#[derive(Clone)]
pub struct SecretKey {
    pub public_param: PublicParam,
    pub master: MasterSecret,
    pub tree: XmssTree,
}

impl SecretKey {
    pub fn public_key(&self) -> PublicKey {
        PublicKey { root: self.tree.root, public_param: self.public_param }
    }
}

/// `P = Th(0^16, address(PARAMETER), S)`: the public parameter of a seed.
pub fn derive_public_param(seed: &MasterSecret) -> PublicParam {
    th(&[0; PUBLIC_PARAM_LEN], &tweak(TWEAK_PARAMETER, 0, 0), seed)
}

/// `s`, the kept subtree of height `b`: the low `h - b` bits of `P` (`0` for a full key).
pub fn subtree_position(pp: &PublicParam, b: usize) -> u64 {
    assert!(b <= H);
    if b == H { 0 } else { u64::from_le_bytes(pp[..8].try_into().unwrap()) & ((1 << (H - b)) - 1) }
}

/// The `h - b` surrogate siblings of a key keeping a subtree of height `b`, levels `b..h`, from the seed.
pub fn derive_surrogates(pp: &PublicParam, seed: &MasterSecret, b: usize) -> Vec<Digest> {
    (b..H).map(|level| th(pp, &tweak(TWEAK_SURROGATE, level as u32, 0), seed)).collect()
}

/// `Gen` for a key keeping a subtree of height `b` (`b = h` for a full key).
///
/// The public parameter is derived from the seed, its low bits place the kept subtree, and the
/// surrogates are derived from the seed. The `2^b` one-time leaves are computed on every core, and every level of the
/// kept subtree stays in memory (`tiers` has the streaming keygen of a key with a bounded node cache).
pub fn key_gen(seed: &MasterSecret, b: usize) -> (SecretKey, PublicKey) {
    assert!(b <= H);
    let public_param = derive_public_param(seed);
    let s = subtree_position(&public_param, b);
    let leaves = par_map(1 << b, |j| wots_leaf(&public_param, seed, ((s << b) + j as u64) as u32));
    let surrogates = derive_surrogates(&public_param, seed, b);
    let tree = XmssTree::from_leaves(&public_param, b, s, leaves, surrogates);
    let sk = SecretKey { public_param, master: *seed, tree };
    let pk = sk.public_key();
    (sk, pk)
}

/// `R_0 = Th(P, tw_rand, S | m)`: the first randomizer a message tries.
pub fn randomizer_base(pp: &PublicParam, master: &MasterSecret, m: &Message) -> Randomizer {
    let mut payload = [0u8; MASTER_SECRET_LEN + MESSAGE_LEN];
    payload[..MASTER_SECRET_LEN].copy_from_slice(master);
    payload[MASTER_SECRET_LEN..].copy_from_slice(m);
    th(pp, &tweak(TWEAK_RANDOMIZER, 0, 0), &payload)
}

/// The randomizer of attempt `i`: `R_0 + i`, as little-endian 128-bit numbers. No hash is needed
/// from one attempt to the next.
pub fn randomizer(base: &Randomizer, i: u32) -> Randomizer {
    u128::from_le_bytes(*base).wrapping_add(u128::from(i)).to_le_bytes()
}

/// `Sign`: take the least `i` whose randomizer `R_0 + i` lands in the kept subtree (`i = 0` for a
/// full key), open FORS, sign its tops with WOTS+C.
pub fn sign(sk: &SecretKey, m: &Message) -> Signature {
    let tree = &sk.tree;
    let path = |idx| Ok::<_, std::convert::Infallible>(tree.path(idx));
    match sign_with(&sk.public_param, &sk.master, m, |idx| tree.contains(idx), path) {
        Ok(sig) => sig,
        Err(never) => match never {},
    }
}

/// `Sign`, with the authentication path of the leaf left to `path`. Everything else depends only on `P`, the master
/// secret and which leaves are kept (`contains`), so [`sign`] (the path from the in-memory tree) and
/// [`sign_with_cache`] (the path from a node cache) give the same bytes. The path is asked for right after the grind:
/// an `Err` (a cache that does not check out) costs no FORS or WOTS work.
pub fn sign_with<E>(
    pp: &PublicParam,
    master: &MasterSecret,
    m: &Message,
    contains: impl Fn(u64) -> bool,
    path: impl FnOnce(u64) -> Result<[Digest; H], E>,
) -> Result<Signature, E> {
    // The randomizers are `R_0 + i`, and the 80-byte digest input is one keccak permutation: an attempt
    // costs one call and one permutation.
    let base = randomizer_base(pp, master, m);
    let rho = (0u32..).map(|i| randomizer(&base, i)).find(|rho| contains(digest_index(pp, rho, m))).unwrap();
    let (idx, u) = message_digest(pp, &rho, m);
    let path = path(idx)?;
    let forest = ForsForest::from_leaves(pp, idx, &fors_leaves(pp, master, idx));
    let fors = ForsOpening {
        secrets: std::array::from_fn(|kappa| fors_secret(pp, master, idx, kappa, u[kappa] as usize)),
        paths: forest.paths(&u),
    };
    let (counter, wots) = wots_sign(pp, master, idx as u32, &forest.tops).expect("no admissible WOTS+C encoding");
    Ok(Signature { randomizer: rho, fors, counter, wots, path })
}

/// `Ver`.
pub fn verify(pk: &PublicKey, m: &Message, sig: &Signature) -> Result<(), VerifyError> {
    let pp = &pk.public_param;
    let (idx, u) = message_digest(pp, &sig.randomizer, m);
    let tops = fors_recover(pp, idx, &u, &sig.fors);
    let leaf = wots_recover(pp, idx as u32, &tops, sig.counter, &sig.wots).ok_or(VerifyError::InadmissibleEncoding)?;
    if tree_fold(pp, idx, leaf, &sig.path) == pk.root { Ok(()) } else { Err(VerifyError::RootMismatch) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(x: u8) -> MasterSecret {
        std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
    }

    #[test]
    fn pruned_sign_verify_and_costs() {
        // P, the kept subtree (per WOTS leaf: 32 secret pairs, 64 * 3 chain steps and the leaf, plus the nodes), and
        // a derivation and a node per surrogate. Every call is one permutation but the leaf's, whose 1056-byte input
        // takes 8.
        let keygen = |b: usize, leaf: u64| {
            1 + (1u64 << b) * (V as u64 / 2 + 192 + leaf) + ((1u64 << b) - 1) + 2 * (H - b) as u64
        };
        let keygen_work = |b: usize| Work { calls: keygen(b, 1), permutations: keygen(b, 8) };
        assert_eq!(V / 2 + V * (CHAIN_LEN - 1) + 1, 225);
        // A full key, 2^26 * 226 calls, the "about 1.52e10 keccak calls" of the leanSphincs-S spec (section 9), which
        // the f spec keeps, the README, lsfk and the Python signer, and 2^26 * 233 permutations: sphincs-art's 15.6B
        // (its keygen figure, 15,636,365,313, counts one node more than a 2^26-leaf tree has). The key does not depend
        // on the FORS parameters or T.
        assert_eq!(keygen_work(H), Work { calls: 15_166_603_264, permutations: 15_636_365_312 });
        for b in [3usize, 10] {
            let before = work();
            let (sk, pk) = key_gen(&seed(b as u8), b);
            assert_eq!(work() - before, keygen_work(b), "b = {b}");
            for t in 0..3u8 {
                let m: Message = std::array::from_fn(|i| t ^ i as u8);
                let sig = sign(&sk, &m);
                let bytes = sig.to_bytes();
                assert_eq!(bytes.len(), SIG_SIZE);
                assert_eq!(Signature::from_bytes(&bytes).unwrap(), sig);
                let before = work();
                assert_eq!(verify(&pk, &m, &sig), Ok(()));
                let spent = work() - before;
                assert_eq!(spent, Work { calls: VERIFY_KECCAK_CALLS, permutations: VERIFY_PERMUTATIONS }, "constant");
                assert_eq!(spent, Work { calls: 279, permutations: 290 });
                let mut other = m;
                other[0] ^= 1;
                assert!(verify(&pk, &other, &sig).is_err());
                let mut bad = sig.clone();
                bad.fors.secrets[3][0] ^= 1;
                assert!(verify(&pk, &m, &bad).is_err());
            }
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The byte offset and length of every field of the encoding (the f spec's section 11 row), in order.
    fn field_offsets() -> Vec<(&'static str, usize, usize)> {
        let mut fields = vec![("randomizer", 0, RANDOMIZER_LEN)];
        for kappa in 0..K {
            fields.push(("FORS secret", 16 + 160 * kappa, N));
            for level in 0..A {
                fields.push(("FORS path", 32 + 160 * kappa + 16 * level, N));
            }
        }
        fields.push(("counter", 3216, COUNTER_LEN));
        fields.extend((0..V).map(|i| ("WOTS value", 3220 + 16 * i, N)));
        fields.extend((0..H).map(|level| ("auth path", 4244 + 16 * level, N)));
        fields
    }

    /// Pins the signature encoding: each field at the offset of the f spec's section 11 row, back to back.
    #[test]
    fn signature_layout() {
        let fields = field_offsets();
        assert_eq!(fields.len(), 1 + K * (1 + A) + 1 + V + H);
        let mut end = 0;
        for &(what, offset, len) in &fields {
            assert_eq!(offset, end, "{what} at {offset}");
            end = offset + len;
        }
        assert_eq!(end, SIG_SIZE);
        // Distinct values in every field (an odd multiplier is a bijection mod 2^128).
        let value = |i: usize| -> Digest {
            ((i as u128 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835)).to_le_bytes()
        };
        let sig = Signature {
            randomizer: value(0),
            fors: ForsOpening {
                secrets: std::array::from_fn(|kappa| value(1 + kappa * (1 + A))),
                paths: std::array::from_fn(|kappa| std::array::from_fn(|level| value(2 + kappa * (1 + A) + level))),
            },
            counter: 0x0403_0201,
            wots: std::array::from_fn(|i| value(1000 + i)),
            path: std::array::from_fn(|level| value(2000 + level)),
        };
        let bytes = sig.to_bytes();
        assert_eq!(bytes[0..16], sig.randomizer);
        for kappa in 0..K {
            assert_eq!(bytes[16 + 160 * kappa..][..16], sig.fors.secrets[kappa]);
            for level in 0..A {
                assert_eq!(bytes[32 + 160 * kappa + 16 * level..][..16], sig.fors.paths[kappa][level]);
            }
        }
        assert_eq!(bytes[3216..3220], [1, 2, 3, 4], "counter, little endian");
        for i in 0..V {
            assert_eq!(bytes[3220 + 16 * i..][..16], sig.wots[i]);
        }
        for level in 0..H {
            assert_eq!(bytes[4244 + 16 * level..][..16], sig.path[level]);
        }
        assert_eq!(Signature::from_bytes(&bytes).unwrap(), sig);
    }

    #[test]
    fn tampered_signatures_are_rejected() {
        let (sk, pk) = key_gen(&seed(9), 10);
        let m: Message = std::array::from_fn(|i| i as u8);
        let sig = sign(&sk, &m);
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        let bytes = sig.to_bytes();
        for len in [0, 32, SIG_SIZE - 1, SIG_SIZE + 1, SIG_SIZE + 32] {
            let mut b = bytes.clone();
            b.resize(len, 0);
            assert!(Signature::from_bytes(&b).is_none(), "length {len}");
        }
        // Other counters: never accepted, and some encode no codeword at all. An inadmissible one stops the
        // verification after the digest, FORS and the encoding (the f spec): 182 calls, 186 permutations.
        let mut inadmissible = 0;
        for delta in 1..=40u32 {
            let mut bad = sig.clone();
            bad.counter = sig.counter.wrapping_add(delta);
            let before = work();
            match verify(&pk, &m, &bad) {
                Err(VerifyError::InadmissibleEncoding) => {
                    inadmissible += 1;
                    assert_eq!(work() - before, Work { calls: 182, permutations: 186 }, "counter + {delta}");
                }
                r => assert_eq!(r, Err(VerifyError::RootMismatch), "counter + {delta}"),
            }
        }
        assert!(inadmissible > 30, "{inadmissible} of 40 altered counters were inadmissible");
        let mut cases: Vec<(&str, Signature)> = Vec::new();
        let mut bad = sig.clone();
        bad.path[7][3] ^= 1;
        cases.push(("auth path", bad));
        let mut bad = sig.clone();
        bad.path[H - 1][0] ^= 0x80;
        cases.push(("top of the auth path", bad));
        let mut bad = sig.clone();
        bad.wots[11][5] ^= 4;
        cases.push(("WOTS value", bad));
        let mut bad = sig.clone();
        bad.fors.paths[2][A - 1][0] ^= 1;
        cases.push(("FORS path", bad));
        let mut bad = sig.clone();
        bad.fors.secrets[K - 1][N - 1] ^= 1;
        cases.push(("FORS secret", bad));
        let mut bad = sig.clone();
        bad.randomizer[0] ^= 1;
        cases.push(("randomizer", bad));
        for (what, bad) in cases {
            assert!(verify(&pk, &m, &bad).is_err(), "tampered {what} accepted");
            assert_eq!(Signature::from_bytes(&bad.to_bytes()).unwrap(), bad);
        }
        // One flipped bit in every field of the encoding, at a byte and bit that move from field to field.
        for (f, &(what, offset, len)) in field_offsets().iter().enumerate() {
            let mut b = bytes.clone();
            b[offset + f % len] ^= 1 << (f % 8);
            let bad = Signature::from_bytes(&b).unwrap();
            assert!(verify(&pk, &m, &bad).is_err(), "tampered {what} at byte {offset} accepted");
        }
        let mut other = pk;
        other.public_param[0] ^= 1;
        assert!(verify(&other, &m, &sig).is_err(), "another public parameter");
        let mut other = pk;
        other.root[N - 1] ^= 1;
        assert_eq!(verify(&other, &m, &sig), Err(VerifyError::RootMismatch), "another root");
    }

    /// Pins the key and the signature bytes of one small pruned key, so that a change to
    /// the addresses, the hash inputs or the serialization cannot pass unnoticed.
    ///
    /// The public key is the one upstream's `known_answer` pins (keccak branch, same seed and `b`), and leanSphincs-S's:
    /// at `h = 26` the key depends on neither the FORS parameters, nor `T`, nor the encoding. The signature is this
    /// crate's own.
    #[test]
    fn known_answer() {
        let (sk, pk) = key_gen(&seed(1), 11);
        let m: Message = std::array::from_fn(|i| (7 * i) as u8);
        let sig = sign(&sk, &m);
        let digest = keccak256(&sig.to_bytes());
        assert_eq!(hex(&pk.to_bytes()), "63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00");
        assert_eq!(hex(&digest), "5e127f8e8428c845624cfb0205d78398c078956ede0136300d0c99d87e4702db");
        assert_eq!(sig.counter, 5553);
    }

    #[test]
    fn a_randomizer_attempt_costs_one_call() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let before = work();
        let base = randomizer_base(&pp, &seed(2), &m);
        assert_eq!(work() - before, Work { calls: 1, permutations: 1 }, "R_0, once per message");
        for i in 0..4 {
            let before = work();
            let index = digest_index(&pp, &randomizer(&base, i), &m);
            assert_eq!(work() - before, Work { calls: 1, permutations: 1 });
            assert_eq!(index, message_digest(&pp, &randomizer(&base, i), &m).0);
        }
    }

    /// Pins the byte order of the randomizer derivation and of the digest, and the addition.
    #[test]
    fn randomizer_and_digest_inputs() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let base = randomizer_base(&pp, &seed(2), &m);
        let input = [&pp[..], &address(&tweak(TWEAK_RANDOMIZER, 0, 0)), &seed(2), &m].concat();
        assert_eq!(input.len(), 96);
        assert_eq!(base[..], keccak256(&input)[..N]);
        assert_eq!(randomizer(&base, 0), base);
        assert_eq!(randomizer(&[0xff; N], 2), {
            let mut wrapped = [0u8; N];
            wrapped[0] = 1;
            wrapped
        });
        let mut carry = [0u8; N];
        carry[0] = 0xff;
        assert_eq!(randomizer(&carry, 1)[..2], [0, 1], "little endian");
        let mut long_carry = [0xffu8; N];
        long_carry[N - 1] = 0;
        let mut expected = [0u8; N];
        expected[N - 1] = 1;
        assert_eq!(randomizer(&long_carry, 1), expected, "the carry runs through all 16 bytes");
        let rho = randomizer(&base, 7);
        let input = [&pp[..], &address(&tweak(TWEAK_MSG, 0, 0)), &m, &rho].concat();
        assert_eq!(input.len(), 80, "one call: P | address | m | rho");
        assert_eq!(digest_block(&pp, &rho, &m), keccak256(&input));
    }

    /// Pins where the digest's fields are (the f spec's section 5 row): seven 9-bit FORS indices in each of words 0 and
    /// 1, six in word 2 (bits 0..54), the 26-bit leaf index in word 3, and no other bit read.
    #[test]
    fn digest_fields() {
        let (pp, m, rho) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN], [7u8; N]);
        let d = digest_block(&pp, &rho, &m);
        let word = |w: usize| u64::from_le_bytes(d[8 * w..][..8].try_into().unwrap());
        let (index, fors) = message_digest(&pp, &rho, &m);
        assert_eq!(index, word(3) & ((1 << 26) - 1));
        for (kappa, &value) in fors.iter().enumerate() {
            let expected = word(kappa / 7) >> (9 * (kappa % 7)) & 0x1ff;
            assert_eq!(u64::from(value), expected, "FORS index {kappa}");
        }
        // Bit `i` of the 256-bit little-endian digest: which field reads it, if any.
        let reader = |i: usize| -> Option<(usize, usize)> {
            let (w, bit) = (i / 64, i % 64);
            match w {
                3 => (bit < H).then_some((K, bit)),
                _ if bit < 63 && 7 * w + bit / 9 < K => Some((7 * w + bit / 9, bit % 9)),
                _ => None,
            }
        };
        assert_eq!((0..256).filter(|&i| reader(i).is_some()).count(), DIGEST_BITS);
        // Word 2 holds kappa = 14..19 in its bits 0..54; bit 63 of words 0 and 1 and bits 54..64 of word 2 are unread.
        assert_eq!((128..192).filter(|&i| reader(i).is_some()).count(), 54);
        assert!([63, 127].iter().all(|&i| reader(i).is_none()) && reader(126) == Some((13, 8)));
        for i in 0..256 {
            let mut one = [0u8; 32];
            one[i / 8] = 1 << (i % 8);
            let (index, fors) = (index_of_block(&one), fors_indices_of_block(&one));
            let mut expected = ([0u32; K], 0u64);
            match reader(i) {
                Some((K, bit)) => expected.1 = 1 << bit,
                Some((kappa, bit)) => expected.0[kappa] = 1 << bit,
                None => {}
            }
            assert_eq!((fors, index), expected, "digest bit {i}");
        }
    }

    /// Pins the encoding's input, `P | A(enc, 0, e) | tops | counter` (spec section 6), and its costs: one call of 5
    /// permutations for the verifier, and 4 permutations once plus one call and 1 permutation per counter for the
    /// signer. (Upstream's test of the same name, keccak branch, at k = 20: 676 bytes instead of 804.)
    #[test]
    fn encoding_absorbs_the_tops_and_the_counter() {
        let pp = [3u8; PUBLIC_PARAM_LEN];
        let tops: ForsTops = std::array::from_fn(|kappa| std::array::from_fn(|half| [(2 * kappa + half) as u8; N]));
        let tops_bytes = tops.as_flattened().as_flattened();
        assert_eq!(tops_bytes.len(), 640);
        assert_eq!(tops_bytes[16 * 3..16 * 4], [3u8; N], "top_{{1,1}} is the fourth value");
        let input = [&pp[..], &address(&tweak(TWEAK_ENC, 0, 77)), tops_bytes, &5u32.to_le_bytes()].concat();
        assert_eq!(input.len(), ENCODING_INPUT_LEN);
        let expected = codeword(keccak256(&input)[..N].try_into().unwrap());
        let before = work();
        assert_eq!(encode(&pp, 77, &tops, 5), expected);
        assert_eq!(work() - before, Work { calls: 1, permutations: 5 });
        let before = work();
        let state = encoding_midstate(&pp, 77, &tops);
        assert_eq!(work() - before, Work { calls: 0, permutations: 4 }, "the whole blocks of the tops, once");
        let before = work();
        assert_eq!(encode_from(&state, 5), expected);
        assert_eq!(work() - before, Work { calls: 1, permutations: 1 }, "one permutation per counter");
        // The least admissible counter, found from the midstate, is the least `c` whose one-pass hash is a codeword.
        let (c, x) = wots_encode(&pp, 77, &tops).unwrap();
        let one_pass = |c: u32| {
            let input = [&pp[..], &address(&tweak(TWEAK_ENC, 0, 77)), tops_bytes, &c.to_le_bytes()].concat();
            codeword(keccak256(&input)[..N].try_into().unwrap())
        };
        assert_eq!(one_pass(c), Some(x));
        assert!((0..c).all(|c| one_pass(c).is_none()), "counter {c} is the least");
    }

    /// `P[sum = 122] = 6.38e-4`: about 1,566 tries (the f spec's section 1 row).
    #[test]
    fn wots_encoding_takes_about_1566_tries() {
        let pp = [7u8; PUBLIC_PARAM_LEN];
        let tries: u64 =
            (0..64u32).map(|e| u64::from(wots_encode(&pp, e, &[[[e as u8; N]; 2]; K]).unwrap().0) + 1).sum();
        let mean = tries as f64 / 64.0;
        assert!((400.0..6000.0).contains(&mean), "mean tries {mean}");
    }

    /// One WOTS+C signature's encoding search: 4 permutations for the fixed part, then one call and one permutation per
    /// counter tried.
    #[test]
    fn wots_encoding_search_costs() {
        let pp = [9u8; PUBLIC_PARAM_LEN];
        let tops: ForsTops = [[[0x42; N]; 2]; K];
        let before = work();
        let (c, _) = wots_encode(&pp, 5, &tops).unwrap();
        let tries = u64::from(c) + 1;
        assert_eq!(work() - before, Work { calls: tries, permutations: 4 + tries });
    }
}
