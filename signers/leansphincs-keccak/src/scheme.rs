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

/// The state of digest call `call` after `P | address(MSG, hi = call) | m`. With the randomizer the whole input is
/// 80 bytes, within one block, so grinding it costs one call and one permutation per attempt.
pub fn digest_midstate(pp: &PublicParam, m: &Message, call: u32) -> Midstate {
    Midstate::new(pp, &tweak(TWEAK_MSG, call, 0), &[m])
}

/// One call of the message digest, `P | address(MSG, hi = call) | m | rho`, untruncated. `P` binds the key, so the
/// root is not hashed.
pub fn digest_block(pp: &PublicParam, rho: &Randomizer, m: &Message, call: u32) -> [u8; 32] {
    digest_midstate(pp, m, call).finish(rho)
}

/// The leaf index alone, from the digest's first call (what grinding computes).
pub fn digest_index(pp: &PublicParam, rho: &Randomizer, m: &Message) -> u64 {
    index_of_block(&digest_block(pp, rho, m, 0))
}

/// The leaf index: the low `h` bits of the last 16 bytes of call 0 (its 64-bit word 2, bytes 16..24).
pub fn index_of_block(d0: &[u8; 32]) -> u64 {
    u64::from_le_bytes(d0[16..24].try_into().unwrap()) & ((1 << H) - 1)
}

/// FORS indices per digest call: six in each of the two 64-bit words of its first 16 bytes.
const INDICES_PER_CALL: usize = 12;

// Six 10-bit fields fill bits 0..60 of a word, two words of each call hold twelve indices, and the two calls hold k.
const _: () = assert!(6 * A <= 64 && INDICES_PER_CALL * DIGEST_CALLS == K && H <= 64);

/// The leaf index and the `k` FORS indices of the two digest calls. No field lies across two 64-bit words: FORS index
/// `kappa` is in call `kappa / 12`, word `(kappa % 12) / 6` of its first 16 bytes, at bit `a * (kappa % 6)`; the leaf
/// index is in the last 16 bytes of call 0. Words 2 and 3 of call 1, word 3 of call 0 and the top 4 bits of every
/// FORS word are not read.
pub fn split_digest(calls: &[[u8; 32]; DIGEST_CALLS]) -> (u64, [u32; K]) {
    let fors_index = |kappa: usize| {
        let r = kappa % INDICES_PER_CALL;
        let word = &calls[kappa / INDICES_PER_CALL][8 * (r / 6)..][..8];
        (u64::from_le_bytes(word.try_into().unwrap()) >> (A * (r % 6)) & ((1 << A) - 1)) as u32
    };
    (index_of_block(&calls[0]), std::array::from_fn(fors_index))
}

/// The message digest, from two calls, read as the leaf index and the `k` FORS indices ([`split_digest`]).
pub fn message_digest(pp: &PublicParam, rho: &Randomizer, m: &Message) -> (u64, [u32; K]) {
    split_digest(&[digest_block(pp, rho, m, 0), digest_block(pp, rho, m, 1)])
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
    // The digest's fixed part is absorbed once, and the randomizers are `R_0 + i`: an attempt costs one call and one
    // permutation (call 0 of the digest, which holds the leaf index).
    let (base, digests) = (randomizer_base(pp, master, m), digest_midstate(pp, m, 0));
    let rho =
        (0u32..).map(|i| randomizer(&base, i)).find(|rho| contains(index_of_block(&digests.finish(rho)))).unwrap();
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

    // ---- Upstream's tests (crates/sphincs/src/scheme.rs, keccak branch), verbatim but for `keccak::hash`, which is
    // ---- `keccak256` here.

    #[test]
    fn pruned_sign_verify_and_costs() {
        for b in [3usize, 12] {
            let before = permutations();
            let (sk, pk) = key_gen(&seed(b as u8), b);
            let keygen = permutations() - before;
            // P, the kept subtree (232 per WOTS leaf plus the nodes), and a derivation and a node per surrogate.
            assert_eq!(keygen, 1 + (1u64 << b) * 232 + ((1u64 << b) - 1) + 2 * (H - b) as u64);
            for t in 0..3u8 {
                let m: Message = std::array::from_fn(|i| t ^ i as u8);
                let sig = sign(&sk, &m);
                let bytes = sig.to_bytes();
                assert_eq!(bytes.len(), SIG_SIZE);
                assert_eq!(Signature::from_bytes(&bytes).unwrap(), sig);
                let before = permutations();
                assert_eq!(verify(&pk, &m, &sig), Ok(()));
                assert_eq!(permutations() - before, VERIFY_PERMUTATIONS, "verification is constant");
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

    #[test]
    fn tampered_signatures_are_rejected() {
        let (sk, pk) = key_gen(&seed(9), 10);
        let m: Message = std::array::from_fn(|i| i as u8);
        let sig = sign(&sk, &m);
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        let bytes = sig.to_bytes();
        for len in [0, SIG_SIZE - 1, SIG_SIZE + 1] {
            let mut b = bytes.clone();
            b.resize(len, 0);
            assert!(Signature::from_bytes(&b).is_none(), "length {len}");
        }
        // Other counters: never accepted, and some encode no codeword at all.
        let mut inadmissible = 0;
        for delta in 1..=40u32 {
            let mut bad = sig.clone();
            bad.counter = sig.counter.wrapping_add(delta);
            match verify(&pk, &m, &bad) {
                Err(VerifyError::InadmissibleEncoding) => inadmissible += 1,
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
        let mut other = pk;
        other.public_param[0] ^= 1;
        assert!(verify(&other, &m, &sig).is_err(), "another public parameter");
    }

    /// Pins the key and the signature bytes of one small pruned key, so that a change to
    /// the addresses, the hash inputs or the serialization cannot pass unnoticed.
    #[test]
    fn known_answer() {
        let (sk, pk) = key_gen(&seed(1), 11);
        let m: Message = std::array::from_fn(|i| (7 * i) as u8);
        let sig = sign(&sk, &m);
        let digest = keccak256(&sig.to_bytes());
        assert_eq!(hex(&pk.to_bytes()), "63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00");
        assert_eq!(hex(&digest), "9a21b6bc61d6ba500b4d67809912c1424be1f58486eda144e4ef70afd01cf94d");
        assert_eq!(sig.counter, 1176);
    }

    #[test]
    fn a_randomizer_attempt_costs_one_permutation() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let before = permutations();
        let (base, digests) = (randomizer_base(&pp, &seed(2), &m), digest_midstate(&pp, &m, 0));
        assert_eq!(permutations() - before, 1, "R_0, once per message; the digest's fixed part fills no block");
        for i in 0..4 {
            let before = permutations();
            let index = index_of_block(&digests.finish(&randomizer(&base, i)));
            assert_eq!(permutations() - before, 1);
            assert_eq!(index, digest_index(&pp, &randomizer(&base, i), &m));
        }
    }

    /// Pins the byte order of the randomizer derivation and of the digest, and the addition.
    #[test]
    fn randomizer_and_digest_inputs() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let base = randomizer_base(&pp, &seed(2), &m);
        let input = [&pp[..], &address(&tweak(TWEAK_RANDOMIZER, 0, 0)), &seed(2), &m].concat();
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
        let rho = randomizer(&base, 7);
        let input = [&pp[..], &address(&tweak(TWEAK_MSG, 1, 0)), &m, &rho].concat();
        assert_eq!(input.len(), 80, "one block");
        assert_eq!(digest_block(&pp, &rho, &m, 1), keccak256(&input));
    }

    /// Pins where the digest's fields are: six FORS indices in each of the first two 64-bit words of
    /// a call, the leaf index in the third word of call 0.
    #[test]
    fn digest_fields() {
        let (pp, m, rho) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN], [7u8; N]);
        let calls = [digest_block(&pp, &rho, &m, 0), digest_block(&pp, &rho, &m, 1)];
        let word = |call: usize, w: usize| u64::from_le_bytes(calls[call][8 * w..][..8].try_into().unwrap());
        let (index, fors) = message_digest(&pp, &rho, &m);
        assert_eq!(index, word(0, 2) % (1 << H));
        for (kappa, &value) in fors.iter().enumerate() {
            let expected = word(kappa / 12, kappa % 12 / 6) >> (A * (kappa % 6)) & 1023;
            assert_eq!(u64::from(value), expected, "FORS index {kappa}");
        }
    }

    /// Pins the encoding's input, `P | A(enc, 0, e) | tops | counter`, and its costs: 6 permutations
    /// for the verifier, and 5 once plus 1 per counter for the signer.
    #[test]
    fn encoding_absorbs_the_tops_and_the_counter() {
        let pp = [3u8; PUBLIC_PARAM_LEN];
        let tops: ForsTops = std::array::from_fn(|kappa| std::array::from_fn(|half| [(2 * kappa + half) as u8; N]));
        let input =
            [&pp[..], &address(&tweak(TWEAK_ENC, 0, 77)), tops.as_flattened().as_flattened(), &5u32.to_le_bytes()]
                .concat();
        assert_eq!(input.len(), 804);
        let expected = codeword(keccak256(&input)[..N].try_into().unwrap());
        let before = permutations();
        assert_eq!(encode(&pp, 77, &tops, 5), expected);
        assert_eq!(permutations() - before, 6);
        let before = permutations();
        let state = encoding_midstate(&pp, 77, &tops);
        assert_eq!(permutations() - before, 5, "the whole blocks of the tops, once");
        let before = permutations();
        assert_eq!(encode_from(&state, 5), expected);
        assert_eq!(permutations() - before, 1, "one permutation per counter");
    }

    #[test]
    fn wots_encoding_takes_about_829_tries() {
        let pp = [7u8; PUBLIC_PARAM_LEN];
        let tries: u64 =
            (0..200u32).map(|e| u64::from(wots_encode(&pp, e, &[[[e as u8; N]; 2]; K]).unwrap().0) + 1).sum();
        let mean = tries as f64 / 200.0;
        assert!((400.0..1600.0).contains(&mean), "mean tries {mean}");
    }

    // ---- This crate's tests: keccak256 calls besides permutations, the spec's offsets and early exit, every digest bit,
    // ---- every signature field (as the leanSphincs-S crate tests them, at these parameters).

    /// The keygen, signing and verification work in keccak256 calls and in permutations.
    #[test]
    fn keygen_sign_and_verify_work() {
        // P, the kept subtree (per WOTS leaf: 32 secret pairs, 64 * 3 chain steps and the leaf, plus the nodes), and
        // a derivation and a node per surrogate. Every call is one permutation but the leaf's, whose 1056-byte input
        // takes 8.
        let keygen = |b: usize, leaf: u64| {
            1 + (1u64 << b) * (V as u64 / 2 + 192 + leaf) + ((1u64 << b) - 1) + 2 * (H - b) as u64
        };
        let keygen_work = |b: usize| Work { calls: keygen(b, 1), permutations: keygen(b, 8) };
        // A full key, 2^26 * 226 calls (about 1.52e10), and 2^26 * 233 permutations: sphincs-art's 15.6B (its keygen
        // figure, 15,636,365,313, counts one node more than a 2^26-leaf tree has). The key does not depend on the FORS
        // parameters, so these are leanSphincs-S's figures.
        assert_eq!(keygen_work(H), Work { calls: 15_166_603_264, permutations: 15_636_365_312 });
        // Signing a message with the tree in memory: R_0, the grind's attempts, the two digest calls, every FORS leaf
        // (K * 512 secret pairs and K * 1024 leaves) and node (K * 1022, no roots), the K opened secrets derived again,
        // the encoding (5 permutations once, then one call and one permutation per counter tried), the 32 WOTS secret
        // pairs and the T = 120 chain steps to the codeword.
        let fors = (K * (FORS_LEAVES / 2 + FORS_LEAVES + FORS_LEAVES - 2) + K) as u64;
        assert_eq!(fors, 61_416);
        for b in [7usize, 9] {
            let before = work();
            let (sk, pk) = key_gen(&seed(20 + b as u8), b);
            assert_eq!(work() - before, keygen_work(b), "b = {b}");
            for t in 0..2u8 {
                let m: Message = std::array::from_fn(|i| t.wrapping_mul(13) ^ i as u8);
                let before = work();
                let sig = sign(&sk, &m);
                let spent = work() - before;
                let base = randomizer_base(&pk.public_param, &sk.master, &m);
                let attempts = u128::from_le_bytes(sig.randomizer).wrapping_sub(u128::from_le_bytes(base)) as u64 + 1;
                let tries = u64::from(sig.counter) + 1;
                let calls = 1 + attempts + DIGEST_CALLS as u64 + fors + tries + V as u64 / 2 + TARGET_SUM as u64;
                assert_eq!(spent, Work { calls, permutations: calls + 5 }, "b = {b}, message {t}");
                let before = work();
                assert_eq!(verify(&pk, &m, &sig), Ok(()));
                let spent = work() - before;
                assert_eq!(spent, Work { calls: VERIFY_KECCAK_CALLS, permutations: VERIFY_PERMUTATIONS }, "constant");
                assert_eq!(spent, Work { calls: 342, permutations: 354 });
            }
        }
    }

    /// The byte offset and length of every field of the encoding (the spec's section 11 offsets), in order.
    fn field_offsets() -> Vec<(&'static str, usize, usize)> {
        let mut fields = vec![("randomizer", 0, RANDOMIZER_LEN)];
        for kappa in 0..K {
            fields.push(("FORS secret", 16 + 176 * kappa, N));
            for level in 0..A {
                fields.push(("FORS path", 32 + 176 * kappa + 16 * level, N));
            }
        }
        fields.push(("counter", 4240, COUNTER_LEN));
        fields.extend((0..V).map(|i| ("WOTS value", 4244 + 16 * i, N)));
        fields.extend((0..H).map(|level| ("auth path", 5268 + 16 * level, N)));
        fields
    }

    /// Pins the signature encoding: each field at the spec's offset, back to back.
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
            assert_eq!(bytes[16 + 176 * kappa..][..16], sig.fors.secrets[kappa]);
            for level in 0..A {
                assert_eq!(bytes[32 + 176 * kappa + 16 * level..][..16], sig.fors.paths[kappa][level]);
            }
        }
        assert_eq!(bytes[4240..4244], [1, 2, 3, 4], "counter, little endian");
        for i in 0..V {
            assert_eq!(bytes[4244 + 16 * i..][..16], sig.wots[i]);
        }
        for level in 0..H {
            assert_eq!(bytes[5268 + 16 * level..][..16], sig.path[level]);
        }
        assert_eq!(Signature::from_bytes(&bytes).unwrap(), sig);
    }

    /// One flipped bit in every field of the encoding fails the signature; an inadmissible counter stops the
    /// verification after the digest, FORS and the encoding: 243 calls, 248 permutations.
    #[test]
    fn every_field_is_bound() {
        let (sk, pk) = key_gen(&seed(9), 10);
        let m: Message = std::array::from_fn(|i| i as u8);
        let sig = sign(&sk, &m);
        let bytes = sig.to_bytes();
        for len in [32, SIG_SIZE + 32] {
            let mut b = bytes.clone();
            b.resize(len, 0);
            assert!(Signature::from_bytes(&b).is_none(), "length {len}");
        }
        let mut inadmissible = 0;
        for delta in 1..=40u32 {
            let mut bad = sig.clone();
            bad.counter = sig.counter.wrapping_add(delta);
            let before = work();
            if verify(&pk, &m, &bad) == Err(VerifyError::InadmissibleEncoding) {
                inadmissible += 1;
                assert_eq!(work() - before, Work { calls: 243, permutations: 248 }, "counter + {delta}");
            }
        }
        assert!(inadmissible > 30, "{inadmissible} of 40 altered counters were inadmissible");
        // At a byte and bit that move from field to field.
        for (f, &(what, offset, len)) in field_offsets().iter().enumerate() {
            let mut b = bytes.clone();
            b[offset + f % len] ^= 1 << (f % 8);
            let bad = Signature::from_bytes(&b).unwrap();
            assert!(verify(&pk, &m, &bad).is_err(), "tampered {what} at byte {offset} accepted");
        }
        let mut other = pk;
        other.root[N - 1] ^= 1;
        assert_eq!(verify(&other, &m, &sig), Err(VerifyError::RootMismatch), "another root");
        let mut long_carry = [0xffu8; N];
        long_carry[N - 1] = 0;
        let mut expected = [0u8; N];
        expected[N - 1] = 1;
        assert_eq!(randomizer(&long_carry, 1), expected, "the carry runs through all 16 bytes");
    }

    /// Every one of the 512 bits of the two digest calls: which field reads it, if any. The fields read 266 bits:
    /// `26 + 24 * 10`.
    #[test]
    fn digest_bits() {
        // Bit `i` of the two calls as one 512-bit little-endian string: (field, bit), the field `K` being the leaf index.
        let reader = |i: usize| -> Option<(usize, usize)> {
            let (call, w, bit) = (i / 256, i % 256 / 64, i % 64);
            match (call, w) {
                (0, 2) => (bit < H).then_some((K, bit)),
                (_, 0 | 1) if bit < 6 * A => Some((12 * call + 6 * w + bit / A, bit % A)),
                _ => None,
            }
        };
        assert_eq!((0..512).filter(|&i| reader(i).is_some()).count(), DIGEST_BITS);
        for i in 0..512 {
            let mut calls = [[0u8; 32]; DIGEST_CALLS];
            calls[i / 256][i % 256 / 8] = 1 << (i % 8);
            let mut expected = (0u64, [0u32; K]);
            match reader(i) {
                Some((K, bit)) => expected.0 = 1 << bit,
                Some((kappa, bit)) => expected.1[kappa] = 1 << bit,
                None => {}
            }
            assert_eq!(split_digest(&calls), expected, "digest bit {i}");
        }
        // The grind reads call 0 only.
        let (pp, m, rho) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN], [7u8; N]);
        assert_eq!(digest_index(&pp, &rho, &m), message_digest(&pp, &rho, &m).0);
        assert_ne!(digest_block(&pp, &rho, &m, 0), digest_block(&pp, &rho, &m, 1), "the calls differ by their address");
    }

    /// A randomizer attempt is one keccak256 call, and the digest two: the midstate of `P | address | m` takes no
    /// whole block.
    #[test]
    fn digest_calls() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let before = work();
        let (base, digests) = (randomizer_base(&pp, &seed(2), &m), digest_midstate(&pp, &m, 0));
        assert_eq!(work() - before, Work { calls: 1, permutations: 1 }, "R_0 is one call; the midstate none");
        let before = work();
        digests.finish(&base);
        assert_eq!(work() - before, Work { calls: 1, permutations: 1 });
        let before = work();
        message_digest(&pp, &base, &m);
        assert_eq!(work() - before, Work { calls: 2, permutations: 2 });
        let input = [&pp[..], &address(&tweak(TWEAK_RANDOMIZER, 0, 0)), &seed(2), &m].concat();
        assert_eq!(input.len(), 96);
    }

    /// The encoding in calls, and its search: the least admissible counter found from the midstate is the least `c`
    /// whose one-pass hash is a codeword, after 5 permutations once and one call and one permutation per counter.
    #[test]
    fn encoding_search() {
        let pp = [3u8; PUBLIC_PARAM_LEN];
        let tops: ForsTops = std::array::from_fn(|kappa| std::array::from_fn(|half| [(2 * kappa + half) as u8; N]));
        let tops_bytes = tops.as_flattened().as_flattened();
        assert_eq!(tops_bytes.len(), 768);
        assert_eq!(tops_bytes[16 * 3..16 * 4], [3u8; N], "top_{{1,1}} is the fourth value");
        let before = work();
        encode(&pp, 77, &tops, 5);
        assert_eq!(work() - before, Work { calls: 1, permutations: 6 });
        let before = work();
        let (c, x) = wots_encode(&pp, 77, &tops).unwrap();
        let tries = u64::from(c) + 1;
        assert_eq!(work() - before, Work { calls: tries, permutations: 5 + tries });
        let one_pass = |c: u32| {
            let input = [&pp[..], &address(&tweak(TWEAK_ENC, 0, 77)), tops_bytes, &c.to_le_bytes()].concat();
            assert_eq!(input.len(), ENCODING_INPUT_LEN);
            codeword(keccak256(&input)[..N].try_into().unwrap())
        };
        assert_eq!(one_pass(c), Some(x));
        assert!((0..c).all(|c| one_pass(c).is_none()), "counter {c} is the least");
    }
}
