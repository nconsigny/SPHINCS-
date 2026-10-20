//! WOTS+C: `v = 64` chains of `2^w - 1 = 3` steps, and the target-sum code that replaces the
//! Winternitz checksum. A codeword is 64 chunks summing to `T = 120`; the signer searches the least
//! counter whose encoding is a codeword. The encoding hashes the FORS tops themselves, with the
//! counter last: there is no separate FORS key hash.

use crate::*;

/// The starts of the `v` chains of the one-time key at leaf `e`. One hash of the seed gives two of
/// them: chains `2 t` and `2 t + 1` are the two halves of the hash at address `t`.
pub fn wots_secrets(pp: &PublicParam, master: &MasterSecret, e: u32) -> [Digest; V] {
    let mut secrets = [[0u8; N]; V];
    for t in 0..V / 2 {
        let pair = th_pair(pp, &wots_secret_tweak(e, t), master);
        secrets[2 * t] = pair[0];
        secrets[2 * t + 1] = pair[1];
    }
    secrets
}

/// The address of the hash that gives the starts of chains `2 t` and `2 t + 1`.
pub fn wots_secret_tweak(e: u32, t: usize) -> Tweak {
    tweak(TWEAK_PRF, t as u32, e)
}

/// The tweak of the step of chain `i` (leaf `e`) that lands on position `to`, in `1..CHAIN_LEN`.
pub fn chain_tweak(e: u32, i: usize, to: usize) -> Tweak {
    debug_assert!((1..CHAIN_LEN).contains(&to));
    tweak(TWEAK_CHAIN, i as u32, e).step(to - 1)
}

/// `steps` chain steps of chain `i` from position `start`.
pub fn chain(pp: &PublicParam, e: u32, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    debug_assert!(start + steps < CHAIN_LEN);
    (start + 1..=start + steps).fold(value, |current, to| th(pp, &chain_tweak(e, i, to), &current))
}

/// The Merkle leaf of a one-time key: `Th` over its 64 chain ends.
pub fn wots_leaf_hash(pp: &PublicParam, e: u32, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &tweak(TWEAK_LEAF, 0, e), ends)
}

/// The encoding hash after its fixed part, `P | A(enc, 0, e) | tops` (800 bytes: 5 whole blocks).
/// The counter falls in the last block, so each counter costs one permutation.
pub fn encoding_midstate(pp: &PublicParam, e: u32, tops: &ForsTops) -> Midstate {
    Midstate::new(pp, &tweak(TWEAK_ENC, 0, e), &[tops.as_flattened().as_flattened()])
}

/// The codeword of counter `c` from the encoding's midstate, or `None` if its digest is not one.
pub fn encode_from(state: &Midstate, c: u32) -> Option<[u8; V]> {
    codeword(state.finish(&c.to_le_bytes())[..N].try_into().unwrap())
}

/// `Enc(P, e, tops, c)`: `Th(P, A(enc, 0, e), tops | c)` decoded, or `None` if it is not a codeword.
pub fn encode(pp: &PublicParam, e: u32, tops: &ForsTops, c: u32) -> Option<[u8; V]> {
    encode_from(&encoding_midstate(pp, e, tops), c)
}

/// The 128 digest bits as 64 chunks of 2 bits, little endian; a codeword if they sum to `T`.
pub fn codeword(digest: &Digest) -> Option<[u8; V]> {
    let d = u128::from_le_bytes(*digest);
    let x: [u8; V] = std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8);
    (x.iter().map(|&c| c as usize).sum::<usize>() == TARGET_SUM).then_some(x)
}

/// The least admissible counter and its codeword. Deterministic in its inputs, which keeps one
/// key to one codeword. The fixed part is absorbed once: each counter tried is one call and one permutation.
pub fn wots_encode(pp: &PublicParam, e: u32, tops: &ForsTops) -> Option<(u32, [u8; V])> {
    let state = encoding_midstate(pp, e, tops);
    (0..MAX_ENCODING_ATTEMPTS).find_map(|c| encode_from(&state, c as u32).map(|x| (c as u32, x)))
}

/// `Ots.sign` from the master secret: the counter and the chain value each chunk opens.
pub fn wots_sign(pp: &PublicParam, master: &MasterSecret, e: u32, tops: &ForsTops) -> Option<(u32, [Digest; V])> {
    let (c, x) = wots_encode(pp, e, tops)?;
    let secrets = wots_secrets(pp, master, e);
    let signature = std::array::from_fn(|i| chain(pp, e, i, 0, x[i] as usize, secrets[i]));
    Some((c, signature))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, or `None` if the counter is not admissible.
pub fn wots_recover(pp: &PublicParam, e: u32, tops: &ForsTops, c: u32, signature: &[Digest; V]) -> Option<Digest> {
    let x = encode(pp, e, tops, c)?;
    let ends = std::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, e, i, start, CHAIN_LEN - 1 - start, signature[i])
    });
    Some(wots_leaf_hash(pp, e, &ends))
}

/// The Merkle leaf of the one-time key at `e`, from the master secret: 32 secret pairs, `64 * 3` chain steps and the
/// leaf hash, [`WOTS_LEAF_CALLS`] keccak256 calls and [`WOTS_LEAF_PERMUTATIONS`] permutations.
pub fn wots_leaf(pp: &PublicParam, master: &MasterSecret, e: u32) -> Digest {
    wots_leaf_hash(pp, e, &wots_ends(pp, master, e))
}

/// keccak256 calls of [`wots_leaf`].
pub const WOTS_LEAF_CALLS: u64 = (V / 2 + V * (CHAIN_LEN - 1) + 1) as u64;
/// Keccak-f permutations of [`wots_leaf`]: one per secret pair and per chain step, 8 for the 1056-byte leaf input.
pub const WOTS_LEAF_PERMUTATIONS: u64 = (V / 2 + V * (CHAIN_LEN - 1)) as u64 + blocks(WOTS_LEAF_INPUT_LEN);

const _: () = assert!(WOTS_LEAF_CALLS == 225 && WOTS_LEAF_PERMUTATIONS == 232);

/// The chain ends of the one-time key at `e`, from the master secret.
pub fn wots_ends(pp: &PublicParam, master: &MasterSecret, e: u32) -> [Digest; V] {
    let secrets = wots_secrets(pp, master, e);
    std::array::from_fn(|i| chain(pp, e, i, 0, CHAIN_LEN - 1, secrets[i]))
}
