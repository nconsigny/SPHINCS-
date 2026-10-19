//! `Th`, the address that names every hash call, and the keccak256 call and Keccak-f permutation counters.

use std::cell::Cell;
use std::ops::{Add, Sub};

use tiny_keccak::{Hasher, Keccak};

use crate::*;

pub const ADDRESS_LEN: usize = 16;

// Hash types (low five bits of the last byte of the address).
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_ENC: u8 = 4;
pub const TWEAK_PARAMETER: u8 = 5;
pub const TWEAK_RANDOMIZER: u8 = 7;
pub const TWEAK_FTS_PRF: u8 = 8;
pub const TWEAK_FTS_LEAF: u8 = 9;
pub const TWEAK_FTS_NODE: u8 = 10;
// Type 11 (the former FORS key hash) is unused: the encoding absorbs the FORS tops.
pub const TWEAK_MSG: u8 = 12;
/// A pruned key's surrogate siblings (the kept subtree's position comes from the low bits of `P`).
pub const TWEAK_SURROGATE: u8 = 13;

/// The address of a hash call: its type, a chain step, and two fields, `hi < 2^24` and `lo`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Tweak {
    t: u8,
    step: u8,
    hi: u32,
    lo: u32,
}

pub fn tweak(t: u8, hi: u32, lo: u32) -> Tweak {
    debug_assert!(t < 32 && hi < 1 << 24);
    Tweak { t, step: 0, hi, lo }
}

impl Tweak {
    /// The same address at chain step `step < 8`.
    pub fn step(self, step: usize) -> Self {
        debug_assert!(step < 8);
        Self { step: step as u8, ..self }
    }
}

/// The 16 bytes that follow `P` in a hash input: `[lo:4 | hi:3 | t + 32 step:1 | 0^8]`, the fields little
/// endian. With `P` they fill one 32-byte EVM word, so every payload starts word-aligned.
pub fn address(tw: &Tweak) -> [u8; ADDRESS_LEN] {
    let mut out = [0u8; ADDRESS_LEN];
    out[..4].copy_from_slice(&tw.lo.to_le_bytes());
    out[4..7].copy_from_slice(&tw.hi.to_le_bytes()[..3]);
    out[7] = tw.t | tw.step << 5;
    out
}

/// Ethereum's Keccak-256 (original `0x01` padding, the EVM `KECCAK256` opcode), not FIPS 202 SHA3-256. Not
/// counted: tests use it to recompute hash inputs by hand.
pub fn keccak256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Keccak::v256();
    hasher.update(data);
    let mut out = [0u8; 32];
    hasher.finalize(&mut out);
    out
}

/// The sponge rate of keccak256 in bytes: `1600 - 2 * 256` bits.
pub const RATE: usize = 136;

/// Keccak-f permutations of one keccak256 call over `len` input bytes: `len / 136 + 1`. The padding takes at least one
/// byte, so an input that fills its last block exactly pays one more permutation for the padding alone.
pub const fn blocks(len: usize) -> u64 {
    (len / RATE + 1) as u64
}

/// A hasher that has absorbed `P | address`.
fn start(pp: &PublicParam, tw: &Tweak) -> Keccak {
    let mut hasher = Keccak::v256();
    hasher.update(pp);
    hasher.update(&address(tw));
    hasher
}

fn finish(hasher: Keccak) -> [u8; 32] {
    let mut out = [0u8; 32];
    hasher.finalize(&mut out);
    out
}

thread_local! {
    static KECCAK_CALLS: Cell<u64> = const { Cell::new(0) };
    static PERMUTATIONS: Cell<u64> = const { Cell::new(0) };
}

/// keccak256 calls this thread has spent in [`th`], [`th_pair`], [`th_digests`], [`th_full`] and
/// [`Midstate::finish`], plus those of the worker threads of [`par_map`] calls it made.
pub fn keccak_calls() -> u64 {
    KECCAK_CALLS.with(Cell::get)
}

/// Keccak-f permutations of the same calls, counted as [`keccak_calls`] is: [`blocks`] per call, except that a
/// [`Midstate`] counts its whole blocks once and each [`Midstate::finish`] the rest.
pub fn permutations() -> u64 {
    PERMUTATIONS.with(Cell::get)
}

/// keccak256 calls and Keccak-f permutations together: what a computation spent is `work() - before`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Work {
    pub calls: u64,
    pub permutations: u64,
}

/// This thread's [`keccak_calls`] and [`permutations`].
pub fn work() -> Work {
    Work { calls: keccak_calls(), permutations: permutations() }
}

impl Add for Work {
    type Output = Work;

    fn add(self, other: Work) -> Work {
        Work { calls: self.calls + other.calls, permutations: self.permutations + other.permutations }
    }
}

impl Sub for Work {
    type Output = Work;

    fn sub(self, other: Work) -> Work {
        Work { calls: self.calls - other.calls, permutations: self.permutations - other.permutations }
    }
}

fn count(spent: Work) {
    KECCAK_CALLS.with(|c| c.set(c.get() + spent.calls));
    PERMUTATIONS.with(|c| c.set(c.get() + spent.permutations));
}

/// One keccak256 call over `len` input bytes.
fn count_call(len: usize) {
    count(Work { calls: 1, permutations: blocks(len) });
}

/// `Th(P, tw, payload)`: keccak256 of `P | address | payload`, truncated to its first 16 bytes.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    th_full(pp, tw, payload)[..N].try_into().unwrap()
}

/// Two secrets for one hash: the two 16-byte halves of the untruncated keccak256 of `P | address | payload`.
pub fn th_pair(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> [Digest; 2] {
    let out = th_full(pp, tw, payload);
    [out[..N].try_into().unwrap(), out[N..].try_into().unwrap()]
}

/// `Th` over a concatenation of digests: a Merkle node or a one-time leaf.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    count_call(PUBLIC_PARAM_LEN + ADDRESS_LEN + values.len() * N);
    let mut hasher = start(pp, tw);
    for value in values {
        hasher.update(value);
    }
    finish(hasher)[..N].try_into().unwrap()
}

/// The untruncated 32-byte keccak256 of `P | address | payload` (the message digest, and the two halves of [`th_pair`]).
pub fn th_full(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> [u8; 32] {
    count_call(PUBLIC_PARAM_LEN + ADDRESS_LEN + payload.len());
    let mut hasher = start(pp, tw);
    hasher.update(payload);
    finish(hasher)
}

/// The sponge state after the whole blocks of `P | address | fixed`, for inputs that differ only in what follows (the
/// WOTS+C encoding's counter). Every whole block of the fixed part is permuted, and counted, here, once; each
/// [`Midstate::finish`] is one keccak256 call and pays for the rest and the padding.
#[derive(Clone)]
pub struct Midstate {
    hasher: Keccak,
    /// The end of the fixed part that is not a whole block, in bytes.
    rest: usize,
}

impl Midstate {
    pub fn new(pp: &PublicParam, tw: &Tweak, fixed: &[&[u8]]) -> Self {
        let mut hasher = start(pp, tw);
        let mut len = PUBLIC_PARAM_LEN + ADDRESS_LEN;
        for part in fixed {
            hasher.update(part);
            len += part.len();
        }
        count(Work { calls: 0, permutations: (len / RATE) as u64 });
        Self { hasher, rest: len % RATE }
    }

    /// The untruncated 32-byte keccak256 of the input completed by `tail`.
    pub fn finish(&self, tail: &[u8]) -> [u8; 32] {
        count_call(self.rest + tail.len());
        let mut hasher = self.hasher.clone();
        hasher.update(tail);
        finish(hasher)
    }
}

/// The number of cores, which [`par_map`] uses.
pub fn available_threads() -> usize {
    std::thread::available_parallelism().map_or(1, usize::from)
}

/// `(0..n).map(f)` on every core, in order. The keccak256 calls and the permutations of the worker threads are added to
/// this thread's counts, so [`keccak_calls`] and [`permutations`] still see the whole computation.
pub fn par_map<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    par_map_on(available_threads(), n, f)
}

/// [`par_map`] on at most `threads` threads: contiguous runs of `n / threads` indices each.
pub fn par_map_on<T: Send>(threads: usize, n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let threads = threads.clamp(1, n.max(1));
    let chunk = n.div_ceil(threads).max(1);
    let f = &f;
    let (parts, spent): (Vec<Vec<T>>, Vec<Work>) = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..n)
            .step_by(chunk)
            .map(|first| {
                scope.spawn(move || {
                    let before = work();
                    let part: Vec<T> = (first..n.min(first + chunk)).map(f).collect();
                    (part, work() - before)
                })
            })
            .collect();
        workers.into_iter().map(|worker| worker.join().unwrap()).unzip()
    });
    count(spent.into_iter().fold(Work::default(), Work::add));
    parts.into_iter().flatten().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins the byte layout of the address and of a hash input (the spec's section 3 example).
    #[test]
    fn address_layout() {
        let tw = tweak(TWEAK_FTS_NODE, 0x123456, 0x89abcdef).step(5);
        assert_eq!(address(&tw), [0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xaa, 0, 0, 0, 0, 0, 0, 0, 0]);
        let pp: PublicParam = std::array::from_fn(|i| i as u8 + 1);
        let payload = [9u8; N];
        let mut input = pp.to_vec();
        input.extend_from_slice(&address(&tw));
        input.extend_from_slice(&payload);
        assert_eq!(th(&pp, &tw, &payload)[..], keccak256(&input)[..N]);
        assert_eq!(th_pair(&pp, &tw, &payload).as_flattened(), keccak256(&input));
        assert_eq!(th_full(&pp, &tw, &payload), keccak256(&input));
        assert_eq!(th_digests(&pp, &tw, &[payload]), th(&pp, &tw, &payload));
    }

    /// keccak256 is Ethereum's (0x01 padding), not SHA3-256.
    #[test]
    fn keccak_is_ethereum_keccak() {
        let hex: String = keccak256(b"").iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
    }

    /// A call over `len` bytes is `len / 136 + 1` permutations: a full last block pays one more for the padding.
    #[test]
    fn permutations_per_call() {
        let cases = [(0, 1), (1, 1), (RATE - 1, 1), (RATE, 2), (2 * RATE - 1, 2), (2 * RATE, 3), (452, 4), (1056, 8)];
        for (len, expected) in cases {
            assert_eq!(blocks(len), expected, "{len} bytes");
        }
    }

    /// Every `Th` form is one keccak256 call, whatever the payload length, and `blocks` of its input in permutations:
    /// 1 for every input up to 135 bytes, 8 for a one-time leaf's 1056.
    #[test]
    fn one_call_per_hash() {
        let (pp, tw) = ([1u8; PUBLIC_PARAM_LEN], tweak(TWEAK_LEAF, 0, 7));
        let before = work();
        th(&pp, &tw, &[]);
        th_pair(&pp, &tw, &[2u8; 32]);
        th_full(&pp, &tw, &[3u8; 48]);
        th_digests(&pp, &tw, &[[4u8; N]; V]);
        assert_eq!(work() - before, Work { calls: 4, permutations: 1 + 1 + 1 + 8 });
        let before = work();
        th_full(&pp, &tw, &[5u8; RATE - 32]);
        assert_eq!(work() - before, Work { calls: 1, permutations: 2 }, "a 136-byte input pays for its padding");
    }

    /// A midstate gives the same hash as one pass, and pays for each whole block once, whether or not the fixed part
    /// ends on a block boundary. Each finish is one call. (Upstream's `midstate_matches_one_pass`, keccak branch.)
    #[test]
    fn midstate_matches_one_pass() {
        let pp: PublicParam = std::array::from_fn(|i| 3 * i as u8);
        let tw = tweak(TWEAK_MSG, 1, 0);
        for fixed_len in [104, 120] {
            let (fixed, tail) = (vec![7u8; fixed_len], [9u8; 16]);
            let input = [&pp[..], &address(&tw), &fixed, &tail].concat();
            let before = work();
            let state = Midstate::new(&pp, &tw, &[&fixed]);
            assert_eq!(work() - before, Work { calls: 0, permutations: 1 }, "the first block");
            for _ in 0..3 {
                let before = work();
                assert_eq!(state.finish(&tail), keccak256(&input));
                assert_eq!(work() - before, Work { calls: 1, permutations: 1 }, "one permutation per tail");
            }
        }
    }

    /// The parallel map keeps the order, the calls and the permutations of its workers.
    #[test]
    fn par_map_keeps_order_and_counts() {
        let pp = [5u8; PUBLIC_PARAM_LEN];
        for n in [0usize, 1, 13, 100] {
            let before = work();
            let out = par_map(n, |j| th_digests(&pp, &tweak(TWEAK_NODE, 0, j as u32), &[[1; N]; 9]));
            assert_eq!(work() - before, Work { calls: n as u64, permutations: 2 * n as u64 });
            let expected: Vec<Digest> =
                (0..n).map(|j| th_digests(&pp, &tweak(TWEAK_NODE, 0, j as u32), &[[1; N]; 9])).collect();
            assert_eq!(out, expected);
        }
    }
}
