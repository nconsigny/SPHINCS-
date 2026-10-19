// SPDX-License-Identifier: MIT
// CREDIT: adapted from TomWambsgans/leanXMSS-leanSPHINCS-candidates (https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates,
// crates/sphincs on branch keccak), MIT OR Apache-2.0, Copyright (c) 2026 Tom Wambsgans, see LICENSE.upstream. That
// crate is in turn adapted from leanVM's SPHINCS crate (https://github.com/leanEthereum/leanVM, crates/sphincs), MIT OR
// Apache-2.0, Copyright (c) 2026 leanEthereum, under the same MIT terms.
// Re-parameterized to leanSphincs-S (docs/leanSphincs-S-keccak.md): one XMSS layer (d = 1) of height h = 26, plain
// FORS with k = 13 trees of height a = 12, WOTS+C with w = 4, 64 chains and target sum 128, and pruned keys (a kept
// subtree plus pseudorandom surrogate siblings). The construction is the keccak branch's: Ethereum keccak256, no FORS
// key hash (the WOTS+C encoding absorbs the FORS tops, then the counter), and the branch's addresses, byte orders and
// serialization. The message digest is one call laid out for a = 12 (spec section 5).

//! leanSphincs-S over keccak256.
//!
//! `Th(P, tw, M) = keccak256(P | tw | M)` truncated to its first `n = 16` bytes, with a 16-byte address `tw` (8 bytes
//! of fields, 8 zero bytes). Every hash call goes through [`hash`], which counts keccak256 calls and Keccak-f
//! permutations (thread-local) so tests can check the costs.
//!
//! [`key_gen`] and [`sign`] hold a key's whole kept subtree in memory and regenerate it per run. The one-signer tiers
//! ([`Tier`], [`keygen_cached`], [`sign_with_cache`], the key file of [`keyfile`]) generate the key once and store it
//! with a node cache of bounded size, from which every signature recomputes only what is not cached: the same keys and
//! the same signature bytes.

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod fors;
pub use fors::*;
mod scheme;
pub use scheme::*;
mod tiers;
pub use tiers::*;
pub mod keyfile;
pub use keyfile::*;

/// `n`: hash value and Merkle node length, in bytes.
pub const N: usize = 16;
pub type Digest = [u8; N];

pub const PUBLIC_PARAM_LEN: usize = 16;
pub type PublicParam = [u8; PUBLIC_PARAM_LEN];

/// The master secret of a (non-threshold) key.
pub const MASTER_SECRET_LEN: usize = 32;
pub type MasterSecret = [u8; MASTER_SECRET_LEN];

pub const RANDOMIZER_LEN: usize = 16;
pub type Randomizer = [u8; RANDOMIZER_LEN];

pub const MESSAGE_LEN: usize = 32;
pub type Message = [u8; MESSAGE_LEN];

pub const COUNTER_LEN: usize = 4;

/// Bits per WOTS chunk: chains of `2^W = 4` positions, i.e. 3 hash steps.
pub const W: usize = 2;
pub const CHAIN_LEN: usize = 1 << W;
/// Number of WOTS chains.
pub const V: usize = 64;
/// WOTS+C target sum of the signed positions.
pub const TARGET_SUM: usize = 128;

/// XMSS height (one layer).
pub const H: usize = 26;
/// FORS tree height and number of trees.
pub const A: usize = 12;
pub const K: usize = 13;

pub const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;

/// The digest bits: the leaf index, then the `k` FORS indices.
pub const DIGEST_BITS: usize = H + K * A;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
pub const SIG_SIZE: usize = RANDOMIZER_LEN + K * (1 + A) * N + COUNTER_LEN + V * N + H * N;
/// keccak256 calls of one verification: digest 1, FORS 13 * (1 + 11), encoding 1 (the 26 FORS tops and the counter),
/// chains 192 - 128, leaf 1, path 26.
pub const VERIFY_KECCAK_CALLS: u64 = 249;
/// Keccak-f permutations of one verification: digest 1, FORS 13 * (1 + 11), encoding 4 (452 input bytes), chains
/// 192 - 128, leaf 8 (1,056 input bytes), path 26.
pub const VERIFY_PERMUTATIONS: u64 = 259;

/// The input bytes of the WOTS+C encoding: `P | address | tops | counter`.
pub const ENCODING_INPUT_LEN: usize = PUBLIC_PARAM_LEN + ADDRESS_LEN + 2 * K * N + COUNTER_LEN;
/// The input bytes of a one-time leaf: `P | address | ends`.
pub const WOTS_LEAF_INPUT_LEN: usize = PUBLIC_PARAM_LEN + ADDRESS_LEN + V * N;

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(SIG_SIZE == 4164);
const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(DIGEST_BITS == 182 && DIGEST_BITS <= 256);
const _: () = assert!(VERIFY_KECCAK_CALLS == (1 + K * A + 1 + (V * (CHAIN_LEN - 1) - TARGET_SUM) + 1 + H) as u64);
const _: () = assert!(ENCODING_INPUT_LEN == 452 && blocks(ENCODING_INPUT_LEN) == 4);
const _: () = assert!(WOTS_LEAF_INPUT_LEN == 1056 && blocks(WOTS_LEAF_INPUT_LEN) == 8);
// Every other call of a verification (the digest, 80 bytes; a FORS leaf or a chain step, 48; a node, 64) is one block.
const _: () = assert!(
    VERIFY_PERMUTATIONS
        == 1 + (K * A) as u64
            + blocks(ENCODING_INPUT_LEN)
            + (V * (CHAIN_LEN - 1) - TARGET_SUM) as u64
            + blocks(WOTS_LEAF_INPUT_LEN)
            + H as u64
);
