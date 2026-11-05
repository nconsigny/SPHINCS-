#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>
"""leanSPHINCS, layered key for 2^30 signatures, over Keccak-256: a Python reference.

The normative specification is EthLib's Lean module `EthLib/Cryptography/Sphincs/`
(ethereum/EthLib PR #152, head aa99d5f), which follows Tom Wambsgans' note leanSPHINCS.tex
and its Lean model formal/sphincs/FORS/Scheme.lean at sphincs.art commit 1538d0a. Every
function below names the Lean definition it mirrors; where this file and the Lean disagree,
the Lean wins. docs/leanSphincs-layered-keccak.md is the human-readable summary.

Parameters (Constants.lean): n = 16, P and the address 16 bytes each, a 32-byte message,
a 16-byte randomizer, WOTS+C with v = 64 chains of w = 4 positions and target sum T = 128
(no checksum chains, a 4-byte little-endian counter), FORS k = 24 trees of height a = 10
with no root hash (its key is the 48 level-9 nodes), a hypertree of three layers of heights
10 (top), 8, 8 (bottom), h = 26. Public key 32 bytes (root ‖ P), signature 7,740 bytes.

Usage (the CLI the Forge FFI tests call; every hex argument may carry a 0x prefix):
    leansphincs_layered_signer.py sign <seed32> <msg32>
        prints 0x ‖ abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig), where
        pkSeed = P ‖ 0^16 and pkRoot = root ‖ 0^16 (the verifier's high-aligned key words)
    leansphincs_layered_signer.py keygen <seed32>       prints the 32-byte public key root ‖ P
    leansphincs_layered_signer.py keygen-file <path>    writes a fresh key file (magic LS-LYKEY, then a seed
        from the OS CSPRNG; mode 0600, never overwrites) and prints its public key root ‖ P
    leansphincs_layered_signer.py sign-key <path> <msg32>   `sign` with the key file's seed, the interface
        script/send_frame_tx_leansphincs.py calls (a key file whose name ends in .json is taken for C13 there)
    leansphincs_layered_signer.py verify <pk32> <msg32> <sig7740>   prints true / false
    leansphincs_layered_signer.py ethlib-check <fixture.json>
        checks every EthLib vector (key_gen, sign, verify) and the Lean known answer's
        intermediate values in the JSON fixture made by script/ethlib_sphincs_fixture.py

Every hash is Keccak-256 with Ethereum's (original Keccak) padding, i.e. the EVM opcode.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

from Crypto.Hash import keccak as _keccak

# ---------------------------------------------------------------------------
# Constants.lean
# ---------------------------------------------------------------------------

N = 16  # hash value / Merkle node bytes
PUBLIC_PARAM_LEN = 16
ADDRESS_LEN = 16
MESSAGE_LEN = 32
RANDOMIZER_LEN = 16
SEED_LEN = 32
SEED_TAG = b"leanSPHINCS"  # 11 ASCII bytes, hashed before the seed
COUNTER_LEN = 4
HASH_LEN = 32

CHAIN_LENGTH = 4  # positions 0..3, w = 4
V = 64  # chains
TARGET_SUM = 128
CHAIN_HASHES = V * (CHAIN_LENGTH - 1) - TARGET_SUM  # 64 verifier chain steps per layer
MAX_COUNTER_TRIALS = 2**32

TOP_HEIGHT = 10
LOWER_HEIGHT = 8
LAYERS = 3
HEIGHT = TOP_HEIGHT + 2 * LOWER_HEIGHT  # 26

FORS_TREES = 24  # k
FORS_HEIGHT = 10  # a

DIGEST_BITS = HEIGHT + FORS_TREES * FORS_HEIGHT  # 266
DIGEST_CALLS = (DIGEST_BITS + 8 * HASH_LEN - 1) // (8 * HASH_LEN)  # 2

PUB_KEY_SIZE = N + PUBLIC_PARAM_LEN  # 32
TREE_OPENING_SIZE = N + FORS_HEIGHT * N  # 176


def layer_sig_size(height: int) -> int:
    return COUNTER_LEN + V * N + height * N


SIG_SIZE = RANDOMIZER_LEN + FORS_TREES * TREE_OPENING_SIZE + 2 * layer_sig_size(LOWER_HEIGHT) + layer_sig_size(
    TOP_HEIGHT
)

assert 2 * V == 8 * N
assert CHAIN_HASHES == 64
assert HEIGHT == 26
assert DIGEST_CALLS == 2
assert SIG_SIZE == 7740
assert layer_sig_size(LOWER_HEIGHT) == 1156 and layer_sig_size(TOP_HEIGHT) == 1188
assert SIG_SIZE == 16 + 16 * FORS_TREES * (FORS_HEIGHT + 1) + 1028 * LAYERS + 16 * HEIGHT
assert FORS_TREES + 64 * (16 * 2**FORS_HEIGHT) <= 2**24  # fors_position_fits_hi
assert list(SEED_TAG) == [0x6C, 0x65, 0x61, 0x6E, 0x53, 0x50, 0x48, 0x49, 0x4E, 0x43, 0x53]

# Serialization.lean offsets.
FORS_OFFSET = RANDOMIZER_LEN  # 16
BOTTOM_OFFSET = FORS_OFFSET + FORS_TREES * TREE_OPENING_SIZE  # 4240
MIDDLE_OFFSET = BOTTOM_OFFSET + layer_sig_size(LOWER_HEIGHT)  # 5396
TOP_OFFSET = MIDDLE_OFFSET + layer_sig_size(LOWER_HEIGHT)  # 6552
assert (BOTTOM_OFFSET, MIDDLE_OFFSET, TOP_OFFSET) == (4240, 5396, 6552)
assert TOP_OFFSET + layer_sig_size(TOP_HEIGHT) == SIG_SIZE

# ---------------------------------------------------------------------------
# Types.lean: layers and one-time keys
# ---------------------------------------------------------------------------

BOTTOM, MIDDLE, TOP = 0, 1, 2  # Layer.toNat: counted from the bottom, the address byte
LAYER_HEIGHT = {BOTTOM: LOWER_HEIGHT, MIDDLE: LOWER_HEIGHT, TOP: TOP_HEIGHT}  # Layer.height
LAYER_BELOW = {BOTTOM: 0, MIDDLE: LOWER_HEIGHT, TOP: 2 * LOWER_HEIGHT}  # Layer.below


@dataclass(frozen=True)
class OtsKey:
    layer: int
    tree: int
    leaf: int


def ots_key_of_index(layer: int, idx: int) -> OtsKey:
    """OtsKey.ofIndex: the key of `layer` on the way from index `idx` up."""
    below, height = LAYER_BELOW[layer], LAYER_HEIGHT[layer]
    return OtsKey(layer, idx >> (below + height), (idx >> below) % 2**height)


# ---------------------------------------------------------------------------
# TweakableHash.lean
# ---------------------------------------------------------------------------


def keccak256(data: bytes) -> bytes:
    """`H`: Ethereum Keccak-256 (FIPS 202 permutation, original 0x01 padding)."""
    return _keccak.new(digest_bits=256, data=data).digest()


def half_of(half: int, full: bytes) -> bytes:
    """halfOf: H_0 is bytes 0..15, H_1 bytes 16..31."""
    assert half in (0, 1) and len(full) == HASH_LEN
    return full[16 * half : 16 * half + 16]


def th_full(pp: bytes, address: bytes, payload: bytes) -> bytes:
    """thFull: H(P | A | M), all 32 bytes."""
    assert len(pp) == PUBLIC_PARAM_LEN and len(address) == ADDRESS_LEN
    return keccak256(pp + address + payload)


def th(pp: bytes, address: bytes, payload: bytes) -> bytes:
    """th: Th(P, A, M) = H_0(P | A | M)."""
    return half_of(0, th_full(pp, address, payload))


# ---------------------------------------------------------------------------
# Address.lean
# ---------------------------------------------------------------------------

# AddressType.code
T_PRF, T_CHAIN, T_LEAF, T_NODE, T_ENCODING, T_PARAM = 0, 1, 2, 3, 4, 5
T_RND, T_MSG, T_FORS_PRF, T_FORS_LEAF, T_FORS_NODE = 7, 12, 14, 15, 17


def encode_address(type_: int, step: int, layer: int, tree: int, hi: int, lo: int) -> bytes:
    """encodeAddress: [ lo: 4 | hi: 3 | type + 32 step: 1 | layer: 1 | tree: 4 | zero: 3 ], LE."""
    assert 0 <= type_ < 32 and 0 <= step < 8 and 0 <= layer < 256
    assert 0 <= tree < 2**32 and 0 <= hi < 2**24 and 0 <= lo < 2**32
    return (
        lo.to_bytes(4, "little")
        + hi.to_bytes(3, "little")
        + bytes([type_ + 32 * step, layer])
        + tree.to_bytes(4, "little")
        + bytes(3)
    )


def key_address(type_: int, step: int, key: OtsKey, hi: int) -> bytes:
    """keyAddress: layer and tree of the key, its leaf in lo (UInt32.ofNat)."""
    return encode_address(type_, step, key.layer, key.tree % 2**32, hi, key.leaf % 2**32)


def addr_prf(key: OtsKey, j: int) -> bytes:
    assert 0 <= j < V // 2
    return key_address(T_PRF, 0, key, j)


def addr_chain(key: OtsKey, i: int, mu: int) -> bytes:
    """The step of chain i from position mu to mu + 1: hi = i, step = mu."""
    assert 0 <= i < V and 0 <= mu < CHAIN_LENGTH - 1
    return key_address(T_CHAIN, mu, key, i)


def addr_leaf(key: OtsKey) -> bytes:
    return key_address(T_LEAF, 0, key, 0)


def addr_encoding(key: OtsKey) -> bytes:
    return key_address(T_ENCODING, 0, key, 0)


def addr_node(layer: int, tree: int, level: int, j: int) -> bytes:
    """addrNode: hi = level (Fin (TOP_HEIGHT + 1)), lo = j (UInt32.ofNat)."""
    assert 0 <= level <= TOP_HEIGHT
    return encode_address(T_NODE, 0, layer, tree % 2**32, level, j % 2**32)


ADDR_PARAM = encode_address(T_PARAM, 0, 0, 0, 0, 0)
ADDR_RND = encode_address(T_RND, 0, 0, 0, 0, 0)


def addr_msg(call: int) -> bytes:
    assert 0 <= call < DIGEST_CALLS
    return encode_address(T_MSG, 0, 0, 0, call, 0)


def fors_hi(kappa: int, position: int) -> int:
    """forsHi: kappa + 64 position, kappa < 24, position < 16 * 2^10."""
    assert 0 <= kappa < FORS_TREES and 0 <= position < 16 * 2**FORS_HEIGHT
    return kappa + 64 * position


def fors_node_position(level: int, j: int) -> int:
    """forsNodePosition: level + 16 j, level < 16, j < 2^10."""
    assert 0 <= level < 16 and 0 <= j < 2**FORS_HEIGHT
    return level + 16 * j


def addr_fors_prf(idx: int, kappa: int, p: int) -> bytes:
    assert 0 <= p < 2**FORS_HEIGHT // 2
    return encode_address(T_FORS_PRF, 0, 0, 0, fors_hi(kappa, p), idx % 2**32)


def addr_fors_leaf(idx: int, kappa: int, leaf: int) -> bytes:
    assert 0 <= leaf < 2**FORS_HEIGHT
    return encode_address(T_FORS_LEAF, 0, 0, 0, fors_hi(kappa, leaf), idx % 2**32)


def addr_fors_node(idx: int, kappa: int, level: int, j: int) -> bytes:
    return encode_address(T_FORS_NODE, 0, 0, 0, fors_hi(kappa, fors_node_position(level, j)), idx % 2**32)


# ---------------------------------------------------------------------------
# Encoding.lean
# ---------------------------------------------------------------------------


def digits(d: bytes) -> List[int]:
    """Internal.digits: x_i = floor(LE^-1(D) / 4^i) mod 4, i < 64."""
    assert len(d) == N
    value = int.from_bytes(d, "little")
    return [(value >> (2 * i)) & 3 for i in range(V)]


def codeword(d: bytes) -> Optional[List[int]]:
    """codeword?: the digits, when they sum to T."""
    x = digits(d)
    return x if sum(x) == TARGET_SUM else None


# ---------------------------------------------------------------------------
# Ots.lean
# ---------------------------------------------------------------------------


def chain_starts(pp: bytes, seed: bytes, key: OtsKey) -> List[bytes]:
    """chainStarts: chains 2j and 2j + 1 start at the two halves of thFull(P, A_prf(K, j), S)."""
    pairs = [th_full(pp, addr_prf(key, j), seed) for j in range(V // 2)]
    return [half_of(i % 2, pairs[i // 2]) for i in range(V)]


def chain_step(pp: bytes, key: OtsKey, i: int, mu: int, value: bytes) -> bytes:
    return th(pp, addr_chain(key, i, mu), value)


def chain(pp: bytes, key: OtsKey, i: int, start: int, steps: int, value: bytes) -> bytes:
    """chain: walk chain i for `steps` steps from position `start`."""
    assert start + steps < CHAIN_LENGTH
    for s in range(steps):
        value = chain_step(pp, key, i, start + s, value)
    return value


def ots_leaf_hash(pp: bytes, key: OtsKey, ends: Sequence[bytes]) -> bytes:
    assert len(ends) == V and all(len(e) == N for e in ends)
    return th(pp, addr_leaf(key), b"".join(ends))


def ots_public_leaf(pp: bytes, seed: bytes, key: OtsKey) -> bytes:
    starts = chain_starts(pp, seed, key)
    return ots_leaf_hash(pp, key, [chain(pp, key, i, 0, CHAIN_LENGTH - 1, starts[i]) for i in range(V)])


def encode(pp: bytes, key: OtsKey, msg: bytes, counter: int) -> Optional[List[int]]:
    """encode: codeword? (Th(P, A_enc(K), M | LE_32(c)))."""
    assert 0 <= counter < 2**32
    return codeword(th(pp, addr_encoding(key), msg + counter.to_bytes(COUNTER_LEN, "little")))


def find_counter(pp: bytes, key: OtsKey, msg: bytes) -> Tuple[int, List[int]]:
    """Internal.findCounter from 0: the least counter whose encoding is a codeword."""
    prefix = pp + addr_encoding(key) + msg
    for c in range(MAX_COUNTER_TRIALS):
        x = codeword(half_of(0, keccak256(prefix + c.to_bytes(COUNTER_LEN, "little"))))
        if x is not None:
            assert x == encode(pp, key, msg, c)
            return c, x
    raise RuntimeError(f"no codeword within the counter limit on layer {key.layer}")


def ots_sign(pp: bytes, seed: bytes, key: OtsKey, msg: bytes) -> Tuple[int, List[bytes]]:
    counter, x = find_counter(pp, key, msg)
    starts = chain_starts(pp, seed, key)
    return counter, [chain(pp, key, i, 0, x[i], starts[i]) for i in range(V)]


def ots_leaf(pp: bytes, key: OtsKey, msg: bytes, counter: int, y: Sequence[bytes]) -> Optional[bytes]:
    """otsLeaf: the leaf a claimed one-time signature leads to, or None (not a codeword)."""
    x = encode(pp, key, msg, counter)
    if x is None:
        return None
    ends = [chain(pp, key, i, x[i], CHAIN_LENGTH - 1 - x[i], y[i]) for i in range(V)]
    return ots_leaf_hash(pp, key, ends)


# ---------------------------------------------------------------------------
# Merkle/Tree.lean (the shared Merkle tree) and Sphincs/Tree.lean
# ---------------------------------------------------------------------------


def merkle_ordered(j: int, current: bytes, sibling: bytes) -> Tuple[bytes, bytes]:
    """Merkle.ordered: the low bit of j says whether `current` is the left child."""
    return (current, sibling) if j % 2 == 0 else (sibling, current)


def merkle_climb(hash_fn, level: int, j: int, current: bytes, siblings: Sequence[bytes]) -> bytes:
    """Merkle.climb: hash (level + 1, j / 2) from the ordered children, one sibling per level."""
    for sibling in siblings:
        left, right = merkle_ordered(j, current, sibling)
        current = hash_fn(level + 1, j // 2, left, right)
        level, j = level + 1, j // 2
    return current


def merkle_levels(hash_fn, leaves: List[bytes], height: int) -> List[List[bytes]]:
    """All nodes of the tree of `height` over `leaves`: levels[l][j] = Merkle.node l j."""
    assert len(leaves) == 2**height
    levels = [leaves]
    for level in range(1, height + 1):
        below = levels[-1]
        levels.append([hash_fn(level, j, below[2 * j], below[2 * j + 1]) for j in range(len(below) // 2)])
    return levels


def merkle_path(levels: List[List[bytes]], height: int, j: int) -> List[bytes]:
    """Merkle.path: pi_l = X_{l, floor(j / 2^l) xor 1}, from the leaf up."""
    return [levels[l][(j >> l) ^ 1] for l in range(height)]


def node_hash(pp: bytes, layer: int, tree: int):
    """Tree.nodeHash: Th(P, A_node(layer, tree, level mod 11, j), left | right)."""

    def h(level: int, j: int, left: bytes, right: bytes) -> bytes:
        return th(pp, addr_node(layer, tree, level % (TOP_HEIGHT + 1), j), left + right)

    return h


def tree_levels(pp: bytes, seed: bytes, layer: int, tree: int) -> List[List[bytes]]:
    height = LAYER_HEIGHT[layer]
    leaves = [ots_public_leaf(pp, seed, OtsKey(layer, tree, j)) for j in range(2**height)]
    return merkle_levels(node_hash(pp, layer, tree), leaves, height)


def tree_fold(pp: bytes, layer: int, tree: int, e: int, leaf: bytes, pi: Sequence[bytes]) -> bytes:
    """Tree.fold: the root a path leads to from the leaf of key e of tree `tree`."""
    assert len(pi) == LAYER_HEIGHT[layer]
    return merkle_climb(node_hash(pp, layer, tree), 0, e, leaf, pi)


# ---------------------------------------------------------------------------
# Fors.lean
# ---------------------------------------------------------------------------


def fors_index(j: int) -> int:
    """forsIndex: the low 10 bits."""
    return j % 2**FORS_HEIGHT


def fors_secret(pp: bytes, seed: bytes, idx: int, kappa: int, leaf: int) -> bytes:
    return half_of(leaf % 2, th_full(pp, addr_fors_prf(idx, kappa, leaf // 2), seed))


def fors_leaf_hash(pp: bytes, idx: int, kappa: int, leaf: int, secret: bytes) -> bytes:
    return th(pp, addr_fors_leaf(idx, kappa, leaf), secret)


def fors_node_hash(pp: bytes, idx: int, kappa: int):
    """forsNodeHash: the level modulo 16, the index modulo 2^10."""

    def h(level: int, j: int, left: bytes, right: bytes) -> bytes:
        return th(pp, addr_fors_node(idx, kappa, level % 16, fors_index(j)), left + right)

    return h


def fors_levels(pp: bytes, seed: bytes, idx: int, kappa: int) -> List[List[bytes]]:
    leaves = [fors_leaf_hash(pp, idx, kappa, l, fors_secret(pp, seed, idx, kappa, l)) for l in range(2**FORS_HEIGHT)]
    # Merkle.node up to level 9 only (forsNode): the scheme never hashes level 10.
    levels = [leaves]
    h = fors_node_hash(pp, idx, kappa)
    for level in range(1, FORS_HEIGHT):
        below = levels[-1]
        levels.append([h(level, j, below[2 * j], below[2 * j + 1]) for j in range(len(below) // 2)])
    assert len(levels[FORS_HEIGHT - 1]) == 2
    return levels


@dataclass
class TreeOpening:
    secret: bytes
    path: List[bytes]  # FORS_HEIGHT nodes, level 0 first; the last is the other level-9 node


def fors_key_bytes(key: Sequence[Tuple[bytes, bytes]]) -> bytes:
    """forsKeyBytes: t_0[0] | t_0[1] | ... | t_23[1], 768 bytes."""
    assert len(key) == FORS_TREES
    return b"".join(a + b for a, b in key)


def tree_recover(pp: bytes, idx: int, kappa: int, leaf: int, opening: TreeOpening) -> Tuple[bytes, bytes]:
    """treeRecover: climb levels 0..8, then order the reached level-9 node with path[9] by bit 9."""
    node = fors_leaf_hash(pp, idx, kappa, leaf, opening.secret)
    reached = merkle_climb(fors_node_hash(pp, idx, kappa), 0, leaf, node, opening.path[: FORS_HEIGHT - 1])
    return merkle_ordered(leaf >> (FORS_HEIGHT - 1), reached, opening.path[FORS_HEIGHT - 1])


# ---------------------------------------------------------------------------
# Digest.lean
# ---------------------------------------------------------------------------


def randomizer(pp: bytes, seed: bytes, m: bytes) -> bytes:
    """R = H_0(P | A_rnd | S | m)."""
    return th(pp, ADDR_RND, seed + m)


def message_digest(pp: bytes, m: bytes, rho: bytes) -> bytes:
    """D = D_0 | D_1, D_c = H(P | A_msg(c) | m | R)."""
    assert len(m) == MESSAGE_LEN and len(rho) == RANDOMIZER_LEN
    return b"".join(th_full(pp, addr_msg(c), m + rho) for c in range(DIGEST_CALLS))


def digest_index(d: bytes) -> int:
    return int.from_bytes(d, "little") % 2**HEIGHT


def digest_leaves(d: bytes) -> List[int]:
    value = int.from_bytes(d, "little")
    return [(value >> (HEIGHT + FORS_HEIGHT * kappa)) % 2**FORS_HEIGHT for kappa in range(FORS_TREES)]


# ---------------------------------------------------------------------------
# Serialization.lean and Verify.lean
# ---------------------------------------------------------------------------


@dataclass
class LayerSignature:
    counter: int
    chain_values: List[bytes]
    path: List[bytes]


@dataclass
class Signature:
    randomizer: bytes
    fors: List[TreeOpening]
    layers: List[LayerSignature]  # bottom, middle, top


def _digests(b: bytes, n: int) -> List[bytes]:
    assert len(b) == n * N
    return [b[N * i : N * i + N] for i in range(n)]


def encode_layer_signature(s: LayerSignature) -> bytes:
    return s.counter.to_bytes(COUNTER_LEN, "little") + b"".join(s.chain_values) + b"".join(s.path)


def encode_signature(sig: Signature) -> bytes:
    out = sig.randomizer + b"".join(o.secret + b"".join(o.path) for o in sig.fors)
    out += b"".join(encode_layer_signature(s) for s in sig.layers)
    assert len(out) == SIG_SIZE
    return out


def decode_layer_signature(b: bytes, offset: int, height: int) -> LayerSignature:
    counter = int.from_bytes(b[offset : offset + COUNTER_LEN], "little")
    chains = _digests(b[offset + COUNTER_LEN : offset + COUNTER_LEN + V * N], V)
    path_off = offset + COUNTER_LEN + V * N
    return LayerSignature(counter, chains, _digests(b[path_off : path_off + height * N], height))


def decode_signature(b: bytes) -> Signature:
    """decodeSignature: length is the only check."""
    if len(b) != SIG_SIZE:
        raise ValueError(f"bad signature size: {len(b)}, expected {SIG_SIZE}")
    fors = []
    for kappa in range(FORS_TREES):
        o = FORS_OFFSET + TREE_OPENING_SIZE * kappa
        fors.append(TreeOpening(b[o : o + N], _digests(b[o + N : o + TREE_OPENING_SIZE], FORS_HEIGHT)))
    layers = [
        decode_layer_signature(b, BOTTOM_OFFSET, LOWER_HEIGHT),
        decode_layer_signature(b, MIDDLE_OFFSET, LOWER_HEIGHT),
        decode_layer_signature(b, TOP_OFFSET, TOP_HEIGHT),
    ]
    return Signature(b[:RANDOMIZER_LEN], fors, layers)


def decode_public_key(b: bytes) -> Tuple[bytes, bytes]:
    """decodePublicKey: root ‖ P."""
    if len(b) != PUB_KEY_SIZE:
        raise ValueError(f"bad public key size: {len(b)}, expected {PUB_KEY_SIZE}")
    return b[:N], b[N:]


def layer_root(pp: bytes, layer: int, idx: int, msg: bytes, s: LayerSignature) -> Optional[bytes]:
    """layerRoot: Ots.leaf, then Tree.fold, at the layer's key on the way from idx up."""
    key = ots_key_of_index(layer, idx)
    leaf = ots_leaf(pp, key, msg, s.counter, s.chain_values)
    if leaf is None:
        return None
    return tree_fold(pp, layer, key.tree, key.leaf, leaf, s.path)


@dataclass
class Trace:
    """What verification computes, for the known-answer checks and for debugging."""

    digest: bytes
    idx: int
    leaves: List[int]
    fors_key: List[Tuple[bytes, bytes]]
    roots: List[Optional[bytes]]  # bottom, middle, top (None from a failed layer on)


def verify_trace(root: bytes, pp: bytes, m: bytes, sig: Signature) -> Tuple[bool, Trace]:
    d = message_digest(pp, m, sig.randomizer)
    idx = digest_index(d)
    leaves = digest_leaves(d)
    fors_key = [tree_recover(pp, idx, k, leaves[k], sig.fors[k]) for k in range(FORS_TREES)]
    roots: List[Optional[bytes]] = []
    msg = fors_key_bytes(fors_key)
    for layer in (BOTTOM, MIDDLE, TOP):
        r = layer_root(pp, layer, idx, msg, sig.layers[layer])
        roots.append(r)
        if r is None:
            break
        msg = r
    ok = len(roots) == LAYERS and roots[-1] is not None and roots[-1] == root
    return ok, Trace(d, idx, leaves, fors_key, roots)


def verify(pk: bytes, m: bytes, sig_bytes: bytes) -> bool:
    """`verify` over encoded inputs; bad lengths raise (the EthLib vectors' `null`)."""
    root, pp = decode_public_key(pk)
    if len(m) != MESSAGE_LEN:
        raise ValueError(f"bad message size: {len(m)}, expected {MESSAGE_LEN}")
    return verify_trace(root, pp, m, decode_signature(sig_bytes))[0]


# ---------------------------------------------------------------------------
# KeyGen.lean and Sign.lean
# ---------------------------------------------------------------------------


def scheme_seed(seed0: bytes) -> bytes:
    """schemeSeed: S = H("leanSPHINCS" | S_0)."""
    if len(seed0) != SEED_LEN:
        raise ValueError(f"bad seed size: {len(seed0)}, expected {SEED_LEN}")
    return keccak256(SEED_TAG + seed0)


def public_param_of(seed: bytes) -> bytes:
    """publicParamOf: P = Th(0^128, A_param, S)."""
    return th(bytes(PUBLIC_PARAM_LEN), ADDR_PARAM, seed)


class Signer:
    """A key from its scheme seed S (the seed below the name hash, as the Lean known answer pins it).

    Use Signer.from_seed(S_0) for EthLib's keyGen / sign. The top tree is built once per Signer."""

    def __init__(self, scheme_seed_bytes: bytes):
        assert len(scheme_seed_bytes) == SEED_LEN
        self.seed = scheme_seed_bytes
        self.pp = public_param_of(self.seed)
        self._top = tree_levels(self.pp, self.seed, TOP, 0)
        self.root = self._top[TOP_HEIGHT][0]

    @classmethod
    def from_seed(cls, seed0: bytes) -> "Signer":
        return cls(scheme_seed(seed0))

    def public_key(self) -> bytes:
        """encodePublicKey: root ‖ P."""
        return self.root + self.pp

    def _sign_layer(self, layer: int, idx: int, msg: bytes, levels: List[List[bytes]]) -> LayerSignature:
        key = ots_key_of_index(layer, idx)
        counter, values = ots_sign(self.pp, self.seed, key, msg)
        return LayerSignature(counter, values, merkle_path(levels, LAYER_HEIGHT[layer], key.leaf))

    def sign(self, m: bytes) -> bytes:
        if len(m) != MESSAGE_LEN:
            raise ValueError(f"bad message size: {len(m)}, expected {MESSAGE_LEN}")
        pp, seed = self.pp, self.seed
        rho = randomizer(pp, seed, m)
        d = message_digest(pp, m, rho)
        idx = digest_index(d)
        leaves = digest_leaves(d)
        fors, fors_key = [], []
        for kappa in range(FORS_TREES):
            lv = fors_levels(pp, seed, idx, kappa)
            l = leaves[kappa]
            # treeOpen: the path of a tree of height 10; its last node is the other level-9 node.
            path = [lv[lev][(l >> lev) ^ 1] for lev in range(FORS_HEIGHT)]
            fors.append(TreeOpening(fors_secret(pp, seed, idx, kappa, l), path))
            fors_key.append((lv[FORS_HEIGHT - 1][0], lv[FORS_HEIGHT - 1][1]))
        bottom_key = ots_key_of_index(BOTTOM, idx)
        middle_key = ots_key_of_index(MIDDLE, idx)
        bottom_levels = tree_levels(pp, seed, BOTTOM, bottom_key.tree)
        middle_levels = tree_levels(pp, seed, MIDDLE, middle_key.tree)
        bottom = self._sign_layer(BOTTOM, idx, fors_key_bytes(fors_key), bottom_levels)
        middle = self._sign_layer(MIDDLE, idx, bottom_levels[LOWER_HEIGHT][0], middle_levels)
        top = self._sign_layer(TOP, idx, middle_levels[LOWER_HEIGHT][0], self._top)
        sig = encode_signature(Signature(rho, fors, [bottom, middle, top]))
        # Self-check, as every signer in this repo does before output.
        if not verify(self.public_key(), m, sig):
            raise AssertionError("signer self-check: the signature does not verify")
        return sig


def key_gen(seed0: bytes) -> bytes:
    """keyGen: the encoded public key root ‖ P of a 32-byte seed S_0."""
    return Signer.from_seed(seed0).public_key()


def sign(seed0: bytes, m: bytes) -> bytes:
    # The lengths first, before the top tree is built (EthLib's sign rejects either).
    scheme_seed(seed0)
    if len(m) != MESSAGE_LEN:
        raise ValueError(f"bad message size: {len(m)}, expected {MESSAGE_LEN}")
    return Signer.from_seed(seed0).sign(m)


# ---------------------------------------------------------------------------
# Known answers: EthLib's vectors and the Lean known answer's intermediate values
# ---------------------------------------------------------------------------


def _hx(s: str) -> bytes:
    s = s[2:] if s.startswith(("0x", "0X")) else s
    return bytes.fromhex(s)


def ethlib_check(path: str) -> int:
    """Check every case of the fixture made by script/ethlib_sphincs_fixture.py. Returns #checks."""
    import json

    with open(path) as f:
        fx = json.load(f)
    checks = 0

    def expect(got, want, what):
        nonlocal checks
        if got != want:
            raise AssertionError(f"{what}: got {got!r}, want {want!r}")
        checks += 1

    def call(fn, *args):
        try:
            return fn(*args)
        except ValueError:
            return None  # a rejected input: the vectors' null

    for case in fx["key_gen"]:
        got = call(lambda s: key_gen(s).hex(), _hx(case["seed"]))
        want = None if case["output"] is None else _hx(case["output"]).hex()
        expect(got, want, f"key_gen {case['name']}")
        print(f"  key_gen {case['name']}: ok", file=sys.stderr)
    for case in fx["sign"]:
        got = call(lambda s, m: sign(s, m).hex(), _hx(case["seed"]), _hx(case["message"]))
        want = None if case["output"] is None else _hx(case["output"]).hex()
        expect(got, want, f"sign {case['name']}")
        print(f"  sign {case['name']}: ok", file=sys.stderr)
    for case in fx["verify"]:
        got = call(verify, _hx(case["public_key"]), _hx(case["message"]), _hx(case["signature"]))
        expect(got, case["output"], f"verify {case['name']}")
        print(f"  verify {case['name']}: ok", file=sys.stderr)

    # The Lean known answer (Proofs/Sphincs/KnownAnswer*.lean): a key from the scheme seed S
    # directly, with every value verification computes on the way to the root.
    ka = fx["lean_known_answer"]
    s = _hx(ka["scheme_seed"])
    expect(scheme_seed(s).hex(), _hx(ka["tagged_seed"]).hex(), "known answer: schemeSeed")
    pk = _hx(ka["public_key"])
    root, pp = pk[:N], pk[N:]
    expect(public_param_of(s).hex(), pp.hex(), "known answer: publicParamOf")
    m = _hx(ka["message"])
    sig = decode_signature(_hx(ka["signature"]))
    ok, tr = verify_trace(root, pp, m, sig)
    expect(tr.digest.hex(), _hx(ka["digest"]).hex(), "known answer: digest")
    expect(tr.idx, ka["idx"], "known answer: idx")
    expect(tr.leaves, ka["leaves"], "known answer: FORS leaves")
    expect(fors_key_bytes(tr.fors_key).hex(), _hx(ka["fors_key"]).hex(), "known answer: FORS key")
    for name, layer in (("bottom", BOTTOM), ("middle", MIDDLE), ("top", TOP)):
        expect(tr.roots[layer].hex(), _hx(ka[f"{name}_root"]).hex(), f"known answer: {name} root")
        key = ots_key_of_index(layer, tr.idx)
        msg = fors_key_bytes(tr.fors_key) if layer == BOTTOM else tr.roots[layer - 1]
        x = encode(pp, key, msg, sig.layers[layer].counter)
        expect(x, ka[f"{name}_codeword"], f"known answer: {name} codeword")
        leaf = ots_leaf(pp, key, msg, sig.layers[layer].counter, sig.layers[layer].chain_values)
        expect(leaf.hex(), _hx(ka[f"{name}_leaf"]).hex(), f"known answer: {name} leaf")
    expect(ok, True, "known answer: verify")
    # And the signer reproduces the pinned signature from the scheme seed.
    expect(Signer(s).sign(m).hex(), _hx(ka["signature"]).hex(), "known answer: sign from the scheme seed")
    expect(Signer(s).public_key().hex(), pk.hex(), "known answer: public key from the scheme seed")
    print("  Lean known answer: ok", file=sys.stderr)
    return checks


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


# A key file: the 8-byte magic, then the 32-byte seed S_0, nothing else (40 bytes, mode 0600). The magic
# keeps the other leanSphincs CLIs' key files (LS-KKKEY, LS-SKKEY, LS-FKKEY, LS23KKEY) out, and theirs
# refuse this one: one seed is one key of one variant.
KEY_FILE_MAGIC = b"LS-LYKEY"


def write_key_file(path: str) -> bytes:
    """A fresh key file with a seed from the OS CSPRNG. Refuses to overwrite. Returns the seed."""
    import os

    seed0 = os.urandom(SEED_LEN)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as f:
        f.write(KEY_FILE_MAGIC + seed0)
    return seed0


def read_key_file(path: str) -> bytes:
    with open(path, "rb") as f:
        data = f.read()
    if len(data) != len(KEY_FILE_MAGIC) + SEED_LEN or not data.startswith(KEY_FILE_MAGIC):
        raise ValueError(f"{path}: not a leanSphincs-layered key file (magic {KEY_FILE_MAGIC.decode()})")
    return data[len(KEY_FILE_MAGIC) :]


def _abi_encode_sign_output(pk_seed: bytes, pk_root: bytes, sig: bytes) -> bytes:
    """abi.encode(bytes32, bytes32, bytes)."""
    assert len(pk_seed) == 32 and len(pk_root) == 32
    padded = sig + bytes((-len(sig)) % 32)
    return pk_seed + pk_root + (96).to_bytes(32, "big") + len(sig).to_bytes(32, "big") + padded


def main(argv: List[str]) -> int:
    if len(argv) >= 1 and argv[0] in ("sign", "sign-key") and len(argv) == 3:
        seed0 = read_key_file(argv[1]) if argv[0] == "sign-key" else _hx(argv[1])
        s = Signer.from_seed(seed0)
        sig = s.sign(_hx(argv[2]))
        out = _abi_encode_sign_output(s.pp + bytes(16), s.root + bytes(16), sig)
        sys.stdout.write("0x" + out.hex())
        return 0
    if len(argv) == 2 and argv[0] == "keygen-file":
        sys.stdout.write("0x" + key_gen(write_key_file(argv[1])).hex())
        return 0
    if len(argv) == 2 and argv[0] == "keygen":
        sys.stdout.write("0x" + key_gen(_hx(argv[1])).hex())
        return 0
    if len(argv) == 4 and argv[0] == "verify":
        sys.stdout.write("true" if verify(_hx(argv[1]), _hx(argv[2]), _hx(argv[3])) else "false")
        return 0
    if len(argv) == 2 and argv[0] == "ethlib-check":
        n = ethlib_check(argv[1])
        print(f"ethlib-check: {n} checks passed", file=sys.stderr)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
