#!/usr/bin/env python3
"""
leanSphincs-23 signer over keccak256 — independent Python reference.
Legacy (verifier in legacy/src): leanSphincs-23 is superseded by leanSphincs-S
(script/leansphincs_s_signer.py); kept to reproduce the legacy KAT fixture.

leanSphincs is Tom Wambsgans' one-layer SPHINCS candidate (leanSPHINCS note,
leanXMSS-leanSPHINCS-candidates `crates/sphincs`, BLAKE2s). leanSphincs-23 is the
sphincs-art retuning of it; this file instantiates it with Ethereum Keccak-256 in
place of BLAKE2s, exactly as pinned by legacy/docs/leanSphincs-23-keccak.md ("the spec",
section numbers below refer to it). It is written from the spec alone, so that
it can be cross-checked byte-for-byte against the Rust port of the upstream crate
(signers/leansphincs23-keccak) and against the on-chain verifier
(legacy/src/LeanSphincs-23Asm.sol).

Parameters (spec §1):
    n = 16 (node bytes)   |P| = 16   |rho| = 16   |m| = 32   counter c = u32 LE
    WOTS+C: w = 2 bits (chains of 4 positions, 3 steps), v = 64 chains, T = 128
    XMSS:   h = 25, one layer (d = 1), pruned keys keep a subtree of height b
    FORS:   k = 13 trees of height a = 12 (4096 leaves), no per-tree root hash

Hash (spec §2), with address(tw) the 16-byte tweak of spec §3:
    Th(P, tw, M)     = keccak256(P ‖ address(tw) ‖ M)[0:16]
    ThPair(P, tw, M) = both 16-byte halves of the same keccak256 (signer PRFs)
    ThFull(P, tw, M) = keccak256(P ‖ address(tw) ‖ M)            (message digest)
    address(t, step, hi, lo) = LE32(lo) ‖ LE24(hi) ‖ (t | step << 5) ‖ 0^8
`P ‖ address` is exactly one 32-byte EVM word, so the "first 16 bytes" of a
digest are the high 128 bits of the KECCAK256 word on-chain.

Signature (4,148 B, spec §11):
    rho(16) ‖ 13 × [FORS secret(16) ‖ 12 path nodes(16)] ‖ counter(4, LE)
            ‖ 64 WOTS values(16) ‖ 25 auth-path nodes(16)

Verification costs exactly 249 keccak256 calls (spec §1); verify() below is a
spec-literal mirror of the on-chain checks of spec §12 and is deliberately
written without the signer's cached address prefixes, so every sign() is
cross-checked by an independently-coded path before it is emitted.

Usage:
    python3 script/leansphincs23_signer.py <seed_hex64> <b> <msg_hex64>
        -> 0x ‖ hex(abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig))
           pkSeed = P ‖ 0^16, pkRoot = root ‖ 0^16 (high-aligned)
    python3 script/leansphincs23_signer.py --json <seed_hex64> <b> <msg_hex64>
        -> KAT JSON object (seed, b, message, pkSeed, pkRoot, sig, idx,
           counter, randomizer, fors_indices)
    python3 script/leansphincs23_signer.py --verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>
        -> true / false  (an on-chain revert prints false, reason on stderr)
    python3 script/leansphincs23_signer.py --selftest [b ...]
        -> address vector, sign/verify, tamper checks, timings (default b = 6 10)

Hex arguments are accepted with or without 0x. b is the kept-subtree height
(0 <= b <= 25; b = 25 is a full key, ~7.6e9 keccak calls — infeasible here).
A pruned key grinds the randomizer for ~2^(25-b) digests per signature, so
b ~ 6..12 is the practical range for this Python signer.

Requires pycryptodome (Crypto.Hash.keccak). Not audited, not production-safe.
"""

import json
import struct
import sys
import time

from Crypto.Hash import keccak as _keccak_mod

# ============================================================
#  Parameters (spec §1)
# ============================================================

N           = 16          # node / hash value bytes
P_LEN       = 16          # public parameter
RHO_LEN     = 16          # randomizer
MSG_LEN     = 32          # message
SEED_LEN    = 32          # master secret S
COUNTER_LEN = 4           # WOTS+C counter, u32 little endian
W           = 2           # bits per WOTS chunk
CHAIN_LEN   = 1 << W      # 4 chain positions (3 hash steps)
V           = 64          # WOTS chains
TARGET_SUM  = 128         # WOTS+C target sum
H           = 25          # XMSS height, one layer
A           = 12          # FORS tree height
K           = 13          # FORS trees
FORS_LEAVES = 1 << A      # 4096

FORS_TREE_LEN = (1 + A) * N                       # 208: secret + 12 path nodes
OFF_RHO       = 0
OFF_FORS      = OFF_RHO + RHO_LEN                 # 16
OFF_COUNTER   = OFF_FORS + K * FORS_TREE_LEN      # 2720
OFF_WOTS      = OFF_COUNTER + COUNTER_LEN         # 2724
OFF_AUTH      = OFF_WOTS + V * N                  # 3748
SIG_LEN       = OFF_AUTH + H * N                  # 4148

assert W * V == 8 * N
assert TARGET_SUM < V * (CHAIN_LEN - 1)
assert SIG_LEN == 16 + 2704 + 4 + 1024 + 400 == 4148
assert H + K * A == 181 <= 256

MASK_H   = (1 << H) - 1
MASK_A   = FORS_LEAVES - 1
MASK_128 = (1 << 128) - 1
# WOTS+C chunk sum without unpacking: each 2-bit chunk x = lo + 2·hi, so
# Σ x_i = popcount(X & 0x55..55) + 2·popcount(X & 0xAA..AA).
_M_LO = int("55" * 16, 16)
_M_HI = int("aa" * 16, 16)

# Tweak types (low five bits of address byte 7, spec §3)
TW_PRF        = 0     # WOTS secrets
TW_CHAIN      = 1
TW_LEAF       = 2     # WOTS leaf
TW_NODE       = 3     # XMSS node
TW_ENC        = 4     # WOTS+C encoding
TW_PARAMETER  = 5     # derives P
TW_RANDOMIZER = 7
TW_FTS_PRF    = 8     # FORS secrets
TW_FTS_LEAF   = 9
TW_FTS_NODE   = 10
TW_FTS_KEY    = 11
TW_MSG        = 12    # message digest
TW_SURROGATE  = 13    # pruned-key siblings

_Z8 = bytes(8)

# ============================================================
#  Hash and address (spec §2, §3)
# ============================================================

_kn = _keccak_mod.new


def keccak256(data):
    """Ethereum Keccak-256 (0x01 padding) — the EVM KECCAK256 opcode."""
    return _kn(digest_bits=256, data=data).digest()


def address(t, step, hi, lo):
    """The 16-byte tweak: LE32(lo) ‖ LE24(hi) ‖ (t | step<<5) ‖ 0^8."""
    if not (0 <= t < 32 and 0 <= step < 8 and 0 <= hi < 1 << 24 and 0 <= lo < 1 << 32):
        raise ValueError(f"address field out of range: t={t} step={step} hi={hi} lo={lo}")
    return lo.to_bytes(4, "little") + hi.to_bytes(3, "little") + bytes([t | (step << 5)]) + _Z8


def th(pp, tw, payload):
    """Th(P, tw, M): first 16 bytes (high 128 bits on the EVM) of keccak256(P ‖ tw ‖ M)."""
    return keccak256(pp + tw + payload)[:N]


def th_pair(pp, tw, payload):
    """ThPair: both 16-byte halves of keccak256(P ‖ tw ‖ M). Signer-side PRFs only."""
    d = keccak256(pp + tw + payload)
    return d[:N], d[N:]


def th_full(pp, tw, payload):
    """ThFull: the untruncated 32-byte keccak256(P ‖ tw ‖ M). Message digest only."""
    return keccak256(pp + tw + payload)


def fors_pos(kappa, level, j):
    """pos(κ, ℓ, j) = κ + 32ℓ + 512j — disjoint bit ranges 0-4 / 5-8 / 9-20 (spec §4)."""
    if not (0 <= kappa < K and 0 <= level < A and 0 <= j < 1 << (A - level)):
        raise ValueError(f"FORS position out of range: κ={kappa} ℓ={level} j={j}")
    return kappa + 32 * level + 512 * j


# --- Signer fast path: cached address bytes ---------------------------------
# address(t, step, hi, lo)[4:16] does not depend on lo, and bytes 4..8 read as
# a u32 LE are exactly hi | (t | step<<5) << 24. The signer therefore builds a
# call's 32-byte word as P ‖ LE32(lo) ‖ tail(t, step, hi), with the tails below
# precomputed once. verify() never uses these, so a slip here is caught by the
# self-verification in sign().

def _tail(t, step, hi):
    return struct.pack("<I", hi | ((t | (step << 5)) << 24)) + _Z8


_PRF_TAILS   = [_tail(TW_PRF, 0, t) for t in range(V // 2)]
_CHAIN_TAILS = [[_tail(TW_CHAIN, s, i) for s in range(CHAIN_LEN - 1)] for i in range(V)]
_LEAF_TAIL   = _tail(TW_LEAF, 0, 0)
_ENC_TAIL    = _tail(TW_ENC, 0, 0)
_pack_u32    = struct.Struct("<I").pack

# ============================================================
#  Message digest (spec §5)
# ============================================================


def digest_fields(d):
    """Split the 32-byte digest into the leaf index and the 13 FORS indices.

    word_w = u64 LE of d[8w : 8w+8]; idx = word_3 & (2^25 - 1);
    u_κ = (word_{κ div 5} >> 12·(κ mod 5)) & 0xFFF (words 0, 1 hold five
    indices each, word 2 holds κ = 10..12; no field straddles two words).
    """
    words = [int.from_bytes(d[8 * w: 8 * w + 8], "little") for w in range(4)]
    idx = words[3] & MASK_H
    u = [(words[kappa // 5] >> (A * (kappa % 5))) & MASK_A for kappa in range(K)]
    return idx, u


def message_digest(pp, rho, m):
    """D = ThFull(P, address(MSG, 0, 0, 0), m ‖ rho); returns (idx, [u_0..u_12])."""
    return digest_fields(th_full(pp, address(TW_MSG, 0, 0, 0), m + rho))


# ============================================================
#  WOTS+C (spec §6)
# ============================================================


def wots_codeword(d):
    """x_i = (X >> 2i) & 3 with X = d as u128 LE; the codeword iff Σ x_i = T, else None."""
    X = int.from_bytes(d, "little")
    x = [(X >> (W * i)) & (CHAIN_LEN - 1) for i in range(V)]
    return x if sum(x) == TARGET_SUM else None


def wots_secrets(pp, seed, e):
    """(s_2t, s_2t+1) = ThPair(P, address(PRF, 0, hi=t, lo=e), S), t = 0..31."""
    pe = pp + _pack_u32(e)
    out = []
    for t in range(V // 2):
        d = _kn(digest_bits=256, data=pe + _PRF_TAILS[t] + seed).digest()
        out.append(d[:N])
        out.append(d[N:])
    return out


def wots_leaf_from_seed(pp, seed, e):
    """Keygen leaf at e: every chain walked 0 -> 3, then Th(LEAF) over the 64 ends."""
    pe = pp + _pack_u32(e)
    kn = _kn
    ends = []
    for i, s in enumerate(wots_secrets(pp, seed, e)):
        t0, t1, t2 = _CHAIN_TAILS[i]
        x = kn(digest_bits=256, data=pe + t0 + s).digest()[:N]
        x = kn(digest_bits=256, data=pe + t1 + x).digest()[:N]
        x = kn(digest_bits=256, data=pe + t2 + x).digest()[:N]
        ends.append(x)
    return kn(digest_bits=256, data=pe + _LEAF_TAIL + b"".join(ends)).digest()[:N]


def wots_encode(pp, e, msg):
    """Least c in [0, 2^32) whose Th(P, address(ENC, 0, 0, e), msg ‖ LE32(c)) is a codeword."""
    prefix = pp + _pack_u32(e) + _ENC_TAIL + msg
    kn, pk = _kn, _pack_u32
    for c in range(1 << 32):
        X = int.from_bytes(kn(digest_bits=256, data=prefix + pk(c)).digest()[:N], "little")
        if (X & _M_LO).bit_count() + 2 * (X & _M_HI).bit_count() == TARGET_SUM:
            return c, [(X >> (W * i)) & (CHAIN_LEN - 1) for i in range(V)]
    raise RuntimeError("no admissible WOTS+C encoding in 2^32 counters")


def wots_sign(pp, seed, e, msg):
    """Counter c and σ_i = chain i walked from position 0 up to x_i."""
    c, x = wots_encode(pp, e, msg)
    pe = pp + _pack_u32(e)
    sigma = []
    for i, s in enumerate(wots_secrets(pp, seed, e)):
        tails = _CHAIN_TAILS[i]
        for to in range(1, x[i] + 1):
            s = _kn(digest_bits=256, data=pe + tails[to - 1] + s).digest()[:N]
        sigma.append(s)
    return c, x, sigma


# ============================================================
#  FORS (spec §7)
# ============================================================


def fors_sign(pp, seed, idx, u):
    """Build FORS instance idx tree by tree, keeping only what the signature needs.

    Returns (secrets[13], paths[13][12], fors_key). Each tree's levels are
    dropped once its opened secret, its 12 path nodes and its two level-11
    tops have been taken, so the peak working set is one 4096-leaf tree.
    """
    kn, pk = _kn, _pack_u32
    pl = pp + _pack_u32(idx)
    prf_t = TW_FTS_PRF << 24
    leaf_t = TW_FTS_LEAF << 24
    node_t = TW_FTS_NODE << 24
    secrets, paths, tops = [], [], []
    for kappa in range(K):
        uk = u[kappa]
        leaves = []
        opened = None
        for t in range(FORS_LEAVES // 2):
            # Secret pair at pos(κ, 0, t); leaves 2t, 2t+1 at pos(κ, 0, 2t[+1]).
            d = kn(digest_bits=256, data=pl + pk(kappa + 512 * t | prf_t) + _Z8 + seed).digest()
            s0, s1 = d[:N], d[N:]
            j = 2 * t
            leaves.append(kn(digest_bits=256, data=pl + pk(kappa + 512 * j | leaf_t) + _Z8 + s0).digest()[:N])
            leaves.append(kn(digest_bits=256, data=pl + pk(kappa + 512 * (j + 1) | leaf_t) + _Z8 + s1).digest()[:N])
            if t == uk >> 1:
                opened = s1 if uk & 1 else s0
        path = [leaves[uk ^ 1]]
        below = leaves
        for level in range(1, A):
            base = kappa + 32 * level
            up = [
                kn(digest_bits=256,
                   data=pl + pk(base + 512 * j | node_t) + _Z8 + below[2 * j] + below[2 * j + 1]).digest()[:N]
                for j in range(len(below) >> 1)
            ]
            below = up
            path.append(up[(uk >> level) ^ 1])
        assert len(below) == 2          # the two level-11 tops; no tree root
        tops += below
        secrets.append(opened)
        paths.append(path)
    fors_key = th(pp, address(TW_FTS_KEY, 0, 0, idx), b"".join(tops))
    return secrets, paths, fors_key


# ============================================================
#  XMSS, keys (spec §8, §9)
# ============================================================


def xmss_node(pp, level, j, left, right):
    """node(ℓ, j) = Th(P, address(NODE, 0, hi=ℓ, lo=j), left ‖ right)."""
    return th(pp, address(TW_NODE, 0, level, j), left + right)


class SecretKey:
    __slots__ = ("seed", "pp", "b", "s", "levels", "surrogates", "root")

    def contains(self, idx):
        return idx >> self.b == self.s

    def auth_path(self, idx):
        """path[ℓ] = kept-subtree sibling for ℓ < b, surrogate for ℓ >= b."""
        assert self.contains(idx)
        local = idx - (self.s << self.b)
        return [self.levels[l][(local >> l) ^ 1] if l < self.b else self.surrogates[l - self.b]
                for l in range(H)]

    @property
    def pk_seed(self):
        return self.pp + bytes(16)

    @property
    def pk_root(self):
        return self.root + bytes(16)


def keygen(seed, b, log=None):
    """Gen with kept-subtree height b (spec §9); b = 25 is a full key.

    P = Th(0^16, address(PARAMETER, 0, 0, 0), S); the kept subtree's position
    s is the low (25 - b) bits of u64 LE P[0:8]; it holds leaves
    [s·2^b, (s+1)·2^b). Surrogate siblings for levels b..24 are
    Th(P, address(SURROGATE, 0, hi=ℓ, lo=0), S); the root is the subtree root
    folded through them, bit (ℓ - b) of s choosing the side.
    """
    if len(seed) != SEED_LEN:
        raise ValueError("seed must be 32 bytes")
    if not 0 <= b <= H:
        raise ValueError(f"kept-subtree height b must be in [0, {H}]")
    pp = th(bytes(P_LEN), address(TW_PARAMETER, 0, 0, 0), seed)
    s = (int.from_bytes(pp[:8], "little") & ((1 << (H - b)) - 1)) if b < H else 0

    first = s << b
    leaves = []
    for j in range(1 << b):
        leaves.append(wots_leaf_from_seed(pp, seed, first + j))
        if log and (j + 1) % 4096 == 0:
            log(f"    {j + 1}/{1 << b} WOTS leaves")
    levels = [leaves]
    for level in range(1, b + 1):
        below = levels[-1]
        off = s << (b - level)          # global index of this level's first kept node
        levels.append([xmss_node(pp, level, off + j, below[2 * j], below[2 * j + 1])
                       for j in range(len(below) >> 1)])

    surrogates = [th(pp, address(TW_SURROGATE, 0, level, 0), seed) for level in range(b, H)]
    node = levels[b][0]
    for t, sib in enumerate(surrogates):
        j = s >> t                      # this node's index at level b + t
        left, right = (node, sib) if j & 1 == 0 else (sib, node)
        node = xmss_node(pp, b + t + 1, j >> 1, left, right)

    sk = SecretKey()
    sk.seed, sk.pp, sk.b, sk.s = seed, pp, b, s
    sk.levels, sk.surrogates, sk.root = levels, surrogates, node
    return sk


# ============================================================
#  Signing (spec §10, §11)
# ============================================================


def sign(sk, m):
    """Sign a 32-byte message. Returns (sig_bytes, info dict); raises if the mirror rejects."""
    if len(m) != MSG_LEN:
        raise ValueError("message must be 32 bytes")
    pp, seed = sk.pp, sk.seed

    # R_0 = Th(P, address(RANDOMIZER, 0, 0, 0), S ‖ m); rho_i = R_0 + i (u128 LE).
    r0 = int.from_bytes(th(pp, address(TW_RANDOMIZER, 0, 0, 0), seed + m), "little")
    prefix = pp + address(TW_MSG, 0, 0, 0) + m
    b, s = sk.b, sk.s
    kn = _kn
    i = 0
    while True:
        rho = ((r0 + i) & MASK_128).to_bytes(RHO_LEN, "little")
        d = kn(digest_bits=256, data=prefix + rho).digest()
        # idx = low 25 bits of word_3 = low 25 bits of LE32(d[24:28]).
        if (int.from_bytes(d[24:28], "little") & MASK_H) >> b == s:
            break
        i += 1
    idx, u = digest_fields(d)
    assert sk.contains(idx)

    fors_secrets, fors_paths, fors_key = fors_sign(pp, seed, idx, u)
    counter, x, sigma = wots_sign(pp, seed, idx, fors_key)
    path = sk.auth_path(idx)

    out = bytearray(rho)
    for kappa in range(K):
        out += fors_secrets[kappa]
        for node in fors_paths[kappa]:
            out += node
    out += counter.to_bytes(COUNTER_LEN, "little")
    for v in sigma:
        out += v
    for node in path:
        out += node
    sig = bytes(out)
    assert len(sig) == SIG_LEN

    if not verify(sk.pk_seed, sk.pk_root, m, sig):
        raise RuntimeError("self-verification failed: refusing to emit signature")

    info = {"idx": idx, "counter": counter, "randomizer": rho, "fors_indices": u,
            "grind_attempts": i + 1, "codeword": x}
    return sig, info


# ============================================================
#  Verification mirror (spec §12)
# ============================================================


class VerifierRevert(Exception):
    """What the on-chain verifier reverts with (Error(string))."""


def verify(pk_seed, pk_root, message, sig):
    """Mirror of LeanSphincs-23Asm.verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig).

    Reverts (raises VerifierRevert) on a wrong signature length or a
    non-canonical key (nonzero low 128 bits of either key word), in that
    order. Returns False for a well-formed signature whose WOTS+C encoding is
    inadmissible or whose root does not match, True otherwise.

    Spec-literal on purpose: every tweak goes through address(), every field
    is sliced at its §11 offset, every Merkle step picks sides by the index bit.
    """
    if len(pk_seed) != 32 or len(pk_root) != 32 or len(message) != MSG_LEN:
        raise ValueError("pkSeed, pkRoot and message are bytes32")
    if len(sig) != SIG_LEN:
        raise VerifierRevert("Invalid sig length")
    if any(pk_seed[16:]) or any(pk_root[16:]):
        raise VerifierRevert("Invalid public key")
    pp, root = pk_seed[:16], pk_root[:16]

    # §5 digest
    rho = sig[OFF_RHO:OFF_RHO + RHO_LEN]
    idx, u = message_digest(pp, rho, message)

    # §7 FORS recover: per tree, leaf + 11 nodes, then order the two tops.
    tops = []
    for kappa in range(K):
        base = OFF_FORS + FORS_TREE_LEN * kappa
        sk = sig[base:base + N]
        p = [sig[base + N + N * l: base + 2 * N + N * l] for l in range(A)]
        uk = u[kappa]
        node = th(pp, address(TW_FTS_LEAF, 0, fors_pos(kappa, 0, uk), idx), sk)
        for l in range(A - 1):
            left, right = (node, p[l]) if (uk >> l) & 1 == 0 else (p[l], node)
            node = th(pp, address(TW_FTS_NODE, 0, fors_pos(kappa, l + 1, uk >> (l + 1)), idx), left + right)
        tops += [node, p[A - 1]] if (uk >> (A - 1)) & 1 == 0 else [p[A - 1], node]
    fors_key = th(pp, address(TW_FTS_KEY, 0, 0, idx), b"".join(tops))

    # §6 WOTS+C recover
    c = int.from_bytes(sig[OFF_COUNTER:OFF_COUNTER + COUNTER_LEN], "little")
    x = wots_codeword(th(pp, address(TW_ENC, 0, 0, idx), fors_key + c.to_bytes(COUNTER_LEN, "little")))
    if x is None:
        return False                    # inadmissible encoding
    ends = []
    for i in range(V):
        val = sig[OFF_WOTS + N * i: OFF_WOTS + N * (i + 1)]
        for to in range(x[i] + 1, CHAIN_LEN):
            val = th(pp, address(TW_CHAIN, to - 1, i, idx), val)
        ends.append(val)
    leaf = th(pp, address(TW_LEAF, 0, 0, idx), b"".join(ends))

    # §8 XMSS fold
    cur = leaf
    for l in range(H):
        sib = sig[OFF_AUTH + N * l: OFF_AUTH + N * (l + 1)]
        left, right = (cur, sib) if (idx >> l) & 1 == 0 else (sib, cur)
        cur = xmss_node(pp, l + 1, idx >> (l + 1), left, right)
    return cur == root


# ============================================================
#  Encoding helpers, CLI
# ============================================================


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def abi_encode(pk_seed, pk_root, sig):
    """abi.encode(bytes32, bytes32, bytes): head (2 words + offset 0x60), length, padded data."""
    enc = pk_seed + pk_root + (0x60).to_bytes(32, "big") + len(sig).to_bytes(32, "big")
    return enc + sig + bytes((-len(sig)) % 32)


def parse_hex(s, length=None, what="value"):
    h = s[2:] if s[:2] in ("0x", "0X") else s
    try:
        data = bytes.fromhex(h)
    except ValueError:
        raise SystemExit(f"error: {what} is not valid hex")
    if length is not None and len(data) != length:
        raise SystemExit(f"error: {what} must be {length} bytes, got {len(data)}")
    return data


def parse_b(s):
    try:
        b = int(s, 0)
    except ValueError:
        raise SystemExit("error: b must be an integer")
    if not 0 <= b <= H:
        raise SystemExit(f"error: b must be in [0, {H}]")
    return b


def keygen_and_sign(seed, b, m):
    t0 = time.perf_counter()
    eprint(f"  keygen b={b} ({1 << b} WOTS leaves, {H - b} surrogates)...")
    sk = keygen(seed, b, log=eprint)
    t1 = time.perf_counter()
    eprint(f"  P = 0x{sk.pp.hex()}  s = {sk.s}  root = 0x{sk.root.hex()}  ({t1 - t0:.2f}s)")
    sig, info = sign(sk, m)
    t2 = time.perf_counter()
    eprint(f"  signed: idx={info['idx']} counter={info['counter']} "
           f"grind={info['grind_attempts']} ({t2 - t1:.2f}s); local verify OK")
    return sk, sig, info, t1 - t0, t2 - t1


def kat_json(seed, b, m, sk, sig, info):
    return {
        "scheme": "leanSphincs-23-keccak",
        "seed": "0x" + seed.hex(),
        "b": b,
        "message": "0x" + m.hex(),
        "pkSeed": "0x" + sk.pk_seed.hex(),
        "pkRoot": "0x" + sk.pk_root.hex(),
        "sig": "0x" + sig.hex(),
        "idx": info["idx"],
        "counter": info["counter"],
        "randomizer": "0x" + info["randomizer"].hex(),
        "fors_indices": list(info["fors_indices"]),
    }


# ============================================================
#  Self-test
# ============================================================


def selftest(bs):
    global keccak256                    # swapped for a counting wrapper below
    ok = True

    def check(cond, what):
        nonlocal ok
        eprint(f"  [{'ok' if cond else 'FAIL'}] {what}")
        ok &= bool(cond)

    eprint("static checks")
    check(keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
          "keccak256('') is Ethereum Keccak-256, not SHA3-256")
    vec = address(10, 5, 0x123456, 0x89abcdef)
    check(vec == bytes.fromhex("efcdab89563412aa0000000000000000"), "§3 address vector")
    check(_pack_u32(0x89abcdef) + _tail(10, 5, 0x123456) == vec, "signer address cache matches address()")
    check(all(_pack_u32(e) + _CHAIN_TAILS[i][st] == address(TW_CHAIN, st, i, e)
              for i in (0, 37, 63) for st in range(3) for e in (0, 1, MASK_H)),
          "chain tails match address()")
    check((OFF_COUNTER, OFF_WOTS, OFF_AUTH, SIG_LEN) == (2720, 2724, 3748, 4148), "§11 offsets")
    check(fors_pos(12, 11, 1) == 12 + 32 * 11 + 512 and fors_pos(12, 0, 4095) < 1 << 21, "§4 pos packing")
    # Digest field split on a synthetic digest with known words.
    words = [0x0FEDCBA987654321, 0x0123456789ABCDEF, 0x0000000ABCDEF123, 0xFFFFFFFFFFFFFFFF]
    d = b"".join(w.to_bytes(8, "little") for w in words)
    idx, u = digest_fields(d)
    check(idx == MASK_H and u[0] == 0x321 and u[4] == 0xFED and u[5] == 0xDEF
          and u[10] == 0x123 and u[12] == 0xABC, "§5 digest field split")

    seed = b"\x11" * 32
    m = b"\xde" * 32
    for b in bs:
        eprint(f"b = {b}")
        sk, sig, info, t_kg, t_sg = keygen_and_sign(seed, b, m)
        pks, pkr = sk.pk_seed, sk.pk_root
        check(len(sig) == SIG_LEN, f"signature is {SIG_LEN} bytes")
        check(verify(pks, pkr, m, sig), "verify accepts")
        check(sig[OFF_RHO:OFF_RHO + 16] == info["randomizer"]
              and int.from_bytes(sig[OFF_COUNTER:OFF_COUNTER + 4], "little") == info["counter"],
              "rho / counter at their offsets")

        # Constant verification cost: 249 keccak256 calls (spec §1).
        real, calls = keccak256, [0]

        def counting(data):
            calls[0] += 1
            return real(data)
        keccak256 = counting
        try:
            verify(pks, pkr, m, sig)
        finally:
            keccak256 = real
        check(calls[0] == 249, f"verify costs {calls[0]} keccak256 calls (expect 249)")

        def flipped(off, mask=0x01):
            bad = bytearray(sig)
            bad[off] ^= mask
            return bytes(bad)

        cases = [
            ("ρ", flipped(OFF_RHO)),
            ("FORS secret κ=12", flipped(OFF_FORS + FORS_TREE_LEN * 12 + N - 1)),
            ("FORS secret κ=0", flipped(OFF_FORS + 3)),
            ("FORS path κ=2 ℓ=11", flipped(OFF_FORS + FORS_TREE_LEN * 2 + N + N * 11)),
            ("FORS path κ=7 ℓ=0", flipped(OFF_FORS + FORS_TREE_LEN * 7 + N + 5)),
            ("counter", flipped(OFF_COUNTER)),
            ("counter high byte", flipped(OFF_COUNTER + 3)),
            ("WOTS σ_11", flipped(OFF_WOTS + N * 11 + 5, 0x04)),
            ("WOTS σ_63", flipped(OFF_WOTS + N * 63 + 15)),
            ("auth path ℓ=7", flipped(OFF_AUTH + N * 7 + 3)),
            ("top auth-path node ℓ=24", flipped(OFF_AUTH + N * 24, 0x80)),
        ]
        for what, bad in cases:
            check(verify(pks, pkr, m, bad) is False, f"tampered {what} -> false")
        check(verify(pks, pkr, bytes([m[0] ^ 1]) + m[1:], sig) is False, "flipped message -> false")
        check(verify(bytes([pks[0] ^ 1]) + pks[1:], pkr, m, sig) is False, "other P -> false")
        check(verify(pks, pkr[:15] + bytes([pkr[15] ^ 1]) + pkr[16:], m, sig) is False, "other root -> false")

        def reverts(reason, *args):
            try:
                verify(*args)
            except VerifierRevert as exc:
                return str(exc) == reason
            return False
        check(reverts("Invalid sig length", pks, pkr, m, sig[:-1]), "short sig reverts")
        check(reverts("Invalid sig length", pks, pkr, m, sig + b"\x00"), "long sig reverts")
        check(reverts("Invalid public key", pks[:31] + b"\x01", pkr, m, sig), "dirty pkSeed reverts")
        check(reverts("Invalid public key", pks, pkr[:16] + b"\x01" + pkr[17:], m, sig), "dirty pkRoot reverts")

        # Determinism, and the ABI encoding against eth_abi when it is installed.
        check(sign(sk, m)[0] == sig, "signing is deterministic")
        enc = abi_encode(pks, pkr, sig)
        try:
            from eth_abi import decode as abi_decode, encode as eth_encode
            check(enc == eth_encode(["bytes32", "bytes32", "bytes"], [pks, pkr, sig]), "ABI encoding matches eth_abi")
            check(tuple(abi_decode(["bytes32", "bytes32", "bytes"], enc)) == (pks, pkr, sig), "ABI round trip")
        except ImportError:
            eprint("  [skip] eth_abi not installed")
        eprint(f"  idx={info['idx']} counter={info['counter']} randomizer attempts={info['grind_attempts']}")
        eprint(f"  sig keccak256 = 0x{keccak256(sig).hex()}")
        eprint(f"  timings: keygen {t_kg:.2f}s, sign {t_sg:.2f}s")
    eprint("ALL OK" if ok else "SELFTEST FAILED")
    return ok


def main(argv):
    usage = ("usage: leansphincs23_signer.py <seed_hex64> <b> <msg_hex64>\n"
             "       leansphincs23_signer.py --json <seed_hex64> <b> <msg_hex64>\n"
             "       leansphincs23_signer.py --verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>\n"
             "       leansphincs23_signer.py --selftest [b ...]")
    if len(argv) >= 1 and argv[0] in ("-h", "--help"):
        print(usage)
        return 0
    if len(argv) >= 1 and argv[0] == "--selftest":
        bs = [parse_b(x) for x in argv[1:]] or [6, 10]
        return 0 if selftest(bs) else 1
    if len(argv) == 5 and argv[0] == "--verify":
        pks = parse_hex(argv[1], 32, "pkSeed")
        pkr = parse_hex(argv[2], 32, "pkRoot")
        m = parse_hex(argv[3], MSG_LEN, "message")
        sig = parse_hex(argv[4], None, "sig")
        try:
            result = verify(pks, pkr, m, sig)
        except VerifierRevert as exc:
            eprint(f"revert: {exc}")
            result = False
        print("true" if result else "false")
        return 0
    as_json = len(argv) == 4 and argv[0] == "--json"
    if as_json:
        argv = argv[1:]
    if len(argv) != 3 or argv[0].startswith("--"):
        eprint(usage)
        return 1
    seed = parse_hex(argv[0], SEED_LEN, "seed")
    b = parse_b(argv[1])
    m = parse_hex(argv[2], MSG_LEN, "message")
    sk, sig, info, _, _ = keygen_and_sign(seed, b, m)
    if as_json:
        print(json.dumps(kat_json(seed, b, m, sk, sig, info)))
    else:
        print("0x" + abi_encode(sk.pk_seed, sk.pk_root, sig).hex())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
