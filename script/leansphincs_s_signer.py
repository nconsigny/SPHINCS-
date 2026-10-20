#!/usr/bin/env python3
"""
leanSphincs-S, leanSphincs-f and leanSphincs signers over keccak256 — independent
Python reference.

CREDIT: the construction is Tom Wambsgans' leanSphincs candidate crate
(TomWambsgans/leanXMSS-leanSPHINCS-candidates, `crates/sphincs` on branch
`keccak`, MIT OR Apache-2.0; itself adapted from leanVM's SPHINCS crate):
Ethereum Keccak-256, a 16-byte tweak, and no FORS key hash (the WOTS+C encoding
absorbs the FORS tops, then the counter). Three parameter sets share it:

    --variant s        leanSphincs-S, the sphincs-art retuning (h = 26, k = 13,
                       a = 12, T = 128): docs/leanSphincs-S-keccak.md ("the spec",
                       section numbers below refer to it). The default.
    --variant f        leanSphincs-f (k = 20, a = 9, T = 122, one-call digest with
                       seven 9-bit indices per word): docs/leanSphincs-f-keccak.md.
    --variant regular  leanSphincs, the upstream keccak branch at its own
                       parameters (k = 24, a = 10, T = 120, upstream's two-call
                       digest): docs/leanSphincs-keccak.md, where the upstream
                       crate is normative.

No upstream code is copied: this file is written from the specs alone, with the
upstream keccak branch as the tie-breaker, so that it can be cross-checked
byte-for-byte against the Rust ports (signers/leansphincs-s-keccak,
signers/leansphincs-f-keccak, signers/leansphincs-keccak) and against the
on-chain verifiers (src/keccak/LeanSphincs-SAsm.sol, LeanSphincs-FAsm.sol,
LeanSphincsAsm.sol).

The core is parameterized (h, a, k, T and the digest layout, class ParamSet):
LEAN_S, LEAN_F and LEAN are the three sets. --upstream-kat runs LEAN (it is the
same as --variant regular --upstream-kat) and reproduces the keccak branch's
`known_answer` test byte for byte: the evidence that the construction here is
upstream's. `--variant regular --selftest` runs it too.

Parameters (spec §1; the other two specs change only a, k, T and the digest):
    n = 16 (node bytes)   |P| = 16   |rho| = 16   |m| = 32   counter c = u32 LE
    WOTS+C: w = 2 bits (chains of 4 positions, 3 steps), v = 64 chains, T
    XMSS:   h = 26, one layer (d = 1), pruned keys keep a subtree of height b
    FORS:   k trees of height a, no per-tree root hash

                     S             f             regular
    a / k / T        12 / 13 / 128  9 / 20 / 122  10 / 24 / 120
    digest           1 call        1 call        2 calls (upstream)
    encoding input   452 B         676 B         804 B
    signature        4,164 B       4,660 B       5,684 B
    verify, calls    249           279           342
    verify, perms    259           290           354

Hash (spec §2), with address(tw) the 16-byte tweak of spec §3:
    Th(P, tw, M)     = keccak256(P ‖ address(tw) ‖ M)[0:16]
    ThPair(P, tw, M) = both 16-byte halves of the same keccak256 (signer PRFs)
    ThFull(P, tw, M) = keccak256(P ‖ address(tw) ‖ M)            (message digest)
    address(t, step, hi, lo) = LE32(lo) ‖ LE24(hi) ‖ (t | step << 5) ‖ 0^8
`P ‖ address` is exactly one 32-byte EVM word, so the "first 16 bytes" of a
digest are the high 128 bits of the KECCAK256 word on-chain.

Merged encoding (spec §6, §7): the WOTS+C one-time key at e = idx signs the 2k
FORS tops directly,
    d = Th(P, address(ENC, 0, 0, e), top_{0,0} ‖ top_{0,1} ‖ … ‖ top_{k-1,1} ‖ LE32(c))
a 452-byte hash input for S; tweak type 11 (the former FORS key hash) is unused.

Signature (spec §11):
    rho(16) ‖ k × [FORS secret(16) ‖ a path nodes(16)] ‖ counter(4, LE)
            ‖ 64 WOTS values(16) ‖ 26 auth-path nodes(16)

Verification costs a constant number of keccak256 calls and Keccak-f
permutations per variant (the table above; the self-test counts both).
verify() below is a spec-literal mirror of the on-chain checks of spec §12 and
is deliberately written without the signer's cached address prefixes, so every
sign() is cross-checked by an independently-coded path before it is emitted.

Usage (every mode takes --variant s|f|regular, anywhere on the line; default s):
    python3 script/leansphincs_s_signer.py [--variant V] <seed_hex64> <b> <msg_hex64>
        -> 0x ‖ hex(abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig))
           pkSeed = P ‖ 0^16, pkRoot = root ‖ 0^16 (high-aligned)
    python3 script/leansphincs_s_signer.py [--variant V] --json <seed_hex64> <b> <msg_hex64>
        -> KAT JSON object (scheme, seed, b, message, pkSeed, pkRoot, sig, idx,
           counter, randomizer, fors_indices)
    python3 script/leansphincs_s_signer.py [--variant V] --verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>
        -> true / false  (an on-chain revert prints false, reason on stderr)
    python3 script/leansphincs_s_signer.py [--variant V] --selftest [b ...]
        -> address vector, digest field map, sign/verify, hash counts, per-field
           tamper checks, timings (default b = 6 10); regular adds --upstream-kat
    python3 script/leansphincs_s_signer.py --upstream-kat
        -> leanSphincs (the upstream keccak branch's parameters): its known_answer
           (key_gen(seed(1), 11), m[i] = 7i) and its unit-test pins, reproduced exactly

Hex arguments are accepted with or without 0x. b is the kept-subtree height
(0 <= b <= 26; b = 26 is a full key, ~1.5e10 keccak calls — infeasible here).
A pruned key grinds the randomizer for ~2^(26-b) digests per signature, so
b ~ 6..12 is the practical range for this Python signer.

Key separation: the three variants derive P, the secrets and the surrogates
identically from the seed, and nothing in a hash input names the parameter
set. One seed is one key of one variant.

Requires pycryptodome (Crypto.Hash.keccak). Not audited, not production-safe.
"""

import contextlib
import json
import struct
import sys
import time

from Crypto.Hash import keccak as _keccak_mod

# ============================================================
#  Fixed parameters (spec §1; shared by every ParamSet)
# ============================================================

N           = 16          # node / hash value bytes
P_LEN       = 16          # public parameter
ADDR_LEN    = 16          # address (tweak)
RHO_LEN     = 16          # randomizer
MSG_LEN     = 32          # message
SEED_LEN    = 32          # master secret S
COUNTER_LEN = 4           # WOTS+C counter, u32 little endian
W           = 2           # bits per WOTS chunk
CHAIN_LEN   = 1 << W      # 4 chain positions (3 hash steps)
V           = 64          # WOTS chains
RATE        = 136         # Keccak-256 sponge rate, bytes

assert W * V == 8 * N
assert P_LEN + ADDR_LEN == 32   # one EVM word

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
TW_ENC        = 4     # WOTS+C encoding (absorbs the FORS tops)
TW_PARAMETER  = 5     # derives P
TW_RANDOMIZER = 7
TW_FTS_PRF    = 8     # FORS secrets
TW_FTS_LEAF   = 9
TW_FTS_NODE   = 10
# 11 is unused: the former FORS key hash (spec §3, §7)
TW_MSG        = 12    # message digest
TW_SURROGATE  = 13    # pruned-key siblings

_Z8 = bytes(8)


def permutations(length):
    """Keccak-f permutations of a keccak256 call over `length` bytes: ⌊L/136⌋ + 1 (spec §1)."""
    return length // RATE + 1


# ============================================================
#  Parameter sets
# ============================================================

# Message-digest layouts. The one-call layout is spec §5 (leanSphincs-S at a = 12, leanSphincs-f at a = 9); the
# two-call layout is the upstream keccak branch's (scheme.rs: message_digest, index_of_block, digest_block),
# which that branch only defines for its a = 10 (leanSphincs).
LAYOUT_ONE_CALL = "one call: ⌊64/a⌋ FORS indices per word in words 0..2, leaf index in word 3"
LAYOUT_UPSTREAM = ("upstream two calls: ⌊64/a⌋ indices per word in words 0, 1 of each call, "
                   "leaf index in word 2 of call 0")


class ParamSet:
    """One instantiation: XMSS height h, k FORS trees of height a, WOTS+C target sum T, digest layout.

    Everything else (n, w, v, the tweak, P, the secrets, the merged encoding,
    the serialization order) is common. The pinned sizes and verification
    costs are recomputed from the parameters and must agree.
    """

    def __init__(self, name, variant, h, a, k, target_sum, layout, sig_len, verify_calls, verify_perms,
                 fail_fast_calls):
        if not (0 < h <= 32 and 0 < a <= 15 and 0 < k <= 32 and 0 < target_sum < V * (CHAIN_LEN - 1)):
            raise ValueError("parameters out of range for the 16-byte tweak")
        self.name, self.variant = name, variant
        self.h, self.a, self.k, self.target_sum, self.layout = h, a, k, target_sum, layout
        self.fors_leaves   = 1 << a
        self.fors_tree_len = (1 + a) * N                          # secret + a path nodes
        self.off_rho       = 0
        self.off_fors      = self.off_rho + RHO_LEN
        self.off_counter   = self.off_fors + k * self.fors_tree_len
        self.off_wots      = self.off_counter + COUNTER_LEN
        self.off_auth      = self.off_wots + V * N
        self.sig_len       = self.off_auth + h * N
        self.mask_h        = (1 << h) - 1
        self.mask_a        = (1 << a) - 1
        self.per_word      = 64 // a                              # no index straddles two 64-bit words
        if layout == LAYOUT_ONE_CALL:
            if k > 3 * self.per_word:
                raise ValueError("one-call digest: the FORS indices must fit in words 0..2")
            self.digest_calls, self.idx_offset = 1, 24            # leaf index: word 3 of the call
        elif layout == LAYOUT_UPSTREAM:
            self.digest_calls = -(-k // (2 * self.per_word))
            self.idx_offset = 16                                  # leaf index: word 2 of call 0
        else:
            raise ValueError("unknown digest layout")
        self.tops_len      = 2 * k * N
        self.enc_input_len = P_LEN + ADDR_LEN + self.tops_len + COUNTER_LEN
        chain_steps = V * (CHAIN_LEN - 1) - target_sum            # constant for every admissible codeword
        # Verification: digest, FORS (leaf + a-1 nodes per tree), encoding, chains, WOTS leaf, auth path.
        self.fail_fast_calls = self.digest_calls + k * a + 1      # an inadmissible counter stops here
        self.verify_calls = self.fail_fast_calls + chain_steps + 1 + h
        self.fail_fast_perms = (self.digest_calls * permutations(32 + MSG_LEN + RHO_LEN)
                                + k * (permutations(32 + N) + (a - 1) * permutations(32 + 2 * N))
                                + permutations(self.enc_input_len))
        self.verify_perms = (self.fail_fast_perms + chain_steps * permutations(32 + N)
                             + permutations(32 + V * N) + h * permutations(32 + 2 * N))
        # Signer's FORS work per signature: k × (2^(a-1) secret pairs + 2^a leaves + 2^a - 2 nodes).
        self.fors_sign_calls = k * ((1 << (a - 1)) + (1 << a) + (1 << a) - 2)
        got = (self.sig_len, self.verify_calls, self.verify_perms, self.fail_fast_calls)
        if got != (sig_len, verify_calls, verify_perms, fail_fast_calls):
            raise AssertionError(f"{name}: sizes/costs {got} differ from the pinned "
                                 f"{(sig_len, verify_calls, verify_perms, fail_fast_calls)}")

    def __repr__(self):
        return f"{self.name} (h={self.h} a={self.a} k={self.k} T={self.target_sum}, sig={self.sig_len} B)"


# leanSphincs-S, the scheme of the spec: 4164-byte signature, 249 keccak256 calls / 259 Keccak-f permutations.
LEAN_S = ParamSet("leanSphincs-S-keccak", "s", h=26, a=12, k=13, target_sum=128, layout=LAYOUT_ONE_CALL,
                  sig_len=4164, verify_calls=249, verify_perms=259, fail_fast_calls=158)
# leanSphincs-f (docs/leanSphincs-f-keccak.md): 4660-byte signature, 279 calls / 290 permutations.
LEAN_F = ParamSet("leanSphincs-f-keccak", "f", h=26, a=9, k=20, target_sum=122, layout=LAYOUT_ONE_CALL,
                  sig_len=4660, verify_calls=279, verify_perms=290, fail_fast_calls=182)
# leanSphincs (docs/leanSphincs-keccak.md), the upstream keccak branch's own set (lib.rs: SIG_SIZE = 5684,
# VERIFY_PERMUTATIONS = 354): 342 calls / 354 permutations.
LEAN = ParamSet("leanSphincs-keccak", "regular", h=26, a=10, k=24, target_sum=120, layout=LAYOUT_UPSTREAM,
                sig_len=5684, verify_calls=342, verify_perms=354, fail_fast_calls=243)
UPSTREAM = LEAN                         # what --upstream-kat runs: the same object as --variant regular

VARIANTS = {ps.variant: ps for ps in (LEAN_S, LEAN_F, LEAN)}

assert (LEAN_S.off_counter, LEAN_S.off_wots, LEAN_S.off_auth) == (2720, 2724, 3748)
assert LEAN_S.sig_len == 16 + 2704 + 4 + 1024 + 416 == 4164
assert LEAN_S.enc_input_len == 452 and LEAN_S.per_word == 5 and LEAN_S.fail_fast_calls == 158
assert LEAN_S.h + LEAN_S.k * LEAN_S.a == 182 <= 256
# leanSphincs-f spec, "Differences" table: §1 sizes, §5 seven indices per word, §6 676-byte input, §11 offsets.
assert (LEAN_F.off_counter, LEAN_F.off_wots, LEAN_F.off_auth, LEAN_F.fors_tree_len) == (3216, 3220, 4244, 160)
assert LEAN_F.sig_len == 16 + 20 * 10 * 16 + 4 + 64 * 16 + 26 * 16 == 4660
assert LEAN_F.enc_input_len == 676 and LEAN_F.per_word == 7 and LEAN_F.digest_calls == 1
assert LEAN_F.h + LEAN_F.k * LEAN_F.a == 206 <= 256 and LEAN_F.fors_sign_calls == 25_560
# leanSphincs spec, "Differences" table: §1 sizes, two digest calls of six indices per word, 804-byte input, §11.
assert (LEAN.off_counter, LEAN.off_wots, LEAN.off_auth, LEAN.fors_tree_len) == (4240, 4244, 5268, 176)
assert LEAN.sig_len == 16 + 24 * 11 * 16 + 4 + 64 * 16 + 26 * 16 == 5684
assert LEAN.enc_input_len == 804 and LEAN.per_word == 6 and LEAN.digest_calls == 2
assert LEAN.h + LEAN.k * LEAN.a == 266 <= 512
assert LEAN_S.fors_sign_calls == 133_094          # spec §14: 13·(2,048 + 4,096 + 4,094)

# ============================================================
#  Hash and address (spec §2, §3)
# ============================================================

# The two hash entry points. keccak256 is what the spec-literal paths
# (verify, th*) call; _kn is the raw constructor the signer's hot loops call.
# hash_counter() swaps both for counting wrappers, so keccak256 must not go
# through the global _kn (a call would count twice).
_new = _keccak_mod.new
_kn = _new


def keccak256(data):
    """Ethereum Keccak-256 (0x01 padding) — the EVM KECCAK256 opcode."""
    return _new(digest_bits=256, data=data).digest()


class HashCount:
    __slots__ = ("calls", "perms")

    def __init__(self):
        self.calls = self.perms = 0

    def add(self, length):
        self.calls += 1
        self.perms += permutations(length)


@contextlib.contextmanager
def hash_counter():
    """Count every keccak256 call (and its permutations) made inside the block, spec-literal or fast path."""
    global keccak256, _kn
    real_k256, real_kn, count = keccak256, _kn, HashCount()

    def counted_k256(data):
        count.add(len(data))
        return real_k256(data)

    def counted_kn(digest_bits, data):
        count.add(len(data))
        return real_kn(digest_bits=digest_bits, data=data)
    keccak256, _kn = counted_k256, counted_kn
    try:
        yield count
    finally:
        keccak256, _kn = real_k256, real_kn


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


def fors_pos(ps, kappa, level, j):
    """pos(κ, ℓ, j) = κ + 32ℓ + 512j (spec §4): κ < 32 in bits 0-4, ℓ < 16 in bits 5-8, j < 2^(a-ℓ) from bit 9.

    The fields are disjoint for every set here: bits 9-20 for a = 12 (S), 9-17 for a = 9 (f; pos < 2^18),
    9-18 for a = 10 (regular, upstream's j < 2^10).
    """
    if not (0 <= kappa < ps.k and 0 <= level < ps.a and 0 <= j < 1 << (ps.a - level)):
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
#  Message digest (spec §5; upstream scheme.rs for LEAN)
# ============================================================


def _u64(d, off):
    return int.from_bytes(d[off:off + 8], "little")


def digest_block(pp, rho, m, call):
    """Digest call `call`: ThFull(P, address(MSG, 0, hi=call, lo=0), m ‖ rho), 80 input bytes."""
    return th_full(pp, address(TW_MSG, 0, call, 0), m + rho)


def digest_fields(ps, blocks):
    """Split the digest call outputs into the leaf index and the k FORS indices.

    One call (spec §5): word_w = u64 LE of D[8w : 8w+8]; idx = word_3 & (2^h - 1);
    u_κ = (word_{κ div p} >> a·(κ mod p)) & (2^a - 1) with p = ⌊64/a⌋ indices
    per word, so no field straddles two words. leanSphincs-S (a = 12, p = 5):
    words 0, 1 hold five indices each, word 2 holds κ = 10..12. leanSphincs-f
    (a = 9, p = 7): words 0, 1 hold κ = 0..13, word 2 holds κ = 14..19 (bits 0-53).

    Upstream two calls (leanSphincs, a = 10): FORS index κ is in call κ div 12,
    word (κ mod 12) div 6 of that call, at bit a·(κ mod 6); idx = word 2 of
    call 0 & (2^h - 1).
    """
    a, pw, mask_a = ps.a, ps.per_word, ps.mask_a
    if ps.layout == LAYOUT_ONE_CALL:
        words = [_u64(blocks[0], 8 * w) for w in range(4)]
        idx = words[3] & ps.mask_h
        u = [(words[kappa // pw] >> (a * (kappa % pw))) & mask_a for kappa in range(ps.k)]
    else:
        per_call = 2 * pw
        idx = _u64(blocks[0], 16) & ps.mask_h
        u = []
        for kappa in range(ps.k):
            r = kappa % per_call
            u.append((_u64(blocks[kappa // per_call], 8 * (r // pw)) >> (a * (r % pw))) & mask_a)
    return idx, u


def message_digest(ps, pp, rho, m):
    """(idx, [u_0..u_{k-1}]) from the ps.digest_calls digest calls."""
    return digest_fields(ps, [digest_block(pp, rho, m, call) for call in range(ps.digest_calls)])


def randomizer(base, i):
    """ρ_i = (u128 LE of R_0 + i) mod 2^128, as 16 little-endian bytes (spec §10)."""
    return ((int.from_bytes(base, "little") + i) & MASK_128).to_bytes(RHO_LEN, "little")


# ============================================================
#  WOTS+C (spec §6)
# ============================================================


def wots_codeword(ps, d):
    """x_i = (X >> 2i) & 3 with X = d as u128 LE; the codeword iff Σ x_i = T, else None."""
    X = int.from_bytes(d, "little")
    x = [(X >> (W * i)) & (CHAIN_LEN - 1) for i in range(V)]
    return x if sum(x) == ps.target_sum else None


def wots_secrets(pp, seed, e):
    """(s_2t, s_2t+1) = ThPair(P, address(PRF, 0, hi=t, lo=e), S), t = 0..31."""
    pe = pp + _pack_u32(e)
    kn = _kn
    out = []
    for t in range(V // 2):
        d = kn(digest_bits=256, data=pe + _PRF_TAILS[t] + seed).digest()
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


def wots_encode(ps, pp, e, tops):
    """Least c in [0, 2^32) whose Th(P, address(ENC, 0, 0, e), tops ‖ LE32(c)) is a codeword.

    Python's keccak has no midstate copy, so each counter re-absorbs the
    fixed part P ‖ address ‖ tops (448 / 672 / 800 bytes for S / f / regular:
    4 / 5 / 6 permutations here; 1 with a midstate, spec §10).
    """
    prefix = pp + _pack_u32(e) + _ENC_TAIL + tops
    assert len(prefix) + COUNTER_LEN == ps.enc_input_len
    kn, pk, target = _kn, _pack_u32, ps.target_sum
    for c in range(1 << 32):
        X = int.from_bytes(kn(digest_bits=256, data=prefix + pk(c)).digest()[:N], "little")
        if (X & _M_LO).bit_count() + 2 * (X & _M_HI).bit_count() == target:
            return c, [(X >> (W * i)) & (CHAIN_LEN - 1) for i in range(V)]
    raise RuntimeError("no admissible WOTS+C encoding in 2^32 counters")


def wots_sign(ps, pp, seed, e, tops):
    """Counter c and σ_i = chain i walked from position 0 up to x_i."""
    c, x = wots_encode(ps, pp, e, tops)
    pe = pp + _pack_u32(e)
    kn = _kn
    sigma = []
    for i, s in enumerate(wots_secrets(pp, seed, e)):
        tails = _CHAIN_TAILS[i]
        for to in range(1, x[i] + 1):
            s = kn(digest_bits=256, data=pe + tails[to - 1] + s).digest()[:N]
        sigma.append(s)
    return c, x, sigma


# ============================================================
#  FORS (spec §7)
# ============================================================


def fors_sign(ps, pp, seed, idx, u):
    """Build FORS instance idx tree by tree, keeping only what the signature needs.

    Returns (secrets[k], paths[k][a], tops), tops being the 2k level-(a-1)
    nodes top_{0,0} ‖ top_{0,1} ‖ … ‖ top_{k-1,1} (no hash folds them: the
    WOTS+C encoding absorbs them). Each tree's levels are dropped once its
    opened secret, its a path nodes and its two tops have been taken, so the
    peak working set is one tree.
    """
    kn, pk = _kn, _pack_u32
    a, half_leaves = ps.a, ps.fors_leaves // 2
    pl = pp + pk(idx)
    prf_t = TW_FTS_PRF << 24
    leaf_t = TW_FTS_LEAF << 24
    node_t = TW_FTS_NODE << 24
    secrets, paths, tops = [], [], []
    for kappa in range(ps.k):
        uk = u[kappa]
        leaves = []
        opened = None
        for t in range(half_leaves):
            # Secret pair at pos(κ, 0, t); leaves 2t, 2t+1 at pos(κ, 0, 2t[+1]).
            d = kn(digest_bits=256, data=pl + pk((kappa + 512 * t) | prf_t) + _Z8 + seed).digest()
            s0, s1 = d[:N], d[N:]
            j = 2 * t
            leaves.append(kn(digest_bits=256, data=pl + pk((kappa + 512 * j) | leaf_t) + _Z8 + s0).digest()[:N])
            leaves.append(kn(digest_bits=256, data=pl + pk((kappa + 512 * (j + 1)) | leaf_t) + _Z8 + s1).digest()[:N])
            if t == uk >> 1:
                opened = s1 if uk & 1 else s0
        path = [leaves[uk ^ 1]]
        below = leaves
        for level in range(1, a):
            base = kappa + 32 * level
            below = [
                kn(digest_bits=256,
                   data=pl + pk((base + 512 * j) | node_t) + _Z8 + below[2 * j] + below[2 * j + 1]).digest()[:N]
                for j in range(len(below) >> 1)
            ]
            path.append(below[(uk >> level) ^ 1])
        assert len(below) == 2          # the two level-(a-1) tops; no tree root
        tops += below
        secrets.append(opened)
        paths.append(path)
    return secrets, paths, b"".join(tops)


# ============================================================
#  XMSS, keys (spec §8, §9)
# ============================================================


def xmss_node(pp, level, j, left, right):
    """node(ℓ, j) = Th(P, address(NODE, 0, hi=ℓ, lo=j), left ‖ right)."""
    return th(pp, address(TW_NODE, 0, level, j), left + right)


class SecretKey:
    __slots__ = ("ps", "seed", "pp", "b", "s", "levels", "surrogates", "root")

    def contains(self, idx):
        return idx >> self.b == self.s

    def auth_path(self, idx):
        """path[ℓ] = kept-subtree sibling for ℓ < b, surrogate for ℓ >= b."""
        assert self.contains(idx)
        local = idx - (self.s << self.b)
        return [self.levels[l][(local >> l) ^ 1] if l < self.b else self.surrogates[l - self.b]
                for l in range(self.ps.h)]

    @property
    def pk_seed(self):
        return self.pp + bytes(16)

    @property
    def pk_root(self):
        return self.root + bytes(16)


def keygen(seed, b, ps=LEAN_S, log=None):
    """Gen with kept-subtree height b (spec §9); b = h is a full key.

    P = Th(0^16, address(PARAMETER, 0, 0, 0), S); the kept subtree's position
    s is the low (h - b) bits of u64 LE P[0:8]; it holds leaves
    [s·2^b, (s+1)·2^b). Surrogate siblings for levels b..h-1 are
    Th(P, address(SURROGATE, 0, hi=ℓ, lo=0), S); the root is the subtree root
    folded through them, bit (ℓ - b) of s choosing the side.
    """
    h = ps.h
    if len(seed) != SEED_LEN:
        raise ValueError("seed must be 32 bytes")
    if not 0 <= b <= h:
        raise ValueError(f"kept-subtree height b must be in [0, {h}]")
    pp = th(bytes(P_LEN), address(TW_PARAMETER, 0, 0, 0), seed)
    s = (int.from_bytes(pp[:8], "little") & ((1 << (h - b)) - 1)) if b < h else 0

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

    surrogates = [th(pp, address(TW_SURROGATE, 0, level, 0), seed) for level in range(b, h)]
    node = levels[b][0]
    for t, sib in enumerate(surrogates):
        j = s >> t                      # this node's index at level b + t
        left, right = (node, sib) if j & 1 == 0 else (sib, node)
        node = xmss_node(pp, b + t + 1, j >> 1, left, right)

    sk = SecretKey()
    sk.ps, sk.seed, sk.pp, sk.b, sk.s = ps, seed, pp, b, s
    sk.levels, sk.surrogates, sk.root = levels, surrogates, node
    return sk


# ============================================================
#  Signing (spec §10, §11)
# ============================================================


def sign(sk, m):
    """Sign a 32-byte message. Returns (sig_bytes, info dict); raises if the mirror rejects."""
    if len(m) != MSG_LEN:
        raise ValueError("message must be 32 bytes")
    ps, pp, seed = sk.ps, sk.pp, sk.seed

    # R_0 = Th(P, address(RANDOMIZER, 0, 0, 0), S ‖ m); rho_i = R_0 + i (u128 LE).
    # Grind on digest call 0 alone, which carries the leaf index.
    r0 = th(pp, address(TW_RANDOMIZER, 0, 0, 0), seed + m)
    prefix = pp + address(TW_MSG, 0, 0, 0) + m
    off, mask_h, b, s = ps.idx_offset, ps.mask_h, sk.b, sk.s
    kn = _kn
    i = 0
    while True:
        rho = randomizer(r0, i)
        d = kn(digest_bits=256, data=prefix + rho).digest()
        if (int.from_bytes(d[off:off + 8], "little") & mask_h) >> b == s:
            break
        i += 1
    idx, u = message_digest(ps, pp, rho, m)
    assert sk.contains(idx)

    fors_secrets, fors_paths, tops = fors_sign(ps, pp, seed, idx, u)
    counter, x, sigma = wots_sign(ps, pp, seed, idx, tops)
    path = sk.auth_path(idx)

    out = bytearray(rho)
    for kappa in range(ps.k):
        out += fors_secrets[kappa]
        for node in fors_paths[kappa]:
            out += node
    out += counter.to_bytes(COUNTER_LEN, "little")
    for v in sigma:
        out += v
    for node in path:
        out += node
    sig = bytes(out)
    assert len(sig) == ps.sig_len

    # The mirror must accept, at exactly the variant's constant cost (spec §1: 249 / 259, 279 / 290, 342 / 354).
    with hash_counter() as hc:
        ok = verify(sk.pk_seed, sk.pk_root, m, sig, ps)
    if not ok:
        raise RuntimeError("self-verification failed: refusing to emit signature")
    if (hc.calls, hc.perms) != (ps.verify_calls, ps.verify_perms):
        raise RuntimeError(f"self-verification cost {hc.calls} calls / {hc.perms} permutations, not the pinned "
                           f"{ps.verify_calls} / {ps.verify_perms}: refusing to emit signature")

    info = {"idx": idx, "counter": counter, "randomizer": rho, "fors_indices": u,
            "grind_attempts": i + 1, "codeword": x}
    return sig, info


# ============================================================
#  Verification mirror (spec §12)
# ============================================================


class VerifierRevert(Exception):
    """What the on-chain verifier reverts with (Error(string))."""


def verify(pk_seed, pk_root, message, sig, ps=LEAN_S):
    """Mirror of verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig) in LeanSphincs-SAsm
    (ps = LEAN_S), LeanSphincs-FAsm (LEAN_F) or LeanSphincsAsm (LEAN).

    Reverts (raises VerifierRevert) on a wrong signature length (ps.sig_len) or a
    non-canonical key (nonzero low 128 bits of either key word), in that
    order. Returns False for a well-formed signature whose WOTS+C encoding is
    inadmissible or whose root does not match, True otherwise.

    Spec-literal on purpose: every tweak goes through address(), every field
    is sliced at its §11 offset, every Merkle step picks sides by the index bit.
    """
    if len(pk_seed) != 32 or len(pk_root) != 32 or len(message) != MSG_LEN:
        raise ValueError("pkSeed, pkRoot and message are bytes32")
    if len(sig) != ps.sig_len:
        raise VerifierRevert("Invalid sig length")
    if any(pk_seed[16:]) or any(pk_root[16:]):
        raise VerifierRevert("Invalid public key")
    pp, root = pk_seed[:16], pk_root[:16]
    a = ps.a

    # §5 digest
    rho = sig[ps.off_rho:ps.off_rho + RHO_LEN]
    idx, u = message_digest(ps, pp, rho, message)

    # §7 FORS recover: per tree, leaf + (a-1) nodes, then order the two tops.
    tops = []
    for kappa in range(ps.k):
        base = ps.off_fors + ps.fors_tree_len * kappa
        sk = sig[base:base + N]
        p = [sig[base + N + N * l: base + 2 * N + N * l] for l in range(a)]
        uk = u[kappa]
        node = th(pp, address(TW_FTS_LEAF, 0, fors_pos(ps, kappa, 0, uk), idx), sk)
        for l in range(a - 1):
            left, right = (node, p[l]) if (uk >> l) & 1 == 0 else (p[l], node)
            node = th(pp, address(TW_FTS_NODE, 0, fors_pos(ps, kappa, l + 1, uk >> (l + 1)), idx), left + right)
        tops += [node, p[a - 1]] if (uk >> (a - 1)) & 1 == 0 else [p[a - 1], node]

    # §6 WOTS+C recover: the encoding absorbs the tops, then the counter.
    c = int.from_bytes(sig[ps.off_counter:ps.off_counter + COUNTER_LEN], "little")
    x = wots_codeword(ps, th(pp, address(TW_ENC, 0, 0, idx), b"".join(tops) + c.to_bytes(COUNTER_LEN, "little")))
    if x is None:
        return False                    # inadmissible encoding
    ends = []
    for i in range(V):
        val = sig[ps.off_wots + N * i: ps.off_wots + N * (i + 1)]
        for to in range(x[i] + 1, CHAIN_LEN):
            val = th(pp, address(TW_CHAIN, to - 1, i, idx), val)
        ends.append(val)
    leaf = th(pp, address(TW_LEAF, 0, 0, idx), b"".join(ends))

    # §8 XMSS fold
    cur = leaf
    for l in range(ps.h):
        sib = sig[ps.off_auth + N * l: ps.off_auth + N * (l + 1)]
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


def parse_b(s, ps=LEAN_S):
    try:
        b = int(s, 0)
    except ValueError:
        raise SystemExit("error: b must be an integer")
    if not 0 <= b <= ps.h:
        raise SystemExit(f"error: b must be in [0, {ps.h}]")
    return b


def keygen_and_sign(seed, b, m, ps=LEAN_S):
    t0 = time.perf_counter()
    eprint(f"  keygen b={b} ({1 << b} WOTS leaves, {ps.h - b} surrogates)...")
    sk = keygen(seed, b, ps, log=eprint)
    t1 = time.perf_counter()
    eprint(f"  P = 0x{sk.pp.hex()}  s = {sk.s}  root = 0x{sk.root.hex()}  ({t1 - t0:.2f}s)")
    sig, info = sign(sk, m)
    t2 = time.perf_counter()
    eprint(f"  signed: idx={info['idx']} counter={info['counter']} "
           f"grind={info['grind_attempts']} ({t2 - t1:.2f}s); local verify OK")
    if ps is not LEAN_S:   # leanSphincs-S keeps its exact stderr; the others name their set
        eprint(f"  {ps.name}: {ps.sig_len}-byte signature, verified at {ps.verify_calls} keccak256 calls / "
               f"{ps.verify_perms} permutations")
    return sk, sig, info, t1 - t0, t2 - t1


def kat_json(seed, b, m, sk, sig, info):
    return {
        "scheme": sk.ps.name,
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


class Checker:
    def __init__(self):
        self.ok = True

    def __call__(self, cond, what):
        eprint(f"  [{'ok' if cond else 'FAIL'}] {what}")
        self.ok &= bool(cond)


def reverts(reason, *args):
    try:
        verify(*args)
    except VerifierRevert as exc:
        return str(exc) == reason
    return False


def keygen_cost(b, ps):
    """keccak256 calls and permutations of keygen(b): P, 2^b WOTS leaves, 2^b - 1 nodes, 2 per surrogate."""
    leaf_calls = V // 2 + V * (CHAIN_LEN - 1) + 1                                  # 225
    leaf_perms = V // 2 + V * (CHAIN_LEN - 1) + permutations(32 + V * N)           # 232
    rest = 1 + ((1 << b) - 1) + 2 * (ps.h - b)
    return (1 << b) * leaf_calls + rest, (1 << b) * leaf_perms + rest


# ============================================================
#  Self-test (every variant)
# ============================================================

# Literal pins per variant, transcribed from the three specs (docs/leanSphincs-S-keccak.md §1, §4, §5, §6, §11, §14;
# docs/leanSphincs-f-keccak.md and docs/leanSphincs-keccak.md: the "Differences from leanSphincs-S" table, the
# message-digest and verification-work paragraphs). None is computed from ParamSet, so a slip in its formulas shows
# here rather than agreeing with itself.
#   tree       bytes per FORS tree in the signature: secret + a path nodes (§11)
#   enc        encoding input bytes / its verifier permutations / whole blocks of the signer's fixed part (§6, §10)
#   verify     keccak256 calls / Keccak-f permutations of every accepted signature (§1)
#   fail_fast  the same for an inadmissible counter: digest, FORS, encoding (calls as the specs give them;
#              permutations by the §1 rule: digest + k·a + the encoding's)
#   p_code     P[Σx = T] as the spec rounds it, and the mean encoding tries it quotes (§1)
#   words      used low bits of the four 64-bit words of each digest call (§5; leanSphincs: "Message digest")
#   loc_u      (call, word, bit) of bit 0 of u_κ, as the spec writes it; loc_idx the same for idx
#   fors_sign  the signer's FORS calls per signature, k·(2^(a-1) + 2^a + 2^a - 2) (§14; leanSphincs-f "Signing")
SPEC_PINS = {
    "s": dict(
        name="leanSphincs-S-keccak", a=12, k=13, T=128, sig_len=4164, tree=208,
        off_counter=2720, off_wots=2724, off_auth=3748, enc=(452, 4, 3), verify=(249, 259), fail_fast=(158, 161),
        p_code=(6.82e-5, 14_670), digest_bits=182, pos_bound=1 << 21, fors_sign=133_094,
        words=[(60, 60, 36, 26)],
        loc_u=lambda kappa: (0, kappa // 5, 12 * (kappa % 5)), loc_idx=(0, 3, 0)),
    "f": dict(
        name="leanSphincs-f-keccak", a=9, k=20, T=122, sig_len=4660, tree=160,
        off_counter=3216, off_wots=3220, off_auth=4244, enc=(676, 5, 4), verify=(279, 290), fail_fast=(182, 186),
        p_code=(6.38e-4, 1_566), digest_bits=206, pos_bound=1 << 18, fors_sign=25_560,
        words=[(63, 63, 54, 26)],
        loc_u=lambda kappa: (0, kappa // 7, 9 * (kappa % 7)), loc_idx=(0, 3, 0)),
    "regular": dict(
        name="leanSphincs-keccak", a=10, k=24, T=120, sig_len=5684, tree=176,
        off_counter=4240, off_wots=4244, off_auth=5268, enc=(804, 6, 5), verify=(342, 354), fail_fast=(243, 248),
        p_code=(1.21e-3, 829), digest_bits=266, pos_bound=1 << 19, fors_sign=24 * (512 + 1024 + 1022),
        words=[(60, 60, 26, 0), (60, 60, 0, 0)],
        loc_u=lambda kappa: (kappa // 12, kappa % 12 // 6, 10 * (kappa % 6)), loc_idx=(0, 2, 0)),
}
# Every signature length a verifier here pins, and leanSphincs-23's (retired to legacy/): each verifier must revert
# on all of them but its own.
SIG_LENGTHS = {4148: "leanSphincs-23", 4164: "leanSphincs-S", 4660: "leanSphincs-f", 5684: "leanSphincs"}


def codeword_probability(target):
    """P[Σ x_i = T] for 64 uniform 2-bit chunks, exactly: the coefficient of z^T in ((1 + z + z² + z³)/4)^64."""
    coeffs = [1]
    for _ in range(V):
        nxt = [0] * (len(coeffs) + CHAIN_LEN - 1)
        for i, c in enumerate(coeffs):
            for x in range(CHAIN_LEN):
                nxt[i + x] += c
        coeffs = nxt
    return coeffs[target] / CHAIN_LEN ** V


def digest_field_map(ps):
    """{(call, word, bit): [field bits]}: the field bits ("idx", t) or ("u", κ, t) each digest bit feeds.

    digest_fields only shifts and masks, so every field bit is one digest bit: setting one bit of all-zero digest
    calls at a time maps the whole function. A correct layout feeds at most one field bit from each digest bit.
    """
    out = {}
    for call in range(ps.digest_calls):
        for w in range(4):
            for bit in range(64):
                blocks = [bytearray(32) for _ in range(ps.digest_calls)]
                blocks[call][8 * w: 8 * w + 8] = (1 << bit).to_bytes(8, "little")
                idx, u = digest_fields(ps, [bytes(blk) for blk in blocks])
                out[(call, w, bit)] = ([("idx", t) for t in range(ps.h) if idx >> t & 1]
                                       + [("u", kappa, t) for kappa in range(ps.k) for t in range(ps.a)
                                          if u[kappa] >> t & 1])
    return out


def sig_fields(ps):
    """Every spec §11 field of a signature, in order, as (name, offset, length)."""
    fields = [("ρ", ps.off_rho, RHO_LEN)]
    for kappa in range(ps.k):
        base = ps.off_fors + ps.fors_tree_len * kappa
        fields.append((f"FORS secret κ={kappa}", base, N))
        fields += [(f"FORS path κ={kappa} ℓ={l}", base + N + N * l, N) for l in range(ps.a)]
    fields.append(("counter", ps.off_counter, COUNTER_LEN))
    fields += [(f"WOTS σ_{i}", ps.off_wots + N * i, N) for i in range(V)]
    fields += [(f"auth path ℓ={l}", ps.off_auth + N * l, N) for l in range(ps.h)]
    return fields


def spec_literal_fields(ps, sk, m, sig, info, tops):
    """Names of the signature fields that differ from a spec-literal recomputation (address(), th, th_pair) from S.

    Covers what acceptance alone cannot vouch for: ρ is R_0 + (attempts - 1) (§10); each FORS secret is the opened
    half of its ThPair (§7); each σ_i is s_i walked to x_i (§6); the counter is the least admissible one for `tops`
    (§6); the auth path is the key's (§8, §9).
    """
    pp, seed, idx, u, x = sk.pp, sk.seed, info["idx"], info["fors_indices"], info["codeword"]
    bad = []
    r0 = th(pp, address(TW_RANDOMIZER, 0, 0, 0), seed + m)
    if sig[ps.off_rho:ps.off_rho + RHO_LEN] != randomizer(r0, info["grind_attempts"] - 1):
        bad.append("ρ")
    for kappa in range(ps.k):
        off = ps.off_fors + ps.fors_tree_len * kappa
        pair = th_pair(pp, address(TW_FTS_PRF, 0, fors_pos(ps, kappa, 0, u[kappa] >> 1), idx), seed)
        if sig[off:off + N] != pair[u[kappa] & 1]:
            bad.append(f"FORS secret κ={kappa}")
    for t in range(V // 2):
        pair = th_pair(pp, address(TW_PRF, 0, t, idx), seed)
        for half in (0, 1):
            i, val = 2 * t + half, pair[half]
            for to in range(1, x[i] + 1):
                val = th(pp, address(TW_CHAIN, to - 1, i, idx), val)
            if sig[ps.off_wots + N * i: ps.off_wots + N * (i + 1)] != val:
                bad.append(f"WOTS σ_{i}")
    tw = address(TW_ENC, 0, 0, idx)
    if int.from_bytes(sig[ps.off_counter:ps.off_counter + COUNTER_LEN], "little") != info["counter"]:
        bad.append("counter")
    for c in range(info["counter"]):
        if wots_codeword(ps, th(pp, tw, tops + c.to_bytes(COUNTER_LEN, "little"))) is not None:
            bad.append(f"counter (c = {c} < {info['counter']} is admissible)")
            break
    for l, node in enumerate(sk.auth_path(idx)):
        if sig[ps.off_auth + N * l: ps.off_auth + N * (l + 1)] != node:
            bad.append(f"auth path ℓ={l}")
    return bad


def selftest_static(ps, pin, check):
    """Checks that need no signature: hash, address, the signer's address cache, sizes, costs, packing, digest map."""
    eprint(f"static checks: {ps!r}")
    check(keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
          "keccak256('') is Ethereum Keccak-256, not SHA3-256")
    vec = address(10, 5, 0x123456, 0x89abcdef)
    check(vec == bytes.fromhex("efcdab89563412aa0000000000000000"), "§3 address vector")
    check(_pack_u32(0x89abcdef) + _tail(10, 5, 0x123456) == vec, "signer address cache matches address()")
    check(all(_pack_u32(e) + _CHAIN_TAILS[i][st] == address(TW_CHAIN, st, i, e)
              for i in (0, 37, 63) for st in range(3) for e in (0, 1, ps.mask_h)),
          "chain tails match address()")
    check(all(_pack_u32(e) + _PRF_TAILS[t] == address(TW_PRF, 0, t, e) for t in (0, 31) for e in (0, ps.mask_h))
          and _pack_u32(9) + _ENC_TAIL == address(TW_ENC, 0, 0, 9)
          and _pack_u32(9) + _LEAF_TAIL == address(TW_LEAF, 0, 0, 9),
          "PRF / ENC / LEAF tails match address()")

    # Parameters and §11 layout, against the spec's literal numbers.
    check((ps.name, ps.h, ps.a, ps.k, ps.target_sum) == (pin["name"], 26, pin["a"], pin["k"], pin["T"]),
          f"§1 {pin['name']}: h = 26, a = {pin['a']}, k = {pin['k']}, T = {pin['T']}")
    check((ps.fors_tree_len, ps.off_counter, ps.off_wots, ps.off_auth, ps.sig_len)
          == (pin["tree"], pin["off_counter"], pin["off_wots"], pin["off_auth"], pin["sig_len"]),
          f"§11 offsets: tree {pin['tree']} B, counter {pin['off_counter']}, WOTS {pin['off_wots']}, "
          f"auth {pin['off_auth']}, {pin['sig_len']} bytes")
    # The §11 table, written out from the pins: ρ 0; secret 16 + tree·κ; path 32 + tree·κ + 16ℓ; counter; σ_i; path.
    expect = [("ρ", 0, 16)]
    for kappa in range(pin["k"]):
        expect.append((f"FORS secret κ={kappa}", 16 + pin["tree"] * kappa, 16))
        expect += [(f"FORS path κ={kappa} ℓ={l}", 32 + pin["tree"] * kappa + 16 * l, 16) for l in range(pin["a"])]
    expect.append(("counter", pin["off_counter"], 4))
    expect += [(f"WOTS σ_{i}", pin["off_wots"] + 16 * i, 16) for i in range(64)]
    expect += [(f"auth path ℓ={l}", pin["off_auth"] + 16 * l, 16) for l in range(26)]
    tiled = all(off == prev_off + prev_len for (_, prev_off, prev_len), (_, off, _) in zip(expect, expect[1:]))
    check(sig_fields(ps) == expect and tiled and expect[-1][1] + expect[-1][2] == pin["sig_len"],
          f"§11 the {len(expect)} fields tile the {pin['sig_len']} bytes: FORS secret 16 + {pin['tree']}κ, "
          f"path 32 + {pin['tree']}κ + 16ℓ")

    # §4: pos(κ, ℓ, j) is injective over every FORS node of an instance, below the spec's bound.
    every_pos = [fors_pos(ps, kappa, level, j)
                 for kappa in range(ps.k) for level in range(ps.a) for j in range(1 << (ps.a - level))]
    check(len(set(every_pos)) == len(every_pos) and max(every_pos) < pin["pos_bound"] <= 1 << 24,
          f"§4 pos packing injective over {len(every_pos)} nodes, max {max(every_pos)} < 2^"
          f"{pin['pos_bound'].bit_length() - 1}")

    # §5: the digest field map, bit by bit, against the spec's layout.
    fmap = digest_field_map(ps)
    shared = [loc for loc, hits in fmap.items() if len(hits) > 1]
    check(not shared, "§5 no digest bit feeds two field bits" + (f": {shared[:3]}" if shared else ""))
    used = {loc: hits[0] for loc, hits in fmap.items() if hits}
    want = {("idx", t) for t in range(ps.h)} | {("u", kappa, t) for kappa in range(pin["k"]) for t in range(pin["a"])}
    per_word = [tuple(sum(1 for b in range(64) if fmap[(c, w, b)]) for w in range(4)) for c in range(ps.digest_calls)]
    low_bits = all(fmap[(c, w, b)] for (c, w, b) in fmap if b < per_word[c][w])
    c0, w0, b0 = pin["loc_idx"]
    placed = (all(fmap[(c0, w0, b0 + t)] == [("idx", t)] for t in range(26))
              and all(fmap[(c, w, b + t)] == [("u", kappa, t)]
                      for kappa in range(pin["k"]) for (c, w, b) in [pin["loc_u"](kappa)] for t in range(pin["a"])))
    check(set(used.values()) == want and len(used) == pin["digest_bits"] and per_word == pin["words"] and low_bits
          and placed,
          f"§5 digest field map: {pin['digest_bits']} bits in {ps.digest_calls} call(s), used low bits per word "
          f"{per_word}, every u_κ and idx where the spec puts it")
    ones = digest_fields(ps, [b"\xff" * 32] * ps.digest_calls)
    check(ones == (ps.mask_h, [ps.mask_a] * ps.k), "§5 an all-ones digest gives idx = 2^26 - 1, every u_κ = 2^a - 1")
    if ps.variant == "s":
        # Synthetic digest with known words (unchanged from the leanSphincs-S-only self-test).
        words = [0x0FEDCBA987654321, 0x0123456789ABCDEF, 0x0000000ABCDEF123, 0xFFFFFFFFFFFFFFFF]
        d = b"".join(w.to_bytes(8, "little") for w in words)
        idx, u = digest_fields(ps, [d])
        check(idx == (1 << 26) - 1 and u[0] == 0x321 and u[4] == 0xFED and u[5] == 0xDEF
              and u[10] == 0x123 and u[12] == 0xABC, "§5 digest field split")
        check(digest_fields(ps, [d[:24] + (1 << 26).to_bytes(8, "little")])[0] == 0,
              "§5 leaf index is word_3 mod 2^26")
    elif ps.variant == "f":
        # u_κ = (word_{⌊κ/7⌋} >> 9·(κ mod 7)) & 0x1FF; bit 63 of words 0, 1 and bits 54.. of word 2 are unused.
        words = [1 << 63 | 0x1AB << 54 | 0x0CD, 1 << 63 | 0x155 << 9, 1 << 54 | 0x1FF << 45 | 0x042, 1 << 26 | 5]
        d = b"".join(w.to_bytes(8, "little") for w in words)
        expect = [0] * 20
        expect[0], expect[6], expect[8], expect[14], expect[19] = 0x0CD, 0x1AB, 0x155, 0x042, 0x1FF
        check(digest_fields(ps, [d]) == (5, expect), "§5 digest field split (seven 9-bit indices per word)")
    else:
        # Call c = ⌊κ/12⌋, r = κ mod 12: u_κ = (word_{c, ⌊r/6⌋} >> 10·(r mod 6)) & 0x3FF; idx = word_{0,2} mod 2^26.
        call0 = [0xF << 60 | 0x3FF << 50, 1, 1 << 26 | 7, (1 << 64) - 1]
        call1 = [0x2AA, 0x3FF << 50, (1 << 64) - 1, (1 << 64) - 1]
        blocks = [b"".join(w.to_bytes(8, "little") for w in ws) for ws in (call0, call1)]
        expect = [0] * 24
        expect[5], expect[6], expect[12], expect[23] = 0x3FF, 1, 0x2AA, 0x3FF
        check(digest_fields(ps, blocks) == (7, expect), "§5 two-call digest field split (upstream's)")

    # §1 / §6 / §10 sizes and costs.
    enc_len, enc_perms, enc_blocks = pin["enc"]
    tops = b"".join(bytes([2 * kappa + half]) * N for kappa in range(ps.k) for half in (0, 1))
    pp3 = bytes([3]) * P_LEN
    with hash_counter() as hc:
        th(pp3, address(TW_ENC, 0, 0, 77), tops + (5).to_bytes(COUNTER_LEN, "little"))
    check(ps.enc_input_len == enc_len and (hc.calls, hc.perms) == (1, enc_perms)
          and (P_LEN + ADDR_LEN + len(tops)) // RATE == enc_blocks,
          f"§6 encoding input {enc_len} B costs {enc_perms} permutations; the signer absorbs {enc_blocks} whole "
          f"blocks once, then one per counter")
    check((ps.verify_calls, ps.verify_perms) == pin["verify"] and (ps.fail_fast_calls, ps.fail_fast_perms)
          == pin["fail_fast"],
          f"§1 verification: {pin['verify'][0]} calls / {pin['verify'][1]} permutations; an inadmissible counter "
          f"stops at {pin['fail_fast'][0]} / {pin['fail_fast'][1]}")
    check(permutations(32 + V * N) == 8 and permutations(80) == 1 and ps.digest_calls == len(pin["words"]),
          f"§1 WOTS leaf (1056 B) = 8, digest (80 B) = 1 permutation, {len(pin['words'])} digest call(s)")
    p = codeword_probability(ps.target_sum)
    check(abs(p / pin["p_code"][0] - 1) < 0.005 and round(1 / p) == pin["p_code"][1],
          f"§1 P[Σx = {ps.target_sum}] = {p:.4g} (spec {pin['p_code'][0]:.3g}), {1 / p:,.1f} tries "
          f"(spec about {pin['p_code'][1]:,})")
    check(ps.fors_sign_calls == pin["fors_sign"], f"FORS signing work {pin['fors_sign']:,} calls per signature")
    with hash_counter() as hc:
        keygen(b"\x22" * 32, 3, ps)
    check((hc.calls, hc.perms) == keygen_cost(3, ps),
          f"keygen b=3 costs {hc.calls} calls / {hc.perms} permutations (expect {keygen_cost(3, ps)})")
    # Key separation (each spec's last section): nothing in a hash input names the set, so one seed and b give the
    # same P, s and root in all three variants. One seed is one key of one variant.
    keys = [keygen(b"\x33" * 32, 3, other) for other in VARIANTS.values()]
    check(len({(key.pp, key.s, key.root) for key in keys}) == 1,
          "key separation: one seed gives the same key in every variant (so a seed must serve one variant only)")


def selftest(bs, ps=LEAN_S):
    """Static checks, then for each b: sign, verify, exact costs, spec-literal fields, per-field tampering, reverts."""
    pin = SPEC_PINS[ps.variant]
    check = Checker()
    selftest_static(ps, pin, check)
    A, K, H = ps.a, ps.k, ps.h
    verify_cost, fail_fast_cost = pin["verify"], pin["fail_fast"]

    seed = b"\x11" * 32
    m = b"\xde" * 32
    for b in bs:
        eprint(f"b = {b}")
        sk, sig, info, t_kg, t_sg = keygen_and_sign(seed, b, m, ps)
        pks, pkr = sk.pk_seed, sk.pk_root
        check(len(sig) == pin["sig_len"], f"signature is {pin['sig_len']} bytes")
        check(verify(pks, pkr, m, sig, ps), "verify accepts")
        check(sig[ps.off_rho:ps.off_rho + 16] == info["randomizer"]
              and int.from_bytes(sig[ps.off_counter:ps.off_counter + 4], "little") == info["counter"],
              "rho / counter at their offsets")
        check(sk.contains(info["idx"]) and len(info["fors_indices"]) == pin["k"]
              and all(0 <= x < 1 << pin["a"] for x in info["fors_indices"]) and sum(info["codeword"]) == pin["T"],
              f"idx in the kept subtree, {pin['k']} FORS indices < 2^{pin['a']}, codeword sums to {pin['T']}")
        check(message_digest(ps, sk.pp, info["randomizer"], m) == (info["idx"], info["fors_indices"]),
              "idx and FORS indices are the digest of (ρ, m)")
        kat = json.loads(json.dumps(kat_json(seed, b, m, sk, sig, info)))
        check(kat["scheme"] == pin["name"] and len(kat["fors_indices"]) == pin["k"] and kat["sig"] == "0x" + sig.hex()
              and kat["idx"] == info["idx"] and kat["counter"] == info["counter"],
              f"--json KAT: scheme {pin['name']}, {pin['k']} fors_indices")

        # Constant verification cost (spec §1).
        with hash_counter() as hc:
            verify(pks, pkr, m, sig, ps)
        check((hc.calls, hc.perms) == verify_cost,
              f"verify costs {hc.calls} keccak256 calls / {hc.perms} permutations "
              f"(expect {verify_cost[0]} / {verify_cost[1]})")

        # The FORS part again, measured: k·(2^(a-1) + 2^a + 2^a - 2) calls, one permutation each.
        with hash_counter() as hc:
            f_secrets, f_paths, tops = fors_sign(ps, sk.pp, seed, info["idx"], info["fors_indices"])
        f_part = b"".join(f_secrets[kappa] + b"".join(f_paths[kappa]) for kappa in range(K))
        check(hc.calls == hc.perms == pin["fors_sign"] and f_part == sig[ps.off_fors:ps.off_counter]
              and len(tops) == 2 * K * N,
              f"FORS signing costs {hc.calls:,} calls / {hc.perms:,} permutations and reproduces the FORS part")
        bad_fields = spec_literal_fields(ps, sk, m, sig, info, tops)
        check(not bad_fields, "ρ, FORS secrets, σ_i, least counter and auth path match a spec-literal recomputation"
              + (f": {bad_fields[:4]}" if bad_fields else ""))

        def flipped(off, mask=0x01):
            bad = bytearray(sig)
            bad[off] ^= mask
            return bytes(bad)

        # Every §11 field, one bit each (the byte and bit vary along the signature).
        fields = sig_fields(ps)
        accepted = [what for j, (what, off, length) in enumerate(fields)
                    if verify(pks, pkr, m, flipped(off + (5 * j) % length, 1 << (j % 8)), ps) is not False]
        check(not accepted, f"each of the {len(fields)} §11 fields tampered (one bit) -> false"
              + (f"; accepted: {accepted[:4]}" if accepted else ""))
        # The upstream tampered_signatures_are_rejected cases, at this variant's k and a.
        cases = [
            ("ρ", flipped(ps.off_rho)),
            (f"FORS secret κ={K - 1}", flipped(ps.off_fors + ps.fors_tree_len * (K - 1) + N - 1)),
            ("FORS secret κ=0", flipped(ps.off_fors + 3)),
            (f"FORS path κ=2 ℓ={A - 1} (a top)", flipped(ps.off_fors + ps.fors_tree_len * 2 + N + N * (A - 1))),
            ("FORS path κ=7 ℓ=0", flipped(ps.off_fors + ps.fors_tree_len * 7 + N + 5)),
            (f"FORS path κ={K - 1} ℓ=6", flipped(ps.off_fors + ps.fors_tree_len * (K - 1) + N + N * 6 + 15)),
            ("counter", flipped(ps.off_counter)),
            ("counter high byte", flipped(ps.off_counter + 3)),
            ("WOTS σ_0", flipped(ps.off_wots)),
            ("WOTS σ_11", flipped(ps.off_wots + N * 11 + 5, 0x04)),
            ("WOTS σ_63", flipped(ps.off_wots + N * 63 + 15)),
            ("auth path ℓ=0", flipped(ps.off_auth + 1)),
            ("auth path ℓ=7", flipped(ps.off_auth + N * 7 + 3)),
            (f"top auth-path node ℓ={H - 1}", flipped(ps.off_auth + N * (H - 1), 0x80)),
        ]
        for what, bad in cases:
            check(verify(pks, pkr, m, bad, ps) is False, f"tampered {what} -> false")
        check(verify(pks, pkr, bytes([m[0] ^ 1]) + m[1:], sig, ps) is False, "flipped message -> false")
        check(verify(pks, pkr, m[:31] + bytes([m[31] ^ 0x80]), sig, ps) is False, "flipped last message bit -> false")
        check(verify(bytes([pks[0] ^ 1]) + pks[1:], pkr, m, sig, ps) is False, "other P -> false")
        check(verify(pks, pkr[:15] + bytes([pkr[15] ^ 1]) + pkr[16:], m, sig, ps) is False, "other root -> false")

        # Other counters (as upstream's tampered_signatures_are_rejected): never accepted; an inadmissible one
        # stops after digest + FORS + encoding (spec §1).
        inadmissible, costs_ok = 0, True
        for delta in range(1, 41):
            bad = bytearray(sig)
            bad[ps.off_counter:ps.off_counter + 4] = ((info["counter"] + delta) & 0xFFFFFFFF).to_bytes(4, "little")
            with hash_counter() as hc:
                res = verify(pks, pkr, m, bytes(bad), ps)
            costs_ok &= res is False and (hc.calls, hc.perms) in (fail_fast_cost, verify_cost)
            inadmissible += (hc.calls, hc.perms) == fail_fast_cost
        check(costs_ok and inadmissible > 30,
              f"40 other counters rejected, {inadmissible} inadmissible at {fail_fast_cost[0]} calls / "
              f"{fail_fast_cost[1]} permutations")

        # Reverts, in the contract's order: the length first, then the key.
        check(reverts("Invalid sig length", pks, pkr, m, sig[:-1], ps), "short sig reverts")
        check(reverts("Invalid sig length", pks, pkr, m, sig + b"\x00", ps), "long sig reverts")
        check(reverts("Invalid sig length", pks, pkr, m, b"", ps), "empty sig reverts")
        for length, scheme in SIG_LENGTHS.items():
            if length != pin["sig_len"]:
                padded = (sig + bytes(length))[:length]
                check(reverts("Invalid sig length", pks, pkr, m, padded, ps),
                      f"a {scheme}-length ({length} B) sig reverts")
        check(reverts("Invalid public key", pks[:31] + b"\x01", pkr, m, sig, ps), "dirty pkSeed reverts")
        check(reverts("Invalid public key", pks, pkr[:16] + b"\x01" + pkr[17:], m, sig, ps), "dirty pkRoot reverts")
        check(reverts("Invalid sig length", pks[:31] + b"\x01", pkr, m, sig[:-1], ps),
              "dirty key and bad length: the length check runs first")

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
    eprint("ALL OK" if check.ok else "SELFTEST FAILED")
    return check.ok


# ============================================================
#  Upstream known answer: leanSphincs (--variant regular), the keccak branch at its own parameters
# ============================================================

# crates/sphincs/src/scheme.rs (branch keccak), test `known_answer`:
#   key_gen(&seed(1), 11), m[i] = 7i as u8, keccak::hash(sig.to_bytes()), sig.counter.
UPSTREAM_KAT_PK      = "63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00"
UPSTREAM_KAT_SIG_K   = "9a21b6bc61d6ba500b4d67809912c1424be1f58486eda144e4ef70afd01cf94d"
UPSTREAM_KAT_COUNTER = 1176


def upstream_seed(x):
    """Upstream test helper seed(x): byte i = x·31 + i (mod 256)."""
    return bytes((x * 31 + i) & 0xFF for i in range(SEED_LEN))


def upstream_kat():
    """Run leanSphincs (the upstream keccak branch's parameters) and reproduce that branch's pinned tests exactly.

    docs/leanSphincs-keccak.md makes the crate normative for this variant, so this is its conformance test: the
    ParamSet is the one `--variant regular` signs and verifies with.
    """
    ps = UPSTREAM
    check = Checker()
    eprint(f"upstream unit-test pins: {ps!r}")
    check(VARIANTS["regular"] is ps and ps.name == "leanSphincs-keccak",
          "--upstream-kat runs the --variant regular parameter set (leanSphincs-keccak)")

    # lib.rs constants.
    check((ps.sig_len, ps.verify_perms) == (5684, 354), "SIG_SIZE = 5684, VERIFY_PERMUTATIONS = 354")
    check(ps.digest_calls == 2 and ps.per_word == 6 and ps.enc_input_len == 804,
          "two digest calls, 6 indices per word, 804-B encoding")

    # hash.rs address_layout.
    check(address(TW_FTS_NODE, 5, 0x123456, 0x89abcdef) == bytes.fromhex("efcdab89563412aa0000000000000000"),
          "address_layout")

    pp3, m5 = bytes([3]) * P_LEN, bytes([5]) * MSG_LEN

    # randomizer_and_digest_inputs: R_0's input order, the u128 LE addition, and an 80-byte digest call.
    base = th(pp3, address(TW_RANDOMIZER, 0, 0, 0), upstream_seed(2) + m5)
    check(base == keccak256(pp3 + address(TW_RANDOMIZER, 0, 0, 0) + upstream_seed(2) + m5)[:N]
          and randomizer(base, 0) == base, "randomizer_base = Th(P, tw_rand, S ‖ m)")
    check(randomizer(b"\xff" * N, 2) == b"\x01" + bytes(15), "randomizer wraps mod 2^128")
    check(randomizer(b"\xff" + bytes(15), 1)[:2] == b"\x00\x01", "randomizer is little endian")
    rho = randomizer(base, 7)
    inp = pp3 + address(TW_MSG, 0, 1, 0) + m5 + rho
    check(len(inp) == 80 and digest_block(pp3, rho, m5, 1) == keccak256(inp), "digest call 1 input, 80 bytes")

    # digest_fields, against a literal transcription of upstream's formula.
    rho7 = bytes([7]) * N
    calls = [digest_block(pp3, rho7, m5, 0), digest_block(pp3, rho7, m5, 1)]

    def word(call, w):
        return int.from_bytes(calls[call][8 * w: 8 * w + 8], "little")
    index, fors = message_digest(ps, pp3, rho7, m5)
    check(index == word(0, 2) % (1 << 26)
          and all(fors[kappa] == (word(kappa // 12, kappa % 12 // 6) >> (10 * (kappa % 6))) & 1023
                  for kappa in range(24)), "digest_fields")

    # encoding_absorbs_the_tops_and_the_counter: P ‖ A(enc, 0, 77) ‖ tops ‖ LE32(5), 804 B, 6 permutations.
    tops = b"".join(bytes([2 * kappa + half]) * N for kappa in range(24) for half in (0, 1))
    inp = pp3 + address(TW_ENC, 0, 0, 77) + tops + (5).to_bytes(4, "little")
    with hash_counter() as hc:
        d = th(pp3, address(TW_ENC, 0, 0, 77), tops + (5).to_bytes(4, "little"))
    check(len(inp) == 804 and d == keccak256(inp)[:N] and hc.perms == 6, "encoding input 804 B, 6 permutations")

    # wots_encoding_takes_about_829_tries: P = 7^16, tops = 48 copies of [e]^16 at e = 0..199; mean in [400, 1600).
    pp7 = bytes([7]) * P_LEN
    tries = sum(wots_encode(ps, pp7, e, bytes([e]) * (2 * ps.k * N))[0] + 1 for e in range(200))
    check(400 <= tries / 200 < 1600, f"WOTS+C encoding takes {tries / 200:.0f} tries on average (about 829)")

    # pruned_sign_verify_and_costs: keygen permutations 1 + 2^b·232 + (2^b - 1) + 2(h - b), at b = 3.
    with hash_counter() as hc:
        sk3 = keygen(upstream_seed(3), 3, ps)
    check(hc.perms == 1 + 8 * 232 + 7 + 2 * 23, f"keygen b=3 costs {hc.perms} permutations (expect 1910)")
    m3 = bytes(i & 0xFF for i in range(32))
    sig3, _ = sign(sk3, m3)
    with hash_counter() as hc:
        ok3 = verify(sk3.pk_seed, sk3.pk_root, m3, sig3, ps)
    check(ok3 and (hc.calls, hc.perms) == (342, 354),
          f"b=3 sign/verify, verify costs {hc.calls} calls / {hc.perms} permutations (expect 342 / 354)")

    # known_answer.
    eprint("upstream known_answer: key_gen(seed(1), 11), m[i] = 7i")
    seed = upstream_seed(1)
    m = bytes((7 * i) & 0xFF for i in range(MSG_LEN))
    t0 = time.perf_counter()
    sk = keygen(seed, 11, ps)
    t1 = time.perf_counter()
    sig, info = sign(sk, m)
    t2 = time.perf_counter()
    pk = sk.root + sk.pp                                    # PublicKey::to_bytes: root ‖ P
    sig_k = keccak256(sig)
    eprint(f"  P = 0x{sk.pp.hex()}  s = {sk.s}  root = 0x{sk.root.hex()}")
    eprint(f"  idx={info['idx']} counter={info['counter']} randomizer attempts={info['grind_attempts']}")
    check(pk.hex() == UPSTREAM_KAT_PK, f"pk          {pk.hex()}")
    check(sig_k.hex() == UPSTREAM_KAT_SIG_K, f"keccak(sig) {sig_k.hex()}")
    check(info["counter"] == UPSTREAM_KAT_COUNTER, f"counter     {info['counter']}")
    check(len(sig) == 5684, "signature is 5684 bytes")
    with hash_counter() as hc:
        ok = verify(sk.pk_seed, sk.pk_root, m, sig, ps)
    check(ok and (hc.calls, hc.perms) == (342, 354),
          f"verify accepts at {hc.calls} calls / {hc.perms} permutations (expect 342 / 354)")
    bad = bytearray(sig)
    bad[ps.off_fors + ps.fors_tree_len * 3] ^= 1            # upstream: bad.fors.secrets[3][0] ^= 1
    check(verify(sk.pk_seed, sk.pk_root, m, bytes(bad), ps) is False, "tampered FORS secret κ=3 -> false")
    kat = kat_json(seed, 11, m, sk, sig, info)
    check(kat["scheme"] == "leanSphincs-keccak" and len(kat["fors_indices"]) == 24
          and kat["pkRoot"] == "0x" + UPSTREAM_KAT_PK[:32] + "0" * 32
          and kat["pkSeed"] == "0x" + UPSTREAM_KAT_PK[32:] + "0" * 32,
          "--variant regular --json: scheme leanSphincs-keccak, 24 FORS indices, key words root ‖ 0, P ‖ 0")
    eprint(f"  timings: keygen b=11 {t1 - t0:.2f}s, sign {t2 - t1:.2f}s")
    eprint("UPSTREAM KAT OK" if check.ok else "UPSTREAM KAT FAILED")
    return check.ok


def split_variant(argv):
    """Take `--variant V` (or `--variant=V`) out of argv, wherever it stands.

    Returns (ParamSet, the other arguments, whether --variant was given). Without it the set is leanSphincs-S, so
    every command line written before the flag existed means what it meant.
    """
    rest, chosen = [], []
    args = iter(argv)
    for arg in args:
        if arg == "--variant":
            value = next(args, None)
            if value is None:
                raise SystemExit("error: --variant needs a value: s, f or regular")
            chosen.append(value)
        elif arg.startswith("--variant="):
            chosen.append(arg.split("=", 1)[1])
        else:
            rest.append(arg)
    if len(chosen) > 1:
        raise SystemExit("error: --variant given more than once")
    name = chosen[0] if chosen else "s"
    if name not in VARIANTS:
        raise SystemExit(f"error: unknown --variant {name!r}: s, f or regular")
    return VARIANTS[name], rest, bool(chosen)


def main(argv):
    usage = ("usage: leansphincs_s_signer.py <seed_hex64> <b> <msg_hex64>\n"
             "       leansphincs_s_signer.py --json <seed_hex64> <b> <msg_hex64>\n"
             "       leansphincs_s_signer.py --verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>\n"
             "       leansphincs_s_signer.py --selftest [b ...]\n"
             "       leansphincs_s_signer.py --upstream-kat\n"
             "every mode takes --variant s|f|regular (default s: leanSphincs-S; f: leanSphincs-f; "
             "regular: leanSphincs)")
    ps, argv, explicit = split_variant(argv)
    if len(argv) >= 1 and argv[0] in ("-h", "--help"):
        print(usage)
        return 0
    if len(argv) >= 1 and argv[0] == "--selftest":
        bs = [parse_b(x, ps) for x in argv[1:]] or [6, 10]
        ok = selftest(bs, ps)
        if ps is UPSTREAM:              # leanSphincs is the upstream crate's set: its own tests are its KAT
            ok = upstream_kat() and ok
        return 0 if ok else 1
    if len(argv) == 1 and argv[0] == "--upstream-kat":
        if explicit and ps is not UPSTREAM:
            raise SystemExit("error: --upstream-kat runs leanSphincs, the upstream parameters (--variant regular)")
        return 0 if upstream_kat() else 1
    if len(argv) == 5 and argv[0] == "--verify":
        pks = parse_hex(argv[1], 32, "pkSeed")
        pkr = parse_hex(argv[2], 32, "pkRoot")
        m = parse_hex(argv[3], MSG_LEN, "message")
        sig = parse_hex(argv[4], None, "sig")
        try:
            result = verify(pks, pkr, m, sig, ps)
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
    b = parse_b(argv[1], ps)
    m = parse_hex(argv[2], MSG_LEN, "message")
    sk, sig, info, _, _ = keygen_and_sign(seed, b, m, ps)
    if as_json:
        print(json.dumps(kat_json(seed, b, m, sk, sig, info)))
    else:
        print("0x" + abi_encode(sk.pk_seed, sk.pk_root, sig).hex())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
