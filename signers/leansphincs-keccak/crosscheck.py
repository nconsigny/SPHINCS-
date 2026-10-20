#!/usr/bin/env python3
"""
Cross-validate the Rust leanSphincs-keccak signer (`lsk`, a port of the
upstream crate's keccak branch at its own parameters) against the independent
Python signer (script/leansphincs_s_signer.py --variant regular), byte for byte.

Both implement docs/leanSphincs-keccak.md ("the spec"; section numbers below
refer to the leanSphincs-S spec, docs/leanSphincs-S-keccak.md, whose rules it
keeps). Keygen and signing are deterministic, so for one (seed, b, message)
the two must agree on every output: pkSeed, pkRoot, the 5684-byte signature,
idx, the WOTS+C counter, the randomizer and the 24 FORS indices. For every
vector this script:

  1. runs `lsk kat` and `leansphincs_s_signer.py --variant regular --json`,
     and compares every field of the two KAT objects; a signature mismatch is
     reported as the first differing §11 field (ρ, FORS secret κ, FORS path
     κ/ℓ, counter, WOTS σ_i, auth path ℓ);
  2. cross-verifies: the Rust signature through the Python `--verify` mirror,
     the Python signature through `lsk verify`, and a tampered signature and
     another message through both (both must say false);
  3. recomputes, with a third spec-literal implementation written here, the
     parts a byte match between two ports cannot vouch for on its own:
     P from the seed (§9), upstream's two-call digest and its split (the
     26-bit leaf index from call 0 bytes 16..24, six 10-bit FORS indices in
     each of words 0 and 1 of each call), the kept subtree (§9), that
     ρ = R_0 + i with i a plausible randomizer attempt (i < 2^40; an honest
     signer's i is about 2^(26-b)) and, for i <= 2^23, the least one landing
     in the kept subtree (§10), the FORS tops, the merged encoding over them
     (tops ‖ LE32(c), 804 input bytes), codeword, WOTS leaf and the 26-level
     root the signature reaches (§6-§8), and that the counter is the least
     admissible one (§6); then, from the seed, the secret side no verifier
     sees (the WOTS and FORS secrets and the surrogates): the key's kept
     subtree and root (§9), which must be pkRoot, and the whole signature of
     ρ (every FORS tree rebuilt, the least counter, σ_i, the auth path),
     which must be the signed bytes (§6, §7, §10, §11).

It also checks that `lsk sign` and the Python default mode print the same
abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig) (the Forge FFI output),
that both verifiers give the same answer and revert reason on malformed input
(the contract checks the length first, then the key), that both signers
reproduce the values pinned by upstream's `known_answer` test (which
src/scheme.rs carries verbatim), and that the §10 check fails an R_0 derived
any other way (negative controls: R_0 is used only by the signers, so an R_0
bug they share passes every other check).

Exits nonzero on any difference.

Usage (pycryptodome is needed; the repo venv has it):
    .venv/bin/python signers/leansphincs-keccak/crosscheck.py [--jobs N] [--no-build] [--b 8 10 ...]

By default it first runs `cargo build --release` in this crate, and it refuses a
binary older than the crate's sources. The Python signer grinds ~2^(26-b)
randomizers per signature, so b = 4 costs ~4M keccak calls in Python, and the
third opinion's grind recheck as many again; its keygen costs 225·2^b calls
(~460K at b = 11) and its FORS rebuild ~61K per vector.
"""

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import time
from pathlib import Path

from Crypto.Hash import keccak as _keccak

CRATE_DIR = Path(__file__).resolve().parent
REPO_ROOT = CRATE_DIR.parents[1]
PY_SIGNER = REPO_ROOT / "script" / "leansphincs_s_signer.py"
DEFAULT_LSK = CRATE_DIR / "target" / "release" / "lsk"
# The Python signer's variant for this scheme.
PY_VARIANT = ("--variant", "regular")

# ============================================================
#  Vectors
# ============================================================

SEEDS = {
    "zero": bytes(32),
    "ff": b"\xff" * 32,
    "x11": b"\x11" * 32,
    "ramp": bytes(range(32)),
    # The Rust tests' seed(1): (31 + i) mod 256.
    "seed1": bytes((31 + i) & 0xFF for i in range(32)),
}
MSGS = {
    "zero": bytes(32),
    "ff": b"\xff" * 32,
    "de": b"\xde" * 32,
    # The Rust known_answer message: 7i mod 256.
    "mul7": bytes((7 * i) & 0xFF for i in range(32)),
}

# (b, seed, message). b = 11 / seed1 / mul7 is the Rust known_answer vector.
VECTORS = [
    (4, "x11", "zero"), (4, "ff", "ff"),
    (5, "seed1", "de"),
    (6, "zero", "de"), (6, "ramp", "zero"), (6, "x11", "ff"),
    (7, "ramp", "de"),
    (8, "ff", "zero"), (8, "ramp", "mul7"), (8, "zero", "ff"),
    (9, "ff", "de"),
    (10, "x11", "de"), (10, "zero", "zero"), (10, "ff", "mul7"), (10, "ramp", "ff"),
    (11, "seed1", "mul7"),
]

# Pinned by upstream's `known_answer` (crates/sphincs, keccak branch), which src/scheme.rs carries verbatim:
# key_gen(seed(1), 11), m[i] = 7i (the spec's "Known answer").
KNOWN_ANSWER = {
    "b": 11, "seed": "seed1", "msg": "mul7",
    "pk": "63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00",   # root ‖ P
    "sig_keccak": "9a21b6bc61d6ba500b4d67809912c1424be1f58486eda144e4ef70afd01cf94d",
    "counter": 1176,
}
SCHEME = "leanSphincs-keccak"   # the KAT objects' "scheme"

KAT_FIELDS = ("scheme", "seed", "b", "message", "pkSeed", "pkRoot", "sig",
              "idx", "counter", "randomizer", "fors_indices")

# Grinding minimality is rechecked up to this many attempts (b = 4 needs ~2^22).
GRIND_CHECK_MAX = 1 << 23
# The randomizer attempt i = ρ - R_0 of an honest signer is geometric with mean 2^(26-b): it
# exceeds 2^40 with probability about exp(-2^(14+b)), nil for any b >= 0. An R_0 the signers
# derive differently from §10 gives i uniform mod 2^128, which lands above this bound.
RANDOMIZER_ATTEMPT_MAX = 1 << 40

# ============================================================
#  Spec-literal recomputation (independent of both signers)
# ============================================================

H, A, K, V, T_SUM = 26, 10, 24, 64, 120
SIG_LEN = 5684
OFF_FORS, FORS_STRIDE, OFF_CTR, OFF_WOTS, OFF_AUTH = 16, 176, 4240, 4244, 5268
ABI_LEN = 4 * 32 + -(-SIG_LEN // 32) * 32   # 5824: two key words, the offset, the length and the padded signature
TW_PRF, TW_CHAIN, TW_LEAF, TW_NODE, TW_ENC, TW_PARAM, TW_RAND = 0, 1, 2, 3, 4, 5, 7
TW_FTS_PRF, TW_FTS_LEAF, TW_FTS_NODE = 8, 9, 10
TW_MSG, TW_SURROGATE = 12, 13   # type 11, the former FORS key hash, is unused (§3, §7)


def keccak256(data):
    return _keccak.new(digest_bits=256, data=data).digest()


def adr(t, step, hi, lo):
    """§3: LE32(lo) ‖ LE24(hi) ‖ (t | step << 5) ‖ 0^8."""
    assert t < 32 and step < 8 and hi < 1 << 24 and lo < 1 << 32
    return lo.to_bytes(4, "little") + hi.to_bytes(3, "little") + bytes([t | step << 5]) + bytes(8)


def th(pp, tw, payload):
    return keccak256(pp + tw + payload)[:16]


def pos(kappa, level, j):
    """§4."""
    assert kappa < K and level < A and j < 1 << (A - level)
    return kappa + 32 * level + 512 * j


def word(d, w):
    return int.from_bytes(d[8 * w:8 * w + 8], "little")


def split_digest(d0, d1):
    """The spec's two-call digest: idx = word 2 of call 0 & (2^26 - 1); u_κ from call κ div 12, word (κ mod 12) div 6,
    at bit 10((κ mod 12) mod 6)."""
    calls = (d0, d1)
    u = [(word(calls[k // 12], k % 12 // 6) >> (A * (k % 6))) & ((1 << A) - 1) for k in range(K)]
    return word(d0, 2) & ((1 << H) - 1), u


def digest_call(pp, rho, m, c):
    """D_c = keccak256(P ‖ address(MSG, step 0, hi = c, lo = 0) ‖ m ‖ ρ), 80 input bytes, untruncated."""
    return keccak256(pp + adr(TW_MSG, 0, c, 0) + m + rho)


def digest(pp, rho, m):
    return split_digest(digest_call(pp, rho, m, 0), digest_call(pp, rho, m, 1))


def codeword(d):
    """§6: x_i = (X >> 2i) & 3 with X = d as u128 LE; admissible iff Σ x_i = T = 120."""
    X = int.from_bytes(d, "little")
    x = [(X >> (2 * i)) & 3 for i in range(V)]
    return x if sum(x) == T_SUM else None


def enc(pp, idx, tops, c):
    """§6, the merged encoding: d = Th(P, address(ENC, 0, 0, e), tops ‖ LE32(c)), an 804-byte keccak input."""
    assert len(tops) == 2 * K * 16
    return codeword(th(pp, adr(TW_ENC, 0, 0, idx), tops + c.to_bytes(4, "little")))


def chain(pp, e, i, value, start, stop):
    """§6: chain i of the one-time key at leaf e, from position `start` to `stop`; the step onto `to` is
    Th(P, address(CHAIN, step = to - 1, hi = i, lo = e), x)."""
    for to in range(start + 1, stop + 1):
        value = th(pp, adr(TW_CHAIN, to - 1, i, e), value)
    return value


def spec_recover(pp, m, sig):
    """§5-§8 on a 5684-byte signature: (idx, u, tops, counter, codeword, leaf, root). tops is the 768 bytes
    top_{0,0} ‖ top_{0,1} ‖ … ‖ top_{23,1} that the encoding absorbs: no hash folds them into a FORS key (§7)."""
    rho = sig[:16]
    idx, u = digest(pp, rho, m)
    tops = []
    for k in range(K):
        base = OFF_FORS + FORS_STRIDE * k
        p = [sig[base + 16 + 16 * l:base + 32 + 16 * l] for l in range(A)]
        node = th(pp, adr(TW_FTS_LEAF, 0, pos(k, 0, u[k]), idx), sig[base:base + 16])
        for l in range(A - 1):
            left, right = (node, p[l]) if (u[k] >> l) & 1 == 0 else (p[l], node)
            node = th(pp, adr(TW_FTS_NODE, 0, pos(k, l + 1, u[k] >> (l + 1)), idx), left + right)
        tops += [node, p[A - 1]] if (u[k] >> (A - 1)) & 1 == 0 else [p[A - 1], node]
    tops = b"".join(tops)
    c = int.from_bytes(sig[OFF_CTR:OFF_CTR + 4], "little")
    x = enc(pp, idx, tops, c)
    if x is None:
        return idx, u, tops, c, None, None, None
    ends = [chain(pp, idx, i, sig[OFF_WOTS + 16 * i:OFF_WOTS + 16 * i + 16], x[i], 3) for i in range(V)]
    leaf = th(pp, adr(TW_LEAF, 0, 0, idx), b"".join(ends))
    cur = leaf
    for l in range(H):
        sib = sig[OFF_AUTH + 16 * l:OFF_AUTH + 16 * l + 16]
        left, right = (cur, sib) if (idx >> l) & 1 == 0 else (sib, cur)
        cur = th(pp, adr(TW_NODE, 0, l + 1, idx >> (l + 1)), left + right)
    return idx, u, tops, c, x, leaf, cur


def randomizer_base(pp, seed, m):
    """§10: R_0 = Th(P, address(RANDOMIZER), S ‖ m), as a little-endian integer."""
    return int.from_bytes(th(pp, adr(TW_RAND, 0, 0, 0), seed + m), "little")


def check_randomizer(pp, r0, m, rho, b, s):
    """§10 for one signature: (failures, attempt i, note). ρ = R_0 + i always holds for SOME i mod 2^128, so
    the check is that i is plausibly small (an honest signer's i is about 2^(26-b)) and, where affordable,
    that no smaller attempt lands in the kept subtree s."""
    i = (int.from_bytes(rho, "little") - r0) % (1 << 128)
    if i >= RANDOMIZER_ATTEMPT_MAX:
        return [f"ρ is R_0 + {i}: not a randomizer attempt (R_0 derived differently from §10?)"], i, None
    if i > GRIND_CHECK_MAX:
        return [], i, f"grind minimality skipped (i = {i})"
    prefix = pp + adr(TW_MSG, 0, 0, 0) + m   # the grind reads call 0 only
    for j in range(i):
        d0 = keccak256(prefix + ((r0 + j) % (1 << 128)).to_bytes(16, "little"))
        if (word(d0, 2) & ((1 << H) - 1)) >> b == s:
            return [f"randomizer attempt {j} < {i} already lands in the kept subtree"], i, None
    return [], i, None


def halves(pp, tw, seed):
    """ThPair (§2): the two 16-byte halves of keccak256(P ‖ address ‖ S), a pair of secrets."""
    d = keccak256(pp + tw + seed)
    return [d[:16], d[16:]]


def spec_wots_secrets(pp, seed, e):
    """§6: s_0 … s_63, (s_2t, s_2t+1) = ThPair(P, address(PRF, 0, hi = t, lo = e), S)."""
    return [s for t in range(V // 2) for s in halves(pp, adr(TW_PRF, 0, t, e), seed)]


def spec_keygen(seed, b):
    """§9 from the seed: (P, s, the kept subtree's levels, the surrogates, the root). The verifier sees none of the
    secret derivations (the WOTS and FORS secrets, the surrogates), so an error the two signers shared in one would
    pass every check above; recomputing the key and the whole signature here is what can see it."""
    pp = th(bytes(16), adr(TW_PARAM, 0, 0, 0), seed)
    s = int.from_bytes(pp[:8], "little") & ((1 << (H - b)) - 1) if b < H else 0
    leaves = []
    for j in range(1 << b):
        e = (s << b) + j
        ends = [chain(pp, e, i, x, 0, 3) for i, x in enumerate(spec_wots_secrets(pp, seed, e))]
        leaves.append(th(pp, adr(TW_LEAF, 0, 0, e), b"".join(ends)))
    levels = [leaves]
    for lv in range(1, b + 1):
        below, first = levels[-1], s << (b - lv)
        levels.append([th(pp, adr(TW_NODE, 0, lv, first + j), below[2 * j] + below[2 * j + 1])
                       for j in range(len(below) // 2)])
    surrogates = [th(pp, adr(TW_SURROGATE, 0, lv, 0), seed) for lv in range(b, H)]
    root = levels[b][0]
    for lv in range(b, H):
        j, sib = s >> (lv - b), surrogates[lv - b]   # the kept subtree's ancestor at level lv, and its sibling
        root = th(pp, adr(TW_NODE, 0, lv + 1, j >> 1), root + sib if j & 1 == 0 else sib + root)
    return pp, s, levels, surrogates, root


def spec_fors(pp, seed, idx, u):
    """§7 from the seed: each tree's opened secret sk_{κ,u_κ}, its path p_κ[0..9] and its two tops (every tree is
    rebuilt: 24 · (512 + 1024 + 1022) calls)."""
    secrets, paths, tops = [], [], []
    for k in range(K):
        sk = [x for t in range(1 << (A - 1)) for x in halves(pp, adr(TW_FTS_PRF, 0, pos(k, 0, t), idx), seed)]
        level = [th(pp, adr(TW_FTS_LEAF, 0, pos(k, 0, j), idx), sk[j]) for j in range(1 << A)]
        path = [level[u[k] ^ 1]]
        for lv in range(1, A):
            level = [th(pp, adr(TW_FTS_NODE, 0, pos(k, lv, j), idx), level[2 * j] + level[2 * j + 1])
                     for j in range(len(level) // 2)]
            path.append(level[(u[k] >> lv) ^ 1])
        secrets.append(sk[u[k]])
        paths.append(path)
        tops += level                                # the two level-9 nodes
    return secrets, paths, b"".join(tops)


def spec_signature(seed, b, m, rho, key):
    """§10-§11 from the seed: the 5684 bytes of the signature of m with randomizer ρ under `key` (spec_keygen), or
    None if ρ's leaf is not kept. check_randomizer is what ties ρ itself to the seed."""
    pp, s, levels, surrogates, _ = key
    idx, u = digest(pp, rho, m)
    if idx >> b != s:
        return None
    secrets, paths, tops = spec_fors(pp, seed, idx, u)
    c = next(c for c in range(1 << 32) if enc(pp, idx, tops, c) is not None)
    x = enc(pp, idx, tops, c)
    sigma = [chain(pp, idx, i, sk, 0, x[i]) for i, sk in enumerate(spec_wots_secrets(pp, seed, idx))]
    local = idx - (s << b)
    auth = [levels[lv][(local >> lv) ^ 1] if lv < b else surrogates[lv - b] for lv in range(H)]
    fors = b"".join(sk + b"".join(p) for sk, p in zip(secrets, paths))
    return rho + fors + c.to_bytes(4, "little") + b"".join(sigma) + b"".join(auth)


def spec_check(seed, b, m, kat, key=None):
    """The third opinion on one KAT: (failures, randomizer attempt i, note); no failures when all hold. `key` is
    spec_keygen(seed, b), computed here if not given."""
    fails = []

    def need(cond, what):
        if not cond:
            fails.append(what)

    pk_seed, pk_root = hx(kat["pkSeed"]), hx(kat["pkRoot"])
    sig = hx(kat["sig"])
    need(len(sig) == SIG_LEN, f"sig is {len(sig)} bytes")
    need(pk_seed[16:] == bytes(16) and pk_root[16:] == bytes(16), "key words not high-aligned")
    if fails:
        return fails, None, None
    pp, root = pk_seed[:16], pk_root[:16]
    need((hx(kat["seed"]), kat["b"], hx(kat["message"])) == (seed, b, m), "KAT seed / b / message are not the inputs")

    # §9: P and the kept subtree's position.
    need(pp == th(bytes(16), adr(TW_PARAM, 0, 0, 0), seed), "P != Th(0^16, PARAMETER, S)")
    s = int.from_bytes(pp[:8], "little") & ((1 << (H - b)) - 1) if b < H else 0

    # The two-call digest, §11: the digest fields and the encoded ρ / counter.
    rho = sig[:16]
    idx, u = digest(pp, rho, m)
    need(rho == hx(kat["randomizer"]), "ρ at offset 0 != randomizer")
    need(idx == kat["idx"], f"digest idx {idx} != {kat['idx']}")
    need(u == list(kat["fors_indices"]), "digest FORS indices differ")
    need(int.from_bytes(sig[OFF_CTR:OFF_CTR + 4], "little") == kat["counter"], f"counter at {OFF_CTR} differs")
    need(kat["scheme"] == SCHEME, f"scheme {kat['scheme']!r} != {SCHEME!r}")
    need(idx >> b == s, f"idx {idx} outside the kept subtree s={s}")

    # §10: ρ = R_0 + i, and no smaller i lands in the kept subtree.
    grind_fails, i, note = check_randomizer(pp, randomizer_base(pp, seed, m), m, rho, b, s)
    fails += grind_fails

    # §6-§8: what the signature reaches, and the least admissible counter.
    _, _, tops, c, x, leaf, got_root = spec_recover(pp, m, sig)
    need(x is not None, "inadmissible WOTS+C encoding")
    need(got_root == root, "signature does not fold to pkRoot")
    if x is not None:
        for c2 in range(c):
            if enc(pp, idx, tops, c2) is not None:
                fails.append(f"counter {c2} < {c} is already admissible")
                break

    # §6-§11 from the seed, the secret side no verifier sees: the root, then all 5684 bytes of the signature.
    key = key or spec_keygen(seed, b)
    need(key[4] == root, "pkRoot != the §9 root recomputed from the seed")
    want = spec_signature(seed, b, m, rho, key)
    if want is not None and want != sig:
        first = next(j for j in range(SIG_LEN) if want[j] != sig[j])
        n_diff = sum(x != y for x, y in zip(want, sig))
        fails.append(f"sig != the one recomputed from the seed: {n_diff} bytes differ, first at byte {first} "
                     f"({sig_field(first)})")
    return fails, i, note


# ============================================================
#  Running the two signers
# ============================================================


def hx(s):
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)


def run(cmd, timeout=1800):
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout.strip(), p.stderr.strip()


def run_ok(cmd):
    code, out, err = run(cmd)
    if code != 0:
        raise RuntimeError(f"{' '.join(map(str, cmd[:3]))} ... exited {code}: {err[-400:]}")
    return out


def py(*args):
    return [sys.executable, str(PY_SIGNER), *PY_VARIANT, *args]


def sig_field(off):
    """Name of the spec §11 field holding byte `off`."""
    if off < 16:
        return "ρ"
    if off < OFF_CTR:
        k, r = divmod(off - OFF_FORS, FORS_STRIDE)
        return f"FORS secret κ={k}" if r < 16 else f"FORS path κ={k} ℓ={(r - 16) // 16}"
    if off < OFF_WOTS:
        return "counter"
    if off < OFF_AUTH:
        return f"WOTS σ_{(off - OFF_WOTS) // 16}"
    if off < SIG_LEN:
        return f"auth path ℓ={(off - OFF_AUTH) // 16}"
    return "past the end"


def compare_kats(rk, pk):
    """Field-by-field differences between the Rust and the Python KAT objects (which carry exactly KAT_FIELDS)."""
    diffs = [f"{who} KAT fields {sorted(kat)} != {sorted(KAT_FIELDS)}"
             for who, kat in (("Rust", rk), ("Python", pk)) if set(kat) != set(KAT_FIELDS)]
    for f in KAT_FIELDS:
        if rk.get(f) != pk.get(f):
            if f == "sig":
                a, b = hx(rk[f]), hx(pk[f])
                first = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))
                n_diff = sum(x != y for x, y in zip(a, b)) + abs(len(a) - len(b))
                diffs.append(f"sig: {n_diff} bytes differ, first at byte {first} ({sig_field(first)})")
            else:
                diffs.append(f"{f}: rust={rk.get(f)!r} python={pk.get(f)!r}")
    return diffs


def verify_both(lsk, pk_seed, pk_root, m_hex, sig_hex):
    """(rust stdout, rust reason, python stdout, python reason)."""
    _, r_out, r_err = run([lsk, "verify", pk_seed, pk_root, m_hex, sig_hex])
    _, p_out, p_err = run(py("--verify", pk_seed, pk_root, m_hex, sig_hex))
    return r_out, r_err.strip(), p_out, p_err.removeprefix("revert: ").strip()


def check_vector(lsk, b, seed_name, msg_name, n):
    seed, m = SEEDS[seed_name], MSGS[msg_name]
    seed_hex, m_hex = "0x" + seed.hex(), "0x" + m.hex()
    fails = []
    t0 = time.perf_counter()
    rk = json.loads(run_ok([lsk, "kat", seed_hex, str(b), m_hex]))
    t1 = time.perf_counter()
    pk = json.loads(run_ok(py("--json", seed_hex, str(b), m_hex)))
    t2 = time.perf_counter()

    fails += [f"KAT {d}" for d in compare_kats(rk, pk)]

    # Cross-verification: each side's signature through the other side's verifier.
    r_ok = run_ok(py("--verify", rk["pkSeed"], rk["pkRoot"], m_hex, rk["sig"]))
    p_ok = run_ok([lsk, "verify", pk["pkSeed"], pk["pkRoot"], m_hex, pk["sig"]])
    if r_ok != "true":
        fails.append(f"Python --verify on the Rust signature: {r_ok}")
    if p_ok != "true":
        fails.append(f"lsk verify on the Python signature: {p_ok}")

    # A tampered byte (a field that moves with the vector) and another message: both say false.
    sig = bytearray(hx(rk["sig"]))
    off = (977 * n + 13) % SIG_LEN
    sig[off] ^= 1 << (n % 8)
    other_m = "0x" + (bytes([m[0] ^ 0x80]) + m[1:]).hex()
    for what, args in ((f"tampered {sig_field(off)}", (m_hex, "0x" + sig.hex())),
                       ("another message", (other_m, rk["sig"]))):
        r_out, _, p_out, _ = verify_both(lsk, rk["pkSeed"], rk["pkRoot"], *args)
        if (r_out, p_out) != ("false", "false"):
            fails.append(f"{what}: rust={r_out} python={p_out} (want false, false)")

    # The third, spec-literal opinion, on each side's output.
    t3 = time.perf_counter()
    key = spec_keygen(seed, b)
    spec_fails, grind_i, note = spec_check(seed, b, m, rk, key)
    fails += [f"spec (Rust KAT): {f}" for f in spec_fails]
    if pk != rk:
        spec_fails_py, _, _ = spec_check(seed, b, m, pk, key)
        fails += [f"spec (Python KAT): {f}" for f in spec_fails_py]
    t4 = time.perf_counter()

    return {
        "label": f"b={b:<2} seed={seed_name:<5} msg={msg_name:<4}",
        "vector": (b, seed_name, msg_name), "rk": rk, "pyk": pk,
        "fails": fails, "grind_i": grind_i, "note": note,
        "times": (t1 - t0, t2 - t1, t4 - t3),
    }


def check_known_answer(lsk, results):
    """Both signers reproduce upstream's known_answer pins (and they are still the ones in scheme.rs)."""
    fails = []
    src = (CRATE_DIR / "src" / "scheme.rs").read_text()
    for key in ("pk", "sig_keccak"):
        if f'"{KNOWN_ANSWER[key]}"' not in src:
            fails.append(f"known_answer: {key} pin {KNOWN_ANSWER[key]} is no longer in src/scheme.rs")
    if f"sig.counter, {KNOWN_ANSWER['counter']})" not in src:
        fails.append("known_answer: the counter pin is no longer in src/scheme.rs")
    # Each side's KAT of that vector if it ran above (with --b it may not have), else a fresh run.
    key = (KNOWN_ANSWER["b"], KNOWN_ANSWER["seed"], KNOWN_ANSWER["msg"])
    args = ("0x" + SEEDS[key[1]].hex(), str(key[0]), "0x" + MSGS[key[2]].hex())
    done = next((r for r in results if r["vector"] == key), {})
    kats = (("rust", done.get("rk") or json.loads(run_ok([lsk, "kat", *args]))),
            ("python", done.get("pyk") or json.loads(run_ok(py("--json", *args)))))
    for who, kat in kats:
        pk_bytes = (hx(kat["pkRoot"])[:16] + hx(kat["pkSeed"])[:16]).hex()
        if pk_bytes != KNOWN_ANSWER["pk"]:
            fails.append(f"known_answer pk: {who} {pk_bytes} != pinned {KNOWN_ANSWER['pk']}")
        sig_k = keccak256(hx(kat["sig"])).hex()
        if sig_k != KNOWN_ANSWER["sig_keccak"]:
            fails.append(f"known_answer keccak256(sig): {who} {sig_k} != pinned {KNOWN_ANSWER['sig_keccak']}")
        if kat["counter"] != KNOWN_ANSWER["counter"]:
            fails.append(f"known_answer counter: {who} {kat['counter']} != pinned {KNOWN_ANSWER['counter']}")
    return fails


def check_randomizer_controls(results):
    """Negative controls for the §10 check: on a real signature, an R_0 derived any other way must FAIL it.
    An R_0 bug shared by both signers leaves the KATs matching and every signature valid (R_0 is signer-only),
    so this check is the only thing that can see it."""
    passing = [r for r in results if r["rk"] and not r["fails"]]
    if not passing:
        return ["randomizer controls: no passing vector to run them on"]
    r = max(passing, key=lambda r: r["vector"][0])
    b, seed_name, msg_name = r["vector"]
    seed, m, kat = SEEDS[seed_name], MSGS[msg_name], r["rk"]
    pp, rho, s = hx(kat["pkSeed"])[:16], hx(kat["sig"])[:16], kat["idx"] >> b
    wrong = {
        "the payload m ‖ S": int.from_bytes(th(pp, adr(TW_RAND, 0, 0, 0), m + seed), "little"),
        "another seed": randomizer_base(pp, bytes([seed[0] ^ 1]) + seed[1:], m),
        "the PRF tweak": int.from_bytes(th(pp, adr(0, 0, 0, 0), seed + m), "little"),
    }
    fails = []
    for what, r0 in wrong.items():
        if not check_randomizer(pp, r0, m, rho, b, s)[0]:
            fails.append(f"randomizer control: an R_0 from {what} passes the §10 check")
    return fails


def check_abi_and_reverts(lsk, b, seed_name, msg_name):
    """`lsk sign` == Python default mode (the FFI output); same answers and revert reasons on malformed input."""
    fails = []
    seed_hex, m_hex = "0x" + SEEDS[seed_name].hex(), "0x" + MSGS[msg_name].hex()
    r_abi = run_ok([lsk, "sign", seed_hex, str(b), m_hex])
    p_abi = run_ok(py(seed_hex, str(b), m_hex))
    if r_abi != p_abi:
        fails.append("ABI: `lsk sign` and the Python default mode differ")
    enc = hx(r_abi)
    pk_seed, pk_root = enc[:32], enc[32:64]
    sig_len = int.from_bytes(enc[96:128], "big")
    if (len(enc), enc[64:96], sig_len) != (ABI_LEN, (0x60).to_bytes(32, "big"), SIG_LEN) or any(enc[128 + SIG_LEN:]):
        fails.append(f"ABI: unexpected layout (want {ABI_LEN} bytes, offset 0x60, length {SIG_LEN}, zero padding)")
    sig = enc[128:128 + SIG_LEN]
    dirty = lambda w: w[:31] + bytes([w[31] ^ 1])   # noqa: E731 (a nonzero low 128 bits)
    cases = [
        ("valid", pk_seed, pk_root, sig, "true", ""),
        ("short sig", pk_seed, pk_root, sig[:-1], "false", "Invalid sig length"),
        ("long sig", pk_seed, pk_root, sig + b"\0", "false", "Invalid sig length"),
        ("empty sig", pk_seed, pk_root, b"", "false", "Invalid sig length"),
        ("dirty pkSeed", dirty(pk_seed), pk_root, sig, "false", "Invalid public key"),
        ("dirty pkRoot", pk_seed, dirty(pk_root), sig, "false", "Invalid public key"),
        # Both wrong: the contract checks the length first (spec §12 order).
        ("short sig + dirty pkRoot", pk_seed, dirty(pk_root), sig[:-1], "false", "Invalid sig length"),
    ]
    for what, s, r, g, want, reason in cases:
        r_out, r_why, p_out, p_why = verify_both(lsk, "0x" + s.hex(), "0x" + r.hex(), m_hex, "0x" + g.hex())
        if (r_out, p_out) != (want, want) or (r_why, p_why) != (reason, reason):
            fails.append(f"verify {what}: rust={r_out}/{r_why!r} python={p_out}/{p_why!r} "
                         f"(want {want}/{reason!r})")
    return fails


# ============================================================
#  Main
# ============================================================


def ensure_binary(lsk, build):
    """Build `lsk` (unless `build` is false), then refuse a default-path binary older than the crate sources.

    The binary is gitignored, so a working tree can carry sources newer than the last build, and a stale binary
    signs under the old scheme without any error (the repo's f5c09ae convention for its C signers). Also used by
    make_kat_fixture.py, so `--no-build` can never write a fixture the current sources do not reproduce.
    """
    if build:
        print("  cargo build --release ...", file=sys.stderr, flush=True)
        subprocess.run(["cargo", "build", "--release", "--quiet"], cwd=CRATE_DIR, check=True)
    if not lsk.exists():
        sys.exit(f"FAIL: {lsk} is missing (run `cargo build --release` in {CRATE_DIR})")
    if lsk != DEFAULT_LSK:
        return
    sources = [CRATE_DIR / "Cargo.toml", CRATE_DIR / "Cargo.lock", *(CRATE_DIR / "src").rglob("*.rs")]
    built = lsk.stat().st_mtime
    newer = sorted(str(p.relative_to(CRATE_DIR)) for p in sources if p.exists() and p.stat().st_mtime > built)
    if newer:
        sys.exit(f"FAIL: {lsk} is older than {', '.join(newer)}; run `cargo build --release` in {CRATE_DIR} "
                 "(or drop --no-build)")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1),
                    help="vectors run concurrently (each Python signer is one process; default 4)")
    ap.add_argument("--no-build", action="store_true", help="skip `cargo build --release`")
    ap.add_argument("--lsk", type=Path, default=DEFAULT_LSK, help="the lsk binary")
    ap.add_argument("--b", type=int, nargs="*", help="only the vectors with these b")
    args = ap.parse_args()

    ensure_binary(args.lsk, not args.no_build)
    lsk = str(args.lsk)
    vectors = [v for v in VECTORS if not args.b or v[0] in args.b]
    print(f"  {len(vectors)} vectors, {args.jobs} jobs; Rust {lsk}, Python {PY_SIGNER} {' '.join(PY_VARIANT)}",
          flush=True)

    t0 = time.perf_counter()
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        futures = [pool.submit(check_vector, lsk, b, s, m, n) for n, (b, s, m) in enumerate(vectors)]
        results = []
        for fut, (b, s, m) in zip(futures, vectors):
            try:
                results.append(fut.result())
            except Exception as exc:                 # a signer crashed: report it as a failure
                results.append({"label": f"b={b:<2} seed={s:<5} msg={m:<4}", "vector": (b, s, m),
                                "rk": None, "pyk": None,
                                "fails": [f"error: {exc}"], "grind_i": None, "note": None, "times": (0, 0, 0)})

    all_fails = []
    print()
    print(f"  {'vector':<30} {'idx':>9} {'ctr':>6} {'grind i':>8}  {'rust':>6} {'python':>7} {'spec':>6}  result")
    for r in results:
        rk = r["rk"] or {}
        tr, tp, ts = r["times"]
        status = "MATCH" if not r["fails"] else "FAIL"
        extra = f"  ({r['note']})" if r["note"] else ""
        print(f"  {r['label']:<30} {rk.get('idx', '-'):>9} {rk.get('counter', '-'):>6} "
              f"{r['grind_i'] if r['grind_i'] is not None else '-':>8}  {tr:5.2f}s {tp:6.2f}s {ts:5.2f}s  {status}{extra}")
        all_fails += [f"[{r['label'].strip()}] {f}" for f in r["fails"]]
        if not r["fails"] and rk:
            sig_k = keccak256(hx(rk["sig"])).hex()
            print(f"      pkSeed {rk['pkSeed'][:34]}  pkRoot {rk['pkRoot'][:34]}  keccak256(sig) 0x{sig_k[:16]}…")

    print("\n  upstream known_answer pins (src/scheme.rs) from both signers ...", flush=True)
    ka_fails = check_known_answer(lsk, results)
    print("    " + ("ok" if not ka_fails else "FAIL"))
    all_fails += ka_fails

    print("  §10 check rejects an R_0 derived any other way (negative controls) ...", flush=True)
    rc_fails = check_randomizer_controls(results)
    print("    " + ("ok" if not rc_fails else "FAIL"))
    all_fails += rc_fails

    abi_vec = (8, "ramp", "mul7")
    print(f"  ABI output and revert parity at b={abi_vec[0]} seed={abi_vec[1]} msg={abi_vec[2]} ...", flush=True)
    abi_fails = check_abi_and_reverts(lsk, *abi_vec)
    print("    " + ("ok" if not abi_fails else "FAIL"))
    all_fails += abi_fails

    print(f"\n  {time.perf_counter() - t0:.1f}s wall")
    if all_fails:
        print(f"\n  MISMATCH ({len(all_fails)}):")
        for f in all_fails:
            print(f"    {f}")
        sys.exit(1)
    print(f"\n  MATCH: {len(results)} vectors byte-for-byte (pkSeed, pkRoot, sig, idx, counter, randomizer, "
          "fors_indices), cross-verified, spec-recomputed; known_answer pins reproduced; §10 negative controls; "
          "ABI and revert parity.")


if __name__ == "__main__":
    main()
