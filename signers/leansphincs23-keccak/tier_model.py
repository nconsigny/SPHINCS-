#!/usr/bin/env python3
"""
Cost model for the leanSphincs-23 signer tiers, in keccak256 calls (legacy/docs/leanSphincs-23-keccak.md, "Tiered signers").

The tiers are the "One signer, leanSphincs-23" table of the sphincs-art fork (https://nconsigny.github.io/sphincs-art/).
The key is generated once, keeping a subtree of 2^b leaves (spec §9), and stored with a node cache of bounded size.
Each signature then recomputes only the auth-path nodes the cache does not hold:

    tier       device class      b    cache
    Light      Ledger Nano S+    13   16 KiB
    Standard   weak CPU          20    1 MiB
    Full       powerful CPU      25   16 MiB   (whole tree)

This is a transcription of scripts/sweep_leansphincs_pruned.py in nconsigny/sphincs-art (commit 1ca729f): tree_cost,
fors_sign, tier_costs and cover_lifetime. That script takes its cost model from scripts/scheme.py in
TomWambsgans/leanXMSS-leanSPHINCS-candidates. Every formula is the script's. Only the unit changes, from BLAKE2s
compressions to keccak256 calls. With --units blake2s this file counts compressions as the script does and gives the
page's figures, and --check asserts both unit systems against pinned values.

Unit costs                                    keccak256 calls   BLAKE2s compressions (P ‖ address ‖ input, 64-B blocks)
  derive (one PRF call gives two secrets)     1                 1
  chain step, FORS leaf, tree node, ENC try   1                 1
  WOTS leaf hash over the 64 chain ends       1                 17
  WOTS leaf from the seed: 32 + 192 + 1       225               241
  FORS key over the 26 tops                   1                 7
  R_0 (S ‖ m), message digest                 1 each            2 each
  randomizer grind, per try                   1                 1   (the script's convention)

A keccak256 call is one invocation, which is one KECCAK256 opcode on the EVM, whatever the input length. The
1,056-byte WOTS leaf input takes eight Keccak-f permutations but counts as one call, as in the spec's §1 and §9 counts.

Cache plans (tree_cost). The auth path of leaf idx inside the kept subtree is its siblings at levels 0..b-1. The
surrogate siblings at levels b..24 are stored with the key and are not part of the cache budget, as in the script.
A cache of cache_bytes holds cache_bytes // 16 nodes (the script's `cache // N`). A plan keeps one of these:

    whole       every node of the subtree, 2^(b+1) - 1 nodes                  0 calls per signature
    top    c    levels c..b, 2^(b-c+1) - 1 nodes                              2^c·leaf + (2^c - 1)
    level  c    level c only, 2^(b-c) nodes                                   2^c·leaf + (2^c - 1) + (2^(b-c) - 1)
    none        nothing (c = b)                                               2^b·leaf + (2^b - 1)

Here 1 <= c <= b. "2^c·leaf + (2^c - 1)" rebuilds the 2^c-leaf block that holds idx, which gives the siblings at
levels 0..c-1. A "level" plan also rehashes the 2^(b-c) cached nodes up to the subtree root to get the siblings at
levels c+1..b-1. plan() takes the cheapest plan that fits. On equal cost it takes the one with fewer cached nodes,
then prefers "top" over "level". With either unit system, the only ties are between "none", "top b" and "level b".
These are the same work (no cache), and the rule picks "none". The cache is filled from the keygen pass, which
computes every node of the subtree anyway, so a plan adds nothing to keygen.

Signature cost, mean (expected_sign_calls):

    R_0 + digest + grind + FORS + WOTS+C + tree_cost
    grind   2^(25-b) digest tries for b < 25: a geometric mean, because the randomizer is ground until the leaf
            lands in the kept subtree. 0 for b = 25.
    FORS    13·(2048 derives + 4096 leaves + 4094 nodes) + FORS key = 133,095 calls
    WOTS+C  mean ENC tries (4^64 / #{x : Σx = 128} ≈ 14,670.4) + 32 derives + 128 chain steps

Both grinds are geometric, so the cost of a single signature varies about its mean. Keygen is
derive(P) + 2^b·(leaf + node) + (25 - b)·(derive + node), with the surrogates derived and folded.

Three script conventions are kept, so the counts match the page. Against a minimal implementation, each overcounts
by one call or one cached node:
  - for b < 25 the digest is counted on top of the grind, though the grind's last try is the digest;
  - keygen counts 2^b nodes where the kept subtree has 2^b - 1;
  - "top" caches (one node), and "level" rehashes (one call), the subtree root (level b), which no auth path uses.

The Rust signer (src/tiers.rs) is not minimal in two of these places. It recomputes the digest after the grind, and
its "level" rehash up to the subtree root is its cache check. It also derives the 13 opened FORS secrets a second
time, which the model does not count. Measured against this model: its keygen is 1 call under; its auth path equals
tree_cost exactly; a signature costs the model's mean + 13 for b < 25, and + 14 at b = 25 (where it also makes one
grind try, against the model's 0). `ls23k sign-key` then verifies the signature (249 calls) and loads and checks the
key file, neither of which the model counts.

Lifetime (cover_lifetime): the cover estimate of leanSPHINCS.pdf §3 at LEVEL = 127 bits. It is the largest N with

    2^127 · 2^(b - 25) · E_{r ~ Poisson(N / 2^b)}[(1 - (1 - 2^-12)^r)^13] <= 1.

It is an estimate, not a proof. For the leanSphincs parameters, Tom's Lean-proved lifetimes are 4-17% below this
estimate, and the gap is worse at small b. The page therefore rates each tier at a target that the estimate clears
by MARGIN = 1.25: Light 20,000 (est. 40.2K), Standard 2^21 (est. 2.78M), Full 2^23 (est. 54.0M). The page rounds
lifetimes down and costs to nearest, and fmt() does the same. The estimate depends only on (h, b, a, k), so it is the
same in both unit systems.

Usage:
    tier_model.py                                  # the three tiers, keccak256 calls
    tier_model.py --b 16 --cache-bytes 64KiB       # the three tiers and a custom (b, cache) column
    tier_model.py --units blake2s                  # BLAKE2s compressions and the page's device times
    tier_model.py --json                           # machine-readable
    tier_model.py --check                          # assert the pinned keccak and BLAKE2s figures; exit 1 on a miss

Only the standard library is used (no numpy or scipy), so any python3 runs it.
"""

import argparse
import json
import math
import re
import sys
from functools import lru_cache
from typing import NamedTuple

# ============================================================
#  leanSphincs-23 (spec §1)
# ============================================================

N = 16  # node bytes: one cached node is 16 bytes
H = 25  # XMSS height, one layer
A = 12  # FORS tree height
K = 13  # FORS trees
V = 64  # WOTS+C chains
W = 4  # chain positions (2-bit chunks)
T_SUM = 128  # WOTS+C target sum
TOP = V * (W - 1)  # 192 chain steps from the secrets to the chain ends

LEVEL = 127  # bits, the cover estimate's security level (the script's LEVEL)
MARGIN = 1.25  # the page's tiers clear target · MARGIN under the estimate (the script's default --margin)


# ============================================================
#  Units
# ============================================================


class Units(NamedTuple):
    name: str
    derive: int  # one PRF call: two secrets
    step: int  # one chain step, or one FORS leaf (a hash of a 16-byte value)
    node: int  # one tree node (XMSS, FORS, or a surrogate fold)
    enc: int  # one WOTS+C encoding try
    wots_pk: int  # the WOTS leaf hash over the 64 chain ends
    fors_key: int  # the FORS key over the 26 tops
    rnd: int  # R_0
    digest: int  # the message digest
    grind_try: int  # one randomizer try

    @property
    def leaf(self):
        """One WOTS leaf from the seed: 32 derives, 192 chain steps, the leaf hash."""
        return V // 2 * self.derive + TOP * self.step + self.wots_pk


def _comp(input_bytes):
    """BLAKE2s compressions for one call over P (16) ‖ address (16) ‖ input: the script's comp()."""
    return max(1, math.ceil((32 + input_bytes) / 64))


KECCAK = Units("keccak", derive=1, step=1, node=1, enc=1, wots_pk=1, fors_key=1, rnd=1, digest=1, grind_try=1)
BLAKE2S = Units(
    "blake2s",
    derive=_comp(32),
    step=_comp(N),
    node=_comp(2 * N),
    enc=_comp(N + 4),
    wots_pk=_comp(V * N),
    fors_key=_comp(2 * K * N),
    rnd=_comp(64),
    digest=math.ceil((H + K * A) / 256) * _comp(32 + N),
    grind_try=1,
)
UNITS = {u.name: u for u in (KECCAK, BLAKE2S)}
UNIT_LABEL = {"keccak": "keccak256 calls", "blake2s": "BLAKE2s compressions"}


# ============================================================
#  Tiers (the page's "One signer, leanSphincs-23")
# ============================================================


class Tier(NamedTuple):
    name: str
    device: str
    b: int
    cache_bytes: int
    target: int  # the page's rated lifetime (signatures), or 0 for a custom column
    rate: float  # the page's device speed in BLAKE2s compressions per second, or 0


TIERS = (
    Tier("Light", "Ledger Nano S+", 13, 16 * 2**10, 20_000, 33e3),
    Tier("Standard", "weak CPU", 20, 2**20, 2**21, 128e6),
    Tier("Full", "powerful CPU", 25, 16 * 2**20, 2**23, 1e9),
)


# ============================================================
#  Cache plans and the auth-path cost (the script's tree_cost)
# ============================================================


class Plan(NamedTuple):
    kind: str  # "whole" | "top" | "level" | "none"
    c: int  # the lowest cached level (0 for "whole", b for "none")
    nodes: int  # cached nodes, 16 bytes each


_KIND_RANK = {"whole": 0, "top": 1, "level": 2, "none": 3}


def cache_nodes(cache_bytes):
    return cache_bytes // N


def _check_b(b):
    if not 0 <= b <= H:
        raise ValueError(f"b must be in [0, {H}], got {b}")


def _block(c, u):
    """Rebuild the 2^c-leaf block holding the signed leaf: its siblings at levels 0..c-1."""
    return 2**c * u.leaf + (2**c - 1) * u.node


def plan_cost(b, p, u=KECCAK):
    """Per-signature auth-path cost of plan p for a kept subtree of 2^b leaves."""
    if p.kind == "whole":
        return 0
    if p.kind == "level":
        return _block(p.c, u) + (2 ** (b - p.c) - 1) * u.node
    return _block(p.c, u)  # "top", or "none" (c = b)


def _plans(b, max_nodes):
    """Every plan the script considers that fits in max_nodes cached nodes."""
    whole = 2 ** (b + 1) - 1
    if whole <= max_nodes:
        yield Plan("whole", 0, whole)
    yield Plan("none", b, 0)
    for c in range(1, b + 1):
        if 2 ** (b - c + 1) - 1 <= max_nodes:
            yield Plan("top", c, 2 ** (b - c + 1) - 1)
        if 2 ** (b - c) <= max_nodes:
            yield Plan("level", c, 2 ** (b - c))


def plan(b, cache_bytes, u=KECCAK):
    """The cheapest plan that fits: ties go to fewer cached nodes, then "top" over "level"."""
    _check_b(b)
    return min(_plans(b, cache_nodes(cache_bytes)), key=lambda p: (plan_cost(b, p, u), p.nodes, _KIND_RANK[p.kind]))


def tree_cost(b, cache_bytes, u=KECCAK):
    """Auth-path work per signature (the script's tree_cost(b, cache // N, leaf))."""
    return plan_cost(b, plan(b, cache_bytes, u), u)


def describe(b, p):
    if p.kind == "whole":
        return f"whole subtree (levels 0..{b})"
    if p.kind == "top":
        return f"levels {p.c}..{b}"
    if p.kind == "level":
        return f"level {p.c} only"
    return "none"


# ============================================================
#  Keygen and signing
# ============================================================


@lru_cache(maxsize=None)
def wots_c_tries():
    """Mean WOTS+C encoding tries: 1 / P[Σx = T] for 64 uniform 2-bit chunks."""
    poly = [1]
    for _ in range(V):
        new = [0] * (len(poly) + W - 1)
        for i, coef in enumerate(poly):
            for d in range(W):
                new[i + d] += coef
        poly = new
    return W**V / poly[T_SUM]


def keygen_calls(b, u=KECCAK):
    """derive(P) + 2^b·(leaf + node) + (25 - b)·(surrogate derive + fold): the script's tier_costs keygen."""
    _check_b(b)
    return u.derive + 2**b * (u.leaf + u.node) + (H - b) * (u.derive + u.node)


def fors_sign_calls(u=KECCAK):
    """All 13 FORS trees (no roots: 4094 nodes each) and the FORS key: the script's fors_sign."""
    return K * (2**A // 2 * u.derive + 2**A * u.step + (2**A - 2) * u.node) + u.fors_key


def wots_c_sign_calls(u=KECCAK):
    """Mean ENC tries, 32 derives, and the 128 chain steps to the codeword."""
    return u.enc * wots_c_tries() + V // 2 * u.derive + T_SUM * u.step


def grind_calls(b, u=KECCAK):
    """Mean randomizer tries until the digest's leaf lands in the kept subtree; 0 for a full key."""
    _check_b(b)
    return 2 ** (H - b) * u.grind_try if b < H else 0


def sign_breakdown(b, cache_bytes, u=KECCAK):
    p = plan(b, cache_bytes, u)
    parts = {
        "r0": u.rnd,
        "digest": u.digest,
        "grind": grind_calls(b, u),
        "fors": fors_sign_calls(u),
        "wots_c": wots_c_sign_calls(u),
        "tree": plan_cost(b, p, u),
    }
    parts["total"] = sum(parts.values())
    return parts


def expected_sign_calls(b, cache_bytes, u=KECCAK):
    """Mean cost of one signature: the script's tier_costs sign."""
    return sign_breakdown(b, cache_bytes, u)["total"]


def verify_calls(u=KECCAK):
    """Verification (spec §1): 249 keccak256 calls, or 272 BLAKE2s compressions."""
    fors = K * (u.step + (A - 1) * u.node) + u.fors_key
    return u.digest + fors + u.enc + (TOP - T_SUM) * u.step + u.wots_pk + H * u.node


# ============================================================
#  Lifetime: the cover estimate (the script's fors_bits / tier_ok / cover_lifetime)
# ============================================================


@lru_cache(maxsize=None)
def fors_bits(n_sigs, b):
    """-log2 E_{r ~ Poisson(n_sigs / 2^b)}[(1 - (1 - 2^-a)^r)^k]: forging at a random one of 2^b instances."""
    lam = n_sigs / 2**b
    if lam > 2 ** (A - 1):  # every leaf of every tree is half-covered
        return 0.0
    hi = int(lam + 60 * math.sqrt(lam) + 400)
    log_lam, log_miss = math.log(lam), math.log1p(-(2.0**-A))
    terms = [
        -lam + r * log_lam - math.lgamma(r + 1) + K * math.log(-math.expm1(r * log_miss)) for r in range(1, hi + 1)
    ]
    top = max(terms)
    return -(top + math.log(math.fsum(math.exp(t - top) for t in terms))) / math.log(2)


def tier_ok(n_sigs, b):
    return (H - b) + fors_bits(n_sigs, b) >= LEVEL


@lru_cache(maxsize=None)
def cover_lifetime(b):
    """Largest number of signatures the cover estimate allows at LEVEL bits (an estimate, not a proof)."""
    _check_b(b)
    lo, hi = 1, 2 ** (b + A)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if tier_ok(mid, b) else (lo, mid)
    return lo


# ============================================================
#  Report
# ============================================================


def evaluate(tier, u=KECCAK, lifetime=True):
    b, cache = tier.b, tier.cache_bytes
    p = plan(b, cache, u)
    out = {
        "tier": tier.name,
        "device": tier.device,
        "b": b,
        "cache_bytes": cache,
        "cache_nodes": cache_nodes(cache),
        "plan": {"kind": p.kind, "c": p.c, "nodes": p.nodes, "bytes": p.nodes * N, "levels": describe(b, p)},
        "tree_cost": plan_cost(b, p, u),
        "keygen": keygen_calls(b, u),
        "sign": sign_breakdown(b, cache, u),
    }
    if lifetime:
        est = cover_lifetime(b)
        out["lifetime"] = {
            "estimate": est,
            "max_target_at_margin": math.floor(est / MARGIN),
            "target": tier.target or None,
            "target_ok": tier_ok(tier.target * MARGIN, b) if tier.target else None,
        }
    if u is BLAKE2S and tier.rate:
        out["seconds"] = {"keygen": out["keygen"] / tier.rate, "sign": out["sign"]["total"] / tier.rate}
    return out


def fmt(x, down=False, sig=3):
    """sig significant figures with K / M / B, as on the page. down=True rounds down (lifetimes)."""
    if x < 1000:
        return str(math.floor(x) if down else round(x))
    q = 10.0 ** (math.floor(math.log10(x)) - (sig - 1))
    x = (math.floor(x / q) if down else round(x / q)) * q
    e = math.floor(math.log10(x) + 1e-9)
    unit = min(9, e - e % 3)
    return f"{x / 10**unit:.{max(0, sig - 1 - (e - unit))}f}{ {3: 'K', 6: 'M', 9: 'B'}[unit]}"


def fmt_time(s):
    """Two significant figures, seconds or milliseconds, as on the page."""
    v, unit = (s, "s") if s >= 1 else (s * 1e3, "ms")
    return f"{v:.{max(0, 1 - math.floor(math.log10(v)))}f} {unit}"


def fmt_bytes(n):
    for div, unit in ((2**30, "GiB"), (2**20, "MiB"), (2**10, "KiB")):
        if n >= div and n % div == 0:
            return f"{n // div} {unit}"
    return f"{n:,} B"


def table(rows, u):
    def pair(x, down=False):
        return f"{round(x):,} ({fmt(x, down)})" if x >= 1000 else f"{round(x):,}"

    lines = [
        ("device", [r["device"] for r in rows]),
        ("kept subtree", [f"2^{r['b']}" + (" (whole tree)" if r["b"] == H else "") for r in rows]),
        ("cache", [f"{fmt_bytes(r['cache_bytes'])} ({r['cache_nodes']:,} nodes)" for r in rows]),
        ("cache plan", [r["plan"]["levels"] for r in rows]),
        ("cached", [f"{r['plan']['nodes']:,} nodes = {r['plan']['bytes']:,} B" for r in rows]),
        ("keygen (once)", [pair(r["keygen"]) for r in rows]),
        ("sign, mean", [pair(r["sign"]["total"]) for r in rows]),
        ("  R_0 + digest", [str(r["sign"]["r0"] + r["sign"]["digest"]) for r in rows]),
        ("  randomizer grind", [f"{r['sign']['grind']:,}" for r in rows]),
        ("  FORS", [f"{r['sign']['fors']:,}" for r in rows]),
        ("  WOTS+C", [f"{r['sign']['wots_c']:,.1f}" for r in rows]),
        ("  auth path", [f"{r['sign']['tree']:,}" for r in rows]),
    ]
    if "seconds" in rows[0]:
        lines.append(("keygen time", [fmt_time(r["seconds"]["keygen"]) if "seconds" in r else "-" for r in rows]))
        lines.append(("sign time", [fmt_time(r["seconds"]["sign"]) if "seconds" in r else "-" for r in rows]))
    if "lifetime" in rows[0]:

        def rated(r):
            lt = r["lifetime"]
            if not lt["target"]:
                return "-"
            return f"{lt['target']:,} ({fmt(lt['target'], sig=2)})" + ("" if lt["target_ok"] else " FAILS")

        def estimate(r):
            lt = r["lifetime"]
            ratio = f", x{lt['estimate'] / lt['target']:.2f}" if lt["target"] else ""
            return f"{lt['estimate']:,} ({fmt(lt['estimate'], True)}{ratio})"

        lines.append(("lifetime, rated", [rated(r) for r in rows]))
        lines.append(("lifetime, estimate", [estimate(r) for r in rows]))
        lines.append((f"  max rating at x{MARGIN}", [f"{r['lifetime']['max_target_at_margin']:,}" for r in rows]))

    head = [""] + [r["tier"] for r in rows]
    body = [[label] + cells for label, cells in lines]
    widths = [max(len(row[i]) for row in [head] + body) for i in range(len(head))]
    out = [
        f"leanSphincs-23 signer tiers in {UNIT_LABEL[u.name]} (h={H}, a={A}, k={K}; WOTS+C v={V}, w={W}, T={T_SUM}; "
        f"verify {verify_calls(u)})",
        "",
    ]
    for row in [head] + body:
        out.append("  ".join(cell.ljust(w) for cell, w in zip(row, widths)).rstrip())
    out.append("")
    out.append(
        f"Sign is a mean: the randomizer grind (2^(25-b) tries) and the WOTS+C counter (~{wots_c_tries():,.0f} tries) "
        "are geometric."
    )
    if "lifetime" in rows[0]:
        out.append(
            f"Lifetimes are the cover estimate at {LEVEL} bits, not proved. The page rates each tier at a target "
            f"that the estimate clears by x{MARGIN}."
        )
    return "\n".join(out)


# ============================================================
#  --check: pinned figures
# ============================================================

# sweep_leansphincs_pruned.py at sphincs-art 1ca729f, evaluated at h=25 b=13/20/25 a=12 k=13 (WOTS+C lg_w=2 T=128)
# with its DEVICES caches. tree_cost there is 2958 / 7743 / 15487 compressions. The page's rounded figures follow.
SCRIPT_BLAKE2S = {
    "Light": dict(keygen=1_982_489, tree=2958, sign=154_989.37193700805, lifetime=40_274),
    "Standard": dict(keygen=253_755_403, tree=7743, sign=155_710.37193700805, lifetime=2_781_217),
    "Full": dict(keygen=8_120_172_545, tree=15_487, sign=163_422.37193700805, lifetime=54_085_110),
}
PAGE = {  # the page's "One signer, leanSphincs-23" figures (sign, keygen, sign time, keygen time, estimate, rated)
    "Light": ("155K", "1.98M", "4.7 s", "60 s", "40.2K", "20K"),
    "Standard": ("156K", "254M", "1.2 ms", "2.0 s", "2.78M", "2.1M"),
    "Full": ("163K", "8.12B", "0.16 ms", "8.1 s", "54.0M", "8.4M"),
}
KECCAK_PINNED = {  # (plan, tree_cost, keygen, mean sign)
    "Light": (Plan("level", 3, 1024), 2830, 1_851_417, 154_853.37193700805),
    "Standard": (Plan("top", 5, 65_535), 7231, 236_978_187, 155_190.37193700805),
    "Full": (Plan("top", 6, 1_048_575), 14_463, 7_583_301_633, 162_390.37193700805),
}


def check():
    failures = 0

    def expect(label, got, want):
        nonlocal failures
        ok = abs(got - want) < 1e-6 if isinstance(want, float) else got == want
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {label}: {got!r}" + ("" if ok else f" (want {want!r})"))

    expect("verify, keccak256 calls (spec §1)", verify_calls(KECCAK), 249)
    expect("verify, BLAKE2s compressions (spec §1)", verify_calls(BLAKE2S), 272)
    expect("WOTS leaf, keccak", KECCAK.leaf, 225)
    expect("WOTS leaf, BLAKE2s", BLAKE2S.leaf, 241)
    expect("FORS signing, keccak", fors_sign_calls(KECCAK), 133_095)
    expect("FORS signing, BLAKE2s", fors_sign_calls(BLAKE2S), 133_101)
    expect("WOTS+C mean tries", wots_c_tries(), 14_670.371937008062)
    for t in TIERS:
        kp, kt, kk, ks = KECCAK_PINNED[t.name]
        expect(f"{t.name} keccak plan", plan(t.b, t.cache_bytes), kp)
        expect(f"{t.name} keccak tree_cost", tree_cost(t.b, t.cache_bytes), kt)
        expect(f"{t.name} keccak keygen", keygen_calls(t.b), kk)
        expect(f"{t.name} keccak keygen formula", keygen_calls(t.b), 1 + 2**t.b * 226 + 2 * (H - t.b))
        expect(f"{t.name} keccak sign", expected_sign_calls(t.b, t.cache_bytes), ks)

        r = evaluate(t, BLAKE2S)
        s = SCRIPT_BLAKE2S[t.name]
        expect(f"{t.name} BLAKE2s keygen", r["keygen"], s["keygen"])
        expect(f"{t.name} BLAKE2s tree_cost", r["tree_cost"], s["tree"])
        expect(f"{t.name} BLAKE2s sign", r["sign"]["total"], s["sign"])
        expect(f"{t.name} lifetime estimate", r["lifetime"]["estimate"], s["lifetime"])
        expect(f"{t.name} clears its target x{MARGIN}", r["lifetime"]["target_ok"], True)
        got = (
            fmt(r["sign"]["total"]),
            fmt(r["keygen"]),
            fmt_time(r["seconds"]["sign"]),
            fmt_time(r["seconds"]["keygen"]),
            fmt(r["lifetime"]["estimate"], down=True),
            fmt(t.target, sig=2),
        )
        expect(f"{t.name} page figures", got, PAGE[t.name])
    print("all pinned figures match" if not failures else f"{failures} mismatch(es)")
    return failures == 0


# ============================================================
#  CLI
# ============================================================


def parse_bytes(s):
    m = re.fullmatch(r"\s*(\d+)\s*(|B|K|KiB|M|MiB|G|GiB)\s*", s, re.IGNORECASE)
    if not m:
        raise argparse.ArgumentTypeError(f"not a byte count: {s!r} (e.g. 16384, 16KiB, 1MiB)")
    scale = {"": 1, "b": 1, "k": 2**10, "kib": 2**10, "m": 2**20, "mib": 2**20, "g": 2**30, "gib": 2**30}
    return int(m.group(1)) * scale[m.group(2).lower()]


def main():
    ap = argparse.ArgumentParser(description=__doc__.strip().split("\n\n")[0])
    ap.add_argument("--b", type=int, help="custom kept-subtree height (with --cache-bytes)")
    ap.add_argument("--cache-bytes", type=parse_bytes, help="custom cache size: 16384, 16KiB, 1MiB, ...")
    ap.add_argument("--units", choices=sorted(UNITS), default="keccak", help="keccak256 calls (default) or BLAKE2s")
    ap.add_argument("--json", action="store_true", help="print one JSON object")
    ap.add_argument("--check", action="store_true", help="assert the pinned figures and exit")
    args = ap.parse_args()

    if args.check:
        sys.exit(0 if check() else 1)
    if (args.b is None) != (args.cache_bytes is None):
        ap.error("--b and --cache-bytes go together")
    tiers = list(TIERS)
    if args.b is not None:
        if not 0 <= args.b <= H:
            ap.error(f"--b must be in [0, {H}]")
        tiers.append(Tier("Custom", "-", args.b, args.cache_bytes, 0, 0.0))

    u = UNITS[args.units]
    rows = [evaluate(t, u) for t in tiers]
    if args.json:
        doc = {
            "scheme": "leanSphincs-23",
            "units": UNIT_LABEL[u.name],
            "params": dict(h=H, a=A, k=K, v=V, w=W, T=T_SUM, n=N),
            "unit_costs": {**u._asdict(), "wots_leaf": u.leaf},
            "verify": verify_calls(u),
            "wots_c_mean_tries": wots_c_tries(),
            "lifetime_model": {"level_bits": LEVEL, "margin": MARGIN, "proved": False},
            "tiers": rows,
        }
        print(json.dumps(doc, indent=1))
    else:
        print(table(rows, u))


if __name__ == "__main__":
    main()
