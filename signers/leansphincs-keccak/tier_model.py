#!/usr/bin/env python3
"""
Cost model for the leanSphincs signer tiers, in keccak256 calls and Keccak-f permutations
(docs/leanSphincs-keccak.md; the tiers of the leanSphincs-S spec's section 14, at these parameters).

leanSphincs is the proposal at its own parameters (the upstream crate's keccak branch: h = 26, a = 10, k = 24,
T = 120). The tiers are the sphincs-art fork's "One signer" table (https://nconsigny.github.io/sphincs-art/), FORS,
Keccak-256, which is the proposal's own. The key is generated once, keeping a subtree of 2^b leaves, and stored with
a node cache of bounded size. Each signature then recomputes only the auth-path nodes the cache does not hold:

    tier       device class      b    cache    lifetime (the proposal's, proved in Lean)
    Light      Ledger Nano S+    13   16 KiB   210K
    Standard   weak CPU          20    1 MiB   22M
    Full       powerful CPU      26   16 MiB   1.15B (2^30; whole tree)

This is a transcription of scripts/keccak_model.py in nconsigny/sphincs-art (commit 537dfd9): its fors() and tiers(),
which take tree_cost and cover_lifetime from scripts/sweep_leansphincs_pruned.py there, at the parameters of its
"Tom FORS (check 354)" line, fors(26, 24, 10, 120). keccak_model.py is the cost model of the upstream crate's keccak
branch (TomWambsgans/leanXMSS-leanSPHINCS-candidates, scripts/scheme.py): one Keccak-f permutation per 136-byte block,
and no FORS key hash (the WOTS+C encoding absorbs the FORS tops, then the counter). Every formula is the script's. In
permutations this file gives the page's figures; in keccak256 calls it counts invocations instead. --check asserts
both unit systems against pinned values, and --sphincs-art DIR runs the script itself (it needs numpy and scipy) and
compares.

Unit costs (P ‖ address ‖ input; a call over L bytes is ⌊L/136⌋ + 1 permutations)   calls   permutations
  derive: one PRF call gives two secrets (S, 64 B in all)                             1       1
  chain step, FORS leaf (48 B), tree node (64 B)                                      1       1
  WOTS leaf hash over the 64 chain ends (1,056 B)                                     1       8
  WOTS leaf from the seed: 32 + 192 + 1                                               225     232
  R_0 (S ‖ m, 96 B), randomizer grind per try (call 0 of the digest, m ‖ ρ, 80 B)     1 each  1 each
  message digest: two calls of 80 B (266 bits: the leaf index and 24 FORS indices)    2       2
  WOTS+C encoding, verifier: P ‖ address ‖ tops ‖ counter (804 B)                     1       6
  WOTS+C encoding, signer: the tops' 5 whole blocks once, then per counter tried     0 + 1   5 + 1

A keccak256 call is one invocation, which is one KECCAK256 opcode on the EVM, whatever the input length. The Rust
signer counts both (keccak_calls() and permutations(); a midstate counts its whole blocks once).

Cache plans (tree_cost). The auth path of leaf idx inside the kept subtree is its siblings at levels 0..b-1. The
surrogate siblings at levels b..25 are stored with the key and are not part of the cache budget, as in the script.
A cache of cache_bytes holds cache_bytes // 16 nodes (the script's `cache // N`). A plan keeps one of these:

    whole       every node of the subtree, 2^(b+1) - 1 nodes                  0 per signature
    top    c    levels c..b, 2^(b-c+1) - 1 nodes                              2^c·leaf + (2^c - 1)
    level  c    level c only, 2^(b-c) nodes                                   2^c·leaf + (2^c - 1) + (2^(b-c) - 1)
    none        nothing (c = b)                                               2^b·leaf + (2^b - 1)

Here 1 <= c <= b, and leaf is 225 calls or 232 permutations (keccak_model.py passes LEAF = 232 to tree_cost).
"2^c·leaf + (2^c - 1)" rebuilds the 2^c-leaf block that holds idx, which gives the siblings at levels 0..c-1. A
"level" plan also rehashes the 2^(b-c) cached nodes up to the subtree root to get the siblings at levels c+1..b-1.
plan() takes the cheapest plan that fits. On equal cost it takes the one with fewer cached nodes, then prefers "top"
over "level". The only ties are between "none", "top b" and "level b". These are the same work (no cache), and the
rule picks "none". Both unit systems choose the same plan for every b and budget (--check verifies it for every
threshold): the leaf's cost decides only "top c+1" against "level c", where "level c" is cheaper iff
2^(b-2c) <= leaf + 1, and no power of two lies in 226..233. The cache is filled from the keygen pass, which computes
every node of the subtree anyway, so a plan adds nothing to keygen. The tree, the WOTS leaf and so the plans and
keygen are leanSphincs-S's: only FORS, T and the digest differ.

Signature cost, mean (expected_sign):

    R_0 + digest + grind + FORS + WOTS+C + tree_cost
    grind   2^(26-b) tries of the digest's call 0 for b < 26: a geometric mean, because the randomizer is ground
            until the leaf lands in the kept subtree. 0 for b = 26.
    FORS    24·(512 derives + 1024 leaves + 1022 nodes) = 61,392, both units: no FORS key hash
    WOTS+C  the encoding's fixed part (0 calls, 5 permutations) + mean counters tried
            (4^64 / #{x : Σx = 120} ≈ 829.2, one call and one permutation each) + 32 derives + 120 chain steps

Both grinds are geometric, so the cost of a single signature varies about its mean. Keygen is
derive(P) + 2^b·(leaf + node) + (26 - b)·(derive + node), with the surrogates derived and folded.

Three script conventions are kept, so the counts match the page. Against a minimal implementation, each overcounts
by one call or one cached node:
  - for b < 26 the digest is counted on top of the grind, though the grind's last try is the digest's call 0;
  - keygen counts 2^b nodes where the kept subtree has 2^b - 1;
  - "top" caches (one node), and "level" rehashes (one call), the subtree root (level b), which no auth path uses.

The Rust signer (src/tiers.rs) is not minimal in two of these places. It recomputes both digest calls after the
grind, and its "level" rehash up to the subtree root is its cache check. It also derives the 24 opened FORS secrets a
second time, which the model does not count. Measured against this model, in calls and in permutations alike (each
of these calls is one permutation): its keygen is 1 under; its auth path equals tree_cost exactly; a signature costs
the model's mean + 24 for b < 26, and + 25 at b = 26 (where it also makes one grind try, against the model's 0).
`lsk sign-key` then verifies the signature (342 calls, 354 permutations) and loads and checks the key file, neither
of which the model counts.

Lifetime. The tiers' lifetimes are the proposal's, proved in Lean (formal/sphincs upstream): 210K, 22M and 1.15B
signatures, the full tree 2^30 (PROVED_LIFETIME; quoted, not recomputed). This file also computes the cover estimate
(cover_lifetime, leanSPHINCS.pdf §3, at LEVEL = 127 bits), the largest N with

    2^127 · 2^(b - 26) · E_{r ~ Poisson(N / 2^b)}[(1 - (1 - 2^-10)^r)^24] <= 1,

which gives 242K / 23.7M / 1.20B. The proved figures sit 13% / 7.6% / 4.4% below it: the proofs also bound adaptive
forgers and the WOTS+C neighbour route, and the sphincs-art README gives this gap as 4-17%, worse at small b (it is
the gap the page applies to the leanSphincs-S estimates). The estimate depends only on (h, b, a, k). The page rounds
lifetimes down and costs to nearest, and fmt() does the same; the page's signing figures are the three-figure value
rounded again to two (73,459 is 73.5K, shown as 74K), and its times below a second have one decimal.

Usage:
    tier_model.py                                  # the three tiers, keccak256 calls then Keccak-f permutations
    tier_model.py --units permutations             # one unit only (calls | permutations | both)
    tier_model.py --b 16 --cache-bytes 64KiB       # the three tiers and a custom (b, cache) column
    tier_model.py --json                           # machine-readable, both units
    tier_model.py --check                          # assert the pinned figures; exit 1 on a miss
    tier_model.py --sphincs-art ~/sphincs-art      # compare with that checkout's scripts/keccak_model.py (numpy, scipy)

Only the standard library is used (no numpy or scipy) except by --sphincs-art, so any python3 runs it.
"""

import argparse
import json
import math
import re
import sys
from functools import lru_cache
from pathlib import Path
from typing import NamedTuple

# ============================================================
#  leanSphincs (docs/leanSphincs-keccak.md)
# ============================================================

N = 16  # node bytes: one cached node is 16 bytes
H = 26  # XMSS height, one layer
A = 10  # FORS tree height
K = 24  # FORS trees
V = 64  # WOTS+C chains
W = 4  # chain positions (2-bit chunks)
T_SUM = 120  # WOTS+C target sum
TOP = V * (W - 1)  # 192 chain steps from the secrets to the chain ends
TOPS = 2 * K * N  # 768 bytes: the two level-9 nodes of each FORS tree, which the WOTS+C encoding absorbs
DIGEST_CALLS = math.ceil((H + K * A) / 256)  # 266 digest bits: two calls
RATE = 136  # keccak256's sponge rate in bytes

LEVEL = 127  # bits, the cover estimate's security level (the script's LEVEL)


# ============================================================
#  Units
# ============================================================


class Units(NamedTuple):
    name: str
    derive: int  # one PRF call: two secrets
    step: int  # one chain step, or one FORS leaf (a hash of a 16-byte value)
    node: int  # one tree node (XMSS, FORS, or a surrogate fold)
    wots_pk: int  # the WOTS leaf hash over the 64 chain ends
    rnd: int  # R_0
    digest: int  # the message digest (two calls)
    grind_try: int  # one randomizer try
    enc: int  # one WOTS+C encoding, as the verifier computes it (the whole input)
    enc_fixed: int  # the signer's encoding midstate: the whole blocks of P ‖ address ‖ tops, once per signature
    enc_try: int  # one counter tried from the midstate

    @property
    def leaf(self):
        """One WOTS leaf from the seed: 32 derives, 192 chain steps, the leaf hash."""
        return V // 2 * self.derive + TOP * self.step + self.wots_pk


def _perm(input_bytes):
    """Keccak-f permutations of one call over P (16) ‖ address (16) ‖ input: keccak_model.py's comp()."""
    return (32 + input_bytes) // RATE + 1


CALLS = Units(
    "calls", derive=1, step=1, node=1, wots_pk=1, rnd=1, digest=DIGEST_CALLS, grind_try=1, enc=1, enc_fixed=0, enc_try=1
)
PERMUTATIONS = Units(
    "permutations",
    derive=_perm(32),
    step=_perm(N),
    node=_perm(2 * N),
    wots_pk=_perm(V * N),
    rnd=_perm(64),
    digest=DIGEST_CALLS * _perm(32 + N),  # keccak_model.py: math.ceil((h + k * a) / 256) * MSG
    grind_try=_perm(32 + N),
    enc=_perm(TOPS + 4),
    enc_fixed=(32 + TOPS) // RATE,  # keccak_model.py's merged(): fixed // RATE
    enc_try=((32 + TOPS) % RATE + 4) // RATE + 1,  # and (fixed % RATE + 4) // RATE + 1
)
UNITS = {u.name: u for u in (CALLS, PERMUTATIONS)}
UNIT_LABEL = {"calls": "keccak256 calls", "permutations": "Keccak-f permutations"}


# ============================================================
#  Tiers (the page's "One signer")
# ============================================================


class Tier(NamedTuple):
    name: str
    device: str
    b: int
    cache_bytes: int
    rate: float  # the page's device speed in Keccak-f permutations per second, or 0


TIERS = (
    Tier("Light", "Ledger Nano S+", 13, 16 * 2**10, 5.8e3),
    Tier("Standard", "weak CPU", 20, 2**20, 128e6),
    Tier("Full", "powerful CPU", 26, 16 * 2**20, 512e6),
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


def plan_cost(b, p, u=CALLS):
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


def plan(b, cache_bytes, u=CALLS):
    """The cheapest plan that fits: ties go to fewer cached nodes, then "top" over "level"."""
    _check_b(b)
    return min(_plans(b, cache_nodes(cache_bytes)), key=lambda p: (plan_cost(b, p, u), p.nodes, _KIND_RANK[p.kind]))


def tree_cost(b, cache_bytes, u=CALLS):
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
    """Mean WOTS+C encoding tries: 1 / P[Σx = T] for 64 uniform 2-bit chunks (keccak_model.py's 1 / alpha(T))."""
    poly = [1]
    for _ in range(V):
        new = [0] * (len(poly) + W - 1)
        for i, coef in enumerate(poly):
            for d in range(W):
                new[i + d] += coef
        poly = new
    return W**V / poly[T_SUM]


def keygen_cost(b, u=CALLS):
    """derive(P) + 2^b·(leaf + node) + (26 - b)·(surrogate derive + fold): the script's tiers() keygen."""
    _check_b(b)
    return u.derive + 2**b * (u.leaf + u.node) + (H - b) * (u.derive + u.node)


def fors_sign_cost(u=CALLS):
    """All 24 FORS trees (no roots: 1022 nodes each), and no FORS key: keccak_model.py's fts_sign."""
    return K * (2**A // 2 * u.derive + 2**A * u.step + (2**A - 2) * u.node)


def wots_c_sign_cost(u=CALLS):
    """The encoding's fixed part, the mean counters tried, 32 derives, and the 120 chain steps to the codeword."""
    return u.enc_fixed + u.enc_try * wots_c_tries() + V // 2 * u.derive + T_SUM * u.step


def grind_cost(b, u=CALLS):
    """Mean randomizer tries (the digest's call 0) until its leaf lands in the kept subtree; 0 for a full key."""
    _check_b(b)
    return 2 ** (H - b) * u.grind_try if b < H else 0


def sign_breakdown(b, cache_bytes, u=CALLS):
    p = plan(b, cache_bytes, u)
    parts = {
        "r0": u.rnd,
        "digest": u.digest,
        "grind": grind_cost(b, u),
        "fors": fors_sign_cost(u),
        "wots_c": wots_c_sign_cost(u),
        "tree": plan_cost(b, p, u),
    }
    parts["total"] = sum(parts.values())
    return parts


def expected_sign(b, cache_bytes, u=CALLS):
    """Mean cost of one signature: the script's tiers() sign."""
    return sign_breakdown(b, cache_bytes, u)["total"]


def verify_cost(u=CALLS):
    """Verification: 342 keccak256 calls, or 354 Keccak-f permutations."""
    fors = K * (u.step + (A - 1) * u.node)
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


# The tiers' lifetimes: the proposal's, proved in Lean (the page and the sphincs-art README: 210K / 22M / 1.15B; the
# full tree 2^30). Quoted, not recomputed (module doc).
PROVED_LIFETIME = {"Light": 210_000, "Standard": 22_000_000, "Full": 1_150_000_000}
# The gap between the cover estimate and the proved lifetimes, as the sphincs-art README gives it.
PROOF_GAP = (0.04, 0.17)


# ============================================================
#  Report
# ============================================================


def evaluate(tier, lifetime=True):
    """One tier in both unit systems."""
    b, cache = tier.b, tier.cache_bytes
    p = plan(b, cache, CALLS)
    out = {
        "tier": tier.name,
        "device": tier.device,
        "b": b,
        "cache_bytes": cache,
        "cache_nodes": cache_nodes(cache),
        "plan": {"kind": p.kind, "c": p.c, "nodes": p.nodes, "bytes": p.nodes * N, "levels": describe(b, p)},
        "tree_cost": {u.name: plan_cost(b, p, u) for u in (CALLS, PERMUTATIONS)},
        "keygen": {u.name: keygen_cost(b, u) for u in (CALLS, PERMUTATIONS)},
        "sign": {u.name: sign_breakdown(b, cache, u) for u in (CALLS, PERMUTATIONS)},
    }
    if lifetime:
        est = cover_lifetime(b)
        proved = PROVED_LIFETIME.get(tier.name)  # None for a custom column
        out["lifetime"] = {
            "proved": proved,
            "estimate": est,
            "gap": 1 - proved / est if proved else None,
            "proved_ok": tier_ok(proved, b) if proved else None,
        }
    if tier.rate:
        out["seconds"] = {
            "rate_permutations_per_s": tier.rate,
            "keygen": out["keygen"]["permutations"] / tier.rate,
            "sign": out["sign"]["permutations"]["total"] / tier.rate,
        }
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
    """Two significant figures, in minutes from 2 min up, else seconds; below a second milliseconds with one decimal,
    as on the page's "One signer" table."""
    if s >= 120:
        v, unit = s / 60, "min"
    elif s >= 1:
        v, unit = s, "s"
    else:
        return f"{s * 1e3:.1f} ms"
    return f"{v:.{max(0, 1 - math.floor(math.log10(v)))}f} {unit}"


def fmt_page_sign(x):
    """The page's signing figures: the three-figure value (fmt), rounded again to two (73,459 is 73.5K, then 74K)."""
    q = 10.0 ** (math.floor(math.log10(x)) - 2)
    return fmt(round(x / q) * q, sig=2)


def fmt_bytes(n):
    for div, unit in ((2**30, "GiB"), (2**20, "MiB"), (2**10, "KiB")):
        if n >= div and n % div == 0:
            return f"{n // div} {unit}"
    return f"{n:,} B"


def table(rows, u, lifetime=True):
    def pair(x, down=False):
        return f"{round(x):,} ({fmt(x, down)})" if x >= 1000 else f"{round(x):,}"

    n = u.name
    lines = [
        ("device", [r["device"] for r in rows]),
        ("kept subtree", [f"2^{r['b']}" + (" (whole tree)" if r["b"] == H else "") for r in rows]),
        ("cache", [f"{fmt_bytes(r['cache_bytes'])} ({r['cache_nodes']:,} nodes)" for r in rows]),
        ("cache plan", [r["plan"]["levels"] for r in rows]),
        ("cached", [f"{r['plan']['nodes']:,} nodes = {r['plan']['bytes']:,} B" for r in rows]),
        ("keygen (once)", [pair(r["keygen"][n]) for r in rows]),
        ("sign, mean", [pair(r["sign"][n]["total"]) for r in rows]),
        ("  R_0 + digest", [str(r["sign"][n]["r0"] + r["sign"][n]["digest"]) for r in rows]),
        ("  randomizer grind", [f"{r['sign'][n]['grind']:,}" for r in rows]),
        ("  FORS", [f"{r['sign'][n]['fors']:,}" for r in rows]),
        ("  WOTS+C", [f"{r['sign'][n]['wots_c']:,.1f}" for r in rows]),
        ("  auth path", [f"{r['sign'][n]['tree']:,}" for r in rows]),
    ]
    if u is PERMUTATIONS:
        lines.append(("keygen time", [fmt_time(r["seconds"]["keygen"]) if "seconds" in r else "-" for r in rows]))
        lines.append(("sign time", [fmt_time(r["seconds"]["sign"]) if "seconds" in r else "-" for r in rows]))
    if lifetime and "lifetime" in rows[0]:

        def proved(r):
            lt = r["lifetime"]
            return f"{lt['proved']:,} ({fmt(lt['proved'], True)})" if lt["proved"] else "-"

        def estimate(r):
            lt = r["lifetime"]
            gap = f", proved {lt['gap']:.1%} below" if lt["proved"] else ""
            return f"{lt['estimate']:,} ({fmt(lt['estimate'], True)}{gap})"

        lines.append(("lifetime, proved", [proved(r) for r in rows]))
        lines.append(("lifetime, estimate", [estimate(r) for r in rows]))

    head = [""] + [r["tier"] for r in rows]
    body = [[label] + cells for label, cells in lines]
    widths = [max(len(row[i]) for row in [head] + body) for i in range(len(head))]
    out = [
        f"leanSphincs signer tiers in {UNIT_LABEL[n]} (h={H}, a={A}, k={K}; WOTS+C v={V}, w={W}, T={T_SUM}; "
        f"merged encoding; verify {verify_cost(u)})",
        "",
    ]
    for row in [head] + body:
        out.append("  ".join(cell.ljust(w) for cell, w in zip(row, widths)).rstrip())
    out.append("")
    out.append(
        f"Sign is a mean: the randomizer grind (2^(26-b) tries) and the WOTS+C counter (~{wots_c_tries():,.0f} tries) "
        "are geometric."
    )
    if lifetime and "lifetime" in rows[0]:
        out.append(
            f"Lifetimes: the proposal's, proved in Lean (quoted), and the cover estimate at {LEVEL} bits (computed); "
            "the proofs land below the estimate."
        )
    return "\n".join(out)


# ============================================================
#  --check: pinned figures
# ============================================================

# keccak_model.py at sphincs-art 537dfd9, "Tom FORS (check 354)": verify 354 permutations, and (keygen, mean sign) per
# tier. The page's rounded figures and times follow.
KECCAK_MODEL = {
    "Light": (1_908_763, 73_459.23681454461),
    "Standard": (244_318_221, 69_900.23681454461),
    "Full": (15_636_365_313, 92_204.23681454461),
}
PAGE = {  # the page's "One signer" Keccak figures: sign, keygen, sign time, keygen time
    "Light": ("74K", "1.91M", "13 s", "5.5 min"),
    "Standard": ("70K", "244M", "0.5 ms", "1.9 s"),
    "Full": ("92K", "15.6B", "0.2 ms", "31 s"),
}
PINNED = {  # plan; then per unit (tree_cost, keygen, mean sign): calls, permutations
    "Light": (
        Plan("level", 3, 1024),
        (2830, 1_851_419, 73_398.23681454461),
        (2886, 1_908_763, 73_459.23681454461),
    ),
    "Standard": (
        Plan("top", 5, 65_535),
        (7231, 236_978_189, 69_671.23681454461),
        (7455, 244_318_221, 69_900.23681454461),
    ),
    "Full": (
        Plan("top", 7, 1_048_575),
        (28_927, 15_166_603_265, 91_303.23681454461),
        (29_823, 15_636_365_313, 92_204.23681454461),
    ),
}
# The cover estimates at (h, b, a, k) = (26, b, 10, 24), which sweep_leansphincs_pruned.py's cover_lifetime gives too.
LIFETIME_ESTIMATE = {"Light": 242_283, "Standard": 23_797_924, "Full": 1_203_134_883}


def threshold_caches(b):
    """0 and 1 node, every threshold of the plan rule and its neighbours, and a large cache, in bytes."""
    thresholds = [0, 1, 2 ** (b + 1) - 1]
    for c in range(1, b + 1):
        thresholds += [2 ** (b - c + 1) - 1, 2 ** (b - c)]
    nodes = sorted({max(0, t + d) for t in thresholds for d in (-1, 0, 1)} | {2**40})
    return [x * N for x in nodes]


def check():
    failures = 0

    def expect(label, got, want):
        nonlocal failures
        ok = abs(got - want) < 1e-6 if isinstance(want, float) else got == want
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {label}: {got!r}" + ("" if ok else f" (want {want!r})"))

    expect("verify, keccak256 calls (the spec's 342)", verify_cost(CALLS), 342)
    expect("verify, Keccak-f permutations (the spec's 354, keccak_model.py)", verify_cost(PERMUTATIONS), 354)
    expect("digest: calls, permutations", (CALLS.digest, PERMUTATIONS.digest), (2, 2))
    encoding = (PERMUTATIONS.enc, PERMUTATIONS.enc_fixed, PERMUTATIONS.enc_try)
    expect("WOTS+C encoding, permutations: verifier, signer fixed part, per counter", encoding, (6, 5, 1))
    expect("WOTS leaf, calls", CALLS.leaf, 225)
    expect("WOTS leaf, permutations", PERMUTATIONS.leaf, 232)
    expect("FORS signing, calls", fors_sign_cost(CALLS), 61_392)
    expect("FORS signing, permutations", fors_sign_cost(PERMUTATIONS), 61_392)
    expect("WOTS+C mean tries", wots_c_tries(), 829.2368145446103)
    same = all(
        plan(b, cache, CALLS) == plan(b, cache, PERMUTATIONS) for b in range(H + 1) for cache in threshold_caches(b)
    )
    expect("calls and permutations choose the same plan (every b, every threshold)", same, True)
    for t in TIERS:
        p, calls, perms = PINNED[t.name]
        r = evaluate(t)
        expect(f"{t.name} plan", plan(t.b, t.cache_bytes), p)
        for u, (tree, keygen, sign) in ((CALLS, calls), (PERMUTATIONS, perms)):
            expect(f"{t.name} {u.name} tree_cost", r["tree_cost"][u.name], tree)
            expect(f"{t.name} {u.name} keygen", r["keygen"][u.name], keygen)
            expect(f"{t.name} {u.name} sign", r["sign"][u.name]["total"], sign)
        expect(f"{t.name} keygen formula, calls", r["keygen"]["calls"], 1 + 2**t.b * 226 + 2 * (H - t.b))
        expect(f"{t.name} keygen formula, permutations", r["keygen"]["permutations"], 1 + 2**t.b * 233 + 2 * (H - t.b))
        got = (r["keygen"]["permutations"], r["sign"]["permutations"]["total"])
        expect(f"{t.name} keccak_model.py (keygen, sign)", got, KECCAK_MODEL[t.name])
        got = (
            fmt_page_sign(r["sign"]["permutations"]["total"]),
            fmt(r["keygen"]["permutations"]),
            fmt_time(r["seconds"]["sign"]),
            fmt_time(r["seconds"]["keygen"]),
        )
        expect(f"{t.name} page figures", got, PAGE[t.name])
        lt = r["lifetime"]
        expect(f"{t.name} lifetime estimate", lt["estimate"], LIFETIME_ESTIMATE[t.name])
        expect(f"{t.name} proved lifetime (quoted)", lt["proved"], PROVED_LIFETIME[t.name])
        expect(f"{t.name} proved lifetime clears the cover estimate's level", lt["proved_ok"], True)
        within = PROOF_GAP[0] <= lt["gap"] <= PROOF_GAP[1]
        expect(f"{t.name} proved lifetime {lt['gap']:.1%} below the estimate (README: 4-17%)", within, True)
    expect("Full lifetime is at least 2^30", PROVED_LIFETIME["Full"] >= 2**30, True)
    gaps = [evaluate(t)["lifetime"]["gap"] for t in TIERS]
    expect("the proofs' gap shrinks as b grows (README: worse at small b)", gaps == sorted(gaps, reverse=True), True)
    print("all pinned figures match" if not failures else f"{failures} mismatch(es)")
    return failures == 0


def compare_sphincs_art(root):
    """Run root/scripts/keccak_model.py's fors(26, 24, 10, 120), "Tom FORS (check 354)" (it needs numpy and scipy),
    and compare."""
    sys.path.insert(0, str(Path(root).expanduser() / "scripts"))
    import keccak_model  # noqa: E402  (sphincs-art; imports sweep_leansphincs_pruned, numpy, scipy)

    verify, tiers = keccak_model.fors(H, K, A, T_SUM)
    failures = 0

    def expect(label, got, want):
        nonlocal failures
        ok = abs(got - want) < 1e-6
        failures += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {label}: model {got!r}, keccak_model.py {want!r}")

    expect("verify", verify_cost(PERMUTATIONS), verify)
    for t, name in zip(TIERS, ("ledger", "standard", "full")):
        keygen, _, sign, _ = tiers[name]
        r = evaluate(t, lifetime=False)
        expect(f"{t.name} keygen", r["keygen"]["permutations"], keygen)
        expect(f"{t.name} sign", r["sign"]["permutations"]["total"], sign)
        sweep = keccak_model.V
        expect(f"{t.name} lifetime estimate", cover_lifetime(t.b), sweep.cover_lifetime(H, t.b, A, K))
    print("keccak_model.py agrees" if not failures else f"{failures} mismatch(es)")
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
    ap.add_argument("--units", choices=["both", *UNITS], default="both", help="the table's units (default both)")
    ap.add_argument("--json", action="store_true", help="print one JSON object (both units)")
    ap.add_argument("--check", action="store_true", help="assert the pinned figures and exit")
    ap.add_argument(
        "--sphincs-art", type=Path, metavar="DIR", help="compare with DIR/scripts/keccak_model.py and exit"
    )
    args = ap.parse_args()

    if args.check:
        sys.exit(0 if check() else 1)
    if args.sphincs_art:
        sys.exit(0 if compare_sphincs_art(args.sphincs_art) else 1)
    if (args.b is None) != (args.cache_bytes is None):
        ap.error("--b and --cache-bytes go together")
    tiers = list(TIERS)
    if args.b is not None:
        if not 0 <= args.b <= H:
            ap.error(f"--b must be in [0, {H}]")
        tiers.append(Tier("Custom", "-", args.b, args.cache_bytes, 0.0))

    rows = [evaluate(t) for t in tiers]
    if args.json:
        doc = {
            "scheme": "leanSphincs",
            "hash": "keccak256",
            "units": UNIT_LABEL,
            "params": dict(h=H, a=A, k=K, v=V, w=W, T=T_SUM, n=N),
            "unit_costs": {u.name: {**u._asdict(), "wots_leaf": u.leaf} for u in (CALLS, PERMUTATIONS)},
            "verify": {u.name: verify_cost(u) for u in (CALLS, PERMUTATIONS)},
            "wots_c_mean_tries": wots_c_tries(),
            "lifetime_model": {"level_bits": LEVEL, "tiers": "proved in Lean (quoted)", "estimate": "cover, computed"},
            "tiers": rows,
        }
        print(json.dumps(doc, indent=1))
        return
    units = [CALLS, PERMUTATIONS] if args.units == "both" else [UNITS[args.units]]
    print("\n\n".join(table(rows, u, lifetime=u is units[-1]) for u in units))


if __name__ == "__main__":
    main()
