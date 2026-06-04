# Security analysis — C13 (FORS+C / WOTS+C) and SLH-DSA-SHA2-128-24

> Status: informal security argument, not a machine-checked proof. It records the
> few-time / subset-resilience accounting behind two review remediations
> (C13-X-f2 secret-keyed `R`; C13-X-f3 WOTS+C reuse) and documents the
> SLH-DSA-SHA2 usage budget (SLH-X-f2cap). Probabilistic bounds are order-of-
> magnitude (base-2 log) estimates in the random-oracle model for keccak256 /
> SHA-256; constants and lower-order terms are dropped. This is a research
> prototype — **not audited, not production-safe.**

C13 parameters: `n=128` (16-byte hashes), `h=22`, `d=2`, `subtree_h=11`,
`a=19`, `k=7`, `w=8`, `l=43`, `target_sum=208`, per-key signature cap `2^22`.

SLH-DSA-SHA2-128-24 parameters: `n=16`, `h=22`, `d=1`, `a=24`, `k=6`, `w=4`,
single XMSS tree of `2^22` leaves, named usage cap `2^24`.

---

## 1. Threat model and what the verifier checks

The on-chain verifier is the trust anchor. It is given `(pkSeed, pkRoot, message, sig)`
and recomputes `digest = H_msg(pkSeed, pkRoot, R, message)` from the randomizer
`R` carried *inside* the signature, then checks the FORS openings, the FORS+C
forced-zero, the WOTS+C target-sum, the WOTS chains, and the hypertree Merkle
climb to `pkRoot`.

Two facts drive the analysis:

- **A forger always controls `R`.** `R` is part of the signature, so when an
  adversary attempts a forgery they may pick any `R*` they like. No signer-side
  choice of `R` constrains a forger's `R*`. (This is why §2's fix is about the
  *honest* signer, not the forger.)
- **A forger must KNOW the revealed secrets.** A FORS/WOTS opening is only
  forgeable if the adversary already holds the secret hash-chain values at the
  required indices. Those can only come from secrets *revealed by honest
  signatures*. Few-time security is the statement that observing `q` honest
  signatures does not reveal enough to open a fresh target.

---

## 2. C13 message randomizer `R` — public-grindable → secret-keyed (review C13-X-f2)

### 2.1 The two attack avenues

For a FORS forgery on target `m*`, the adversary needs, for each of the
`k_eff` message-dependent FORS trees, the secret at index `md_i(pkSeed,R*,m*)`
in the FORS instance selected by `ht_idx(pkSeed,R*,m*)`.

**Avenue A — forger grinds its own `R*` (inherent, both models).**
The forger grinds `R*` so the target's indices land on already-revealed secrets.
This avenue exists no matter how the honest signer derives `R`; it is bounded by
the FORS parameters (§3) and gives the ~`2^133` figure of §2.3.

**Avenue B — adversary steers HONEST signatures (only if `R` is public).**
This is the dangerous one. If the map `m ↦ ht_idx(pkSeed,R(m),m)` is *publicly
computable*, a chosen-message adversary can:

1. Offline, evaluate `ht_idx(m)` for many candidate messages `m` and keep only
   those mapping to one **target FORS instance** `T`. Each candidate hits a
   chosen `T` with probability `2^-h = 2^-22`, so finding one costs `~2^22`
   hashes.
2. Request honest signatures on those colliding messages. Every such signature
   reveals `k` FORS secrets **in instance `T`**.

With the `2^22` signing budget concentrated onto a single instance, each of
`T`'s height-`a=19` FORS trees (`2^19` leaves) is *saturated* with reveals
(`2^22 ≫ 2^19`): the adversary learns essentially every secret of instance `T`.
A forgery on any message that maps to `T` then costs only the grind to land on
`T` with the forced-zero satisfied — `2^h · 2^a = 2^22 · 2^19 = 2^41` — which is
**catastrophically below 128 bits.**

The pre-fix C13 derived `R = mask_n(keccak("R_grind" ‖ nonce))`, ground over
`nonce` until the forced-zero predicate held. The preimage contains **no secret**,
so `ht_idx(m)` is fully public and Avenue B is open.

### 2.2 The fix: bind `R` to the secret seed

Post-fix (`signers/signer-wasm/src/fors.rs::grind_r`, `script/signer.py::grind_R_fors`):

```
R = mask_n(keccak256( sk_seed[32] ‖ "R_grind" ‖ message[32] ‖ nonce[32] ))
    grinding `nonce` until the FORS+C forced-zero predicate holds.
```

`sk_seed` is secret, so `m ↦ ht_idx(m)` is a **secret keyed function**: the
adversary cannot evaluate it offline and therefore cannot pre-select messages
that land on a target instance. Honest reveals are spread pseudo-randomly across
the `2^22` instances (`≈ 1` reveal per instance at the cap), closing Avenue B and
returning C13 to the standard secret-randomizer model. The derivation stays
**deterministic** per `(key, message)` (the nonce search is deterministic), so no
runtime randomness is required; it may optionally be hedged by folding fresh
`opt_rand` into the preimage.

The verifier is **unchanged** — it only reads `R` from the signature. The Rust
and Python signers use a byte-identical preimage so the cross-implementation
oracle (`signers/signer-wasm/tests/cross_validate.rs`) and the on-chain digest stay in
lock-step.

### 2.3 Residual bound (Avenue A, after the fix)

With reveals spread (`r ≈ 1` per instance at `q = 2^22`), a forger grinding its
own `R*`:

- must satisfy the FORS+C **forced-zero** on `md_{k-1}` — a `2^a = 2^19` factor;
- must hit, in the selected instance, the `k-1 = 6` message-dependent tree
  indices that coincide with the (≈ single) revealed index per tree —
  `(1/2^a)^{k-1} = 2^{-114}`.

Combined work `≈ 2^{19} · 2^{114} = 2^{133}`, i.e. **above the 128-bit target.**
The bound degrades with per-instance reuse `r` roughly as `2^{155 − 6·log2 r}`;
keeping `q ≤ 2^22` with spread reveals keeps `r` small. (See ePrint 2025/2203 for
the FORS+C subset-resilience treatment this mirrors.)

**Conclusion.** C13's forgery resistance is `≥ 2^133` in the secret-randomizer
model restored by the fix. The fix does not change Avenue A (inherent), but it
eliminates Avenue B (the `~2^41` chosen-message concentration break that public
`R` admitted).

---

## 3. FORS+C forced-zero — effective `k = 6` (review C13-X-f1, not a defect)

C13 forces the last (`k-1 = 6`) FORS tree's index to `0` by grinding `R`, and the
verifier reveals that tree's leaf-0 root directly (saving one auth path, shrinking
the signature). Consequently the forced-zero tree carries **no message-dependent
index entropy**: an adversary "always has" index 0 of tree 6.

The effective few-time strength is therefore carried by `k_eff = k − 1 = 6`
message-dependent trees of height `a = 19`, i.e. `a·(k−1) = 114` bits of FORS
subset-resilience, *plus* the `2^a = 2^19` forced-zero grind a forger must also
pay (§2.3), for the `2^133` total. This reduction from `a·k = 133` to `a·(k−1)`
is an **intended property** of the +C construction, not a flaw — but it must
appear explicitly in the proven bound, which §2.3 does.

---

## 4. WOTS+C target-sum reuse under `ht_idx` collisions (review C13-X-f3)

### 4.1 Why bottom-layer WOTS keys are reused

The layer-0 WOTS keypair is keyed by `(layer=0, tree=idxTree, kp=idxLeaf)`
derived from the 22-bit `ht_idx`. With a `q = 2^22` signing budget over `2^22`
leaves, **`ht_idx` collisions are expected** — by the birthday bound, roughly
`q^2 / 2^{23} ≈ 2^{21}` colliding pairs. Each collision between two messages with
distinct `fors_pk` means one layer-0 WOTS keypair signs two different WOTS
messages: a textbook WOTS one-time-use violation. This is inherent to all
SPHINCS+/SLH-DSA bottom layers and is absorbed by the FORS few-time layer, not
prevented by WOTS.

### 4.2 What target-sum WOTS+C changes, and why single-use forgery is still blocked

WOTS+C replaces the classic monotone checksum with a fixed digit-sum constraint:
the verifier rejects unless the 43 base-8 digits of the WOTS message digest sum to
exactly `target_sum = 208`. Forward-only forgery from a *single* signature is
still blocked: revealing a chain at digit `d[i]` lets a forger only advance to
digits `≥ d[i]`; any alternative vector `d'` with `d'[i] ≥ d[i] ∀i` and
`Σd' = 208 = Σd` forces `d' = d` (you cannot increase one digit without
decreasing another, which would require walking a chain backwards).

### 4.3 The multi-reuse (min-combination) residual, and the gating argument

Under a `ht_idx` collision, two reused signatures reveal each of the 43 chains
down to the per-signature minimum `min(d1[i], d2[i])`. A min-combination forgery
would need a third vector `d3` with `d3[i] ≥ min(d1[i],d2[i]) ∀i` and `Σd3 = 208`.
**Crucially, the WOTS message is itself `fors_pk`** (the layer-0 node the WOTS
keypair signs). So to mount this the adversary must exhibit a *third distinct
`fors_pk'`* that (a) hashes (with an attacker-chosen `count`) to such a `d3`, and
(b) is a `fors_pk'` they can actually open — i.e. for which they hold the FORS
secrets. Producing an openable `fors_pk'` of their choice is exactly a FORS
forgery.

**Gating conclusion.** A WOTS+C reuse forgery at layer 0 is therefore *gated by*
FORS few-time security on the same `ht_idx` instance: it cannot succeed unless the
adversary can already forge the FORS opening, which §2–§3 bound at `≥ 2^133` once
`R` is secret-keyed (no instance concentration). WOTS one-time-ness is **not** the
load-bearing property; the FORS term is. The target-sum-specific min-combination
probability for `w=8, l=43, T=208` against `r` reuses is the residual that the
ePrint 2025/2203 analysis must carry; we do not re-derive it here, and we add an
empirical guard (§4.4).

### 4.4 Regression guard

`signers/signer-wasm/tests/wots_reuse_poc.rs` constructs two messages colliding on
`ht_idx` with distinct `fors_pk`, harvests the WOTS chains both reveal, and
asserts that the union of revealed chain values does **not** admit a valid
WOTS+C opening (`Σ digits == 208`, every digit reachable) for a third, distinct
`fors_pk` target. It is a guard against a regression that would make the layer-0
WOTS keypair forgeable from reuse *independently* of FORS — it does not replace
the analytic bound.

---

## 5. SLH-DSA-SHA2-128-24 — external mode and the `2^22` leaf budget

### 5.1 External FIPS 205 (review SLH-X-f1)

The verifier implements **FIPS 205 external `SLH-DSA.Verify` with an empty
context**: the message is wrapped as `M' = toByte(0,1) ‖ toByte(|ctx|,1) ‖ ctx ‖ M`
= `0x00 ‖ 0x00 ‖ M` before `H_msg` (FIPS 205 Algorithm 24). This matches published
NIST/ACVP *external* known-answer vectors. The C reference (`slh_sign_internal`)
and the Python signer apply the same envelope by prepending `0x00 0x00`; the
on-chain verifier prepends it internally before the inner SHA-256
(`R ‖ seed ‖ root ‖ 0x00 ‖ 0x00 ‖ M`, 82 bytes).

### 5.2 The signature budget (review SLH-X-f2cap)

With `h=22, d=1` the hypertree is a single XMSS tree of `2^22` one-time WOTS
leaves, and the signing leaf `leafIdx` is chosen *pseudo-randomly* from the
message digest. Therefore:

- WOTS-leaf collisions appear by the birthday bound — onset `~2^{11}` signatures,
  not at the named `2^24` cap;
- by `2^24` signatures, leaves have been reused `~4×` on average (`2^24 / 2^22`);
- this is **expected and tolerated**: a leaf collision is not itself a WOTS
  forgery, and the FORS few-time layer (`a=24, k=6`) absorbs the reuse.

So "2^24" is a recommended **per-key usage cap**, not a flat one-time-WOTS
security guarantee, and the 128-bit level across the window is carried by the FORS
margin. Operators bounding risk should treat the per-key budget as a function of
the acceptable WOTS-reuse / FORS-collision probability (birthday over `2^22`),
not as a hard `2^24` security cliff. This differs from C7/C13, whose `2^24`/`2^22`
figures *are* the actual hypertree-leaf counts at full one-time-WOTS security.

---

## 6. Summary

| Property | Bound / status | Basis |
|---|---|---|
| C13 forgery, secret-keyed `R`, `q ≤ 2^22` | `≥ 2^133` work | §2.3 (FORS+C, forger-controlled `R*`) |
| C13 chosen-message concentration (public `R`) | `~2^41` — **closed by the fix** | §2.1 Avenue B |
| C13 FORS+C effective few-time | `k_eff = 6`, `a·(k−1)=114` + `2^19` forced-zero | §3 |
| C13 WOTS+C layer-0 reuse | gated by FORS (`≥2^133`); residual min-combination per ePrint 2025/2203 | §4 |
| SLH-DSA-SHA2 conformance | FIPS 205 external (empty ctx), ACVP external KATs | §5.1 |
| SLH-DSA-SHA2 budget | `2^22` leaf space, FORS-absorbed; `2^24` = usage cap | §5.2 |

**What is proven vs assumed.** The forced-zero / target-sum structural facts and
the gating argument (§4.3) are deterministic and verifier-checked. The
probabilistic forgery bounds (§2.3, §4) are random-oracle estimates that inherit
the FORS+C subset-resilience analysis of ePrint 2025/2203; they are documented
here, not machine-checked. The `verity/` Lean model covers the keccak
collision-resistance axioms and Merkle-kernel compilation correctness, not these
probabilistic few-time bounds.
