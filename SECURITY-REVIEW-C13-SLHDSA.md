# Agent-Assisted Security Review — SPHINCs- C13 & SLH-DSA-SHA2-128-24

> **What this is (and is not):** this review was produced with AI-agent assistance
> (automated source reading plus adversarial verification passes), driven and checked
> by the maintainer. It is **not an independent professional security audit** and
> confers no audit-grade assurance. Treat it as a best-effort engineering review.

**Scope:** Two cryptographic families, signer side and on-chain verifier side.
1. **C13** — custom lightweight SPHINCS+ "+C" variant (ePrint 2025/2203 family), FIPS 205 §4.2 uncompressed 32-byte ADRS + keccak256. Verifier `src/SPHINCs-C13Asm.sol`; signers `signer-wasm/` (Rust), `script/signer.py`.
2. **SLH-DSA-SHA2-128-24** — NIST SP 800-230 IPD parameter set, claimed FIPS 205 bit-exact. Verifier `src/SLH-DSA-SHA2-128-24verifier.sol`; reference oracle `signers/sphincsplus-128-24/` (C), `script/slh_dsa_sha2_128_24_*signer.py`.

Out of scope and **not examined**: SLH-DSA-Keccak twin, slhvk Vulkan GPU signer, C7/C9/C11/C12, legacy verifiers.

**Status of the project itself:** research prototype, **not audited, not production-safe** (per repo README). This report is consistent with that posture.

---

## 1. Executive Summary

No forgery, key-recovery, false-accept, or accept-invalid vulnerability was found in either family. Every confirmed finding is one of: a security-*model* / documentation gap (the design is sound but the claimed guarantee is stated more strongly than what is proven in-repo), a robustness / fail-closed inconsistency, a test-oracle / CI-assurance gap, or a maintainability hazard. The two verifiers are byte-exact with their own signers on the happy path, and the cryptographic cores (digest parsing, ADRS packing, FORS/WOTS/Merkle climbs) reconcile against the parameterized signer expressions.

The single most important substantive item is **C13-cross-f2 (high → reconciled medium): C13's message randomizer `R` is fully public-grindable with no secret/message binding**, which silently moves C13 into the strictly stronger "adversary controls the index-mapping randomizer" security model. The best known resulting forgery is ~2^133 work — above the 128-bit design target — so it is not a practical break, but the few-time bound must be *proven in that model* and the public-grindability *documented*. The second-most-important class is the absence of any automated NIST/ACVP KAT or cross-implementation byte-exactness check in CI for the SLH "FIPS 205 bit-exact" claim — that claim is currently only ever validated as signer-vs-verifier *mutual* consistency.

### Overall risk posture

| Family | Verifier core | Signer | Parity | Crypto model | Test/CI assurance |
|---|---|---|---|---|---|
| **C13** | Sound; no false-accept path. Fail-closed gaps + magic-number fragility. | Sound; bounded grinds, returns `Err` on exhaustion. | Rust↔Python unit oracle is **broken/stale** (does not compile; fixture mismatched). | **Public-grindable R** moves to a stronger model; few-time bound unproven in-repo. No external spec — correctness = byte-exact agreement. | Full-param crosscheck never run in CI; `#[ignore]`d. |
| **SLH-DSA-SHA2-128-24** | Sound; canonical-key guard present (better than C13). Latent 4-byte/1-byte ADRSc field-width divergence (harmless at these params). | Pure-Python CLI diverges from C reference for non-32-byte messages. | C reference is the ground truth; signer/verifier mutually consistent at 32-byte messages. | "FIPS 205 bit-exact" is true for `slh_*_internal` only (no external context envelope); advertised 2^24 cap looser than the real 2^22 leaf budget. | Hedged-by-default forge test = no reproducible KAT; crosscheck.py is manual, no `.github/workflows` exists. |

**Honesty note on method:** All verifier line/citation facts, signer source claims, and the account-integration revert paths in this report were verified by reading source. The numeric crypto bounds (~2^133 forgery, ~2^21 ht_idx collisions at the 2^22 cap, grind trial counts) were reasoned statically. The full-parameter cross-implementation byte-exactness oracles (`c13-crosscheck`, `sphincsplus-128-24/crosscheck.py`), the `#[ignore]`d full-height tests, and external NIST/ACVP KAT vectors were **not executed** in this pass.

---

## 2. Findings Table (sorted by severity)

Severities are the **reconciled** severity after applying the adversarial verifier verdicts (code-reality / spec-conformance / exploitability lenses). Where the exploitability lens downgraded a finding, the lower severity is taken and the original is noted in the detail.

| ID | Severity | Component | Title | One-line impact |
|---|---|---|---|---|
| **C13-X-f2** | **Medium** (orig. high) | cross | Message randomizer `R` is fully public-grindable, no secret/message binding | C13 silently adopts the stronger "adversary controls the index-map randomizer" model; few-time bound unproven there (best forgery ~2^133, no practical break) |
| **SLH-X-f1** | **Medium** | SLH-verifier / cross | "FIPS 205 bit-exact" is only `slh_*_internal`; no external context envelope | Pure NIST/ACVP *external* KATs fail; only interoperates with its own signer |
| **SLH-X-f2cap** | **Medium** | cross | Advertised 2^24 cap is looser than the true 2^22 single-XMSS-tree budget | Operator over-signs past safe budget; docs overstate flat-128-bit by ~4× (spec-conformance lens calls the cap *correct* by design — see detail) |
| **C13-S-f1** | **Medium** | C13-signer | Rust↔Python parity oracle `cross_validate.rs` does not compile | Documented `cargo test --release` aborts; the cross-impl regression guard is dead |
| **C13-S-f2** | **Medium** | C13-signer | Stale pinned `PY_FORS_SECRET_0_0` no longer matches ht_idx-folding `fors_secret` | Even after the compile fix the FORS-PRF parity assertion is wrong/vacuous |
| **C13-X-f3** | **Medium** | cross | Target-sum WOTS+C multi-reuse (min-combination) resistance is load-bearing and unproven | At the 2^22 cap ~2^21 layer-0 WOTS keypairs sign ≥2 distinct `fors_pk`; the property carrying that is unproven for w=8,l=43,T=208 |
| **SLH-S-f1** | **Low** (orig. medium) | SLH-signer | Pure-Python signer zero-pads message to 32B; C/fast signer signs raw bytes | The two signers disagree for any non-32-byte message (off-chain only; bytes32 verifier unaffected) |
| **C13-V-f1 / C13-acc-f2** | **Low** | C13-verifier | No canonical-form check on pkSeed/pkRoot (inconsistent with SLH) | Non-canonical key silently *bricks* the account; fail-closed, no false-accept |
| **C13-mal-f1** | **Low** | C13-verifier | Signature elements not canonicalized → byte-string malleability | Many distinct 3688-B strings verify identically; only matters if a consumer keys on raw sig bytes |
| **SLH-V-f2 / SLH-mal-f6** | **Low** | SLH-verifier | Fixed bytes32 message, no length binding / FIPS envelope / domain sep | Only exactly-32-byte messages round-trip; domain separation is the caller's job |
| **SLH-S-f3** | **Low** | SLH-signer | Fast-wrapper disk cache key omits C-binary params/identity | Stale cached fixture can silently desync from verifier in deterministic mode |
| **SLH-X-f5 / SLH-X-f4** | **Low** | cross | Hedged-by-default forge test; no reproducible FIPS KAT in CI | Symmetric signer+verifier co-drift away from FIPS would not be caught automatically |
| **C13-acc-g1** | **Low** | cross | `SphincsAccount._validateSignature` reverts (not `SIG_VALIDATION_FAILED`) on malformed outer/ECDSA sig | EntryPoint `AA23` bundle-level revert instead of graceful per-op drop (conditional on non-compliant bundler) |
| **C13-mal-f1-erc4337** | **Low** | cross | ERC-4337 userOp.signature malleable at ABI-wrapper; sig not in userOpHash | No replay/forgery (nonce anchors); only matters if a bundler/indexer keys on sig bytes |
| **C13-evm-f1** | **Low** | C13-verifier | `assembly("memory-safe")` annotation is unsound (clobbers FMP/zero-slot, writes high mem) | Latent: a future normal-exit edit would let the optimizer use a corrupted FMP. Today only sound by virtue of unconditional return/revert |
| **C13-evm-f2 / C13-frame-f2** | **Low** | cross | Frame account turns verifier `revert(0,0)` into `"verify call failed"` | Misleading error surface for forced-zero/target-sum rejections; still rejected |
| **C13-V-f4 / C13-S-f3 / C13-mal-f2(A=19)** | **Info** | C13-verifier | Verifier hardcodes digest-shift/mask/fold literals (133/114/19/18/0x3FFFFF/0x7FFFF) instead of deriving from K/A/H | Silent signer/verifier desync under any reparameterization; no live bug at A=19,K=7,H=22 |
| **C13-V-f2** | **Info** | C13-verifier | Forced-zero / target-sum failures `revert(0,0)` with no reason | Three distinct failure modes (string-revert / empty-revert / return-false); diagnosability only |
| **C13-V-f3** | **Info** | C13-verifier | Stale/misleading comments on forced-zero bit range and ht_shift derivation | `// bits 114..132` and `sphincs.rs // 128` are wrong; code is correct. Future-edit hazard |
| **SLH-V-f3 / SLH-mal-f3** | **Info** | SLH-verifier / cross | ADRSc chain/hash/tree_height written as 4-byte fields vs C reference's single bytes | Byte-identical only because every value <256 at these params; latent reparam divergence |
| **SLH-V-f4** | **Info** | SLH-verifier | Diagnostic contract hardcodes `globalY := parentIdx` (correct only for FORS t=0) | Debug-only, not deployed; copy-paste hazard if reused as a multi-tree template |
| **SLH-evm-f6** | **Info** | SLH-verifier | T_l final packed-element write spills 16 zero bytes to [0x496,0x4A6) | Harmless (10-byte gap + output overwrite); margin depends on l=68,n=16 |
| **C13-X-f1 (FORS+C 114-bit)** | **Info / not-a-defect** | C13 | FORS+C forced-zero tree carries no secret entropy → effective FTS strength a·(k−1)=114 | code-reality real; spec & exploitability refuted — by design, factor into the proven bound |

---

## 3. Detailed Findings

Duplicates that arose across analysis dimensions from the same root cause are merged below. Where the three lenses disagreed on severity, the reconciliation is stated.

---

### C13-X-f2 — Message randomizer `R` is fully public-grindable, with no secret and no message/key binding *(Medium — reconciled down from High)*

**Location:** `signer-wasm/src/fors.rs:61-79` (`grind_r`); `script/signer.py:541-550`; `src/SPHINCs-C13Asm.sol:52-60, 75-83`.

**What's wrong.** `R` is derived as `R = mask_n(keccak256("R_grind" ‖ u256(nonce)))`, scanning `nonce` upward until the digest satisfies the FORS+C forced-zero predicate (`(digest >> 114) & a_mask == 0`). It contains **no secret key material** and is **not a PRF of the message or sk_seed**. In standard SLH-DSA / SP 800-230, `R = PRF_msg(sk_prf, opt_rand, M)` is secret-keyed precisely so an adversary cannot offline-search for a (message, randomizer) whose FORS indices and hypertree leaf land on previously-revealed leaves. Here the entire FORS index map `md[0..5]`, the forced-zero `md[6]`, and the hypertree-leaf selector `ht_idx` are all functions of `digest = H_msg(pkSeed, pkRoot, R, M)` over public inputs and an attacker-computable `R`.

**Evidence.** `fors.rs grind_r` builds `r_input = b"R_grind" ‖ to_bytes32(u256(nonce))`, sets `r = mask_n(keccak256(&r_input))`, called from `sphincs.rs:13` as `grind_r(seed, pk_root, message)` — `sk_seed` is **not** passed. `signer.py:545` is byte-identical. The verifier (`src/SPHINCs-C13Asm.sol:52-60`, confirmed by source read) recomputes the identical `digest = keccak256(seed ‖ root ‖ R ‖ message ‖ 0xFF..FF)` from the public `(seed, root, R, message)`, so a forger can evaluate `digest` for arbitrarily many `(M*, R)` offline and select one whose `(ht_idx, md[0..5])` hit already-revealed `(instance, leaf)` pairs.

**Impact.** This is the SPHINCS+ interleaved/weighted subset-resilience attack run with the index map fully exposed and offline. Quantified: after `q` observed signatures the cheapest offline forgery is ~`2^(a + (h−log q) + a·(k−1))` H_msg ≈ **2^133 at q=2^22** (single reveals), dropping with instance reuse `r` as ~`2^(155 − 6·log2 r)`. The work stays above 2^100 at C13 params, so it is **not a practical key/forgery break today** — which is why the exploitability lens rated it *low* and the spec lens *medium*. It nonetheless removes the anti-grinding / hedging guarantee a secret-keyed `R` provides and changes the model in which the few-time bound must be proven. **Reconciled severity: medium** (model + documentation gap; the headline "high" overstated a non-practical attack, while "low" understated the model change).

**Fix.** Either (a) key `R` with a secret PRF as in SLH-DSA — `R = mask_n(keccak(sk_prf ‖ opt_rand ‖ M))` — and continue grinding the forced-zero predicate via a secret-dependent nonce, restoring the secret-randomizer model; or (b) explicitly state that C13 is analyzed in the stronger "adversary controls the index-mapping randomizer" model and prove the few-time / subset-resilience bound there (it appears to hold at ~2^133, but it must be the *proven* bound, not the secret-`R` one). At minimum, document that `R` is public-grindable and that the proof is the offline-grinding variant.

---

### C13-X-f3 — Target-sum WOTS+C multi-reuse (min-combination) resistance is load-bearing and unproven *(Medium)*

**Location:** `src/SPHINCs-C13Asm.sol:151-200` (layer loop), `:168-173` (`sum==208` is the only structural WOTS check); `signer-wasm/src/wots.rs:38-49,75-88`.

**What's wrong.** WOTS+C replaces the classic monotone checksum with a fixed digit-sum constraint: the verifier reverts unless the 43 base-8 digits sum to exactly 208. The layer-0 WOTS keypair is keyed only by the hypertree leaf `(layer=0, tree=idxTree, kp=idxLeaf)` derived from `ht_idx` (22 bits). Because `ht_idx` is a hash-derived selector over 2^22 leaves, at the advertised q=2^22 cap birthday collisions are *expected* (~q²/2²³ ≈ 2²¹ colliding pairs). Each `ht_idx` collision between two messages with different `fors_pk` means the **same** layer-0 WOTS keypair signs two different WOTS-message digests — a WOTS one-time-use violation by design, absorbed only by the FORS few-time layer plus the target-sum's forgery resistance *under reuse*.

**Evidence.** Verifier `:160` `count := shr(224, calldataload(...))` — `count` is read from the signature, i.e. attacker-controlled on a forgery. `:166` `d := keccak256(... currentNode ... count ...)`. `:168-173`: the only structural check is `digitSum == 208`; there is no per-chain monotone constraint preventing a digit vector that dominates the per-chain minima of two reused signatures. `wots.rs` sign reveals `chain_hash(..., start=0, steps=digits[i])`, so a lower digit reveals more of the chain; two reuses reveal each chain down to the per-signature minimum. Forward-only forgery from a *single* signature is correctly blocked (any `d'` with `d'[i] ≥ d[i]` and `Σd' = 208` forces `d' = d`).

**Impact.** Whether a min-combination forgery (a third vector `d3` with `d3[i] ≥ min(d1[i], d2[i])` and `Σd3 = 208`, with `count` attacker-suppliable and `fors_pk'` grindable) is infeasible rests on the **unproven-in-repo** reuse resistance of target-sum WOTS at these params. The exploitability lens rated this *low/uncertain* (bottom-layer WOTS reuse is inherent to all SPHINCS+ and is normally absorbed by parameter sizing; no concrete forgery is constructible without *also* breaking the FORS few-time bound). The spec lens rated it *medium* as a genuine gap in the security argument. **Reconciled: medium** as an assurance gap, with the explicit caveat that no exploit exists.

**Fix.** Document and prove that C13's few-time security under expected `ht_idx` reuse at the 2^22 cap is carried by the FORS subset-resilience term (with effective k=6 per the forced-zero tree), not by WOTS one-time-ness, and bound the target-sum WOTS multi-reuse min-combination forgery probability explicitly for w=8, l=43, T=208 against `r` reuses. Alternatively bind `count` into the FORS/hypertree input so a forged `(count, fors_pk')` cannot be freely chosen. Add a regression test that exercises two messages colliding on `ht_idx` with distinct `fors_pk` and asserts no third valid WOTS+C opening can be assembled from the revealed chains.

---

### C13-S-f1 — Rust↔Python parity oracle does not compile *(Medium)*

**Location:** `signer-wasm/tests/cross_validate.rs:52` (call site); `signer-wasm/src/fors.rs:12`.

**What's wrong.** `fors::fors_secret` gained a 4th mandatory parameter `ht_idx: u32` (`fors.rs:12`: `pub fn fors_secret(sk_seed, tree_idx, leaf_idx, ht_idx)`), but the test still calls it with 3 arguments: `let fs = fors::fors_secret(sk_seed, 0, 0);`. This is a hard `E0061` compile error in the `cross_validate` test binary, which aborts the whole binary before *any* of its tests run (`test_key_derivation_matches_python`, `test_wots_secret_matches_python`, `test_fors_secret_matches_python`, `test_params`).

**Evidence (empirically run).** `cd signer-wasm && cargo test --release` produced `error[E0061]: this function takes 4 arguments but 3 arguments were supplied --> tests/cross_validate.rs:52:14` and `could not compile sphincs-c13-signer (test "cross_validate")`. The sibling binary `fors_leaf_keying` compiles and its test passes, so the failure is localized. `CLAUDE.md` and `README.md` advertise `cargo test --release -- --ignored` ("9/9") as *the* signer test — that command currently cannot compile.

**Impact.** Robustness / oracle-integrity, no on-chain exploit. The cross-implementation regression guard meant to catch a Rust↔Python↔verifier byte-level desync is dead. The production signing path was independently confirmed consistent, and the security-critical per-message FORS leaf-keying fix is still covered by the separate `fors_leaf_keying.rs` binary — so the exploitability lens rated this *low*. **Reconciled: medium** as the documented test command is broken and the unit-level cross-language guard is gone (spec lens *low*, code-reality *medium*).

**Fix.** Update the call site to pass `ht_idx`, e.g. `fors::fors_secret(sk_seed, 0, 0, 0)`, regenerate the pinned reference value (see C13-S-f2), and add the compile to CI.

---

### C13-S-f2 — Stale pinned `PY_FORS_SECRET_0_0` no longer matches `fors_secret` *(Medium)*

**Location:** `signer-wasm/tests/cross_validate.rs:26, 50-54`; `signer-wasm/src/fors.rs:12-20`.

**What's wrong.** Even after the trivial compile fix in C13-S-f1, the FORS-secret parity assertion is wrong. The fixture `PY_FORS_SECRET_0_0 = 0x644806f5...862` was generated from the **legacy** preimage `sk_seed ‖ "fors" ‖ tree_idx(4) ‖ leaf_idx(4)` (no `ht_idx`). The current Rust `fors_secret` has **no** `ht_idx=None` path — it *always* folds `ht_idx`: preimage = `sk_seed ‖ "fors" ‖ ht_idx(4) ‖ tree_idx(4) ‖ leaf_idx(4)`. So `fors_secret(sk,0,0,ht)` can never reproduce the pinned value.

**Evidence (empirically reproduced).** Against test entropy `[0x42;32]` (`sk_seed = keccak("sk_seed" ‖ entropy)`): Python `fors_secret(sk,0,0)` (no ht) = `0x644806f5...862` == fixture (True); Python `fors_secret(sk,0,0,0)` (ht=0, the C13 form) = `0xf3c46060...8239` ≠ fixture (False). Rust always uses the ht form. The Python signer still has the legacy no-ht default (`signer.py:229-240`, `ht_idx=None`) which produces the fixture, but C13 production always passes `ht_idx` (`fors_bind_leaf=True`). The fixture therefore pins a value no production C13 call ever computes.

**Impact.** Oracle-integrity only. If restored naively the assertion fails; if the fixture is blindly bumped to whatever Rust outputs, the cross-impl check becomes vacuous (Rust-vs-Rust). Either way the Rust↔Python guard for the security-critical FORS-instance-keying PRF is gone. Exploitability lens: *low* (confined to the test file). **Reconciled: medium** for the same reason as C13-S-f1.

**Fix.** Regenerate `PY_FORS_SECRET_0_0` from the Python signer using the C13 preimage (`fors_secret(sk_seed, 0, 0, ht_idx=0)` → `0xf3c46060...`), update the call site to pass the same `ht_idx`, and add a comment noting the value folds `ht_idx`.

---

### SLH-X-f1 — "FIPS 205 bit-exact" is true only for `slh_*_internal`; external context envelope is absent *(Medium)*

**Location:** `src/SLH-DSA-SHA2-128-24verifier.sol:67-92` (Hmsg over `R‖seed‖root‖M`, no envelope); `signers/sphincsplus-128-24/sign.c:95-148` (`crypto_sign_signature` = `slh_sign_internal`), `main.c:184`.

**What's wrong.** The contract docstring (line 5: "Bit-exact NIST compliance using FIPS 205") and `CLAUDE.md` advertise FIPS 205 bit-exactness. FIPS 205 §10.2 / Algorithm 22–24 (the external "pure" `SLH-DSA.Sign`/`.Verify`) require wrapping the message before hashing: `M' = toByte(0,1) ‖ toByte(|ctx|,1) ‖ ctx ‖ M`. Only `slh_*_internal` (Alg 19/20) hash `M` directly. The verifier computes `inner = SHA-256(R ‖ seed ‖ root ‖ M)` over the raw 32-byte message (lines 79-83, input region `0x00..0x50` = 80 bytes) with **no** `0x00 ‖ len(ctx) ‖ ctx` prefix; the C oracle drives `crypto_sign_signature` (= internal), which likewise omits the envelope.

**Evidence.** Verifier inner-hash input is exactly `R(0x00) ‖ seed(0x10) ‖ root(0x20) ‖ M(0x30)` (80 bytes); an empty-ctx envelope would add ≥2 leading bytes (`0x00 0x00`). The C ref signs `m` unmodified. Signer and verifier are therefore mutually consistent (the end-to-end forge test passes) but neither matches FIPS 205 external/ACVP "pure" KAT vectors — they would match only ACVP *internal* vectors. (Spec lens caveat: the internal-KAT *positive* match is asserted structurally, not executed.)

**Impact.** Robustness / interop, not a forgery. Anyone validating against published NIST/ACVP *external* KATs sees every vector fail; a third-party FIPS-205-conformant signer applying the standard empty-context envelope (`0x00 0x00 ‖ M`) produces signatures this verifier rejects. The exploitability lens rated this *low* (no forgery, mutually consistent). **Reconciled: medium** — the documentation claim is materially overstated and interop is broken (code-reality and spec lenses *medium*).

**Fix.** Either (a) prepend the FIPS 205 envelope `toByte(0,1) ‖ toByte(|ctx|,1) ‖ ctx` (empty ctx = `0x00 0x00`) before the inner SHA-256, and have the C reference call external `crypto_sign`; or (b) downgrade the documentation to state explicitly that this implements `slh_*_internal` (matches ACVP *internal* KATs only), not external `SLH-DSA.Sign`/`.Verify`.

---

### SLH-X-f2cap — Advertised 2^24 signature cap is looser than the true 2^22 single-XMSS-tree budget *(Medium — contested; see reconciliation)*

**Location:** `README.md:36,52,67`; `src/SLH-DSA-SHA2-128-24verifier.sol:7,113`; `signers/sphincsplus-128-24/params.h:16-20`.

**What's wrong (as filed).** With `SPX_FULL_HEIGHT=22`, `SPX_D=1`, there is a single XMSS tree of 2^22 one-time WOTS leaves; the signing leaf is `leafIdx = (dWord >> 88) & 0x3FFFFF`, a 22-bit *pseudorandom* (not counter) index. The README claims "flat 128-bit up to the 2²⁴ hard cap" and a "Signature-count cap | 2²⁴" table for the SLH rows. The binding budget is the 2^22 leaf space: by the birthday bound, WOTS-leaf collisions begin around 2^11 signatures.

**Evidence.** `params.h:17` `SPX_FULL_HEIGHT 22`, `:18 SPX_D 1`; verifier `:113` `leafIdx := and(shr(88, dWord), 0x3FFFFF)` (22-bit); `hash_sha2.c:194-195` masks `leaf_idx` to `SPX_LEAF_BITS=22` — pseudorandom, not sequential.

**Reconciliation — this finding is contested.** The spec-conformance lens **refuted** it: the "2^24 / flat-128-bit" claim is the *design-intended* SP 800-230 statement for this parameter set; pseudorandom WOTS-leaf collisions are *expected and tolerated* by the SLH-DSA security proof (FORS is the few-time mechanism that absorbs them), and a leaf collision is **not** by itself a WOTS forgery. The code-reality and exploitability lenses rated it **low** and flagged the original "forgery essentially certain before 2^22 / reuse begins at 2^11" narrative as overstated — it conflates collision *onset* with *catastrophe*. **Net:** the *security* is fine and as-designed; the documentation/security-accounting is the only real issue (the table cites 2^24 as a flat-security cap without a birthday/FORS caveat). Treat as a **documentation fix**, not a code defect.

**Fix.** State that WOTS one-time-ness is statistical over the 2^22 leaf space (collision risk grows by the birthday bound) and is distinct from the FORS few-time bound that absorbs collisions; give the recommended per-key signing budget with the collision-probability formula rather than citing "2^24 hard cap" as a flat-security guarantee.

---

### SLH-S-f1 — Pure-Python signer zero-pads message to 32 bytes; C/fast signer signs raw bytes *(Low — reconciled down from Medium)*

**Location:** `script/slh_dsa_sha2_128_24_signer.py:501-503` vs `signers/sphincsplus-128-24/main.c:148-184`, `script/slh_dsa_sha2_128_24_fast_signer.py:99-129`.

**What's wrong.** The pure-Python CLI forces the message to 32 bytes (`bytes.fromhex(msg_hex).rjust(32, b'\x00')[-32:]`), while the C reference (the bit-exactness ground truth) signs the raw decoded bytes of arbitrary length, and the Solidity verifier always hashes a fixed `bytes32`. All three agree only at exactly 32 bytes.

**Evidence.** Python `:501-503` left-pads then truncates. C `main.c:148` `msg_len = msg_hex_len/2`, `:184` `crypto_sign_signature(sig,&siglen,msg,msg_len,sk)` signs raw bytes; `hash_message` folds full `mlen` into the inner SHA-256. The fast wrapper passes `msg_hex` through raw.

**Impact.** Off-chain robustness/interop, not a forgery. The on-chain verifier is bytes32-only, so production (which always uses 32-byte messages) is unaffected. **Reconciliation:** all three lenses agreed *low* (one slow dev helper diverging from the FIPS-correct C path; no security impact). Spec lens additionally notes the *fault* is in the Python CLI deviating from FIPS, not the C path "diverging." **Reconciled: low.**

**Fix.** Make the pure-Python CLI sign raw bytes (drop the rjust/truncate) to match the C reference and FIPS, or document the 32-byte-only contract and have the C/fast wrapper reject `msg_len != 32`. Add a crosscheck vector with a non-32-byte message.

---

### C13-V-f1 / C13-acc-f2 — No canonical-form check on pkSeed/pkRoot *(Low)*

**Location:** `src/SPHINCs-C13Asm.sol:47-48, 53, 226`; contrast `src/SLH-DSA-SHA2-128-24verifier.sol:55-61`.

**What's wrong.** C13 never checks that `pkSeed`/`pkRoot` are canonical (low 128 bits zero). It uses `seed := pkSeed` / `root := pkRoot` verbatim (lines 47-48, **confirmed by source read** — the prologue jumps straight from the length gate to `seed := pkSeed`), feeds the full 32 bytes into H_msg, and compares `valid := eq(currentNode, root)` (line 226) against an unmasked `pkRoot`. The sibling SLH verifier rejects non-canonical keys (lines 55-61, **confirmed present**).

**Evidence.** `currentNode` is always `and(keccak256(...), N_MASK)`, so its low 128 bits are always zero. A `pkRoot` with any nonzero low-128 bit can therefore *never* equal `currentNode` → `verify` can only return false. A non-canonical `pkSeed` feeds 32 bytes into H_msg, diverging from the signer which always masks (`keygen.rs from_mnemonic`, `signer.py derive_keys` `& N_MASK`). Both `SphincsAccount` and `SphincsFrameAccount` store deployer-supplied keys verbatim.

**Impact.** Fail-closed availability/diagnostic only — a deployer passing a 32-byte (non-top-aligned) key creates a permanently unverifiable ("bricked") account with no on-deploy diagnostic. **Cannot cause a false accept.** All three lenses agreed *low*. **Reconciled: low.**

**Fix.** Mirror the SLH guard near line 47: `if or(iszero(eq(pkSeed, and(pkSeed,N_MASK))), iszero(eq(pkRoot, and(pkRoot,N_MASK)))) { revert ... }` — fail loudly instead of silently bricking, and keep the two verifiers consistent.

---

### C13-mal-f1 — Signature elements not canonicalized → byte-string malleability *(Low)*

**Location:** `src/SPHINCs-C13Asm.sol:39-45` (only length gate); element reads at `:52, :90, :103, :180, :211`.

**What's wrong.** Every 16-byte signature element is read as `calldataload(...) & N_MASK`, keeping the top 128 bits and discarding the low 16 bytes of each 32-byte-aligned read. C13 performs no canonicalization on any of the 3688 signature bytes.

**Reconciliation — partially contested.** The exploitability lens rated it *low*; the spec-conformance lens **refuted** the headline. The nuance: because C13's packing is *dense* (the low 16 bytes "discarded" by one read are the *used* top 16 bytes of the next element), there are **no** free padding bytes *inside* a transmittable 3688-byte string except the discarded low half of the *final* element, which lies past the signature and is zero-padded. So the practical malleability is much narrower than the headline ("2^(128·230) variants"); the byte-coverage analysis (finding C13-mal-f3, below) confirms zero uncovered bytes in `[0, 3688)`. **Also note:** the headline implicated pkSeed/pkRoot, but those are used *raw* (no mask) and DO feed the digest and final compare, so they are load-bearing, not free bits. **Net:** keep as a *low* hygiene note — never treat C13 signature bytes as a uniqueness key.

**Fix.** Add the canonical-key gate (C13-V-f1) and document that sig-element low bytes are intentionally ignored; for strict non-malleability one could require each element's low 16 bytes to be zero (~230 checks, costly). At minimum, key any replay protection on the message/nonce, never on the signature bytes.

---

### SLH-V-f2 / SLH-mal-f6 — Fixed bytes32 message, no length binding / FIPS envelope / domain separation *(Low)*

**Location:** `src/SLH-DSA-SHA2-128-24verifier.sol:41, 79-92`.

**What's wrong.** `verify()` takes `message` as `bytes32` and always feeds exactly 32 message bytes into the inner Hmsg (input length fixed at `0x50` = 80 bytes). There is no length field, domain separator, prehash, or FIPS 205 context envelope. Only exactly-32-byte messages round-trip with the arbitrary-length FIPS/PQClean signer.

**Evidence.** Line 41 `bytes32 message`; inner staticcall covers a constant 80 bytes (`R(16) ‖ seed(16) ‖ root(16) ‖ M(32)`). The forge test uses a 32-byte `MSG`; agreement holds only at 32 bytes.

**Impact.** Interop / footgun, not a forgery. Second-preimage protection for >32-byte payloads rests entirely on the caller's upstream hash. The deployed accounts pass `userOpHash`/`sigHash`, which are domain-separated upstream, so production is fine. Lenses ranged *low → info*; the "trailing-zeros indistinguishable from shorter intent" framing was flagged as overstated (the message domain is *only* 32-byte values). **Reconciled: low** (overlaps SLH-X-f1's envelope point).

**Fix.** Document the 32-byte-message contract explicitly, or take `bytes calldata message` and feed its true length into the inner SHA-256 to match the FIPS/PQClean signer.

---

### SLH-S-f3 — Fast-wrapper disk cache key omits C-binary params/identity *(Low)*

**Location:** `script/slh_dsa_sha2_128_24_fast_signer.py:56-69, 109-121`.

**What's wrong.** The on-disk fixture cache is keyed by `sha256(CONVENTION_TAG ‖ master_sk_hex ‖ message_hex ‖ sig_counter)` — it does **not** include the C binary's compile-time params (`h, a, k, w`) or any digest/mtime of the binary. If the binary is rebuilt with different params (e.g. a reduced-height dev build) without bumping `CONVENTION_TAG`, a previously-cached signature is returned verbatim and won't verify on-chain — or a fixture under wrong params masks a regression.

**Evidence.** Lines 60-69 hash only the tag, sk, message, counter — no params, no `os.stat(BIN_PATH)`, no binary hash. Cache read at 117-121. The only guard is the hand-edited string tag `"fips205-be-fors-v1"`.

**Impact.** Robustness / test-integrity, deterministic (counter) mode only. The forge test runs hedged so never hits the cache (see SLH-X-f4). Exploitability lens **refuted** it as a security issue (dev-ergonomics footgun, no path to harm) → effectively *info*; code-reality/spec rated *low*. **Reconciled: low.**

**Fix.** Fold the C-binary identity into the cache key (`h.update(open(BIN_PATH,'rb').read())` or at least `os.path.getmtime(BIN_PATH)` plus `h,a,k,w`), or store params alongside the fixture and assert on read.

---

### SLH-X-f5 / SLH-X-f4 — Hedged-by-default forge test; no reproducible FIPS KAT in CI *(Low)*

**Location:** `script/slh_dsa_sha2_128_24_fast_signer.py:87-88,126-129`; `test/SLH-DSA-SHA2-128-24-Test.t.sol:24-35`; `signers/sphincsplus-128-24/crosscheck.py` (manual).

**What's wrong.** The fast signer defaults to hedged mode when no `sig_counter` is given (`args.hedged=True`), invoking the C binary with `--hedged` (opt_rand from the kernel CSPRNG) and bypassing the disk cache. The forge `setUp` passes no counter, so every `forge test` run signs a fresh, non-reproducible signature and pays a full cold sign. The bit-exactness of the C reference against Python (the genuine FIPS-direction check — MSB-first digest parse, ADRSc packing) is asserted only by `crosscheck.py`, which **no** forge/cargo/CI hook runs (there is no `.github/workflows` directory at all).

**Evidence.** `fast_signer.py:87` `if not args.hedged and args.sig_counter is None: args.hedged = True`; `:112` `if not args.hedged:` gates the entire cache block; `:126-127` invokes `--hedged`. `Test.t.sol:28-32` builds inputs with only SK and MSG. (The SLH suite *does* include wrong-message/wrong-root/short-sig/non-canonical-key/byte-tamper rejection tests at `:63-103` — none is a pinned KAT.)

**Impact.** Test-quality / conformance-assurance gap, not a runtime bug. A symmetric signer+verifier co-drift to a mutually-consistent-but-wrong-vs-FIPS state would still pass `forge test`. All lenses agreed *low/info*. **Reconciled: low.**

**Fix.** Add a deterministic forge fixture (explicit `optrand`/`sig_counter`) pinned to a known-answer `(seed, msg, sig, root)` tuple cross-validated once via `crosscheck.py`, assert `verify() == true` on it in CI, and wire `crosscheck.py` into a cargo/CI step. Keep the hedged path as an additional non-overfitting check.

---

### C13-acc-g1 — `SphincsAccount._validateSignature` reverts (not `SIG_VALIDATION_FAILED`) on malformed outer/ECDSA signature *(Low)*

**Location:** `src/SphincsAccount.sol:72-78`; OZ `ECDSA.sol:124-126, 273-283`; account-abstraction `EntryPoint.sol:619-634`.

**What's wrong.** ERC-4337 requires `_validateSignature` to *return* `SIG_VALIDATION_FAILED` for any signature failure, never revert. Two paths revert first: (1) `abi.decode(userOp.signature, (bytes, bytes))` (line 72-75) reverts on a non-well-formed 2-element tuple (empty/truncated/out-of-bounds offsets); (2) `userOpHash.recover(ecdsaSig)` (line 78) resolves to OZ's *reverting* `recover` overload (via `using ECDSA for bytes32`), which reverts on non-65-byte length, bad `v`, or high-`s`. A reverting `validateUserOp` is caught by the EntryPoint as `revert FailedOpWithRevert(opIndex, "AA23 reverted", ...)`, reverting the whole `handleOps` call.

**Evidence (source-confirmed).** I read `SphincsAccount.sol:72-99`: the function reverts at `abi.decode`/`recover` but otherwise correctly returns `SIG_VALIDATION_FAILED` on the ECDSA-mismatch and the SPHINCS+ verifier paths (`!success`, `result.length < 32`, `!valid`). `using ECDSA for bytes32` binds `.recover` to the reverting overload; `_throwError` (ECDSA.sol:277/279/281) reverts the three error cases.

**Impact.** Robustness / DoS-flavored, low. A spec-compliant bundler simulates each op and drops the offender before bundling, so the bundle succeeds; the wholesale `AA23` revert only bites a **non-compliant** bundler that skipped per-op simulation (or on-chain `handleOps` relays). The exploitability lens flagged that "an honest user who mis-encodes" is overstated — that user only harms their own op. No forgery, no false-accept, no fund loss. **Reconciled: low** (conditional on bundler misbehavior).

**Fix.** Make `_validateSignature` total: guard the `abi.decode` shape (or bounds-checked calldata view) and return `SIG_VALIDATION_FAILED` on malformed input; replace `userOpHash.recover(ecdsaSig)` with `ECDSA.tryRecover` and return `SIG_VALIDATION_FAILED` when `err != NoError` or `recovered != owner`.

---

### C13-mal-f1-erc4337 — ERC-4337 userOp.signature malleable at the ABI-wrapper layer *(Low)*

**Location:** `src/SphincsAccount.sol:72-99`; verifiers `SPHINCs-C13Asm.sol:33`, `SLH-DSA-SHA2-128-24verifier.sol:41`.

**What's wrong.** The hybrid account decodes `userOp.signature` as `abi.encode(ecdsaSig, sphincsSig)`. The EntryPoint computes `userOpHash` *without* the signature field, so neither signature is bound into it; combined with `abi.encode(bytes,bytes)` admitting multiple valid encodings (non-minimal offsets/padding), the outer `userOp.signature` byte-string is malleable — a third party can rewrap the same authorization into a different blob that still validates.

**Impact.** Replay/malleability only, benign under EntryPoint semantics (the nonce anchors anti-replay; `userOpHash` is unchanged). OZ v5 `recover` already rejects high-`s`. No forgery, no replay. Matters only if a bundler/indexer dedup or fee-accounting layer keys on `userOp.signature` bytes. Spec lens **refuted** as a contract defect; exploitability **info**; code-reality **low**. **Reconciled: low/info.**

**Fix.** Document that `userOp.signature` is non-canonical and must never be used as a uniqueness key; rely solely on the nonce. No on-chain change warranted.

---

### C13-evm-f1 — `assembly("memory-safe")` annotation is unsound *(Low → info under exploitability)*

**Location:** `src/SPHINCs-C13Asm.sol:36` (annotation; **confirmed verbatim** `assembly ("memory-safe")`); writes to `0x40` at `:54,:94,:109,:122,:164,:187`; to `0x60` at `:55,:110,:165,:217`; high memory `0x80..0x5C0` at `:114,:190` etc.

**What's wrong.** The block is annotated `memory-safe`, but it freely writes Solidity's free-memory-pointer slot (`0x40`), the zero slot (`0x60`), and high memory up to `0x5C0` (WOTS chain-top stash, `i` up to 42) without allocating via the FMP or updating it. It is sound *only* because every exit is an unconditional in-assembly `return(0x00,0x20)` (line 228) or `revert` (44/77/173), so Solidity never regains control with a corrupted FMP. The SLH twin deliberately uses bare `assembly` for the same pattern — the more honest choice.

**Impact.** Latent robustness. No current exploit and no miscompilation today. The hazard: a future edit introducing any *normal* exit (a Yul `leave`/fallthrough, or a Solidity-level `return valid;` after the block) would let the ABI encoder allocate using the corrupted FMP. The `memory-safe` tag also licenses optimizer stack-to-memory/reordering decisions on the false premise that `0x80+` is untouched. Exploitability lens rated this *info* (no constructible exploit); code-reality/spec *low*. **Reconciled: low**, latent. (Minor: line 114 reaches only 0x140 — bounded by `lt(i,6)`; the 0x5C0 write is line 190.)

**Fix.** Drop the `("memory-safe")` annotation to match the SLH verifier's bare `assembly` (minimal correct fix, given the block always terminates with return/revert), or load the FMP at entry and operate strictly above it (and restore it) if the annotation is to be kept honest.

---

### C13-evm-f2 / C13-frame-f2 — Frame account turns verifier `revert(0,0)` into `"verify call failed"` *(Low)*

**Location:** `src/SPHINCs-C13Asm.sol:77, 173`; `src/SphincsFrameAccount.sol:33-44`.

**What's wrong.** C13's FORS forced-zero check (`:77 if and(shr(114,dVal),0x7FFFF) { revert(0,0) }`) and WOTS target-sum check (`:173 if iszero(eq(digitSum,208)) { revert(0,0) }`) revert with empty returndata, whereas the length gate returns a proper `Error(string)` and a well-formed-but-invalid signature returns `false`. `SphincsAccount` tolerates a reverting staticcall (`!success → SIG_VALIDATION_FAILED`), but `SphincsFrameAccount.verifyAndApprove` does `require(success && result.length >= 32, "verify call failed")` (**confirmed by source read**) — so a forced-zero/target-sum failure surfaces as the *wrong* error (`"verify call failed"` instead of `"invalid SPHINCS+ signature"`).

**Impact.** Robustness / UX only. The verifier still *rejects* every malformed signature; only the error surface is misleading. No forgery, no accept-invalid. All lenses *low/info*. **Reconciled: low.**

**Fix.** Make the verifier return `false` (`mstore(0x00,0); return(0x00,0x20)`) for the forced-zero and target-sum failures so all soundness rejections are uniform, or have `SphincsFrameAccount` map a reverting `verify()` to the `"invalid SPHINCS+ signature"` path (mirroring `SphincsAccount`).

---

### C13-V-f4 / C13-S-f3 / C13-mal-f2 — Verifier hardcodes digest-shift/mask/fold literals instead of deriving from K/A/H *(Info)*

**Location:** `src/SPHINCs-C13Asm.sol:60, 77, 82-83, 89, 92, 106, 121`; signer counterparts `signer-wasm/src/fors.rs:38,50,63,102`, `script/signer.py`.

**What's wrong.** The verifier embeds the digest bit budget and ADRS folding as raw literals: `htIdx := shr(133,…)` mask `0x3FFFFF` (`:60`), forced-zero `shr(114,…)` mask `0x7FFFF` (`:77`), `idxLeaf0 := and(htIdx,0x7FF)` / `idxTree0 := shr(11,…)` (`:82-83`), FORS leaf fold `shl(19,i)` (`:92`), internal fold `shl(sub(18,h),i)` (`:106`), last-tree `shl(19,6)` (`:121`). These equal the parameterized signer expressions only because **A=19, K=7, H=22, SUBTREE_H=11**: 133=K·A, 114=(K−1)·A, 0x3FFFFF=2^H−1, 0x7FFFF=2^A−1, 19=A, 18=A−1, 0x7FF=2^SUBTREE_H−1. The signers derive all of these symbolically (`fors.rs:63 (K-1)*A`, `:102 K*A`; `signer.py (k-1)*a`, `k*a`).

**Impact.** Maintainability / future-edit fragility; **no live bug** at the deployed params (numerically verified to reproduce the signer's shifts exactly across leaf, all internal levels, last tree, FORS_ROOTS, WOTS chains, WOTS_PK, TREE). A future C13′ that tweaks any of K/A/H/SUBTREE_H, or a clone of this verifier body, would silently desync without a compile error — and the only check that would catch it (the crosscheck) is broken (C13-S-f1) / `#[ignore]`d. All lenses *info*. **Reconciled: info.** (Merges three separately-filed dimension findings with the same root cause.)

**Fix.** Add a comment block at the literal sites asserting the identities (`133=K*A`, `114=(K-1)*A`, masks, `18=A-1`, `19=A`, `11=SUBTREE_H`), and/or a compile-time check in the signer/test harness asserting the literals match params before signing. Document that any param change requires regenerating all the verifier constants in lockstep.

---

### C13-V-f2 — Forced-zero / target-sum failures `revert(0,0)` with no reason *(Info)*

**Location:** `src/SPHINCs-C13Asm.sol:77, 173`.

**What's wrong.** Both crypto-gate failures revert with empty returndata, whereas the length gate returns a proper `Error(string)` and a well-formed-invalid signature returns `false`. `verify()` (declared `returns (bool valid)`) thus has three distinct failure modes for what a caller treats as "invalid signature."

**Impact.** Diagnosability only — both account integrators still reject the signature; no forgery, no accept-invalid. **Info.** (Closely related to C13-evm-f2; kept separate as it is the verifier-internal view.)

**Fix.** Either return `false` for these two malformations to match the bool contract, or revert with a descriptive `Error(string)` like the length gate.

---

### C13-V-f3 — Stale/misleading comments on the forced-zero bit range and ht_shift derivation *(Info)*

**Location:** `src/SPHINCs-C13Asm.sol:76`; `signer-wasm/src/sphincs.rs:16`.

**What's wrong.** The line-76 comment says the forced-zero index i=6 is "at bits 114..132", but the applied mask is `0x7FFFF` (19 bits) → checked range `[114,133)`. The code is correct (shr 114, 19-bit mask); the comment's upper bound is ambiguous/off by one against the adjacent exclusive-range convention. Separately, `sphincs.rs:16 let ht_shift = K * A; // 128` — K·A = 7·19 = **133**, not 128; the code is right, the comment is unambiguously stale.

**Impact.** Documentation only; no runtime effect. The future-edit hazard is real: someone "fixing" `shr(114)` or trusting the `// 128` comment could introduce a genuine signer/verifier desync. **Info.**

**Fix.** Correct line 76 to "…at bits 114..133 (mask = 2^19−1)" and `sphincs.rs:16` to `// = K*A = 133`.

---

### SLH-V-f3 / SLH-mal-f3 — ADRSc chain/hash/tree_height written as 4-byte fields vs C reference's single bytes *(Info)*

**Location:** `src/SLH-DSA-SHA2-128-24verifier.sol:156,200,204,219,245`; `signers/sphincsplus-128-24/sha2_offsets.h:13-16`, `address.c:72-95`.

**What's wrong.** The C reference writes `chain_addr` (offset 17), `hash_addr` (offset 21), and `tree_height` (offset 17) as **single bytes**, leaving adjacent bytes zero. The verifier (and the Python signer via `struct.pack(">III")`) write them as full **4-byte big-endian** fields (`shl(112,…)` → bytes 14-17, `shl(80,…)` → bytes 18-21). The SHA-256 preimages coincide **only** because every such value is <256 at these params (chain ∈ [0,67], tree_height ∈ [1,24], WOTS hash ∈ [0,2]), so the high 3 bytes are zero and match the C struct's padding. `tree_index` is a genuine 4-byte field on both sides (matches unconditionally).

**Impact.** No divergence at NIST-128-24 params; latent. A reparameterization pushing chain/height/hash ≥256 would silently split the verifier+Python signer (4-byte) from the C reference (1-byte, overflowing into the wrong adjacent byte), breaking the "FIPS bit-exact" claim. The exploitability lens noted the only attacker-influenced index (FORS `mdT`) feeds the genuine 4-byte `tree_index`, so there is zero attacker reachability → *info*. **Reconciled: info.** (Minor: original mention of line 144 is the FORS leaf `tree_index`, a genuine 4-byte field on both sides — not a divergent field.)

**Fix.** Add a comment/`static_assert` in the verifier, C, and Python signers that the 4-byte↔1-byte equivalence requires `WOTS_LEN<256`, `tree/FORS height<256`, `w<256`, so a parameter bump forces review.

---

### SLH-V-f4 — Diagnostic contract hardcodes `globalY := parentIdx` (correct only for FORS t=0) *(Info)*

**Location:** `src/SLH-DSA-SHA2-128-24-Diagnostic.sol:64`; contrast production `src/SLH-DSA-SHA2-128-24verifier.sol:154`.

**What's wrong.** `forsTree0Trace` sets `globalY := parentIdx` (with comment "t=0 so shift doesn't matter"), dropping the `(t << (23−j))` idx_offset the production verifier computes (`globalY := or(shl(sub(23,j),t), parentIdx)`). Correct only for tree 0.

**Impact.** Debug-only, not deployed for verification → no live impact. Copy-paste hazard: reusing the loop as a multi-tree template would compute wrong FORS roots for t>0 (fail-closed — would reject valid sigs). **Info.**

**Fix.** Add an assert/comment that the diagnostic is t=0-only, or compute the full `globalY` even in the diagnostic so it is safe to copy.

---

### SLH-evm-f6 — T_l final packed-element write spills 16 zero bytes to [0x496,0x4A6) *(Info)*

**Location:** `src/SLH-DSA-SHA2-128-24verifier.sol:230-235`.

**What's wrong.** The T_l compression packs 68 WOTS chain-tops into `0x56+16·i` with 32-byte `mstore`s. The hashed input is `[0x00,0x496)`. The final iteration (i=67) writes `mstore(0x486, …)` spanning `[0x486,0x4A6)`; its meaningful top 16 bytes land at `[0x486,0x496)` (the last input word), its trailing 16 bytes spill to `[0x496,0x4A6)`, overlapping the staticcall output region `[0x4A0,0x4C0)`.

**Impact.** Harmless: the spilled bytes are deterministic **zeros** (the N_MASK'd low half of element 67), the 10-byte gap `[0x496,0x4A0)` is outside the hashed input, and the staticcall overwrites `[0x4A0,0x4A6)` with the digest. Spec lens **refuted** as a conformance bug (WOTS_pk computed bit-exactly); a maintenance/margin note only. The margin depends entirely on l=68, n=16. **Info.**

**Fix.** None needed today. If hardening: write the final element with a 16-byte-only store, or move the T_l output higher (e.g. 0x500), and add an assertion pinning `0x56 + l*16 == insize` and `out > insize`.

---

### C13-X-f1 — FORS+C forced-zero tree carries no secret entropy *(Info / not-a-defect)*

**Location:** C13 FORS+C design; forced-zero gate `src/SPHINCs-C13Asm.sol:77`.

**Claim (as filed).** Because the last (k=7th) FORS tree index is forced to 0 and its root is revealed directly, the effective few-time strength is `a·(k−1) = 114` bits rather than `a·k = 133`, undercutting the "flat 128-bit to the 2^22 cap" framing.

**Reconciliation.** code-reality **real**, but spec-conformance and exploitability **refuted**: the reduced FORS term is an *intended* property of the +C construction, and 114 bits of FORS subset-resilience is one term among several (combined with the hypertree term it does not drop the scheme below its target). This is **not a defect** — but it *is* the quantity that must appear in the proven few-time bound (see C13-X-f2 and C13-X-f3). Recorded here as info so the security argument accounts for it explicitly.

---

## 4. Needs Manual Review (Unverified)

No candidate findings were left in an unadjudicated state — the adversarial verifier pass returned a usable verdict for every candidate (the empty `UNVERIFIED CANDIDATES` set confirms this). Below are the genuine **assurance gaps** from the coverage assessment: areas where no contradicting evidence was found, but which were **not empirically executed** in this pass and should be run before any productionization. These are *not* findings — they are unverified surface.

| Area | What to run / check | Where to look |
|---|---|---|
| SLH NIST/ACVP KAT conformance | Run external (and internal) ACVP/NIST known-answer vectors against the verifier. None is executed anywhere (no `.github/workflows`). The "FIPS 205 bit-exact" claim is only ever checked as signer↔verifier mutual consistency. | `signers/sphincsplus-128-24/crosscheck.py` (manual); `test/SLH-DSA-SHA2-128-24-Test.t.sol` |
| Full-parameter C13 byte-equality (Py vs Rust vs verifier) | Run the three-way crosscheck at real C13 height (A=19, SUBTREE_H=11). A Python-signer-specific bug (count-grind or ADRS edge that only manifests at full params) would not be caught by anything that runs by default. The `cross_validate.rs` unit oracle is broken (C13-S-f1/f2). | `signers/c13-crosscheck/crosscheck.py`; `signer-wasm/tests/cross_validate.rs`, `fors_reuse_poc.rs` (`#[ignore]`d) |
| C13 Python vs Rust key-derivation chains | Confirm production always injects the account's *actual* fixed pkRoot via `sign_with_known_keys` — `signer.py main()/derive_keys` uses a *different* derivation and produces message-derived keys that will NOT match a deployed account. | `script/signer.py` (`derive_keys`, `sign_with_known_keys`) |
| Off-chain key-handling / non-canonical key origination | Verify deploy/send scripts cannot ship a non-canonical (non-top-128) pkSeed/pkRoot to an account — which (per C13-V-f1) would silently brick it. The on-chain accounts store keys verbatim. | `legacy/script/deploy_frame_account.py`, `send_userop_c13.py`, `send_frame_tx_c13.py` |
| SLH-DSA-Keccak twin & slhvk Vulkan signer | **Out of review scope, not examined.** No automated test guards that the Keccak verifier and its signer agree byte-for-byte at full params; the LSB-first convention is documented as intentionally incompatible with the SHA-2 BE family. | `src/SLH-DSA-keccak-128-24verifier.sol`, `signers/slhvk-sha2-128-24/` |
| SphincsFrameAccount APPROVE step | The approve step is an empty placeholder assembly block (deferred to off-chain `frame_tx.py`); the `sigHash` is caller-supplied with no in-contract binding to transaction parameters. Scaffold-by-design — note for productionization. | `src/SphincsFrameAccount.sol` |

---

## 5. Checked and OK / Refuted

Candidates examined and dropped (so the reader sees the surface was covered):

- **FORS+C forced-zero tree → effective FTS 114 not 133 "undercuts flat-128-bit."** Refuted on spec & exploitability: 114-bit FORS subset-resilience is an intended +C property and one term among several; not a defect. (Folded into C13-X-f1 as info, and into the C13-X-f2/f3 bound discussion.)
- **"Low 16 bytes of every element are attacker-controlled ⇒ trivial 2^(128·230) malleability."** Refuted: C13's packing is dense — the "discarded" low half of one read is the *used* top half of the next element. Byte-coverage simulation over the full layout returns **zero uncovered bytes** in `[0,3688)`. The only unconstrained bytes are `sig[3688:3704]` (past length, masked off, attacker cannot influence). Narrowed to the genuine *low* hygiene note C13-mal-f1.
- **Both verifiers rely on EVM zero-padding for past-end calldata (last element reads 16 B past `sig.length`).** Verified **correct**: the exact-length gate (3688/3856) + N_MASK make it sound; appending bytes trips the length revert. Documentation-only; not a malleability or acceptance edge.
- **SLH staticcalls forward all gas via `gas()` with no return-data-size check.** Refuted: ~360 sequential precompile calls are fine; the implicit 32-byte read is sufficient and SHA-256/0x02 cannot fail at these inputs. No issue.
- **C13 WOTS+C `count` not range-checked / uniquely bound ⇒ malleable.** Refuted: the target-sum gate (`Σ==208`) makes alternative valid counts computationally infeasible to produce; `count` is uniquely determined per accepted signature in practice. (The genuine residual is the *reuse* question, captured in C13-X-f3, not malleability.)
- **C13 R-malleability.** Refuted: `R` is fully bound into the digest (and thus into `ht_idx`, FORS indices, forced-zero), so a mutated `R` requires a fresh full forgery and no two distinct `R` verify the same sig body. (The *grindability* of R is the real concern — C13-X-f2 — not malleability.)
- **ERC-4337 userOp.signature in `userOpHash` / ECDSA malleability as a contract defect.** Refuted as a defect: correct per ERC-4337 (nonce anchors anti-replay; userOpHash excludes the signature by design) and OZ v5 rejects high-`s`. Reduced to the off-chain-dedup hygiene note C13-mal-f1-erc4337.
- **Gas DoS via unbounded loops.** Checked OK: every verifier loop is bounded by fixed compile-time parameters; no attacker-controlled iteration count.
- **Signer liveness (grind exhaustion).** Checked OK: both R-grind (~2^19 forced-zero target, 10M cap) and count-grind (~58k expected trials for sum=208, 10M cap) are bounded, succeed w.h.p., and return `Result/Err` on exhaustion (no silent invalid sig).
- **SphincsAccount access control (execute / rotateKeys / rotateOwner).** Checked OK: well-tested by `SphincsAccountAccessControlTest` (execute-is-EntryPoint-only, rotation gating).

---

## 6. Recommended Next Steps

Ordered by leverage for the two in-scope families.

1. **Resolve the C13 security model (C13-X-f2, highest substantive item).** Either secret-key `R` (`R = mask_n(keccak(sk_prf ‖ opt_rand ‖ M))`, keep grinding the forced-zero predicate with a secret nonce), **or** write the few-time / subset-resilience proof in the public-grindable-randomizer model and document that C13's `R` is adversary-grindable. State the proven bound (~2^133), not the secret-`R` one.
2. **Prove or document the target-sum WOTS+C multi-reuse bound (C13-X-f3).** Show that C13's few-time security under expected `ht_idx` reuse at the 2^22 cap is carried by the FORS term (effective k=6), not WOTS one-time-ness, and bound the min-combination forgery probability for w=8, l=43, T=208. Add a regression test: two messages colliding on `ht_idx` with distinct `fors_pk`, assert no third valid WOTS+C opening is assemblable from the revealed chains.
3. **Repair and wire up the C13 cross-implementation oracle (C13-S-f1, C13-S-f2).** Fix the 3→4-arg `fors_secret` call, regenerate `PY_FORS_SECRET_0_0` to the ht_idx-folded value (`0xf3c46060…`), and add `cargo test --release` (compile + run) to CI so the test binary cannot silently rot again.
4. **Add a pinned, reproducible FIPS KAT to CI for SLH (SLH-X-f1, SLH-X-f4/f5).** A deterministic forge fixture (explicit `optrand`/`sig_counter`) pinned to a known-answer `(seed, msg, sig, root)` cross-validated once via `crosscheck.py`, asserting `verify()==true`. Run the full Python-vs-C `crosscheck.py` in CI. This is the single largest assurance gap for the "FIPS 205 bit-exact" claim. Decide and document whether the target is *internal* (ACVP-internal) or *external* (add the `0x00 0x00 ‖ M` envelope on both signer and verifier).
5. **Correct the documentation claims.** (a) Reword the SLH "FIPS 205 bit-exact" docstring to "internal mode / no context envelope" unless the envelope is added (SLH-X-f1). (b) Replace the "2^24 hard cap / flat 128-bit" SLH wording with the true 2^22 leaf budget + birthday/FORS caveat (SLH-X-f2cap). (c) Make the C13 Python CLI sign raw bytes or document the 32-byte-only contract (SLH-S-f1 / SLH-V-f2).
6. **Low-cost hardening on the verifiers.** Add the canonical-key guard to C13 mirroring SLH (C13-V-f1); drop the inaccurate `("memory-safe")` annotation on C13 (C13-evm-f1); make the forced-zero/target-sum failures return `false` (or document revert==invalid) and have `SphincsFrameAccount` map verifier reverts to "invalid signature" (C13-V-f2 / C13-evm-f2); make `SphincsAccount._validateSignature` total via `tryRecover` + a guarded decode (C13-acc-g1).
7. **Pin the magic numbers (C13-V-f4, SLH-V-f3).** Comment every literal-vs-param identity (133=K·A, 114=(K−1)·A, 19=A, 18=A−1, masks, 11=SUBTREE_H; SLH ADRSc field widths <256), and re-enable the `#[ignore]`d full-height crosscheck so a desync is caught empirically.

**Honest summary of the confirmed set:** the list is genuinely short on severity — **zero critical/high** after reconciliation (the one originally-high item is a non-practical, ~2^133-work security-model gap, reconciled to medium), **six medium** (all model/conformance/test-oracle gaps, no exploit), and the remainder low/info robustness, consistency, and documentation items. No forgery, key-recovery, or false-accept path was found in either in-scope family. The prior critical "Finding C" (global FORS instance → universal forgery) is **fixed** in the current tree (per-message hypertree-leaf keying), and that fix is still covered by `fors_leaf_keying.rs`. The largest *residual risk* is not a code bug but an **assurance gap**: the "FIPS 205 bit-exact" SLH claim and the C13 cross-implementation parity are not guarded by any automated KAT or CI hook.