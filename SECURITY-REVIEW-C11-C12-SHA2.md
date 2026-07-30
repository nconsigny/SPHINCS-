# Security Review — New SPHINCS+ Verifiers (branch `migrate/c11-c12-fips-layout`)

> **AI-agent-assisted review, not an independent professional audit.** Produced by a
> multi-agent adversarial process (35 per-dimension reviewers → exploit-lens + refute-lens
> verification per finding → synthesis), then **independently re-verified by the lead reviewer**
> (by-hand re-derivation of the load-bearing literals, `grep` corroboration, and a full run of the
> branch's Foundry suite). It has **not** been signed off by a human security professional. The
> code remains **not audited, not production-safe** (per `CLAUDE.md`). Companion to the prior
> `SECURITY-REVIEW-C13-SLHDSA.md`.
>
> **Resolution note (2026-07-30):** L-03 is fixed in all current C12 on-chain
> backends. Keccak, SHA-2, and BLAKE2b now use `len1=43`, `len2=3`, `l=46`;
> their 43rd message digit binds the final two node bits with one zero pad bit.
> This is a breaking key/signature-format change: existing C12 roots and
> signatures must be regenerated.

## 1. Scope

Five **new** verifiers on this branch, plus the C11/C12 JARDIN→FIPS ADRS migration:

| ID | File | Construction / hash | Branch status |
|---|---|---|---|
| c11-keccak | `src/keccak/SPHINCs-C11Asm.sol` | WOTS+C / FORS+C, keccak256, FIPS 205 §4.2 uncompressed 32-B ADRS | migrated JARDIN→FIPS |
| c12-keccak | `src/keccak/SPHINCs-C12Asm.sol` | **plain SPHINCS+ (SPX)**, real WOTS+ checksum + d=5 hypertree, keccak256, FIPS uncompressed ADRS | migrated JARDIN→FIPS |
| c13-sha | `src/sha/SPHINCs-C13-SHA.sol` | WOTS+C / FORS+C "minimal twin", SHA-256 precompile, 22-B ADRSc, one-shot H_msg (not FIPS) | new |
| c11-sha | `src/sha/SPHINCs-C11-SHA.sol` | WOTS+C / FORS+C "minimal twin", SHA-256, 22-B ADRSc, one-shot H_msg (not FIPS) | new |
| c12-sha | `src/sha/SPHINCs-C12-SHA.sol` | **full FIPS 205 SLH-DSA-SHA2** at C12 params (MGF1 H_msg + `0x00‖0x00` envelope, standard WOTS+ checksum) | new |

**Trusted baseline** (already reviewed, no forgery found): `SECURITY-REVIEW-C13-SLHDSA.md`
(C13-keccak + SLH-DSA-SHA2-128-24). The new verifiers are twins/migrations of those, so the audit
leaned on two high-signal axes: **differential** (new verifier vs trusted twin) and **param-literal
re-derivation** (every hard-coded shift/mask/offset recomputed from the new `(n,h,d,a,k,w)`).

## 2. Executive summary

**No accept-forgery / false-accept path was found in any of the five verifiers.** The cryptographic
core of each (FORS+C / WOTS+C counter-grind for the C-series; real WOTS+ checksum + d=5 hypertree
for C12; MGF1 + empty-context envelope for C12-SHA) re-derives correctly from its own parameters and
is internally consistent with its own signer. Every confirmed issue is on a **rejection path or is
fail-closed**.

| Reconciled severity | Count |
|---|---|
| Critical / High | **0** |
| Medium | **0** |
| Low | **3** (deduplicated: L-01, L-02, L-03) |
| Info | **3** (I-01, I-02, I-03) |

The recurring theme is **twin-parity drift**: the migrated keccak C11/C12 did not inherit three
hardening conventions the trusted C13 verifier established (uniform bool-false rejection; the
canonical-public-key guard; dropping the unsound `("memory-safe")` annotation). None affects
soundness. The one cross-cutting item — a shared all-`0xFF` H_msg domain tag across the C-series
(§6) — is a documentation/hygiene gap that is **de-facto mitigated** by distinct signature lengths
and hash functions (§6), not a live forgery vector.

## 3. Lead-reviewer independent verification

To avoid the signer-as-oracle blind spot (the Foundry tests pass because the in-repo signer and the
verifier agree — a *shared* deviation would pass yet still be wrong), the following were checked
directly, independent of the agent fleet:

- **Foundry suite — green, 20/20.** `SphincsC11Test` (1), `SphincsC12Test` (5, incl. reject-short-sig),
  `SphincsC11ShaTest` (4), `SphincsC13ShaTest` (4), `SphincsC12ShaTest` (4), `AdvVerifyPaddingProbe` (2).
  Confirms accept-valid + coarse reject (wrong-message / wrong-root) + that past-length calldata is
  dead input. **Caveat:** the negative tests do *not* flip individual structural fields (one auth
  node, one WOTS digit), so fine-grained tamper-rejection remains source-verified only (§6.2).
- **C12-SHA is genuinely full-FIPS** (by-hand byte trace of `src/sha/SPHINCs-C12-SHA.sol:50-61`):
  inner `SHA-256(R‖seed‖root‖0x00 0x00‖M)` (82 B at `0x00..0x52`), outer
  `SHA-256(R‖seed‖inner‖I2OSP(0,4))` (68 B at `0x00..0x44`) = MGF1 block 0, m=21 B ≤ 32 B so one
  block suffices, R correctly truncated to 16 B. The empty-context envelope the trusted d=1 SLH
  verifier *omits* (prior SLH-X-f1) **is present here.** The FORS index partition (md[t]=`shr(249-7t)`
  bits [116,256), tree [96,112), leaf [88,92) — disjoint), the WOTS+ checksum (`csum<<7`, MSB-first
  `shr(13-3j)&7`), and the FORS tree-index fold `(t<<(a-1-h))|parent` all re-derive correctly.
- **d=5 hypertree descent is bijective** (both C12 variants): leafIdx (4 bits) + treeIdx (16 bits)
  = 20 = h; layer 0 consumes leafIdx, layers 1-4 peel 4-bit nibbles off treeIdx
  (`curLeaf = curTree & 0xF; curTree >>= 4`). No bit reused or dropped — closes §6.4.
- **`grep` corroboration:** the canonical-pubkey guard is present in C13 + all three SHA verifiers
  and absent in C7/C9/C11/C12-keccak (L-02); the all-`0xFF` H_msg tag is shared by
  C7/C9/C11/C13-keccak + C11-SHA/C13-SHA, with only C12-keccak (`0xFF..FC`) distinct (§6); C11-keccak
  lines 53/136 reject via `revert(0,0)` (L-01); the keccak C-series length gates (3688/3704/3816/3976)
  are pairwise distinct (§6).

The lead-reviewer pass agreed with every workflow verdict and changed none of the severities; it
**downgrades the practical risk** of the §6 domain item (see there) and **closes** open items §6.4
and §6.6.

## 4. Per-verifier risk posture

| Verifier | Core soundness | Differential vs twin | Notable gaps |
|---|---|---|---|
| **c11-keccak** | OK — `htIdx=shr(143)&0xFFFF`, forced-zero `shr(132)&0x7FF`, `target_sum=203`, sig=3976 all re-derive | matches C13 math | L-01 empty-revert; L-02 no pubkey guard; I-01 `("memory-safe")` |
| **c12-keccak** | OK — H_msg, digest split (a=7,k=20,h=20,d=5), checksum, d=5 descent re-derive | matches legacy JARDIN twin (only ADRS word positions move) | L-02 no pubkey guard; L-03 WOTS+ len1=42; I-01 `("memory-safe")` |
| **c13-sha** | OK (minimal SHA twin of trusted C13) | faithful | shares all-`0xFF` H_msg tag (§6) |
| **c11-sha** | OK (minimal SHA twin of new C11) | twin of c11-keccak (itself new — not an independent oracle) | shares all-`0xFF` H_msg tag (§6); has the pubkey guard c11-keccak lacks |
| **c12-sha** | OK — verified to actually do MGF1 + `0x00‖0x00` envelope; mirrors KAT-validated d=1 SLH-DSA-SHA2 | structurally faithful, adds the envelope | L-03 WOTS+ len1=42; research params → no NIST KAT |

## 5. Findings (reconciled severity, deduplicated)

Where the exploit lens lowered severity, the lower value is used and the original noted.

### L-01 — c11-keccak soundness gates empty-revert instead of returning bool `false` *(low)*
**Location:** `src/keccak/SPHINCs-C11Asm.sol:53` (FORS forced-zero gate) and `:136` (WOTS+C
digit-sum gate). Trusted twin returns `false` here (C13 review fix **C13-V-f2**).
**Impact:** none / interop only. Empty-revert is strictly *more* restrictive than `return false` —
it cannot accept anything C13 rejects, and honest signatures trip neither gate (literals verified:
forced-zero is the last FORS index `i=12` at bits `(k-1)·a = 132`, mask `2^11-1 = 0x7FF`;
`target_sum=203` matches the C11 signer config). In-repo accounts absorb a revert via the staticcall
`success` flag identically to bool-false, so only a hypothetical external `try verify() returns(bool)`
caller is affected (and `SphincsFrameAccount` would surface the wrong require message).
**Fix:** replace both `revert(0,0)` with `mstore(0x00,0) return(0x00,0x20)`.

### L-02 — c11-keccak and c12-keccak omit the non-canonical public-key guard *(low; c12 originally proposed medium, downgraded)*
**Location:** guard absent at `src/keccak/SPHINCs-C11Asm.sol:33-34` and
`src/keccak/SPHINCs-C12Asm.sol:58-59`; present in `src/keccak/SPHINCs-C13Asm.sol` and all three SHA
verifiers (confirmed by `grep "Invalid public key"`: C13/C11-SHA/C13-SHA/C12-SHA = 1; C7/C9/C11/C12-keccak = 0).
**Impact:** none (reject-valid / fail-closed). The final accept is `valid := eq(currentNode, root)`
where `currentNode` is **always** `keccak256(...) & N_MASK` (low 128 bits zero) but `root = pkRoot`
is used raw; a non-canonical key can therefore only make the equality *fail*, never spuriously
succeed — reaching the root still requires the full FORS+WOTS+Merkle preimage chain. The exploit lens
downgraded the c12 candidate from medium to low for exactly this reason. The in-repo signers always
emit canonical keys (`& N_MASK`), so no honestly-provisioned account is bricked. (Also true of the
unmasked `pkSeed` flowing into preimages: a non-canonical seed desyncs the hash chains from the
signer → reject, not accept — this is reject-valid only, **not** a soundness tweak.) Not a migration
regression (legacy JARDIN C11/C12 and live C7/C9 also lack it — C13 set the precedent).
**Fix:** port C13's guard verbatim after the length check into C11/C12-keccak (ideally C7/C9 too);
optionally validate keys at the account layer to fail loudly at provisioning.

### L-03 — both C12 variants use WOTS+ `len1=42` where FIPS 205 requires `43` *(low; originally proposed medium, downgraded)*
**Location:** `src/keccak/SPHINCs-C12Asm.sol:146-147`, `src/sha/SPHINCs-C12-SHA.sol:126-127`;
signers `jardin_spx_signer.py` (`L1=42`), `slh_dsa_sha2_c12_signer.py` (`L1=42`).
**What's wrong:** for `n=16` (128-bit WOTS message) and `w=8` (`lg_w=3`), FIPS 205 WOTS+ requires
`len1 = ceil(8n/lg_w) = ceil(128/3) = 43` message chains. Both C12 verifiers use `len1=42`,
`len2=3`, `l=45`, so 42·3 = 126 of the 128 message bits are signed; the remaining 2 bits are read by
no chain and added to no checksum (keccak/LSB-first drops value bits 126-127; SHA/MSB-first drops
value bits 0-1). Two WOTS messages differing only in those 2 bits produce an identical signature.
**Impact:** spec-divergence; **not an exploitable accept-forgery.** At every layer the WOTS message
is a hash output (FORS pk via `T_k`, or an XMSS subtree root via `H`), so weaponizing the 2 unbound
bits needs a ~2^126 second-preimage on keccak/SHA-256 — only ~2 bits below the 128-bit baseline, and
not the binding security bound at C12's reduced params. The checksum is sound over the 42 covered
digits. **The "full FIPS 205" label on C12-SHA is imprecise** — its WOTS+ length is non-standard.
**Fix:** either adopt `len1=43 / len2=3 / l=46` in both verifiers and both signers, or document the
`len1=42` choice and drop the "full FIPS 205 WOTS+" wording from the C12-SHA header.

### I-01 — `assembly ("memory-safe")` on C11/C12-keccak where C13 forbids it *(info)*
`src/keccak/SPHINCs-C11Asm.sol:22`, `src/keccak/SPHINCs-C12Asm.sol:47` annotate a block that writes
the FMP slot `0x40`, zero slot `0x60`, and high memory without advancing the FMP. **Refuted as
exploitable** by both lenses: every exit is an unconditional in-assembly `return`/`revert`, the whole
function body is the assembly block, and contracts compile under `via_ir` with passing tests — so the
annotation is benign today (and C7/C9 carry it too; C13 is the conservative outlier). Latent only:
a future fall-through/post-block edit could license an unsound optimization. **Fix (optional):** drop
the qualifier to match C13.

### I-02 — ADRS layout / hash-framing / param-literal audit clean *(info — positive result)*
Exhaustive differential + literal audits found **no** defect in the ADRS byte layout, tweakable-hash
framing, or parameter literals of c11-keccak, c12-keccak, or c12-sha. Notably: c12-keccak's H_msg
`keccak(seed‖root‖R‖msg‖0xFF..FC)` is byte-identical to the legacy JARDIN twin with only the
documented ADRS word-position shifts; its digest split consumes every index bit exactly once; the
full 32-B R is read unmasked, matching this verifier's own signer (consistent — c12 binds the whole
R field, unlike c13 which masks it).

### I-03 — stale signature size in C12-SHA signer docstring *(info)*
`script/slh_dsa_sha2_c12_signer.py` prose says "6,512 B" (a keccak-C12 leftover); actual is 6,496 B
(R=16). Contradicted by the file's own runtime assert, the verifier length gate
(`src/sha/SPHINCs-C12-SHA.sol:31`), and the test. Cosmetic.

## 6. Residual / needs-manual-review

1. **Cross-verifier H_msg domain separation *(documentation/hygiene; practical risk LOW)*.**
   `grep`-confirmed: C7/C9/C11/C13-keccak and C11-SHA/C13-SHA all feed the identical all-`0xFF` tag
   into H_msg, with the same FIPS ADRS leaf framing; only C12-keccak (`0xFF..FC`) and C12-SHA
   (empty-ctx envelope) differ. This **contradicts** `CLAUDE.md`'s "Domain-separated H_msg (prevents
   cross-variant collisions)" claim. **However, lead-reviewer analysis finds the live variants are
   de-facto separated:** (a) within the keccak C-series the exact-length gates are pairwise distinct
   (3688/3704/3816/3976), so a signature for one variant reverts the length check of another;
   (b) a keccak verifier and its same-length SHA twin (C11↔C11-SHA, C13↔C13-SHA) are separated by the
   hash function itself (keccak256 vs SHA-256 yield unrelated digests and tweakable hashes); and
   (c) per-variant digest bit-slicing differs, so intermediate FORS/WOTS leaves do not structurally
   reuse across variants. The residual is therefore the inaccurate doc claim + latent fragility if a
   future variant ever collides in length *and* hash *and* parse. **Action:** correct the `CLAUDE.md`
   wording, and either add a distinct per-variant domain byte to H_msg or assert that a `(pkSeed,
   pkRoot)` key MUST NOT be shared across verifiers. Cheap confirmation: a replay matrix
   (sign with C11, feed to C7/C9/C13 and the SHA twin; assert all reject).
2. **Fine-grained tamper-rejection.** The Foundry suite confirms accept-valid + wrong-message /
   wrong-root reject, but does not flip individual fields. Add a 1-byte-flip sweep at each structural
   boundary (R, each FORS sk/auth, each WOTS chain, count field, XMSS auth) asserting false/revert.
3. **C12-SHA envelope *binding* (structurally verified, dynamically unconfirmed).** Flip one envelope
   byte (e.g. ctx-len `0x00→0x01`) in `slh_dsa_sha2_c12_signer.py` and confirm both signer and
   verifier reject — proving the envelope is bound, not cosmetic. No NIST KAT exists (research params).
4. **~~d=5 hypertree descent~~ — CLOSED by §3** (20-bit address bijectively consumed).
5. **Signature malleability via `N_MASK`.** Every verifier ignores the low 128 bits of each 16-B
   on-wire field (and the low 28 B of the `count` word), so many byte-strings verify identically
   (carry-forward of C13-mal-f1; the `AdvVerifyPaddingProbe` test demonstrates the dead-padding case).
   Benign provided `SphincsAccount`/`SphincsFrameAccount` anchor replay on the nonce, never on sig
   bytes — confirm and document; never key uniqueness on the signature.
6. **~~C12 FORS forced-zero absence~~ — CLOSED by §3.** Both C12 variants read 20 distinct 7-bit FORS
   indices over a disjoint digest partition with no index forced to zero (correct for plain FORS).

## 7. Recommended next steps (highest leverage first)

1. **Fix the `CLAUDE.md` domain-separation claim** and decide on per-variant H_msg domain bytes vs a
   documented key-isolation requirement (§6.1). This is the only item adjacent to soundness (via key
   reuse); the cheap replay-matrix test confirms the de-facto separation argument.
2. **Fix L-02:** port C13's `Invalid public key` canonical guard into C11/C12-keccak (and C7/C9).
3. **Fix L-01:** replace the two `revert(0,0)` in C11 with bool-false to match C13's uniform contract.
4. **Resolve L-03:** choose FIPS-conformant `len1=43` or correct the "full FIPS 205 WOTS+" labeling.
5. **Run the dynamic 1-byte-flip rejection sweep (§6.2) and the envelope-binding test (§6.3)** to
   convert source-verified claims into round-trip-confirmed results.
6. **Hygiene (I-01, I-03):** drop the `("memory-safe")` annotation on C11/C12-keccak; fix the
   6,512→6,496 signer docstring.

---
*Method: 35 per-(verifier × attack-class) reviewers → 2-lens adversarial verification (exploit +
refute) per finding → synthesis (77 agents, ~3.4M tokens), then lead-reviewer re-verification +
Foundry suite. Source-analysis findings on the keccak C11/C12 paths should be treated as
source-verified; the dynamic items in §6.2/§6.3 remain open.*
