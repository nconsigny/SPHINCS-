# Agent-Assisted Security Review: live verifiers, accounts and signers (2026-10)

> **AI-agent-assisted review, not an independent professional audit.** Produced by a
> multi-agent workflow (finders, then deduplication, then one reproduce-or-refute agent per
> finding, then measured patches and old-vs-new trace-equivalence passes) and re-checked by the
> lead reviewer. No human security professional has signed it off. The code remains
> **not audited, not production-safe** (see `CLAUDE.md`). Companion to
> `../SECURITY-REVIEW-C13-SLHDSA.md`, `../SECURITY-REVIEW-C11-C12-SHA2.md` and
> `SECURITY-ANALYSIS.md`.

**Baseline:** `7cb0c55`. The fixes and gas changes below are on branch `review/verifier-fixes`
(commits `8fbe0aa` to `a5d3b6d`, one per area).

## 1. Scope

| Area | Files |
|---|---|
| Keccak verifiers | `src/keccak/SPHINCs-C{7,9,10,11,12,13}Asm.sol` |
| SHA-256 verifiers | `src/sha/SPHINCs-C1{0,1,2,3}-SHA.sol`, `SLH-DSA-SHA2-128-24verifier.sol`, `-Diagnostic.sol` |
| BLAKE2b verifiers | `src/blake/SPHINCs-C1{1,2,3}-BLAKE.sol` (precompile 0x09) |
| Accounts | `SphincsAccount.sol`, `SphincsAccountFactory.sol`, `SphincsFrameAccount.sol`, `SphincsFrameVerify.yul` |
| Signers and tooling | `script/*signer*.py`, `signers/noble-slh-dsa/`, `signers/c13-crosscheck/` |

**Proof-coupled, not modified:** `src/keccak/SPHINCs-C13Asm.sol` and
`src/sha/SLH-DSA-SHA2-128-24verifier.sol` are pinned by the Lean model in `verity/`. Neither has
a diff against `7cb0c55`. Gas savings for them are reported only (§9).

**Not examined:** `legacy/` verifiers (except where the C12 signer fix reaches them), the
`verity/` proofs, the GPU signer, and the JARDIN repo.

## 2. Method

1. **Vectors.** One valid vector per live verifier (14). A shared harness checks the valid
   signature, two message flips and 48 byte flips, and records cold/warm gas from a raw
   `STATICCALL`. All gas figures below come from it unless stated.
2. **Finding.** 14 finders, one per area (keccak C7/C9, C10/C11, C12, C13; SHA twins, C12-SHA,
   SLH-DSA; BLAKE C11/C13, C12; frame module; 4337 accounts), plus three cross-cutting passes
   (twin consistency, signer/verifier agreement, git-history regressions). 69 raw findings
   (12 bug, 34 gas, 23 hardening) deduplicated to 26.
3. **Verification.** One refute agent per finding; every bug was reproduced with a PoC in a
   private copy. All 26 confirmed (some severities corrected), none rejected.
4. **Patches and equivalence.** Gas ideas were measured as patches, rebased, and only the best
   combination applied. Per family, old and new code were trace-compared on every hash or
   precompile input, and a skeptic read the diff and fuzzed old against new (§8).
5. **EIP-8141 research** on the witness-copy form live ethrex networks run (§10).

PoCs lived in scratch copies outside the repository and are described, not shipped. Every fix
has an in-tree regression test that fails against the pre-fix code.

## 3. Summary

- **Critical: forgery on C12 keccak and C12-BLAKE (B-01).** The C12 signer derived FORS secrets
  without the hypertree position. About 1,000 honest signatures let anyone forge a signature on
  any message, and the unmodified live verifiers accept it. The fix is signer-only. **Every C12
  key that has signed with the old signer must be rotated.**
- **The EIP-8141 frame module could not approve under the current spec (B-02).** It also always
  used the first ARBITRARY signature entry (B-03). Both failed closed; both are fixed.
- No other false-accept path was found in the 14 live verifiers. Two low tooling bugs are fixed
  (B-04, B-05), and seven hardening items are applied (§5).
- **Gas:** verifier gas fell about 24% for keccak C7 to C12, 24 to 28% for the SHA twins and
  about 95% for BLAKE. 4337 validation is about 7% cheaper and the frame verify path about 6.2K
  cheaper (§7). C13 could save 26 to 37K once its proof is updated (§9).
- The new SHA kernel relies on one documented assumption about how 0x02 fails (§6.1). It holds
  on every EVM-equivalent chain.

## 4. Findings

| ID | Severity | Title | Status |
|---|---|---|---|
| **B-01** | **Critical** | C12 keccak/BLAKE FORS PRF not bound to the hypertree position: universal forgery | Fixed (signer); **rotate keys** |
| **B-02** | Medium (filed High) | Frame module copies the witness with the removed `SIGPARAM(0x04)` form | Fixed |
| B-03 | Low | Frame module always takes the first ARBITRARY/empty-msg entry | Fixed |
| B-04 | Low | SLH-DSA Diagnostic uses the pre-envelope (internal) H_msg | Fixed |
| B-05 | Low | C13 three-way crosscheck points at a deleted verifier path | Fixed |
| H-01 | Low | Keccak C7/C9/C10/C11 soundness gates `revert(0,0)` instead of returning false | Applied |
| H-02 | Low | No precompile-presence check on the 0x02 / 0x09 calls | Applied (SLH-DSA report-only) |
| H-03 | Low | BLAKE "RejectsWrongRoot" tests hit the key guard, never the root compare | Applied (tests) |
| H-04 | Low | `SphincsFrameAccount` constructor accepts bad keys and code-less verifier/module | Applied |
| H-05 | Low | Factory predicts undeployable addresses; `createAccount` not idempotent | Applied |
| H-06 | Low | `SphincsAccount` accepts zero owner / zero root (permanent brick) | Applied |
| H-07 | Low | noble signer hex parsing differs from the Python signers; no 32-byte check | Applied |
| G-01…G-14 | gas | see §7 | Applied, superseded or report-only |

### B-01: C12 FORS secrets not bound to the hypertree position (Critical)

**Mechanism.** `script/jardin_spx_signer.py::fors_secret(sk_seed, tree_idx, leaf_idx)` hashed
`sk_seed ‖ "spx_fors" ‖ t ‖ j`: despite the parameter names, both call sites passed the FORS
tree number `t` and leaf `j`, never the hypertree position `(ht_tree, ht_leaf)`.
`spx_fips_signer.py` (keccak C12) and `spx_blake_signer.py` (C12-BLAKE) patch that module's
hashes and ADRS but not `fors_secret`. So all 2^20 FORS instances under a key shared one table
of 20 × 128 = 2,560 secrets. The verifier binds the FORS ADRS to the position, but a leaf is
`F(pkSeed, ADRS, sk)` with `pkSeed` and `ADRS` public, so a secret revealed at one position
rebuilds the same leaf anywhere. The signer's self-check (`spx_verify`) used the same
derivation, so it could not catch this. The same class was fixed for C6/C8/C10 in `b5082aa`.

**Attack.** (1) Pool the 20 secrets each honest signature reveals until the table is full.
(2) Grind `R`, which the verifier reads freely from the signature, until `H_msg(m*)` lands on a
position that already has an honest signature. (3) Rebuild the 20 FORS trees from the pool: the
FORS public key equals the honest one, so the honest hypertree half is reused unchanged.

**PoC (scratch, unmodified signer and verifiers).** 1,200 honest signatures filled the table;
a forgery on `keccak256("ATTACKER-CHOSEN MESSAGE: drain the account")` then took 94 H_msg trials
on keccak C12 and 2,311 on C12-BLAKE, and both live verifiers returned `true`. An independent
C12-BLAKE run had a full table after 1,500 signatures and forged in 341 trials. A third run
found 113 secrets revealed with identical bytes at two positions in just 40 signatures.

Our estimate, for uniform indices, of forgery cost against the number of signatures `q`:

| q | 50 | 100 | 250 | ≥1,000 |
|---|---|---|---|---|
| H_msg evaluations | about 2^47 | about 2^31 | about 2^16 | about 2^10 |

**Affected:** keccak C12, C12-BLAKE, legacy C12, and the JARDIN repo's `JardinSpxVerifier`
stack (it shares `jardin_spx_signer.py`). The retired Python `slh_dsa_keccak_128_24_signer.py`
had the same pattern (impractical to harvest at a=24; its C fork binds correctly) and was fixed
too. **Not affected:** C12-SHA (FIPS PRF over the ADRS), `script/signer.py` (folds in `ht_idx`),
`signers/signer-wasm`, and the frozen `legacy/script/signer.py` (fresh keypair per message).

**Fix.** `fors_secret(sk_seed, ht_tree, ht_leaf, fors_t, j)` now hashes
`sk_seed ‖ "spx_fors" ‖ ht_tree(8) ‖ ht_leaf(4) ‖ t(4) ‖ j(4)`, and both call sites pass the
position. The verifiers, `pk_root` and the signature format are unchanged. Regression:
`test/SphincsC12ForsBindingTest.t.sol` (`testC12ForsSecretsArePositionBound`,
`testC12BlakeForsSecretsArePositionBound`, helper `test/py/c12_fors_binding.py`). Two honest
signatures at different positions that open the same `(t, j)` must reveal different secrets, and
moving A's secret into B must fail on chain. Both tests fail against the old signer.

**Operational consequence: rotate.**
- **Old secrets still forge.** Secrets revealed under the old derivation stay valid at every
  position with an honest old-derivation hypertree signature. The verifiers and `pk_root` are
  unchanged, so those forgeries still verify after the signer is upgraded.
- **The key cannot simply keep signing.** Re-signing such a position under the new PRF makes its
  layer-0 WOTS key sign a second FORS public key.
- **Nothing forces rotation**, because `pk_root` does not change.

**Treat every C12 key that produced signatures with the old signer as compromised and rotate
it**, whatever its signature count. That covers keccak and BLAKE, live and legacy, and keys used
through JARDIN's `JardinSpxVerifier`. Port the fix to the nconsigny/JARDIN copy of the signer.

### B-02: Witness copy uses the removed `SIGPARAM(0x04)` form (Medium, filed High)

**Mechanism.** `sigCopyToArgs` ran `hex"80600390b46100a49160009190600490b4"`, the five-operand
SIGPARAM copy from the 2026-07-28 EIP-8141 text the module cited. Since then `4a9ad32` (07-30)
reordered the operands, and `ead1a36` (08-18) moved the copy to a new `SIGDATACOPY` (0xb5):
SIGPARAM now defines only params 0x00 to 0x03, and any other param halts.

**Impact.** Under the current spec every VERIFY frame halted; under the 07-30 text the copy read
the wrong bytes and verification failed. Both fail closed, but `frameModule` is immutable, the
legacy `verifyAndApprove` never runs APPROVE and `execute` is self-call only, so an account built
with this module could never be approved and ETH sent to it was stuck. The bytecode test pinned
the stale blob, so CI stayed green. The verification agent rated it Medium (fail-closed drift
in a Draft EIP). **PoC (scratch):** an 8141-opcode emulator ran the real module with the real
`SphincsC13Asm` answering: 07-28 text gives APPROVE(3); 07-30 corrupts the calldata from byte 164
("invalid SPHINCS+ signature"); the current text halts at pc 224 ("undefined SIGPARAM param 0x04").

**Fix.** The copy is now `80600390b460006100a4b5`: SIGPARAM(0x03) for the length, then
`SIGDATACOPY(mem 0xa4, data 0, len, i)`. The header cites `af3a7802c8ea` (2026-10-09).
`test_FrameModule_EmitsTheSpecifiedInstructions` asserts the new blob and forbids the old one.
`test/SphincsFrameModuleEmuTest.t.sol` (7 tests) runs the module under
`test/py/frame8141_emu.py`, an emulator of the current spec, with real C13 witnesses. With the
old blob restored, it halts. The right opcode byte for a given chain is discussed in §10.

### B-03: Frame module always takes the first ARBITRARY entry (Low)

The module stopped at the first entry with scheme 0 and an empty msg, and frames had no way to
choose another. With two `SphincsFrameAccount`s in one transaction (`[only_verify(A), pay(B)]`),
both picked entry 0 and one always failed, whatever the order (shown in the emulator).
Soundness was intact. Note that a sponsoring SphincsFrameAccount reads its own storage, which
public-mempool rules forbid.

**Fix.** A new `verifyFrameAndApprove(uint256 sigIndex)` forwards an index. The module requires
`idx < len(signatures)` and an ARBITRARY entry with an empty msg at that index. The no-argument
variant keeps first-match. `compute_sig_hash` covers the frame data, so the witness commits to
the index. Tests: `test_Sponsored_BothAccountsApproveWithExplicitIndices`,
`test_Sponsored_FirstMatchCannotServeTheSponsor`, `test_Index_*` and
`test_VerifyFrameAndApprove_ForwardsKeysAndIndex`.

### B-04: SLH-DSA Diagnostic uses a stale H_msg (Low)

After SLH-X-f1 the verifier hashes `0x00‖0x00‖M` (a 0x52-byte inner hash). The Diagnostic still
hashed 0x50 bytes with no envelope, so it traced a FORS tree the verifier never computes:
leafIdx 1,432,635 against 2,085,853 on the pinned KAT. It also stored j=1..4 where its docstring
promised checkpoints c5/c11/c17/c22, and its test asserted nothing. This is debug-only and never
deployed.

**Fix:** use the verifier's envelope and store the documented checkpoints.
`DiagnosticTest.testTree0TraceMatchesVerifierPath` checks it against an independent `sha256`
reference that rebuilds `pkRoot` from the pinned KAT.

### B-05: C13 crosscheck points at a deleted path (Low)

`signers/c13-crosscheck/crosscheck.py` deployed `src/SPHINCs-C13Asm.sol`, which moved to
`src/keccak/` in `a99d0f9`. So its on-chain step (anvil plus `cast call` on the Python and Rust
signatures) died. No CI job runs it.

**Fix:** correct the path and add a prerequisite check. The full three-way run then printed
`OVERALL: PASS`. Regression: `C13CrosscheckPathTest.testCrosscheckVerifierSourceExists`.

## 5. Hardening (all applied)

- **H-01: keccak gates return false.** All 8 forced-zero and target-sum gates in keccak
  C7/C9/C10/C11 now return ABI `false`, matching C13 and the SHA and BLAKE twins. This closes
  L-01 of the previous review, which covered C11 only. It has no soundness effect, because
  callers already required success and a returned word of 1. Typed callers no longer see a
  bubbled revert. Tests: `test/helpers/SoundnessGates.sol`, used by
  `SphincsC7/C9/C10/C11Test`, covers both gates.
- **H-02: precompile presence.** A missing precompile answers with success and no data. On a
  chain without 0x09 every BLAKE output becomes the constant C16, so honest keys are silently
  bricked and old C12-BLAKE accepted any blob when `pkRoot == C16`. BLAKE now keeps an `ok` accumulator plus one `returndatasize() == 64` check
  before the compare. The SHA twins check `returndatasize() == 0x20` after the first (H_msg) call
  and before the compare (§6.1). Pitfall: Yul evaluates arguments right to left, so capture
  `let ok := staticcall(..)` before reading `returndatasize()`. SLH-DSA is report-only (its
  layout fails closed). Tests: `test/PrecompilePresenceTest.t.sol` (11); its pass-through
  forgeries verify true if the guards are removed.
- **H-03: BLAKE negative tests.** `RejectsWrongRoot` now flips bit 200 (canonical) instead of
  bit 0. New `RejectsCorruptedTopLayer` and `RevertsOnNonCanonicalKey` tests mean a
  `valid := 1` mutant of C11/C13-BLAKE now fails.
- **H-04: frame constructor.** It reverts `NonCanonicalKey`, `VerifierHasNoCode` or
  `FrameModuleHasNoCode`. A module of `address(0)` is still allowed.
- **H-05: factory.** `_check` (owner ≠ 0, root ≠ 0, canonical keys) also runs in `getAddress`.
  `createAccount` returns an existing account. EntryPoint v0.9 `getSenderAddress` works before
  and after deployment.
- **H-06: `SphincsAccount`.** Rejects a zero owner and a zero `pkRoot`; emits `KeysRotated` /
  `OwnerRotated`. Validation requires the verifier to return one 32-byte word equal to 1, and
  malformed blobs give `SIG_VALIDATION_FAILED` without reverting. A non-zero `pkSeed` check and
  proof of possession on `rotateKeys` were deliberately left out.
- **H-07: signer CLIs.** noble's hex parsing now matches the Python signers: optional `0x`, odd
  lengths left-padded, non-hex rejected. noble, fast, GPU and C12-SHA reject non-32-byte
  messages. The pure-Python FIPS reference signer only warns.

## 6. Residual assumptions and observations

### 6.1 SHA twins: precompile failure model (documented in code)

The new kernel writes each 0x02 output into the slot the next hash reads, and the calls are
`pop()`ed, so a call that fails without writing passes its input through. This is safe because
an absent 0x02 or a call-depth failure affects every call alike (the first-call check reverts
before any output is read); an out-of-gas call burns all it was forwarded (EIP-150), leaving at
most 5 gas, too little to reach another call or the compare; and the check before the compare
covers the call that produced the root.

**Residual assumption:** no 0x02 call fails mid-sequence without burning its gas (as a zkEVM
input-size limit might). The skeptic built a concrete forgery on the c11-sha vector (top-layer
`auth[5]` swapped for the honest height-6 node): if that one TREE call reverts
(`vm.mockCallRevert`) or returns no data, new code accepts; old code reverted or returned false;
with a real 0x02 both reject. The code comment says to restore per-call guards on such a chain.
The last-call check is load-bearing: without it a pass-through with `auth[7] = pkRoot` passes.

**Caught during review:** the first in-place-kernel patch checked only the first call, and a
forged signature per twin verified `true` under a mock that answered only H_msg. The applied
patch adds the last-call check. Tests: `test<Cx>ShaRejectsPassThroughForgeryWhenOnlyHmsgAnswers`,
and `test<Cx>ShaOutOfGasNeverReturnsFalse` (`test/helpers/OogSweep.sol`), which sweeps the 3,000
gas limits below the verifying minimum and never sees `false` (a mutant that holds gas back from
each call returned `false` 64 times).

### 6.2 BLAKE

Four 16-byte outputs rely on fresh zeroed memory for the low half of their slot (the last FORS
root, T_k slot 0x100 in C13 / 0x1C0 in C11, and the first FORS leaf's L/R slot). This holds in an
external call frame but is a maintenance hazard; an explicit `mstore(slot, 0)` costs about 3 gas.
The kernel uses `MCOPY`, so the BLAKE verifiers need Cancun (as the accounts and C9 already did)
and fail closed on older chains. Old code reverted at the first failed 0x09 call; new code
reverts only at the end, through the accumulator, so a failure followed by a gate could in
theory return false instead of reverting. Inputs always have the right shape, so it cannot.

## 7. Gas

Warm verifier gas from the vector harness (cold = warm + 2,500). The "after" column was re-run
on the final tree: all 14 vectors pass 3/3, and none of the 48 byte flips is accepted.

| Verifier | Before | After | Δ | Main changes |
|---|---:|---:|---:|---|
| C7 | 125,704 | 95,919 | −23.7% | T_k/T_l hashed in place, SWAR digit sum, ADRS-as-counter chains, incremental climbs |
| C9 | 109,548 | 82,798 | −24.4% | same |
| C10 | 114,302 | 86,804 | −24.1% | same |
| C11 | 114,382 | 86,854 | −24.1% | same |
| C12 | 262,355 | 203,885 | −22.3% | same; checksum as `301 − SWAR sum` |
| C13 | 106,788 | 106,788 | 0 | proof-coupled (§9) |
| C10-SHA | 186,421 | 140,991 | −24.4% | right-aligned ADRSc, in-place outputs, `pop()` + first/last presence check, N_MASK removal |
| C11-SHA | 187,095 | 141,389 | −24.4% | same |
| C12-SHA | 478,141 | 342,224 | −28.4% | same |
| C13-SHA | 173,665 | 131,075 | −24.5% | same |
| SLH-DSA-SHA2-128-24 | 146,308 | 146,308 | 0 | proof-coupled (§9) |
| C11-BLAKE | 2,786,058 | 135,026 | −95.2% | precomputed LE IV and counter, fixed F/H precompile buffers |
| C12-BLAKE | 7,796,886 | 313,667 | −96.0% | same |
| C13-BLAKE | 2,573,621 | 126,056 | −95.1% | same |

**Accounts** (real C13 vector, fresh tx per case; signature sliced from calldata, keys packed in
one slot): `validateUserOp` cold 130,894 → 121,769, warm 119,879 → 112,754; ECDSA-fail path warm
11,238 → 4,872; deploy 688,758 → 601,670. **Frame:** verify path 122,263 → 116,038 (no-arg) /
115,977 (indexed). Keys and verifier are account immutables forwarded to the module, which does
no SLOAD. Because the module now trusts its input it has a delegatecall-only guard; otherwise a
VERIFY frame aimed at the module itself could APPROVE with an attacker's keys
(`test_FrameModule_RejectsDirectCall`, `test_FrameModule_HasNoStorageOpcodes`).

| ID | Item (workflow slug) | Status |
|---|---|---|
| G-01 | BLAKE IV/counter as constants (`blake-kernel-runtime-iv-bswap`) | Applied, then superseded by G-02 |
| G-02 | BLAKE fixed F/H buffers (`blake-fixed-precompile-buffers`) | Applied |
| G-03 | SHA redundant N_MASK (`sha-twins-redundant-nmask`) | Applied, folded into G-04 |
| G-04 | SHA in-place kernel (`sha-twins-inplace-kernel`) | Applied to the twins; SLH-DSA report-only |
| G-05 | SHA in-place T buffers (`sha-twins-inplace-t-buffers`) | Subsumed by G-04; SLH-DSA report-only |
| G-06 | `pop()` + final presence check (`slh-gas-precompile-check`) | Applied to the twins (with first-call check); SLH-DSA report-only |
| G-07 | T_k/T_l hashed in place (`c7-c9-gas-copy-loops`) | Applied via G-11; C13 report-only; not needed in C12-BLAKE |
| G-08 | SWAR digit sum (`c7-c9-gas-swar-digit-sum`) | Applied via G-11 (keccak C7–C12); SHA twins not applied (≈ −6.7K) |
| G-09 | ADRS-as-counter chain loop (`c7-c9-gas-chain-loop-adrs-counter`) | Applied via G-11; C13 report-only |
| G-10 | Incremental auth climbs (`c7-c9-gas-auth-climb-incremental`) | Applied via G-11; C13 report-only |
| G-11 | Combined keccak rewrite (`c10c11-gas-combined`, loops kept) | Applied to C7–C12. Unrolled variant (≈ −40K, +1.2–1.9 KB runtime) not applied |
| G-12 | Frame keys as immutables (`frame-keys-in-storage-gas`) | Applied |
| G-13 | Account calldata slicing (`acct-gas-calldata-decode`) | Applied |
| G-14 | Account key packing (`acct-gas-pack-keys`) | Applied |

**Doc side effects.** C13 is no longer the cheapest verifier at 128-bit security: C7 is now
about 96K against C13's 105K. README and CLAUDE.md are updated accordingly, and their C12 and SHA
figures moved to the verifier-only basis, with the Forge e2e numbers alongside. The Frame and
4337 totals in the docs come from older deployments and are marked as not re-measured.

## 8. Old-vs-new equivalence

| Family | Method | Variants | Inputs compared | Outcome differences |
|---|---|---:|---:|---|
| Keccak C7–C12 | revm inspector recording every `KECCAK256` input and CALL-family op; cross-checked against Foundry debug-trace recording on 94 runs | 1,963 | 608,462 hash inputs, all identical | Intended only: old reverts empty, new returns `false` at a gate (1,054 variants, each re-checked by recomputing the gate). C12: none |
| SHA twins | state-diff recording of every precompile access | 1,364 | about 535,000 0x02 inputs, all identical | Only with 0x02 absent: old false, new revert |
| BLAKE | state-diff recording of every 0x09 access; an independent Python model predicted every outcome and call count | 1,192 | 642,783 0x09 calls, all identical | Only with 0x09 absent on C12: old false, new revert (475) |

Tampered variants were re-ground (R or message, then the per-layer count) so they pass the gates
and reach the root compare. The SHA and BLAKE harnesses each flagged an injected one-line bug (SHA
odd-leaf slot, BLAKE h+2 height word). **Skeptic pass:** per family, the diff was read by hand
and old was fuzzed against new with the gates removed so random inputs ran the full path (keccak
3,000 runs per verifier, and the SWAR sum matched the loop on 800,093 values; SHA 1,000 runs, every-byte
bit flips, and a gas-limit sweep from 0 to full cost + 300 with no wrong verdict; BLAKE 300 runs,
which caught an injected one-byte `t_0` mutation). No semantic change beyond the intended ones
was found. **Not covered:** BLAKE under limited gas (new code is about 20× cheaper, so its
out-of-gas behaviour is bound to differ).

## 9. Report-only: proof-coupled verifiers

Measured but not applied: these changes need the `verity/` model and proofs updated first. The
patch files were kept in the review scratch area, not in this tree.

**C13 keccak** (baseline 106,788)

| Item | Saving |
|---|---:|
| Hash T_k/T_l in place | ≈ −7.2K to −7.5K |
| SWAR digit sum | ≈ −6.2K |
| ADRS hash address as chain-loop counter | ≈ −4.4K to −4.9K |
| Incremental FORS + hypertree climbs | ≈ −7.6K |
| **All four, loops kept** | **−26,334** |
| All four, fixed-length auth loops unrolled (runtime 1,191 → 3,343 B) | −37,210 |
| `optimizer_runs = 1_000_000`, no source change | 106,788 → 97,414 (−9,374) |

The `optimizer_runs` effect comes from solc rebuilding `N_MASK` at about 600 sites under
`runs = 200`. Changing it touches every contract, so it is noted rather than applied. The
combined rewrite accepted four Rust-signer vectors and rejected all 3,688 single-bit mutants
with the same return data as the current code.

**SLH-DSA-SHA2-128-24** (baseline 146,308)

| Item | Saving |
|---|---:|
| In-place kernel | −35,587 rolled / −46,210 unrolled |
| In-place T_k/T_l buffers | −6,641 |
| `pop()` guards + one final `returndatasize` check | −4,042 |
| 2-bit SWAR checksum | −688 |
| All combined | 108,417 rolled (1,207 B) / 95,119 unrolled (3,965 B); 91,842 unrolled with `pop()` |
| Presence check alone | +21 |

If SLH-DSA adopts the in-place kernel, it must take both the first-call and last-call presence
checks and inherits the assumption in §6.1. Its current layout fails closed when 0x02 is absent.

## 10. EIP-8141: SIGPARAM copy or SIGDATACOPY?

**Verdict.** The applied `SIGDATACOPY 0xb5` form (`80600390b460006100a4b5`) matches the current
EIP-8141 text (`ead1a36` through `af3a780`) and the ethrex `frames-devnet-0/1` /
`hegota-testnet-hotfix` builds: the privacy testnet (chain 8141, confirmed with read-only
`eth_call` opcode fingerprints) and the frames testnet (chain 81410, source only; its RPC
returns 502). No live network implements the pre-review blob's 07-28 operand order.

**Chain 3151908 is the exception.** The repo docs name it, but it has been recut: the
`*.eip-8141.ethrex.xyz` names are NXDOMAIN and the id now belongs to the Hegotá devnet
(`*.hegota.ethrex.xyz`, genesis 2026-08-06). There 0xB5 is `RECENTROOTREFLOAD` (EIP-8272),
`SIGDATACOPY` sits at 0xBA, and the SIGPARAM copy exists in the 07-30 operand order. The applied
blob halts there; the pre-review blob runs with swapped operands (copies 164 bytes to offset
`len`), so verification fails and nothing is approved. The 2026-06-04 frame account the docs
cite never used SIGPARAM: it was the hand-assembled calldata runtime from
`legacy/script/deploy_frame_account.py`, on a chain that is gone.

**Recommendation.**
- Make `sigCopyToArgs`, the only blob that differs between targets, a build-time choice: "spec"
  (default, the current `…b5`) or "ethrex-hegota-devnet" (`80600390b460006100a4ba`, marked as a
  temporary ethrex-local byte). Drop the 07-28 blob.
- The module is immutable, so the deploy script should map chain id to variant and probe first:
  `eth_call` of `0x60006000b5` (spec) or `0x60006000ba` (Hegotá) must answer "Stack Underflow".
  Refuse to deploy on a mismatch.
- Update `script/send_frame_tx_c13.py` (June envelope, dead RPC) to the current 11-field envelope
  with an ARBITRARY `signatures` entry, and mark the README's ethrex 3151908 rows defunct.

All three networks run `--mempool.max-verify-gas 500000`, so a C13 VERIFY frame fits.

## 11. Compatibility, tests and open items

**Compatibility.** Every changed verifier has new bytecode and must be redeployed for the
savings; deployed verifiers keep their old, sound code. C12 / C12-BLAKE signer output changed
(rotate, B-01). `SphincsAccount` packs its keys, so its CREATE2 addresses differ from the Sepolia
factory's. `SphincsFrameAccount` keys are immutables and the module input ABI is new (0x60 / 0x80
bytes), so deploy account and module together. BLAKE needs Cancun; with the precompile absent,
the SHA twins and C12-BLAKE now revert instead of returning false.

**Tests on the final tree.** Vector harness 14/14 (3/3 each). Forge, in a private offline copy:
25 suites, 137/137, covering the keccak C7–C12, SHA-twin and BLAKE e2e suites, the SLH KAT and
JsonKAT suites, `AdvVerifyPaddingProbe`, the account suites (`SphincsAccountAccessControlTest`,
`SphincsAccountC13Test`, `SphincsFrameAccountC13Test`), and the seven new or rewritten suites
(C12 FORS binding, PrecompilePresence, FrameModuleEmu, AccountHardening, C13CrosscheckPath,
Diagnostic, Blake2bKernel). Earlier in the workflow: legacy C12 5/5 and the C13 three-way
crosscheck `OVERALL: PASS`. **Not run:** `SphincsC13Test` (verifier and signer unchanged) and
`SLH_DSA_SHA2_128_24_Test` / `CalldataGas` (need the unbuilt C signer and an 11-minute sign;
that verifier is unchanged and its KATs pass).

**Open items.**
1. Rotate every C12 / C12-BLAKE key that has signed (B-01). Port the fix to nconsigny/JARDIN,
   and add a rotation warning next to the README's C12 compatibility note.
2. EIP-8141: the build-time copy variant, the pre-deploy probes, `send_frame_tx_c13.py`, and the
   stale README rows (§10).
3. Port the proof-coupled savings (§9) only after updating `verity/`. SLH-DSA must take both
   presence checks.
4. Add a CI job for `signers/c13-crosscheck`.
5. Make the BLAKE zeroed-memory assumptions explicit (§6.2).
6. Re-measure the Frame and 4337 totals after redeploying.

---
*Method:* 14 finders, deduplication, then one refute agent per finding with reproduction (48
agents in the main workflow). Then patch rebasing, trace-equivalence and skeptic passes per
family, and EIP-8141 source and RPC research. The lead reviewer re-ran the vector harness and
the affected Forge suites on the final tree.
