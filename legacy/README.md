# legacy/

Frozen historical artifacts. Nothing here is imported by the current default
stack (SPX + plain-FORS + JardinAccount + JardineroFrameAccount); they're
kept for reproducibility of prior benchmarks, as a reference for the
ADRS / hash conventions they share with the current verifiers, and as an
escape hatch if someone needs to redeploy an earlier variant.

**`SLH-DSA-keccak-128-24verifier.sol`** was retired here when the repo
standardized on the two FIPS 205 ADRS layouts (uncompressed 32 B + keccak,
ADRSc 22 B + SHA-2): it stayed on the JARDIN 32-byte ADRS layout and was never
migrated.

**C11 and C12 were migrated** to the FIPS uncompressed layout and now live in
`src/` (`src/SPHINCs-C11Asm.sol`, `src/SPHINCs-C12Asm.sol`) as live verifiers.
Their JARDIN-layout originals (`SPHINCs-C11Asm.sol`, `SPHINCs-C12Asm.sol` here)
are kept frozen for benchmark reproducibility and because the JARDIN-layout
C12 is cross-referenced verbatim by the JARDIN repo as `JardinSpxVerifier`.

The JARDIN-mode off-chain signers (`script/jardin_spx_signer.py`,
`signers/jardin-keccak-128-24/`, and `script/signer.py` in JARDIN `adrs_mode`)
and the keccak SLH-DSA deploy entry in `script/DeploySlhDsa128_24Sepolia.s.sol`
are unchanged and still point at these files via `../legacy/src/`. The migrated
FIPS C12 has its own signer at `script/spx_fips_signer.py`.

## What's here

### `legacy/src/` — Solidity verifiers and accounts

| File | What it is |
|---|---|
| `SPHINCs-C6Asm.sol` … `SPHINCs-C11Asm.sol` | Stateless SPHINCS+ / SPHINCs- WOTS+C + FORS+C verifiers (n=128, d=2). |
| `SPHINCs-C12Asm.sol` | Plain SPHINCS+ (SPX) verifier, JARDIN 32-byte ADRS. 6,512-B sig, ~276 K verify. `JardinSpxVerifier` in the JARDIN repo. |
| `SLH-DSA-keccak-128-24verifier.sol` | JARDIN-convention Keccak twin of SLH-DSA-128-24 (keccak opcode, 32-byte ADRS). SHA-2 twin stays live in `src/`. |
| `SphincsAccount.sol`, `SphincsAccountFactory.sol` | Original hybrid ECDSA + SPHINCs- ERC-4337 account and its factory. |
| `SphincsFrameAccount.sol` | Original EIP-8141 frame account wired to the C-series verifiers. |
| `JardinT0Verifier.sol` | JARDINERO T0 variant: plain FORS + WOTS+C hypertree (h=14 d=7 a=6 k=39). |
| `JardinForsCVerifier.sol` | JARDÍN compact-path variant 2: FORS+C (k=26 a=5) under balanced Merkle h ∈ [2, 8]. |
| `JardinFrameAccount.sol` | C11-based EIP-8141 frame account. |

### `legacy/script/` — Off-chain signers, UserOp builders, deploy scripts

| File | What it is |
|---|---|
| `signer.py` | Python signer for the SPHINCs- C-series (c2 / c6 / c7). |
| `jardin_signer.py` | JARDÍN FORS+C signer (k=26 a=5). Primitives previously shared with `jardin_fors_plain_signer.py` — those now live in `script/jardin_primitives.py`. |
| `jardin_t0_signer.py` | JARDINERO T0 signer. |
| `jardin_userop.py` / `jardin_t0_userop.py` | 4337 UserOp builders for the C11 and T0 variants (Candide bundler). |
| `jardin_frame_tx.py` / `jardin_frame_cycle.py` | EIP-8141 frame tx builders for the C11 variant. |
| `deploy_frame_account.py` | Legacy frame account deployer (ELT-era). |
| `send_userop.py` | Original sphincs-c6 UserOp builder. |
| `DeploySepolia.s.sol` | Deploy script for the `Sphincs*Account` family. |
| `jardin_cycle.sh`, `jardin_cast_verify.sh`, `jardin_call_verifier.py`, `sweep_d2_fluhrer_dang.py` | One-off research / verification helpers. |

### `legacy/test/` — Foundry tests for the frozen contracts

| File | Covers |
|---|---|
| `SphincsC8Test.t.sol` … `SphincsC11Test.t.sol` | Stateless SPHINCs- C8–C11 verifiers. |
| `SphincsC12Test.t.sol` | Plain SPHINCS+ C12 verifier. |
| `SLH-DSA-Keccak-128-24-CalldataGas.t.sol`, `SLH-DSA-keccak-128-24-Test.t.sol` | Keccak SLH-DSA-128-24 twin (calldata-gas + FFI round-trip). FFI signer paths under `script/` / `signers/` are unchanged. |
| `JardinT0Test.t.sol` | T0 verifier standalone. |
| `JardinForsCTest.t.sol`, `JardinForsCVariableHTest.t.sol` | FORS+C verifier (fixed and variable-h). |

These tests are not compiled by the default `forge test` run (Foundry only
scans `test/` at the project root); to run them, copy the relevant `.sol`
files back into `test/` and update the `../src/` imports to
`../legacy/src/`, or invoke Foundry with an explicit path.

## Why they're kept

The JARDÍN family shares one 32-byte ADRS layout and one set of tweakable
hash primitives (`script/jardin_primitives.py::th / th_pair / th_multi`)
across every verifier here — the legacy C-series and FORS+C variants are
the same crypto kernel as the current SPX + plain-FORS pair, just with
different parameters. Keeping them in-tree makes it obvious when a future
tweak to the shared primitives is a breaking change for a deployed verifier.
