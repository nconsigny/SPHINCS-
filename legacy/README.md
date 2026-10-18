# legacy/

Frozen historical artifacts. Nothing in the live `src/` / `test/` tree imports
them (the one exception is the keccak entry of
`script/DeploySlhDsa128_24Sepolia.s.sol`, which imports
`../legacy/src/SLH-DSA-keccak-128-24verifier.sol`). They are kept for
reproducibility of prior benchmarks, as a reference for the JARDIN 32-byte ADRS /
hash conventions they share, and as an escape hatch if someone needs to redeploy
an earlier variant.

**`SLH-DSA-keccak-128-24verifier.sol`** was retired here when the repo
standardized on the two FIPS 205 ADRS layouts (uncompressed 32 B + keccak,
ADRSc 22 B + SHA-2): it stayed on the JARDIN 32-byte ADRS layout and was never
migrated.

**C10, C11 and C12 were migrated** to the FIPS uncompressed layout and now live
in `src/keccak/` (`SPHINCs-C10Asm.sol`, `SPHINCs-C11Asm.sol`,
`SPHINCs-C12Asm.sol`) as live verifiers; C10 was promoted last, together with
its SHA-2 twin in `src/sha/`. Their JARDIN-layout originals
(`SPHINCs-C10Asm.sol`, `SPHINCs-C11Asm.sol`, `SPHINCs-C12Asm.sol` here) are kept
frozen for benchmark reproducibility and because the JARDIN-layout C12 is
cross-referenced verbatim by the JARDIN repo as `JardinSpxVerifier`.

The JARDIN-mode off-chain signers (`script/jardin_spx_signer.py`,
`signers/jardin-keccak-128-24/` + `script/slh_dsa_keccak_128_24_fast_signer.py`,
and `script/signer.py` variants `c6` / `c8` / `c10` / `c11-jardin`) are unchanged. The
legacy tests FFI-call them by repo-root path (`script/...`), so they stay in
`script/`. The migrated FIPS C12 has its own signer at `script/spx_fips_signer.py`.

## What's here

### `legacy/src/` — Solidity verifiers

| File | What it is |
|---|---|
| `SPHINCs-C6Asm.sol`, `SPHINCs-C8Asm.sol`, `SPHINCs-C10Asm.sol`, `SPHINCs-C11Asm.sol` | Stateless SPHINCs- WOTS+C + FORS+C verifiers (n=128, d=2), JARDIN 32-byte ADRS. C10/C11 have FIPS-layout successors in `src/keccak/`. |
| `SPHINCs-C12Asm.sol` | Plain SPHINCS+ (SPX) verifier, JARDIN 32-byte ADRS. 6,512-B sig, ~276 K verify. `JardinSpxVerifier` in the JARDIN repo. |
| `SLH-DSA-keccak-128-24verifier.sol` | JARDIN-convention Keccak twin of SLH-DSA-128-24 (keccak opcode, 32-byte ADRS). The SHA-2 twin stays live in `src/sha/`. |

### `legacy/script/` — Off-chain signers, UserOp builders, deploy scripts

| File | What it is |
|---|---|
| `signer.py` | Frozen snapshot of the Python C-series signer (variants c2 / c6 / c7 / c8 / c9 / c10 / c11 / c13). Imported by `send_userop.py`; the maintained signer is `script/signer.py`. |
| `send_userop.py` | Original hybrid ERC-4337 UserOp builder (uses `legacy/script/signer.py`). |
| `deploy_frame_account.py` | Legacy EIP-8141 frame account deployer (imports the maintained `script/signer.py`). |
| `DeploySepolia.s.sol` | Deploy script for a shared C6 verifier + `SphincsAccountFactory`. Does not compile as-is: it imports `../src/SphincsAccountFactory.sol`, which is not in `legacy/src/` (the factory lives in the root `src/`). |
| `sweep_d2_fluhrer_dang.py` | One-off research helper: constrained parameter sweep (FORS+C / PORS+FP). |

### `legacy/test/` — Foundry tests for the frozen contracts

| File | Covers |
|---|---|
| `SphincsC8Test.t.sol`, `SphincsC10Test.t.sol`, `SphincsC11Test.t.sol` | JARDIN-layout C8 / C10 / C11 verifiers. |
| `SphincsC12Test.t.sol` | JARDIN-layout plain SPHINCS+ C12 verifier. |
| `SLH-DSA-Keccak-128-24-CalldataGas.t.sol`, `SLH-DSA-keccak-128-24-Test.t.sol` | Keccak SLH-DSA-128-24 twin (calldata-gas + FFI round-trip). |

These tests are not compiled by the default `forge test` run (Foundry only
scans `test/` at the project root). Run them from the repo root with
`FOUNDRY_TEST=legacy/test forge test` (the CI `legacy-verifiers` job does
exactly this); the root working directory matters because the FFI signer paths
are repo-root-relative.

## Why they're kept

The JARDIN-layout verifiers here share one 32-byte ADRS layout and one set of
tweakable hash primitives (`script/jardin_primitives.py::th / th_pair /
th_multi`), the same kernel the nconsigny/JARDIN repo still uses; they differ
only in parameters. Keeping them in-tree makes it obvious when a future tweak to
the shared primitives is a breaking change for a deployed verifier.
