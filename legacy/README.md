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

**leanSphincs-23** (`LeanSphincs-23Asm.sol`) was retired here when leanSphincs-S
(`src/keccak/LeanSphincs-SAsm.sol`, spec `docs/leanSphincs-S-keccak.md`) superseded it:
the sphincs-art leanSphincs set gained one tree level (h = 25 → 26, rated 2^26 for the
Full tier) and moved to the upstream crate's `keccak` branch construction, whose merged
WOTS+C encoding absorbs the FORS tops directly (no FORS key hash). It is not a SPHINCS+
ADRS scheme and does not share the JARDIN kernel; it keeps leanSphincs's own 16-byte
tweak. Its spec moved with it (`legacy/docs/leanSphincs-23-keccak.md`), and so did its
Forge suites and their KAT fixture (`legacy/test/fixtures/leansphincs23-keccak-kat.json`).
Its signers stay where they are: the Rust crate `signers/leansphincs23-keccak` (`ls23k`,
whose `make_kat_fixture.py` now writes the fixture under `legacy/test/fixtures`) and the
Python `script/leansphincs23_signer.py`; the CI `leansphincs23` job still runs their
cargo tests, the Rust ↔ Python crosscheck, `make_kat_fixture.py --check` and these Forge
suites. Never reuse a leanSphincs-23 seed for leanSphincs-S.

## What's here

### `legacy/src/` — Solidity verifiers

| File | What it is |
|---|---|
| `SPHINCs-C6Asm.sol`, `SPHINCs-C8Asm.sol`, `SPHINCs-C10Asm.sol`, `SPHINCs-C11Asm.sol` | Stateless SPHINCs- WOTS+C + FORS+C verifiers (n=128, d=2), JARDIN 32-byte ADRS. C10/C11 have FIPS-layout successors in `src/keccak/`. |
| `SPHINCs-C12Asm.sol` | Plain SPHINCS+ (SPX) verifier, JARDIN 32-byte ADRS. 6,512-B sig, ~276 K verify. `JardinSpxVerifier` in the JARDIN repo. |
| `SLH-DSA-keccak-128-24verifier.sol` | JARDIN-convention Keccak twin of SLH-DSA-128-24 (keccak opcode, 32-byte ADRS). The SHA-2 twin stays live in `src/sha/`. |
| `LeanSphincs-23Asm.sol` | leanSphincs-23 over keccak256 (n=16, h=25, d=1, FORS k=13 a=12, WOTS+C T=128; 4,148-B sig, ~39 K verify, 249 keccak256 calls). leanSphincs's own 16-byte tweak, not a FIPS ADRS. Superseded by `src/keccak/LeanSphincs-SAsm.sol`. |

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
| `LeanSphincs23Test.t.sol`, `SphincsAccountLeanSphincs23Test.t.sol` | leanSphincs-23 verifier (KATs, tampering, spec model, random digests, gas ceiling, `ls23k` FFI round-trips) and the `SphincsAccount` wired to it. Read `fixtures/leansphincs23-keccak-kat.json` (allowed by `fs_permissions` in `foundry.toml`); the FFI tests need `ls23k` built (`cd signers/leansphincs23-keccak && cargo build --release`). |

These tests are not compiled by the default `forge test` run (Foundry only
scans `test/` at the project root). Run them from the repo root with
`FOUNDRY_TEST=legacy/test forge test` (the CI `legacy-verifiers` job does
exactly this); the root working directory matters because the FFI signer paths
are repo-root-relative. For one suite, e.g. leanSphincs-23:
`FOUNDRY_TEST=legacy/test forge test --match-contract LeanSphincs23 -vv`.

### `legacy/docs/` — Specs of retired schemes

| File | What it is |
|---|---|
| `leanSphincs-23-keccak.md` | The leanSphincs-23 keccak256 instantiation that `legacy/src/LeanSphincs-23Asm.sol`, `signers/leansphincs23-keccak` and `script/leansphincs23_signer.py` implement ("the spec" in their comments). Frozen; its successor is `docs/leanSphincs-S-keccak.md`. |

## Why they're kept

leanSphincs-23 is kept so the leanSphincs-S delta (`docs/leanSphincs-S-keccak.md`) stays
checkable against a working predecessor, and because its signer crate is the base the
leanSphincs-S crate was derived from.

The JARDIN-layout verifiers here share one 32-byte ADRS layout and one set of
tweakable hash primitives (`script/jardin_primitives.py::th / th_pair /
th_multi`), the same kernel the nconsigny/JARDIN repo still uses; they differ
only in parameters. Keeping them in-tree makes it obvious when a future tweak to
the shared primitives is a breaking change for a deployed verifier.
