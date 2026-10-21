# Off-chain signers

Every signer here is **off-chain and untrusted**. The on-chain verifiers are
stateless and pure — they re-check a signature from scratch on every call, so a
signer can only ever produce something the verifier accepts or rejects; it is
never an authority. The reason there are *many* implementations (Solidity ⟷ C ⟷
Rust ⟷ JS ⟷ Python) is **cross-validation**: agreement byte-for-byte across
independent code bases is the evidence that the on-chain verifier is correct.

Signers live in two places: language-native projects under `signers/` (this
directory), and thin Python drivers/reference signers under `script/`.

## Which signer for which verifier

| Verifier | Signer | Lang | Location | Notes |
|---|---|---|---|---|
| **C7 / C9 / C10 / C11 / C13** (`src/keccak/`, WOTS+C/FORS+C) | `signer.py` | Python | `script/signer.py` | Live variants `c7` / `c9` / `c10-fips` / `c11` / `c13` (`adrs_mode=fips`); `c6` / `c8` / `c10` / `c11-jardin` drive the JARDIN-layout `legacy/` verifiers. Slow. |
| **C13** | `signer-c13` + WASM | Rust | `signers/signer-wasm/` | Crate `sphincs-c13-signer`. CLI `signer-c13` is the fast path for the C13 forge FFI tests; `lib.rs` is the WASM signer (BIP-39/44 derivation). |
| **C13** (validation only) | `crosscheck.py` | Python | `signers/c13-crosscheck/` | Three-way Python ⟷ Rust ⟷ verifier byte-equality. |
| **C12** (plain SPHINCS+, `src/keccak/`) | `spx_fips_signer.py` | Python | `script/` | FIPS-ADRS twin of `jardin_spx_signer.py` (reuses it with `l=46`). |
| **C10-SHA / C11-SHA / C13-SHA** (`src/sha/`) | `signer.py` | Python | `script/signer.py` | Variants `c10-sha` / `c11-sha` / `c13-sha` (SHA-256 + 22-byte ADRSc; not FIPS). |
| **C12-SHA** (`src/sha/`) | `slh_dsa_sha2_c12_signer.py` | Python | `script/` | Full FIPS 205 SLH-DSA-SHA2 algorithm at the C12 parameters. |
| **C11-BLAKE / C13-BLAKE** (`src/blake/`) | `signer.py` | Python | `script/signer.py` | Variants `c11-blake` / `c13-blake` (BLAKE2b, FIPS uncompressed ADRS). |
| **C12-BLAKE** (`src/blake/`) | `spx_blake_signer.py` | Python | `script/` | BLAKE2b twin of `spx_fips_signer.py`. |
| **SLH-DSA-SHA2-128-24** (`src/sha/`, live) | `slh_dsa_sha2_128_24_signer.py` | Python | `script/` | Pure-Python FIPS-205 reference. Hours at NIST params — use `--height/--a` for dev. |
| ″ | C reference | C | `signers/sphincsplus-128-24/` | Fork of sphincs/sphincsplus, `w=4` added. ~1–3 min/sign. Backend for the fast signer + the FIPS oracle. |
| ″ | `slh_dsa_sha2_128_24_fast_signer.py` | Python | `script/` | Wrapper: JARDIN key derivation → C binary → disk cache. Used by the forge FFI tests. |
| ″ | `slh_dsa_sha2_128_24_signer.mjs` | JS | `signers/noble-slh-dsa/` | Patched `@noble/post-quantum`. Drop-in for the fast signer; validated byte-for-byte vs the C ref and the pinned on-chain KAT. |
| ″ | `slhdsa-sha2-128-24-gpu` | C + Vulkan | `signers/slhvk-sha2-128-24/` | GPU-accelerated SLH-DSA (conduition `slhvk` fork). Driven by `script/slh_dsa_sha2_128_24_gpu_signer.py`. |
| **SLH-DSA-Keccak-128-24** (`legacy/`, retired) | `slh_dsa_keccak_128_24_signer.py` / C fork | Python / C | `script/`, `signers/jardin-keccak-128-24/` | JARDIN-convention keccak twin + its `*_fast_signer.py` wrapper. Frozen. |
| **C12** (plain SPHINCS+, `legacy/`, retired, JARDIN ADRS) | `jardin_spx_signer.py` | Python | `script/` | Self-contained; shares `jardin_primitives.py` with the JARDIN repo. |
| **leanSphincs-23** (`legacy/src/LeanSphincs-23Asm.sol`, legacy, superseded by leanSphincs-s) | `ls23k` | Rust | `signers/leansphincs23-keccak/` | Port of the upstream leanSphincs crate, keccak256 for BLAKE2s. Pruned keys (`b` = kept-subtree height); fast path for the forge FFI tests and the KAT fixture. Tiered signer: `keygen` stores the key once in a key file with a bounded node cache (Light / Standard / Full), `sign-key` signs from it, byte-identical to `sign`. |
| ″ | `leansphincs23_signer.py` | Python | `script/` | Independent, written from `legacy/docs/leanSphincs-23-keccak.md`. Practical for `b ≈ 6..12`. |
| **leanSphincs-s** (`src/keccak/LeanSphincs-SAsm.sol`, keccak) | `lssk` | Rust | `signers/leansphincs-s-keccak/` | Port of the upstream crate's `keccak` branch (h=26, no FORS key hash), by way of `ls23k`, whose tiers, key file and CLI it keeps. Counts keccak calls and Keccak-f permutations. Fast path for the forge FFI tests and the KAT fixture. |
| ″ | `leansphincs_s_signer.py` | Python | `script/` | Independent, written from `docs/leanSphincs-S-keccak.md`; `--upstream-kat` reproduces the upstream keccak branch's `known_answer`. Practical for `b ≈ 6..12`. |
| **leanSphincs-f** (`src/keccak/LeanSphincs-FAsm.sol`, keccak) | `lsfk` | Rust | `signers/leansphincs-f-keccak/` | leanSphincs-s re-parameterized to `a = 9`, `k = 20`, `T = 122` (one-call digest, seven 9-bit indices per word; 4,660-B sig), by way of `lssk`, whose tiers, key-file layout and CLI it keeps (magic `LS-FKKEY`). Fast path for the forge FFI tests and the KAT fixture. |
| ″ | `leansphincs_s_signer.py --variant f` | Python | `script/` | The same independent signer at the f parameters, written from `docs/leanSphincs-f-keccak.md`. Practical for `b ≈ 6..12`. |
| **leanSphincs** (`src/keccak/LeanSphincsAsm.sol`, keccak) | `lsk` | Rust | `signers/leansphincs-keccak/` | The upstream crate's `keccak` branch at its own parameters (`a = 10`, `k = 24`, `T = 120`, two-call digest; 5,684-B sig); its `known_answer` passes unchanged. Tiers, key-file layout and CLI as `lssk` (magic `LS-KKKEY`). Fast path for the forge FFI tests and the KAT fixture. |
| ″ | `leansphincs_s_signer.py --variant regular` | Python | `script/` | The same independent signer at the upstream parameters (`docs/leanSphincs-keccak.md`); reproduces upstream's `known_answer` (also via `--upstream-kat`). Practical for `b ≈ 6..12`. |

## `signers/` directory contents

- **`signer-wasm/`** — Rust crate `sphincs-c13-signer`. Bin `signer-c13`
  (`sign` / `keygen` / `sign-with` subcommands) is the fast C13 signer the forge
  FFI tests probe for; the `cdylib` is the browser WASM signer with BIP-39 →
  HMAC-SHA-512 key derivation. Build: `cd signers/signer-wasm && cargo build --release`.
- **`sphincsplus-128-24/`** — C fork of the SPHINCS+ reference for the live
  SLH-DSA-SHA2-128-24 set (`n=16,h=22,d=1,a=24,k=6,w=4`). FIPS 205 external,
  SHA-256, 22-byte ADRSc. `params.h` heights are `-D`-overridable for fast
  reduced-param cross-checks. `crosscheck.py` here is the Python↔C parity test.
- **`noble-slh-dsa/`** — pure-JS SLH-DSA-SHA2-128-24 signer on a 6-edit-patched
  `@noble/post-quantum`. Independent third implementation; see its `README.md`.
- **`slhvk-sha2-128-24/`** — Vulkan compute-shader SLH-DSA signer for the SHA-2
  set; GPU-accelerated keygen/sign. See its `README.md` / `STATUS.md`.
- **`jardin-keccak-128-24/`** — C fork for the **retired** SLH-DSA-Keccak twin
  (JARDIN 32-byte ADRS, native `keccak256`). Kept reproducible for `legacy/`.
- **`c13-crosscheck/`** — Python harness that cross-validates the C13 Python and
  Rust signers against each other (and the verifier) at full parameters.
- **`leansphincs23-keccak/`** — legacy (verifier in `legacy/src`, superseded by
  leanSphincs-s). Rust crate for leanSphincs-23 over keccak256
  (`h=25,d=1,k=13,a=12`, WOTS+C `T=128`, 4,148-B sig). Bin `ls23k`
  (`sign` / `kat` / `verify`, and the tiered signer's `keygen` / `sign-key` /
  `info`: seed from `--seed-file` or `--seed-stdin`, never argv; the key file
  holds it; one seed, one key). `crosscheck.py` holds it to byte equality with
  the Python signer; `make_kat_fixture.py` writes the legacy Forge KAT fixture;
  `tier_model.py` is the sphincs-art tier cost model. See its `README.md` and
  spec §14. Build: `cd signers/leansphincs23-keccak && cargo build --release`.
- **`leansphincs-s-keccak/`** — Rust crate for leanSphincs-s over keccak256
  (`h=26,d=1,k=13,a=12`, WOTS+C `T=128` over the 26 FORS tops, no FORS key
  hash; 4,164-B sig). Bin `lssk`, with `ls23k`'s subcommands and tiers (Full is
  the whole `2^26` tree). Its key files are not `ls23k`'s, and a seed must never
  serve both schemes. `crosscheck.py`, `make_kat_fixture.py` and `tier_model.py`
  as for leanSphincs-23 (the model in both keccak calls and Keccak-f
  permutations). See its `README.md` and spec §14. Build:
  `cd signers/leansphincs-s-keccak && cargo build --release`.
- **`leansphincs-f-keccak/`** — Rust crate for leanSphincs-f over keccak256
  (`h=26,d=1,k=20,a=9`, WOTS+C `T=122` over the 40 FORS tops; 4,660-B sig). Bin
  `lsfk`, with `lssk`'s subcommands, tiers and tooling (`crosscheck.py`,
  `make_kat_fixture.py`, `tier_model.py`). See its `README.md` and
  `docs/leanSphincs-f-keccak.md`. Build:
  `cd signers/leansphincs-f-keccak && cargo build --release`.
- **`leansphincs-keccak/`** — Rust crate for leanSphincs over keccak256, the
  upstream keccak branch at its own parameters (`h=26,d=1,k=24,a=10`, WOTS+C
  `T=120` over the 48 FORS tops, two-call digest; 5,684-B sig). Bin `lsk`, with
  `lssk`'s subcommands, tiers and tooling; its `tier_model.py` quotes the
  proposal's Lean-proved lifetimes. See its `README.md` and
  `docs/leanSphincs-keccak.md`. Build:
  `cd signers/leansphincs-keccak && cargo build --release`.

Each leanSphincs CLI (`ls23k`, `lssk`, `lsfk`, `lsk`) has its own key-file
magic and refuses the others' key files. They all derive the same one-time keys
from a seed, so one seed is one key of one variant: never reuse a seed across
variants or tiers.

## Cross-validation map

- **C13**: `signers/c13-crosscheck/crosscheck.py` (Py ↔ Rust), plus the Rust
  `signers/signer-wasm/tests/cross_validate.rs` oracle and the WOTS+C/FORS+C
  reuse PoCs.
- **SLH-DSA-SHA2-128-24**: `signers/sphincsplus-128-24/crosscheck.py` (Py ↔ C),
  `signers/noble-slh-dsa/crosscheck.mjs` (noble ↔ C) and `kat-check.mjs`
  (noble ↔ pinned on-chain KAT), plus the Forge KAT
  (`test/SLH-DSA-SHA2-128-24-KAT.t.sol`).
- **leanSphincs-23**: `signers/leansphincs23-keccak/crosscheck.py` (Rust ↔
  Python, plus a spec-literal third recomputation), and the legacy Forge KAT fixture
  `legacy/test/fixtures/leansphincs23-keccak-kat.json` (`make_kat_fixture.py --check`).
  The tiered `sign-key` is held to `ls23k sign` byte for byte (the crate's
  tests, the Forge FFI test `testVerifyFFI_RustLightTierKeyFile`, CI), and its
  call counts to `tier_model.py`.
- **leanSphincs-s**: `signers/leansphincs-s-keccak/crosscheck.py` (Rust ↔
  Python, plus a spec-literal third recomputation), the Python signer's
  `--upstream-kat` (the upstream keccak branch's `known_answer` at its own
  parameters), and the Forge KAT fixture
  `test/fixtures/leansphincs-s-keccak-kat.json` (`make_kat_fixture.py --check`).
  `sign-key` is held to `lssk sign` as for leanSphincs-23.
- **leanSphincs-f** / **leanSphincs**: the same, per crate
  (`signers/leansphincs-f-keccak/crosscheck.py` against `--variant f`,
  `signers/leansphincs-keccak/crosscheck.py` against `--variant regular`), the
  Forge KAT fixtures `test/fixtures/leansphincs-f-keccak-kat.json` and
  `test/fixtures/leansphincs-keccak-kat.json`, and `sign-key` held to `lsfk sign`
  / `lsk sign`. For leanSphincs, both `lsk` and the Python signer also reproduce
  the upstream `known_answer` (pk `63b1…cd00`, `keccak256(sig)` `9a21…f94d`,
  counter 1176).

CI (`.github/workflows/ci.yml`) runs the fast cross-checks (`rust-signer`, and
`slh-crosscheck` / `noble-crosscheck` at reduced parameters; `leansphincs23`,
`leansphincs-s`, `leansphincs-f` and `leansphincs` at full parameters on pruned
keys), the full forge suite (`solidity`) and the frozen `legacy/` suites
(`legacy-verifiers`) on every push to `main` and on every pull request.

> **Not audited, not production-safe.**
