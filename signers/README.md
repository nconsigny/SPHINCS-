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
| **C7 / C9 / C13** (`src/`, keccak, WOTS+C/FORS+C) | `signer.py` | Python | `script/signer.py` | C6–C13; `adrs_mode` = `fips` (live) or `jardin` (legacy). Slow. |
| **C13** | `signer-c13` + WASM | Rust | `signers/signer-wasm/` | Crate `sphincs-c13-signer`. CLI `signer-c13` is the fast path for the C13 forge FFI tests; `lib.rs` is the WASM signer (BIP-39/44 derivation). |
| **C13** (validation only) | `crosscheck.py` | Python | `signers/c13-crosscheck/` | Three-way Python ⟷ Rust ⟷ verifier byte-equality. |
| **SLH-DSA-SHA2-128-24** (`src/`, live) | `slh_dsa_sha2_128_24_signer.py` | Python | `script/` | Pure-Python FIPS-205 reference. Hours at NIST params — use `--height/--a` for dev. |
| ″ | C reference | C | `signers/sphincsplus-128-24/` | Fork of sphincs/sphincsplus, `w=4` added. ~1–3 min/sign. Backend for the fast signer + the FIPS oracle. |
| ″ | `slh_dsa_sha2_128_24_fast_signer.py` | Python | `script/` | Wrapper: JARDIN key derivation → C binary → disk cache. Used by the forge FFI tests. |
| ″ | `slh_dsa_sha2_128_24_signer.mjs` | JS | `signers/noble-slh-dsa/` | Patched `@noble/post-quantum`. Drop-in for the fast signer; validated byte-for-byte vs the C ref and the pinned on-chain KAT. |
| ″ | `slhdsa-sha2-128-24-gpu` | C + Vulkan | `signers/slhvk-sha2-128-24/` | GPU-accelerated SLH-DSA (conduition `slhvk` fork). Driven by `script/slh_dsa_sha2_128_24_gpu_signer.py`. |
| **SLH-DSA-Keccak-128-24** (`legacy/`, retired) | `slh_dsa_keccak_128_24_signer.py` / C fork | Python / C | `script/`, `signers/jardin-keccak-128-24/` | JARDIN-convention keccak twin + its `*_fast_signer.py` wrapper. Frozen. |
| **C12** (plain SPHINCS+, `legacy/`, retired) | `jardin_spx_signer.py` | Python | `script/` | Self-contained; shares `jardin_primitives.py` with the JARDIN repo. |
| **leanSphincs-23** (`src/keccak/LeanSphincs-23Asm.sol`, keccak) | `ls23k` | Rust | `signers/leansphincs23-keccak/` | Port of the upstream leanSphincs crate, keccak256 for BLAKE2s. Pruned keys (`b` = kept-subtree height); fast path for the forge FFI tests and the KAT fixture. Tiered signer: `keygen` stores the key once in a key file with a bounded node cache (Light / Standard / Full), `sign-key` signs from it, byte-identical to `sign`. |
| ″ | `leansphincs23_signer.py` | Python | `script/` | Independent, written from `docs/leanSphincs-23-keccak.md`. Practical for `b ≈ 6..12`. |

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
- **`leansphincs23-keccak/`** — Rust crate for leanSphincs-23 over keccak256
  (`h=25,d=1,k=13,a=12`, WOTS+C `T=128`, 4,148-B sig). Bin `ls23k`
  (`sign` / `kat` / `verify`, and the tiered signer's `keygen` / `sign-key` /
  `info`: seed from `--seed-file` or `--seed-stdin`, never argv; the key file
  holds it; one seed, one key). `crosscheck.py` holds it to byte equality with
  the Python signer; `make_kat_fixture.py` writes the Forge KAT fixture;
  `tier_model.py` is the sphincs-art tier cost model. See its `README.md` and
  spec §14. Build: `cd signers/leansphincs23-keccak && cargo build --release`.

## Cross-validation map

- **C13**: `signers/c13-crosscheck/crosscheck.py` (Py ↔ Rust), plus the Rust
  `signers/signer-wasm/tests/cross_validate.rs` oracle and the WOTS+C/FORS+C
  reuse PoCs.
- **SLH-DSA-SHA2-128-24**: `signers/sphincsplus-128-24/crosscheck.py` (Py ↔ C),
  `signers/noble-slh-dsa/crosscheck.mjs` (noble ↔ C) and `kat-check.mjs`
  (noble ↔ pinned on-chain KAT), plus the Forge KAT
  (`test/SLH-DSA-SHA2-128-24-KAT.t.sol`).
- **leanSphincs-23**: `signers/leansphincs23-keccak/crosscheck.py` (Rust ↔
  Python, plus a spec-literal third recomputation), and the Forge KAT fixture
  `test/fixtures/leansphincs23-keccak-kat.json` (`make_kat_fixture.py --check`).
  The tiered `sign-key` is held to `ls23k sign` byte for byte (the crate's
  tests, the Forge FFI test `testVerifyFFI_RustLightTierKeyFile`, CI), and its
  call counts to `tier_model.py`.

CI (`.github/workflows/ci.yml`) runs the fast cross-checks (`rust-signer`, and
`slh-crosscheck` / `noble-crosscheck` at reduced parameters; `leansphincs23` at
full parameters on pruned keys) and the full forge suite on every push.

> **Not audited, not production-safe.**
