# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

SPHINCs- is a research prototype for lightweight SPHINCS+ variants on Ethereum. Live verifiers in `src/` are organized **one folder per hash function**: `src/keccak/` (keccak256 opcode), `src/sha/` (SHA-256 precompile 0x02), and `src/blake/` (BLAKE2b via the BLAKE2F compression precompile 0x09). Accounts live in `src/` root. The families:

1. **C-series** (`src/keccak/`: C7, C9, **C10**, **C11**, **C13**; C6/C8 in `legacy/src/`) — stateless WOTS+C / FORS+C (ePrint 2025/2203), n=128. Signature-count cap = 2^h (C7 → 2²⁴, C13 → 2²², C11 → 2¹⁶); security degrades with N as shown in the variants table in the README. **Every live keccak C-series verifier uses the FIPS 205 §4.2 uncompressed 32-byte ADRS layout** (the SHAKE-instantiation form, §11.1; keccak256 swapped for SHAKE256 — see "ADRS layout discipline" below). C11 and C10 were migrated from JARDIN's 32-byte ADRS to FIPS uncompressed; their JARDIN-layout originals are kept in `legacy/src/` for benchmark reproducibility.
2. **C12** (`src/keccak/SPHINCs-C12Asm.sol`) — plain SPHINCS+ (SPX) variant. h=20, d=5, a=7, k=20, w=8, l=46. 6,592-B sig. Migrated from the JARDIN 32-byte ADRS to the FIPS uncompressed 32-byte ADRS + keccak256 truncated to 16 B. The JARDIN-layout original stays in `legacy/src/SPHINCs-C12Asm.sol`, cross-referenced by the JARDIN repo as `JardinSpxVerifier`. Its FIPS signer is `script/spx_fips_signer.py`.
3. **SHA-256 twins** (`src/sha/`: `SPHINCs-C10-SHA.sol`, `SPHINCs-C11-SHA.sol`, `SPHINCs-C13-SHA.sol`, `SPHINCs-C12-SHA.sol`) — SHA-256 + 22-byte ADRSc versions of C10/C11/C13/C12. The hash and address change *as a coupled unit* (SHA-256 precompile; FIPS §11.2 compressed ADRSc; MSB-first `base_2b` parsing). **C10-SHA / C11-SHA / C13-SHA are "minimal twins"** — same WOTS+C/FORS+C counter-grinding and one-shot H_msg as their keccak originals, NOT FIPS (no MGF1, no envelope). **C12-SHA is full FIPS 205 SLH-DSA-SHA2** (plain SPHINCS+ can take it): MGF1 H_msg, `0x00‖0x00` empty-context envelope, standard checksum — a true SLH-DSA algorithm at research params (not a NIST set, so no KAT match). R is n=16 B on the wire ⇒ 6,576-B sig. Vectors: `script/signer.py {c10-sha,c11-sha,c13-sha}` and `script/slh_dsa_sha2_c12_signer.py`.
4. **BLAKE2b twins** (`src/blake/`: `SPHINCs-C11-BLAKE.sol`, `SPHINCs-C13-BLAKE.sol`, `SPHINCs-C12-BLAKE.sol`) — BLAKE2b versions of C11/C13/C12 that **reuse the keccak FIPS uncompressed 32-byte ADRS verbatim**; only the hash primitive changes (keccak256 → BLAKE2b). These are *minimal twins* of the keccak C-series (same WOTS+C/FORS+C and one-shot H_msg for C11/C13; same plain-SPHINCS+ for C12), **NOT FIPS** (BLAKE2b has no FIPS 205 instantiation). The on-chain hash is built on the **BLAKE2F compression precompile 0x09** (EIP-152) — *not* a hash but BLAKE2b's compression `F`, so each verifier carries a `blake2b()` Yul kernel that wraps it with the BLAKE2b construction (IV/param-block init, 128-byte block loop, LE↔BE lane bridging). F/H/T use a 16-byte digest; H_msg and the WOTS+C message digest use 32 bytes. Verifiers are `view` (the precompile is a staticcall). Same sig sizes as the keccak originals (3,976 / 6,592 / 3,688 B); verify gas is far higher (~3.1M C11, ~8.26M C12, ~2.8M C13) — inherent to a compression-only precompile + endianness handling. Vectors: `script/signer.py {c11-blake,c13-blake}` (C-series) and `script/spx_blake_signer.py` (C12). The BLAKE2b kernel is independently KAT-validated against `hashlib.blake2b` in `test/Blake2bKernelTest.t.sol`.
5. **SLH-DSA-128-24** — NIST SP 800-230 parameter set (d=1, h=22, a=24, k=6, w=4). Two variants:
   - FIPS 205 **external** SLH-DSA-SHA2 (`src/sha/SLH-DSA-SHA2-128-24verifier.sol`), empty-context envelope (`M' = 0x00‖0x00‖M`); SHA-256 precompile at 0x02. Matches NIST/ACVP external KATs.
   - JARDIN-convention Keccak twin (`legacy/src/SLH-DSA-keccak-128-24verifier.sol`, retired), native `keccak256`. Retired to `legacy/` alongside the other JARDIN-layout verifiers; the SHA-2 variant is the live one.

Accounts present in this repo use the C-series: `SphincsAccount` (ERC-4337), `SphincsAccountFactory`, `SphincsFrameAccount` (EIP-8141). The JARDIN hybrid-account stack (ECDSA + SPHINCs-) lives in the separate [nconsigny/JARDIN](https://github.com/nconsigny/JARDIN) repo.

**Not audited, not production-safe.**

## Build and Test Commands

```bash
forge build                                             # compile all contracts
forge test                                              # run all forge tests
cd signer-wasm && cargo test --release -- --ignored     # Rust C-series signer (9/9)

# SLH-DSA-128-24 fast C signers (one-time build; ~11 min per NIST-params sign).
# The binaries are gitignored, so a fresh checkout has none and a stale checkout
# has an old one. Both fast-signer wrappers refuse to run a binary older than any
# .c/.h/Makefile beside it (exit 1, naming the files and the make command) —
# parameters and CLI shape are compile-time, so a stale binary can sign under the
# wrong scheme with no error. Override only to reproduce an old vector on purpose:
# --allow-stale-binary. The Makefiles carry -MMD -MP, so a header edit really does
# trigger a rebuild.
(cd signers/sphincsplus-128-24  && make)
(cd signers/jardin-keccak-128-24 && make)

# Forge FFI end-to-end tests (first run triggers a real sign; cache hits after):
forge test --match-contract SLH_DSA_SHA2_128_24_Test   -vv
forge test --match-contract SLH_DSA_Keccak_128_24_Test -vv

# Keccak C-series (Python signer; C10 was promoted out of legacy/ — the JARDIN
# original still lives in legacy/test/ and is driven by `signer.py c10`):
forge test --match-contract SphincsC10Test    -vv     # keccak FIPS C10 (vectors: c10-fips)

# SHA-256 twins (Python signers, no C build needed; C13-SHA ~40s to sign):
forge test --match-contract SphincsC10ShaTest -vv     # SHA twin of C10
forge test --match-contract SphincsC11ShaTest -vv     # SHA twin of C11
forge test --match-contract SphincsC13ShaTest -vv     # SHA twin of C13
forge test --match-contract SphincsC12ShaTest -vv     # full-FIPS SLH-DSA-SHA2 at C12 params

# BLAKE2b twins (Python signers; BLAKE2F precompile 0x09; C13-BLAKE ~50s to sign):
forge test --match-contract Blake2bKernelTest -vv      # BLAKE2b-over-0x09 kernel KATs (no signer)
forge test --match-contract SphincsC11BlakeTest -vv    # BLAKE2b twin of C11
forge test --match-contract SphincsC13BlakeTest -vv    # BLAKE2b twin of C13
forge test --match-contract SphincsC12BlakeTest -vv    # BLAKE2b twin of plain-SPHINCS+ C12
```

Python env: `pip install eth-account eth-abi requests pycryptodome`.

## Architecture

### Shared Verifier Model

Every verifier is deployed once as a stateless pure contract and shared by all accounts. Accounts store their own keys and pass them into the verifier on each call.

```
<verifier> (deployed once, stateless, pure)
    ↑ verify(pkSeed, pkRoot, message, sig) → bool
    │
    ├── SphincsAccount        (ERC-4337, keys as immutables)
    └── SphincsFrameAccount   (EIP-8141, keys embedded in bytecode via PUSH32)
```

### ADRS layout discipline

Every verifier in `src/` now uses **one of only two address layouts**; the JARDIN
32-byte layout has been retired to `legacy/` (see "Retired layout" below):

1. **FIPS 205 §4.2 uncompressed 32-byte ADRS** + keccak256 — the SHAKE-instantiation form with keccak swapped in for SHAKE-256. Layout: `layer(4) ‖ tree(12) ‖ type(4) ‖ word1(4) ‖ word2(4) ‖ word3(4)`. Word semantics per type (FIPS 205 Table 1):
   - 0 WOTS_HASH:  word1=kp, word2=chain_address, word3=hash_address
   - 1 WOTS_PK:    word1=kp, word2=0, word3=0
   - 2 TREE:       word1=0, word2=tree_height, word3=tree_index
   - 3 FORS_TREE:  word1=kp, word2=tree_height, word3=tree_index
   - 4 FORS_ROOTS: word1=kp, word2=0, word3=0
2. **FIPS 205 §11.2.1 ADRSc (22 B compressed)** + SHA-256 (precompile 0x02) — required for the FIPS-SHA2 instantiation; smaller because SHA-2 block size benefits from packing.

Current users (everything in `src/`):
- **`src/keccak/` C7, C9, C10, C11, C13**: FIPS uncompressed 32 B + keccak256 (C13 was first on this layout; C7/C9 migrated from JARDIN, then C11, then C10). FORS is keyed by the per-message hypertree leaf via the FIPS field split — tree=idxTree0, kp=idxLeaf0, FORS tree number folded into tree_index.
- **`src/keccak/` C12**: FIPS uncompressed 32 B + keccak256, plain SPHINCS+ (d=5 hypertree, standard WOTS+ checksum). XMSS_TREE uses word2=height, word3=tree_index per FIPS Table 1.
- **`src/sha/` C10-SHA, C11-SHA, C13-SHA, C12-SHA, and SLH-DSA-SHA2-128-24**: FIPS §11.2 ADRSc 22 B + SHA-256. All share the `SHA-256(seed‖toByte(0,48)‖ADRSc‖payload)` framing and MSB-first parsing. C10-SHA/C11-SHA/C13-SHA keep the compact construction (counter-grinding, one-shot H_msg — not FIPS); C12-SHA and SLH-DSA-SHA2 are full FIPS (MGF1 H_msg, empty-context envelope). The ADRSc field semantics (word1/word2/word3 per type) are identical to the uncompressed layout — only layer (4→1 B) and tree (12→8 B) are compressed.

The two ADRS *byte layouts* in `src/` are therefore still just two (FIPS uncompressed 32 B for keccak, FIPS ADRSc 22 B for SHA-2); the SHA twins reuse the existing ADRSc.

Retired layout (`legacy/`, frozen — not maintained):
- **SLH-DSA-Keccak-128-24**, plus the JARDIN-layout **C11/C12 originals**: the older JARDIN 32 B layout (`layer4 ‖ tree8 ‖ type4 ‖ kp4 ‖ ci4 ‖ cp4 ‖ ha4`) + keccak256. The keccak SLH-DSA twin was never migrated; the C11/C12 JARDIN originals are kept frozen for benchmark reproducibility and (C12) for the JARDIN repo's `JardinSpxVerifier` reference, while their migrated FIPS twins are the live `src/` verifiers.

JARDIN's structural divergence from FIPS uncompressed is a shorter tree field (8 B vs 12 B) and a 4th type-dependent word (`ha`) that is never actually populated by any type. The visible difference between layouts is that JARDIN's `ci` (chain_index, WOTS-only) and `cp`/`ha` (height/index, TREE-only) live at distinct byte positions; FIPS overloads `word2` and `word3` per type. Both layouts are sound; FIPS is the cross-impl interop choice.

**New keccak-family verifiers MUST use FIPS uncompressed** — JARDIN is a frozen legacy layout, not an option for new work. The JARDIN-aware signers in `script/signer.py` (`cfg["adrs_mode"]` defaulting to JARDIN) still drive the legacy C6/C8/C10 paths (`c10` stays JARDIN for `legacy/src/`; the promoted twin is `c10-fips`); live C7/C9/C10/C11/C13 set `cfg["adrs_mode"]="fips"`, and `signer-wasm` is C13-only. The plain-SPX C12 FIPS signer is `script/spx_fips_signer.py` (wraps the shared `jardin_spx_signer.py`). Only touch JARDIN ADRS code to keep a `legacy/` verifier reproducible.

### Shared hash kernel (legacy phrasing, kept for context)

The legacy **C-series (C6/C8/C10) and SLH-DSA-Keccak** verifiers in `legacy/` share the JARDIN kernel: one 32-byte ADRS layout and the `keccak(seed32 ‖ adrs32 ‖ inputs)` tweakable-hash shape (see `script/jardin_primitives.py`). A device port covers those with a single `sphincs_th*` implementation. The live verifiers split into two kernels: **SLH-DSA-SHA2-128-24** uses FIPS 205's 22-byte compressed ADRSc + SHA-256 with the nested MGF1 Hmsg, in **external** mode (empty-context envelope `M' = 0x00‖0x00‖M`); **C7, C9, C10, C11, C12, C13** use FIPS uncompressed 32 B ADRS + keccak256 — the canonical keccak-family layout now that the C-series has all migrated off JARDIN.

### Current contracts (`src/`)

Verifiers are split by hash function: `src/keccak/` and `src/sha/`. Accounts stay in `src/` root (they reference a verifier by address, no import dependency).

**`src/keccak/`** (keccak256 opcode, FIPS uncompressed 32-byte ADRS):

| File | Purpose |
|---|---|
| `SPHINCs-C7Asm.sol` | C-series verifier, stateless, n=128, h=24 d=2 a=16 k=8 w=8. 3,704-B sig, ~127 K verify |
| `SPHINCs-C9Asm.sol` | C-series verifier, stateless, n=128, h=20 d=2 a=12 k=11 w=8. 3,816-B sig, ~117 K verify |
| `SPHINCs-C10Asm.sol` | C-series verifier, n=128, h=18 d=2 a=11 k=13 w=8. 4,008-B sig, ~115 K verify. ~104.5-bit at 2²⁰ cap. Promoted out of `legacy/src/`; same params as C11 but h=18. |
| `SPHINCs-C11Asm.sol` | C-series verifier, n=128, h=16 d=2 a=11 k=13 w=8. 3,976-B sig, ~116 K verify. ~86-bit at 2²⁰ cap — prefer C13 when verify-time security matters. |
| `SPHINCs-C12Asm.sol` | Plain SPHINCS+ (SPX) verifier, n=16, h=20 d=5 a=7 k=20 w=8 l=46. 6,592-B sig, ~726 K verify. JARDIN original kept in `legacy/src/` as `JardinSpxVerifier`. |
| `SPHINCs-C13Asm.sol` | C-series verifier, n=128, h=22 d=2 a=19 k=7 w=8. 3,688-B sig, ~105 K verify (cheapest at 128-bit). First verifier on the FIPS uncompressed layout. |

**`src/sha/`** (SHA-256 precompile 0x02, FIPS §11.2 compressed 22-byte ADRSc):

| File | Purpose |
|---|---|
| `SPHINCs-C10-SHA.sol` | SHA-256 "minimal twin" of C10 (WOTS+C/FORS+C kept, one-shot H_msg, MSB-first). 4,008-B sig, ~475 K verify. Not FIPS. |
| `SPHINCs-C11-SHA.sol` | SHA-256 "minimal twin" of C11 (WOTS+C/FORS+C kept, one-shot H_msg, MSB-first). ~473 K verify. Not FIPS. |
| `SPHINCs-C13-SHA.sol` | SHA-256 "minimal twin" of C13. ~440 K verify. Not FIPS. |
| `SPHINCs-C12-SHA.sol` | **Full FIPS 205 SLH-DSA-SHA2** at C12 params (MGF1 H_msg, `0x00‖0x00` envelope, MSB-first base_2b, standard checksum). 6,576-B sig (R=16 B), ~942 K verify. Research params, not a NIST set. |
| `SLH-DSA-SHA2-128-24verifier.sol` | FIPS 205 **external** SLH-DSA-SHA2-128-24 verifier (empty-ctx envelope; SHA-256 precompile). Matches NIST/ACVP KATs. |
| `SLH-DSA-SHA2-128-24-Diagnostic.sol` | Debug tool used to bisect the SHA-2 verifier during development |

**`src/blake/`** (BLAKE2b via the BLAKE2F compression precompile 0x09; reuses the FIPS uncompressed 32-byte ADRS, `view` not `pure`):

| File | Purpose |
|---|---|
| `SPHINCs-C11-BLAKE.sol` | BLAKE2b "minimal twin" of C11 (WOTS+C/FORS+C, one-shot H_msg). 3,976-B sig, ~3.07 M verify. Not FIPS. |
| `SPHINCs-C13-BLAKE.sol` | BLAKE2b "minimal twin" of C13. 3,688-B sig, ~2.84 M verify. Not FIPS. |
| `SPHINCs-C12-BLAKE.sol` | BLAKE2b twin of the plain-SPHINCS+ C12 (standard WOTS+ checksum, d=5). 6,592-B sig, ~8.26 M verify. Not FIPS. |

Each carries a `blake2b(ptr,len,nn)` Yul kernel wrapping the 0x09 compression `F` (the precompile is **not** a hash). The kernel is KAT-validated against `hashlib.blake2b` in `test/Blake2bKernelTest.t.sol`; kernel scratch is at memory `0x800+` (clear of the SPHINCS+ working set ≤ `0x620`), preimages are read from `0x00`. Verify gas is ~10–25× the keccak originals — inherent to a compression-only precompile + per-call LE↔BE lane swaps + multi-block compression on the large T_l input.

**`src/`** (accounts): `SphincsAccount.sol` (ERC-4337 hybrid ECDSA + SPHINCs-, verifier pluggable via immutable), `SphincsAccountFactory.sol` (CREATE2 factory), `SphincsFrameAccount.sol` (EIP-8141 pure-PQ, keys in bytecode).

### Frozen variants (`legacy/`)

Prior C-series verifiers (C6, C8) kept for benchmark reproducibility, plus the JARDIN-layout **C10 original** — C10 was promoted to `src/keccak/` (and gained a `src/sha/` twin), but its legacy verifier stays `legacy/test/SphincsC10Test.t.sol` still exercises it via `signer.py c10`. Same 32-byte ADRS kernel, different parameters. **SLH-DSA-Keccak-128-24** is frozen here too — it stayed on the JARDIN 32-byte ADRS layout while the repo standardized on the two FIPS layouts. The **JARDIN-layout C11/C12 originals** also remain here: C11 and C12 were migrated to FIPS uncompressed in `src/`, but their JARDIN versions are kept frozen for benchmark reproducibility and (C12) for the JARDIN repo's `JardinSpxVerifier` reference. Legacy Forge tests live in `legacy/test/` (outside the default `forge test` path) and the JARDIN-mode off-chain signers (`script/jardin_spx_signer.py`, `signers/jardin-keccak-128-24/`, `script/signer.py` JARDIN mode) are unchanged. See `legacy/README.md`.

| Variant | h | d | a | k | w | swn | Sig | sign_h | Verify | Frame | 4337 | sec_20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| C6 | 24 | 2 | 16 | 8 | 16 | 240 | 3352 B | 5.7M | 156K | 232K | 333K | 128 |
| **C7** | **24** | **2** | **16** | **8** | **8** | **151** | **3704 B** | **4.3M** | **127K** | **210K** | **318K** | **128** |
| C8 | 20 | 2 | 13 | 12 | 16 | 162 | 3848 B | 1.4M | 194K | 271K | 377K | 128 |
| **C9** | **20** | **2** | **12** | **11** | **8** | **208** | **3816 B** | **1.3M** | **117K** | **195K** | **300K** | **112.6** |
| C10 | 18 | 2 | 11 | 13 | 8 | 205 | 4008 B | 609K | 115K | 203K | 308K | 104.5 |
| **C11** | **16** | **2** | **11** | **13** | **8** | **203** | **3976 B** | **292K** | **116K** | **202K** | **308K** | **86.1** |

## SLH-DSA-128-24

NIST SP 800-230 (April 2026 IPD) parameter set with a hard 2^24 signature limit per key. Parameters: n=16, h=22, d=1 (single XMSS tree), h'=22, a=24, k=6, w=4, m=21. Signature size 3,856 B (same for both hash variants).

- **SHA-2 variant** (`SLH-DSA-SHA2-128-24verifier.sol`): FIPS 205 **external** SLH-DSA.Verify, empty context. Message wrapped as `M' = 0x00‖0x00‖M` before H_msg; 22-byte compressed ADRSc, nested Hmsg = `MGF1-SHA-256(R‖seed‖SHA-256(R‖seed‖root‖M'), 21)`, **big-endian / MSB-first digest parsing** (`md[t]=BE(digest[3t..3t+3])` — FIPS 205 / current PQClean; *not* the legacy LSB-first SPHINCS+ ref). Signers prepend the same `0x00 0x00`. Every F / H / T is a SHA-256 precompile (0x02) staticcall.
- **Keccak variant** (`SLH-DSA-keccak-128-24verifier.sol`): JARDIN-family twin. 32-byte full JARDIN ADRS (`layer4‖tree8‖type4‖kp4‖ci4‖cp4‖ha4`), one-shot Hmsg = `keccak(seed‖root‖R‖msg‖0xFF..FB)`, LSB-first digest parsing on the 256-bit keccak output (not byte-wise), LSB-first-within-128-bit WOTS `base_w`. Every F / H / T is a native `keccak256` opcode.

**Hash-call counts** (both variants, same tree shape):

| Step | Operations | Calls |
|---|---|---:|
| Keygen — 2²²-leaf XMSS (one-time per key) | leaves × (68 WOTS chains × 3 F + 1 T_l) + 2²² − 1 H | ~864 M |
| Sign — FORS (6 × 2²⁴ leaves; can't be cached across signs — different leaf_idx → different FORS keys) | 6 × (leaves + internal + 1 T_k) | ~201 M |
| Sign — XMSS tree-hash pass for auth path (**skippable** if the signer caches the 2²²-leaf tree after keygen, ~128 MB RAM) | same work as keygen | ~864 M |
| Sign — WOTS on FORS-pk | 68 chains × ~1.5 F avg | ~100 |
| **Per signature, cold signer** (hardware wallet, no tree cache) | FORS + XMSS rebuild + WOTS | **≈ 1.07 × 10⁹** |
| **Per signature, cached signer** (keeps 128 MB XMSS tree in RAM) | FORS + WOTS only | **≈ 2.01 × 10⁸** |

So a desktop-class signer that holds the XMSS tree in RAM amortises keygen across many sigs and pays ~200 M hashes per subsequent signature — still ~50× more than C11's per-sign cost, because the FORS work (2^24 × 6 ≈ 100 M leaves) is redone every time. A hardware-wallet-class signer without the RAM to cache the XMSS tree pays the full ~1.07 B per signature.

**Measured on-chain verify gas** (Sepolia top-level tx with 3,872-B calldata):
- SHA-2 variant: 225,642 gas (pure assembly ~142 K)
- Keccak variant: 177,910 gas (pure assembly ~94 K) — ~21 % cheaper at tx level, ~34 % at assembly level.

## Off-chain Components

### C-series signers

- `script/signer.py` — Python SPHINCs- C-series signer (C6–C13 all supported; live C7/C9/C11/C13 + `c10-fips` in FIPS ADRS mode, legacy C6/C8/C10 in JARDIN mode; slow, ~30 s per C6 sig). **SHA-256 twins** `c10-sha` / `c11-sha` / `c13-sha` are gated by `cfg["hash"]="sha2"` + `adrs_mode="adrsc"` + `parse="msb"`; **BLAKE2b twins** `c11-blake` / `c13-blake` by `cfg["hash"]="blake2"` + `adrs_mode="fips"` (default LSB parse). The keccak path is byte-identical when no `hash` flag is set. A `verify_c_series` mirror self-checks every signature (all three backends) before output. **Backend dispatch must be total:** all tweakable-hash helpers — `th`/`th_pair`/`th_multi`/`wots_digest`/`h_msg` *and* the FIPS chain hash `chain_hash_fips` — route through the `HASH_BACKEND` switch. (`chain_hash_fips` previously hardcoded keccak, which the `verify_c_series` self-check could not catch — both Python sides shared the bug — but diverged from the BLAKE2b verifier. For keccak, `th()` ≡ the old `_keccak_3x32 & N_MASK`, so that fix is behavior-preserving for C7/C9/C11/C13.)
- `signer-wasm/` — Rust/WASM C-series signer with BIP-39/44 key derivation

### C12 (plain SPHINCS+) signer

- `script/spx_fips_signer.py` — Python signer for the **keccak FIPS-layout C12** (`src/keccak/SPHINCs-C12Asm.sol`). Thin wrapper that imports `jardin_spx_signer.py`, configures the corrected `l1=43, l2=3, l=46` WOTS+ width, and monkeypatches `make_adrs` to the FIPS 205 uncompressed constructor. Used by `test/SphincsC12Test.t.sol`.
- `script/slh_dsa_sha2_c12_signer.py` — Python signer for the **full-FIPS C12-SHA** (`src/sha/SPHINCs-C12-SHA.sol`). The d=5 generalisation of `slh_dsa_sha2_128_24_signer.py` at C12 params (w=8): SHA-256 + ADRSc, MGF1 H_msg, `0x00‖0x00` envelope, MSB-first base_2b. Self-contained, with a local `slh_verify`. R=16 B ⇒ 6,576-B sig. Used by `test/SphincsC12ShaTest.t.sol`.
- `script/jardin_spx_signer.py` — Python signer for the **legacy JARDIN-layout C12** (`legacy/src/SPHINCs-C12Asm.sol`, plain SPHINCS+, h=20, d=5, w=8). Self-contained; uses `jardin_primitives.py` for ADRS + tweakable hashes. Name kept as `jardin_spx_signer.py` because the same file is shared verbatim with the JARDIN repo's hybrid-account stack — do not change its output.
- `script/spx_blake_signer.py` — Python signer for the **BLAKE2b C12** (`src/blake/SPHINCs-C12-BLAKE.sol`). Like `spx_fips_signer.py` it imports `jardin_spx_signer.py`, configures `l1=43, l2=3, l=46`, and monkeypatches `make_adrs` to the FIPS constructor; it additionally swaps the tweakable hashes `F`/`H_`/`T_l`/`T_k`/`h_msg` for `hashlib.blake2b` (16-byte F/H/T, 32-byte H_msg, domain `0xFF..FC`). The PRFs (`wots_secret`/`fors_secret`/`derive_R`) stay keccak — signer-only, never recomputed by the verifier. Used by `test/SphincsC12BlakeTest.t.sol`.

### SLH-DSA-128-24 signers

- `script/slh_dsa_sha2_128_24_signer.py`, `script/slh_dsa_keccak_128_24_signer.py` — pure-Python reference signers (very slow: ~hours at NIST params; use `--height N --a N` overrides for dev iteration).
- `signers/sphincsplus-128-24/` — fork of sphincs/sphincsplus ref with a `params-*-128-24.h` header and w=4 support. ~11 min for a full NIST-params sign in pure C.
- `signers/jardin-keccak-128-24/` — separate C fork for the Keccak variant. Adds a ~70 LOC minimal keccak256 (legacy 0x01 padding, Ethereum-flavour), a 32-byte JARDIN ADRS `address.c`, bit-level LSB-first digest-to-indices, and LSB-first-within-128-bit WOTS `base_w`.
- `script/slh_dsa_sha2_128_24_fast_signer.py`, `script/slh_dsa_keccak_128_24_fast_signer.py` — Python wrappers that derive seeds via JARDIN HMAC-SHA-512, invoke the C binary, cache the result on disk. Used by the Forge FFI tests.
- `signers/*/crosscheck.py` — Python-vs-C cross-validation at arbitrary h/a.

### Deploy scripts

- `script/DeploySlhDsa128_24Sepolia.s.sol` — deploys both SLH-DSA-128-24 verifiers to Sepolia.
- `legacy/script/DeploySepolia.s.sol` — deploys a C-series shared verifier + `SphincsAccountFactory`.

### Key derivation (C-series)

BIP-39 mnemonic → HMAC-SHA512("sphincs-c6-v1", seed) → SPHINCs- keys (quantum-safe path). ECDSA derived via BIP-32 m/44'/60'/0'/0/0 (independent from the SPHINCs- path).

## Gas Optimizations Applied

- Branchless Merkle swap: `mstore(xor(0x40, s), node)` (Solady pattern) — used in the 32-byte-aligned C-series, C12, and SLH-DSA-Keccak verifiers. The SLH-DSA SHA-2 verifier has a 16-byte-aligned L/R layout that REQUIRES L-first-then-R order; see the `switch and(pathIdx, 1)` blocks.
- SHL for power-of-2 multiplications (`shl(4, i)` instead of `mul(i, 16)`)
- Hoisted loop-invariant chain address
- Domain-separated H_msg (prevents cross-variant collisions)
- Frame-account v2: keys embedded as PUSH32 (no SLOAD, saves ~4.2 K gas)

## Formal Verification (`verity/`)

The `verity/` directory is a small Verity workbench that hand-models two
of the production verifiers in `src/` and proves each model refines a
functional spec. See `verity/README.md` for scope, file map, and build
instructions, and `verity/SphincsMinusVerifiers/AXIOMS.md` for the full
remaining trust surface.

The `SphincsMinusVerifiers` workbench (`verity/SphincsMinusVerifiers/`)
layers the refinement as: hand-transcribed Verity model →
`ByteLevel.verifyBytes` (byte-level contract spec) → `verifySpec`
(abstract algorithmic spec). The lower-to-abstract link
(`verifyBytes_eq_verifySpec`, `byteVerifier_refines_spec`) is fully
proved (`#print axioms` -> `propext`). The per-verifier theorems
`c13_refines_spec` and `slhDsaSha2_128_24_refines_spec` are proved in
`Proofs.lean`. `c13_refines_spec` rests on Lean's logic plus three named
residual assembly axioms; `slhDsaSha2_128_24_refines_spec` rests on
Lean's logic plus its model-to-byte-spec bridge axiom and an opaque
SHA-256 primitives constant. All are enumerated in
`SphincsMinusVerifiers/AXIOMS.md`. A follow-up PR is discharging the
residual assembly obligations; the README is worded so it stays true in
both proof states.

The Verity models are hand-transcribed from the Solidity inline
assembly. They are not compiled into the production contracts, not
deployed, and not replayed in the Foundry test suite. There is no
EVM-side regression test that takes the Lean model and runs it against
the on-chain verifier; correspondence rests on the transcription itself
being reviewed against the assembly. The old `SphincsC6/`, `SphincsC6Full/`,
`SphincsC6V/`, and `SphincsKernel/` trees, the C12 model, the
`verity/artifacts/` Yul artefacts, and `test/MerkleKernelVerityTest.t.sol`
have been removed; no Verity artifact is exercised by Foundry.

**Build discipline (16 GB machines):** never run a bare `lake build`. Use
`verity/scripts/build.sh` (caps the Lean task pool at 2 workers via
`LEAN_NUM_THREADS`; `lakefile.lean` sets `maxHeartbeats 1000000` so a
runaway whnf aborts as an error instead of OOMing the machine). Several
proof files were authored on large cloud machines and exceed 12 GB per
worker if a defeq diverges.

## Foundry Config

- `via_ir = true`, `optimizer_runs = 200`
- `ffi = true` (for Python signer calls)
- Deployed on Sepolia (chain 11155111). Legacy ethrex (chain 1729) deployments for the frame-tx path.
