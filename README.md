# SPHINCs- — post-quantum signature verifiers for Ethereum

> **WARNING: research prototype, not for production.** These are explorations of lightweight SPHINCS+
> variants. The code has **not been audited** and is **not safe to use with real funds**.

SPHINCs- is a family of EVM-optimised variants of SLH-DSA (FIPS 205) and of the proposed
[SLH-DSA-128-24](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-230.ipd.pdf). Every verifier
runs in plain EVM code, with no new precompile, so it works today without a hard fork. The two main levers are
swapping SHAKE256 for the native `keccak256` opcode and shrinking the signature budget: NIST standardised a
2^64-signature budget, while 99.99% of the 64,294,251 mainnet addresses that sent a transaction in 2025 sent fewer
than 3,000 that year. Each variant trades the per-key signature budget against verify gas and signer work (how
hardware-wallet friendly it is).

The verifiers are stateless and hold 128-bit security up to their stated limits, so a smart account can use any
of them. For constrained devices, the JARDÍN account design (SPHINCs- plus a compact path) lives in a separate repo,
[`nconsigny/JARDIN`](https://github.com/nconsigny/JARDIN).

## Schemes

| Scheme | Family | h | d | a | k | w | l | swn | Sig | sign_h | Verify | Verify tx | Frame | 4337 | sec_10 | sec_14 | sec_18 | sec_20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **C7** | WOTS+C / FORS+C | 24 | 2 | 16 | 8 | 8 | 43 | 151 | 3,704 B | 4.3 M | 96 K | - | 210 K † | 318 K † | 128 | 128 | 128 | 128 |
| **C12** | vanilla SPHINCs+ | 20 | 5 | 7 | 20 | 8 | 46 | - | 6,592 B | ~37.3 K | ~204 K | - | - | - | 128 | 127.8 | 109.1 | 95.4 |
| **C13** | WOTS+C / FORS+C | 22 | 2 | 19 | 7 | 8 | 43 | 208 | 3,688 B | ~10 M | 105 K ♦ | **263 K** | **258 K** | 293 K † | 128 | 128 | 128 | 128 |
| **SLH-DSA-Keccak-128-24** | vanilla SPHINCs+ | 22 | 1 | 24 | 6 | 4 | 68 | - | 3,856 B | ~1.07 B | ~94 K | 178 K † | - | - | 128 | 128 | 128 | 128 |
| **leanSphincs** | leanSphincs (WOTS+C / FORS) | 26 | 1 | 10 | 24 | 4 | 64 | 120 | 5,684 B | see below | ~53 K | 390 K | 385 K | - | 128 | 128 | 128 | 128 |
| **leanSphincs-s** | leanSphincs (WOTS+C / FORS) | 26 | 1 | 12 | 13 | 4 | 64 | 128 | 4,164 B | see below | ~39 K | 294 K | 288 K | - | 128 | 128 | 128 | 128 |
| **leanSphincs-f** | leanSphincs (WOTS+C / FORS) | 26 | 1 | 9 | 20 | 4 | 64 | 122 | 4,660 B | see below | ~44 K | 325 K | 320 K | - | 128 | 128 | 128 | 128 |

- **Family**: the construction style. WOTS+C / FORS+C is the C-series compact construction with counter grinding
  (ePrint 2025/2203). Vanilla SPHINCs+ is the standard FIPS 205 construction with no counter grinding: C12 and
  SLH-DSA-128-24 are the same algorithm at different parameter sets. The leanSphincs family is Tom Wambsgans'
  [proposal](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates): one XMSS layer, WOTS+C, and FORS
  without tree roots. leanSphincs is the proposal at its own parameters (the upstream crate's `keccak` branch),
  leanSphincs-s the [sphincs-art](https://nconsigny.github.io/sphincs-art/) parameter set, and leanSphincs-f a
  retuning of -S for faster signing (smaller FORS trees, a larger signature).
- **sign_h**: hash calls for keygen plus one signature on a zero-memory signer (no caching between signatures, the
  relevant case for a hardware wallet). A high number means a lot of work for the hardware. The leanSphincs variants
  keep a generated key with a small node cache instead; see [Signing](#signing).
- **swn**: the WOTS+C target sum, i.e. the digit sum the signer grinds its counter for. Vanilla SPHINCs+ uses the
  standard Winternitz checksum and doesn't grind.
- **sec_N**: security bits at 2^N signatures per key. SLH-DSA-128-24 (h=22, d=1) is a **single XMSS tree of
  2²² WOTS leaves**, and the signing leaf is picked pseudorandomly from the message digest. WOTS-leaf collisions
  therefore start around 2¹¹ signatures, well before the named 2²⁴ usage cap. This is expected and **absorbed by
  the FORS few-time layer** (it is not a WOTS forgery): the 128 bits come from the FORS margin, *not* from one-time
  WOTS use, so 2²⁴ is a recommended per-key **usage cap**, not a flat one-time guarantee. See
  [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md). (review SLH-X-f2cap) The leanSphincs figures are for a
  full 2²⁶ key: leanSphincs's 2³⁰-signature lifetime is proved in Lean by the proposal; -S and -f are rated for 2²⁶
  signatures (sphincs-art estimates of 103 M and 119 M, not proved). A pruned key's lifetime is lower (below).
- **Verify (pure)**: Foundry gas of the verifier call alone (`gasleft()` around the call, or the call frame via
  `vm.lastCallGas` for leanSphincs). C12's Forge e2e test prints ~665 K because it also copies the cached 6,592-B
  signature out of storage; ~204 K is the verifier itself.
- **Verify tx**: one standalone `verify` transaction on Sepolia, October 2026. **Frame**: one self-paying EIP-8141 frame
  tx (VERIFY then a 0.00001 ETH SENDER transfer) on the ethrex privacy testnet (chain 8141), October 2026. Both are
  priced by the calldata floor, about 64 gas per signature byte, so they rank by signature size, not by verifier
  execution: C13's 3,688-B signature beats leanSphincs-s's 4,164 B even though it executes ~107 K against ~39 K.
  **4337**: total ERC-4337 `handleOps` tx gas (Sepolia), through `SphincsAccount` + `SphincsAccountFactory`; the
  leanSphincs verifiers plug into `SphincsAccount` unchanged (`validateUserOp` ~60.8 K / ~46.5 K / ~51.6 K in Forge).
  Addresses and transactions: [docs/deployments.md](docs/deployments.md) and each signer's README.
- **†** measured in June 2026 under earlier gas rules (before the 64-gas-per-byte calldata floor, on the now-defunct
  ethrex devnet for Frame), against verifiers that predate the October 2026 loop optimisations; not comparable with
  the October figures.
- **♦** C13's verifier is pinned by the Lean model in `verity/`, so it does not have the loop optimisations that
  took C7 and C12 down ~22–24%. Until it does, C7 verifies cheaper than C13.
- **SLH-DSA-Keccak-128-24** is the keccak twin of the NIST set (JARDIN 32-byte ADRS); its verifier is frozen in
  [`legacy/`](legacy/README.md). The live NIST verifier is the FIPS 205 **SLH-DSA-SHA2-128-24**
  (`src/sha/`, ~142 K verify, matches the NIST/ACVP external KATs), with the same parameters and signer cost.

> **C12 keys:** the 2026-07-30 `l = 45 → 46` correction changed C12 signatures and public keys, and the C12
> signer fixed in October 2026 used to derive FORS secrets without the hypertree position (about 1,000
> signatures allowed a forgery; [B-01](docs/SECURITY-REVIEW-2026-10.md)). Retire any C12 key that signed with an
> older signer.

Every variant, including C9/C10/C11, the SHA-256 and BLAKE2b twins, and the C13 comparison table, is in
[docs/variants.md](docs/variants.md).

## Signing

Signing time at the device rates of [sphincs.art](https://nconsigny.github.io/sphincs-art/), Tom Wambsgans'
figures for Keccak-f[1600]: **Ledger Nano S+ 5.8 K/s, weak CPU 128 M/s, powerful CPU 512 M/s.** The C-series and
SLH-DSA count one permutation per hash call (multi-block calls add about 1%).

| Scheme | Hashes / signature | Ledger Nano S+ | Weak CPU | Powerful CPU |
|---|---|---|---|---|
| C7 | 4.3 M (zero-memory) | 12 min | 34 ms | 8.4 ms |
| C12 | 37.3 K (zero-memory) | 6.4 s | 0.29 ms | 73 µs |
| C13 | ~10 M (zero-memory) | 29 min | 78 ms | 20 ms |
| SLH-DSA-Keccak-128-24 | ~1.07 B (zero-memory) | 51 h | 8.4 s | 2.1 s |
| leanSphincs | 73.5 K / 69.9 K / 92.2 K permutations | **13 s** (Light) | **0.55 ms** (Standard) | **0.18 ms** (Full) |
| leanSphincs-s | 159 K / 155 K / 178 K permutations | **27 s** (Light) | **1.2 ms** (Standard) | **0.35 ms** (Full) |
| leanSphincs-f | 38.4 K / 34.8 K / 57.1 K permutations | **6.6 s** (Light) | **0.27 ms** (Standard) | **0.11 ms** (Full) |

- **leanSphincs, -S and -f** follow the page's one-signer tiers: the key is generated once and kept with a node
  cache. Light keeps a 2¹³ subtree in 16 KiB (keygen 1.91 M permutations, 5.5 min on the Ledger), Standard a 2²⁰
  subtree in 1 MiB (244 M, 1.9 s), Full the whole 2²⁶ tree in 16 MiB (15.6 B, 31 s), in every variant. Lifetimes:
  leanSphincs 210 K / 22 M / 1.15 B (proved), -S and -f rated 20 K / 2²¹ / 2²⁶ (estimates). The signatures are the
  same in every tier. **One seed = one key of one variant**: never reuse a seed across variants or tiers. Our Rust
  signers `lsk` / `lssk` / `lsfk` take 4–9 / 7–29 / 3–12 ms per signature (Light) and 14–15 / 17–24 / 13–15 ms
  (Standard) on 8 cores, key loading and a self-check included; keygen takes 0.06 s (Light) and 8 s (Standard).
- **SLH-DSA-128-24** on a CPU that keeps its 2²² XMSS tree in RAM (128 MB) needs ~201 M hashes: 1.6 s / 0.39 s.
  FORS (6 trees of 2²⁴ leaves) has to be rebuilt for every signature, so it stays the slowest signer here.
- **Measured on a Ledger Nano S+ today:** our C11 and C12 signers take 390 s and 47.5 s, about 750 Keccak calls per
  second, roughly 7× below the page's rate.

## How it works

Every verifier is deployed once, is stateless (`pure`), and is shared by all accounts, which pass their own keys:

```
<verifier> (deployed once)
    ↑ verify(pkSeed, pkRoot, message, sig) → bool
    ├── SphincsAccount       ERC-4337 hybrid: ECDSA(owner) + SPHINCs- over userOpHash
    └── SphincsFrameAccount  EIP-8141 pure PQ: keys as immutables, verified in a VERIFY frame
```

Hash inputs and address layouts:

- **C-series and C12** (`src/keccak/`): FIPS 205 §4.2 uncompressed 32-byte ADRS, `keccak256(seed ‖ ADRS ‖ payload)`
  truncated to 16 bytes.
- **SLH-DSA-SHA2-128-24 and the SHA-256 twins** (`src/sha/`): FIPS 205 §11.2 ADRSc (22 bytes) over the SHA-256
  precompile; the NIST verifier is FIPS 205 external SLH-DSA.Verify with an empty context.
- **leanSphincs, leanSphincs-s and leanSphincs-f** (`src/keccak/LeanSphincsAsm.sol`, `LeanSphincs-SAsm.sol`,
  `LeanSphincs-FAsm.sol`): leanSphincs's own 16-byte tweak, `keccak256(P ‖ tweak ‖ payload)` truncated to 16 bytes,
  as on the upstream crate's `keccak` branch. Specs: [leanSphincs](docs/leanSphincs-keccak.md) (the upstream crate
  is normative), [leanSphincs-s](docs/leanSphincs-S-keccak.md), [leanSphincs-f](docs/leanSphincs-f-keccak.md).

Key derivation (Rust/WASM signer): BIP-39 mnemonic → `HMAC-SHA512("sphincs-c6-v1", seed)` for the SPHINCs- keys,
and BIP-32 `m/44'/60'/0'/0/0` for the independent ECDSA key. More detail: [CLAUDE.md](CLAUDE.md),
[docs/variants.md](docs/variants.md).

## Signers

| Scheme | Signers |
|---|---|
| C7 / C13 | `script/signer.py` (Python, `c7` / `c13`), `signers/signer-wasm` (Rust/WASM, C13 only, BIP-39) |
| C12 | `script/spx_fips_signer.py` |
| SLH-DSA-128-24 | `signers/sphincsplus-128-24` (C, SHA-2), `signers/noble-slh-dsa` (JS), `signers/slhvk-sha2-128-24` (GPU), `signers/jardin-keccak-128-24` (C, Keccak twin) |
| leanSphincs | `signers/leansphincs-keccak` (Rust, `lsk`, tiered key files), `script/leansphincs_s_signer.py --variant regular` (Python) |
| leanSphincs-s | `signers/leansphincs-s-keccak` (Rust, `lssk`, tiered key files), `script/leansphincs_s_signer.py` (Python) |
| leanSphincs-f | `signers/leansphincs-f-keccak` (Rust, `lsfk`, tiered key files), `script/leansphincs_s_signer.py --variant f` (Python) |

Which signer targets which verifier, and how they are cross-checked: [signers/README.md](signers/README.md).

## Quick start

```bash
forge build
pip install eth-account eth-abi requests pycryptodome
forge test --no-match-contract '^SLH_DSA_SHA2_128_24_(Test|CalldataGas)$'   # skips the two slow NIST-parameter signs
(cd signers/leansphincs-keccak && cargo test --release)
(cd signers/leansphincs-s-keccak && cargo test --release)
(cd signers/leansphincs-f-keccak && cargo test --release)
(cd signers/signer-wasm && cargo test --release -- --ignored)
FOUNDRY_TEST=legacy/test forge test   # frozen legacy verifiers (includes two slow NIST-parameter SLH-DSA-Keccak signs)
```

The skipped SLH-DSA suites sign at NIST parameters with `signers/sphincsplus-128-24` (`make` it first), which takes
minutes per signature; the pinned KAT suites cover the verifier without it.

## Deployments

| Chain | Contract | Address |
|---|---|---|
| Sepolia | C13 verifier (hardened, 2026-06-04) | [`0xc6f4009D…A5F2`](https://sepolia.etherscan.io/address/0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2) |
| Sepolia | SphincsAccountFactory (C13) | [`0x8830d362…ABA4`](https://sepolia.etherscan.io/address/0x8830d36284829656F2A60CD028062686069FABA4), [`0x79FDD0aF…d857`](https://sepolia.etherscan.io/address/0x79FDD0aFcb2214D6C17E639dA7eF6357956Cd857) |
| Sepolia | SphincsAccount (ERC-4337 hybrid, C13) | [`0x01280171…0dD4`](https://sepolia.etherscan.io/address/0x01280171F336869e9c96F9e6eb674b1548D10dD4) |
| Sepolia | SLH-DSA-SHA2-128-24 verifier (FIPS 205 external) | [`0x12B712ad…0553`](https://sepolia.etherscan.io/address/0x12B712ad3ca6D81d4B3690B2f93420cd65EA0553) |
| Sepolia | SLH-DSA-Keccak-128-24 verifier | [`0x2Ac9Ec4a…6205`](https://sepolia.etherscan.io/address/0x2Ac9Ec4a2A062aFc1be718e77ec3300D087E6205) |
| Sepolia | leanSphincs verifier | [`0x4B1CF99F…0db0`](https://sepolia.etherscan.io/address/0x4B1CF99FD1C9dfD6F3F4BE6751E902F71C6f0db0) |
| Sepolia | leanSphincs-s verifier | [`0x7E406078…16a7`](https://sepolia.etherscan.io/address/0x7E4060786AE34E143978dF07da82A388292316a7) |
| Sepolia | leanSphincs-f verifier | [`0xd7597406…011B`](https://sepolia.etherscan.io/address/0xd75974064757B7C3C7988AbD38B3D722E0d8011B) |
| ethrex privacy testnet (8141) | leanSphincs / -s / -f frame accounts (EIP-8141) | [`0x874f5ba1…eDD7`](https://dora.privacy.ethrex.xyz/address/0x874f5ba1d47B477CB70999795cAf7E6Bb53EeDD7), [`0x8e2812cc…aE62`](https://dora.privacy.ethrex.xyz/address/0x8e2812cc597389b0E6522E610eAaeD635acbaE62), [`0xaD6b0De1…60b7`](https://dora.privacy.ethrex.xyz/address/0xaD6b0De1E1b5792AF346E192346D120B484560b7) |

EntryPoint v0.9 on Sepolia: `0x433709009B8330FDa32311DF1C2AFA402eD8D009`. The C13 verifier's code is unchanged since that deploy, and
the SLH-DSA-SHA2 one verified the pinned KAT (`signers/slhvk-sha2-128-24/kat-counter0.json`). Older deployments, sample transactions and the (now defunct) ethrex EIP-8141 devnet:
[docs/deployments.md](docs/deployments.md), which also lists the leanSphincs verify and frame transactions
(frame txs: 288K gas for leanSphincs-s, 320K for -f, 385K for leanSphincs; `script/send_frame_tx_leansphincs.py`).

## Formal verification

`verity/` holds a Lean 4 / Verity model of the C13 and SLH-DSA-SHA2-128-24 verifiers, with refinement proofs
against a byte-level spec. The other verifiers are not modelled. Scope, remaining axioms and build steps:
[verity/README.md](verity/README.md).

## More

- [`legacy/`](legacy/README.md): frozen verifiers kept for reproducibility: C6, C8, the JARDIN-layout C10/C11/C12
  originals, SLH-DSA-Keccak-128-24 and leanSphincs-23.
- [`docs/`](docs/): the specs, the security reviews and analysis, and the variant and deployment records above.
- [`signers/README.md`](signers/README.md): every signer and the cross-validation map.

Licensed under the terms in [LICENSE](LICENSE).
