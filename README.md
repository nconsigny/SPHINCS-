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

| Scheme | Family | h | d | a | k | w | l | swn | Sig | sign_h | Verify | Frame | 4337 | sec_10 | sec_14 | sec_18 | sec_20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **C7** | WOTS+C / FORS+C | 24 | 2 | 16 | 8 | 8 | 43 | 151 | 3,704 B | 4.3 M | 96 K | 210 K | 318 K | 128 | 128 | 128 | 128 |
| **C12** | vanilla SPHINCs+ | 20 | 5 | 7 | 20 | 8 | 46 | - | 6,592 B | ~37.3 K | ~204 K | - | - | 128 | 127.8 | 109.1 | 95.4 |
| **C13** | WOTS+C / FORS+C | 22 | 2 | 19 | 7 | 8 | 43 | 208 | 3,688 B | ~10 M | 105 K ♦ | 188 K | 293 K | 128 | 128 | 128 | 128 |
| **SLH-DSA-Keccak-128-24** | vanilla SPHINCs+ | 22 | 1 | 24 | 6 | 4 | 68 | - | 3,856 B | ~1.07 B | ~94 K | - | - | 128 | 128 | 128 | 128 |
| **leanSphincs-S** | leanSphincs (WOTS+C / FORS) | 26 | 1 | 12 | 13 | 4 | 64 | 128 | 4,164 B | see below | ~39 K | - | - | 128 | 128 | 128 | 128 |

- **Family**: the construction style. WOTS+C / FORS+C is the C-series compact construction with counter grinding
  (ePrint 2025/2203). Vanilla SPHINCs+ is the standard FIPS 205 construction with no counter grinding: C12 and
  SLH-DSA-128-24 are the same algorithm at different parameter sets. leanSphincs is Tom Wambsgans'
  [proposal](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates): one XMSS layer, WOTS+C, and FORS
  without tree roots; leanSphincs-S is the [sphincs-art](https://nconsigny.github.io/sphincs-art/) parameter set.
- **sign_h**: hash calls for keygen plus one signature on a zero-memory signer (no caching between signatures, the
  relevant case for a hardware wallet). A high number means a lot of work for the hardware. leanSphincs-S keeps a
  generated key with a small node cache instead; see [Signing](#signing).
- **swn**: the WOTS+C target sum, i.e. the digit sum the signer grinds its counter for. Vanilla SPHINCs+ uses the
  standard Winternitz checksum and doesn't grind.
- **sec_N**: security bits at 2^N signatures per key. SLH-DSA-128-24 (h=22, d=1) is a **single XMSS tree of
  2²² WOTS leaves**, and the signing leaf is picked pseudorandomly from the message digest. WOTS-leaf collisions
  therefore start around 2¹¹ signatures, well before the named 2²⁴ usage cap. This is expected and **absorbed by
  the FORS few-time layer** (it is not a WOTS forgery): the 128 bits come from the FORS margin, *not* from one-time
  WOTS use, so 2²⁴ is a recommended per-key **usage cap**, not a flat one-time guarantee. See
  [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md). (review SLH-X-f2cap) leanSphincs-S's figures are for a
  full 2²⁶ key, rated for 2²⁶ signatures (sphincs-art estimate, not proved); a pruned key's rating is lower (below).
- **Verify (pure)**: Foundry gas of the verifier call alone (`gasleft()` around the call, or the call frame via
  `vm.lastCallGas` for leanSphincs-S). C12's Forge e2e test prints ~665 K because it also copies the cached
  6,592-B signature out of storage; ~204 K is the verifier itself.
- **Frame**: total EIP-8141 frame-tx gas (ethrex). **4337**: total ERC-4337 `handleOps` tx gas (Sepolia), through
  `SphincsAccount` + `SphincsAccountFactory`. `-` means no account has been deployed for that scheme yet
  (leanSphincs-S plugs into `SphincsAccount` unchanged: `validateUserOp` is ~46.5 K in Forge).
- Frame and 4337 were measured against the deployed verifiers, which predate the October 2026 loop optimisations
  (C7's Verify column); a redeploy should lower each total by roughly the drop in the Verify column.
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
| leanSphincs-S | 159 K / 155 K / 178 K permutations | **27 s** (Light) | **1.2 ms** (Standard) | **0.35 ms** (Full) |

- **leanSphincs-S** follows the page's one-signer tiers: the key is generated once and kept with a node cache.
  Light keeps a 2¹³ subtree in 16 KiB (keygen 1.91 M permutations, 5.5 min on the Ledger; rated 20 K signatures);
  Standard a 2²⁰ subtree in 1 MiB (244 M, 1.9 s; rated 2²¹); Full the whole 2²⁶ tree in 16 MiB (15.6 B, 31 s;
  rated 2²⁶). The signatures are the same in every tier. Our Rust signer (`lssk`) measures 13–32 ms (Light) and
  20–32 ms (Standard) per signature on 8 cores, key loading and a self-check included.
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
- **leanSphincs-S** (`src/keccak/LeanSphincs-SAsm.sol`): leanSphincs's own 16-byte tweak,
  `keccak256(P ‖ tweak ‖ payload)` truncated to 16 bytes, as on the upstream crate's `keccak` branch. Spec:
  [docs/leanSphincs-S-keccak.md](docs/leanSphincs-S-keccak.md).

Key derivation (Rust/WASM signer): BIP-39 mnemonic → `HMAC-SHA512("sphincs-c6-v1", seed)` for the SPHINCs- keys,
and BIP-32 `m/44'/60'/0'/0/0` for the independent ECDSA key. More detail: [CLAUDE.md](CLAUDE.md),
[docs/variants.md](docs/variants.md).

## Signers

| Scheme | Signers |
|---|---|
| C7 / C13 | `script/signer.py` (Python, `c7` / `c13`), `signers/signer-wasm` (Rust/WASM, C13 only, BIP-39) |
| C12 | `script/spx_fips_signer.py` |
| SLH-DSA-128-24 | `signers/sphincsplus-128-24` (C, SHA-2), `signers/noble-slh-dsa` (JS), `signers/slhvk-sha2-128-24` (GPU), `signers/jardin-keccak-128-24` (C, Keccak twin) |
| leanSphincs-S | `signers/leansphincs-s-keccak` (Rust, `lssk`, tiered key files), `script/leansphincs_s_signer.py` (Python) |

Which signer targets which verifier, and how they are cross-checked: [signers/README.md](signers/README.md).

## Quick start

```bash
forge build
pip install eth-account eth-abi requests pycryptodome
forge test --no-match-contract '^SLH_DSA_SHA2_128_24_(Test|CalldataGas)$'   # skips the two slow NIST-parameter signs
(cd signers/leansphincs-s-keccak && cargo test --release)
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

EntryPoint v0.9 on Sepolia: `0x433709009B8330FDa32311DF1C2AFA402eD8D009`. The C13 verifier's code is unchanged since that deploy, and
the SLH-DSA-SHA2 one verified the pinned KAT (`signers/slhvk-sha2-128-24/kat-counter0.json`). Older deployments, sample transactions and the (now defunct) ethrex EIP-8141 devnet:
[docs/deployments.md](docs/deployments.md).

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
