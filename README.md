# SPHINCS- Post-Quantum Ethereum verifiers

---

> ## WARNING: RESEARCH PROTOTYPE - NOT FOR PRODUCTION USE
>
> This codebase is a scheme exploration for lightweight variants of SPHINCS+ (called SPHINCs-).
> It has **not been audited yet**, and is
> **not safe to use with real funds**.

---
**Welcome to SPHINCs-**, a family of EVM-optimised variants of SLH-DSA and the recently proposed [SLH-DSA-SHA2-128-24](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-230.ipd.pdf). They all achieve low gas cost for pure on-chain signature verification without any precompile which makes them useful today without any ethereum hardfork. The key modifications is substituting SHAKE256 with the native keccak256 opcode and a significant reduction of the signature budget. NIST initially standardized a scheme with a 2^64 signature budget which is a huge number. Ethereum's on chain data shows that among 64,294,251 Ethereum mainnet addresses that sent at least one transaction in 2025 99.99% had less than 3000 transactions annually. The variants described in the repo give a trade-off between signing budget per key pair, verifier cost in gas and signer keygen and signing keccak calls (hardware wallet friendliness).

One can simply build a smart account using any of these verifiers, they are stateless and they maintain 128bits up their specified limits. For a efficient design that works on constrained device you can use the JARDÍN account design (A combination of SPHINCs- with a smaller compact path) are available for this. The SPHINCS+ registration path, the FORS compact path, all the JARDIN contracts and signers lives in a separate repo: [`nconsigny/JARDIN`](https://github.com/nconsigny/JARDIN).

---

## Variants

There are different ways to construct the SPHINCS signature scheme. Existing litterature shows various ways to optimise for signature size or verify cost.

| Variant | Family | h | d | a | k | w | l | swn | Sig | sign_h | Verify | Frame | 4337 | sec_10 | sec_14 | sec_18 | sec_20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **C7** | WOTS+C / FORS+C | 24 | 2 | 16 | 8 | 8 | 43 | 151 | 3,704 B | 4.3 M | 127 K | 210 K | 318 K | 128 | 128 | 128 | 128 |
| **C11** | WOTS+C / FORS+C | 16 | 2 | 11 | 13 | 8 | 43 | 203 | 3,976 B | 292 K | 116 K | 202 K | 308 K | 128 | 128 | 104.5 | 86.1 |
| **C13** † | WOTS+C / FORS+C | 22 | 2 | 19 | 7 | 8 | 43 | 208 | 3,688 B | ~10 M | **105 K** | **188 K** | **293 K** | 128 | 128 | 128 | 128 |
| **C12** | vanilla SPHINCs+ | 20 | 5 | 7 | 20 | 8 | 45 | - | 6,512 B | 36.6 K | 276 K | - | - | 128 | 127.8 | 109.1 | 95.4 |
| **SLH-DSA-SHA2-128-24** | vanilla SPHINCs+ | 22 | 1 | 24 | 6 | 4 | 68 | - | 3,856 B | ~1.07 B | ~142 K | - | - | 128 | 128 | 128 | 128 |
| **SLH-DSA-Keccak-128-24** | vanilla SPHINCs+ | 22 | 1 | 24 | 6 | 4 | 68 | - | 3,856 B | ~1.07 B | ~94 K | - | - | 128 | 128 | 128 | 128 |

- **Family**: the SPHINCS+ construction style (vanilla SPHINCs+ SPX, WOTS +). WOTS+C / FORS+C is the C-series compact construction with counter-grinding (ePrint 2025/2203). Plain SLH-DSA / SPHINCS+ is the standard FIPS 205 construction with no counter grinding: C12 and the two SLH-DSA-128-24 entries are the same algorithm at different parameter sets, with the SHA-2 row using the FIPS 22-byte ADRSc + SHA-256 hash.
- **sign_h**: hash-function calls during keygen + one signature, zero-memory signer (no inter-sign caching, the relevant case for a hardware wallet). A high number means a lot of work for the hardware. C12 the lightest is ~40 sec to sign on secure element. 
- **swn**: small-Winternitz-number counter bits used by the WOTS+C / FORS+C grinding. Plain SPX and SLH-DSA don't counter-grind.
- **sec_N**: security bits at 2^N signatures per key. For SLH-DSA-*-128-24 (h=22, d=1) the hypertree is a **single XMSS tree of only 2²² WOTS leaves**, and the signing leaf is chosen *pseudorandomly* from the message digest, so WOTS-leaf collisions appear by the birthday bound (onset ~2¹¹ signatures), well before the named 2²⁴ usage cap. This is expected and **absorbed by the FORS few-time layer** (it is not a WOTS forgery); 128-bit security is carried with the FORS margin, *not* by one-time WOTS use. The "2²⁴" figure is therefore a recommended per-key **usage cap**, not a flat one-time-security guarantee. See [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md) for the budget/collision accounting. (review SLH-X-f2cap)
- **Verify (pure)**: Foundry `gasleft()` measurement of the assembly block.
- **Frame**: total EIP-8141 frame-tx gas (ethrex). C12 / SLH-DSA-128-24 are not yet wired to frame accounts in this repo.
- **4337**: total ERC-4337 `handleOps` tx gas (Sepolia). The 4337 wiring for C7 / C11 lives in `SphincsAccount` + `SphincsAccountFactory`; no SLH-DSA or C12 account exists here yet.
- **†**: C13 uses the **FIPS 205 §4.2 uncompressed 32-byte ADRS layout** with keccak256, not JARDIN's. First verifier on the FIPS address layout (see the *Address layout* subsection below).

### C13 vs the rest of the family: what changes

C13's parameter choice (`h=22 d=2 a=19 k=7 w=8`) was built around three goals: smallest signature, cheapest verify at full 128-bit security across the signature-count window, FIPS-aligned address layout. The numbers above bear out the design:

| Property                       | C7      | C11     | **C13** | C12     | SLH-DSA-SHA2-128-24 | SLH-DSA-Keccak-128-24 |
|--------------------------------|---------|---------|---------|---------|---------------------|-----------------------|
| Sig size                       | 3,704 B | 3,976 B | **3,688 B** ← smallest | 6,512 B | 3,856 B | 3,856 B |
| Pure-asm verify                | 127 K   | 116 K   | **105 K** ← cheapest at sec_20=128 | 276 K | 142 K | 94 K |
| Frame tx total (ethrex)        | 210 K   | 202 K   | **188 K** | n/a | n/a | n/a |
| 4337 handleOps total (Sepolia) | 318 K   | 308 K   | **293 K** | n/a | n/a | n/a |
| Signature-count cap            | 2²⁴     | 2¹⁶     | 2²²     | 2²⁰ (h=20, d=5) | 2²⁴ ‡ | 2²⁴ ‡ |
| Security at the cap            | 128 bit | 86 bit  | **128 bit** | 95 bit | 128 bit § | 128 bit § |
| Hash-call cost / sign (cold)   | 4.3 M   | 292 K   | ~10 M   | 36.6 K | ~1.07 B | ~1.07 B |
| ADRS layout                    | **FIPS uncompressed** | **FIPS uncompressed** | **FIPS uncompressed** | **FIPS uncompressed** | FIPS ADRSc | JARDIN |

‡ **SLH-DSA-*-128-24 cap is a usage cap, not a leaf budget.** h=22, d=1 ⇒ a single XMSS tree of 2²² WOTS leaves; the leaf is chosen pseudorandomly per message, so by 2²⁴ signatures leaves have been reused ~4× on average (and birthday collisions begin ~2¹¹). Unlike C7/C13, whose 2²⁴/2²² figures are the actual hypertree-leaf counts at full one-time-WOTS security, the SLH "2²⁴" exceeds its 2²² leaf space by design.

§ **128 bit at the cap is carried by FORS, not by WOTS one-time-ness.** Pseudorandom leaf reuse is expected and absorbed by the FORS few-time layer (a=24, k=6); a leaf collision is not itself a forgery. See [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md). (review SLH-X-f2cap)

Reading the table:

- **vs C7**: C13 holds full 128-bit security up to its 2²² cap (vs C7's 2²⁴), but verifies in **105 K vs 127 K** (~17 % cheaper) and signs roughly half the hashes. Trade-off: half the signature-count budget per key. Good fit when keys rotate often or the per-key budget is bounded by policy.
- **vs C11**: Same security at sec_14 (128 bit), but C11 collapses to 86 bit at sec_20. C13 holds 128 bit all the way to sec_20. Cost: ~30× higher signer hash count (C13's a=19 FORS trees vs C11's a=11), but **cheapest verify in the C-series**.
- **vs C12** (plain SPHINCS+ without counter grinding): C13 verifies ~2.6× cheaper for a comparable security envelope, with a sig that's ~44 % smaller. C12 wins decisively on signer cost (it has no counter-grinding step at all), so C12 stays the right pick for tightly-constrained signers (e.g. secure-element keys). C13 is the right pick when verify gas matters more than signer time.
- **vs SLH-DSA-SHA2-128-24** (NIST-compliant standalone): C13 is roughly **same sig size** (-4 %) and **~25 % cheaper to verify**, with ~100× lower signer cost. The trade is that SLH-DSA is the FIPS 205 NIST-blessed parameter set; C13 is a research parameter choice in the ePrint 2025/2203 family. C13's ADRS layout now matches FIPS to keep cross-impl porting clean.
- **Smallest signature** of any variant in the repo. The combination `k=7, a=19` with the 4 B count tail and 11-level subtree gives the leanest payload.

The takeaway: **C13 is the cheapest verifier in the repo at 128-bit security up to a 2²² sig cap**, and the smallest signature. The cost is sign-time, which is ~30× C11 and ~2× C7. For an Ethereum smart account that signs occasionally and is verified by everyone, that asymmetry is the right shape.

C11 and C12 are light enough to run on a hardware wallet, 390s and 47.5s signature times on a ST33K1M5 secure element (Ledger nano S+). C12 has the lowest hardware signer cost of all (36 K hashes - plain SPX with d=5 hypertree skips most tree-hash work) at the price of a 6,512-byte sig. SLH-DSA-SHA2-128-24 is the FIPS-aligned alternative: much larger signer cost even on a desktop-class signer that caches the XMSS tree (~200 M hashes / sig, dominated by FORS, which can't be cached because the leaf-index to FORS-tree-address mapping changes with every message), and ~1.07 B / sig on a zero-memory signer that has to rebuild the 2²²-leaf XMSS for every auth path. 128-bit security across the 2²⁴ usage window is carried by the FORS few-time layer absorbing the expected pseudorandom WOTS-leaf reuse over the 2²² leaf space (‡/§ above; [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md)), not by one-time WOTS use. The SHA-2 verifier implements **FIPS 205 *external* SLH-DSA.Verify with an empty context** (M wrapped as `0x00‖0x00‖M` before H_msg), so it matches published NIST/ACVP external KAT vectors. The Keccak twin trades bit-exact NIST compliance for ~34 % cheaper on-chain verification (but not a very interesting trade-off as it keeps the same signer cost).

## Stateless SPHINCs- Architecture

### Shared hash kernel

Live verifiers in `src/` are organized **one folder per hash function**: `src/keccak/`, `src/sha/`, and `src/blake/` (accounts stay in `src/` root). There are **three hash backends** but still **only two ADRS byte layouts**, both straight out of FIPS 205: **FIPS uncompressed 32 B** (keccak *and* BLAKE2b families) and **FIPS ADRSc 22 B** (SHA-2 family) — the BLAKE2b twins reuse the keccak FIPS uncompressed layout verbatim. The keccak C-series all migrated off JARDIN to FIPS uncompressed (C13 first, then C7/C9, then C11/C12); only the keccak SLH-DSA twin stays on JARDIN, **retired to `legacy/`** (along with the JARDIN-layout C11/C12 originals, kept for benchmark reproducibility and the [nconsigny/JARDIN](https://github.com/nconsigny/JARDIN) repo's `JardinSpxVerifier` reference).

`src/sha/` holds the **SHA-256 twins** of C11/C13/C12 plus the NIST SLH-DSA-SHA2. C11-SHA/C13-SHA are *minimal twins* (compact construction kept; not FIPS — one-shot H_msg, MSB-first parsing); C12-SHA is *full FIPS 205 SLH-DSA-SHA2* at C12 params (MGF1 H_msg, empty-context envelope). See [SHA-256 twins](#sha-256-twins-srcsha) below. `src/blake/` holds the **BLAKE2b twins** of C11/C13/C12 — minimal twins of the keccak C-series with only the hash swapped (keccak256 → BLAKE2b), built on the **BLAKE2F compression precompile 0x09** (EIP-152; *not* a hash — each verifier wraps it with a `blake2b()` Yul kernel that does the BLAKE2b construction + LE↔BE bridging). Not FIPS. Verify gas is far higher (~3–8 M) — inherent to a compression-only precompile.

| Layout | Variants | ADRS bytes | Hash | F/H/T input |
|---|---|---|---|---|
| **FIPS uncompressed 32 B** (`src/keccak/`) | **C7, C9, C11, C12, C13** (C13 first)          | `layer4 ‖ tree12 ‖ type4 ‖ word1·4 ‖ word2·4 ‖ word3·4` | keccak256 | `seed32 ‖ adrs32 ‖ payload` |
| **FIPS uncompressed 32 B** (`src/blake/`) | C11-BLAKE, C13-BLAKE, C12-BLAKE | `layer4 ‖ tree12 ‖ type4 ‖ word1·4 ‖ word2·4 ‖ word3·4` | BLAKE2b (precompile 0x09, F-only) | `seed32 ‖ adrs32 ‖ payload` |
| **FIPS ADRSc 22 B** (`src/sha/`) | C11-SHA, C13-SHA, C12-SHA, SLH-DSA-SHA2-128-24 | `layer1 ‖ tree8 ‖ type1 ‖ 12 B type-dependent` | SHA-256 (precompile 0x02) | `PK.seed(16) ‖ zeros(48) ‖ ADRSc(22) ‖ payload` |
| _JARDIN 32 B (retired → `legacy/`)_ | SLH-DSA-Keccak-128-24; legacy C11/C12 originals | `layer4 ‖ tree8 ‖ type4 ‖ kp4 ‖ ci4 ‖ cp4 ‖ ha4` | keccak256 | `seed32 ‖ adrs32 ‖ payload` |

### SHA-256 twins (`src/sha/`)

SHA-256 + 22-byte ADRSc versions of the keccak verifiers, for deployments that prefer the SHA-256 precompile (e.g. cross-impl alignment with the FIPS SHA-2 family) over native keccak. The hash and address change as a coupled unit (SHA-256; FIPS §11.2 ADRSc; MSB-first `base_2b` parsing); they cost more gas than the keccak originals (SHA-256 precompile staticcall vs native opcode).

| Variant | Construction | FIPS? | Sig | Verify gas (harness) |
|---|---|---|---|---|
| **C11-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 3,976 B | ~473 K |
| **C13-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 3,688 B | ~440 K |
| **C12-SHA** | plain SPHINCS+, full FIPS 205 SLH-DSA-SHA2 (MGF1 H_msg, `0x00‖0x00` envelope, standard checksum) | Algorithm yes; params not a NIST set (no KAT) | 6,496 B | ~908 K |

The compact twins (C11/C13) **cannot** be made FIPS-compliant — their WOTS+C/FORS+C counter-grinding has no FIPS 205 analog — so they only borrow the SHA-256 hash + ADRSc. C12 is plain SPHINCS+, so it takes the full FIPS algorithm. Vectors: `script/signer.py {c11-sha,c13-sha}` and `script/slh_dsa_sha2_c12_signer.py`.

### Address layout

**FIPS 205 §4.2 uncompressed 32-byte ADRS** (the SHAKE-instantiation form):

```
bytes  0.. 4  layer address       (uint32)
bytes  4..16  tree address        (96 bits big-endian; top 4 B = 0 in current instances)
bytes 16..20  type                (uint32)
bytes 20..24  word1 (type-dependent)
bytes 24..28  word2 (type-dependent)
bytes 28..32  word3 (type-dependent)
```

| type | name | word1 | word2 | word3 |
|---|---|---|---|---|
| 0 | WOTS_HASH  | key_pair_address | chain_address | hash_address |
| 1 | WOTS_PK    | key_pair_address | 0 | 0 |
| 2 | TREE       | 0 | tree_height | tree_index |
| 3 | FORS_TREE  | key_pair_address | tree_height | tree_index |
| 4 | FORS_ROOTS | key_pair_address | 0 | 0 |

**JARDIN 32-byte ADRS** (retired to `legacy/`; was used by C7/C9/C11/C12/SLH-DSA-Keccak before all the C-series migrated to FIPS uncompressed): same 32-byte width, but with an 8-byte `tree` field (FIPS gives it 12) and **four** type-dependent words (FIPS uses three). The freed-up byte budget went to `ci` (chain_index) being a dedicated WOTS-only slot, while in FIPS `chain_address` and `tree_height` share `word2` (same bytes, type-dependent meaning). JARDIN's 4th word (`ha`) is unused for every type in practice; the structural divergence from FIPS is the 8 vs 12 byte tree field.

**Why C13 moved to FIPS uncompressed.** "Reduce differences between families": FIPS-aligning the ADRS makes the keccak verifier port cleanly from a FIPS reference implementation, and pares the repo's address-layout inventory toward just two layouts (above). The hash stays keccak256; switching to SHA-256 would double on-chain gas (precompile staticcall vs native opcode) and would only be relevant if we needed full SLH-DSA-SHA2 family alignment, which we don't.

**SLH-DSA-128-24 family**, two wire-level layouts:
  - **SHA-2 variant**: FIPS 205 §11.2.1 hashing, **external SLH-DSA.Verify with empty context**: ADRSc (22 B), SHA-256 via precompile, message wrapped as `M' = 0x00 ‖ 0x00 ‖ M` (empty-ctx envelope), nested `Hmsg = MGF1-SHA-256(R ‖ seed ‖ SHA-256(R ‖ seed ‖ root ‖ M'), m=21)`, **big-endian (MSB-first) digest-to-indices** (`md[t] = BE(digest[3t..3t+3])`, the FIPS 205 / current PQClean convention; *not* the legacy LSB-first SPHINCS+ reference). Matches published NIST/ACVP *external* KATs; signers prepend the same `0x00 0x00`. (review SLH-X-f1)
  - **Keccak variant**: JARDIN twin: 32-byte JARDIN ADRS (`layer4 ‖ tree8 ‖ type4 ‖ kp4 ‖ ci4 ‖ cp4 ‖ ha4`), keccak256 primitive, F / H / T input = `seed32 ‖ adrs32 ‖ payload`, one-shot `Hmsg = keccak(seed ‖ root ‖ R ‖ msg ‖ 0xFF..FB)` (no MGF1), LSB-first digest-to-indices on the 256-bit keccak output interpreted as a single big-endian integer.

### Shared Verifier Model

The SPHINCS- verifier is **deployed once** and shared by all accounts. Follows the [ZKnox/Kohaku](https://github.com/ethereum/kohaku/tree/master/examples/pq-account) pattern.

```
SPHINCs-Asm (deployed once, stateless, pure)
    ↑ verify(pkSeed, pkRoot, message, sig) → bool
    │
    ├── SphincsAccount (4337)       ← keys in storage, rotatable
    └── FrameAccount (EIP-8141)     ← keys in storage, rotatable
```

### ERC-4337 Hybrid Account

The account stores keys as immutables and passes them to the shared verifier on each UserOp.

```
EntryPoint.handleOps()
    └── SphincsAccount._validateSignature()
            ├── ECDSA.recover(userOpHash, ecdsaSig) == owner
            └── sharedVerifier.verify(pkSeed, pkRoot, userOpHash, sphincsSig) == true
```

### EIP-8141 Frame Transaction (Pure PQ)

The frame account has keys baked into its bytecode - no storage, no calldata overhead for keys. It receives `sigHash + raw_sig`, builds the full ABI call to the shared verifier internally, and calls APPROVE on success.

```
Frame Transaction (type 0x06)
    ├── Frame 0 (VERIFY): frame account builds verify(pkSeed, pkRoot, sigHash, sig)
    │     from embedded keys + calldata → STATICCALLs shared verifier → APPROVE
    └── Frame 1 (SENDER): ETH transfer / contract call
```
No ECDSA - pure post-quantum. Keys are stored in EVM storage (not bytecode) to support future key rotation via `rotateKeys()` - costs ~4K gas per verify but keeps the same account address across key changes.

## Key Derivation

### BIP-39 Path (Rust WASM signer)

```
BIP-39 mnemonic (12 or 24 words)
    │
    ├──▶ HMAC-SHA512("sphincs-c6-v1", seed) → pkSeed, sk_seed (quantum-safe)
    └──▶ BIP-32 m/44'/60'/0'/0/0 → ECDSA address (independent)
```

SPHINCs- and ECDSA are derived through independent paths - compromising one does not compromise the other.

## Signers

| Signer | Language | Targets | BIP-39 |
|---|---|---|---|
| `script/signer.py` | Python | C-series (C7/C9/C11/C13) + SHA twins (c11-sha/c13-sha) | No |
| `signer-wasm/` | Rust/WASM | C-series | **Yes** |
| `script/slh_dsa_sha2_128_24_signer.py` | Python (slow; ~hours at NIST params) | SLH-DSA-SHA2-128-24 | No |
| `script/slh_dsa_keccak_128_24_signer.py` | Python (slow; ~hours at NIST params) | SLH-DSA-Keccak-128-24 | No |
| `signers/sphincsplus-128-24/` | C (forked from sphincs/sphincsplus ref) | SLH-DSA-SHA2-128-24 | No, seeds fed in |
| `signers/jardin-keccak-128-24/` | C (sphincsplus fork + custom keccak + 32-B ADRS) | SLH-DSA-Keccak-128-24 | No |

```bash
# Rust WASM C-series signer
cd signer-wasm && wasm-pack build --release --target web
cargo test --release -- --ignored

# SLH-DSA-128-24 fast C signers (~11 min per NIST-params sign on pure C, no SHA-NI)
(cd signers/sphincsplus-128-24  && make)
(cd signers/jardin-keccak-128-24 && make)
# Python wrapper with disk cache; Forge FFI tests use these:
python3 script/slh_dsa_sha2_128_24_fast_signer.py   <master_sk_hex> <message_hex>
python3 script/slh_dsa_keccak_128_24_fast_signer.py <master_sk_hex> <message_hex>
```

## Deployed Contracts & Transactions

EntryPoint v0.9: `0x433709009B8330FDa32311DF1C2AFA402eD8D009` (Sepolia)

### 2026-06-04 redeploy: new accounts & factories

New C13 `SphincsAccountFactory` instances and freshly-deployed accounts (each account funded 0.1 ETH):

| Chain | Contract | Address |
|---|---|---|
| Sepolia | SphincsAccountFactory | [`0x8830d3...`](https://sepolia.etherscan.io/address/0x8830d36284829656F2A60CD028062686069FABA4) |
| Sepolia | SphincsAccountFactory (fresh) | [`0x79FDD0...`](https://sepolia.etherscan.io/address/0x79FDD0aFcb2214D6C17E639dA7eF6357956Cd857) |
| Sepolia | SphincsAccount (ERC-4337 hybrid, C13) | [`0x012801...`](https://sepolia.etherscan.io/address/0x01280171F336869e9c96F9e6eb674b1548D10dD4) |
| ethrex | SphincsAccountFactory | [`0x874f5b...`](https://explorer.eip-8141.ethrex.xyz/address/0x874f5ba1d47B477CB70999795cAf7E6Bb53EeDD7) |
| ethrex | Frame account (EIP-8141, C13) | [`0x253A4d...`](https://explorer.eip-8141.ethrex.xyz/address/0x253A4d0100fe7A2a6d6839b37BDC283FD1dF693d) |

> ethrex's `SphincsAccountFactory` is deployed for completeness, but EntryPoint v0.9 has no code on ethrex, so accounts created there are inert for ERC-4337. ethrex's functional PQ path is the EIP-8141 frame account. Full address record: [`script/.c13_addresses.json`](./script/.c13_addresses.json).

### Sepolia (ERC-4337 Hybrid, C-series)

| Variant | Verifier | Account | Gas | Tx |
|---|---|---|---|---|
| C9 | [`0x18F005...`](https://sepolia.etherscan.io/address/0x18F005EECd41624644AA364bA8857258FEB3C26D) | [`0xA94111...`](https://sepolia.etherscan.io/address/0xA941116763AE386a50133c5af40356c9D93b2978) | 300 K | [`0x8366513b...`](https://sepolia.etherscan.io/tx/0x8366513b096ee53dd1cb105363ab21a52267dd966b822b4bb2cf5492abf1550f) |
| C11 | [`0xC25ef5...`](https://sepolia.etherscan.io/address/0xC25ef566884DC36649c3618EEDF66d715427Fd74) | [`0x3C3b0c...`](https://sepolia.etherscan.io/address/0x3C3b0c3498E5ed9350F6fBFA0Ef8dC55f524eA50) | 308 K | [`0x9fba169c...`](https://sepolia.etherscan.io/tx/0x9fba169ca76b6712586e44e1a4a2d0407b8b8b9ce767272a193e41a756260b74) |
| **C13** | [`0xce176d...`](https://sepolia.etherscan.io/address/0xce176df2680f6612a61486f74502db62d014d23d) | [`0xcef985...`](https://sepolia.etherscan.io/address/0xcef985d4db485e96ab9187ad462561bff241db0d) (factory [`0xcaf5d2...`](https://sepolia.etherscan.io/address/0xcaf5d2582eb405e3c4b65f3a52d147badfd96fed)) | 293 K | [`0xbbf06456...`](https://sepolia.etherscan.io/tx/0xbbf06456145a4daea1b5006f1f5d7b214c62c1c2877eabb61ae4b26e453189d0) |

> **C13 on Sepolia uses the FIPS 205 §4.2 uncompressed 32-byte ADRS** (keccak256 hash). First verifier in the repo on the FIPS address layout. Standalone verify tx-level gas: **188,278**. Full hybrid-4337 `handleOps` UserOp gas: **292,727** (ECDSA recovery + C13 verify + 0.00001 ETH self-transfer through `SphincsAccount.execute`). See [`script/.c13_addresses.json`](./script/.c13_addresses.json) for the canonical address record.

### Sepolia (SLH-DSA-128-24 standalone verifiers, no account wired yet)

| Variant | Verifier | Deploy tx | Sample verify tx | Verify-tx gas |
|---|---|---|---|---|
| SLH-DSA-SHA2-128-24 | [`0x9Fe417...`](https://sepolia.etherscan.io/address/0x9Fe41769395BC9fefb7e0d340064ed29F4a4Af91) | [`0x09be3c59...`](https://sepolia.etherscan.io/tx/0x09be3c5984ed99a93f9c43881822d9937e1efa9b31aee0630f59fca814d90e15) | [`0x00fa6b37...`](https://sepolia.etherscan.io/tx/0x00fa6b37347e2bedf37429a74563b2c68502becdffe3257ebde90f63e165030a) | **225,642** |
| SLH-DSA-Keccak-128-24 | [`0x2Ac9Ec...`](https://sepolia.etherscan.io/address/0x2Ac9Ec4a2A062aFc1be718e77ec3300D087E6205) | [`0x253aa6dc...`](https://sepolia.etherscan.io/tx/0x253aa6dc5c93a201abc7a5cfb4ce27cdeafb35e34fc69c23ef1daae0535c4c4a) | [`0x90d785a1...`](https://sepolia.etherscan.io/tx/0x90d785a112fd0198b4506caf432632777aef43b00ceb648e864dcb119311fed4) | **177,910** |

Verify-tx gas is the full top-level tx cost including 21 K tx base + ~63 K for the 3,872-B calldata payload; pure assembly execution is ~142 K (SHA-2) / ~94 K (Keccak). Keccak wins by ~21 % tx-level and ~34 % assembly-level because every F / H / T is a single native `keccak256` opcode, while the SHA-2 variant pays a `staticcall(0x02)` dispatch per hash × ~280 hashes.

### ethrex Testnet (EIP-8141 Frame Tx - Pure PQ)

Older demo devnet at `demo.eip-8141.ethrex.xyz` (chain 1729): C9 / C10 / C11 frame accounts:

| Variant | Verifier | Frame Account | Gas | Verify | Tx |
|---|---|---|---|---|---|
| C9 | [`0xc0F115...`](https://demo.eip-8141.ethrex.xyz:8082/address/0xc0F115A19107322cFBf1cDBC7ea011C19EbDB4F8) | [`0xc96304...`](https://demo.eip-8141.ethrex.xyz:8082/address/0xc96304e3c037f81dA488ed9dEa1D8F2a48278a75) | 195K | 117K | [`0x393588ec...`](https://demo.eip-8141.ethrex.xyz:8082/tx/0x393588eceeda4839371f103e16b10c5e2900416d7b194faee8478b6561792813) |
| C10 | [`0xD0141E...`](https://demo.eip-8141.ethrex.xyz:8082/address/0xD0141E899a65C95a556fE2B27e5982A6DE7fDD7A) | [`0x07882A...`](https://demo.eip-8141.ethrex.xyz:8082/address/0x07882Ae1ecB7429a84f1D53048d35c4bB2056877) | 203K | 122K | [`0x0a2571f8...`](https://demo.eip-8141.ethrex.xyz:8082/tx/0x0a2571f8423ab4ec75e09623773b22ff91794a82d1b3db2d616b8af354730353) |
| C11 | [`0x315575...`](https://demo.eip-8141.ethrex.xyz:8082/address/0x3155755b79aA083bd953911C92705B7aA82a18F9) | [`0x5bf5b1...`](https://demo.eip-8141.ethrex.xyz:8082/address/0x5bf5b11053e734690269C6B9D438F8C9d48F528A) | 202K | 122K | [`0x053428f5...`](https://demo.eip-8141.ethrex.xyz:8082/tx/0x053428f530521a5c42c4d2406d1cfb8e07baefa0328c0e425045a3ba9317106b) |

Current `eip-8141.ethrex.xyz` devnet (chain **3151908**, Osaka fork, frame opcodes enabled from genesis; RPCs `rpc1`/`rpc2`/`rpc3.eip-8141.ethrex.xyz`):

| Variant | Verifier | Frame Account | Frame Gas | Sample Frame Tx |
|---|---|---|---|---|
| **C13** | [`0x659415...`](https://explorer.eip-8141.ethrex.xyz/address/0x6594157F1d690CbeBAA93dD13579FEb14E81F5C9) | [`0xae3bA3...`](https://explorer.eip-8141.ethrex.xyz/address/0xae3bA3e1DC1bD3866608ECA1498D3e9263B3481a) | **188 K** | [`0xabf3ce2f...`](https://explorer.eip-8141.ethrex.xyz/tx/0xabf3ce2f989fbb1480af2a6c0026f2335b643adb54561ebb536824af8faee81d) |

> EIP-8141 type-0x06 frame tx, two frames: `[VERIFY(frame_account, sigHash‖c13_sig, flags=approve sender+payer), SENDER(0x...dead, value=0.00001 ETH)]`. The VERIFY frame's runtime staticcalls the shared C13 verifier and `APPROVE(0,0,3)`s on success. Sender by the frame account itself (no protocol-level signature needed). Reproduce with `script/send_frame_tx_c13.py`. Note: ethrex's on-chain `FrameTransaction` RLP layout differs from the draft EIP-8141 markdown by omitting the `signatures` field: the script handles this; the deviation is documented inline.

## Setup

```bash
forge build
pip install eth-account eth-abi requests pycryptodome
cd signer-wasm && cargo build --release
```

## Usage

```bash
# ── C-series (stateless hybrid + frame accounts) ───────────────────────────
# Deploy shared C-series verifier + SphincsAccountFactory (once):
forge script legacy/script/DeploySepolia.s.sol --rpc-url sepolia --broadcast

# Create account + send hybrid ERC-4337 UserOp (C7 / C11):
python3 legacy/script/send_userop.py create \
  --factory <factory> --ecdsa-key $PRIVATE_KEY --variant c7
python3 legacy/script/send_userop.py send \
  --account <account> --ecdsa-key $PRIVATE_KEY \
  --to <recipient> --value 0.001 --variant c7

# ── SLH-DSA-128-24 (standalone verifiers, no account) ──────────────────────
# Deploy both SLH-DSA verifiers to Sepolia:
forge script script/DeploySlhDsa128_24Sepolia.s.sol --rpc-url sepolia --broadcast

# Build the fast C signer (used by Forge FFI tests, ~11 min per NIST-params sign):
(cd signers/sphincsplus-128-24  && make)  # SHA-2 variant
(cd signers/jardin-keccak-128-24 && make) # Keccak variant

# Run the Forge end-to-end verify tests (first run triggers a real sign; later
# runs hit the disk cache at signers/*/\.cache/):
forge test --match-contract SLH_DSA_SHA2_128_24_Test   -vv
forge test --match-contract SLH_DSA_Keccak_128_24_Test -vv
```

## Tests

```bash
forge test
cd signer-wasm && cargo test --release -- --ignored
```

## Formal Verification (Lean 4 / Verity)

This repo ships a small Verity workbench under `verity/`. It models a strict
subset of the live Solidity verifiers and proves that each model refines a
functional spec. Source-to-model fidelity (the transcription of the
handwritten Solidity assembly into Lean) is a review and differential-testing
assumption; it is not itself a Verity obligation.

### Scope of the modeled verifiers

The Verity workbench currently models only two production verifiers:

- `src/keccak/SPHINCs-C13Asm.sol` (keccak; the main production verifier). The model
  includes the public-key canonicality guard from the Solidity: `pkSeed` and
  `pkRoot` must each equal themselves masked by `N_MASK`, otherwise the
  verifier reverts with `Invalid public key`.
- `src/sha/SLH-DSA-SHA2-128-24verifier.sol` (FIPS 205 external SLH-DSA, empty
  context, SHA-256 precompile).

The other live production verifiers, `src/keccak/SPHINCs-C7Asm.sol`,
`src/keccak/SPHINCs-C9Asm.sol`, `src/keccak/SPHINCs-C11Asm.sol`, and
`src/keccak/SPHINCs-C12Asm.sol`, are **not** modeled and **not** verified. Treat
them as unverified code. Any future Verity coverage would be a separate
change.

The old C12 Verity model (which targeted the JARDIN-layout C12) has been
removed; C12 has since been migrated to FIPS uncompressed and lives in
`src/` again, but remains unmodeled. The old `SphincsC6/`, `SphincsC6Full/`,
`SphincsC6V/`, and `SphincsKernel/` work, the `verity/artifacts/` Yul
artifacts, and `test/MerkleKernelVerityTest.t.sol` have been removed from
this tree. After this change, no Verity artifact is exercised by Foundry;
nothing in `verity/` is compiled into a production contract or replayed
in the test suite.

### What the models are, and what they are not

The Verity models in `verity/SphincsMinusVerifiers/Model.lean` are
**hand-transcribed** from the Solidity inline assembly. They mirror the
handwritten assembly structure (stacks, memory, and Yul revert fragments)
and use Verity's ABI-aware `Bytes` parameter locals (`sig.length`,
`sig.offset`).

- The models are **not** compiled into the production contracts.
- The models are **not** deployed.
- The models are **not** replayed in the Foundry test suite. There is no
  EVM-side regression test that takes the Lean model and runs it against
  the on-chain verifier.
- The proof target is model-to-byte-spec correspondence inside Lean.
  Correspondence between the model and the deployed code rests on the
  transcription itself being reviewed against the assembly.

### Where the specs and models live

- `verity/SphincsMinusVerifierSpec/Spec.lean` defines the byte-level
  contract spec (`ByteLevel.verifyBytes`) and the abstract algorithmic
  spec (`verifyParsed`, `verifySpec`). The byte spec refines the
  algorithmic spec unconditionally: `verifyBytes_eq_verifySpec` and
  `byteVerifier_refines_spec` are proved with no assumptions beyond
  `propext`.
- `verity/SphincsMinusVerifierSpec/C13Concrete.lean` and
  `C13Mirror.lean` (plus the matching `Axioms` files) provide the
  hand-coded `Primitives` instances and concrete FORS / hypertree
  arithmetic that the algorithmic spec is checked against.
- `verity/SphincsMinusVerifiers/Model.lean` holds the hand-transcribed
  Verity models for the C13 keccak verifier and the
  SLH-DSA-SHA2-128-24 verifier.
- `verity/SphincsMinusVerifiers/Proofs.lean` is the per-verifier
  refinement surface, with `c13_refines_spec` and
  `slhDsaSha2_128_24_refines_spec` as the top-level theorems.

### Proof state and remaining trust surface

- `c13_refines_spec` is currently proved in Lean and rests on Lean's
  logic plus three named residual assembly axioms, all enumerated in
  `verity/SphincsMinusVerifiers/AXIOMS.md`. The keccak hashing in the
  C13 model is concrete (the interpreter's own pure Keccak), so no
  opaque primitive axiom remains on the C13 side. A follow-up PR is
  discharging the residual assembly axioms; once it lands,
  `c13_refines_spec` will rest on Lean's logic alone.
- `slhDsaSha2_128_24_refines_spec` is proved in Lean but additionally
  keeps a named bridge axiom for byte-addressed memory modeling (the
  SHA-256 precompile path uses overlapping sub-word `mstore`s that the
  current word-keyed interpreter does not represent) and an opaque
  SHA-256 primitives constant.
- A hand-held walkthrough of what SPHINCS- is, what a correct verifier
  must check, and how the proof is structured is at
  **https://lfglabs.dev/research/sphincs-minus-verifier**.

The full remaining trust surface (every named bridge axiom, opaque
primitive, and residual assembly axiom) is enumerated in
`verity/SphincsMinusVerifiers/AXIOMS.md`. Cryptographic security of the
scheme itself (hash collision resistance, EUF-CMA) is an assumption
outside the proofs, not a Lean axiom; the theorems establish
implementation correctness only. The README is worded so it
stays true in both proof states: as of today, and after the residual
assembly obligations are discharged.
