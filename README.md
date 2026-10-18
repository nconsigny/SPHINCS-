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
| **C7** | WOTS+C / FORS+C | 24 | 2 | 16 | 8 | 8 | 43 | 151 | 3,704 B | 4.3 M | 96 K | 210 K | 318 K | 128 | 128 | 128 | 128 |
| **C10** | WOTS+C / FORS+C | 18 | 2 | 11 | 13 | 8 | 43 | 205 | 4,008 B | 609 K | 87 K | 203 K | 308 K | 128 | 128 | 128 | 104.5 |
| **C11** | WOTS+C / FORS+C | 16 | 2 | 11 | 13 | 8 | 43 | 203 | 3,976 B | 292 K | 87 K | 202 K | 308 K | 128 | 128 | 104.5 | 86.1 |
| **C13** † | WOTS+C / FORS+C | 22 | 2 | 19 | 7 | 8 | 43 | 208 | 3,688 B | ~10 M | **105 K** | **188 K** | **293 K** | 128 | 128 | 128 | 128 |
| **C12** | vanilla SPHINCs+ | 20 | 5 | 7 | 20 | 8 | 46 | - | 6,592 B | ~37.3 K | ~204 K | - | - | 128 | 127.8 | 109.1 | 95.4 |
| **SLH-DSA-SHA2-128-24** | vanilla SPHINCs+ | 22 | 1 | 24 | 6 | 4 | 68 | - | 3,856 B | ~1.07 B | ~142 K | - | - | 128 | 128 | 128 | 128 |
| **SLH-DSA-Keccak-128-24** | vanilla SPHINCs+ | 22 | 1 | 24 | 6 | 4 | 68 | - | 3,856 B | ~1.07 B | ~94 K | - | - | 128 | 128 | 128 | 128 |

- **Family**: the SPHINCS+ construction style (vanilla SPHINCs+ SPX, WOTS +). WOTS+C / FORS+C is the C-series compact construction with counter-grinding (ePrint 2025/2203). Plain SLH-DSA / SPHINCS+ is the standard FIPS 205 construction with no counter grinding: C12 and the two SLH-DSA-128-24 entries are the same algorithm at different parameter sets, with the SHA-2 row using the FIPS 22-byte ADRSc + SHA-256 hash.
- **sign_h**: hash-function calls during keygen + one signature, zero-memory signer (no inter-sign caching, the relevant case for a hardware wallet). A high number means a lot of work for the hardware. C12 the lightest is ~40 sec to sign on secure element. 
- **swn**: small-Winternitz-number counter bits used by the WOTS+C / FORS+C grinding. Plain SPX and SLH-DSA don't counter-grind.
- **sec_N**: security bits at 2^N signatures per key. For SLH-DSA-*-128-24 (h=22, d=1) the hypertree is a **single XMSS tree of only 2²² WOTS leaves**, and the signing leaf is chosen *pseudorandomly* from the message digest, so WOTS-leaf collisions appear by the birthday bound (onset ~2¹¹ signatures), well before the named 2²⁴ usage cap. This is expected and **absorbed by the FORS few-time layer** (it is not a WOTS forgery); 128-bit security is carried with the FORS margin, *not* by one-time WOTS use. The "2²⁴" figure is therefore a recommended per-key **usage cap**, not a flat one-time-security guarantee. See [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md) for the budget/collision accounting. (review SLH-X-f2cap)
- **Verify (pure)**: Foundry `gasleft()` measurement of the assembly block, i.e. the verifier-only STATICCALL gas. C12's Forge e2e test (`testC12VerifyGas`) prints ~665 K because it also copies the cached 6,592-B sig out of storage; ~204 K is the verifier itself.
- **Frame**: total EIP-8141 frame-tx gas (ethrex). C12 / SLH-DSA-128-24 are not yet wired to frame accounts in this repo.
- **4337**: total ERC-4337 `handleOps` tx gas (Sepolia). The 4337 wiring for C7 / C11 lives in `SphincsAccount` + `SphincsAccountFactory`; no SLH-DSA or C12 account exists here yet.
- Frame and 4337 were measured against the deployed verifiers, which predate the October 2026 loop optimisations of C7 / C10 / C11 (Verify column). They have not been re-measured; a redeploy should lower each total by roughly the drop in the Verify column.
- **†**: C13 uses the **FIPS 205 §4.2 uncompressed 32-byte ADRS layout** with keccak256, not JARDIN's. First verifier on the FIPS address layout (see the *Address layout* subsection below).

> **C12 compatibility note:** the 2026-07-30 correction from `l=45` to
> `l=46` changes both signature encoding and WOTS/XMSS public keys. Existing
> C12 signatures and `pkRoot` values must be regenerated; an account cannot
> migrate by replacing only its verifier.
>
> **C12 key rotation (2026-10, B-01 in [docs/SECURITY-REVIEW-2026-10.md](docs/SECURITY-REVIEW-2026-10.md)):**
> the C12 keccak / BLAKE signer used to derive FORS secrets without the
> hypertree position, so about 1,000 signatures from one key allow a forgery
> on any message that the verifiers accept. The signer is fixed; any C12 key
> that signed with the old signer must be retired, not reused.

### C13 vs the rest of the family: what changes

C13's parameter choice (`h=22 d=2 a=19 k=7 w=8`) was built around three goals: smallest signature, cheapest verify at full 128-bit security across the signature-count window, FIPS-aligned address layout. The numbers above bear out the design:

| Property                       | C7      | C11     | **C13** | C12     | SLH-DSA-SHA2-128-24 | SLH-DSA-Keccak-128-24 |
|--------------------------------|---------|---------|---------|---------|---------------------|-----------------------|
| Sig size                       | 3,704 B | 3,976 B | **3,688 B** ← smallest | 6,592 B | 3,856 B | 3,856 B |
| Pure-asm verify                | 96 K    | 87 K    | **105 K** ¶ | 204 K | 142 K | 94 K |
| Frame tx total (ethrex)        | 210 K   | 202 K   | **188 K** | n/a | n/a | n/a |
| 4337 handleOps total (Sepolia) | 318 K   | 308 K   | **293 K** | n/a | n/a | n/a |
| Signature-count cap            | 2²⁴     | 2¹⁶     | 2²²     | 2²⁰ (h=20, d=5) | 2²⁴ ‡ | 2²⁴ ‡ |
| Security at the cap            | 128 bit | 86 bit  | **128 bit** | 95 bit | 128 bit § | 128 bit § |
| Hash-call cost / sign (cold)   | 4.3 M   | 292 K   | ~10 M   | ~37.3 K | ~1.07 B | ~1.07 B |
| ADRS layout                    | **FIPS uncompressed** | **FIPS uncompressed** | **FIPS uncompressed** | **FIPS uncompressed** | FIPS ADRSc | JARDIN |

‡ **SLH-DSA-*-128-24 cap is a usage cap, not a leaf budget.** h=22, d=1 ⇒ a single XMSS tree of 2²² WOTS leaves; the leaf is chosen pseudorandomly per message, so by 2²⁴ signatures leaves have been reused ~4× on average (and birthday collisions begin ~2¹¹). Unlike C7/C13, whose 2²⁴/2²² figures are the actual hypertree-leaf counts at full one-time-WOTS security, the SLH "2²⁴" exceeds its 2²² leaf space by design.

§ **128 bit at the cap is carried by FORS, not by WOTS one-time-ness.** Pseudorandom leaf reuse is expected and absorbed by the FORS few-time layer (a=24, k=6); a leaf collision is not itself a forgery. See [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md). (review SLH-X-f2cap)

¶ **C13 has not had the loop optimisations yet.** Its verifier is pinned by the Lean model in `verity/`, so it does not carry the in-place T buffers, incremental auth-path climbs, ADRS-as-counter WOTS chains and SWAR checksum that took C7 / C9 / C10 / C11 / C12 down ~22–24 %. Until it does, C7 verifies cheaper than C13 at sec_20 = 128 (C7 was 127 K before those changes).

Reading the table:

- **vs C7**: C13 holds full 128-bit security up to its 2²² cap (vs C7's 2²⁴) and signs roughly half the hashes. It used to verify ~17 % cheaper (105 K vs 127 K); with C7 now at 96 K and C13 still unoptimised (¶), C13 currently costs ~9 % more. Trade-off: half the signature-count budget per key. Good fit when keys rotate often or the per-key budget is bounded by policy.
- **vs C11**: Same security at sec_14 (128 bit), but C11 collapses to 86 bit at sec_20. C13 holds 128 bit all the way to sec_20. Cost: ~30× higher signer hash count (C13's a=19 FORS trees vs C11's a=11), and for now ~18 K more verify gas (105 K vs 87 K, ¶).
- **vs C12** (plain SPHINCS+ without counter grinding): C13 verifies ~1.9× cheaper (105 K vs 204 K verifier-only) for a comparable security envelope, with a sig that's ~44 % smaller. C12 wins decisively on signer cost (it has no counter-grinding step at all), so C12 stays the right pick for tightly-constrained signers (e.g. secure-element keys). C13 is the right pick when verify gas matters more than signer time.
- **vs SLH-DSA-SHA2-128-24** (NIST-compliant standalone): C13 is roughly **same sig size** (-4 %) and **~25 % cheaper to verify**, with ~100× lower signer cost. The trade is that SLH-DSA is the FIPS 205 NIST-blessed parameter set; C13 is a research parameter choice in the ePrint 2025/2203 family. C13's ADRS layout now matches FIPS to keep cross-impl porting clean.
- **Smallest signature** of any variant in the repo. The combination `k=7, a=19` with the 4 B count tail and 11-level subtree gives the leanest payload.

The takeaway: **C13 has the smallest signature in the repo at 128-bit security up to a 2²² sig cap**, and it was the cheapest verifier at that security level until C7 got the loop optimisations that C13's proof-pinned verifier does not have yet (¶). The cost is sign-time, which is ~30× C11 and ~2× C7. For an Ethereum smart account that signs occasionally and is verified by everyone, that asymmetry is the right shape.

C11 and C12 are light enough to run on a hardware wallet, 390s and 47.5s signature times on a ST33K1M5 secure element (Ledger nano S+). C12 has the lowest hardware signer cost of all (~37 K hashes - plain SPX with d=5 hypertree skips most tree-hash work) at the price of a 6,592-byte sig. SLH-DSA-SHA2-128-24 is the FIPS-aligned alternative: much larger signer cost even on a desktop-class signer that caches the XMSS tree (~200 M hashes / sig, dominated by FORS, which can't be cached because the leaf-index to FORS-tree-address mapping changes with every message), and ~1.07 B / sig on a zero-memory signer that has to rebuild the 2²²-leaf XMSS for every auth path. 128-bit security across the 2²⁴ usage window is carried by the FORS few-time layer absorbing the expected pseudorandom WOTS-leaf reuse over the 2²² leaf space (‡/§ above; [docs/SECURITY-ANALYSIS.md](docs/SECURITY-ANALYSIS.md)), not by one-time WOTS use. The SHA-2 verifier implements **FIPS 205 *external* SLH-DSA.Verify with an empty context** (M wrapped as `0x00‖0x00‖M` before H_msg), so it matches published NIST/ACVP external KAT vectors. The Keccak twin trades bit-exact NIST compliance for ~34 % cheaper on-chain verification (but not a very interesting trade-off as it keeps the same signer cost).

## leanSphincs-23 (keccak256)

`src/keccak/LeanSphincs-23Asm.sol` verifies **leanSphincs-23**, the retuned set from the [sphincs-art](https://nconsigny.github.io/sphincs-art/) fork of Tom Wambsgans' leanSphincs ([note](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/releases/download/doc-latest/leanSPHINCS.pdf), [code](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/tree/main/crates/sphincs)), with **keccak256 in place of BLAKE2s**. That is the only change: tweaks, byte order, field splits and serialization are the upstream crate's, re-parameterized. The one thing upstream does not fix for these parameters, the message-digest field layout for `a = 12`, is pinned by the spec: [docs/leanSphincs-23-keccak.md](docs/leanSphincs-23-keccak.md).

It is one XMSS tree (`h = 25`, `d = 1`) over FORS (`k = 13`, `a = 12`; no tree roots, the two top nodes of each tree feed the FORS key) and WOTS+C (64 chains of 4 positions, target sum `T = 128`), with `n = 16`. leanSphincs is not a SPHINCS+ ADRS scheme: it keeps its own 16-byte tweak (`LE32(lo) ‖ LE24(hi) ‖ t|step<<5 ‖ 0^8`), so `P ‖ tweak` is exactly one EVM word. Verification is a constant **249 keccak256 calls**. The interface is the C-series `verify(pkSeed, pkRoot, message, sig)` (keys high-aligned: `P ‖ 0^16`, `root ‖ 0^16`), so `SphincsAccount` takes it unchanged.

| | **leanSphincs-23 (keccak)** | C13 | SLH-DSA-SHA2-128-24 |
|---|---|---|---|
| h / d | 25 / 1 | 22 / 2 | 22 / 1 |
| Few-time layer | FORS, k=13, a=12 | FORS+C, k=7, a=19 | FORS, k=6, a=24 |
| One-time layer | WOTS+C, w=4, 64 chains, T=128 | WOTS+C, w=8, 43 chains | WOTS+, w=4, 68 chains |
| Sig | 4,148 B | 3,688 B | 3,856 B |
| Verify gas | **~39 K** | 105 K | ~142 K |
| Lifetime | 2²³ full key / 2²¹ standard / 20 K light | 2²² cap | 2²⁴ usage cap |

- **Verify gas** for leanSphincs-23 is the `verify` call frame (`vm.lastCallGas`, the same as Forge's trace): 38,879–39,002 over the six KAT vectors, 38,845 for a fresh Rust signature. The keccak count is fixed, but the gas depends on the WOTS chain step counts and on nothing else: typical signatures differ by a few hundred, and any admissible signature lies in 38,366–39,395. The tests gate the frame figure at 39,600, on the KATs and on random-digest signatures. A `gasleft()` delta around the external call is 40.3–40.5 K: it adds the call's account access and the caller's ABI encoding of the 4,148-byte argument, so it depends on the caller (and is 2.5 K higher again under `forge test --isolate`, where the verifier is cold on every call). `SphincsAccount.validateUserOp` (ECDSA + leanSphincs-23) is 53.9–54.0 K. C13 and SLH-DSA are the pure-assembly figures from the Variants table.
- **Lifetime** figures are sphincs-art's one-signer estimates for leanSphincs-23 (not proved in Lean): **8.4 M ≈ 2²³** signatures for a full `2^25` key, **2.1 M ≈ 2²¹** for the "standard" `2^20` subtree, **20 K** for the "light" (Ledger Nano S+) `2^13` subtree.
- **Keygen.** Keys are pruned: the signer builds a subtree of `2^b` leaves, and the tree levels above it are surrogate siblings derived from the seed. The verifier cannot tell a pruned key from a full one, so lifetime is bought with keygen time: `≈ 2^b · 226` keccak calls, i.e. 1.85 M (`b = 13`), 237 M (`b = 20`), 7.6·10⁹ (full key).
- **Signing** costs about 148 K keccak calls plus `2^(25−b)` randomizer tries: 133 K to rebuild the 13 FORS trees of the signed instance, about 14.7 K WOTS+C counter tries, and a ρ grind until the digest's leaf lands in the kept subtree. Measured on the Rust signer: 152.5 K per signature at `b = 13`.

```bash
cd signers/leansphincs23-keccak && cargo build --release && cargo test --release
./target/release/ls23k sign <seed_hex64> <b> <msg_hex64>   # 0x ‖ abi.encode(pkSeed, pkRoot, sig); b = kept subtree height
cd ../.. && python3 signers/leansphincs23-keccak/crosscheck.py --jobs 4   # Rust ↔ Python, byte for byte
forge test --match-contract LeanSphincs23Test -vv   # verifier + SphincsAccount suites (KATs, tampering, spec model, random digests, FFI)
```

The Rust signer (`signers/leansphincs23-keccak`) is a port of the upstream crate. `script/leansphincs23_signer.py` is an independent Python signer written from the spec, and the crosscheck holds the two to byte equality. The Forge KAT fixture `test/fixtures/leansphincs23-keccak-kat.json` is regenerated by `signers/leansphincs23-keccak/make_kat_fixture.py`, and CI job `leansphincs23` runs all of the above.

### Tiered signer

`ls23k keygen` generates a key once for one of the "One signer, leanSphincs-23" tiers of the [sphincs-art page](https://nconsigny.github.io/sphincs-art/) and writes it to a key file with a node cache of bounded size. `ls23k sign-key` then recomputes only the auth-path nodes the cache does not hold. Spec §14; CLI, cache plans and key-file layout in the [crate README](signers/leansphincs23-keccak/README.md).

```bash
./target/release/ls23k keygen --seed-file seed.hex --tier light -o light.key   # or --seed-stdin; --tier standard|full, or --b N --cache-bytes N
./target/release/ls23k sign-key light.key <msg_hex64>                          # the bytes `ls23k sign <seed> 13 <msg>` prints
./target/release/ls23k info light.key                                          # tier, plan, key words, costs; no secret
```

| Tier | `b` / cache (plan) | Keygen: keccak256 calls, time | Sign: keccak256 calls (mean), time | Peak RSS, keygen / sign | Lifetime, page estimate (rated) | Page, BLAKE2s: keygen / sign |
|---|---|---|---|---|---|---|
| Light | 13 / 16 KiB (level 3) | 1.85 M, 0.05 s | 155 K, 13 ms | 2.7–3.0 / 4.5–4.9 MB | 40.2 K (20 K) | 1.98 M, 60 s / 155 K, 4.7 s |
| Standard | 20 / 1 MiB (levels 5..20) | 237 M, 4.7–5.8 s | 155 K, 24 ms | 3.1–3.6 / 5.4–6.2 MB | 2.78 M (2.1 M) | 254 M, 2.0 s / 156 K, 1.2 ms |
| Full | 25 / 16 MiB (levels 6..25) | 7.58 B, 224–229 s | 162 K, 0.2–0.4 s | 30–37 / 47 MB\* | 54.0 M (8.4 M) | 8.12 B, 8.1 s / 163 K, 0.16 ms |

- **Times** are this machine's (Ryzen 9 9955HX3D, 16C/32T, `ls23k` on 32 threads, 33–50 M keccak256 calls/s), measured while other tenants kept the load average at 10–91, so they are upper bounds. Call counts are exact. A signature's time is one `sign-key` run, which also loads and checks the key file (1,048 / 32,778 / 524,288 calls) and verifies the signature (249) before printing it. For Full the load check dominates: with the key loaded once, a signature takes about 19 ms. Keygen is `2^b·226 + 2(25 − b)` calls. The signing means are the reference signer's (the page's model plus 13 calls, 14 for Full); 24 measured signatures per tier averaged 156.1 K / 156.3 K / 161.9 K.
- **Peak RSS** is `VmHWM` (`LS23K_RSS=1`), a lower bound. \*Full's figures were measured before the key-file writer and loader stopped copying the cache. By the crate's heap accounting Full now needs about 16 MiB (keygen) and 19 MB (`sign-key`) plus about 3 MB for the process; that was not re-measured, since no Full keygen was run after the change.
- **Page** figures are sphincs-art's (default "vanilla" view): BLAKE2s compressions, and times at its device rates (Ledger Nano S+ 33 K/s, weak CPU 128 M/s, powerful CPU 1 G/s). They do not transfer to keccak256 on those devices. The lifetime is the page's cover estimate (not proved); each tier is rated at a target the estimate clears by at least 25 %.

Operational rules:

- **One seed, one key.** Never use a seed at two different `b` (two tiers, or `keygen` and `ls23k sign` at another `b`). Same-seed keys share `P` and every one-time key, and where their kept subtrees overlap a signature of one converts into a signature of the other from public data alone. Use a fresh seed for every key.
- **The key file is the secret.** It holds the seed in the clear (mode 0600): back it up like a private key. `keygen` reads the seed only from `--seed-file` (refused if group or others can access it) or `--seed-stdin`, never from the command line.
- **Same signatures, same verifier.** `sign-key` prints exactly what the stateless `ls23k sign <seed> <b> <msg>` prints (Rust tests, the Forge FFI test `testVerifyFFI_RustLightTierKeyFile` and CI check this), so `LeanSphincs-23Asm.sol`, the spec's encoding and the KAT fixture are unchanged. Nothing counts signatures: staying under the rated lifetime is the caller's job.

## Stateless SPHINCs- Architecture

### Shared hash kernel

Live verifiers in `src/` are organized **one folder per hash function**: `src/keccak/`, `src/sha/`, and `src/blake/` (accounts stay in `src/` root). There are **three hash backends** but still **only two ADRS byte layouts**, both straight out of FIPS 205: **FIPS uncompressed 32 B** (keccak *and* BLAKE2b families) and **FIPS ADRSc 22 B** (SHA-2 family) — the BLAKE2b twins reuse the keccak FIPS uncompressed layout verbatim. The keccak C-series all migrated off JARDIN to FIPS uncompressed (C13 first, then C7/C9, then C11/C12); only the keccak SLH-DSA twin stays on JARDIN, **retired to `legacy/`** (along with the JARDIN-layout C11/C12 originals, kept for benchmark reproducibility and the [nconsigny/JARDIN](https://github.com/nconsigny/JARDIN) repo's `JardinSpxVerifier` reference).

`src/sha/` holds the **SHA-256 twins** of C11/C13/C12 plus the NIST SLH-DSA-SHA2. C11-SHA/C13-SHA are *minimal twins* (compact construction kept; not FIPS — one-shot H_msg, MSB-first parsing); C12-SHA is *full FIPS 205 SLH-DSA-SHA2* at C12 params (MGF1 H_msg, empty-context envelope). See [SHA-256 twins](#sha-256-twins-srcsha) below. `src/blake/` holds the **BLAKE2b twins** of C11/C13/C12 — minimal twins of the keccak C-series with only the hash swapped (keccak256 → BLAKE2b), built on the **BLAKE2F compression precompile 0x09** (EIP-152; *not* a hash — each verifier wraps it with a `blake2b()` Yul kernel that does the BLAKE2b construction + LE↔BE bridging). Not FIPS. Verify gas is ~1.2× (C13) to ~1.55× (C11, C12) the keccak originals (~126–314 K; the C11/C12 keccak originals now carry the loop optimisations) — one 0x09 STATICCALL per tweakable hash; the single-block F/H hashes run from fixed, pre-initialised precompile input buffers (only ADRS + payload are written per call, the 16-byte digest lands directly in the next input slot), and the LE IV and counter are pre-swapped constants, so endianness bridging is free at runtime.

| Layout | Variants | ADRS bytes | Hash | F/H/T input |
|---|---|---|---|---|
| **FIPS uncompressed 32 B** (`src/keccak/`) | **C7, C9, C11, C12, C13** (C13 first)          | `layer4 ‖ tree12 ‖ type4 ‖ word1·4 ‖ word2·4 ‖ word3·4` | keccak256 | `seed32 ‖ adrs32 ‖ payload` |
| **FIPS uncompressed 32 B** (`src/blake/`) | C11-BLAKE, C13-BLAKE, C12-BLAKE | `layer4 ‖ tree12 ‖ type4 ‖ word1·4 ‖ word2·4 ‖ word3·4` | BLAKE2b (precompile 0x09, F-only) | `seed32 ‖ adrs32 ‖ payload` |
| **FIPS ADRSc 22 B** (`src/sha/`) | C11-SHA, C13-SHA, C12-SHA, SLH-DSA-SHA2-128-24 | `layer1 ‖ tree8 ‖ type1 ‖ 12 B type-dependent` | SHA-256 (precompile 0x02) | `PK.seed(16) ‖ zeros(48) ‖ ADRSc(22) ‖ payload` |
| _JARDIN 32 B (retired → `legacy/`)_ | SLH-DSA-Keccak-128-24; legacy C11/C12 originals | `layer4 ‖ tree8 ‖ type4 ‖ kp4 ‖ ci4 ‖ cp4 ‖ ha4` | keccak256 | `seed32 ‖ adrs32 ‖ payload` |

leanSphincs-23 (`src/keccak/LeanSphincs-23Asm.sol`) is not in this table: it is not a SPHINCS+ ADRS scheme, and it keeps leanSphincs's own 16-byte tweak with input `P(16) ‖ tweak(16) ‖ payload` (see [leanSphincs-23](#leansphincs-23-keccak256)).

### SHA-256 twins (`src/sha/`)

SHA-256 + 22-byte ADRSc versions of the keccak verifiers, for deployments that prefer the SHA-256 precompile (e.g. cross-impl alignment with the FIPS SHA-2 family) over native keccak. The hash and address change as a coupled unit (SHA-256; FIPS §11.2 ADRSc; MSB-first `base_2b` parsing); they cost more gas than the keccak originals (SHA-256 precompile staticcall vs native opcode).

| Variant | Construction | FIPS? | Sig | Verify gas (verifier-only) |
|---|---|---|---|---|
| **C10-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 4,008 B | ~141 K |
| **C11-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 3,976 B | ~141 K |
| **C13-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 3,688 B | ~131 K |
| **C12-SHA** | plain SPHINCS+, full FIPS 205 SLH-DSA-SHA2 (MGF1 H_msg, `0x00‖0x00` envelope, standard checksum) | Algorithm yes; params not a NIST set (no KAT) | 6,576 B | ~342 K |

The compact twins (C10/C11/C13) **cannot** be made FIPS-compliant — their WOTS+C/FORS+C counter-grinding has no FIPS 205 analog — so they only borrow the SHA-256 hash + ADRSc. C12 is plain SPHINCS+, so it takes the full FIPS algorithm. Vectors: `script/signer.py {c10-sha,c11-sha,c13-sha}` and `script/slh_dsa_sha2_c12_signer.py`.

The Forge e2e tests (`SphincsC1{0,1,3,2}ShaTest`) print ~429 K / ~427 K / ~397 K / ~805 K, because they also copy the cached sig out of storage.

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

**Why C13 moved to FIPS uncompressed.** "Reduce differences between families": FIPS-aligning the ADRS makes the keccak verifier port cleanly from a FIPS reference implementation, and pares the repo's address-layout inventory toward just two layouts (above). The hash stays keccak256; switching to SHA-256 costs more on-chain gas (C13-SHA verifies at ~1.2× C13's verifier-only gas; precompile staticcall vs native opcode) and would only be relevant if we needed full SLH-DSA-SHA2 family alignment, which we don't.

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
    └── FrameAccount (EIP-8141)     ← keys as immutables (code), no SLOAD
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
No ECDSA - pure post-quantum. `src/SphincsFrameAccount.sol` keeps `pkSeed`, `pkRoot` and `verifier` as immutables and forwards them to the `SphincsFrameVerify.yul` module as its DELEGATECALL input. The verify path therefore runs no SLOAD. A frame transaction starts with an empty `accessed_storage_keys`, so storage keys would cost 3 × 2,100 gas of cold SLOADs on every verify. The module refuses to run unless it is delegatecalled. The older ethrex demo runtime (`legacy/script/deploy_frame_account.py`, used by `script/send_frame_tx_c13.py`) still keeps its keys in storage slots 0 and 1.

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
| `signers/signer-wasm/` | Rust/WASM | C-series | **Yes** |
| `script/slh_dsa_sha2_128_24_signer.py` | Python (slow; ~hours at NIST params) | SLH-DSA-SHA2-128-24 | No |
| `script/slh_dsa_keccak_128_24_signer.py` | Python (slow; ~hours at NIST params) | SLH-DSA-Keccak-128-24 | No |
| `signers/sphincsplus-128-24/` | C (forked from sphincs/sphincsplus ref) | SLH-DSA-SHA2-128-24 | No, seeds fed in |
| `signers/jardin-keccak-128-24/` | C (sphincsplus fork + custom keccak + 32-B ADRS) | SLH-DSA-Keccak-128-24 | No |
| `signers/leansphincs23-keccak/` (`ls23k`) | Rust (port of the upstream leanSphincs crate) | leanSphincs-23 (keccak) | No, seed fed in |
| `script/leansphincs23_signer.py` | Python (independent, from the spec; `b ≈ 6..12`) | leanSphincs-23 (keccak) | No |

```bash
# Rust WASM C-series signer
cd signers/signer-wasm && wasm-pack build --release --target web
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

Hardened C13 verifiers (commit 16732a7), new C13 `SphincsAccountFactory` instances and freshly-deployed accounts (each account funded 0.1 ETH):

| Chain | Contract | Address |
|---|---|---|
| Sepolia | C13 verifier (hardened) | [`0xc6f400...`](https://sepolia.etherscan.io/address/0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2) |
| Sepolia | SphincsAccountFactory | [`0x8830d3...`](https://sepolia.etherscan.io/address/0x8830d36284829656F2A60CD028062686069FABA4) |
| Sepolia | SphincsAccountFactory (fresh) | [`0x79FDD0...`](https://sepolia.etherscan.io/address/0x79FDD0aFcb2214D6C17E639dA7eF6357956Cd857) |
| Sepolia | SphincsAccount (ERC-4337 hybrid, C13) | [`0x012801...`](https://sepolia.etherscan.io/address/0x01280171F336869e9c96F9e6eb674b1548D10dD4) |
| ethrex | C13 verifier (hardened) | [`0xAA481E...`](https://explorer.eip-8141.ethrex.xyz/address/0xAA481E835ec1b82E528d6D36D432F9Af440B4295) |
| ethrex | SphincsAccountFactory | [`0x874f5b...`](https://explorer.eip-8141.ethrex.xyz/address/0x874f5ba1d47B477CB70999795cAf7E6Bb53EeDD7) |
| ethrex | Frame account (EIP-8141, C13) | [`0x253A4d...`](https://explorer.eip-8141.ethrex.xyz/address/0x253A4d0100fe7A2a6d6839b37BDC283FD1dF693d) |

> ethrex's `SphincsAccountFactory` is deployed for completeness, but EntryPoint v0.9 has no code on ethrex, so accounts created there are inert for ERC-4337. ethrex's functional PQ path is the EIP-8141 frame account. The full address record is kept locally in the gitignored `script/.c13_addresses.json` (read by `script/send_userop_c13.py` and `script/send_frame_tx_c13.py`).

### Sepolia (ERC-4337 Hybrid, C-series)

| Variant | Verifier | Account | Gas | Tx |
|---|---|---|---|---|
| C9 | [`0x18F005...`](https://sepolia.etherscan.io/address/0x18F005EECd41624644AA364bA8857258FEB3C26D) | [`0xA94111...`](https://sepolia.etherscan.io/address/0xA941116763AE386a50133c5af40356c9D93b2978) | 300 K | [`0x8366513b...`](https://sepolia.etherscan.io/tx/0x8366513b096ee53dd1cb105363ab21a52267dd966b822b4bb2cf5492abf1550f) |
| C11 | [`0xC25ef5...`](https://sepolia.etherscan.io/address/0xC25ef566884DC36649c3618EEDF66d715427Fd74) | [`0x3C3b0c...`](https://sepolia.etherscan.io/address/0x3C3b0c3498E5ed9350F6fBFA0Ef8dC55f524eA50) | 308 K | [`0x9fba169c...`](https://sepolia.etherscan.io/tx/0x9fba169ca76b6712586e44e1a4a2d0407b8b8b9ce767272a193e41a756260b74) |
| **C13** | [`0xce176d...`](https://sepolia.etherscan.io/address/0xce176df2680f6612a61486f74502db62d014d23d) | [`0xcef985...`](https://sepolia.etherscan.io/address/0xcef985d4db485e96ab9187ad462561bff241db0d) (factory [`0xcaf5d2...`](https://sepolia.etherscan.io/address/0xcaf5d2582eb405e3c4b65f3a52d147badfd96fed)) | 293 K | [`0xbbf06456...`](https://sepolia.etherscan.io/tx/0xbbf06456145a4daea1b5006f1f5d7b214c62c1c2877eabb61ae4b26e453189d0) |

> **C13 on Sepolia uses the FIPS 205 §4.2 uncompressed 32-byte ADRS** (keccak256 hash). First verifier in the repo on the FIPS address layout. Standalone verify tx-level gas: **188,278**. Full hybrid-4337 `handleOps` UserOp gas: **292,727** (ECDSA recovery + C13 verify + 0.00001 ETH self-transfer through `SphincsAccount.execute`). The verifier, factory, account and tx in this row predate the 2026-06-04 hardening redeploy; the current verifier is in the table above, and the canonical address record is the gitignored local `script/.c13_addresses.json`.

### Sepolia (SLH-DSA-128-24 standalone verifiers, no account wired yet)

| Variant | Verifier | Deploy tx | Sample verify tx | Verify-tx gas |
|---|---|---|---|---|
| SLH-DSA-SHA2-128-24 | [`0x9Fe417...`](https://sepolia.etherscan.io/address/0x9Fe41769395BC9fefb7e0d340064ed29F4a4Af91) | [`0x09be3c59...`](https://sepolia.etherscan.io/tx/0x09be3c5984ed99a93f9c43881822d9937e1efa9b31aee0630f59fca814d90e15) | [`0x00fa6b37...`](https://sepolia.etherscan.io/tx/0x00fa6b37347e2bedf37429a74563b2c68502becdffe3257ebde90f63e165030a) | **225,642** |
| SLH-DSA-Keccak-128-24 | [`0x2Ac9Ec...`](https://sepolia.etherscan.io/address/0x2Ac9Ec4a2A062aFc1be718e77ec3300D087E6205) | [`0x253aa6dc...`](https://sepolia.etherscan.io/tx/0x253aa6dc5c93a201abc7a5cfb4ce27cdeafb35e34fc69c23ef1daae0535c4c4a) | [`0x90d785a1...`](https://sepolia.etherscan.io/tx/0x90d785a112fd0198b4506caf432632777aef43b00ceb648e864dcb119311fed4) | **177,910** |

Verify-tx gas is the full top-level tx cost including 21 K tx base + ~63 K for the 3,872-B calldata payload; pure assembly execution is ~142 K (SHA-2) / ~94 K (Keccak). Keccak wins by ~21 % tx-level and ~34 % assembly-level because every F / H / T is a single native `keccak256` opcode, while the SHA-2 variant pays a `staticcall(0x02)` dispatch per hash × ~280 hashes.

### ethrex Testnet (EIP-8141 Frame Tx - Pure PQ)

> **Defunct (checked 2026-10-18).** The `*.eip-8141.ethrex.xyz` names no longer resolve, and chain
> id 3151908 now belongs to ethrex's Hegotá devnet (`*.hegota.ethrex.xyz`, genesis 2026-08-06),
> where none of the addresses below (or the ethrex rows of the 2026-06-04 table) exist. They are
> kept as a record of the June demo. Before a new frame-account deploy, see
> [docs/SECURITY-REVIEW-2026-10.md §10](docs/SECURITY-REVIEW-2026-10.md): the witness-copy opcode
> differs between the current EIP-8141 text (SIGDATACOPY `0xb5`) and the Hegotá devnet (`0xba`).

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
cd signers/signer-wasm && cargo build --release
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
(cd signers/leansphincs23-keccak && cargo test --release)
cd signers/signer-wasm && cargo test --release -- --ignored
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
