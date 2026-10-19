# Variant details

The full variant table, comparisons and layout notes that used to live in the README (moved here unchanged when the README was shortened; figures are as of October 2026). The README presents C7, C12, C13, SLH-DSA-Keccak-128-24 and leanSphincs-S.

## All variants

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
- **sign_h**: hash-function calls during keygen + one signature, zero-memory signer (no inter-sign caching, the relevant case for a hardware wallet). A high number means a lot of work for the hardware. C12, the lightest, takes 47.5 s with our current Ledger Nano S+ signer, and about 6.4 s at 5.8K Keccak-f permutations per second, the [sphincs.art](https://sphincs.art) figure for the Ledger Nano S+. 
- **swn**: small-Winternitz-number counter bits used by the WOTS+C / FORS+C grinding. Plain SPX and SLH-DSA don't counter-grind.
- **sec_N**: security bits at 2^N signatures per key. For SLH-DSA-*-128-24 (h=22, d=1) the hypertree is a **single XMSS tree of only 2²² WOTS leaves**, and the signing leaf is chosen *pseudorandomly* from the message digest, so WOTS-leaf collisions appear by the birthday bound (onset ~2¹¹ signatures), well before the named 2²⁴ usage cap. This is expected and **absorbed by the FORS few-time layer** (it is not a WOTS forgery); 128-bit security is carried with the FORS margin, *not* by one-time WOTS use. The "2²⁴" figure is therefore a recommended per-key **usage cap**, not a flat one-time-security guarantee. See [docs/SECURITY-ANALYSIS.md](SECURITY-ANALYSIS.md) for the budget/collision accounting. (review SLH-X-f2cap)
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
> **C12 key rotation (2026-10, B-01 in [docs/SECURITY-REVIEW-2026-10.md](SECURITY-REVIEW-2026-10.md)):**
> the C12 keccak / BLAKE signer used to derive FORS secrets without the
> hypertree position, so about 1,000 signatures from one key allow a forgery
> on any message that the verifiers accept. The signer is fixed; any C12 key
> that signed with the old signer must be retired, not reused.

### C13 vs the rest of the family: what changes

C13's parameter choice (`h=22 d=2 a=19 k=7 w=8`) was built around three goals: smallest signature, cheapest verify at full 128-bit security across the signature-count window, FIPS-aligned address layout. The numbers above bear out the design:

| Property                       | C7      | C11     | **C13** | C12     | SLH-DSA-SHA2-128-24 | SLH-DSA-Keccak-128-24 |
|--------------------------------|---------|---------|---------|---------|---------------------|-----------------------|
| Sig size                       | 3,704 B | 3,976 B | **3,688 B** ← smallest | 6,592 B | 3,856 B | 3,856 B |
| Pure-asm verify                | 96 K    | 87 K    | **105 K** ♦ | 204 K | 142 K | 94 K |
| Frame tx total (ethrex)        | 210 K   | 202 K   | **188 K** | n/a | n/a | n/a |
| 4337 handleOps total (Sepolia) | 318 K   | 308 K   | **293 K** | n/a | n/a | n/a |
| Signature-count cap            | 2²⁴     | 2¹⁶     | 2²²     | 2²⁰ (h=20, d=5) | 2²⁴ ‡ | 2²⁴ ‡ |
| Security at the cap            | 128 bit | 86 bit  | **128 bit** | 95 bit | 128 bit § | 128 bit § |
| Hash-call cost / sign (cold)   | 4.3 M   | 292 K   | ~10 M   | ~37.3 K | ~1.07 B | ~1.07 B |
| Ledger Nano S+ sign, est. ¶    | 12 min  | 50 s    | 29 min  | 6.4 s   | n/a (SHA-256) | ~51 h |
| ADRS layout                    | **FIPS uncompressed** | **FIPS uncompressed** | **FIPS uncompressed** | **FIPS uncompressed** | FIPS ADRSc | JARDIN |

‡ **SLH-DSA-*-128-24 cap is a usage cap, not a leaf budget.** h=22, d=1 ⇒ a single XMSS tree of 2²² WOTS leaves; the leaf is chosen pseudorandomly per message, so by 2²⁴ signatures leaves have been reused ~4× on average (and birthday collisions begin ~2¹¹). Unlike C7/C13, whose 2²⁴/2²² figures are the actual hypertree-leaf counts at full one-time-WOTS security, the SLH "2²⁴" exceeds its 2²² leaf space by design.

¶ **Estimated at 5.8K Keccak-f permutations per second**, the figure [sphincs.art](https://sphincs.art) uses for the Ledger Nano S+, counting one permutation per hash call (multi-block compressions add about 1%). Ledger's own SPHINCS+-128s benchmark (2.0M hashes in 6 min 18 s, 5.3K/s) agrees. Our current signer is about 7x slower (see below).

§ **128 bit at the cap is carried by FORS, not by WOTS one-time-ness.** Pseudorandom leaf reuse is expected and absorbed by the FORS few-time layer (a=24, k=6); a leaf collision is not itself a forgery. See [docs/SECURITY-ANALYSIS.md](SECURITY-ANALYSIS.md). (review SLH-X-f2cap)

♦ **C13 has not had the loop optimisations yet.** Its verifier is pinned by the Lean model in `verity/`, so it does not carry the in-place T buffers, incremental auth-path climbs, ADRS-as-counter WOTS chains and SWAR checksum that took C7 / C9 / C10 / C11 / C12 down ~22–24 %. Until it does, C7 verifies cheaper than C13 at sec_20 = 128 (C7 was 127 K before those changes).

Reading the table:

- **vs C7**: C13 holds full 128-bit security up to its 2²² cap (vs C7's 2²⁴) and signs roughly half the hashes. It used to verify ~17 % cheaper (105 K vs 127 K); with C7 now at 96 K and C13 still unoptimised (♦), C13 currently costs ~9 % more. Trade-off: half the signature-count budget per key. Good fit when keys rotate often or the per-key budget is bounded by policy.
- **vs C11**: Same security at sec_14 (128 bit), but C11 collapses to 86 bit at sec_20. C13 holds 128 bit all the way to sec_20. Cost: ~30× higher signer hash count (C13's a=19 FORS trees vs C11's a=11), and for now ~18 K more verify gas (105 K vs 87 K, ¶).
- **vs C12** (plain SPHINCS+ without counter grinding): C13 verifies ~1.9× cheaper (105 K vs 204 K verifier-only) for a comparable security envelope, with a sig that's ~44 % smaller. C12 wins decisively on signer cost (it has no counter-grinding step at all), so C12 stays the right pick for tightly-constrained signers (e.g. secure-element keys). C13 is the right pick when verify gas matters more than signer time.
- **vs SLH-DSA-SHA2-128-24** (NIST-compliant standalone): C13 is roughly **same sig size** (-4 %) and **~25 % cheaper to verify**, with ~100× lower signer cost. The trade is that SLH-DSA is the FIPS 205 NIST-blessed parameter set; C13 is a research parameter choice in the ePrint 2025/2203 family. C13's ADRS layout now matches FIPS to keep cross-impl porting clean.
- **Smallest signature** of any variant in the repo. The combination `k=7, a=19` with the 4 B count tail and 11-level subtree gives the leanest payload.

The takeaway: **C13 has the smallest signature in the repo at 128-bit security up to a 2²² sig cap**, and it was the cheapest verifier at that security level until C7 got the loop optimisations that C13's proof-pinned verifier does not have yet (♦). The cost is sign-time, which is ~30× C11 and ~2× C7. For an Ethereum smart account that signs occasionally and is verified by everyone, that asymmetry is the right shape.

C11 and C12 are light enough to run on a hardware wallet. Our current signer measures 390 s and 47.5 s on the ST33K1M5 secure element (Ledger Nano S+), about 750 Keccak calls per second; at the 5.8K permutations per second assumed by sphincs.art (¶) they would take about 50 s and 6.4 s. C12 has the lowest hardware signer cost of all (~37 K hashes - plain SPX with d=5 hypertree skips most tree-hash work) at the price of a 6,592-byte sig. SLH-DSA-SHA2-128-24 is the FIPS-aligned alternative: much larger signer cost even on a desktop-class signer that caches the XMSS tree (~200 M hashes / sig, dominated by FORS, which can't be cached because the leaf-index to FORS-tree-address mapping changes with every message), and ~1.07 B / sig on a zero-memory signer that has to rebuild the 2²²-leaf XMSS for every auth path. 128-bit security across the 2²⁴ usage window is carried by the FORS few-time layer absorbing the expected pseudorandom WOTS-leaf reuse over the 2²² leaf space (‡/§ above; [docs/SECURITY-ANALYSIS.md](SECURITY-ANALYSIS.md)), not by one-time WOTS use. The SHA-2 verifier implements **FIPS 205 *external* SLH-DSA.Verify with an empty context** (M wrapped as `0x00‖0x00‖M` before H_msg), so it matches published NIST/ACVP external KAT vectors. The Keccak twin trades bit-exact NIST compliance for ~34 % cheaper on-chain verification (but not a very interesting trade-off as it keeps the same signer cost).

## Hash backends and address layouts

Live verifiers in `src/` are organized **one folder per hash function**: `src/keccak/`, `src/sha/`, and `src/blake/` (accounts stay in `src/` root). There are **three hash backends** but still **only two ADRS byte layouts**, both straight out of FIPS 205: **FIPS uncompressed 32 B** (keccak *and* BLAKE2b families) and **FIPS ADRSc 22 B** (SHA-2 family) — the BLAKE2b twins reuse the keccak FIPS uncompressed layout verbatim. The keccak C-series all migrated off JARDIN to FIPS uncompressed (C13 first, then C7/C9, then C11/C12); only the keccak SLH-DSA twin stays on JARDIN, **retired to `legacy/`** (along with the JARDIN-layout C11/C12 originals, kept for benchmark reproducibility and the [nconsigny/JARDIN](https://github.com/nconsigny/JARDIN) repo's `JardinSpxVerifier` reference).

`src/sha/` holds the **SHA-256 twins** of C11/C13/C12 plus the NIST SLH-DSA-SHA2. C11-SHA/C13-SHA are *minimal twins* (compact construction kept; not FIPS — one-shot H_msg, MSB-first parsing); C12-SHA is *full FIPS 205 SLH-DSA-SHA2* at C12 params (MGF1 H_msg, empty-context envelope). See [SHA-256 twins](#sha-256-twins-srcsha) below. `src/blake/` holds the **BLAKE2b twins** of C11/C13/C12 — minimal twins of the keccak C-series with only the hash swapped (keccak256 → BLAKE2b), built on the **BLAKE2F compression precompile 0x09** (EIP-152; *not* a hash — each verifier wraps it with a `blake2b()` Yul kernel that does the BLAKE2b construction + LE↔BE bridging). Not FIPS. Verify gas is ~1.2× (C13) to ~1.55× (C11, C12) the keccak originals (~126–314 K; the C11/C12 keccak originals now carry the loop optimisations) — one 0x09 STATICCALL per tweakable hash; the single-block F/H hashes run from fixed, pre-initialised precompile input buffers (only ADRS + payload are written per call, the 16-byte digest lands directly in the next input slot), and the LE IV and counter are pre-swapped constants, so endianness bridging is free at runtime.

| Layout | Variants | ADRS bytes | Hash | F/H/T input |
|---|---|---|---|---|
| **FIPS uncompressed 32 B** (`src/keccak/`) | **C7, C9, C11, C12, C13** (C13 first)          | `layer4 ‖ tree12 ‖ type4 ‖ word1·4 ‖ word2·4 ‖ word3·4` | keccak256 | `seed32 ‖ adrs32 ‖ payload` |
| **FIPS uncompressed 32 B** (`src/blake/`) | C11-BLAKE, C13-BLAKE, C12-BLAKE | `layer4 ‖ tree12 ‖ type4 ‖ word1·4 ‖ word2·4 ‖ word3·4` | BLAKE2b (precompile 0x09, F-only) | `seed32 ‖ adrs32 ‖ payload` |
| **FIPS ADRSc 22 B** (`src/sha/`) | C11-SHA, C13-SHA, C12-SHA, SLH-DSA-SHA2-128-24 | `layer1 ‖ tree8 ‖ type1 ‖ 12 B type-dependent` | SHA-256 (precompile 0x02) | `PK.seed(16) ‖ zeros(48) ‖ ADRSc(22) ‖ payload` |
| _JARDIN 32 B (retired → `legacy/`)_ | SLH-DSA-Keccak-128-24; legacy C11/C12 originals | `layer4 ‖ tree8 ‖ type4 ‖ kp4 ‖ ci4 ‖ cp4 ‖ ha4` | keccak256 | `seed32 ‖ adrs32 ‖ payload` |

leanSphincs-23 and leanSphincs-S (`legacy/src/LeanSphincs-23Asm.sol`, `src/keccak/LeanSphincs-SAsm.sol`) are not in this table: they are not SPHINCS+ ADRS schemes, and they keep leanSphincs's own 16-byte tweak with input `P(16) ‖ tweak(16) ‖ payload` (see [leanSphincs-23](../legacy/docs/leanSphincs-23-keccak.md) and [leanSphincs-S](leanSphincs-S-keccak.md)).

## SHA-256 twins (`src/sha/`)

SHA-256 + 22-byte ADRSc versions of the keccak verifiers, for deployments that prefer the SHA-256 precompile (e.g. cross-impl alignment with the FIPS SHA-2 family) over native keccak. The hash and address change as a coupled unit (SHA-256; FIPS §11.2 ADRSc; MSB-first `base_2b` parsing); they cost more gas than the keccak originals (SHA-256 precompile staticcall vs native opcode).

| Variant | Construction | FIPS? | Sig | Verify gas (verifier-only) |
|---|---|---|---|---|
| **C10-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 4,008 B | ~141 K |
| **C11-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 3,976 B | ~141 K |
| **C13-SHA** | WOTS+C / FORS+C (minimal twin, one-shot H_msg) | No (counter-grinding) | 3,688 B | ~131 K |
| **C12-SHA** | plain SPHINCS+, full FIPS 205 SLH-DSA-SHA2 (MGF1 H_msg, `0x00‖0x00` envelope, standard checksum) | Algorithm yes; params not a NIST set (no KAT) | 6,576 B | ~342 K |

The compact twins (C10/C11/C13) **cannot** be made FIPS-compliant — their WOTS+C/FORS+C counter-grinding has no FIPS 205 analog — so they only borrow the SHA-256 hash + ADRSc. C12 is plain SPHINCS+, so it takes the full FIPS algorithm. Vectors: `script/signer.py {c10-sha,c11-sha,c13-sha}` and `script/slh_dsa_sha2_c12_signer.py`.

The Forge e2e tests (`SphincsC1{0,1,3,2}ShaTest`) print ~429 K / ~427 K / ~397 K / ~805 K, because they also copy the cached sig out of storage.

## Address layout

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
