# leanSphincs-f over keccak256

leanSphincs-f is a re-parameterization of [leanSphincs-S](leanSphincs-S-keccak.md) chosen for faster signing:
smaller FORS trees and a WOTS+C target sum closer to the mean, paid for with a larger signature and more
verification work, within a 290-permutation verification budget. It keeps leanSphincs-S's full-key and Ledger
lifetime floors (≥ 100M and ≥ 20K signatures, sphincs-art estimates). The on-chain verifier is
`src/keccak/LeanSphincs-FAsm.sol`.

**Everything is leanSphincs-S** (`docs/leanSphincs-S-keccak.md`: the upstream crate's `keccak` branch construction,
Ethereum Keccak-256, the 16-byte tweak, no FORS key hash, the merged WOTS+C encoding, `h = 26`, keys, pruning,
randomizer grind, serialization order, interface, tiers) **except the items below.** Section numbers refer to that
spec.

## Differences from leanSphincs-S

| Spec § | leanSphincs-S | **leanSphincs-f** |
|---|---|---|
| §1 FORS `a` / `k` | 12 / 13 | **9 / 20** |
| §1 WOTS+C target sum `T` | 128 | **122** (`P[Σx = 122] ≈ 6.38·10⁻⁴`, about 1,566 tries) |
| §1 signature | 4,164 B | **4,660 B** = `16 + 20·10·16 + 4 + 64·16 + 26·16` |
| §1 digest bits | 182 | **206** = `26 + 20·9` (one keccak256 call) |
| §1 verification | 249 calls / 259 permutations | **279 calls / 290 permutations** (below) |
| §4 FORS position | `κ < 13`, `ℓ < 12`, `j < 2^12` | `κ < 20`, `ℓ < 9`, `j < 2^9`; `pos = κ + 32ℓ + 512j < 2^18` |
| §5 FORS indices | 5 per 64-bit word | **7 per word**: `u_κ = (word_{⌊κ/7⌋} >> (9·(κ mod 7))) & 0x1FF`; words 0 and 1 hold κ = 0..13, word 2 holds κ = 14..19 (bits 0–53) |
| §5 leaf index | `word_3 & (2^26 − 1)` | unchanged |
| §6 encoding input | `tops` = 26 × 16 = 416 B; 452-byte input | `tops` = 40 × 16 = **640 B**; **676-byte** input `P ‖ address ‖ tops ‖ LE32(c)` |
| §7 FORS levels | ℓ = 1..11, tops at level 11 | ℓ = 1..8, tops at level 8 (bit 8 of `u` orders the pair) |
| §11 signature offsets | — | ρ 0; FORS secret `16 + 160κ`; FORS path `32 + 160κ + 16ℓ` (ℓ = 0..8); counter **3216**; WOTS `σ_i` **3220 + 16i**; auth path **4244 + 16ℓ** (ℓ = 0..25) |
| §12 length check | `sig.length != 4164` | `sig.length != 4660` |
| §13 CLI | `lssk` | **`lsfk`** (`signers/leansphincs-f-keccak`); Python `script/leansphincs_s_signer.py --variant f` |
| §14 key file | magic `LS-SKKEY` | magic **`LS-FKKEY`**, same layout: `lsfk` refuses an `lssk` (`LS-SKKEY`), `lsk` (`LS-KKKEY`) or `ls23k` (`LS23KKEY`) key file before reading anything else, and those signers refuse this one |

Verification work, constant for every signature that passes the WOTS+C admissibility check: 1 digest + 20·(1 leaf +
8 nodes) + 1 encoding + 70 chain steps (`192 − 122`) + 1 WOTS leaf + 26 path nodes = **279 keccak256 calls**, or
**290 Keccak-f permutations** (the 676-byte encoding input costs 5, the 1,056-byte WOTS leaf 8, every other call 1).
An inadmissible counter returns `false` after the first 182 calls (digest, FORS, encoding).

Signing: the encoding's fixed part `P ‖ address ‖ tops` is 672 bytes, four whole 136-byte blocks absorbed once per
signature; the counter falls in the fifth block, one permutation per counter tried. FORS rebuilds 20 trees of 512
leaves per signature (25,560 permutations, against 133,094 for leanSphincs-S).

## Lifetimes and tiers

The tiers are leanSphincs-S's (Light 2^13 / 16 KiB, Standard 2^20 / 1 MiB, Full 2^26 / 16 MiB). Lifetimes are the
sphincs-art method (the cover estimate, lowered by the proposal's proof gap at the same subtree size: 13% / 6% / 4%),
estimates, not proofs: **31.5K** (Light, rated 20K), **2.78M** (Standard, rated 2²¹), **119M** (Full, rated 2²⁶).
Expected signing work, in Keccak-f permutations: 38.4K (Light), 34.8K (Standard), 57.1K (Full).

## Measured

Verifier (Forge; forge 1.5.1, solc 0.8.33, via-ir): 43,977–44,133 gas in its own call frame over the KAT fixture, and
43,479–44,546 for any admissible signature (the gas depends only on the WOTS step counts), gated at 44,746 by
`test/LeanSphincsFTest.t.sol`. Through `SphincsAccount` (ECDSA + leanSphincs-f), `validateUserOp` is about 51.6K.

Reference signer `lsfk`, 8 cores of a shared host: a Light keygen (1,851,418 calls) takes 0.06 s and a Standard one
(236,978,188 calls, a 1 MiB key file) 8.1 s. `sign-key` took 2.8–12.5 ms over 25 Light signatures (mean 37,375
permutations) and 12.8–15.3 ms over 12 Standard ones (mean 35,332), loading the key file and verifying the signature
included, with a VmHWM of 3.1–3.6 MB. These are host times; the device times are the page's rates applied to the
model's counts.

## Key separation

leanSphincs, leanSphincs-S and leanSphincs-f derive `P`, the WOTS and FORS secrets and the surrogates identically
from the seed, and nothing in a hash input names the parameter set. One seed is one key of one variant: never reuse
a seed across variants or tiers. The key files cannot be confused (each variant's has its own magic, the §14 row),
but the seed is the same 32 bytes, and no signer can detect the reuse.
