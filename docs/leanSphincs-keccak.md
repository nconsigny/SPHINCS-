# leanSphincs over keccak256

leanSphincs is Tom Wambsgans' proposal ([sphincs.art](https://sphincs.art),
[note](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/releases/download/doc-latest/leanSPHINCS.pdf)) in
its Keccak-256 form: **the upstream crate's `keccak` branch** (`crates/sphincs`, MIT OR Apache-2.0) at its own
parameters, with nothing re-parameterized. The on-chain verifier is `src/keccak/LeanSphincsAsm.sol`. Its lifetime is
**2³⁰ signatures, proved in Lean** by the proposal (`formal/sphincs`); the sphincs-art one-signer tiers are 210K
(Light), 22M (Standard) and 1.15B (Full).

Every construction rule is the one [leanSphincs-s](leanSphincs-S-keccak.md) takes from that branch (Ethereum
Keccak-256, the 16-byte tweak, no FORS key hash, the merged WOTS+C encoding, `h = 26`, keys, pruning, randomizer
grind, serialization order, interface, tiers). The upstream crate is normative here: where this document and the
crate disagree, the crate wins. Section numbers refer to the leanSphincs-s spec.

## Differences from leanSphincs-s

| Spec § | leanSphincs-s | **leanSphincs** |
|---|---|---|
| §1 FORS `a` / `k` | 12 / 13 | **10 / 24** |
| §1 WOTS+C target sum `T` | 128 | **120** (`P[Σx = 120] ≈ 1.21·10⁻³`, about 829 tries) |
| §1 signature | 4,164 B | **5,684 B** = `16 + 24·11·16 + 4 + 64·16 + 26·16` |
| §1 digest bits | 182 (one call) | **266** = `26 + 24·10`: **two calls** (below) |
| §1 verification | 249 calls / 259 permutations | **342 calls / 354 permutations** (below) |
| §4 FORS position | `κ < 13`, `ℓ < 12`, `j < 2^12` | `κ < 24`, `ℓ < 10`, `j < 2^10` (upstream) |
| §5 message digest | one call, `hi = 0` | **upstream's two calls** (below) |
| §6 encoding input | `tops` = 416 B; 452-byte input | `tops` = 48 × 16 = **768 B**; **804-byte** input `P ‖ address ‖ tops ‖ LE32(c)` |
| §7 FORS levels | ℓ = 1..11, tops at level 11 | ℓ = 1..9, tops at level 9 (bit 9 of `u` orders the pair) |
| §11 signature offsets | — | ρ 0; FORS secret `16 + 176κ`; FORS path `32 + 176κ + 16ℓ` (ℓ = 0..9); counter **4240**; WOTS `σ_i` **4244 + 16i**; auth path **5268 + 16ℓ** (ℓ = 0..25) |
| §12 length check | `sig.length != 4164` | `sig.length != 5684` |
| §13 CLI | `lssk` | **`lsk`** (`signers/leansphincs-keccak`); Python `script/leansphincs_s_signer.py --variant regular` |
| §14 key file | magic `LS-SKKEY` | magic **`LS-KKKEY`**, same layout: `lsk` refuses an `lssk` (`LS-SKKEY`), `lsfk` (`LS-FKKEY`) or `ls23k` (`LS23KKEY`) key file before reading anything else, and those signers refuse this one |

## Message digest (upstream, two calls)

```
D_c = ThFull(P, address(MSG, step 0, hi = c, lo = 0), m ‖ ρ)       c = 0, 1;  80 input bytes each
word_{c,w} = u64 little endian of D_c[8w : 8w+8]
```

- Leaf index: `idx = word_{0,2} & (2^26 − 1)` (call 0, bytes 16..24).
- FORS index κ (0 ≤ κ < 24): call `c = ⌊κ/12⌋`, `r = κ mod 12`:
  `u_κ = (word_{c, ⌊r/6⌋} >> (10·(r mod 6))) & 0x3FF`. Six indices per 64-bit word, words 0 and 1 of each call;
  no field crosses a word.
- The randomizer grind needs only call 0 (the leaf index).

## Verification work

2 digest calls + 24·(1 leaf + 9 nodes) + 1 encoding + 72 chain steps (`192 − 120`) + 1 WOTS leaf + 26 path nodes =
**342 keccak256 calls**, or **354 Keccak-f permutations** (the 804-byte encoding input costs 6, the 1,056-byte WOTS
leaf 8, every other call 1) — the sphincs.art figure. An inadmissible counter returns `false` after the first 243 calls
(digests, FORS, encoding).

## Known answer

Upstream's `known_answer` test pins `key_gen(seed(1), 11)` with `seed(x)[i] = x·31 + i mod 256` and `m[i] = 7i mod 256`:
public key `63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00` (root ‖ P),
`keccak256(sig) = 9a21b6bc61d6ba500b4d67809912c1424be1f58486eda144e4ef70afd01cf94d`, counter **1176**. Both signers
must reproduce it.

## Tiers and measurements

The tiers are leanSphincs-s's (Light 2^13 / 16 KiB, Standard 2^20 / 1 MiB, Full 2^26 / 16 MiB), with the proposal's
proved lifetimes (210K, 22M, 1.15B). Expected signing work, in Keccak-f permutations, is sphincs.art's "Tom FORS"
figures (`scripts/keccak_model.py`, reproduced by `signers/leansphincs-keccak/tier_model.py`): 73.5K (Light), 69.9K
(Standard), 92.2K (Full), or 13 s, 0.55 ms and 0.18 ms at the page's device rates; keygen is 1.91M / 244M / 15.6B.

Verifier (Forge; forge 1.5.1, solc 0.8.33, via-ir): 52,837–52,983 gas in its own call frame over the KAT fixture, and
52,246–53,342 for any admissible signature (the gas depends only on the WOTS step counts), gated at 53,542 by
`test/LeanSphincsTest.t.sol`. Through `SphincsAccount` (ECDSA + leanSphincs), `validateUserOp` is about 60.8K.

Reference signer `lsk`, 8 cores of a shared host: a Light keygen (1,851,418 calls) takes 0.06 s and a Standard one
(236,978,188 calls, a 1 MiB key file) 8.2 s. `sign-key` took 3.9–9.0 ms over 25 Light signatures (mean 71,750
permutations) and 13.7–15.2 ms over 12 Standard ones (mean 70,067), loading the key file and verifying the signature
included, with a VmHWM of 3.6–4.1 MB. These are host times, not device times.

## Key separation

leanSphincs, leanSphincs-s and leanSphincs-f derive `P`, the WOTS and FORS secrets and the surrogates identically
from the seed. One seed is one key of one variant: never reuse a seed across variants or tiers. The key files cannot
be confused (each variant's has its own magic, the §14 row), but the seed is the same 32 bytes, and no signer can
detect the reuse.
