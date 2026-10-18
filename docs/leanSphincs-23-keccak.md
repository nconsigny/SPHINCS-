# leanSphincs-23 over keccak256

leanSphincs-23 is the retuned leanSphincs set from the
[sphincs-art fork](https://nconsigny.github.io/sphincs-art/) (source:
[nconsigny/sphincs-art](https://github.com/nconsigny/sphincs-art)). leanSphincs itself is Tom Wambsgans'
proposal ([note](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/releases/download/doc-latest/leanSPHINCS.pdf),
[code](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/tree/main/crates/sphincs)). This
document pins the keccak256 instantiation that the on-chain verifier `src/keccak/LeanSphincs-23Asm.sol`
checks.

**The only change from the upstream BLAKE2s construction is the hash function.** Every address, byte order,
field split, and serialization below is the upstream crate's (`crates/sphincs`, MIT OR Apache-2.0), re-parameterized to
leanSphincs-23. The one thing upstream does not fix for these parameters is the message-digest field
layout (upstream's layout is specific to `a = 10`, two calls). §5 defines it for `a = 12`, one call.

leanSphincs is not a SPHINCS+ ADRS scheme. It has its own 16-byte tweak, and that tweak is kept verbatim.
The repo's "keccak verifiers use the FIPS 205 uncompressed ADRS" rule covers the SPHINCs- C-series / SPX
family, not this scheme.

## 1. Parameters

| Symbol | Value | Meaning |
|---|---|---|
| `n` | 16 | hash value / node length (bytes) |
| `P` | 16 B | public parameter |
| `ρ` | 16 B | randomizer |
| `m` | 32 B | message |
| `c` | 4 B | WOTS+C counter, u32 little endian |
| `w` | 2 bits | WOTS chunk; chains of 4 positions (3 steps) |
| `v` | 64 | WOTS chains |
| `T` | 128 | WOTS+C target sum |
| `h` | 25 | XMSS height, one layer (`d = 1`) |
| `a` | 12 | FORS tree height (4096 leaves) |
| `k` | 13 | FORS trees |

- Signature: `16 + k(1+a)·16 + 4 + v·16 + h·16 = 16 + 2704 + 4 + 1024 + 400 = 4148` bytes.
- Public key: `root (16) ‖ P (16)` = 32 bytes.
- Digest bits used: `h + k·a = 25 + 156 = 181` (one keccak256 call).
- WOTS+C success probability per counter: `P[Σx = 128] ≈ 6.82·10⁻⁵`, about 14,670 tries on average.
- Verification work is constant for every signature that passes the WOTS+C admissibility check: 1 digest
  + 13·(1 leaf + 11 nodes) + 1 FORS key + 1 encoding + 64 chain steps (`192 − T`) + 1 WOTS leaf +
  25 path nodes = **249 keccak256 calls**. An inadmissible counter returns `false` after the first
  159 calls (digest, FORS, FORS key, encoding). All inputs are public, so the early exit leaks nothing. The BLAKE2s
  count for the same sequence is 272 compressions, which matches the sphincs-art figure
  (digest 2 + FORS 163 + WOTS+C 82 + path 25).

## 2. Hash

`keccak256` is Ethereum's Keccak-256 (original `0x01` padding), i.e. the EVM `KECCAK256` opcode.
It is not FIPS 202 SHA3-256.

```
Th(P, tw, M)     = keccak256(P ‖ address(tw) ‖ M)[0:16]          // first 16 output bytes
ThPair(P, tw, M) = (keccak256(...)[0:16], keccak256(...)[16:32])  // both halves, signer only
ThFull(P, tw, M) = keccak256(P ‖ address(tw) ‖ M)                 // all 32 bytes, digest only
```

`P ‖ address` is exactly 32 bytes (one EVM word), so every payload starts word-aligned.

On the EVM, "first 16 output bytes" means the **high** 128 bits of the `keccak256` word:
`and(h, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000)`.

## 3. Address (16 bytes)

```
address(t, step, hi, lo) =
    lo   as u32 little endian      bytes 0..4
    hi   low 3 bytes, little endian  bytes 4..7     (hi < 2^24)
    t | (step << 5)                 byte  7        (t < 32, step < 8)
    0x00 × 8                        bytes 8..16
```

Example (upstream test vector): `address(t=10, step=5, hi=0x123456, lo=0x89abcdef)` =
`ef cd ab 89 56 34 12 aa 00 00 00 00 00 00 00 00`.

As the low half of the EVM word `P ‖ address`, with byte 0 the most significant: `lo` occupies word bytes
16–19, `hi` bytes 20–22, `t|step<<5` byte 23, zeros bytes 24–31. So `lo`'s least significant byte is at bit
offset 120 and `hi`'s least significant byte is at bit offset 88.

Tweak types (low five bits of byte 7), as upstream:

| t | name | t | name |
|---|---|---|---|
| 0 | PRF (WOTS secrets) | 8 | FTS_PRF (FORS secrets) |
| 1 | CHAIN | 9 | FTS_LEAF |
| 2 | LEAF (WOTS leaf) | 10 | FTS_NODE |
| 3 | NODE (XMSS node) | 11 | FTS_KEY |
| 4 | ENC (WOTS+C encoding) | 12 | MSG (message digest) |
| 5 | PARAMETER (derives P) | 13 | SURROGATE (pruned-key siblings) |
| 7 | RANDOMIZER | | |

`step` is 0 except on CHAIN calls.

## 4. FORS position

`pos(κ, ℓ, j) = κ + 32·ℓ + 512·j`, with `κ < 13`, level `ℓ < 12`, and `j < 2^(12−ℓ)`. The fields are
disjoint bit ranges (κ in bits 0–4, ℓ in bits 5–8, j in bits 9–20), so `pos < 2^21 < 2^24`. Upstream
asserts `j < 2^10` because it has `a = 10`. Here `j < 2^12`, and the packing stays injective.

## 5. Message digest (leanSphincs-23 layout)

```
D = ThFull(P, address(MSG, step 0, hi = 0, lo = 0), m ‖ ρ)     // 32 + 32 + 16 = 80 input bytes
word_w = u64 little endian of D[8w : 8w+8],   w = 0..3
```

- Leaf index: `idx = word_3 & (2^25 − 1)`.
- FORS index κ (0 ≤ κ < 13): `u_κ = (word_{⌊κ/5⌋} >> (12 · (κ mod 5))) & 0xFFF`.
  Words 0 and 1 hold five indices each (bits 0–59), and word 2 holds κ = 10, 11, 12 (bits 0–35).

This is upstream's rule ("no field lies across two 64-bit words; the leaf index has a word of its own")
applied to `a = 12`: five 12-bit indices fit in a word, so 13 indices take three words, and the fourth
word holds the leaf index. `hi = 0` because there is a single call (upstream's `hi` is the call
number).

## 6. WOTS+C (one-time key at leaf `e`, `lo = e`)

```
secrets:  (s_{2t}, s_{2t+1}) = ThPair(P, address(PRF, 0, hi = t, lo = e), S)           t = 0..31
chain:    stepping chain i onto position `to` ∈ {1,2,3}:
          x ← Th(P, address(CHAIN, step = to − 1, hi = i, lo = e), x)
encode:   d = Th(P, address(ENC, 0, hi = 0, lo = e), M ‖ LE32(c))     // M = 16-byte FORS key
          X = d as u128 little endian;  x_i = (X >> 2i) & 3,  i = 0..63
          admissible iff Σ x_i = 128
leaf:     Th(P, address(LEAF, 0, hi = 0, lo = e), end_0 ‖ … ‖ end_63)    // 1024-byte payload
sign:     least c ∈ [0, 2^32) that is admissible;  σ_i = chain s_i from position 0 to x_i
recover:  end_i = chain σ_i from position x_i to 3;  leaf as above
```

## 7. FORS (instance `idx`, `lo = idx`)

```
secret pair: (sk_{κ,2t}, sk_{κ,2t+1}) = ThPair(P, address(FTS_PRF, 0, pos(κ,0,t), idx), S)
leaf:        L_{κ,j}   = Th(P, address(FTS_LEAF, 0, pos(κ,0,j), idx), sk_{κ,j})
node:        N_{κ,ℓ,j} = Th(P, address(FTS_NODE, 0, pos(κ,ℓ,j), idx), left ‖ right)   ℓ = 1..11
tops:        the two level-11 nodes of each tree (a FORS tree has no root hash)
FORS key:    Th(P, address(FTS_KEY, 0, hi = 0, lo = idx), top_{0,0} ‖ top_{0,1} ‖ … ‖ top_{12,0} ‖ top_{12,1})
```

Recover, per tree κ, with opened leaf `u = u_κ`, secret `sk`, and path `p[0..12]`:

```
node = Th(P, address(FTS_LEAF, 0, pos(κ,0,u), idx), sk)
for ℓ = 0 .. 10:
    (L, R) = bit ℓ of u is 0 ? (node, p[ℓ]) : (p[ℓ], node)
    node   = Th(P, address(FTS_NODE, 0, pos(κ, ℓ+1, u >> (ℓ+1)), idx), L ‖ R)
(top_{κ,0}, top_{κ,1}) = bit 11 of u is 0 ? (node, p[11]) : (p[11], node)
```

## 8. XMSS (one layer, `h = 25`)

```
node(ℓ, j) = Th(P, address(NODE, 0, hi = ℓ, lo = j), left ‖ right)      ℓ = 1..25
fold(idx, leaf, path[0..25]):
    for ℓ = 0 .. 24:
        (L, R) = bit ℓ of idx is 0 ? (cur, path[ℓ]) : (path[ℓ], cur)
        cur    = node(ℓ + 1, idx >> (ℓ + 1))
root = node(25, 0)
```

## 9. Keys (seed `S`, 32 bytes; kept subtree height `b ≤ 25`)

```
P = Th(0^16, address(PARAMETER, 0, 0, 0), S)
s = (u64 little endian of P[0:8]) & (2^(25−b) − 1)   if b < 25, else 0
leaves e ∈ [s·2^b, (s+1)·2^b):  WOTS leaf from the chain ends
surrogates ℓ = b..24:            Th(P, address(SURROGATE, 0, hi = ℓ, lo = 0), S)
root: the kept subtree's root, folded up through the surrogates (bit (ℓ−b) of s picks the side)
```

A full key is `b = 25`, which costs about 7.6·10⁹ keccak calls to generate: `2^25 · 226`, that is 225 per WOTS
leaf (32 secret pairs, 192 chain steps, the leaf) plus one per tree node. (sphincs-art's 8.1·10⁹ for the same key
counts BLAKE2s compressions: the 1056-byte leaf input alone takes 17.) A pruned key keeps a subtree of 2^b leaves,
and the verifier cannot tell the two apart. Tests use small `b`.

## 10. Signing (message `m`, 32 bytes)

```
R_0 = Th(P, address(RANDOMIZER, 0, 0, 0), S ‖ m)
ρ_i = (u128 little endian of R_0 + i) mod 2^128, as 16 little-endian bytes
ρ   = ρ_i for the least i ≥ 0 whose digest leaf index lies in the kept subtree (i = 0 for a full key)
(idx, u) = digest(ρ, m);  open FORS instance idx;  WOTS+C-sign the FORS key at e = idx;  auth path of idx
```

## 11. Signature encoding (4148 bytes)

| Offset | Length | Field |
|---:|---:|---|
| 0 | 16 | ρ |
| 16 + 208·κ | 16 | FORS secret `sk_{κ,u_κ}`, κ = 0..12 |
| 32 + 208·κ + 16·ℓ | 16 | FORS path `p_κ[ℓ]`, ℓ = 0..11 |
| 2720 | 4 | counter `c`, u32 little endian |
| 2724 + 16·i | 16 | WOTS value `σ_i`, i = 0..63 |
| 3748 + 16·ℓ | 16 | auth path `path[ℓ]`, ℓ = 0..24 |

Every field after the counter is offset by 4 bytes from a 16-byte boundary. `calldataload` doesn't care.

## 12. On-chain interface

```solidity
function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
    external pure returns (bool valid);
```

- `pkSeed = P ‖ 0^16` and `pkRoot = root ‖ 0^16` (high-aligned). The interface is the same as the
  C-series verifiers, so `SphincsAccount` can plug this one in.
- `sig.length != 4148` → revert `"Invalid sig length"`.
- Non-canonical key (a nonzero low 128 bits in `pkSeed` or `pkRoot`) → revert `"Invalid public key"`.
- When both are wrong, the length check runs first (so the revert is `"Invalid sig length"`). The Python
  mirror and `ls23k verify` follow the same order.
- Any well-formed signature that fails (inadmissible WOTS+C encoding, or root mismatch) → return `false`.

## 13. Signer FFI convention

`signers/leansphincs23-keccak` (Rust, port of the upstream crate) and `script/leansphincs23_signer.py`
(independent Python) both print `0x` + hex of `abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)`,
with the high-aligned key words above, which is what the Forge tests decode.
