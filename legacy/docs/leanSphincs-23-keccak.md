# leanSphincs-23 over keccak256

> **Retired (legacy).** leanSphincs-23 is superseded by leanSphincs-s (one more tree level, `h = 26`, and the
> upstream `keccak` branch's merged encoding): see [`docs/leanSphincs-S-keccak.md`](../../docs/leanSphincs-S-keccak.md).
> The verifier now lives in `legacy/src/LeanSphincs-23Asm.sol`, its Forge suites in `legacy/test/` (run with
> `FOUNDRY_TEST=legacy/test forge test --match-contract LeanSphincs23`); the signers
> (`signers/leansphincs23-keccak`, `script/leansphincs23_signer.py`) stay where they are. This spec is frozen.

leanSphincs-23 is the retuned leanSphincs set from the
[sphincs-art fork](https://nconsigny.github.io/sphincs-art/) (source:
[nconsigny/sphincs-art](https://github.com/nconsigny/sphincs-art)). leanSphincs itself is Tom Wambsgans'
proposal ([note](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/releases/download/doc-latest/leanSPHINCS.pdf),
[code](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/tree/main/crates/sphincs)). This
document pins the keccak256 instantiation that the on-chain verifier `legacy/src/LeanSphincs-23Asm.sol`
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
and the verifier cannot tell the two apart. Tests use small `b`. §14 generates a key once and signs from a key file
with a bounded node cache.

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
with the high-aligned key words above, which is what the Forge tests decode. `ls23k sign-key` (§14) prints the
same bytes from a key file.

## 14. Tiered signers

A tiered signer generates the key once, for a kept subtree of height `b` (§9), and stores the key with a node cache of
bounded size. Each signature then recomputes only the auth-path nodes that the cache does not hold. The tiers are the
"One signer, leanSphincs-23" table of the [sphincs-art fork](https://nconsigny.github.io/sphincs-art/), in the page's
vanilla variant (its default view, FORS with no root hash; the figures below are that view's). There is one parameter
set, and the tiers differ only in how much of the tree the signer builds and keeps.

A tiered signature is **byte-identical** to the stateless `sign(key_gen(S, b), m)` of §9–§10. The two signers use the
same `P`, the same subtree position `s`, the same root, the same `ρ` (`R_0 + i`, the least `i` that lands in the kept
subtree), the same WOTS+C counter and the same FORS openings. Only the source of the auth-path nodes changes. The
verifier, the encoding and every existing KAT and fixture stay as they are, and no one can tell which signer produced a
signature.

| Tier | Device class (the page's) | `b` | Cache | Cache plan | Cached nodes |
|---|---|---:|---:|---|---:|
| Light | Ledger Nano S+ | 13 | 16 KiB | level 3 only | 1,024 |
| Standard | weak CPU | 20 | 1 MiB | levels 5..20 | 65,535 |
| Full | powerful CPU | 25 (whole tree) | 16 MiB | levels 6..25 | 1,048,575 |

The device classes are the page's, sized from its BLAKE2s figures. Light's 16 KiB cache is the page's budget for a
Ledger Nano S+ class device, but a keccak256 call costs more than a BLAKE2s compression on such a device, so the page's
times are optimistic here. Neither the model nor the reference signer measures device times.
`signers/leansphincs23-keccak` is a host-side reference signer, not a device implementation. A custom `(b, cache_bytes)`
picks its plan by the rule under "Cache plans" below.

### CLI

`signers/leansphincs23-keccak` implements the tiers (`ls23k`, see its README):

```sh
ls23k keygen --seed-file seed.hex --tier light -o key.ls23k   # or --seed-stdin; --tier standard|full, or --b N --cache-bytes N
                                                              # [--force] [--threads N]; prints 0x || abi.encode(pkSeed, pkRoot)
ls23k sign-key key.ls23k <msg_hex64>                          # 0x || abi.encode(pkSeed, pkRoot, sig): the bytes `ls23k sign` prints
ls23k info key.ls23k                                          # JSON: tier, b, s, plan, cache, key words, costs; no secret
```

`keygen` reads the seed from a file that group and others cannot access, or from standard input, never from the
command line (where other local users and the shell history see it). It checks the output path before the keygen, and
writes the key file (mode 0600) through a temporary file beside it, so nothing partial is ever at the key file's path.
Without `--force` it never replaces an existing file. `sign-key` verifies each signature under the key file's public
key before printing it.

### Cache plans

The auth path of leaf `idx` is the `b` siblings inside the kept subtree (levels `0..b−1`), followed by the `25 − b`
surrogates (levels `b..24`). The surrogates are stored with the key, or re-derived at one call each, and do not count
toward the cache. A cache of `cache_bytes` holds `⌊cache_bytes / 16⌋` nodes. A plan keeps one of the following:

| Plan | Cached | Keccak calls per signature |
|---|---|---|
| whole | every node of the subtree, `2^(b+1) − 1` | 0 |
| top `c` | levels `c..b`, `2^(b−c+1) − 1` nodes | `2^c·225 + (2^c − 1)` |
| level `c` | level `c` only, `2^(b−c)` nodes | `2^c·225 + (2^c − 1) + (2^(b−c) − 1)` |
| none | nothing | `2^b·225 + (2^b − 1)` |

`1 ≤ c ≤ b`. The term `2^c·225 + (2^c − 1)` rebuilds the `2^c`-leaf block that holds `idx`, which gives the siblings
below level `c`. A WOTS leaf costs 225 calls (32 secret pairs, 192 chain steps, the leaf hash). A "level" plan also
rehashes the cached nodes up to the subtree root to get the siblings above level `c`. The signer uses the cheapest
plan that fits. On equal cost it takes the plan with fewer cached nodes, then prefers "top" over "level". The only
ties are between "none", "top `b`" and "level `b`", which all do the same work, and the rule picks "none". The keygen
pass computes every node of the subtree anyway, so filling the cache adds nothing to keygen.

- **Light** (1,024 nodes): the whole subtree is 16,383 nodes. Levels 4..13 fit and cost `16·225 + 15 = 3,615` per
  signature. Level 3 alone costs `8·225 + 7 + 1,023 = 2,830`, which is less.
- **Standard** (65,536 nodes): levels 5..20 are 65,535 nodes. Each signature rebuilds a 32-leaf block, `32·225 + 31 =
  7,231` calls.
- **Full** (1,048,576 nodes): levels 6..25 are 1,048,575 nodes. Each signature rebuilds a 64-leaf block, `64·225 + 63 =
  14,463` calls. Caching the whole tree would take `2^26 − 1` nodes (1 GiB) and make the auth path free.

### Cost

Keygen costs `2^b·226 + 2·(25 − b)` keccak256 calls: `P`, 225 calls per WOTS leaf, the `2^b − 1` nodes of the kept
subtree, then the surrogates derived and folded. (The page's model counts `2^b` nodes, one call more.) Signing costs
on average, in the page's model,
`R_0 (1) + digest (1) + 2^(25−b) randomizer tries + FORS 133,095 + WOTS+C 14,830.4 + auth path`, with no randomizer
tries for `b = 25`. The FORS term is `13·(2,048 + 4,096 + 4,094) + 1`. The WOTS+C term is 14,670.4 mean encoding
tries plus 32 secret pairs and 128 chain steps. Both grinds are geometric, so the cost of a single signature varies
around this mean.

| | Light | Standard | Full |
|---|---:|---:|---:|
| Keygen (once), keccak256 calls, the signer | 1,851,416 (1.85M) | 236,978,186 (237M) | 7,583,301,632 (7.58B) |
| Keygen, keccak256 calls, the page's model | 1,851,417 | 236,978,187 | 7,583,301,633 |
| Keygen, BLAKE2s compressions (page) | 1.98M | 254M | 8.12B |
| Sign, mean, keccak256 calls, the page's model | 154,853 | 155,190 | 162,390 |
| … randomizer grind | 4,096 | 32 | 0 |
| … auth path | 2,830 | 7,231 | 14,463 |
| Sign, mean, keccak256 calls, the reference signer | 154,866 | 155,203 | 162,404 |
| `sign-key`: verification of the signature | 249 | 249 | 249 |
| `sign-key`: loading and checking the key file, per run | 1,048 | 32,778 | 524,288 |
| Sign, BLAKE2s compressions (page) | 155K | 156K | 163K |
| Page's time, keygen / sign | 60 s / 4.7 s | 2.0 s / 1.2 ms | 8.1 s / 0.16 ms |
| Verify, keccak256 calls | 249 | 249 | 249 |

The page's times are BLAKE2s compressions at its device rates (33K, 128M and 1G per second). They do not transfer to
keccak256, because the devices' keccak throughput is different. The two counts differ only where an input is longer
than one BLAKE2s block. A keccak256 call is one call however long its input is, while BLAKE2s pays one compression
per 64-byte block: 17 for the WOTS leaf hash, 7 for the FORS key, 2 each for `R_0` and the digest.

`signers/leansphincs23-keccak/tier_model.py` transcribes the page's cost model (sphincs-art
`scripts/sweep_leansphincs_pruned.py` at `1ca729f`: `tree_cost`, `fors_sign`, `tier_costs`, `cover_lifetime`) in
keccak256 calls. It prints the model's rows above, a custom column with `--b N --cache-bytes N`, the BLAKE2s figures
with `--units blake2s`, and JSON with `--json`. `--check` asserts the model's figures in this section and the page's.
The model keeps three of the script's counting conventions, each one call or one cached node over a minimal signer: it
counts the digest on top of the grind, although the grind's last try is the digest; it counts `2^b` subtree nodes
where there are `2^b − 1`; and its "top" plan caches, and its "level" plan rehashes, the subtree root, which no auth
path uses.

The reference signer is measured against the model as follows (exact counts, from its tests and benchmarks):

- keygen is one call under the model (`2^b − 1` nodes);
- the auth path equals the model's per-plan cost exactly: with a "level" plan, the rehash up to the subtree root is the
  signer's check of the cache;
- a signature costs the model's mean plus 13 calls for `b < 25`, because the 13 opened FORS secrets are derived a
  second time, and plus 14 at `b = 25`, where it also makes one grind try and recomputes the digest after it (the model
  counts no grind there);
- `sign-key` also spends 249 calls verifying each signature under the key file's public key, and each run loads and
  checks the key file (every cached node above the lowest cached level, `P` and the surrogates). The model counts
  neither.

### Lifetime

| | Light | Standard | Full |
|---|---:|---:|---:|
| Rated (the page's target) | 20,000 | 2^21 (2.1M) | 2^23 (8.4M) |
| Cover estimate at 127 bits | 40,274 (40.2K, ×2.01) | 2,781,217 (2.78M, ×1.33) | 54,085,110 (54.0M, ×6.45) |

The estimate is the cover bound of the leanSPHINCS note (§3). It gives the largest `N` with
`2^127 · 2^(b−25) · E_{r ~ Poisson(N/2^b)}[(1 − (1 − 2^−12)^r)^13] ≤ 1`. It is an estimate and is not proved. For the
original leanSphincs parameters, the Lean-proved lifetimes are 4–17% below this estimate, and the gap is widest at
small `b`. The page therefore rates each tier at a target that the estimate clears by at least 25%, and it rounds the
estimates down. The estimate depends only on `(h, b, a, k)`, so it is the same for keccak256 as for BLAKE2s. The
lifetime is a count of signatures under one key, whichever signer made them. Nothing enforces it: not the signature,
not the verifier, and not the signer or the key file, which keep no count of signatures.

### Operational rules

- **One seed is one key.** Never use a seed with two different `b`: two tiers, a tier and a custom `b`, or the plain
  `ls23k sign` at another `b`. `P`, the WOTS and FORS keys and the real tree nodes depend on `S` and the leaf index
  only, not on `b` (§6–§9). Where two same-seed keys' kept subtrees overlap, a signature of one key is turned into a
  valid signature of the other by replacing its auth path above the smaller subtree with the other key's nodes there.
  Those are public: the other key's surrogates, or the path of any of its signatures whose leaf falls in the shared
  subtree. No secret is needed. A full key's tree contains every subtree, so the overlap is certain against a full key;
  a Light and a Standard key from one seed overlap for 1 seed in 32. The stronger key then falls to the weaker one's
  lifetime, and the usage of the two keys adds up. Use a fresh, independent seed for every key. The plain `ls23k sign`
  at the same `b` is the same key, and its signatures are identical to the tiered signer's.
- **The key file holds the secret seed.** Anyone with the file can sign. It is created with mode 0600; back it up like
  a private key. Everything else in the file (`P`, `s`, the root, the surrogates, the cache) is derived from `S` and
  `b`, and the seed and `b` alone rebuild the key, at the keygen cost above. The cached nodes are not secret: they are
  hashes of WOTS public keys, and auth paths reveal them as the key is used. The cache needs integrity, not secrecy.
- **What a key file proves.** Loading checks that `P`, `s` and the surrogates are the seed's, and that the cache, the
  kept subtree's root and the root are consistent with one another. It cannot check that the root is the seed's
  without a keygen. A file whose cache was edited consistently and re-checksummed loads and reports its own root; the
  checksum covers `S`, so only a holder of the seed can make one. A corrupt key file is refused when it is loaded, a
  cache corrupted in memory afterwards is refused where signing recomputes over it, and `sign-key` verifies every
  signature under the key file's public key before printing it. So a printed signature always verifies under the key
  words printed with it: compare those with the registered key. (A signature from a bad auth path would reveal
  nothing beyond the correct signature of the same message.)
- **Signing is deterministic.** The same message gives the same signature, which reveals nothing new. Each distinct
  message counts against the lifetime.
- **The verifier is unchanged.** Tiered signatures are the stateless signer's signatures, so
  `legacy/src/LeanSphincs-23Asm.sol`, the 249-call verification and the KAT fixture apply as they are.
