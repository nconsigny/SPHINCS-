# leanSphincs-layered over keccak256

leanSphincs-layered is **leanSPHINCS as EthLib specifies it**: Keccak-256, FORS, and a layered key for 2³⁰
signatures, the "layered 10+8+8, FORS 24×10" set of [sphincs.art](https://sphincs.art) at lifetime 2³⁰. The
on-chain verifier is `src/keccak/LeanSphincs-LayeredAsm.sol` (contract `LeanSphincsLayeredAsm`).

**The normative spec is EthLib's Lean module** `EthLib/Cryptography/Sphincs/`
([ethereum/EthLib PR #152](https://github.com/ethereum/EthLib/pull/152), head
`aa99d5fcfd84e51e337383c477c48f4fba290e00`). That module follows Tom Wambsgans' note
[`leanSPHINCS.tex`](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex)
and its Lean model `formal/sphincs/FORS/Scheme.lean` (`Params.layered 26 3 8 24 10`) at sphincs.art commit
`1538d0a`. Where this document and the Lean module disagree, the Lean module wins. This document summarizes it for
reviewers of the verifier; each section names the Lean definitions it restates.

It is **not a re-parameterization** of leanSphincs, leanSphincs-s or leanSphincs-f (docs/leanSphincs-*.md). Those
three follow the upstream crate's older `keccak` branch: one XMSS layer, a different address layout and different
type codes. leanSphincs-layered shares their shape: a 16-byte tweakable hash with no FORS key hash, where the WOTS+C
encoding absorbs the FORS tops. Every byte-level convention below is EthLib's. A seed must never be reused across
variants.

## 1. Parameters (`Constants.lean`)

| | |
|---|---|
| hash | Keccak-256 (Ethereum's, original Keccak padding: the EVM opcode); `n = 16` (outputs truncated to the first 16 bytes) |
| hypertree | `d = 3` layers of heights **10 (top), 8 (middle), 8 (bottom)**, `h = 26` |
| FORS | `k = 24` trees of height `a = 10`, **no root hash**: the FORS key is the 48 level-9 nodes |
| WOTS+C | `v = 64` chains of `w = 4` positions (2-bit digits), **target sum `T = 128`**, no checksum chains, 4-byte LE counter |
| keys | public key 32 B = `root ‖ P` (`P` the 16-byte public parameter); secret key = a 32-byte seed `S_0` |
| message | 32 bytes (a message hash) |
| signature | **7,740 B** = `16 + 24·11·16 + 2·(4 + 64·16 + 8·16) + (4 + 64·16 + 10·16)` |
| verification | **466 keccak256 calls, 492 Keccak-f[1600] permutations**, constant |
| lifetime | **2³⁰ signatures**: the model proves 127-bit SUF-CMA security in the ROM up to 1,182,000,000 (≈ 2^30.14), theorem `h26_layered` of `formal/sphincs/FORS/Main.lean` |

The 127-bit bound is a theorem about the sphincs.art model. It is not a theorem about EthLib's module: EthLib proves
functional correctness and domain separation, and says plainly that no theorem links its module to the model
(EthLib's README, "What is not proved").

## 2. Tweakable hash and addresses (`TweakableHash.lean`, `Address.lean`)

`Th(P, A, M) = keccak256(P ‖ A ‖ M)[0:16]`. The message digest keeps all 32 bytes, and so do the signer-only
derivations, whose two halves give two secrets.

The address is 16 bytes, every field little endian:

```
[ lo: 4 | hi: 3 | type + 32·step: 1 | layer: 1 | tree: 4 | zero: 3 ]
```

| type | call | step | layer, tree | hi | lo |
|---|---|---|---|---|---|
| 0 PRF | chain starts `2j`, `2j+1` (signer) | 0 | key's | `j` | key leaf |
| 1 CHAIN | chain `i`, step from position `mu` | `mu` | key's | `i` | key leaf |
| 2 LEAF | one-time leaf over the 64 chain ends | 0 | key's | 0 | key leaf |
| 3 NODE | tree node at level `λ` (1..height), index `j` | 0 | tree's | `λ` | `j` |
| 4 ENCODING | `Th(P, A, msg ‖ LE32(c))` | 0 | key's | 0 | key leaf |
| 5 PARAM | `P = Th(0^16, A, S)` (signer) | 0 | 0 | 0 | 0 |
| 7 RND | `R = Th(P, A, S ‖ m)` (signer) | 0 | 0 | 0 | 0 |
| 12 MSG | digest call `c` | 0 | 0 | `c` | 0 |
| 14 FORS_PRF | FORS secrets of leaves `2p`, `2p+1` (signer) | 0 | 0 | `κ + 64p` | `idx` |
| 15 FORS_LEAF | FORS leaf `l` of tree `κ` | 0 | 0 | `κ + 64l` | `idx` |
| 17 FORS_NODE | FORS node at level `λ`, index `j`, tree `κ` | 0 | 0 | `κ + 64(λ + 16j)` | `idx` |

The layers are numbered from the bottom: 0 bottom, 1 middle, 2 top. A layer's one-time key on the path of `idx` is
`OtsKey.ofIndex`:

| layer | tree | leaf |
|---|---|---|
| 0 bottom | `idx >> 8` (< 2¹⁸) | `idx mod 2⁸` |
| 1 middle | `idx >> 16` (< 2¹⁰) | `(idx >> 8) mod 2⁸` |
| 2 top | 0 | `idx >> 16` (< 2¹⁰) |

## 3. Message digest (`Digest.lean`)

```
D_c = keccak256(P ‖ A_msg(c) ‖ m ‖ R)       c = 0, 1  (80-byte inputs)
D   = D_0 ‖ D_1, read as ONE 512-bit little-endian number
idx      = bits 0..25
leaf_κ   = bits 26 + 10κ .. 35 + 10κ        κ = 0..23
```

`leaf_23` is bits 256..265, so it lies entirely in `D_1` (its byte 0, and the low 2 bits of byte 1). The public
key's root is not hashed into the digest, because `P` already binds the digest to the key.

## 4. FORS (`Fors.lean`)

Each tree `κ` of instance `idx` has leaves `Y_{0,l} = Th(P, A_fleaf(idx, κ, l), s_l)` and nodes
`Y_{λ,j} = Th(P, A_fnode(idx, κ, λ, j), Y_{λ-1,2j} ‖ Y_{λ-1,2j+1})` for `λ = 1..9`. Level 10 is never hashed. An
opening is the secret of `leaf_κ` and its 10 path nodes, from level 0 up. The last path node is the other level-9
node. The verifier climbs 9 levels (`Merkle.climb`), then orders the level-9 node it reached with path node 9 by bit
9 of `leaf_κ` (`Merkle.ordered`). The FORS key is the 48 nodes `t_0[0] ‖ t_0[1] ‖ … ‖ t_23[1]`, 768 bytes. No hash
folds them: the bottom one-time key signs those bytes directly.

## 5. WOTS+C and the layers (`Encoding.lean`, `Ots.lean`, `Tree.lean`, `Verify.lean`)

For each layer, from the bottom up, with key `K = OtsKey.ofIndex(layer, idx)`:

1. `d = Th(P, A_enc(K), msg ‖ LE32(c))`, where `msg` is the FORS key (768 B, an 804-byte input) on the bottom layer
   and the root of the layer below (16 B, a 52-byte input) above it.
2. Digits `x_i = (LE128(d) >> 2i) & 3`, `i < 64`. **Reject unless `Σ x_i = 128`.** Each layer is checked: a failing
   counter on any layer makes the whole signature invalid.
3. `end_i` = chain `σ_i` from position `x_i` to 3. The step from position `mu` is `Th(P, A_chain(K, i, mu), ·)`.
   The verifier walks `3·64 − 128 = 64` steps per layer.
4. `leaf = Th(P, A_leaf(K), end_0 ‖ … ‖ end_63)`, a 1,056-byte input.
5. `root = Tree.fold`: climb `height` levels from `(0, K.leaf)`. The node at level `λ`, index `j` is
   `Th(P, A_node(layer, K.tree, λ, j), L ‖ R)`.

Accept iff no layer failed and the top root equals the key's root.

## 6. Signature layout (`Serialization.lean`)

| offset | field |
|---|---|
| 0 | `R` (16) |
| `16 + 176κ` | FORS secret of tree `κ` (16), `κ = 0..23` |
| `32 + 176κ + 16ℓ` | FORS path node `ℓ` of tree `κ`, `ℓ = 0..9` |
| 4240 / 5396 / 6552 | bottom / middle / top layer signature (1,156 / 1,156 / 1,188 B), each: |
| `+0` | counter `c`, u32 LE (4) |
| `+4 + 16i` | chain value `σ_i`, `i = 0..63` |
| `+1028 + 16ℓ` | tree path node `ℓ`, `ℓ < 8 / 8 / 10`, from the leaf up |

## 7. The verifier

`verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig) → bool`, the repo's shared interface. The key
words are EthLib's public key split and high-aligned: `pkSeed = pk[16:32] ‖ 0^16` (P), `pkRoot = pk[0:16] ‖ 0^16`
(root). It reverts `Error("Invalid sig length")` unless `sig.length == 7740`. It reverts `Error("Invalid public
key")` if either key word has a nonzero low half, and the length is checked first. Otherwise it returns `false` or
`true`: an inadmissible counter returns `false` at once (after 243 calls for the bottom layer). The verifier is
`pure` and stateless, deployed once and shared by every account.

Work:

| | calls | input bytes | permutations |
|---|---:|---:|---:|
| message digest | 2 | 80 | 2 |
| FORS leaves | 24 | 48 | 24 |
| FORS nodes (24 · 9) | 216 | 64 | 216 |
| bottom encoding | 1 | 804 | 6 |
| middle, top encodings | 2 | 52 | 2 |
| chain steps (3 · 64) | 192 | 48 | 192 |
| one-time leaves | 3 | 1,056 | 24 |
| tree nodes (8 + 8 + 10) | 26 | 64 | 26 |
| **total** | **466** | | **492** |

Gas (Forge; forge 1.5.1, solc 0.8.33, via-IR): **81,958–82,289** in its own call frame over the EthLib and fixture
signatures. Any admissible signature costs **80,395–83,482**, because the gas depends only on the WOTS step counts.
That range comes from a zero-residual fit of the per-chain costs over 381 random-digest signatures, extremised over
every step-count split. `test/LeanSphincsLayeredTest.t.sol` gates it at 83,700. Through `SphincsAccount` (ECDSA +
leanSphincs-layered), `validateUserOp` costs about 90.6 K.

**On chain.** On the ethrex privacy testnet (chain 8141), a full EIP-8141 frame transaction used **516,906 gas**:
a VERIFY frame of 90,385 (the verifier plus the frame module) and a SENDER frame transferring 0.00001 ETH
([`0x902c9423…`](https://dora.privacy.ethrex.xyz/tx/0x902c942324fa1195bee3e9aa1b48fb84fdee45931250d904cd0992859985b3ab); `docs/deployments.md`). That is
the calldata floor, `21,546 + 64 × 7,740`: the 7,740-byte signature sets the cost, and the verifier's execution is far
below the floor. A cheaper verifier would not make this transaction cheaper.

**Gas estimation.** Rejections are cheaper than acceptance: about 38 K when the bottom layer's counter is
inadmissible, which is the case for any random or all-zero dummy signature, and about 67 K when only the top
layer's is. A wallet that estimates `verificationGasLimit` with a dummy signature therefore underestimates by about
44 K. The verifier then runs out of gas inside the account's staticcall, and `SphincsAccount` reports that as
`SIG_VALIDATION_FAILED` (AA24), not as out of gas. So budget at least 84 K for the verifier, or estimate with a dummy
whose three counters are admissible. `verify` is `pure`, so simulation and inclusion always agree.

The Yul is derived from `LeanSphincsAsm.sol`: the same hash window, MASKING, L/R placement and chain dispatch, all
documented in the source. The new parts are the address's layer and tree bytes, which live in memory at 0x20..0x27
and 0x80..0x87 and are written once per layer. Also new are the FORS position encoding, the digest's bit layout and
a `layerRoot` function run once per layer.

## 8. Signing

`script/leansphincs_layered_signer.py` is a Python reference of `keyGen` and `sign`. It derives every secret from
`S = keccak256("leanSPHINCS" ‖ S_0)`, signs deterministically, and self-verifies before output. It reproduces every
EthLib `key_gen` and `sign` vector, every `verify` verdict, and the Lean known answer with all its intermediate
values, byte for byte (`ethlib-check`).

Keygen is 231,425 keccak256 calls (238,593 permutations): the top tree of 2¹⁰ one-time keys, plus the seed-tag hash.
A signature from the seed alone rebuilds the top tree's path, both lower trees, the FORS instance and three counter
searches, about half a million calls. Each search tries about 2^13.8 ≈ 14,700 counters (`P[Σx = 128] = 2^-13.84`,
EthLib `code_probability`). In Python on one host core, keygen takes about 0.9 s and a signature about 1 s with the top tree
cached. The CLI's `sign` takes about 2.5 s, because it rebuilds the top tree and self-verifies.

There are no tiered key files or Rust CLI, unlike the other leanSphincs variants. **Never sign more than 2³⁰ messages
with one key.** Nothing counts signatures, so the caller must.

## 9. Test vectors and tests

- `test/fixtures/leansphincs-layered-ethlib.json` vendors EthLib's own vectors (CC0-1.0) via
  `script/ethlib_sphincs_fixture.py <ethlib-checkout>`: 4 `key_gen`, 5 `sign` and 24 `verify` cases, each file
  checked against EthLib's `SHA256SUMS`. It also holds the Lean known answer (`Proofs/Sphincs/KnownAnswer.lean`, a
  key from the scheme seed `S[i] = 37i + 11` signing `m[i] = 7i + 3`) with its intermediate values.
- `test/fixtures/leansphincs-layered-keccak-kat.json` holds 6 signatures from the Python signer, made by
  `script/make_leansphincs_layered_kat.py` (`--check` reproduces it). Each has per-layer counter substitutions that
  isolate each layer's target-sum check.
- `test/LeanSphincsLayeredTest.t.sol` covers:
  - every EthLib verify case;
  - the sign outputs under the key_gen keys;
  - the Lean known answer and its intermediate values, against a plain-Solidity spec model;
  - per-field tampering on every layer, and every bit of P, the root and the message;
  - each layer's target sum on its boundary (127 and 129), and at a second codeword, under the zero root too;
  - a fuzz against the spec model;
  - random-digest signatures whose three counters are ground in the test;
  - malformed input, dirty ABI padding and non-canonical ABI offsets;
  - the gas ceiling;
  - a fresh FFI signature.
- `test/SphincsAccountLeanSphincsLayeredTest.t.sol` runs the 4337 account path.

## 10. Review

- **Mutation testing.** 52 single-point mutants of the verifier were run against the suite, and all were killed.
  They cover masks, shifts, type codes, level constants, store order, hash lengths, the target-sum comparison, the
  key checks, ABI positions and partial root comparisons.
- **Independent spec review** (November 2026). The reviewer wrote a model of `verify` from the Lean files alone. It
  agrees with all 24 EthLib verify vectors. The compiled verifier matched it on 314 vectors, 153 of them valid, with
  edge cases ground for: top leaf ≥ 768; bottom and middle leaf 255; FORS leaves 0 and 1023; bit 9 set and clear on
  trees 0..5, 22 and 23; zero and all-ones P and messages. Every single-byte signature flip and every key or message
  bit flip rejects. The reviewer found no divergence, and every memory and calldata claim in the source checked out.
- **Independent adversarial review** (November 2026). It found nothing exploitable in the verifier or in its use by
  `SphincsAccount`, covering non-canonical, unaligned and junk-padded ABI offsets, memory aliasing, control flow and
  layer mixing. It found four gaps in the tests, each of which would have let a plausible regression through: the
  root was compared at 2 of its 128 bits, below-T was tested only far from T, the zero root was never paired with
  an inadmissible top layer, and every call used the canonical ABI encoding. Those four are now tested, and their
  mutants are among the 52 above. It also raised the gas-estimation note in §7.

## 11. Notes on the spec text

Two comments in the EthLib Lean module disagree with its definitions. The definitions are what this repo follows,
and both slips are harmless:

- `Digest.lean` says "leaf 23 straddles the two calls". It does not: `leaf_23` is bits 256..265, all in `D_1`, and
  no leaf straddles the boundary (`leaf_22` ends at bit 255).
- `Address.lean` says "The bottom layer has the most trees, `2^17`". It has `2^26 / 2^8 = 2^18` (`Types.lean` says
  `2^18`). A tree number fits the 4-byte field either way.
