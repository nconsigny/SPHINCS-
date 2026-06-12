/-
  Concrete C13 `Primitives` package (Phase 0, STRATEGY §1).

  This file replaces the *opaque* `axiom c13Primitives : Primitives` with a
  concrete `def c13PrimitivesConcrete : Primitives` whose hashing is routed
  through the SAME pure Keccak the Verity interpreter uses
  (`KeccakEngine.keccak256`), fed the SAME big-endian word-aligned byte preimage
  the interpreter feeds it (`memorySliceBytesBE` / `byteArrayToNatBE`, see
  `Compiler/Proofs/IRGeneration/SourceSemantics.lean`).

  It is ADDITIVE: it does not touch `axiom c13Primitives`, `execC13`, the bridge
  axioms, or `Model.lean`. It models `src/SPHINCs-C13Asm.sol` faithfully.

  ## The hash bridge (STEP 1)

  The interpreter models EVM `keccak256(offset, size)` as

      keccakMemorySlice memory offset size
        = wordNormalize (byteArrayToNatBE
            (keccak256 (memorySliceBytesBE memory offset size)))

  where `memorySliceBytesBE` concatenates `wordToBytesBE (memory cell)` for each
  32-byte-aligned cell covering `[offset, offset+size)` and keeps the first
  `size` bytes.  For every C13 hash, `size` is a multiple of 32 (0x60, 0x80,
  0xA0, 0x120, 0x5A0), so the preimage is *exactly* the big-endian concatenation
  of the 32-byte memory words.  `byteArrayToNatBE` then reads the 32-byte digest
  back big-endian (byte 0 most significant) — i.e. exactly how the EVM treats a
  keccak result as a 256-bit word.

  We therefore work in the contract's native unit — the 256-bit memory word
  (`Word := Nat`, taken mod 2^256) — and define a kernel `keccakWords` that:
    * encodes each input word big-endian (`wordToBytesBE`, the SAME function),
    * concatenates them,
    * applies `KeccakEngine.keccak256`,
    * reads the result big-endian (`byteArrayToNatBE`, the SAME function).
  This is definitionally the value the interpreter computes for the matching
  word-aligned `keccak256(0x00, 32*k)` call, so a future model→spec proof can
  rewrite each interpreter hash to a `keccakWords` application by `rfl`/`simp`.
-/

import SphincsMinusVerifierSpec.Spec
import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SphincsMinusVerifierSpec
namespace C13Concrete

open Compiler.Proofs.IRGeneration.SourceSemantics (wordToBytesBE)

/-- A 256-bit EVM memory word, represented as a `Nat` (callers keep it `< 2^256`). -/
abbrev Word := Nat

def wordMod : Nat := 2 ^ 256

/-- The C13 `N_MASK`: keep the high 16 bytes (n=128 bits) of a 256-bit word,
zero the low 16 bytes.  This is the contract's
`0xFFFF…FFFF00000000000000000000000000000000`. -/
def nMask : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

/-- Apply `N_MASK` to a word (`and(w, N_MASK)` in the contract). -/
def maskN (w : Word) : Word := w &&& nMask

/-! ### STEP-1 kernel: keccak over big-endian 32-byte words

`keccakWords ws` is the interpreter's `keccak256(0x00, 32 * ws.length)` value
when memory cell `32*i` holds `ws[i]`: the inputs are encoded big-endian with
the SAME `wordToBytesBE`, concatenated in the SAME order, hashed with the SAME
`KeccakEngine.keccak256`, and read back big-endian with the SAME
`byteArrayToNatBE`.  The only deliberate omission is the interpreter's outer
`wordNormalize` (mod 2^256): a keccak digest is already `< 2^256`, so the two
agree on every C13 call (we re-establish this with `keccakWords_lt`). -/
def keccakBytes (ws : List Word) : ByteArray :=
  KeccakEngine.keccak256
    (ws.foldl (fun acc w => acc ++ wordToBytesBE w) ByteArray.empty)

def keccakWords (ws : List Word) : Word :=
  KeccakEngine.byteArrayToNatBE (keccakBytes ws)

/-- The C13 tweakable hash kernel, of the contract's shape
`and(keccak256(seed ‖ adrs ‖ payload), N_MASK)`.  Each of `seed`, `adrs`, and
the `payload` entries is one 256-bit memory word. -/
def thKeccak (seed adrs : Word) (payload : List Word) : Word :=
  maskN (keccakWords (seed :: adrs :: payload))

/-! ### Word ↔ 16-byte hash conversions

C13 hashes are 16 bytes (n=128) living in the *high* 16 bytes of a 256-bit
word (post-`N_MASK`).  The spec's `Bytes` values for nodes/seeds/roots are
16-byte `ByteArray`s.  `wordOfHash16` injects a 16-byte hash into the high half
of a word; `hash16OfWord` reads the high 16 bytes back as a 16-byte `ByteArray`.
These are mutually inverse on canonical inputs (16-byte arrays / masked words). -/

/-- Big-endian `Nat` value of a `ByteArray` (byte 0 most significant). -/
def baToNatBE (ba : ByteArray) : Nat :=
  ba.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Inject a 16-byte hash into the high 16 bytes of a 256-bit word. -/
def wordOfHash16 (b : Bytes) : Word := (baToNatBE b % (2 ^ 128)) * (2 ^ 128)

/-- Read the high 16 bytes of a word as a 16-byte big-endian `ByteArray`. -/
def hash16OfWord (w : Word) : Bytes :=
  ⟨((List.range 16).map (fun i => UInt8.ofNat ((w / (256 ^ (31 - i))) % 256))).toArray⟩

/-- Reading the high half of a word always produces a C13-sized hash. -/
theorem hash16OfWord_size (w : Word) : (hash16OfWord w).size = 16 := by
  simp [hash16OfWord, ByteArray.size]

/-- A byte string is canonical for C13 root comparison when it is the high
16-byte projection of some word. -/
def CanonicalHash16 (b : Bytes) : Prop := ∃ w, b = hash16OfWord w

theorem hash16OfWord_canonical (w : Word) : CanonicalHash16 (hash16OfWord w) :=
  ⟨w, rfl⟩

/-! ### Signature byte layout (C13, 3688 bytes)

    R                 : bytes  0..16   (high 16 of word at offset 0)
    FORS sk[7]        : 16 + 16*i      (i = 0..6)        -> 128 bytes total
    FORS auth[6][19]  : 128 + 304*t + 16*h               -> 1824 bytes
    HT_START          : 1952
    per layer (×2):
      chains[43]      : sigOff + 16*i                     -> 688 bytes
      count           : sigOff + 688 (high 4 bytes = uint32, shr 224)
      auth[11]        : sigOff + 692 + 16*h               -> 176 bytes
      next sigOff     : (sigOff + 692) + 176 = sigOff + 868

All 16-byte fields are read as `and(calldataload(off), N_MASK)`, i.e. the high
16 bytes of the 32-byte word at `off`. -/

/-- Read the 16-byte hash at byte-offset `off` from `sig`, as a `ByteArray`. -/
def read16 (sig : Bytes) (off : Nat) : Bytes :=
  ⟨((List.range 16).map (fun i => (sig[off + i]?).getD 0)).toArray⟩

def parseSignatureC13 (v : Variant) (sig : Bytes) : Option Signature :=
  if sig.size ≠ v.sigBytes then none
  else
    let R := read16 sig 0
    let forsSk := (List.range 7).map (fun i => read16 sig (16 + 16 * i))
    let forsAuth := (List.range 6).map (fun t =>
      (List.range 19).map (fun h => read16 sig (128 + 304 * t + 16 * h)))
    let fors : ForsSig := { sk := forsSk, authPath := forsAuth }
    let layers := (List.range 2).map (fun layer =>
      let sigOff := 1952 + 868 * layer
      let chains := (List.range 43).map (fun i => read16 sig (sigOff + 16 * i))
      -- count = uint32 in the high 4 bytes of the word at sigOff+688
      let count :=
        (List.range 4).foldl
          (fun acc j => acc * 256 + ((sig[sigOff + 688 + j]?).getD 0).toNat) 0
      let auth := (List.range 11).map (fun h => read16 sig (sigOff + 692 + 16 * h))
      ({ wots := { chains := chains, count := count }, authPath := auth } : XmssLayerSig))
    some { R := R, fors := fors, layers := layers }

/-! ### Auth-path extraction lemmas (`hauth`)

These pin the byte-offset of every auth-path sibling the climb reads, purely as a
list-indexing fact about `parseSignatureC13`'s `(List.range n).map …` fields.  No
execution semantics: the model→spec climb correspondence consumes these as the
`hauth` supplier (`(auth[h]?).getD ⟨#[]⟩ = read16 sig sOff`). -/

/-- Indexing into a `range`-map: `((range n).map f)[h]? = some (f h)` when `h<n`. -/
theorem getElem?_map_range {α} (f : Nat → α) {n h : Nat} (hh : h < n) :
    ((List.range n).map f)[h]? = some (f h) := by
  rw [List.getElem?_map, List.getElem?_range hh]
  rfl

/-- Indexing into a `range`-map, `getElem` form. -/
theorem getElem_map_range {α} (f : Nat → α) {n h : Nat} (hh : h < n) :
    ((List.range n).map f)[h]'(by simp [hh]) = f h := by
  simp only [List.getElem_map, List.getElem_range]

/-- When `parseSignatureC13` succeeds, its size guard passed. -/
theorem parseSignatureC13_size {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s) : sig.size = v.sigBytes := by
  unfold parseSignatureC13 at hparse
  by_cases hsz : sig.size = v.sigBytes
  · exact hsz
  · simp [hsz] at hparse

/-- The concrete C13 parser has exactly one guard: signature byte length.  On
the length-ok branch it always constructs a parsed signature. -/
theorem parseSignatureC13_some_of_size {v : Variant} {sig : Bytes}
    (hsz : sig.size = v.sigBytes) :
    ∃ s, parseSignatureC13 v sig = some s := by
  unfold parseSignatureC13
  simp [hsz]

/-- Parse failure for the concrete C13 parser is equivalent to failing its byte
length guard. -/
theorem parseSignatureC13_eq_none_iff {v : Variant} {sig : Bytes} :
    parseSignatureC13 v sig = none ↔ sig.size ≠ v.sigBytes := by
  unfold parseSignatureC13
  by_cases hsz : sig.size = v.sigBytes <;> simp [hsz]

/-- `Option.isSome` form of `parseSignatureC13_some_of_size`. -/
theorem parseSignatureC13_isSome_iff {v : Variant} {sig : Bytes} :
    (parseSignatureC13 v sig).isSome ↔ sig.size = v.sigBytes := by
  unfold parseSignatureC13
  by_cases hsz : sig.size = v.sigBytes <;> simp [hsz]

/-- Successful concrete C13 parsing fixes the parsed `R` field to the first
16-byte signature read. -/
theorem parseSignatureC13_R {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 c13 sig = some s) :
    s.R = read16 sig 0 := by
  unfold parseSignatureC13 at hparse
  by_cases hsz : sig.size = c13.sigBytes
  · simp [hsz] at hparse
    rw [← hparse]
  · simp [hsz] at hparse

/-- Successful concrete C13 parsing constructs exactly the C13 signature shape:
16-byte `R`, seven 16-byte FORS secrets, six FORS auth paths of height 19, and
two XMSS layers with 43 WOTS chains and 11 auth nodes each. -/
theorem parseSignatureC13_shape {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 c13 sig = some s) :
    signatureShapeOk c13 s = true := by
  have hsz : sig.size = c13.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  simp [signatureShapeOk, allSized, allAuthSized, read16, ByteArray.size, c13]

/-- C13 accepts the contract-facing public-key words without low-byte
canonicality checks. -/
theorem publicKeyOk_c13 (pk : PublicKey) :
    publicKeyOk c13 pk = true := by
  simp [publicKeyOk, c13]

/-- Byte-level C13 public-key parsing is just the two exposed `bytes32`
arguments packaged as a `PublicKey`. -/
theorem parsePublicKey_c13 (pkSeed pkRoot : Bytes) :
    SphincsMinusVerifierSpec.ByteLevel.parsePublicKey c13 pkSeed pkRoot =
      some { pkSeed := pkSeed, pkRoot := pkRoot } := by
  simp [SphincsMinusVerifierSpec.ByteLevel.parsePublicKey, publicKeyOk_c13]

/-- Current byte-level C13 public-key parsing does not imply the 16-byte root
shape needed to reflect the executable word comparison back to raw byte-array
equality.  This records the exact blocker for making the C13 byte-refinement
reducer unconditional without either normalizing the byte spec's public key or
adding a public-key shape premise. -/
theorem parsePublicKey_c13_does_not_force_pkRoot_size :
    ∃ pkSeed pkRoot pk,
      SphincsMinusVerifierSpec.ByteLevel.parsePublicKey c13 pkSeed pkRoot =
        some pk ∧
      pk.pkRoot.size ≠ 16 := by
  refine ⟨ByteArray.empty, ByteArray.empty,
    ({ pkSeed := ByteArray.empty, pkRoot := ByteArray.empty } : PublicKey),
    ?_, ?_⟩
  · exact parsePublicKey_c13 ByteArray.empty ByteArray.empty
  · simp [ByteArray.size]

/-- **XMSS `hauth`.**  The `h`-th auth-path sibling of climb layer `layer`
(`layer < 2`, `h < 11`) is the 16-byte hash at sig byte-offset
`1952 + 868*layer + 692 + 16*h`. -/
theorem parseSignatureC13_layer_authPath_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {layer : Nat} (hlayer : layer < 2)
    {lsig : XmssLayerSig} (hlsig : s.layers[layer]? = some lsig)
    {h : Nat} (hh : h < 11) :
    lsig.authPath[h]? = some (read16 sig (1952 + 868 * layer + 692 + 16 * h)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ hlayer] at hlsig
  injection hlsig with hlsig
  subst hlsig
  exact getElem?_map_range _ hh

/-- **XMSS WOTS chain.**  The `k`-th WOTS chain seed of climb layer `layer`
(`layer < 2`, `k < 43`) is the 16-byte hash at signature byte-offset
`1952 + 868*layer + 16*k`. -/
theorem parseSignatureC13_layer_wots_chain_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {layer : Nat} (hlayer : layer < 2)
    {lsig : XmssLayerSig} (hlsig : s.layers[layer]? = some lsig)
    {k : Nat} (hk : k < 43) :
    lsig.wots.chains[k]? =
      some (read16 sig (1952 + 868 * layer + 16 * k)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ hlayer] at hlsig
  injection hlsig with hlsig
  subst hlsig
  exact getElem?_map_range _ hk

/-- **XMSS WOTS+C count.**  The parsed WOTS count for climb layer `layer`
(`layer < 2`) is the big-endian uint32 stored in the high four bytes at
signature byte-offset `1952 + 868*layer + 688`. -/
theorem parseSignatureC13_layer_wots_count
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {layer : Nat} (hlayer : layer < 2)
    {lsig : XmssLayerSig} (hlsig : s.layers[layer]? = some lsig) :
    lsig.wots.count =
      (List.range 4).foldl
        (fun acc j =>
          acc * 256 + ((sig[1952 + 868 * layer + 688 + j]?).getD 0).toNat) 0 := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ hlayer] at hlsig
  injection hlsig with hlsig
  subst hlsig
  rfl

/-- **FORS `hauth`.**  The `h`-th auth-path sibling of FORS tree `t`
(`t < 6`, `h < 19`) is the 16-byte hash at sig byte-offset
`128 + 304*t + 16*h`. -/
theorem parseSignatureC13_fors_authPath_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {t : Nat} (ht : t < 6)
    {tAuth : List Bytes} (htAuth : s.fors.authPath[t]? = some tAuth)
    {h : Nat} (hh : h < 19) :
    tAuth[h]? = some (read16 sig (128 + 304 * t + 16 * h)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ ht] at htAuth
  injection htAuth with htAuth
  subst htAuth
  exact getElem?_map_range _ hh

/-- `getD` form of `parseSignatureC13_fors_authPath_getElem?`, matching the
normal-root spec expression `(fors.authPath[i]?).getD []`. -/
theorem parseSignatureC13_fors_authPath_getD_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {t : Nat} (ht : t < 6)
    {h : Nat} (hh : h < 19) :
    (((s.fors.authPath[t]?).getD [])[h]?)
      = some (read16 sig (128 + 304 * t + 16 * h)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  rw [getElem?_map_range _ ht]
  exact getElem?_map_range _ hh

/-- **FORS secret-key word.**  The `i`-th FORS secret-key preimage
(`i < 7`, including the forced-zero seventh tree) is the 16-byte hash at
signature byte-offset `16 + 16*i`. -/
theorem parseSignatureC13_fors_sk_getElem?
    {v : Variant} {sig : Bytes} {s : Signature}
    (hparse : parseSignatureC13 v sig = some s)
    {i : Nat} (hi : i < 7) :
    s.fors.sk[i]? = some (read16 sig (16 + 16 * i)) := by
  have hsz : sig.size = v.sigBytes := parseSignatureC13_size hparse
  unfold parseSignatureC13 at hparse
  simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hparse
  subst hparse
  exact getElem?_map_range _ hi

/-! ### H_msg

The contract computes
`digest = keccak256(seed ‖ root ‖ R ‖ message ‖ 0xFF…FB)` (5 words, 0xA0 bytes),
then:
  * `htIdx   = (digest >> 133) & (2^22 - 1)`
  * for FORS tree `i` (0..6): `idx_i = (digest >> (19*i)) & (2^19 - 1)`.

`R`, `seed`, `root` are masked to their high 16 bytes; `message` is a full word. -/

/-- The H_msg trailing domain-separation word `0xFF…FF` (32 bytes of 0xFF,
i.e. 2^256 - 1) as written by `mstore(0x80, 0xFF…FF)` in the contract. -/
def hMsgPad : Word :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

def hMsgC13 (v : Variant) (pk : PublicKey) (R message : Bytes) : HMsg :=
  let digest :=
    keccakWords
      [ wordOfHash16 pk.pkSeed
      , wordOfHash16 pk.pkRoot
      , wordOfHash16 R
      , baToNatBE message % wordMod
      , hMsgPad ]
  let forsIndex := (List.range 7).map (fun i => (digest >>> (19 * i)) % (2 ^ 19))
  let hyperIndex := (digest >>> 133) % (2 ^ 22)
  { forsIndex := forsIndex, hyperIndex := hyperIndex }

theorem hMsgC13_forsIndex_six (pk : PublicKey) (R message : Bytes) :
    (hMsgC13 c13 pk R message).forsIndex[6]? =
      some ((keccakWords
        [ wordOfHash16 pk.pkSeed
        , wordOfHash16 pk.pkRoot
        , wordOfHash16 R
        , baToNatBE message % wordMod
        , hMsgPad ] >>> 114) % (2 ^ 19)) := by
  unfold hMsgC13
  exact getElem?_map_range _ (by decide : 6 < 7)

/-- `getD` form of the concrete C13 `H_msg` FORS index for any of the seven
19-bit slices. -/
theorem hMsgC13_forsIndex_getD_eq
    (pk : PublicKey) (R message : Bytes) {j : Nat} (hj : j < 7) :
    ((hMsgC13 c13 pk R message).forsIndex[j]?).getD 0 =
      (keccakWords
        [ wordOfHash16 pk.pkSeed
        , wordOfHash16 pk.pkRoot
        , wordOfHash16 R
        , baToNatBE message % wordMod
        , hMsgPad ] >>> (19 * j)) % (2 ^ 19) := by
  unfold hMsgC13
  have h := getElem?_map_range
    (fun i => (keccakWords [wordOfHash16 pk.pkSeed, wordOfHash16 pk.pkRoot,
        wordOfHash16 R, baToNatBE message % wordMod, hMsgPad] >>> (19 * i)) % (2 ^ 19))
    hj
  simpa using congrArg (fun o => o.getD 0) h

/-- Every FORS index extracted by the concrete C13 `H_msg` reconstruction is
19-bit.  This is the spec-side bound needed by concrete FORS leaf address
assembly. -/
theorem hMsgC13_forsIndex_getD_lt
    (pk : PublicKey) (R message : Bytes) {j : Nat} (hj : j < 7) :
    ((hMsgC13 c13 pk R message).forsIndex[j]?).getD 0 < 2 ^ 19 := by
  unfold hMsgC13
  rw [getElem?_map_range _ hj]
  exact Nat.mod_lt _ (by decide : 0 < 2 ^ 19)

/-- The concrete C13 hypertree index reconstructed from `H_msg` is 22-bit. -/
theorem hMsgC13_hyperIndex_lt (pk : PublicKey) (R message : Bytes) :
    (hMsgC13 c13 pk R message).hyperIndex < 2 ^ 22 := by
  unfold hMsgC13
  exact Nat.mod_lt _ (by decide : 0 < 2 ^ 22)

/-- The first C13 XMSS tree index derived from `hyperIndex` is 11-bit. -/
theorem hMsgC13_hyperIndex_div_2048_lt (pk : PublicKey) (R message : Bytes) :
    (hMsgC13 c13 pk R message).hyperIndex / 2048 < 2048 := by
  have h := hMsgC13_hyperIndex_lt pk R message
  omega

/-- FIPS 205 field split of the C13 hypertree index: the bottom-subtree index
(`tree` ADRS field).  Matches the model's `shr(11, htIdx)`. -/
def idxTree0C13 (digest : HMsg) : Nat := digest.hyperIndex >>> 11

/-- FIPS 205 field split of the C13 hypertree index: the bottom-leaf index
(`keypair` ADRS field).  Matches the model's `and(htIdx, 0x7FF)`. -/
def idxLeaf0C13 (digest : HMsg) : Nat := digest.hyperIndex &&& 0x7FF

/-- The C13 FORS tree digit is 11-bit (22-bit hypertree index, top half). -/
theorem idxTree0C13_lt (pk : PublicKey) (R message : Bytes) :
    idxTree0C13 (hMsgC13 c13 pk R message) < 2 ^ 11 := by
  unfold idxTree0C13
  have h := hMsgC13_hyperIndex_lt pk R message
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- The C13 FORS keypair digit is 11-bit unconditionally (masked). -/
theorem idxLeaf0C13_lt (digest : HMsg) : idxLeaf0C13 digest < 2 ^ 11 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

/-! ### FORS+C reconstruction

For each of the K=7 FORS trees:
  * trees i=0..5 are "normal": leaf = `th(seed, FORS_TREE leaf adrs, sk_i)`,
    then climb A=19 auth levels with branchless Merkle swap;
  * tree i=6 is forced-zero: `node_6 = th(seed, FORS_TREE adrs (h=0,idx=0), sk_6)`.
Then compress: `forsPk = th(seed, FORS_ROOTS adrs, node_0..node_6)`.

FORS leaf ADRS (type=3): `or(forsBase, or(shl(19, i), idx))` where
`forsBase = or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))`.  The
auth-path ADRS supplies `shl(32, h+1)` (height) and
`or(shl(18-h, i), parentIdx)` (tree index folding the k=7 FORS trees into
one 19-bit `word3` per FIPS 205 Alg 17).  layer=0 (top of hypertree),
tree=idxTree0, kp=idxLeaf0. -/

def adrsForsBase (idxTree0 idxLeaf0 : Nat) : Word :=
  (idxTree0 <<< 128) ||| (3 <<< 96) ||| (idxLeaf0 <<< 64)

def adrsForsLeaf (idxTree0 idxLeaf0 i treeIdx : Nat) : Word :=
  adrsForsBase idxTree0 idxLeaf0 ||| (i <<< 19) ||| treeIdx

def adrsForsNode (idxTree0 idxLeaf0 i h parentIdx : Nat) : Word :=
  adrsForsBase idxTree0 idxLeaf0
    ||| ((h + 1) <<< 32)
    ||| (i <<< (18 - h))
    ||| parentIdx

def adrsForsRoots (idxTree0 idxLeaf0 : Nat) : Word :=
  (idxTree0 <<< 128) ||| (4 <<< 96) ||| (idxLeaf0 <<< 64)

/-- Central factoring lemma: every FORS leaf address is built from the base.
    This replaces the previous 20+ adrsForsLeaf_*_eq + manual bit-mask lemmas. -/
theorem adrsForsLeaf_eq_of_forsBase
    (idxTree0 idxLeaf0 i treeIdx : Nat) :
    adrsForsLeaf idxTree0 idxLeaf0 i treeIdx
      = adrsForsBase idxTree0 idxLeaf0 ||| (i <<< 19) ||| treeIdx := by
  rfl

/-- C13 FORS-roots compression address, named with the digest so bridge lemmas
can track the FIPS-hardened address dependency at the spec boundary.  In the
current C13 executable model this is the constant `FORS_ROOTS` word. -/
def adrsForsRootsC13 (digest : HMsg) : Word :=
  adrsForsRoots (idxTree0C13 digest) (idxLeaf0C13 digest)

/-- `adrsForsBase` is a bounded 192-bit word (well below 2^256) when
`idxTree0 < 2^64` and `idxLeaf0 < 2^32` (the maximum the FIPS 205 §11.2.2
32-byte ADRS ever needs: 12-byte tree field + 4-byte kp).  This is the
*only* place the bit-disjointness reasoning for the `adrsForsBase` summand
lives; the leaf / node corollaries call it.  Returning `< 2^192` (not the
more permissive `< 2^256`) leaves room for the leaf / node OR to chain
`Nat.bitwise_lt_two_pow` without re-introducing the bit-disjointness
reasoning at every call site. -/
theorem adrsForsBase_lt_of_bounds
    {idxTree0 idxLeaf0 : Nat}
    (hT : idxTree0 < 2 ^ 64) (hL : idxLeaf0 < 2 ^ 32) :
    adrsForsBase idxTree0 idxLeaf0 < 2 ^ 192 := by
  unfold adrsForsBase
  -- adrsForsBase = (idxTree0 <<< 128) ||| (3 <<< 96) ||| (idxLeaf0 <<< 64).
  -- First OR: (idxTree0 <<< 128) ||| (3 <<< 96) < 2^192 (both summands < 2^192).
  have hShiftT : (idxTree0 : Nat) <<< 128 < 2 ^ 192 := by
    rw [Nat.shiftLeft_eq]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hT (by decide : (0:ℕ) < 2^128))
      (by simpa [Nat.pow_add] using Nat.le_refl _)
  have h3 : (3 : Nat) <<< 96 < 2 ^ 192 := by
    rw [Nat.shiftLeft_eq]; decide
  have h1 : (idxTree0 : Nat) <<< 128 ||| (3 <<< 96) < 2 ^ 192 :=
    Nat.bitwise_lt_two_pow hShiftT h3 (f := or)
  have hShiftL : (idxLeaf0 : Nat) <<< 64 < 2 ^ 96 := by
    rw [Nat.shiftLeft_eq]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hL (by decide : (0:ℕ) < 2^64))
      (by simpa [Nat.pow_add] using Nat.le_refl _)
  have h2 : (idxLeaf0 : Nat) <<< 64 < 2 ^ 192 := lt_trans hShiftL (by decide : 2^96 < 2^192)
  exact Nat.bitwise_lt_two_pow h1 h2 (f := or)

/-- The concrete FORS leaf address word is a bounded EVM word for the six normal
FORS roots when the decoded tree index is 19-bit.  Bounds on `idxTree0` /
`idxLeaf0` are passed as hypotheses; specialized corollaries (e.g. for the
C13 hypertree-leaf case) live next to `hMsgC13`. -/
theorem adrsForsLeaf_lt_of_normal_idx_lt
    {idxTree0 idxLeaf0 i idx : Nat}
    (hT : idxTree0 < 2 ^ 64) (hL : idxLeaf0 < 2 ^ 32)
    (hi : i < 6) (hidx : idx < 2 ^ 19) :
    adrsForsLeaf idxTree0 idxLeaf0 i idx < 2 ^ 256 := by
  unfold adrsForsLeaf
  -- adrsForsLeaf = adrsForsBase ||| (i <<< 19) ||| idx.
  have hBase : adrsForsBase idxTree0 idxLeaf0 < 2 ^ 192 := adrsForsBase_lt_of_bounds hT hL
  have hShiftI : (i : Nat) <<< 19 < 2 ^ 192 := by
    rw [Nat.shiftLeft_eq]
    calc i * 2 ^ 19 ≤ 5 * 2 ^ 19 := Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hi)
      _ < 2 ^ 192 := by decide
  have h1 : adrsForsBase idxTree0 idxLeaf0 ||| (i <<< 19) < 2 ^ 192 :=
    Nat.bitwise_lt_two_pow hBase hShiftI (f := or)
  have hShiftIdx : idx < 2 ^ 192 := lt_trans hidx (by decide : 2^19 < 2^192)
  have h2 : (adrsForsBase idxTree0 idxLeaf0 ||| (i <<< 19)) ||| idx < 2 ^ 192 :=
    Nat.bitwise_lt_two_pow h1 hShiftIdx (f := or)
  exact lt_trans h2 (by decide : 2^192 < 2^256)

/-- Specialization of `adrsForsLeaf_lt_of_normal_idx_lt` to the normal-root
indices inside concrete C13 `H_msg`.  The FIPS digits derived from the C13
hypertree index are 11-bit, well inside the `2^64`/`2^32` field bounds. -/
theorem adrsForsLeaf_hMsgC13_normal_lt
    (pk : PublicKey) (R message : Bytes) {j : Nat} (hj : j < 6) :
    adrsForsLeaf (idxTree0C13 (hMsgC13 c13 pk R message))
        (idxLeaf0C13 (hMsgC13 c13 pk R message))
        j (((hMsgC13 c13 pk R message).forsIndex[j]?).getD 0) < 2 ^ 256 :=
  adrsForsLeaf_lt_of_normal_idx_lt
    (lt_trans (idxTree0C13_lt pk R message) (by decide : (2:Nat) ^ 11 < 2 ^ 64))
    (lt_trans (idxLeaf0C13_lt _) (by decide : (2:Nat) ^ 11 < 2 ^ 32))
    hj (hMsgC13_forsIndex_getD_lt pk R message (lt_trans hj (by decide : 6 < 7)))

/-- Climb one FORS auth path (A=19) using fuel-bounded recursion.  Mirrors the
contract's branchless swap: when `pathIdx` is even, `node` is the left child;
when odd, the right child. -/
def forsClimb (seed i : Word) (idxTree0 idxLeaf0 : Nat) (fuel : Nat) (h : Nat)
    (pathIdx : Nat) (node : Word) (auth : List Bytes) : Word :=
  match fuel with
  | 0 => node
  | fuel + 1 =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := pathIdx / 2
    let adrs := adrsForsNode idxTree0 idxLeaf0 i h parentIdx
    let node' :=
      if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    forsClimb seed i idxTree0 idxLeaf0 fuel (h + 1) parentIdx node' auth

def forsPkFromSigC13 (v : Variant) (pk : PublicKey) (digest : HMsg)
    (fors : ForsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  -- normal trees i = 0..5
  let roots := (List.range 6).map (fun i =>
    let treeIdx := (digest.forsIndex[i]?).getD 0
    let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
    let leaf := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) i treeIdx, sk])
    forsClimb seed i (idxTree0C13 digest) (idxLeaf0C13 digest) 19 0 treeIdx leaf ((fors.authPath[i]?).getD []))
  -- forced-zero tree i = 6
  let sk6 := wordOfHash16 ((fors.sk[6]?).getD ⟨#[]⟩)
  let root6 := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) 6 0, sk6])
  let allRoots := roots ++ [root6]
  let forsPk := maskN (keccakWords (seed :: adrsForsRootsC13 digest :: allRoots))
  some (hash16OfWord forsPk)

/-- The six normal FORS tree roots reconstructed by C13 before adding the
forced-zero tree.  Named so verifier lemmas can target the same spec word list
without replaying the `forsPkFromSigC13` body. -/
def forsNormalRootsC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : List Word :=
  let seed := wordOfHash16 pk.pkSeed
  (List.range 6).map (fun i =>
    let treeIdx := (digest.forsIndex[i]?).getD 0
    let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
    let leaf := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) i treeIdx, sk])
    forsClimb seed i (idxTree0C13 digest) (idxLeaf0C13 digest) 19 0 treeIdx leaf ((fors.authPath[i]?).getD []))

/-- The forced-zero seventh FORS root used by C13. -/
def forsForcedRootC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : Word :=
  let seed := wordOfHash16 pk.pkSeed
  let sk6 := wordOfHash16 ((fors.sk[6]?).getD ⟨#[]⟩)
  maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) 6 0, sk6])

/-- All seven FORS roots in the exact order consumed by C13's FORS public-key
compression. -/
def forsAllRootsC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : List Word :=
  forsNormalRootsC13 pk digest fors ++ [forsForcedRootC13 pk digest fors]

/-- The masked C13 FORS public-key compression word. -/
def forsPkWordC13 (pk : PublicKey) (digest : HMsg) (fors : ForsSig) : Word :=
  let seed := wordOfHash16 pk.pkSeed
  maskN (keccakWords (seed :: adrsForsRootsC13 digest :: forsAllRootsC13 pk digest fors))

/-- The named FORS root list has the expected C13 length. -/
theorem forsAllRootsC13_length (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    (forsAllRootsC13 pk digest fors).length = 7 := by
  unfold forsAllRootsC13 forsNormalRootsC13
  simp

/-- Indexing the six normal C13 FORS roots exposes the same per-tree expression
used by `forsPkFromSigC13`. -/
theorem forsNormalRootsC13_getElem?
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsNormalRootsC13 pk digest fors)[i]? =
      some
        (let seed := wordOfHash16 pk.pkSeed
         let treeIdx := (digest.forsIndex[i]?).getD 0
         let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
         let leaf := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) i treeIdx, sk])
         forsClimb seed i (idxTree0C13 digest) (idxLeaf0C13 digest) 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  unfold forsNormalRootsC13
  exact getElem?_map_range _ hi

/-- `getElem` form of `forsNormalRootsC13_getElem?`. -/
theorem forsNormalRootsC13_getElem
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsNormalRootsC13 pk digest fors)[i]'(by
        unfold forsNormalRootsC13
        simp [hi]) =
      (let seed := wordOfHash16 pk.pkSeed
       let treeIdx := (digest.forsIndex[i]?).getD 0
       let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
       let leaf := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) i treeIdx, sk])
       forsClimb seed i (idxTree0C13 digest) (idxLeaf0C13 digest) 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  unfold forsNormalRootsC13
  exact getElem_map_range _ hi

/-- The full seven-root C13 FORS list agrees with the normal-root expression on
indices `0..5`. -/
theorem forsAllRootsC13_getElem?_normal
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsAllRootsC13 pk digest fors)[i]? =
      some
        (let seed := wordOfHash16 pk.pkSeed
         let treeIdx := (digest.forsIndex[i]?).getD 0
         let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
         let leaf := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) i treeIdx, sk])
         forsClimb seed i (idxTree0C13 digest) (idxLeaf0C13 digest) 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  unfold forsAllRootsC13
  rw [List.getElem?_append_left]
  · exact forsNormalRootsC13_getElem? pk digest fors hi
  · unfold forsNormalRootsC13
    simp [hi]

/-- The seventh C13 FORS root is exactly the forced-zero root. -/
theorem forsAllRootsC13_getElem?_forced
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    (forsAllRootsC13 pk digest fors)[6]? = some (forsForcedRootC13 pk digest fors) := by
  unfold forsAllRootsC13 forsNormalRootsC13
  simp

/-- `getElem` form of `forsAllRootsC13_getElem?_normal`. -/
theorem forsAllRootsC13_getElem_normal
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    {i : Nat} (hi : i < 6) :
    (forsAllRootsC13 pk digest fors)[i]'(by
        rw [forsAllRootsC13_length]
        omega) =
      (let seed := wordOfHash16 pk.pkSeed
       let treeIdx := (digest.forsIndex[i]?).getD 0
       let sk := wordOfHash16 ((fors.sk[i]?).getD ⟨#[]⟩)
       let leaf := maskN (keccakWords [seed, adrsForsLeaf (idxTree0C13 digest) (idxLeaf0C13 digest) i treeIdx, sk])
       forsClimb seed i (idxTree0C13 digest) (idxLeaf0C13 digest) 19 0 treeIdx leaf ((fors.authPath[i]?).getD [])) := by
  have hidx : i < (forsAllRootsC13 pk digest fors).length := by
    rw [forsAllRootsC13_length]
    omega
  have h :=
    forsAllRootsC13_getElem?_normal (pk := pk) (digest := digest) (fors := fors) hi
  simpa [List.getElem?_eq_getElem hidx] using h

/-- `getElem` form of `forsAllRootsC13_getElem?_forced`. -/
theorem forsAllRootsC13_getElem_forced
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    (forsAllRootsC13 pk digest fors)[6]'(by
        rw [forsAllRootsC13_length]
        omega) = forsForcedRootC13 pk digest fors := by
  have hidx : 6 < (forsAllRootsC13 pk digest fors).length := by
    rw [forsAllRootsC13_length]
    omega
  have h := forsAllRootsC13_getElem?_forced pk digest fors
  simpa [List.getElem?_eq_getElem hidx] using h

/-- `forsPkFromSigC13` is exactly the named seven-root compression word, encoded
back to 16 bytes.  This is purely a spec-side factoring lemma for the C13 accept
path; it does not touch any executable model or bridge axiom. -/
theorem forsPkFromSigC13_eq_named
    (v : Variant) (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    forsPkFromSigC13 v pk digest fors
      = some (hash16OfWord (forsPkWordC13 pk digest fors)) := by
  unfold forsPkFromSigC13 forsPkWordC13 forsAllRootsC13
    forsNormalRootsC13 forsForcedRootC13
  rfl

/-- If C13 FORS reconstruction returns a byte string, it is exactly the high
16-byte read of the named FORS compression word. -/
theorem forsPkFromSigC13_some_eq_hash16_named
    {v : Variant} {pk : PublicKey} {digest : HMsg} {fors : ForsSig}
    {forsPk : Bytes}
    (h : forsPkFromSigC13 v pk digest fors = some forsPk) :
    forsPk = hash16OfWord (forsPkWordC13 pk digest fors) := by
  rw [forsPkFromSigC13_eq_named] at h
  injection h with hEq
  exact hEq.symm

/-- Any successful C13 FORS public-key reconstruction returns a 16-byte value. -/
theorem forsPkFromSigC13_size
    {v : Variant} {pk : PublicKey} {digest : HMsg} {fors : ForsSig}
    {forsPk : Bytes}
    (h : forsPkFromSigC13 v pk digest fors = some forsPk) :
    forsPk.size = 16 := by
  rw [forsPkFromSigC13_eq_named] at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_size _

/-- Any successful C13 FORS public-key reconstruction returns a canonical
`hash16OfWord` output. -/
theorem forsPkFromSigC13_canonical
    {v : Variant} {pk : PublicKey} {digest : HMsg} {fors : ForsSig}
    {forsPk : Bytes}
    (h : forsPkFromSigC13 v pk digest fors = some forsPk) :
    CanonicalHash16 forsPk := by
  exact ⟨forsPkWordC13 pk digest fors, forsPkFromSigC13_some_eq_hash16_named h⟩

/-- For C13, the spec-side forced-zero check means the seventh FORS index is
present and equal to zero. -/
theorem forcedZeroOk_c13_forsIndex_six
    (digest : HMsg) (h : forcedZeroOk c13 digest = true) :
    digest.forsIndex[6]? = some 0 := by
  unfold forcedZeroOk at h
  simpa [c13] using h

/-! ### WOTS+ chains and PK compression

Per layer, with `idxLeaf`, `idxTree`, base node `currentNode`, `count`:
  * `d = keccak256(seed ‖ WOTS_HASH base ADRS ‖ currentNode ‖ count)` (4 words),
    where WOTS_HASH base ADRS = `or(shl(224,layer), or(shl(128,idxTree), shl(64,idxLeaf)))`
    (type=0 implicit, word2=word3=0);
  * digit_i = `(d >> (3*i)) & 7`, steps_i = `7 - digit_i`;
  * chain i: start from `chains[i]`, apply `steps_i` hashes with ADRS
    `or(chainBase, add(digit, step))`, `chainBase = or(wotsAdrs, shl(32, i))`;
  * WOTS_PK = `th(seed, WOTS_PK adrs, chain_0..chain_42)`,
    WOTS_PK adrs = `or(shl(224,layer), or(shl(128,idxTree), or(shl(96,1), shl(64,idxLeaf))))`.

`d` is *not* masked in the contract (full 256-bit word used for digit extraction).
The grinding check requires `sum(digit_i) == 208`. -/

def adrsWotsHashBase (layer idxTree idxLeaf : Nat) : Word :=
  (layer <<< 224) ||| (idxTree <<< 128) ||| (idxLeaf <<< 64)
def adrsWotsPk (layer idxTree idxLeaf : Nat) : Word :=
  (layer <<< 224) ||| (idxTree <<< 128) ||| (1 <<< 96) ||| (idxLeaf <<< 64)

/-- The WOTS message digest word `d` for a layer. -/
def wotsDigest (seed : Word) (layer idxTree idxLeaf count : Nat)
    (node : Word) : Word :=
  keccakWords [seed, adrsWotsHashBase layer idxTree idxLeaf, node, count]

/-- Apply `steps` chain hashes starting from `val`, beginning at chain position
`digit` (so the `step`-th hash uses ADRS word3 = `digit + step`). -/
def chainHash (seed chainBase : Word) (digit : Nat) (fuel step : Nat)
    (val : Word) : Word :=
  match fuel with
  | 0 => val
  | fuel + 1 =>
    let val' := maskN (keccakWords [seed, chainBase ||| (digit + step), val])
    chainHash seed chainBase digit fuel (step + 1) val'

def wotsDigitSum (d : Word) : Nat :=
  (List.range 43).foldl (fun acc i => acc + ((d >>> (3 * i)) % 8)) 0

/-- The reconstructed WOTS public key word for one layer.  `treeIdx`/`leafIdx`
follow the spec's per-layer naming (`nextTree`/`idxLeaf`). -/
def wotsPkWord (seed : Word) (layer treeIdx leafIdx : Nat)
    (node : Word) (wots : WotsSig) : Word :=
  let d := wotsDigest seed layer treeIdx leafIdx wots.count node
  let wotsAdrs := adrsWotsHashBase layer treeIdx leafIdx
  let chainsEnd := (List.range 43).map (fun i =>
    let digit := (d >>> (3 * i)) % 8
    let steps := 7 - digit
    let val := wordOfHash16 ((wots.chains[i]?).getD ⟨#[]⟩)
    let chainBase := wotsAdrs ||| (i <<< 32)
    chainHash seed chainBase digit steps 0 val)
  maskN (keccakWords (seed :: adrsWotsPk layer treeIdx leafIdx :: chainsEnd))

/-- C13 WOTS public-key reconstruction at a concrete hypertree layer.  The
contract threads the loop variable into the WOTS address, so executable layer
proofs must keep this parameter visible. -/
def wotsPkFromSigC13AtLayer (layer : Nat) (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let nodeW := wordOfHash16 node
  let pkW := wotsPkWord seed layer treeIdx leafIdx nodeW wots
  some (hash16OfWord pkW)

/-- C13 grinding predicate at a concrete hypertree layer. -/
def wotsGrindingOkC13AtLayer (layer : Nat) (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Bool :=
  let seed := wordOfHash16 pk.pkSeed
  let nodeW := wordOfHash16 node
  let d := wotsDigest seed layer treeIdx leafIdx wots.count nodeW
  wotsDigitSum d == 208

/-- The contract-facing `Primitives` API does not carry the hypertree layer, so
the current byte spec exposes the layer-0 C13 WOTS reconstruction.  Layer-aware
helpers above are the executable target for concrete loop proofs. -/
def wotsPkFromSigC13 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Option Bytes :=
  wotsPkFromSigC13AtLayer 0 v pk treeIdx leafIdx node wots

/-- Contract-facing layer-0 C13 grinding predicate; see
`wotsGrindingOkC13AtLayer` for the executable layer-indexed form. -/
def wotsGrindingOkC13 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Bool :=
  wotsGrindingOkC13AtLayer 0 v pk treeIdx leafIdx node wots

/-! ### XMSS Merkle auth path (subtree height 11)

TREE ADRS: `or(shl(224,layer), or(shl(128,idxTree), shl(96,2)))`, supplying
`shl(32, h+1)` (height) and `parentIdx` (index).  Branchless swap as in FORS. -/

def adrsXmssTree (layer idxTree : Nat) : Word :=
  (layer <<< 224) ||| (idxTree <<< 128) ||| (2 <<< 96)

def xmssClimb (seed treeAdrs : Word) (fuel : Nat) (h : Nat) (mIdx : Nat)
    (node : Word) (auth : List Bytes) : Word :=
  match fuel with
  | 0 => node
  | fuel + 1 =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := mIdx / 2
    let adrs := treeAdrs ||| ((h + 1) <<< 32) ||| parentIdx
    let node' :=
      if mIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    xmssClimb seed treeAdrs fuel (h + 1) parentIdx node' auth

/-- C13 XMSS root reconstruction at a concrete hypertree layer. -/
def xmssRootFromSigC13AtLayer (layer : Nat) (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (wotsPk : Bytes) (auth : List Bytes) : Option Bytes :=
  let seed := wordOfHash16 pk.pkSeed
  let treeAdrs := adrsXmssTree layer treeIdx
  let start := wordOfHash16 wotsPk
  let root := xmssClimb seed treeAdrs 11 0 leafIdx start auth
  some (hash16OfWord root)

/-- Contract-facing layer-0 C13 XMSS reconstruction; see
`xmssRootFromSigC13AtLayer` for the executable layer-indexed form. -/
def xmssRootFromSigC13 (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (wotsPk : Bytes) (auth : List Bytes) : Option Bytes :=
  xmssRootFromSigC13AtLayer 0 v pk treeIdx leafIdx wotsPk auth

theorem wotsPkFromSigC13AtLayer_zero (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) :
    wotsPkFromSigC13AtLayer 0 v pk treeIdx leafIdx node wots =
      wotsPkFromSigC13 v pk treeIdx leafIdx node wots := rfl

theorem wotsGrindingOkC13AtLayer_zero (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) :
    wotsGrindingOkC13AtLayer 0 v pk treeIdx leafIdx node wots =
      wotsGrindingOkC13 v pk treeIdx leafIdx node wots := rfl

theorem xmssRootFromSigC13AtLayer_zero (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (wotsPk : Bytes) (auth : List Bytes) :
    xmssRootFromSigC13AtLayer 0 v pk treeIdx leafIdx wotsPk auth =
      xmssRootFromSigC13 v pk treeIdx leafIdx wotsPk auth := rfl

/-- Any successful layer-aware C13 WOTS public-key reconstruction returns a
16-byte value. -/
theorem wotsPkFromSigC13AtLayer_size
    {layer : Nat} {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat}
    {node : Bytes} {wots : WotsSig} {wotsPk : Bytes}
    (h : wotsPkFromSigC13AtLayer layer v pk treeIdx leafIdx node wots = some wotsPk) :
    wotsPk.size = 16 := by
  unfold wotsPkFromSigC13AtLayer at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_size _

/-- Any successful C13 WOTS public-key reconstruction returns a 16-byte value. -/
theorem wotsPkFromSigC13_size
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {node : Bytes}
    {wots : WotsSig} {wotsPk : Bytes}
    (h : wotsPkFromSigC13 v pk treeIdx leafIdx node wots = some wotsPk) :
    wotsPk.size = 16 :=
  wotsPkFromSigC13AtLayer_size h

/-- Any successful layer-aware C13 WOTS public-key reconstruction returns a
canonical `hash16OfWord` output. -/
theorem wotsPkFromSigC13AtLayer_canonical
    {layer : Nat} {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat}
    {node : Bytes} {wots : WotsSig} {wotsPk : Bytes}
    (h : wotsPkFromSigC13AtLayer layer v pk treeIdx leafIdx node wots = some wotsPk) :
    CanonicalHash16 wotsPk := by
  unfold wotsPkFromSigC13AtLayer at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_canonical _

/-- Any successful C13 WOTS public-key reconstruction returns a canonical
`hash16OfWord` output. -/
theorem wotsPkFromSigC13_canonical
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {node : Bytes}
    {wots : WotsSig} {wotsPk : Bytes}
    (h : wotsPkFromSigC13 v pk treeIdx leafIdx node wots = some wotsPk) :
    CanonicalHash16 wotsPk :=
  wotsPkFromSigC13AtLayer_canonical h

/-- Any successful layer-aware C13 XMSS root reconstruction returns a 16-byte
value. -/
theorem xmssRootFromSigC13AtLayer_size
    {layer : Nat} {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat}
    {wotsPk : Bytes} {auth : List Bytes} {root : Bytes}
    (h : xmssRootFromSigC13AtLayer layer v pk treeIdx leafIdx wotsPk auth = some root) :
    root.size = 16 := by
  unfold xmssRootFromSigC13AtLayer at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_size _

/-- Any successful C13 XMSS root reconstruction returns a 16-byte value. -/
theorem xmssRootFromSigC13_size
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {wotsPk : Bytes}
    {auth : List Bytes} {root : Bytes}
    (h : xmssRootFromSigC13 v pk treeIdx leafIdx wotsPk auth = some root) :
    root.size = 16 :=
  xmssRootFromSigC13AtLayer_size h

/-- Any successful layer-aware C13 XMSS root reconstruction returns a canonical
`hash16OfWord` output. -/
theorem xmssRootFromSigC13AtLayer_canonical
    {layer : Nat} {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat}
    {wotsPk : Bytes} {auth : List Bytes} {root : Bytes}
    (h : xmssRootFromSigC13AtLayer layer v pk treeIdx leafIdx wotsPk auth = some root) :
    CanonicalHash16 root := by
  unfold xmssRootFromSigC13AtLayer at h
  injection h with hEq
  rw [← hEq]
  exact hash16OfWord_canonical _

/-- Any successful C13 XMSS root reconstruction returns a canonical
`hash16OfWord` output. -/
theorem xmssRootFromSigC13_canonical
    {v : Variant} {pk : PublicKey} {treeIdx leafIdx : Nat} {wotsPk : Bytes}
    {auth : List Bytes} {root : Bytes}
    (h : xmssRootFromSigC13 v pk treeIdx leafIdx wotsPk auth = some root) :
    CanonicalHash16 root :=
  xmssRootFromSigC13AtLayer_canonical h

/-- The concrete C13 `Primitives`, all six fields routed through `keccakWords`
(hence `KeccakEngine.keccak256` over the interpreter's big-endian word preimage).
No `sorry`, no new axioms. -/
def c13PrimitivesConcrete : Primitives :=
  { parseSignature  := parseSignatureC13
  , hMsg            := hMsgC13
  , forsPkFromSig   := forsPkFromSigC13
  , wotsPkFromSig   := wotsPkFromSigC13
  , wotsPkFromSigAtLayer := wotsPkFromSigC13AtLayer
  , wotsGrindingOk  := wotsGrindingOkC13
  , wotsGrindingOkAtLayer := wotsGrindingOkC13AtLayer
  , xmssRootFromSig := xmssRootFromSigC13
  , xmssRootFromSigAtLayer := xmssRootFromSigC13AtLayer }

/-- The C13 grinding predicate is exactly the 43 three-bit digit sum check
against target `208`.  This is the spec-side half of the executable
`digitSum`-guard bridge. -/
theorem wotsGrindingFailsC13_false_iff
    (pk : PublicKey) (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) :
    wotsGrindingFails c13PrimitivesConcrete c13 pk treeIdx leafIdx node wots = false ↔
      wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) 0 treeIdx leafIdx wots.count
          (wordOfHash16 node)) = 208 := by
  unfold wotsGrindingFails c13PrimitivesConcrete wotsGrindingOkC13
    wotsGrindingOkC13AtLayer c13
  by_cases h :
      wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) 0 treeIdx leafIdx wots.count
          (wordOfHash16 node)) = 208
  · simp [h]
  · simp [h]

/-- Forward form of `wotsGrindingFailsC13_false_iff`. -/
theorem wotsDigitSum_eq_of_wotsGrindingFailsC13_false
    {pk : PublicKey} {treeIdx leafIdx : Nat} {node : Bytes} {wots : WotsSig}
    (hGrinding :
      wotsGrindingFails c13PrimitivesConcrete c13 pk treeIdx leafIdx node wots = false) :
    wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) 0 treeIdx leafIdx wots.count
          (wordOfHash16 node)) = 208 :=
  (wotsGrindingFailsC13_false_iff pk treeIdx leafIdx node wots).mp hGrinding

/-- Layer-indexed C13 grinding failure is exactly failure of the executable
43-digit checksum target. -/
theorem wotsGrindingFailsC13AtLayer_true_iff
    (layer : Nat) (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node : Bytes) (wots : WotsSig) :
    wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk treeIdx leafIdx node wots = true ↔
      wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) layer treeIdx leafIdx wots.count
          (wordOfHash16 node)) ≠ 208 := by
  unfold wotsGrindingFailsAtLayer c13PrimitivesConcrete wotsGrindingOkC13AtLayer c13
  by_cases h :
      wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) layer treeIdx leafIdx wots.count
          (wordOfHash16 node)) = 208
  · simp [h]
  · simp [h]

/-- Forward form of `wotsGrindingFailsC13AtLayer_true_iff`. -/
theorem wotsDigitSum_ne_of_wotsGrindingFailsC13AtLayer_true
    {layer : Nat} {pk : PublicKey} {treeIdx leafIdx : Nat}
    {node : Bytes} {wots : WotsSig}
    (hGrinding :
      wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk
        treeIdx leafIdx node wots = true) :
    wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) layer treeIdx leafIdx wots.count
          (wordOfHash16 node)) ≠ 208 :=
  (wotsGrindingFailsC13AtLayer_true_iff layer pk treeIdx leafIdx node wots).mp hGrinding

/-- Forward form for the successful layer-indexed C13 grinding target. -/
theorem wotsDigitSum_eq_of_wotsGrindingFailsC13AtLayer_false
    {layer : Nat} {pk : PublicKey} {treeIdx leafIdx : Nat}
    {node : Bytes} {wots : WotsSig}
    (hGrinding :
      wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk
        treeIdx leafIdx node wots = false) :
    wotsDigitSum
        (wotsDigest (wordOfHash16 pk.pkSeed) layer treeIdx leafIdx wots.count
          (wordOfHash16 node)) = 208 := by
  by_contra hNe
  have hTrue :
      wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk
        treeIdx leafIdx node wots = true :=
    (wotsGrindingFailsC13AtLayer_true_iff layer pk treeIdx leafIdx node wots).mpr hNe
  rw [hGrinding] at hTrue
  cases hTrue

/-- If the C13 hypertree climb returns `.ok root`, then the returned root is
16 bytes, provided the starting FORS public key is 16 bytes. -/
theorem foldHypertreeAux_c13_ok_root_size
    (pk : PublicKey) (fuel layer idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig) {root : Bytes}
    (hNode : node.size = 16)
    (h : foldHypertreeAux c13PrimitivesConcrete c13 pk fuel layer idxTree node layers
        = .ok root) :
    root.size = 16 := by
  induction fuel generalizing layer idxTree node root with
  | zero =>
      unfold foldHypertreeAux at h
      injection h with hEq
      rw [← hEq]
      exact hNode
  | succ fuel ih =>
      unfold foldHypertreeAux at h
      by_cases hlt : layer < c13.d
      · simp only [hlt, ↓reduceIte] at h
        cases hLayer : layers[layer]? with
        | none => simp [hLayer] at h
        | some lsig =>
            simp only [hLayer] at h
            let idxLeaf := idxTree % 2 ^ c13.subtreeH
            let nextTree := idxTree / 2 ^ c13.subtreeH
            by_cases hgrind :
                wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk nextTree idxLeaf node lsig.wots
                  = true
            · simp [idxLeaf, nextTree, hgrind] at h
            · simp only [idxLeaf, nextTree, hgrind] at h
              cases hWots :
                  c13PrimitivesConcrete.wotsPkFromSigAtLayer layer c13 pk nextTree idxLeaf node lsig.wots
                  with
              | none =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSigAtLayer layer c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = none := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp [hWots'] at h
              | some wotsPk =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSigAtLayer layer c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = some wotsPk := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp only [hWots'] at h
                  cases hXmss :
                      c13PrimitivesConcrete.xmssRootFromSigAtLayer layer c13 pk nextTree idxLeaf
                        wotsPk lsig.authPath with
                  | none =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSigAtLayer layer c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = none := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp [hXmss'] at h
                  | some xmssRoot =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSigAtLayer layer c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = some xmssRoot := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp only [hXmss'] at h
                      have hx : xmssRoot.size = 16 := by
                        exact xmssRootFromSigC13AtLayer_size
                          (by simpa [c13PrimitivesConcrete] using hXmss')
                      exact ih (layer + 1) nextTree xmssRoot hx h
      · simp only [hlt, ↓reduceIte] at h
        injection h with hEq
        rw [← hEq]
        exact hNode

/-- C13 `foldHypertree` preserves 16-byte roots on successful `.ok` output. -/
theorem foldHypertree_c13_ok_root_size
    {pk : PublicKey} {digest : HMsg} {forsPk : Bytes} {layers : List XmssLayerSig}
    {root : Bytes}
    (hForsPk : forsPk.size = 16)
    (h : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    root.size = 16 :=
  foldHypertreeAux_c13_ok_root_size pk c13.d 0 digest.hyperIndex forsPk layers hForsPk h

/-- C13 `foldHypertree` returns a 16-byte root after successful C13 FORS
reconstruction. -/
theorem foldHypertree_c13_ok_root_size_of_fors
    {pk : PublicKey} {digest : HMsg} {fors : ForsSig} {forsPk root : Bytes}
    {layers : List XmssLayerSig}
    (hFors : c13PrimitivesConcrete.forsPkFromSig c13 pk digest fors = some forsPk)
    (hFold : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    root.size = 16 :=
  foldHypertree_c13_ok_root_size
    (forsPkFromSigC13_size (by simpa [c13PrimitivesConcrete] using hFors)) hFold

/-- Concrete C13 WOTS reconstruction is total.  The generic spec allows
primitive reconstruction to fail and return `.rejected`; the concrete C13
primitive never takes that branch. -/
theorem wotsPkFromSigC13_isSome
    (v : Variant) (pk : PublicKey) (treeIdx leafIdx : Nat) (node : Bytes)
    (wots : WotsSig) :
    (wotsPkFromSigC13 v pk treeIdx leafIdx node wots).isSome = true := by
  unfold wotsPkFromSigC13
  rfl

/-- Concrete C13 XMSS reconstruction is total. -/
theorem xmssRootFromSigC13_isSome
    (v : Variant) (pk : PublicKey) (treeIdx leafIdx : Nat) (wotsPk : Bytes)
    (auth : List Bytes) :
    (xmssRootFromSigC13 v pk treeIdx leafIdx wotsPk auth).isSome = true := by
  unfold xmssRootFromSigC13
  rfl

/-- A parsed C13 layer list has both concrete layer entries available to the
two-step hypertree fold. -/
private theorem c13_layers_getElem?_some_of_length
    (layers : List XmssLayerSig) (hLen : layers.length = c13.d) {idx : Nat}
    (hidx : idx < c13.d) :
    ∃ lsig, layers[idx]? = some lsig := by
  have hidx' : idx < layers.length := by
    rw [hLen]
    exact hidx
  exact ⟨layers[idx]'hidx', List.getElem?_eq_getElem hidx'⟩

/-- Concrete C13 `foldHypertreeAux` cannot hit `.rejected` when every layer
index that the C13 variant may inspect is present.  The only concrete early
failure branch left is `.reverted`, caused by a WOTS+C grinding miss. -/
theorem foldHypertreeAux_c13_ne_rejected_of_layers
    (pk : PublicKey) (fuel layer idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig)
    (hLayerSome : ∀ idx, idx < c13.d → ∃ lsig, layers[idx]? = some lsig) :
    foldHypertreeAux c13PrimitivesConcrete c13 pk fuel layer idxTree node layers
      ≠ .rejected := by
  induction fuel generalizing layer idxTree node with
  | zero =>
      intro h
      unfold foldHypertreeAux at h
      cases h
  | succ fuel ih =>
      intro h
      unfold foldHypertreeAux at h
      by_cases hlt : layer < c13.d
      · obtain ⟨lsig, hLayer⟩ := hLayerSome layer hlt
        simp only [hlt, ↓reduceIte, hLayer] at h
        let idxLeaf := idxTree % 2 ^ c13.subtreeH
        let nextTree := idxTree / 2 ^ c13.subtreeH
        by_cases hgrind :
            wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk nextTree idxLeaf node lsig.wots
              = true
        · simp [idxLeaf, nextTree, hgrind] at h
        · simp [idxLeaf, nextTree, hgrind] at h
          simp [c13PrimitivesConcrete, wotsPkFromSigC13, xmssRootFromSigC13] at h
          exact ih (layer + 1) nextTree _ h
      · simp [hlt] at h

/-- With the concrete C13 primitives and a two-layer parsed signature, the
hypertree fold cannot hit the abstract `.rejected` branch.  The remaining
outcomes are the real C13 outcomes: `.reverted` on a WOTS+C grinding failure, or
`.ok root` after both concrete layers complete. -/
theorem foldHypertree_c13_ne_rejected_of_layers_length
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig)
    (hLen : layers.length = c13.d) :
    foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers ≠ .rejected := by
  unfold foldHypertree
  exact
    foldHypertreeAux_c13_ne_rejected_of_layers pk c13.d 0 digest.hyperIndex forsPk
      layers (fun idx hidx => c13_layers_getElem?_some_of_length layers hLen hidx)

/-- Parsed C13 signatures instantiate the two-layer no-`.rejected` fold fact. -/
theorem foldHypertree_c13_ne_rejected_of_parse
    {sigBytes : Bytes} {sig : Signature}
    (hParse : parseSignatureC13 c13 sigBytes = some sig)
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes) :
    foldHypertree c13PrimitivesConcrete c13 pk digest forsPk sig.layers ≠ .rejected := by
  have hLen : sig.layers.length = c13.d := by
    have hsz : sigBytes.size = c13.sigBytes := parseSignatureC13_size hParse
    unfold parseSignatureC13 at hParse
    simp only [hsz, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hParse
    subst hParse
    simp [c13]
  exact foldHypertree_c13_ne_rejected_of_layers_length pk digest forsPk sig.layers hLen

/-- Data exposed by a successful concrete C13 two-layer hypertree fold.  This is
the pure spec-side decomposition needed by bridge proofs that must relate the
`.ok root` branch back to the two executable layer iterations. -/
structure FoldHypertreeC13OkTwoLayerData
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig) (specRoot : Bytes) where
  lsig0 : XmssLayerSig
  wotsPk0 : Bytes
  root0 : Bytes
  hLayer0 : layers[0]? = some lsig0
  hGrinding0 :
    wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk lsig0.wots = false
  hWots0 :
    c13PrimitivesConcrete.wotsPkFromSigAtLayer 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk lsig0.wots = some wotsPk0
  hXmss0 :
    c13PrimitivesConcrete.xmssRootFromSigAtLayer 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      wotsPk0 lsig0.authPath = some root0
  lsig1 : XmssLayerSig
  wotsPk1 : Bytes
  hLayer1 : layers[1]? = some lsig1
  hGrinding1 :
    wotsGrindingFailsAtLayer c13PrimitivesConcrete 1 c13 pk
      ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
      root0 lsig1.wots = false
  hWots1 :
    c13PrimitivesConcrete.wotsPkFromSigAtLayer 1 c13 pk
      ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
      root0 lsig1.wots = some wotsPk1
  hXmss1 :
    c13PrimitivesConcrete.xmssRootFromSigAtLayer 1 c13 pk
      ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
      wotsPk1 lsig1.authPath = some specRoot

/-- A successful concrete C13 hypertree fold exposes exactly the two successful
layer records that produced the returned root. -/
def foldHypertree_c13_ok_two_layer_data
    (pk : PublicKey) (digest : HMsg) (forsPk specRoot : Bytes)
    (layers : List XmssLayerSig)
    (hFold : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers
        = .ok specRoot) :
    FoldHypertreeC13OkTwoLayerData pk digest forsPk layers specRoot := by
  unfold foldHypertree at hFold
  unfold foldHypertreeAux at hFold
  simp [c13] at hFold
  cases hLayer0 : layers[0]? with
  | none =>
      simp [hLayer0] at hFold
  | some lsig0 =>
      simp [hLayer0] at hFold
      by_cases hGrinding0True :
          wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            forsPk lsig0.wots = true
      · have hGrinding0True' :
            wotsGrindingFailsAtLayer c13PrimitivesConcrete 0
              { name := "SPHINCS-C13", n := 16, fullPkSeed := true, fullPkRoot := true,
                h := 22, d := 2, subtreeH := 11, forsK := 7, forsA := 19,
                forsAuthTrees := 6, wotsW := 8, wotsLen := 43, rBytes := 16,
                sigBytes := 3688, hashAlg := HashAlg.keccak256,
                adrsFormat := AddressFormat.fipsUncompressed,
                wotsMode := WotsMode.grindingTarget 208,
                forsMode := ForsMode.grindingForcedZero 6 }
              pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots = true := by
          simpa [c13] using hGrinding0True
        simp [hGrinding0True'] at hFold
      · have hGrinding0False :
            wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
              (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots = false := by
          cases h :
              wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
                (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                forsPk lsig0.wots <;> simp [h] at hGrinding0True ⊢
        have hGrinding0False' :
            ¬ wotsGrindingFailsAtLayer c13PrimitivesConcrete 0
              { name := "SPHINCS-C13", n := 16, fullPkSeed := true, fullPkRoot := true,
                h := 22, d := 2, subtreeH := 11, forsK := 7, forsA := 19,
                forsAuthTrees := 6, wotsW := 8, wotsLen := 43, rBytes := 16,
                sigBytes := 3688, hashAlg := HashAlg.keccak256,
                adrsFormat := AddressFormat.fipsUncompressed,
                wotsMode := WotsMode.grindingTarget 208,
                forsMode := ForsMode.grindingForcedZero 6 }
              pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots = true := by
          simpa [c13] using hGrinding0True
        simp only [hGrinding0False'] at hFold
        simp at hFold
        cases hWots0 :
            c13PrimitivesConcrete.wotsPkFromSigAtLayer 0 c13 pk
              (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots with
        | none =>
            have hWots0' :
                c13PrimitivesConcrete.wotsPkFromSigAtLayer 0
                  { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                    fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                    forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                    wotsLen := 43, rBytes := 16, sigBytes := 3688,
                    hashAlg := HashAlg.keccak256,
                    adrsFormat := AddressFormat.fipsUncompressed,
                    wotsMode := WotsMode.grindingTarget 208,
                    forsMode := ForsMode.grindingForcedZero 6 }
                  pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                  forsPk lsig0.wots = none := by
              simpa [c13] using hWots0
            simp [hWots0'] at hFold
        | some wotsPk0 =>
            have hWots0' :
                c13PrimitivesConcrete.wotsPkFromSigAtLayer 0
                  { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                    fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                    forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                    wotsLen := 43, rBytes := 16, sigBytes := 3688,
                    hashAlg := HashAlg.keccak256,
                    adrsFormat := AddressFormat.fipsUncompressed,
                    wotsMode := WotsMode.grindingTarget 208,
                    forsMode := ForsMode.grindingForcedZero 6 }
                  pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                  forsPk lsig0.wots = some wotsPk0 := by
              simpa [c13] using hWots0
            simp [hWots0'] at hFold
            cases hXmss0 :
                c13PrimitivesConcrete.xmssRootFromSigAtLayer 0 c13 pk
                  (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                  wotsPk0 lsig0.authPath with
            | none =>
                have hXmss0' :
                    c13PrimitivesConcrete.xmssRootFromSigAtLayer 0
                      { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                        fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                        forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                        wotsLen := 43, rBytes := 16, sigBytes := 3688,
                        hashAlg := HashAlg.keccak256,
                        adrsFormat := AddressFormat.fipsUncompressed,
                        wotsMode := WotsMode.grindingTarget 208,
                        forsMode := ForsMode.grindingForcedZero 6 }
                      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                      wotsPk0 lsig0.authPath = none := by
                  simpa [c13] using hXmss0
                simp [hXmss0'] at hFold
            | some root0 =>
                have hXmss0' :
                    c13PrimitivesConcrete.xmssRootFromSigAtLayer 0
                      { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                        fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                        forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                        wotsLen := 43, rBytes := 16, sigBytes := 3688,
                        hashAlg := HashAlg.keccak256,
                        adrsFormat := AddressFormat.fipsUncompressed,
                        wotsMode := WotsMode.grindingTarget 208,
                        forsMode := ForsMode.grindingForcedZero 6 }
                      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                      wotsPk0 lsig0.authPath = some root0 := by
                  simpa [c13] using hXmss0
                simp [hXmss0'] at hFold
                unfold foldHypertreeAux at hFold
                simp at hFold
                cases hLayer1 : layers[1]? with
                | none =>
                    simp [hLayer1] at hFold
                | some lsig1 =>
                    simp [hLayer1] at hFold
                    by_cases hGrinding1True :
                        wotsGrindingFailsAtLayer c13PrimitivesConcrete 1 c13 pk
                          ((digest.hyperIndex / 2048) / 2048)
                          ((digest.hyperIndex / 2048) % 2048)
                          root0 lsig1.wots = true
                    · have hGrinding1True' :
                          wotsGrindingFailsAtLayer c13PrimitivesConcrete 1
                            { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                              fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                              forsK := 7, forsA := 19, forsAuthTrees := 6,
                              wotsW := 8, wotsLen := 43, rBytes := 16,
                              sigBytes := 3688, hashAlg := HashAlg.keccak256,
                              adrsFormat := AddressFormat.fipsUncompressed,
                              wotsMode := WotsMode.grindingTarget 208,
                              forsMode := ForsMode.grindingForcedZero 6 }
                            pk ((digest.hyperIndex / 2048) / 2048)
                            ((digest.hyperIndex / 2048) % 2048)
                            root0 lsig1.wots = true := by
                        simpa [c13] using hGrinding1True
                      simp [hGrinding1True'] at hFold
                    · have hGrinding1False :
                          wotsGrindingFailsAtLayer c13PrimitivesConcrete 1 c13 pk
                            ((digest.hyperIndex / 2048) / 2048)
                            ((digest.hyperIndex / 2048) % 2048)
                            root0 lsig1.wots = false := by
                        cases h :
                            wotsGrindingFailsAtLayer c13PrimitivesConcrete 1 c13 pk
                              ((digest.hyperIndex / 2048) / 2048)
                              ((digest.hyperIndex / 2048) % 2048)
                              root0 lsig1.wots <;> simp [h] at hGrinding1True ⊢
                      have hGrinding1False' :
                          ¬ wotsGrindingFailsAtLayer c13PrimitivesConcrete 1
                            { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                              fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                              forsK := 7, forsA := 19, forsAuthTrees := 6,
                              wotsW := 8, wotsLen := 43, rBytes := 16,
                              sigBytes := 3688, hashAlg := HashAlg.keccak256,
                              adrsFormat := AddressFormat.fipsUncompressed,
                              wotsMode := WotsMode.grindingTarget 208,
                              forsMode := ForsMode.grindingForcedZero 6 }
                            pk ((digest.hyperIndex / 2048) / 2048)
                            ((digest.hyperIndex / 2048) % 2048)
                            root0 lsig1.wots = true := by
                        simpa [c13] using hGrinding1True
                      simp only [hGrinding1False'] at hFold
                      simp at hFold
                      cases hWots1 :
                          c13PrimitivesConcrete.wotsPkFromSigAtLayer 1 c13 pk
                            ((digest.hyperIndex / 2048) / 2048)
                            ((digest.hyperIndex / 2048) % 2048)
                            root0 lsig1.wots with
                      | none =>
                          have hWots1' :
                              c13PrimitivesConcrete.wotsPkFromSigAtLayer 1
                                { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                  fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                  forsK := 7, forsA := 19, forsAuthTrees := 6,
                                  wotsW := 8, wotsLen := 43, rBytes := 16,
                                  sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                  adrsFormat := AddressFormat.fipsUncompressed,
                                  wotsMode := WotsMode.grindingTarget 208,
                                  forsMode := ForsMode.grindingForcedZero 6 }
                                pk ((digest.hyperIndex / 2048) / 2048)
                                ((digest.hyperIndex / 2048) % 2048)
                                root0 lsig1.wots = none := by
                            simpa [c13] using hWots1
                          simp [hWots1'] at hFold
                      | some wotsPk1 =>
                          have hWots1' :
                              c13PrimitivesConcrete.wotsPkFromSigAtLayer 1
                                { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                  fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                  forsK := 7, forsA := 19, forsAuthTrees := 6,
                                  wotsW := 8, wotsLen := 43, rBytes := 16,
                                  sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                  adrsFormat := AddressFormat.fipsUncompressed,
                                  wotsMode := WotsMode.grindingTarget 208,
                                  forsMode := ForsMode.grindingForcedZero 6 }
                                pk ((digest.hyperIndex / 2048) / 2048)
                                ((digest.hyperIndex / 2048) % 2048)
                                root0 lsig1.wots = some wotsPk1 := by
                            simpa [c13] using hWots1
                          simp [hWots1'] at hFold
                          cases hXmss1 :
                              c13PrimitivesConcrete.xmssRootFromSigAtLayer 1 c13 pk
                                ((digest.hyperIndex / 2048) / 2048)
                                ((digest.hyperIndex / 2048) % 2048)
                                wotsPk1 lsig1.authPath with
                          | none =>
                              have hXmss1' :
                                  c13PrimitivesConcrete.xmssRootFromSigAtLayer 1
                                    { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                      fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                      forsK := 7, forsA := 19, forsAuthTrees := 6,
                                      wotsW := 8, wotsLen := 43, rBytes := 16,
                                      sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                      adrsFormat := AddressFormat.fipsUncompressed,
                                      wotsMode := WotsMode.grindingTarget 208,
                                      forsMode := ForsMode.grindingForcedZero 6 }
                                    pk ((digest.hyperIndex / 2048) / 2048)
                                    ((digest.hyperIndex / 2048) % 2048)
                                    wotsPk1 lsig1.authPath = none := by
                                simpa [c13] using hXmss1
                              simp [hXmss1'] at hFold
                          | some root1 =>
                              have hXmss1' :
                                  c13PrimitivesConcrete.xmssRootFromSigAtLayer 1
                                    { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                      fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                      forsK := 7, forsA := 19, forsAuthTrees := 6,
                                      wotsW := 8, wotsLen := 43, rBytes := 16,
                                      sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                      adrsFormat := AddressFormat.fipsUncompressed,
                                      wotsMode := WotsMode.grindingTarget 208,
                                      forsMode := ForsMode.grindingForcedZero 6 }
                                    pk ((digest.hyperIndex / 2048) / 2048)
                                    ((digest.hyperIndex / 2048) % 2048)
                                    wotsPk1 lsig1.authPath = some root1 := by
                                simpa [c13] using hXmss1
                              simp [hXmss1'] at hFold
                              injection hFold with hRoot
                              subst hRoot
                              exact
                                { lsig0 := lsig0
                                  wotsPk0 := wotsPk0
                                  root0 := root0
                                  hLayer0 := hLayer0
                                  hGrinding0 := hGrinding0False
                                  hWots0 := hWots0
                                  hXmss0 := hXmss0
                                  lsig1 := lsig1
                                  wotsPk1 := wotsPk1
                                  hLayer1 := hLayer1
                                  hGrinding1 := hGrinding1False
                                  hWots1 := hWots1
                                  hXmss1 := hXmss1 }

/-- Data exposed when the concrete C13 hypertree fold reverts immediately at
layer 0 because the WOTS+C grinding target failed. -/
structure FoldHypertreeC13RevertedLayer0Data
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig) where
  lsig0 : XmssLayerSig
  hLayer0 : layers[0]? = some lsig0
  hGrinding0 :
    wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk lsig0.wots = true

/-- Data exposed when the concrete C13 hypertree fold succeeds at layer 0 and
then reverts at layer 1 because the WOTS+C grinding target failed. -/
structure FoldHypertreeC13RevertedLayer1Data
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig) where
  lsig0 : XmssLayerSig
  wotsPk0 : Bytes
  root0 : Bytes
  hLayer0 : layers[0]? = some lsig0
  hGrinding0 :
    wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk lsig0.wots = false
  hWots0 :
    c13PrimitivesConcrete.wotsPkFromSigAtLayer 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk lsig0.wots = some wotsPk0
  hXmss0 :
    c13PrimitivesConcrete.xmssRootFromSigAtLayer 0 c13 pk
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      wotsPk0 lsig0.authPath = some root0
  lsig1 : XmssLayerSig
  hLayer1 : layers[1]? = some lsig1
  hGrinding1 :
    wotsGrindingFailsAtLayer c13PrimitivesConcrete 1 c13 pk
      ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
      root0 lsig1.wots = true

/-- Data exposed by a concrete C13 hypertree fold that hard-reverts.  With
`d = 2`, the revert must be either the first layer's grinding miss or the second
layer's grinding miss after a successful first layer. -/
inductive FoldHypertreeC13RevertedTwoLayerData
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig) where
  | layer0 :
      FoldHypertreeC13RevertedLayer0Data pk digest forsPk layers →
      FoldHypertreeC13RevertedTwoLayerData pk digest forsPk layers
  | layer1 :
      FoldHypertreeC13RevertedLayer1Data pk digest forsPk layers →
      FoldHypertreeC13RevertedTwoLayerData pk digest forsPk layers

/-- A concrete C13 hypertree hard-revert exposes the corresponding two-layer
grinding-failure record. -/
def foldHypertree_c13_reverted_two_layer_data
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig)
    (hFold : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers
        = .reverted) :
    FoldHypertreeC13RevertedTwoLayerData pk digest forsPk layers := by
  unfold foldHypertree at hFold
  unfold foldHypertreeAux at hFold
  simp [c13] at hFold
  cases hLayer0 : layers[0]? with
  | none =>
      simp [hLayer0] at hFold
  | some lsig0 =>
      simp [hLayer0] at hFold
      by_cases hGrinding0True :
          wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            forsPk lsig0.wots = true
      · exact FoldHypertreeC13RevertedTwoLayerData.layer0
          { lsig0 := lsig0
            hLayer0 := hLayer0
            hGrinding0 := hGrinding0True }
      · have hGrinding0False :
            wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
              (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots = false := by
          cases h :
              wotsGrindingFailsAtLayer c13PrimitivesConcrete 0 c13 pk
                (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                forsPk lsig0.wots <;> simp [h] at hGrinding0True ⊢
        have hGrinding0False' :
            ¬ wotsGrindingFailsAtLayer c13PrimitivesConcrete 0
              { name := "SPHINCS-C13", n := 16, fullPkSeed := true, fullPkRoot := true,
                h := 22, d := 2, subtreeH := 11, forsK := 7, forsA := 19,
                forsAuthTrees := 6, wotsW := 8, wotsLen := 43, rBytes := 16,
                sigBytes := 3688, hashAlg := HashAlg.keccak256,
                adrsFormat := AddressFormat.fipsUncompressed,
                wotsMode := WotsMode.grindingTarget 208,
                forsMode := ForsMode.grindingForcedZero 6 }
              pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots = true := by
          simpa [c13] using hGrinding0True
        simp only [hGrinding0False'] at hFold
        simp at hFold
        cases hWots0 :
            c13PrimitivesConcrete.wotsPkFromSigAtLayer 0 c13 pk
              (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
              forsPk lsig0.wots with
        | none =>
            have hWots0' :
                c13PrimitivesConcrete.wotsPkFromSigAtLayer 0
                  { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                    fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                    forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                    wotsLen := 43, rBytes := 16, sigBytes := 3688,
                    hashAlg := HashAlg.keccak256,
                    adrsFormat := AddressFormat.fipsUncompressed,
                    wotsMode := WotsMode.grindingTarget 208,
                    forsMode := ForsMode.grindingForcedZero 6 }
                  pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                  forsPk lsig0.wots = none := by
              simpa [c13] using hWots0
            simp [hWots0'] at hFold
        | some wotsPk0 =>
            have hWots0' :
                c13PrimitivesConcrete.wotsPkFromSigAtLayer 0
                  { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                    fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                    forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                    wotsLen := 43, rBytes := 16, sigBytes := 3688,
                    hashAlg := HashAlg.keccak256,
                    adrsFormat := AddressFormat.fipsUncompressed,
                    wotsMode := WotsMode.grindingTarget 208,
                    forsMode := ForsMode.grindingForcedZero 6 }
                  pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                  forsPk lsig0.wots = some wotsPk0 := by
              simpa [c13] using hWots0
            simp [hWots0'] at hFold
            cases hXmss0 :
                c13PrimitivesConcrete.xmssRootFromSigAtLayer 0 c13 pk
                  (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                  wotsPk0 lsig0.authPath with
            | none =>
                have hXmss0' :
                    c13PrimitivesConcrete.xmssRootFromSigAtLayer 0
                      { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                        fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                        forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                        wotsLen := 43, rBytes := 16, sigBytes := 3688,
                        hashAlg := HashAlg.keccak256,
                        adrsFormat := AddressFormat.fipsUncompressed,
                        wotsMode := WotsMode.grindingTarget 208,
                        forsMode := ForsMode.grindingForcedZero 6 }
                      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                      wotsPk0 lsig0.authPath = none := by
                  simpa [c13] using hXmss0
                simp [hXmss0'] at hFold
            | some root0 =>
                have hXmss0' :
                    c13PrimitivesConcrete.xmssRootFromSigAtLayer 0
                      { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                        fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                        forsK := 7, forsA := 19, forsAuthTrees := 6, wotsW := 8,
                        wotsLen := 43, rBytes := 16, sigBytes := 3688,
                        hashAlg := HashAlg.keccak256,
                        adrsFormat := AddressFormat.fipsUncompressed,
                        wotsMode := WotsMode.grindingTarget 208,
                        forsMode := ForsMode.grindingForcedZero 6 }
                      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                      wotsPk0 lsig0.authPath = some root0 := by
                  simpa [c13] using hXmss0
                simp [hXmss0'] at hFold
                unfold foldHypertreeAux at hFold
                simp at hFold
                cases hLayer1 : layers[1]? with
                | none =>
                    simp [hLayer1] at hFold
                | some lsig1 =>
                    simp [hLayer1] at hFold
                    by_cases hGrinding1True :
                        wotsGrindingFailsAtLayer c13PrimitivesConcrete 1 c13 pk
                          ((digest.hyperIndex / 2048) / 2048)
                          ((digest.hyperIndex / 2048) % 2048)
                          root0 lsig1.wots = true
                    · exact FoldHypertreeC13RevertedTwoLayerData.layer1
                        { lsig0 := lsig0
                          wotsPk0 := wotsPk0
                          root0 := root0
                          hLayer0 := hLayer0
                          hGrinding0 := hGrinding0False
                          hWots0 := hWots0
                          hXmss0 := hXmss0
                          lsig1 := lsig1
                          hLayer1 := hLayer1
                          hGrinding1 := hGrinding1True }
                    · have hGrinding1False' :
                          ¬ wotsGrindingFailsAtLayer c13PrimitivesConcrete 1
                            { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                              fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                              forsK := 7, forsA := 19, forsAuthTrees := 6,
                              wotsW := 8, wotsLen := 43, rBytes := 16,
                              sigBytes := 3688, hashAlg := HashAlg.keccak256,
                              adrsFormat := AddressFormat.fipsUncompressed,
                              wotsMode := WotsMode.grindingTarget 208,
                              forsMode := ForsMode.grindingForcedZero 6 }
                            pk ((digest.hyperIndex / 2048) / 2048)
                            ((digest.hyperIndex / 2048) % 2048)
                            root0 lsig1.wots = true := by
                        simpa [c13] using hGrinding1True
                      simp only [hGrinding1False'] at hFold
                      simp at hFold
                      cases hWots1 :
                          c13PrimitivesConcrete.wotsPkFromSigAtLayer 1 c13 pk
                            ((digest.hyperIndex / 2048) / 2048)
                            ((digest.hyperIndex / 2048) % 2048)
                            root0 lsig1.wots with
                      | none =>
                          have hWots1' :
                              c13PrimitivesConcrete.wotsPkFromSigAtLayer 1
                                { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                  fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                  forsK := 7, forsA := 19, forsAuthTrees := 6,
                                  wotsW := 8, wotsLen := 43, rBytes := 16,
                                  sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                  adrsFormat := AddressFormat.fipsUncompressed,
                                  wotsMode := WotsMode.grindingTarget 208,
                                  forsMode := ForsMode.grindingForcedZero 6 }
                                pk ((digest.hyperIndex / 2048) / 2048)
                                ((digest.hyperIndex / 2048) % 2048)
                                root0 lsig1.wots = none := by
                            simpa [c13] using hWots1
                          simp [hWots1'] at hFold
                      | some wotsPk1 =>
                          have hWots1' :
                              c13PrimitivesConcrete.wotsPkFromSigAtLayer 1
                                { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                  fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                  forsK := 7, forsA := 19, forsAuthTrees := 6,
                                  wotsW := 8, wotsLen := 43, rBytes := 16,
                                  sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                  adrsFormat := AddressFormat.fipsUncompressed,
                                  wotsMode := WotsMode.grindingTarget 208,
                                  forsMode := ForsMode.grindingForcedZero 6 }
                                pk ((digest.hyperIndex / 2048) / 2048)
                                ((digest.hyperIndex / 2048) % 2048)
                                root0 lsig1.wots = some wotsPk1 := by
                            simpa [c13] using hWots1
                          simp [hWots1'] at hFold
                          cases hXmss1 :
                              c13PrimitivesConcrete.xmssRootFromSigAtLayer 1 c13 pk
                                ((digest.hyperIndex / 2048) / 2048)
                                ((digest.hyperIndex / 2048) % 2048)
                                wotsPk1 lsig1.authPath with
                          | none =>
                              have hXmss1' :
                                  c13PrimitivesConcrete.xmssRootFromSigAtLayer 1
                                    { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                      fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                      forsK := 7, forsA := 19, forsAuthTrees := 6,
                                      wotsW := 8, wotsLen := 43, rBytes := 16,
                                      sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                      adrsFormat := AddressFormat.fipsUncompressed,
                                      wotsMode := WotsMode.grindingTarget 208,
                                      forsMode := ForsMode.grindingForcedZero 6 }
                                    pk ((digest.hyperIndex / 2048) / 2048)
                                    ((digest.hyperIndex / 2048) % 2048)
                                    wotsPk1 lsig1.authPath = none := by
                                simpa [c13] using hXmss1
                              simp [hXmss1'] at hFold
                          | some root1 =>
                              have hXmss1' :
                                  c13PrimitivesConcrete.xmssRootFromSigAtLayer 1
                                    { name := "SPHINCS-C13", n := 16, fullPkSeed := true,
                                      fullPkRoot := true, h := 22, d := 2, subtreeH := 11,
                                      forsK := 7, forsA := 19, forsAuthTrees := 6,
                                      wotsW := 8, wotsLen := 43, rBytes := 16,
                                      sigBytes := 3688, hashAlg := HashAlg.keccak256,
                                      adrsFormat := AddressFormat.fipsUncompressed,
                                      wotsMode := WotsMode.grindingTarget 208,
                                      forsMode := ForsMode.grindingForcedZero 6 }
                                    pk ((digest.hyperIndex / 2048) / 2048)
                                    ((digest.hyperIndex / 2048) % 2048)
                                    wotsPk1 lsig1.authPath = some root1 := by
                                simpa [c13] using hXmss1
                              simp [hXmss1'] at hFold
                              unfold foldHypertreeAux at hFold
                              simp at hFold

/-- If the C13 hypertree climb returns `.ok root`, then the returned root is
canonical, provided the starting FORS public key is canonical. -/
theorem foldHypertreeAux_c13_ok_root_canonical
    (pk : PublicKey) (fuel layer idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig) {root : Bytes}
    (hNode : CanonicalHash16 node)
    (h : foldHypertreeAux c13PrimitivesConcrete c13 pk fuel layer idxTree node layers
        = .ok root) :
    CanonicalHash16 root := by
  induction fuel generalizing layer idxTree node root with
  | zero =>
      unfold foldHypertreeAux at h
      injection h with hEq
      rw [← hEq]
      exact hNode
  | succ fuel ih =>
      unfold foldHypertreeAux at h
      by_cases hlt : layer < c13.d
      · simp only [hlt, ↓reduceIte] at h
        cases hLayer : layers[layer]? with
        | none => simp [hLayer] at h
        | some lsig =>
            simp only [hLayer] at h
            let idxLeaf := idxTree % 2 ^ c13.subtreeH
            let nextTree := idxTree / 2 ^ c13.subtreeH
            by_cases hgrind :
                wotsGrindingFailsAtLayer c13PrimitivesConcrete layer c13 pk nextTree idxLeaf node lsig.wots
                  = true
            · simp [idxLeaf, nextTree, hgrind] at h
            · simp only [idxLeaf, nextTree, hgrind] at h
              cases hWots :
                  c13PrimitivesConcrete.wotsPkFromSigAtLayer layer c13 pk nextTree idxLeaf node lsig.wots
                  with
              | none =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSigAtLayer layer c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = none := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp [hWots'] at h
              | some wotsPk =>
                  have hWots' :
                      c13PrimitivesConcrete.wotsPkFromSigAtLayer layer c13 pk
                        (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                        node lsig.wots = some wotsPk := by
                    simpa [idxLeaf, nextTree] using hWots
                  simp only [hWots'] at h
                  cases hXmss :
                      c13PrimitivesConcrete.xmssRootFromSigAtLayer layer c13 pk nextTree idxLeaf
                        wotsPk lsig.authPath with
                  | none =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSigAtLayer layer c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = none := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp [hXmss'] at h
                  | some xmssRoot =>
                      have hXmss' :
                          c13PrimitivesConcrete.xmssRootFromSigAtLayer layer c13 pk
                            (idxTree / 2 ^ c13.subtreeH) (idxTree % 2 ^ c13.subtreeH)
                            wotsPk lsig.authPath = some xmssRoot := by
                        simpa [idxLeaf, nextTree] using hXmss
                      simp only [hXmss'] at h
                      have hx : CanonicalHash16 xmssRoot := by
                        exact xmssRootFromSigC13AtLayer_canonical
                          (by simpa [c13PrimitivesConcrete] using hXmss')
                      exact ih (layer + 1) nextTree xmssRoot hx h
      · simp only [hlt, ↓reduceIte] at h
        injection h with hEq
        rw [← hEq]
        exact hNode

/-- C13 `foldHypertree` preserves canonical roots on successful `.ok` output. -/
theorem foldHypertree_c13_ok_root_canonical
    {pk : PublicKey} {digest : HMsg} {forsPk : Bytes} {layers : List XmssLayerSig}
    {root : Bytes}
    (hForsPk : CanonicalHash16 forsPk)
    (h : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    CanonicalHash16 root :=
  foldHypertreeAux_c13_ok_root_canonical
    pk c13.d 0 digest.hyperIndex forsPk layers hForsPk h

/-- C13 `foldHypertree` returns a canonical root after successful C13 FORS
reconstruction. -/
theorem foldHypertree_c13_ok_root_canonical_of_fors
    {pk : PublicKey} {digest : HMsg} {fors : ForsSig} {forsPk root : Bytes}
    {layers : List XmssLayerSig}
    (hFors : c13PrimitivesConcrete.forsPkFromSig c13 pk digest fors = some forsPk)
    (hFold : foldHypertree c13PrimitivesConcrete c13 pk digest forsPk layers = .ok root) :
    CanonicalHash16 root :=
  foldHypertree_c13_ok_root_canonical
    (forsPkFromSigC13_canonical (by simpa [c13PrimitivesConcrete] using hFors)) hFold

#print axioms forsAllRootsC13_length
#print axioms forsNormalRootsC13_getElem?
#print axioms forsNormalRootsC13_getElem
#print axioms forsAllRootsC13_getElem?_normal
#print axioms forsAllRootsC13_getElem?_forced
#print axioms forsAllRootsC13_getElem_normal
#print axioms forsAllRootsC13_getElem_forced
#print axioms forsPkFromSigC13_eq_named
#print axioms forsPkFromSigC13_some_eq_hash16_named
#print axioms hash16OfWord_size
#print axioms CanonicalHash16
#print axioms hash16OfWord_canonical
#print axioms forsPkFromSigC13_size
#print axioms forsPkFromSigC13_canonical
#print axioms wotsPkFromSigC13_size
#print axioms wotsPkFromSigC13_canonical
#print axioms xmssRootFromSigC13_size
#print axioms xmssRootFromSigC13_canonical
#print axioms wotsPkFromSigC13AtLayer_zero
#print axioms wotsGrindingOkC13AtLayer_zero
#print axioms xmssRootFromSigC13AtLayer_zero
#print axioms wotsGrindingFailsC13_false_iff
#print axioms wotsDigitSum_eq_of_wotsGrindingFailsC13_false
#print axioms wotsGrindingFailsC13AtLayer_true_iff
#print axioms wotsDigitSum_ne_of_wotsGrindingFailsC13AtLayer_true
#print axioms wotsDigitSum_eq_of_wotsGrindingFailsC13AtLayer_false
#print axioms wotsPkFromSigC13_isSome
#print axioms xmssRootFromSigC13_isSome
#print axioms foldHypertreeAux_c13_ne_rejected_of_layers
#print axioms foldHypertree_c13_ne_rejected_of_layers_length
#print axioms foldHypertree_c13_ne_rejected_of_parse
#print axioms FoldHypertreeC13OkTwoLayerData
#print axioms foldHypertree_c13_ok_two_layer_data
#print axioms FoldHypertreeC13RevertedLayer0Data
#print axioms FoldHypertreeC13RevertedLayer1Data
#print axioms FoldHypertreeC13RevertedTwoLayerData
#print axioms foldHypertree_c13_reverted_two_layer_data
#print axioms foldHypertreeAux_c13_ok_root_size
#print axioms foldHypertree_c13_ok_root_size
#print axioms foldHypertree_c13_ok_root_size_of_fors
#print axioms foldHypertreeAux_c13_ok_root_canonical
#print axioms foldHypertree_c13_ok_root_canonical
#print axioms foldHypertree_c13_ok_root_canonical_of_fors
#print axioms parseSignatureC13_R
#print axioms parseSignatureC13_some_of_size
#print axioms parseSignatureC13_eq_none_iff
#print axioms parseSignatureC13_isSome_iff
#print axioms parseSignatureC13_shape
#print axioms parsePublicKey_c13
#print axioms parsePublicKey_c13_does_not_force_pkRoot_size
#print axioms parseSignatureC13_fors_sk_getElem?
#print axioms parseSignatureC13_fors_authPath_getD_getElem?
#print axioms parseSignatureC13_layer_wots_count
#print axioms forcedZeroOk_c13_forsIndex_six
#print axioms hMsgC13_forsIndex_six
#print axioms hMsgC13_forsIndex_getD_eq
#print axioms hMsgC13_forsIndex_getD_lt
#print axioms hMsgC13_hyperIndex_lt
#print axioms hMsgC13_hyperIndex_div_2048_lt
#print axioms adrsForsLeaf_lt_of_normal_idx_lt
#print axioms adrsForsLeaf_hMsgC13_normal_lt

end C13Concrete
end SphincsMinusVerifierSpec
