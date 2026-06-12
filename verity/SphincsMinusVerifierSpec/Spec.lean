/-
  Lean 4 specification for the SPHINCS- verifier variants in nconsigny/SPHINCS-.

  This file separates two specification layers:

  * `verifyParsed` is the algorithmic spec over a parsed public key and parsed
    signature. It stays close to the mathematical verifier.
  * `ByteLevel.verifyBytes` is the contract-facing byte spec. It checks ABI-level
    public-key canonicality, parses signature bytes, and then delegates to
    `verifyParsed`.

  Verity models refine the byte-level spec. The byte-level spec then refines the
  algorithmic spec by construction. Memory layout and Yul mechanics belong only
  in the Verity implementation model.
-/

namespace SphincsMinusVerifierSpec

abbrev Bytes := ByteArray

/-- Big-endian `Nat` value of a byte string, with byte 0 most significant. -/
def bytesToNatBE (ba : Bytes) : Nat :=
  ba.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Big-endian `len`-byte projection of a natural number. -/
def bytesOfNatBE (len : Nat) (w : Nat) : Bytes :=
  ⟨((List.range len).map
    (fun i => UInt8.ofNat ((w / (256 ^ (len - 1 - i))) % 256))).toArray⟩

/-- Keep the low `8 * len` bits of a byte string and render them as exactly
`len` big-endian bytes.  This is the byte-level counterpart of the Verity
models' `bytes32` parameter word projection for the Keccak SPHINCS- contracts. -/
def lowBytesProjection (len : Nat) (x : Bytes) : Bytes :=
  bytesOfNatBE len (bytesToNatBE x % (2 ^ (8 * len)))

inductive HashAlg where
  | keccak256
  | sha256_MGF1
  deriving DecidableEq, Repr

inductive AddressFormat where
  | fipsUncompressed
  | fipsCompressed
  | jardin
  deriving DecidableEq, Repr

inductive WotsMode where
  | standardChecksum
  | grindingTarget (targetSum : Nat)
  deriving DecidableEq, Repr

inductive ForsMode where
  | standard
  | grindingForcedZero (forcedTree : Nat)
  deriving DecidableEq, Repr

structure Variant where
  name          : String
  n             : Nat
  fullPkSeed    : Bool
  fullPkRoot    : Bool
  h             : Nat
  d             : Nat
  subtreeH      : Nat
  forsK         : Nat
  forsA         : Nat
  forsAuthTrees : Nat
  wotsW         : Nat
  wotsLen       : Nat
  rBytes        : Nat
  sigBytes      : Nat
  hashAlg       : HashAlg
  adrsFormat    : AddressFormat
  wotsMode      : WotsMode
  forsMode      : ForsMode
  deriving Repr

/-- Public-key root bytes used by the byte-level final comparison.  Variants
whose public-key root is modeled as a full `bytes32` contract word compare the
scheme-sized low-word projection; canonicalized variants keep raw byte equality. -/
def comparePkRootBytes (v : Variant) (pkRoot : Bytes) : Bytes :=
  if v.fullPkRoot then lowBytesProjection v.n pkRoot else pkRoot

/-- Final root comparison at the byte-spec boundary. -/
def rootMatchesPk (v : Variant) (root pkRoot : Bytes) : Bool :=
  root == comparePkRootBytes v pkRoot

def Variant.paramOk (v : Variant) : Prop :=
  v.h = v.d * v.subtreeH ∧
  v.forsAuthTrees ≤ v.forsK ∧
  (v.rBytes = v.n ∨ v.rBytes = 2 * v.n)

def c13 : Variant :=
  { name := "SPHINCS-C13"
  , n := 16
  , fullPkSeed := true
  , fullPkRoot := true
  , h := 22
  , d := 2
  , subtreeH := 11
  , forsK := 7
  , forsA := 19
  , forsAuthTrees := 6
  , wotsW := 8
  , wotsLen := 43
  , rBytes := 16
  , sigBytes := 3688
  , hashAlg := .keccak256
  , adrsFormat := .fipsUncompressed
  , wotsMode := .grindingTarget 208
  , forsMode := .grindingForcedZero 6 }

def slhDsaSha2_128_24 : Variant :=
  { name := "SLH-DSA-SHA2-128s-24"
  , n := 16
  , fullPkSeed := false
  , fullPkRoot := false
  , h := 22
  , d := 1
  , subtreeH := 22
  , forsK := 6
  , forsA := 24
  , forsAuthTrees := 6
  , wotsW := 4
  , wotsLen := 68
  , rBytes := 16
  , sigBytes := 3856
  , hashAlg := .sha256_MGF1
  , adrsFormat := .fipsCompressed
  , wotsMode := .standardChecksum
  , forsMode := .standard }

theorem c13_paramOk : c13.paramOk := by
  simp [Variant.paramOk, c13]

theorem slhDsaSha2_128_24_paramOk : slhDsaSha2_128_24.paramOk := by
  simp [Variant.paramOk, slhDsaSha2_128_24]

structure PublicKey where
  pkSeed : Bytes
  pkRoot : Bytes

structure HMsg where
  /-- FORS message indices, one per FORS tree. -/
  forsIndex : List Nat
  /-- Full hypertree index. Each layer consumes the low `subtreeH` bits as the
      leaf index and shifts them off to obtain the next layer's tree index,
      mirroring the verifier's `idxLeaf := idxTree & mask; idxTree := idxTree >> subtreeH`
      walk (WOTS/XMSS at a layer use the post-shift tree index). -/
  hyperIndex : Nat

structure ForsSig where
  sk       : List Bytes
  authPath : List (List Bytes)

structure WotsSig where
  chains : List Bytes
  /-- Present only for WOTS+C variants. Ignored by standard WOTS+. -/
  count  : Nat

structure XmssLayerSig where
  wots     : WotsSig
  authPath : List Bytes

structure Signature where
  R      : Bytes
  fors   : ForsSig
  layers : List XmssLayerSig

/--
Semantic primitives used by the verifier.

The address format and hash algorithm are part of `Variant`; these functions
must interpret them exactly. For example, C13 uses Keccak-256 over
`seed || FIPS-uncompressed-ADRS || payload`, while the SHA2 variant uses the
FIPS compressed ADRS and SHA-256/MGF1 construction.
-/
structure Primitives where
  parseSignature  : (v : Variant) → Bytes → Option Signature
  hMsg            : (v : Variant) → PublicKey → Bytes → Bytes → HMsg
  forsPkFromSig   : (v : Variant) → PublicKey → HMsg → ForsSig → Option Bytes
  wotsPkFromSig   : (v : Variant) → PublicKey → Nat → Nat → Bytes → WotsSig → Option Bytes
  wotsPkFromSigAtLayer :
    (layer : Nat) → (v : Variant) → PublicKey → Nat → Nat → Bytes → WotsSig → Option Bytes
  /-- Whether a layer's WOTS+C signature meets its grinding `targetSum`. Only
      consulted for `WotsMode.grindingTarget` variants; the contract reverts when
      this fails. -/
  wotsGrindingOk  : (v : Variant) → PublicKey → Nat → Nat → Bytes → WotsSig → Bool
  wotsGrindingOkAtLayer :
    (layer : Nat) → (v : Variant) → PublicKey → Nat → Nat → Bytes → WotsSig → Bool
  xmssRootFromSig : (v : Variant) → PublicKey → Nat → Nat → Bytes → List Bytes → Option Bytes
  xmssRootFromSigAtLayer :
    (layer : Nat) → (v : Variant) → PublicKey → Nat → Nat → Bytes → List Bytes → Option Bytes

def forcedZeroOk (v : Variant) (digest : HMsg) : Bool :=
  match v.forsMode with
  | .standard => true
  | .grindingForcedZero t =>
      t < v.forsK && digest.forsIndex[t]? == some 0

def allSized (n : Nat) (xs : List Bytes) : Bool :=
  xs.all (fun x => x.size == n)

def allAuthSized (height : Nat) (xs : List (List Bytes)) : Bool :=
  xs.all (fun x => x.length == height)

def signatureShapeOk (v : Variant) (sig : Signature) : Bool :=
  sig.R.size == v.rBytes &&
  sig.fors.sk.length == v.forsK &&
  allSized v.n sig.fors.sk &&
  sig.fors.authPath.length == v.forsAuthTrees &&
  allAuthSized v.forsA sig.fors.authPath &&
  sig.layers.length == v.d &&
  sig.layers.all (fun layer =>
    layer.wots.chains.length == v.wotsLen &&
    allSized v.n layer.wots.chains &&
    layer.authPath.length == v.subtreeH &&
    allSized v.n layer.authPath)

/-- A public-key part is canonical when every byte below the `n` significant high
bytes is zero. This mirrors the contract's `x == x & N_MASK` guard, where `N_MASK`
keeps the high `n` bytes and forces the remaining low bytes to zero. -/
def pkPartCanonical (v : Variant) (x : Bytes) : Bool :=
  (List.range x.size).all (fun i => decide (i < v.n) || x.get! i == 0)

/-- Contract-faithful public-key acceptance at the byte-spec boundary. Variants
whose public-key parts use the full word (`fullPk* = true`, including C13)
impose no byte-level constraint; variants that mask to `n` bytes (`fullPk* =
false`, including the SHA-2 SLH-DSA verifier) require the low bytes to be zero
and otherwise reject with `Invalid public key`. -/
def publicKeyOk (v : Variant) (pk : PublicKey) : Bool :=
  (v.fullPkSeed || pkPartCanonical v pk.pkSeed) &&
  (v.fullPkRoot || pkPartCanonical v pk.pkRoot)

/-- Outcome of the hypertree climb, distinguishing the contract's two failure
modes: a hard `revert` (e.g. a WOTS+C grinding-target miss) versus a normal
`false` return (reconstruction produced a root that need not match). -/
inductive HyperResult where
  /-- The contract `revert`s before returning (grinding-target check failed). -/
  | reverted
  /-- Reconstruction could not complete; the contract returns `false`. -/
  | rejected
  /-- The climb produced a final root to compare against `pkRoot`. -/
  | ok (root : Bytes)
  deriving Nonempty

/-- Whether the layer's WOTS+C signature fails its grinding target. Standard
WOTS+ variants never grind, so they never revert here. -/
def wotsGrindingFails
    (p : Primitives) (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Bool :=
  match v.wotsMode with
  | .standardChecksum => false
  | .grindingTarget _ => ¬ p.wotsGrindingOk v pk treeIdx leafIdx node wots

/-- Layer-aware form used by the hypertree climb. -/
def wotsGrindingFailsAtLayer
    (p : Primitives) (layer : Nat) (v : Variant) (pk : PublicKey)
    (treeIdx leafIdx : Nat) (node : Bytes) (wots : WotsSig) : Bool :=
  match v.wotsMode with
  | .standardChecksum => false
  | .grindingTarget _ => ¬ p.wotsGrindingOkAtLayer layer v pk treeIdx leafIdx node wots

/--
Hypertree climb, written as a structural recursion on an explicit `fuel`
argument rather than a `partial def`.

Each step either terminates (`.ok`/`.rejected`/`.reverted`) or recurses with
`fuel` strictly decreased, so the kernel accepts the definition as total and
generates the usual equation lemmas. `foldHypertree` seeds `fuel := v.d`, which
covers every layer because the climb advances `layer` by one per step and stops
once `layer = v.d`; running out of fuel coincides with `layer = v.d` and yields
the same `.ok node` the `layer < v.d` guard would have produced.
-/
def foldHypertreeAux
    (p : Primitives) (v : Variant) (pk : PublicKey)
    (fuel : Nat) (layer : Nat) (idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig) : HyperResult :=
  match fuel with
  | 0 => .ok node
  | fuel + 1 =>
    if layer < v.d then
      match layers[layer]? with
      | none => .rejected
      | some lsig =>
      -- Match the verifier's per-layer walk: the low `subtreeH` bits are the leaf
      -- index, and WOTS/XMSS address with the tree index *after* shifting them off.
      let idxLeaf := idxTree % 2 ^ v.subtreeH
      let nextTree := idxTree / 2 ^ v.subtreeH
      if wotsGrindingFailsAtLayer p layer v pk nextTree idxLeaf node lsig.wots then
        .reverted
      else
        match p.wotsPkFromSigAtLayer layer v pk nextTree idxLeaf node lsig.wots with
        | none => .rejected
        | some wotsPk =>
            match p.xmssRootFromSigAtLayer layer v pk nextTree idxLeaf wotsPk lsig.authPath with
            | none => .rejected
            | some root =>
                foldHypertreeAux p v pk fuel (layer + 1) nextTree root layers
    else
      .ok node

def foldHypertree
    (p : Primitives) (v : Variant) (pk : PublicKey)
    (digest : HMsg) (startNode : Bytes) (layers : List XmssLayerSig) : HyperResult :=
  foldHypertreeAux p v pk v.d 0 digest.hyperIndex startNode layers

/--
Algorithmic verifier over parsed inputs.

This layer deliberately does not know about ABI decoding, Solidity memory
layout, or raw Yul. It assumes the public key and signature have already been
parsed into their scheme-level structures.
-/
def verifyParsed (p : Primitives) (v : Variant)
    (pk : PublicKey) (message : Bytes) (sig : Signature) : Option Bool :=
  let digest := p.hMsg v pk sig.R message
  -- `none` models a Solidity `revert`; `some b` models a normal boolean return.
  if ¬ signatureShapeOk v sig then
    none
  else if ¬ forcedZeroOk v digest then
    -- The forced-zero FORS bits were non-zero: the contract reverts.
    none
  else
    match p.forsPkFromSig v pk digest sig.fors with
    | none => some false
    | some forsPk =>
        match foldHypertree p v pk digest forsPk sig.layers with
        | .reverted => none
        | .rejected => some false
        | .ok root => some (rootMatchesPk v root pk.pkRoot)

/--
Compatibility wrapper for the original abstract target.

For the linked Nico contracts:
* bad signature length is malformed and should correspond to the Solidity revert;
* malformed public keys matter for the SHA2 verifier, where high-16-byte
  canonicality is checked by the contract;
* otherwise verification succeeds iff FORS reconstruction, all WOTS/XMSS
  layers, and final root comparison succeed under the selected variant.
-/
def verifySpec (p : Primitives) (v : Variant)
    (pk : PublicKey) (message sigBytes : Bytes) : Option Bool :=
  if sigBytes.size ≠ v.sigBytes then
    none
  else if ¬ publicKeyOk v pk then
    none
  else
    match p.parseSignature v sigBytes with
    | none => none
    | some sig =>
        verifyParsed p v pk message sig

namespace ByteLevel

/--
Parse the contract-facing public-key bytes.

The Solidity contracts expose `pkSeed` and `pkRoot` as separate `bytes32`
arguments. Canonical high-byte checks, where present, are part of the byte-level
contract API rather than the Verity memory model.
-/
def parsePublicKey (v : Variant)
    (pkSeed pkRoot : Bytes) : Option PublicKey :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  if publicKeyOk v pk then some pk else none

/--
Contract-facing byte-level verifier.

This layer owns externally observable byte parsing and malformed-input
behavior. It does not mention Solidity scratch memory, loop layout, or Yul.
-/
def verifyBytes (p : Primitives) (v : Variant)
    (pkSeed pkRoot message sigBytes : Bytes) : Option Bool :=
  if sigBytes.size ≠ v.sigBytes then
    none
  else
    match parsePublicKey v pkSeed pkRoot with
    | none => none
    | some pk =>
        match p.parseSignature v sigBytes with
        | none => none
        | some sig => verifyParsed p v pk message sig

theorem verifyBytes_eq_verifySpec
    (p : Primitives) (v : Variant)
    (pkSeed pkRoot message sigBytes : Bytes) :
    verifyBytes p v pkSeed pkRoot message sigBytes =
      verifySpec p v { pkSeed := pkSeed, pkRoot := pkRoot } message sigBytes := by
  unfold verifyBytes verifySpec parsePublicKey
  by_cases hLen : sigBytes.size ≠ v.sigBytes
  · simp [hLen]
  · simp [hLen]
    by_cases hPk : publicKeyOk v { pkSeed := pkSeed, pkRoot := pkRoot }
    · simp [hPk]
    · simp [hPk]

/--
Soundness of the algorithmic layer: when `verifyParsed` accepts, a concrete,
well-formed witness exists. The signature passes its shape check, the forced-zero
FORS guard holds, FORS reconstruction yields a public key, and the hypertree
  climb terminates in `.ok root` whose variant-specific byte projection matches
  the public-key root. This is the accept-direction stated as an existence claim
  about the reconstructed data, not merely as "did not revert".
-/
theorem verifyParsed_accepts_sound
    (p : Primitives) (v : Variant)
    (pk : PublicKey) (message : Bytes) (sig : Signature)
    (h : verifyParsed p v pk message sig = some true) :
    signatureShapeOk v sig = true ∧
    forcedZeroOk v (p.hMsg v pk sig.R message) = true ∧
    ∃ forsPk root,
      p.forsPkFromSig v pk (p.hMsg v pk sig.R message) sig.fors = some forsPk ∧
      foldHypertree p v pk (p.hMsg v pk sig.R message) forsPk sig.layers = .ok root ∧
      rootMatchesPk v root pk.pkRoot = true := by
  by_cases hShape : signatureShapeOk v sig = true
  · by_cases hZero : forcedZeroOk v (p.hMsg v pk sig.R message) = true
    · refine ⟨hShape, hZero, ?_⟩
      simp only [verifyParsed, hShape, hZero, not_true, if_false] at h
      split at h
      · simp at h
      · next forsPk hFors =>
          split at h
          · simp at h
          · simp at h
          · next root hFold =>
              exact ⟨forsPk, root, hFors, hFold, by simpa using h⟩
    · simp [verifyParsed, hShape, hZero] at h
  · simp [verifyParsed, hShape] at h

theorem verifyBytes_accepts_implies_parsed_accepts
    (p : Primitives) (v : Variant)
    (pkSeed pkRoot message sigBytes : Bytes) :
    verifyBytes p v pkSeed pkRoot message sigBytes = some true →
      ∃ pk sig,
        parsePublicKey v pkSeed pkRoot = some pk ∧
        p.parseSignature v sigBytes = some sig ∧
        verifyParsed p v pk message sig = some true := by
  intro h
  unfold verifyBytes at h
  split at h
  · contradiction
  · rename_i hLen
    cases hPk : parsePublicKey v pkSeed pkRoot with
    | none =>
        simp [hPk] at h
    | some pk =>
        cases hSig : p.parseSignature v sigBytes with
        | none =>
            simp [hPk, hSig] at h
        | some sig =>
            simp [hPk, hSig] at h
            exact ⟨pk, sig, rfl, rfl, h⟩

/--
Byte-level soundness: an accepting `verifyBytes` run exhibits a canonical public
key, a parsed signature, and the full well-formed witness from
`verifyParsed_accepts_sound`. This upgrades
`verifyBytes_accepts_implies_parsed_accepts` from "the parsed layer also accepts"
to "a concrete reconstructed root whose variant-specific projection matches
`pkRoot` exists".
-/
theorem verifyBytes_accepts_sound
    (p : Primitives) (v : Variant)
    (pkSeed pkRoot message sigBytes : Bytes)
    (h : verifyBytes p v pkSeed pkRoot message sigBytes = some true) :
    ∃ pk sig forsPk root,
      parsePublicKey v pkSeed pkRoot = some pk ∧
      p.parseSignature v sigBytes = some sig ∧
      signatureShapeOk v sig = true ∧
      forcedZeroOk v (p.hMsg v pk sig.R message) = true ∧
      p.forsPkFromSig v pk (p.hMsg v pk sig.R message) sig.fors = some forsPk ∧
      foldHypertree p v pk (p.hMsg v pk sig.R message) forsPk sig.layers = .ok root ∧
      rootMatchesPk v root pk.pkRoot = true := by
  obtain ⟨pk, sig, hPk, hSig, hParsed⟩ :=
    verifyBytes_accepts_implies_parsed_accepts p v pkSeed pkRoot message sigBytes h
  obtain ⟨hShape, hZero, forsPk, root, hFors, hFold, hRoot⟩ :=
    verifyParsed_accepts_sound p v pk message sig hParsed
  exact ⟨pk, sig, forsPk, root, hPk, hSig, hShape, hZero, hFors, hFold, hRoot⟩

/--
`verifyBytes` returns a normal result (does not revert) exactly when the
signature length is correct, the public key is canonical, the signature parses,
and the parsed verification does not itself revert. This pins the externally
observable revert boundary of the contract.
-/
theorem verifyBytes_isSome_iff
    (p : Primitives) (v : Variant)
    (pkSeed pkRoot message sigBytes : Bytes) :
    (verifyBytes p v pkSeed pkRoot message sigBytes).isSome ↔
      sigBytes.size = v.sigBytes ∧
      publicKeyOk v { pkSeed := pkSeed, pkRoot := pkRoot } = true ∧
      ∃ sig, p.parseSignature v sigBytes = some sig ∧
        (verifyParsed p v { pkSeed := pkSeed, pkRoot := pkRoot } message sig).isSome := by
  unfold verifyBytes parsePublicKey
  by_cases hLen : sigBytes.size = v.sigBytes
  · by_cases hPk : publicKeyOk v { pkSeed := pkSeed, pkRoot := pkRoot } = true
    · cases hSig : p.parseSignature v sigBytes with
      | none => simp [hLen, hPk]
      | some sig => simp [hLen, hPk]
    · simp [hLen, hPk]
  · simp [hLen]

/--
Contrapositive convenience form: a wrong signature length always reverts.
-/
theorem verifyBytes_bad_length
    (p : Primitives) (v : Variant)
    (pkSeed pkRoot message sigBytes : Bytes)
    (hLen : sigBytes.size ≠ v.sigBytes) :
    verifyBytes p v pkSeed pkRoot message sigBytes = none := by
  unfold verifyBytes
  simp [hLen]

/--
Refinement target for a Verity-modeled Solidity verifier. `exec` is the
observable model of `verify(pkSeed, pkRoot, message, sig)`: `none` means revert,
and `some b` means normal return with boolean `b`.
-/
def ImplementsByteVerifier
    (p : Primitives) (v : Variant)
    (exec : Bytes → Bytes → Bytes → Bytes → Option Bool) : Prop :=
  ∀ pkSeed pkRoot message sig,
    exec pkSeed pkRoot message sig = verifyBytes p v pkSeed pkRoot message sig

end ByteLevel

/--
Refinement target for a Verity-modeled Solidity verifier. `exec` is the
observable model of `verify(pkSeed, pkRoot, message, sig)`: `none` means revert,
and `some b` means normal return with boolean `b`.
-/
def ImplementsVerifier
    (p : Primitives) (v : Variant)
    (exec : PublicKey → Bytes → Bytes → Option Bool) : Prop :=
  ∀ pk message sig, exec pk message sig = verifySpec p v pk message sig

end SphincsMinusVerifierSpec
