/-
  C13 spec mirror (Phase-1 / Worker D).

  Goal: re-express `ByteLevel.verifyBytes c13PrimitivesConcrete c13` over the
  C13 variant as an explicit composition of NAMED INTERMEDIATES whose boundaries
  match the compiled model's segment map in
  `SphincsMinusVerifiers/INTERFACE_CONTRACT.md`:

      S2  H_msg digest               -> `c13DigestBytes`, `c13HtIndex`,
                                         `c13ForsIndices`
      S3  forced-zero guard          -> `c13ForcedZeroOk`
      S4  FORS+C reconstruction      -> `c13ForsRootBytes`
      Layer 3 (d=2) hypertree climb  -> per-layer `c13WotsPkBytes`,
                                         `c13XmssRootBytes`, the climb
                                         `c13HtClimb`, and `c13FinalRootBytes`.

  Then ONE composition theorem `verifyBytes_c13_eq_mirror` rewrites the whole
  `verifyBytes` body purely in terms of those named intermediates.  Every
  Phase-2 segment lemma's RHS will reference exactly one of these intermediates,
  so the segment proofs compose.

  Additive: imports `C13Concrete`, edits nothing in `Model.lean`/`Proofs.lean`.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifierSpec
namespace C13Mirror

open SphincsMinusVerifierSpec.C13Concrete
open SphincsMinusVerifierSpec.ByteLevel

/-- The C13 variant the mirror is evaluated at. -/
abbrev c13Variant : Variant := c13

/-- The concrete C13 primitives the mirror is evaluated at. -/
abbrev c13P : Primitives := c13PrimitivesConcrete

/-! ## S2 — H_msg digest and the indices it carries -/

/-- S2 result: the `H_msg` digest structure (FORS indices + hypertree index)
produced by the first keccak.  This is `(c13P).hMsg c13Variant pk R message`. -/
def c13Digest (pk : PublicKey) (R message : Bytes) : HMsg :=
  c13P.hMsg c13Variant pk R message

/-- S2 hypertree index `htIdx` (= `digest >> 133 & (2^22-1)`). -/
def c13HtIndex (pk : PublicKey) (R message : Bytes) : Nat :=
  (c13Digest pk R message).hyperIndex

/-- S3 FORS indices: the 7 nineteen-bit message indices. -/
def c13ForsIndices (pk : PublicKey) (R message : Bytes) : List Nat :=
  (c13Digest pk R message).forsIndex

/-- The `i`-th FORS index (S3 accessor). -/
def c13ForsIndex (pk : PublicKey) (R message : Bytes) (i : Nat) : Nat :=
  ((c13Digest pk R message).forsIndex[i]?).getD 0

/-- S3 forced-zero guard: the contract reverts when the 7th (forced-zero) FORS
index is non-zero.  This is `forcedZeroOk c13Variant digest`. -/
def c13ForcedZeroOk (pk : PublicKey) (R message : Bytes) : Bool :=
  forcedZeroOk c13Variant (c13Digest pk R message)

/-! ## S4 — FORS+C reconstruction -/

/-- S4 result: the FORS public key bytes, `forsPkFromSig` over the concrete C13
primitives.  `none` models the contract returning `false`. -/
def c13ForsRootBytes (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    Option Bytes :=
  c13P.forsPkFromSig c13Variant pk digest fors

/-! ## Layer 3 — per-layer WOTS / XMSS and the d=2 hypertree climb

C13 has `d = 2`.  Each layer of `foldHypertreeAux` does, in order:
  * split `idxTree` into `idxLeaf := idxTree % 2^subtreeH`,
    `nextTree := idxTree / 2^subtreeH`;
  * a WOTS+C grinding check (revert on miss);
  * `wotsPkFromSig`  -> `c13WotsPkBytes`  (S5 work, folded into the loop);
  * `xmssRootFromSig` -> `c13XmssRootBytes` (S6 work, folded into the loop);
  * recurse on the produced root with `layer+1`, `nextTree`.

`c13HtClimb` mirrors `foldHypertreeAux` exactly for these concrete primitives. -/

/-- Per-layer WOTS public key bytes (the contract's in-loop WOTS reconstruction).
`treeIdx`/`leafIdx` follow the spec's post-shift naming. -/
def c13WotsPkBytes (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node : Bytes) (wots : WotsSig) : Option Bytes :=
  c13P.wotsPkFromSig c13Variant pk treeIdx leafIdx node wots

/-- Per-layer XMSS auth-path root bytes (the contract's in-loop Merkle climb). -/
def c13XmssRootBytes (pk : PublicKey) (treeIdx leafIdx : Nat)
    (wotsPk : Bytes) (auth : List Bytes) : Option Bytes :=
  c13P.xmssRootFromSig c13Variant pk treeIdx leafIdx wotsPk auth

/-- Per-layer grinding-failure predicate (revert on a WOTS+C target miss). -/
def c13WotsGrindFails (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node : Bytes) (wots : WotsSig) : Bool :=
  wotsGrindingFails c13P c13Variant pk treeIdx leafIdx node wots

/-- The d=2 hypertree climb, mirroring `foldHypertreeAux` at the concrete C13
primitives.  `fuel`/`layer`/`idxTree`/`node` thread exactly as the spec's. -/
def c13HtClimb (pk : PublicKey) (fuel layer idxTree : Nat) (node : Bytes)
    (layers : List XmssLayerSig) : HyperResult :=
  foldHypertreeAux c13P c13Variant pk fuel layer idxTree node layers

/-- The full climb seeded as `foldHypertree` does: fuel `= d = 2`, layer 0,
starting from the hypertree index and the FORS public key. -/
def c13FinalRoot (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig) : HyperResult :=
  foldHypertree c13P c13Variant pk digest forsPk layers

/-- `c13FinalRoot` is literally `c13HtClimb` seeded at fuel 2 / layer 0 /
`digest.hyperIndex`.  (Definitional; recorded for the Phase-2 climb lemma.) -/
theorem c13FinalRoot_eq_climb (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (layers : List XmssLayerSig) :
    c13FinalRoot pk digest forsPk layers
      = c13HtClimb pk c13Variant.d 0 digest.hyperIndex forsPk layers := by
  rfl

/-- The S4-result accessor as `Option`, plus the climb, give the final root
bytes (when both reconstructions complete). -/
def c13FinalRootBytes (pk : PublicKey) (digest : HMsg)
    (fors : ForsSig) (layers : List XmssLayerSig) : Option Bytes :=
  match c13ForsRootBytes pk digest fors with
  | none => none
  | some forsPk =>
      match c13FinalRoot pk digest forsPk layers with
      | .ok root => some root
      | _ => none

/-! ## Composition

`c13VerifyParsedBody` is `verifyParsed c13P c13Variant pk message sig` rewritten
purely in terms of the named intermediates above.  The composition theorem
states the byte verifier equals this body once length / pubkey / parse succeed.

The structure mirrors the segment order:
  shapeOk guard (S1-ish parse shape) → forced-zero guard (S3) →
  FORS reconstruction (S4) → climb (Layer 3) → final compare. -/

/-- The parsed-verifier body re-expressed via the named intermediates.  This is
*definitionally* `verifyParsed c13P c13Variant pk message sig`; the theorem
`c13VerifyParsedBody_eq` records the equality and the explicit factoring. -/
def c13VerifyParsedBody (pk : PublicKey) (message : Bytes) (sig : Signature) :
    Option Bool :=
  let digest := c13Digest pk sig.R message
  if ¬ signatureShapeOk c13Variant sig then
    none
  else if ¬ c13ForcedZeroOk pk sig.R message then
    none
  else
    match c13ForsRootBytes pk digest sig.fors with
    | none => some false
    | some forsPk =>
        match c13HtClimb pk c13Variant.d 0 digest.hyperIndex forsPk sig.layers with
        | .reverted => none
        | .rejected => some false
        | .ok root => some (rootMatchesPk c13Variant root pk.pkRoot)

/-- The named-intermediate body equals the spec's `verifyParsed` for C13. -/
theorem c13VerifyParsedBody_eq (pk : PublicKey) (message : Bytes)
    (sig : Signature) :
    verifyParsed c13P c13Variant pk message sig
      = c13VerifyParsedBody pk message sig := by
  unfold verifyParsed c13VerifyParsedBody
  -- `c13Digest`, `c13ForcedZeroOk`, `foldHypertree`/`c13HtClimb` are all
  -- definitional unfoldings of the same terms.
  simp only [c13Digest, c13ForcedZeroOk, c13ForsRootBytes, c13HtClimb,
    foldHypertree]
  rfl

/-- **Composition theorem.**  The C13 byte verifier, once the length /
public-key / parse guards pass, equals the explicit composition of the named
intermediates `c13Digest` (S2) · `c13ForcedZeroOk` (S3) · `c13ForsRootBytes`
(S4) · the `c13HtClimb` hypertree climb (Layer 3) · the final root compare. -/
theorem verifyBytes_c13_eq_mirror
    (pkSeed pkRoot message sigBytes : Bytes) :
    verifyBytes c13P c13Variant pkSeed pkRoot message sigBytes
      = (if sigBytes.size ≠ c13Variant.sigBytes then none
         else match parsePublicKey c13Variant pkSeed pkRoot with
           | none => none
           | some pk =>
             match c13P.parseSignature c13Variant sigBytes with
             | none => none
             | some sig => c13VerifyParsedBody pk message sig) := by
  unfold verifyBytes
  by_cases hLen : sigBytes.size ≠ c13Variant.sigBytes
  · simp [hLen]
  · simp only [hLen, if_false]
    cases hPk : parsePublicKey c13Variant pkSeed pkRoot with
    | none => rfl
    | some pk =>
        cases hSig : c13P.parseSignature c13Variant sigBytes with
        | none => rfl
        | some sig => exact c13VerifyParsedBody_eq pk message sig

end C13Mirror
end SphincsMinusVerifierSpec
