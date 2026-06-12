/-
  C13BridgePrep — observation lemmas for the concrete `execC13Concrete`.

  The executable runner now lives in `ProofCore.lean`; this file packages the
  current accept and reject subdomain theorems into observed byte-spec equality
  results that the final `ByteLevel.ImplementsByteVerifier` theorem can consume.
-/

import SphincsMinusVerifiers.SegmentRejectSpec

namespace SphincsMinusVerifiers.C13BridgePrep

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifierSpec

/-- Observable verifier result for a completed source-semantics run.  Only the
EVM boolean words `0` and `1` are accepted as normal boolean returns; reverts map
to `none`, matching `ByteLevel.verifyBytes`. -/
def observeStmtResult (r : StmtResult) : Option Bool :=
  match r with
  | .return value _ =>
      if value = 0 then some false
      else if value = 1 then some true
      else none
  | .revert => none
  | .continue _ => none
  | .stop _ => none

/-- The concrete body runner, exposed under the bridge-prep name used by the
accept/reject slice lemmas.  It is definitionally the concrete `execC13Concrete` from
`ProofCore.lean`. -/
def runC13BodyObserved
    (pkSeed pkRoot message sig : ByteArray) : Option Bool :=
  execC13Concrete pkSeed pkRoot message sig

/-- On the C13 length-ok branch, byte-level
verification always reaches the parsed verifier.  The concrete parser cannot
fail for any other reason. -/
theorem c13_verifyBytes_eq_verifyParsed_of_length
    (pkSeed pkRoot message sig : ByteArray)
    (hLen : sig.size = c13.sigBytes) :
    ∃ sigParsed,
      C13Concrete.parseSignatureC13 c13 sig = some sigParsed ∧
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig =
        verifyParsed C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  obtain ⟨sigParsed, hParse⟩ :=
    C13Concrete.parseSignatureC13_some_of_size (v := c13) (sig := sig) hLen
  refine ⟨sigParsed, hParse, ?_⟩
  unfold ByteLevel.verifyBytes
  simp [hLen, C13Concrete.parsePublicKey_c13 pkSeed pkRoot,
    c13Primitives,
    C13Concrete.c13PrimitivesConcrete, hParse]

theorem observeStmtResult_return_boolWord
    (b : Bool) (st : RuntimeState) :
    observeStmtResult (.return (wordNormalize (boolWord b)) st) = some b := by
  cases b <;> rfl

theorem observeStmtResult_revert :
    observeStmtResult .revert = none := rfl

/-- Two-step current-node accept-side observed-result bridge.  This is the
bridge-facing form of the bounded C13 layer handoff: it only requires facts for
the concrete `layer = 0` and `layer = 1` states. -/
theorem runC13BodyObserved_accept_from_concrete_layer_current_node_two_step_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
        pkSeed pkRoot message sig sigParsed forsPk) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  rcases
    SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_concrete_layer_current_node_two_step_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold hObs with ⟨finalState, hSpec, hExec⟩
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_return_boolWord]
  have hLen : sig.size = c13.sigBytes :=
    C13Concrete.parseSignatureC13_size hParse
  unfold ByteLevel.verifyBytes
  simp [hLen, C13Concrete.parsePublicKey_c13 pkSeed pkRoot,
    c13Primitives,
    C13Concrete.c13PrimitivesConcrete, hParse]
  simpa [C13Concrete.c13PrimitivesConcrete] using hSpec.symm

/-- Bridge-facing accept theorem at the narrowed current-node boundary.  The
pure WOTS/XMSS facts are derived from `foldHypertree ... = .ok specRoot`; callers
only supply the two executable layer guards and the two post-step
`"currentNode"` equalities. -/
theorem runC13BodyObserved_accept_from_fold_ok_current_nodes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hGuard0 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk))
    (hGuard1 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        = C13Concrete.wordOfHash16 specRoot)
    (hPkRootSize : pkRoot.size = 16) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  exact
    runC13BodyObserved_accept_from_concrete_layer_current_node_two_step_obligations
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold
      (SegmentAcceptSpec.concrete_layer_current_node_two_step_obligations_of_fold_ok_current_nodes
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hFold hGuard0 hCurrent0 hGuard1 hCurrent1 hPkRootSize)

/-- Bridge-facing accept theorem with the final comparison exposed directly.
Unlike `runC13BodyObserved_accept_from_fold_ok_current_nodes`, this does not
require `pkRoot.size = 16`; callers provide the exact premise needed by the
final `currentNode == root` comparison.  This is the useful boundary for the
eventual all-input bridge, where compare-false cases cannot be hidden behind an
accept-only root-size roundtrip. -/
theorem runC13BodyObserved_accept_from_fold_ok_current_nodes_wordcmp
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hGuard0 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk))
    (hGuard1 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        = C13Concrete.wordOfHash16 specRoot)
    (hWordCmp :
      decide (C13Concrete.wordOfHash16 specRoot = C13Concrete.wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  let st := mkC13State pkSeed pkRoot message sig
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let specStep := SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
  have hTwo : wordNormalize 2 = 2 := by
    exact SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256)
  have hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed st) with
          bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
      0 (wordNormalize 2) := by
    rw [hTwo]
    unfold ClimbLoopGuarded.allGuardsPass
    refine ⟨?_, ?_⟩
    · simpa [st, CurrentNodeFrame.c13LayerLoopState0,
        CurrentNodeFrame.c13LayerStartState] using hGuard0
    · refine ⟨?_, True.intro⟩
      simpa [st, CurrentNodeFrame.c13LayerLoopState1,
        CurrentNodeFrame.c13LayerAfterStep0, CurrentNodeFrame.c13LayerLoopState0,
        CurrentNodeFrame.c13LayerStartState, Nat.zero_add] using hGuard1
  have hRoots :=
    CurrentNodeFrame.rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
      pk message sig hParse
  have hForsPkByte :
      forsPk = C13Concrete.hash16OfWord
        (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors =
        C13Concrete.wordOfHash16 forsPk := by
    rw [hForsPkByte]
    exact (SegmentAcceptSpec.forsPkWordC13_roundtrip pk digest sigParsed.fors).symm
  have hTd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13 digest := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_idxTree0_mkC13State pkSeed pkRoot message sig
  have hLd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13 digest := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_idxLeaf0_mkC13State pkSeed pkRoot message sig
  have hTltd : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
    C13Concrete.idxTree0C13_lt pk sigParsed.R message
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord (afterFors st) =
        C13Concrete.wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last
      pkSeed pkRoot message sig digest (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
      (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors) hTd hTltd hLd]
    · simpa [pk, digest, C13Concrete.forsPkWordC13] using hForsPkWord
    · intro j hj
      simpa [pk, digest] using hRoots.1 j hj
    · simpa [pk, digest] using hRoots.2
  have hForsPkFinal :
      lookupValue (afterFinalize st).bindings "forsPk" =
        C13Concrete.wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress st forsPk hForsCompress
  have hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot := by
    simpa [pk, digest, specStep] using
      SegmentAcceptSpec.specFold_c13HypertreeSpecStepAtLayer_eq_of_foldHypertree_ok
        pk digest forsPk specRoot sigParsed.layers hFold
  have hStep0 :
      CurrentNodeFrame.CurrentNodeRel C13Concrete.wordOfHash16
        (SegmentLayer3.stepLayer (CurrentNodeFrame.c13LayerLoopState0 st))
        (specStep 0 forsPk) := by
    change
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0 st)).bindings
          "currentNode" = C13Concrete.wordOfHash16 (specStep 0 forsPk)
    simpa [st, pk, digest, specStep] using hCurrent0
  have hStep1Node : specStep 1 (specStep 0 forsPk) = specRoot := by
    simpa [ClimbLoop.specFold, hTwo] using hSpecFold
  have hStep1 :
      CurrentNodeFrame.CurrentNodeRel C13Concrete.wordOfHash16
        (SegmentLayer3.stepLayer (CurrentNodeFrame.c13LayerLoopState1 st))
        (specStep 1 (specStep 0 forsPk)) := by
    change
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1 st)).bindings
          "currentNode" = C13Concrete.wordOfHash16 (specStep 1 (specStep 0 forsPk))
    rw [hStep1Node]
    simpa [st] using hCurrent1
  have hCurrent :
      lookupValue (afterLayer st).bindings "currentNode" =
        C13Concrete.wordOfHash16 specRoot :=
    CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_two_steps
      st specStep forsPk specRoot hForsPkFinal hStep0 hStep1 hSpecFold
  rcases
    SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_root
      pkSeed pkRoot message sig pk sigParsed forsPk specRoot rfl
      (C13Concrete.parseSignatureC13_shape hParse) hZero hFors hFold
      (SegmentAcceptSpec.c13_sig_length_of_parseSignatureC13
        pkSeed pkRoot message sig sigParsed hParse)
      (SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero
        pkSeed pkRoot message sig pk sigParsed rfl hParse hZero)
      (by simpa [st] using hgL)
      (by simpa [st] using hCurrent)
      hWordCmp with
    ⟨finalState, hSpec, hExec⟩
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_return_boolWord]
  have hLen : sig.size = c13.sigBytes :=
    C13Concrete.parseSignatureC13_size hParse
  unfold ByteLevel.verifyBytes
  simp [hLen, C13Concrete.parsePublicKey_c13 pkSeed pkRoot,
    c13Primitives,
    C13Concrete.c13PrimitivesConcrete, hParse]
  simpa [C13Concrete.c13PrimitivesConcrete] using hSpec.symm

/-- Bad-length observed-result bridge. -/
theorem runC13BodyObserved_revert_on_bad_length
    (pkSeed pkRoot message sig : ByteArray)
    (hlen : sig.size ≠ 3688) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  rcases SegmentRejectSpec.c13_revert_on_bad_length pkSeed pkRoot message sig hlen with
    ⟨hExec, hSpec⟩
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_revert, hSpec]

/-- Spec side for the C13 WOTS+C hard-revert branch: once bytes parse, the
signature shape and public-key checks are fixed, so a `.reverted` hypertree fold
is exactly byte-level `none`. -/
theorem c13_verifyBytes_none_of_fold_reverted
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted) :
    ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none := by
  have hLen : sig.size = c13.sigBytes :=
    C13Concrete.parseSignatureC13_size hParse
  have hShape : signatureShapeOk c13 sigParsed = true :=
    C13Concrete.parseSignatureC13_shape hParse
  have hZero' :
      forcedZeroOk c13
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true := by
    simpa [C13Concrete.c13PrimitivesConcrete] using hZero
  have hFors' :
      C13Concrete.forsPkFromSigC13 c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
        = some forsPk := by
    simpa [C13Concrete.c13PrimitivesConcrete] using hFors
  have hFold' :
      foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted := by
    simpa [C13Concrete.c13PrimitivesConcrete] using hFold
  have hFold'' :
      foldHypertree
        { parseSignature := C13Concrete.parseSignatureC13,
          hMsg := C13Concrete.hMsgC13,
          forsPkFromSig := C13Concrete.forsPkFromSigC13,
          wotsPkFromSig := C13Concrete.wotsPkFromSigC13,
          wotsPkFromSigAtLayer := C13Concrete.wotsPkFromSigC13AtLayer,
          wotsGrindingOk := C13Concrete.wotsGrindingOkC13,
          wotsGrindingOkAtLayer := C13Concrete.wotsGrindingOkC13AtLayer,
          xmssRootFromSig := C13Concrete.xmssRootFromSigC13,
          xmssRootFromSigAtLayer := C13Concrete.xmssRootFromSigC13AtLayer }
        c13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted := by
    simpa [C13Concrete.c13PrimitivesConcrete] using hFold'
  unfold ByteLevel.verifyBytes
  simp [hLen, C13Concrete.parsePublicKey_c13 pkSeed pkRoot,
    c13Primitives,
    C13Concrete.c13PrimitivesConcrete, hParse, verifyParsed, hShape, hZero',
    hFors', hFold'']

/-- Observed bridge for a first-layer WOTS+C checksum failure, paired with the
spec-side `.reverted` fold fact. -/
theorem runC13BodyObserved_revert_on_layer_first_guard_of_fold_reverted
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hg3 : SegmentS3.s3Guard
        (SegmentCompose.afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hguard :
      SegmentLayer3.layerGuard
        (ClimbLoopGuarded.loopState "layer"
          { (SegmentCompose.afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings :=
              bindValue
                (SegmentCompose.afterSeed
                  (mkC13State pkSeed pkRoot message sig)).bindings
                "layer" (wordNormalize 0) } 0)
        = false)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  have hLen :
      lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
        = wordNormalize 3688 := by
    rw [SegmentRejectSpec.mkC13State_lookup_sigLength]
    have hsz : sig.size = c13.sigBytes :=
      C13Concrete.parseSignatureC13_size hParse
    change sig.size = wordNormalize 3688
    rw [hsz]
    rfl
  have hExec :=
    SegmentRejectSpec.c13_body_reverts_on_layer_first_guard
      (mkC13State pkSeed pkRoot message sig) hLen
      (SegmentRejectSpec.mkC13State_pkSeed_canonical pkSeed pkRoot message sig)
      (SegmentRejectSpec.mkC13State_pkRoot_canonical pkSeed pkRoot message sig) hg3 hguard
  have hSpec :=
    c13_verifyBytes_none_of_fold_reverted
      pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_revert, hSpec]

/-- Observed bridge for a second-layer WOTS+C checksum failure, paired with the
spec-side `.reverted` fold fact. -/
theorem runC13BodyObserved_revert_on_layer_second_guard_of_fold_reverted
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hg3 : SegmentS3.s3Guard
        (SegmentCompose.afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hguard0 :
      SegmentLayer3.layerGuard
        (ClimbLoopGuarded.loopState "layer"
          { (SegmentCompose.afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings :=
              bindValue
                (SegmentCompose.afterSeed
                  (mkC13State pkSeed pkRoot message sig)).bindings
                "layer" (wordNormalize 0) } 0)
        = true)
    (hguard1 :
      SegmentLayer3.layerGuard
        (ClimbLoopGuarded.loopState "layer"
          (SegmentLayer3.stepLayer
            (ClimbLoopGuarded.loopState "layer"
              { (SegmentCompose.afterSeed (mkC13State pkSeed pkRoot message sig)) with
                bindings :=
                  bindValue
                    (SegmentCompose.afterSeed
                      (mkC13State pkSeed pkRoot message sig)).bindings
                    "layer" (wordNormalize 0) } 0))
          1)
        = false)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  have hLen :
      lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
        = wordNormalize 3688 := by
    rw [SegmentRejectSpec.mkC13State_lookup_sigLength]
    have hsz : sig.size = c13.sigBytes :=
      C13Concrete.parseSignatureC13_size hParse
    change sig.size = wordNormalize 3688
    rw [hsz]
    rfl
  have hExec :=
    SegmentRejectSpec.c13_body_reverts_on_layer_second_guard
      (mkC13State pkSeed pkRoot message sig) hLen
      (SegmentRejectSpec.mkC13State_pkSeed_canonical pkSeed pkRoot message sig)
      (SegmentRejectSpec.mkC13State_pkRoot_canonical pkSeed pkRoot message sig) hg3 hguard0 hguard1
  have hSpec :=
    c13_verifyBytes_none_of_fold_reverted
      pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_revert, hSpec]

/-- Forced-zero observed-result bridge on the parse-shaped reject subdomain. -/
theorem runC13BodyObserved_revert_on_forced_zero_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hg3 : SegmentS3.s3Guard
        (SegmentCompose.afterS2 (mkC13State pkSeed pkRoot message sig)) ≠ 0) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  rcases
    SegmentRejectSpec.c13_revert_on_forced_zero_of_parse
      pkSeed pkRoot message sig sigParsed hParse hg3 with ⟨hExec, hSpec⟩
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_revert, hSpec]

/-- Forced-zero observed-result bridge from the spec-side failed forced-zero
decision. -/
theorem runC13BodyObserved_revert_on_forced_zero_false_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = false) :
    runC13BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig := by
  rcases
    SegmentRejectSpec.c13_revert_on_forced_zero_false_of_parse
      pkSeed pkRoot message sig sigParsed hParse hZero with ⟨hExec, hSpec⟩
  unfold runC13BodyObserved execC13Concrete
  rw [hExec, SphincsMinusVerifiers.observeStmtResultBool_revert, hSpec]

/-! ## Axiom audit. -/

#print axioms observeStmtResult_return_boolWord
#print axioms c13_verifyBytes_eq_verifyParsed_of_length
#print axioms c13_verifyBytes_none_of_fold_reverted
#print axioms runC13BodyObserved_accept_from_concrete_layer_current_node_two_step_obligations
#print axioms runC13BodyObserved_accept_from_fold_ok_current_nodes
#print axioms runC13BodyObserved_accept_from_fold_ok_current_nodes_wordcmp
#print axioms runC13BodyObserved_revert_on_bad_length
#print axioms runC13BodyObserved_revert_on_layer_first_guard_of_fold_reverted
#print axioms runC13BodyObserved_revert_on_layer_second_guard_of_fold_reverted
#print axioms runC13BodyObserved_revert_on_forced_zero_of_parse
#print axioms runC13BodyObserved_revert_on_forced_zero_false_of_parse

end SphincsMinusVerifiers.C13BridgePrep
