/-
  CurrentNodeFrame — structural adapters for the left operand of C13's final
  `currentNode == root` comparison.

  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool_from_root` reduces the
  remaining accept-path data obligation to:

      lookupValue (afterLayer (mkC13State ...)).bindings "currentNode"
        = wordOfHash16 specRoot

  This file packages the pure loop-composition part of that obligation.  It does
  not prove the per-layer WOTS/XMSS keccak correspondence; instead it shows that
  once a one-layer correspondence is available, the existing `afterLayer` fold
  carries it from the `afterSeed` start state to the final comparison operand.

  No `execC13`, no bridge axiom, no `sorry`, no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentCompose
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifiers.SegmentS2R
import SphincsMinusVerifiers.SegmentS4Fors
import SphincsMinusVerifiers.SegmentS4ForsMerkleFrame
import SphincsMinusVerifiers.SegmentS4Finalize
import SphincsMinusVerifiers.SegmentSeed
import SphincsMinusVerifiers.SegmentLayer3
import SphincsMinusVerifiers.KeccakBridge
import SphincsMinusVerifiers.SiblingCalldata
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.CurrentNodeFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.ClimbKit (N_MASK)
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete (adrsForsRootsC13 keccakWords maskN nMask wordOfHash16)

private theorem calldataloadWord_lt_of_ge4 (sel : Nat) (cd : List Nat) (off : Nat)
    (hoff : 4 ≤ off) :
    Compiler.Proofs.YulGeneration.calldataloadWord sel cd off < 2 ^ 256 := by
  have hmod : (0 : Nat) < Compiler.Constants.evmModulus := by
    show 0 < 2 ^ 256; positivity
  unfold Compiler.Proofs.YulGeneration.calldataloadWord
  rw [if_neg (by omega : ¬ off = 0), if_neg (by omega : ¬ off < 4)]
  show (if _ then _ else _) < Compiler.Constants.evmModulus
  split
  · exact Nat.mod_lt _ hmod
  · exact Nat.mod_lt _ hmod

/-! ## Seed boundary. -/

/-- The S2 H_msg block writes the public seed word to scratch slot `0x00` in the
frozen entry state. -/
theorem afterS2_seed_slot_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    ((afterS2 (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed :=
  SegmentS2.s2Step_seed_mkC13State pkSeed pkRoot message sig

/-- S3 only updates bindings, so it preserves the seed scratch cell written by
S2. -/
theorem afterS3_seed_slot_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    ((afterS3 (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  unfold afterS3 SegmentS3.stepS3
  exact afterS2_seed_slot_mkC13State pkSeed pkRoot message sig

/-! ## Static calldata-frame bindings. -/

/-- S2 reads `"sig_data_offset"` to load `R`, but does not rebind the ABI-local
itself. -/
theorem s2Step_preserves_sig_data_offset (st : RuntimeState) :
    lookupValue (SegmentS2.s2Step st).bindings "sig_data_offset"
      = lookupValue st.bindings "sig_data_offset" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sig_data_offset" SegmentS2.s2Body st (SegmentS2.s2Step st) ?_ (SegmentS2.execS2 st)
  intro s s'' stmt hmem hexec
  simp [SegmentS2.s2Body] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "seed" "sig_data_offset" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "root" "sig_data_offset" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sig_data_offset" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "R" "sig_data_offset" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sig_data_offset" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sig_data_offset" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sig_data_offset" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sig_data_offset" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "digest" "sig_data_offset" _ (by decide) hexec

/-- S2 may read calldata and write memory/bindings, but it preserves the static
selector and calldata image. -/
theorem s2Step_preserves_selector_calldata (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st (SegmentS2.s2Step st) := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    SegmentS2.s2Body st (SegmentS2.s2Step st) ?_ (SegmentS2.execS2 st)
  intro s s'' stmt hmem hexec
  simp [SegmentS2.s2Body] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "seed" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "root" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "R" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "digest" _ hexec

/-- Frozen-entry S2 keeps the ABI signature-data offset at `164`. -/
theorem afterS2_sig_data_offset_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterS2 (mkC13State pkSeed pkRoot message sig)).bindings
        "sig_data_offset" = sigDataOffset := by
  unfold afterS2
  rw [s2Step_preserves_sig_data_offset]
  rfl

/-- S3 binds `"sigBase"` from the preserved ABI signature-data offset. -/
theorem afterS3_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterS3 (mkC13State pkSeed pkRoot message sig)).bindings
        "sigBase" = sigDataOffset := by
  unfold afterS3 SegmentS3.stepS3
  rw [MemoryKit.lookupValue_bindValue_self]
  exact afterS2_sig_data_offset_mkC13State pkSeed pkRoot message sig

/-- S3 binds `"htIdx"` to the concrete C13 `H_msg` hypertree index. -/
theorem afterS3_htIdx_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterS3 (mkC13State pkSeed pkRoot message sig)).bindings "htIdx"
      =
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.read16 sig 0) message).hyperIndex := by
  let digest :=
    keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot,
      wordOfHash16 (C13Concrete.read16 sig 0), C13Concrete.baToNatBE message % C13Concrete.wordMod,
      C13Concrete.hMsgPad ]
  have hdigest :
      lookupValue (afterS2 (mkC13State pkSeed pkRoot message sig)).bindings "digest"
        = digest := by
    dsimp [digest]
    exact SphincsMinusVerifiers.SegmentS2R.s2_digest_mkC13State_final
      pkSeed pkRoot message sig
  unfold afterS3 SegmentS3.stepS3
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigBase" "htIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "dVal" "htIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hBound : digest < 2 ^ 256 := by
    dsimp [digest]
    simpa [Compiler.Constants.evmModulus] using
      KeccakBridge.keccakWords_lt
        [ wordOfHash16 pkSeed, wordOfHash16 pkRoot,
          wordOfHash16 (C13Concrete.read16 sig 0),
          C13Concrete.baToNatBE message % C13Concrete.wordMod, C13Concrete.hMsgPad ]
  rw [SegmentS3.htIdxVal_eq_hyperIndex
    (afterS2 (mkC13State pkSeed pkRoot message sig)) digest hdigest hBound]
  rfl

/-- Frozen-entry S2 preserves the static selector and calldata image installed by
`mkC13State`. -/
theorem afterS2_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterS2 (mkC13State pkSeed pkRoot message sig)).selector = 0
      ∧ (afterS2 (mkC13State pkSeed pkRoot message sig)).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold afterS2
  have h := s2Step_preserves_selector_calldata (mkC13State pkSeed pkRoot message sig)
  exact ⟨by rw [h.1]; rfl, by rw [h.2]; rfl⟩

/-- S3 only updates bindings, so it preserves the static selector/calldata frame
from S2. -/
theorem afterS3_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterS3 (mkC13State pkSeed pkRoot message sig)).selector = 0
      ∧ (afterS3 (mkC13State pkSeed pkRoot message sig)).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold afterS3 SegmentS3.stepS3
  exact afterS2_selector_calldata_mkC13State pkSeed pkRoot message sig

/-! ### The FIPS FORS pre-loop setup over the byte-facing entry state.

Statements 13..15 hoist the `idxLeaf0`/`idxTree0` digits and the FIPS ADRS base
`forsBase` between S3 and the FORS outer loop (`SegmentCompose.afterForsSetup`).
These project the S3-level frame facts through the three pure binder writes. -/

theorem afterForsSetup_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "sigBase" = sigDataOffset := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_preserves_sigBase_step]
  exact afterS3_sigBase_mkC13State pkSeed pkRoot message sig

theorem afterForsSetup_htIdx_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings "htIdx"
      =
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.read16 sig 0) message).hyperIndex := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_preserves_htIdx_step]
  exact afterS3_htIdx_mkC13State pkSeed pkRoot message sig

theorem afterForsSetup_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterForsSetup (mkC13State pkSeed pkRoot message sig)).selector = 0
      ∧ (afterForsSetup (mkC13State pkSeed pkRoot message sig)).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold afterForsSetup
  have h := SegmentForsSetup.stepForsSetup_preserves_selector_calldata_step
    (afterS3 (mkC13State pkSeed pkRoot message sig))
  have hS3 := afterS3_selector_calldata_mkC13State pkSeed pkRoot message sig
  exact ⟨h.1.trans hS3.1, h.2.trans hS3.2⟩

theorem afterForsSetup_seed_slot_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    ((afterForsSetup (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_preserves_memory_step]
  exact afterS3_seed_slot_mkC13State pkSeed pkRoot message sig

/-- The hoisted FIPS ADRS base over the byte-facing entry state is exactly the
digest-derived `adrsForsBase (idxTree0C13 d) (idxLeaf0C13 d)`. -/
theorem afterForsSetup_forsBase_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13
            (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message))
          (C13Concrete.idxLeaf0C13
            (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message)) := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_forsBase_eq
    (afterS3 (mkC13State pkSeed pkRoot message sig))
    ((C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.read16 sig 0) message).hyperIndex)
    (afterS3_htIdx_mkC13State pkSeed pkRoot message sig)
    (C13Concrete.hMsgC13_hyperIndex_lt _ _ _)]
  rfl

/-- Concrete C13 FORS outer-loop prefix state, with the same initial `"i"` bind
used by `afterFors`. -/
def forsOuterPrefixState
    (pkSeed pkRoot message sig : ByteArray) (n : Nat) : RuntimeState :=
  ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
          "i" (wordNormalize 0) }
    0 n

/-- The actual state handed to the next concrete FORS leaf step after the outer
loop has reached prefix length `t`.  Naming this state keeps the prefix-local
lemmas from repeatedly expanding the rebound record expression. -/
def forsOuterLeafState
    (pkSeed pkRoot message sig : ByteArray) (t : Nat) : RuntimeState :=
  { (forsOuterPrefixState pkSeed pkRoot message sig t) with
    bindings :=
      bindValue (forsOuterPrefixState pkSeed pkRoot message sig t).bindings
        "i" (wordNormalize t) }

/-- The C13 FORS auth-path calldata word reader for tree `t` and climb height
`h`, in the same `Nat → Nat` shape used by `MerkleClimbData`. -/
def forsAuthCdAt
    (pkSeed pkRoot message sig : ByteArray) (t h : Nat) : Nat :=
  Compiler.Proofs.YulGeneration.calldataloadWord 0
    (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
    (sigDataOffset + (128 + 304 * t) + 16 * h)

/-- Every concrete prefix of the C13 FORS outer loop carries the signature-base
binding installed by S3.  This is the local frame needed to apply the concrete
FORS setup theorem at an actual outer-loop state, rather than at an arbitrary
`RuntimeState`. -/
theorem forsOuterPrefix_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (n : Nat) :
    lookupValue (forsOuterPrefixState pkSeed pkRoot message sig n).bindings
        "sigBase" = sigDataOffset := by
  unfold forsOuterPrefixState
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "sigBase"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_sigBase
        _ 0 n]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "sigBase" (wordNormalize 0) (by decide)]
  exact afterForsSetup_sigBase_mkC13State pkSeed pkRoot message sig

/-- Every concrete prefix of the C13 FORS outer loop carries the hoisted FIPS
ADRS base installed by the fors-setup segment. -/
theorem forsOuterPrefix_forsBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (n : Nat) :
    lookupValue (forsOuterPrefixState pkSeed pkRoot message sig n).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13
            (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message))
          (C13Concrete.idxLeaf0C13
            (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message)) := by
  unfold forsOuterPrefixState
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "forsBase"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_forsBase
        _ 0 n]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "forsBase" (wordNormalize 0) (by decide)]
  exact afterForsSetup_forsBase_mkC13State pkSeed pkRoot message sig

/-- Every concrete prefix of the C13 FORS outer loop carries the frozen selector
and calldata image from the byte-facing `mkC13State`. -/
theorem forsOuterPrefix_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (n : Nat) :
    (forsOuterPrefixState pkSeed pkRoot message sig n).selector = 0
      ∧ (forsOuterPrefixState pkSeed pkRoot message sig n).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold forsOuterPrefixState
  have hfold := SphincsMinusVerifiers.StateFrame.foldLoop_preserves_selector_calldata
    "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_selector_calldata
    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
        bindings :=
          bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
            "i" (wordNormalize 0) }
    0 n
  have hS3 := afterForsSetup_selector_calldata_mkC13State pkSeed pkRoot message sig
  exact ⟨by rw [hfold.1]; exact hS3.1, by rw [hfold.2]; exact hS3.2⟩

/-- At every actual C13 FORS outer-loop prefix in the six-iteration range, the
state about to enter the next concrete leaf step has the local setup facts needed
by the FORS frozen-site lemmas: the rebound loop index, the S3 `sigBase`, and the
frozen selector/calldata image from `mkC13State`. -/
theorem forsOuterPrefix_leafSetupFacts_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (t : Nat) (ht : t < 6) :
    let st :=
      { (forsOuterPrefixState pkSeed pkRoot message sig t) with
        bindings :=
          bindValue (forsOuterPrefixState pkSeed pkRoot message sig t).bindings
            "i" (wordNormalize t) }
    lookupValue st.bindings "i" = t
      ∧ lookupValue st.bindings "sigBase" = sigDataOffset
      ∧ st.selector = 0
      ∧ st.world.calldata = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
      ∧ lookupValue st.bindings "forsBase"
          = C13Concrete.adrsForsBase
              (C13Concrete.idxTree0C13
                (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C13Concrete.read16 sig 0) message))
              (C13Concrete.idxLeaf0C13
                (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C13Concrete.read16 sig 0) message)) := by
  intro st
  let pref := forsOuterPrefixState pkSeed pkRoot message sig t
  have hi :
      lookupValue (bindValue pref.bindings "i" (wordNormalize t)) "i" = t := by
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_trans ht (by decide))]
  have hsigBase :
      lookupValue pref.bindings "sigBase" = sigDataOffset := by
    dsimp [pref]
    exact forsOuterPrefix_sigBase_mkC13State pkSeed pkRoot message sig t
  have hsc := forsOuterPrefix_selector_calldata_mkC13State pkSeed pkRoot message sig t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [st, pref]
    exact hi
  · dsimp [st, pref]
    rw [MemoryKit.lookupValue_bindValue_ne
      (forsOuterPrefixState pkSeed pkRoot message sig t).bindings
      "i" "sigBase" (wordNormalize t) (by decide)]
    exact hsigBase
  · dsimp [st, pref] at hsc ⊢
    exact hsc.1
  · dsimp [st, pref] at hsc ⊢
    exact hsc.2
  · dsimp [st, pref]
    rw [MemoryKit.lookupValue_bindValue_ne
      (forsOuterPrefixState pkSeed pkRoot message sig t).bindings
      "i" "forsBase" (wordNormalize t) (by decide)]
    exact forsOuterPrefix_forsBase_mkC13State pkSeed pkRoot message sig t

/-- Named-state projection of `forsOuterPrefix_leafSetupFacts_mkC13State`. -/
theorem forsOuterLeafState_setupFacts_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (t : Nat) (ht : t < 6) :
    lookupValue (forsOuterLeafState pkSeed pkRoot message sig t).bindings "i" = t
      ∧ lookupValue (forsOuterLeafState pkSeed pkRoot message sig t).bindings
          "sigBase" = sigDataOffset
      ∧ (forsOuterLeafState pkSeed pkRoot message sig t).selector = 0
      ∧ (forsOuterLeafState pkSeed pkRoot message sig t).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
      ∧ lookupValue (forsOuterLeafState pkSeed pkRoot message sig t).bindings "forsBase"
          = C13Concrete.adrsForsBase
              (C13Concrete.idxTree0C13
                (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C13Concrete.read16 sig 0) message))
              (C13Concrete.idxLeaf0C13
                (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C13Concrete.read16 sig 0) message)) := by
  simpa [forsOuterLeafState] using
    forsOuterPrefix_leafSetupFacts_mkC13State pkSeed pkRoot message sig t ht

/-- One actual C13 FORS outer-loop prefix preserves the seed scratch slot through
the next concrete leaf step. -/
theorem forsLeafStep_preserves_seed_slot_of_mkC13State_prefix
    (pkSeed pkRoot message sig : ByteArray) (t : Nat) (ht : t < 6) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (forsOuterLeafState pkSeed pkRoot message sig t)).world.memory 0).val
      = ((forsOuterLeafState pkSeed pkRoot message sig t).world.memory 0).val := by
  rcases forsOuterLeafState_setupFacts_mkC13State pkSeed pkRoot message sig t ht with
    ⟨hi, hsigBase, hsel, hcd, hbase⟩
  exact
    SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_of_forsFrozenSetup
      (forsOuterLeafState pkSeed pkRoot message sig t)
      t _ pkSeed pkRoot message sig hi ht hsigBase hbase
      (lt_trans
        (C13Concrete.adrsForsBase_lt_of_bounds
          (lt_trans (C13Concrete.idxTree0C13_lt _ _ _) (by decide))
          (lt_trans (C13Concrete.idxLeaf0C13_lt _) (by decide)))
        (by decide))
      hsel hcd

/-- One actual C13 FORS outer-loop prefix preserves a different ordinary root
slot through the next concrete leaf step. -/
theorem forsLeafStep_preserves_root_cell_ne_of_mkC13State_prefix
    (pkSeed pkRoot message sig : ByteArray) (j t : Nat) (ht : t < 6) (hne : j ≠ t) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (forsOuterLeafState pkSeed pkRoot message sig t)).world.memory
        (0x80 + 32 * j)).val
      = ((forsOuterLeafState pkSeed pkRoot message sig t).world.memory
          (0x80 + 32 * j)).val := by
  rcases forsOuterLeafState_setupFacts_mkC13State pkSeed pkRoot message sig t ht with
    ⟨hi, hsigBase, hsel, hcd, hbase⟩
  exact
    SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup
      (forsOuterLeafState pkSeed pkRoot message sig t)
      j t _ pkSeed pkRoot message sig hi ht hne hsigBase hbase
      (lt_trans
        (C13Concrete.adrsForsBase_lt_of_bounds
          (lt_trans (C13Concrete.idxTree0C13_lt _ _ _) (by decide))
          (lt_trans (C13Concrete.idxLeaf0C13_lt _) (by decide)))
        (by decide))
      hsel hcd

/-- Concrete one-step carry for an ordinary FORS root slot across a non-writing
outer iteration. -/
theorem forsOuterPrefix_root_cell_succ_ne_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (j t : Nat) (ht : t < 6) (hne : j ≠ t) :
    ((forsOuterPrefixState pkSeed pkRoot message sig (t + 1)).world.memory
        (0x80 + 32 * j)).val
      = ((forsOuterPrefixState pkSeed pkRoot message sig t).world.memory
          (0x80 + 32 * j)).val := by
  let start :=
    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
          "i" (wordNormalize 0) }
  have hsplit :=
    ClimbLoop.foldLoop_append "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
      start 0 t 1
  calc
    ((forsOuterPrefixState pkSeed pkRoot message sig (t + 1)).world.memory
        (0x80 + 32 * j)).val
        =
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          (forsOuterLeafState pkSeed pkRoot message sig t)).world.memory
          (0x80 + 32 * j)).val := by
        simpa [forsOuterPrefixState, forsOuterLeafState, start,
          ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_zero, Nat.zero_add] using
          congrArg (fun st => ((st.world.memory (0x80 + 32 * j)).val)) hsplit
    _ = ((forsOuterLeafState pkSeed pkRoot message sig t).world.memory
          (0x80 + 32 * j)).val :=
        forsLeafStep_preserves_root_cell_ne_of_mkC13State_prefix
          pkSeed pkRoot message sig j t ht hne
    _ = ((forsOuterPrefixState pkSeed pkRoot message sig t).world.memory
          (0x80 + 32 * j)).val := rfl

/-- After concrete FORS iteration `j` has written root slot `j`, every later
concrete outer prefix up to the six-iteration endpoint preserves that slot. -/
theorem forsOuterPrefix_root_cell_suffix_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (j k : Nat)
    (hk : j + 1 + k ≤ 6) :
    ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1 + k)).world.memory
        (0x80 + 32 * j)).val
      = ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1)).world.memory
          (0x80 + 32 * j)).val := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have ht : j + 1 + k < 6 := by omega
      have hne : j ≠ j + 1 + k := by omega
      have hidx : j + 1 + (k + 1) = (j + 1 + k) + 1 := by omega
      calc
        ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1 + (k + 1))).world.memory
            (0x80 + 32 * j)).val
            =
          ((forsOuterPrefixState pkSeed pkRoot message sig ((j + 1 + k) + 1)).world.memory
            (0x80 + 32 * j)).val := by rw [hidx]
        _ = ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1 + k)).world.memory
              (0x80 + 32 * j)).val :=
            forsOuterPrefix_root_cell_succ_ne_mkC13State
              pkSeed pkRoot message sig j (j + 1 + k) ht hne
        _ = ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1)).world.memory
              (0x80 + 32 * j)).val :=
            ih (by omega)

/-- The concrete prefix immediately after FORS iteration `j` has root slot `j`
equal to the post-inner-climb `"node"` word from that iteration. -/
theorem forsOuterPrefix_root_cell_iteration_node_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) (hj : j < 6) :
    ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1)).world.memory
        (0x80 + 32 * j)).val
      =
    wordNormalize
      (lookupValue
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
            (forsOuterLeafState pkSeed pkRoot message sig j))).bindings "node") := by
  let start :=
    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
          "i" (wordNormalize 0) }
  have hsplit :=
    ClimbLoop.foldLoop_append "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
      start 0 j 1
  rcases forsOuterLeafState_setupFacts_mkC13State pkSeed pkRoot message sig j hj with
    ⟨hi, _, _, _⟩
  calc
    ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1)).world.memory
        (0x80 + 32 * j)).val
        =
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          (forsOuterLeafState pkSeed pkRoot message sig j)).world.memory
          (0x80 + 32 * j)).val := by
        simpa [forsOuterPrefixState, forsOuterLeafState, start,
          ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_zero, Nat.zero_add] using
          congrArg (fun st => ((st.world.memory (0x80 + 32 * j)).val)) hsplit
    _ =
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pkSeed pkRoot message sig j))).bindings "node") :=
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_root_cell_range
          (forsOuterLeafState pkSeed pkRoot message sig j) j hj hi

/-- `afterFors` over the byte-facing C13 entry state is exactly the six-step
concrete outer prefix. -/
theorem afterFors_eq_forsOuterPrefixState_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    afterFors (mkC13State pkSeed pkRoot message sig)
      = forsOuterPrefixState pkSeed pkRoot message sig 6 := by
  unfold afterFors forsOuterPrefixState
  have h6 : wordNormalize 6 = 6 := by
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  rw [h6]

/-- Every in-range concrete C13 FORS outer-loop prefix preserves the seed
scratch slot installed by S2/S3. -/
theorem forsOuterPrefix_seed_slot_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (n : Nat) (hn : n ≤ 6) :
    ((forsOuterPrefixState pkSeed pkRoot message sig n).world.memory 0).val
      = wordOfHash16 pkSeed := by
  let start :=
    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
          "i" (wordNormalize 0) }
  induction n with
  | zero =>
      dsimp [forsOuterPrefixState, start]
      exact afterForsSetup_seed_slot_mkC13State pkSeed pkRoot message sig
  | succ n ih =>
      have hnlt : n < 6 := by omega
      have hsplit :=
        ClimbLoop.foldLoop_append "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          start 0 n 1
      calc
        ((forsOuterPrefixState pkSeed pkRoot message sig (n + 1)).world.memory 0).val
            =
          ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
              (forsOuterLeafState pkSeed pkRoot message sig n)).world.memory 0).val := by
            simpa [forsOuterPrefixState, forsOuterLeafState, start,
              ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_zero, Nat.zero_add] using
              congrArg (fun st => ((st.world.memory 0).val)) hsplit
        _ = ((forsOuterLeafState pkSeed pkRoot message sig n).world.memory 0).val :=
          forsLeafStep_preserves_seed_slot_of_mkC13State_prefix
            pkSeed pkRoot message sig n hnlt
        _ = ((forsOuterPrefixState pkSeed pkRoot message sig n).world.memory 0).val := rfl
        _ = wordOfHash16 pkSeed := ih (by omega)

/-- Concrete frozen-entry FORS seed-cell preservation, with the range-gated leaf
premise discharged for the actual six C13 outer-loop prefix states. -/
theorem afterFors_seed_slot_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_eq_forsOuterPrefixState_mkC13State]
  exact forsOuterPrefix_seed_slot_mkC13State pkSeed pkRoot message sig 6 (by omega)

/-- The FORS outer loop carries the signature base binding unchanged. -/
theorem afterFors_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings
        "sigBase" = sigDataOffset := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "sigBase"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_sigBase
        _ 0 (wordNormalize 6)]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "sigBase" (wordNormalize 0) (by decide)]
  exact afterForsSetup_sigBase_mkC13State pkSeed pkRoot message sig

/-- The hoisted FIPS ADRS base survives the FORS outer loop. -/
theorem afterFors_forsBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13
            (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message))
          (C13Concrete.idxLeaf0C13
            (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message)) := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "forsBase"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_forsBase
        _ 0 (wordNormalize 6)]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "forsBase" (wordNormalize 0) (by decide)]
  exact afterForsSetup_forsBase_mkC13State pkSeed pkRoot message sig

/-- The hoisted FIPS tree digit over the byte-facing entry state. -/
theorem afterForsSetup_idxTree0_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
      = C13Concrete.idxTree0C13
          (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message) := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_idxTree0
    (afterS3 (mkC13State pkSeed pkRoot message sig))
    ((C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.read16 sig 0) message).hyperIndex)
    (afterS3_htIdx_mkC13State pkSeed pkRoot message sig)
    (C13Concrete.hMsgC13_hyperIndex_lt _ _ _)]
  rfl

/-- The hoisted FIPS leaf digit over the byte-facing entry state. -/
theorem afterForsSetup_idxLeaf0_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
      = C13Concrete.idxLeaf0C13
          (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message) := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_idxLeaf0
    (afterS3 (mkC13State pkSeed pkRoot message sig))
    ((C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.read16 sig 0) message).hyperIndex)
    (afterS3_htIdx_mkC13State pkSeed pkRoot message sig)
    (C13Concrete.hMsgC13_hyperIndex_lt _ _ _)]
  rfl

/-- The FIPS tree digit survives the FORS outer loop. -/
theorem afterFors_idxTree0_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
      = C13Concrete.idxTree0C13
          (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message) := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "idxTree0"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_idxTree0
        _ 0 (wordNormalize 6)]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "idxTree0" (wordNormalize 0) (by decide)]
  exact afterForsSetup_idxTree0_mkC13State pkSeed pkRoot message sig

/-- The FIPS leaf digit survives the FORS outer loop. -/
theorem afterFors_idxLeaf0_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
      = C13Concrete.idxLeaf0C13
          (C13Concrete.hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.read16 sig 0) message) := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "idxLeaf0"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_idxLeaf0
        _ 0 (wordNormalize 6)]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "idxLeaf0" (wordNormalize 0) (by decide)]
  exact afterForsSetup_idxLeaf0_mkC13State pkSeed pkRoot message sig

/-- The FORS outer loop carries the digest-derived hypertree index unchanged. -/
theorem afterFors_htIdx_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings
        "htIdx"
      =
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.read16 sig 0) message).hyperIndex := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "htIdx"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_htIdx
        _ 0 (wordNormalize 6)]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "htIdx" (wordNormalize 0) (by decide)]
  exact afterForsSetup_htIdx_mkC13State pkSeed pkRoot message sig

/-- The FORS outer loop carries the frozen selector and calldata image unchanged. -/
theorem afterFors_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterFors (mkC13State pkSeed pkRoot message sig)).selector = 0
      ∧ (afterFors (mkC13State pkSeed pkRoot message sig)).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold afterFors
  have hfold := SphincsMinusVerifiers.StateFrame.foldLoop_preserves_selector_calldata
    "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_selector_calldata
    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
        bindings := bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
          "i" (wordNormalize 0) }
    0 (wordNormalize 6)
  have hS3 := afterForsSetup_selector_calldata_mkC13State pkSeed pkRoot message sig
  exact ⟨by rw [hfold.1]; exact hS3.1, by rw [hfold.2]; exact hS3.2⟩

/-- Selector projection of `afterFors_selector_calldata_mkC13State`. -/
theorem afterFors_selector_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterFors (mkC13State pkSeed pkRoot message sig)).selector = 0 :=
  (afterFors_selector_calldata_mkC13State pkSeed pkRoot message sig).1

/-- Calldata-image projection of `afterFors_selector_calldata_mkC13State`. -/
theorem afterFors_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterFors (mkC13State pkSeed pkRoot message sig)).world.calldata
      = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig :=
  (afterFors_selector_calldata_mkC13State pkSeed pkRoot message sig).2

theorem forsFinalizeStep_preserves_sigBase (st : RuntimeState) :
    lookupValue (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep st).bindings
      "sigBase" = lookupValue st.bindings "sigBase" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigBase" SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeBody st
    (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep st) ?_
    (SphincsMinusVerifiers.SegmentS4Finalize.execForsFinalize st)
  intro s s'' stmt hmem hexec
  refine SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeBody_mem_cases
    (P := fun stmt => execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "sigBase" = lookupValue s.bindings "sigBase")
    hmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "lastSecret" "sigBase" _ (by decide) hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" _ _ hexec
  · intro hexec
    refine SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "i" "sigBase" _ SphincsMinusVerifiers.SegmentS4Finalize.forsCopyBody
      s s'' (by decide) ?_ hexec
    intro s0 s1 copyStmt hcopy hcopyExec
    refine SphincsMinusVerifiers.SegmentS4Finalize.forsCopyBody_mem_cases
      (P := fun copyStmt => execStmt [] s0 copyStmt = .continue s1 →
        lookupValue s1.bindings "sigBase" = lookupValue s0.bindings "sigBase")
      hcopy ?_ hcopyExec
    intro hcopyExec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s0 s1 "sigBase" _ _ hcopyExec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "forsPk" "sigBase" _ (by decide) hexec

theorem forsFinalizeStep_preserves_htIdx (st : RuntimeState) :
    lookupValue (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep st).bindings
      "htIdx" = lookupValue st.bindings "htIdx" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "htIdx" SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeBody st
    (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep st) ?_
    (SphincsMinusVerifiers.SegmentS4Finalize.execForsFinalize st)
  intro s s'' stmt hmem hexec
  refine SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeBody_mem_cases
    (P := fun stmt => execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "htIdx" = lookupValue s.bindings "htIdx")
    hmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "lastSecret" "htIdx" _ (by decide) hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec
  · intro hexec
    refine SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "i" "htIdx" _ SphincsMinusVerifiers.SegmentS4Finalize.forsCopyBody
      s s'' (by decide) ?_ hexec
    intro s0 s1 copyStmt hcopy hcopyExec
    refine SphincsMinusVerifiers.SegmentS4Finalize.forsCopyBody_mem_cases
      (P := fun copyStmt => execStmt [] s0 copyStmt = .continue s1 →
        lookupValue s1.bindings "htIdx" = lookupValue s0.bindings "htIdx")
      hcopy ?_ hcopyExec
    intro hcopyExec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s0 s1 "htIdx" _ _ hcopyExec
  · intro hexec
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "forsPk" "htIdx" _ (by decide) hexec

theorem forsFinalizeStep_preserves_selector_calldata (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st
      (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep st) := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeBody st
    (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep st) ?_
    (SphincsMinusVerifiers.SegmentS4Finalize.execForsFinalize st)
  intro s s'' stmt hmem hexec
  refine SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeBody_mem_cases
    (P := fun stmt => execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'')
    hmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ hexec
  · intro hexec
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "lastSecret" _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · intro hexec
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · intro hexec
    refine SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ SphincsMinusVerifiers.SegmentS4Finalize.forsCopyBody s s'' ?_ hexec
    intro s0 s1 copyStmt hcopy hcopyExec
    refine SphincsMinusVerifiers.SegmentS4Finalize.forsCopyBody_mem_cases
      (P := fun copyStmt => execStmt [] s0 copyStmt = .continue s1 →
        StateFrame.PreservesSelectorCalldata s0 s1)
      hcopy ?_ hcopyExec
    intro hcopyExec
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s0 s1 _ _ hcopyExec
  · intro hexec
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "forsPk" _ hexec

theorem afterFinalize_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings
        "sigBase" = sigDataOffset := by
  unfold afterFinalize
  rw [forsFinalizeStep_preserves_sigBase]
  exact afterFors_sigBase_mkC13State pkSeed pkRoot message sig

theorem afterFinalize_htIdx_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings
        "htIdx"
      =
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.read16 sig 0) message).hyperIndex := by
  unfold afterFinalize
  rw [forsFinalizeStep_preserves_htIdx]
  exact afterFors_htIdx_mkC13State pkSeed pkRoot message sig

theorem afterFinalize_seed_slot_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    ((afterFinalize (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  unfold afterFinalize
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep_seed_slot]
  exact afterFors_seed_slot_mkC13State pkSeed pkRoot message sig

theorem afterFinalize_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterFinalize (mkC13State pkSeed pkRoot message sig)).selector = 0
      ∧ (afterFinalize (mkC13State pkSeed pkRoot message sig)).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold afterFinalize
  have hfin := forsFinalizeStep_preserves_selector_calldata
    (afterFors (mkC13State pkSeed pkRoot message sig))
  have hfors := afterFors_selector_calldata_mkC13State pkSeed pkRoot message sig
  exact ⟨by rw [hfin.1]; exact hfors.1, by rw [hfin.2]; exact hfors.2⟩

theorem stepSeed_preserves_sigBase (st : RuntimeState) :
    lookupValue (SphincsMinusVerifiers.SegmentSeed.stepSeed st).bindings "sigBase"
      = lookupValue st.bindings "sigBase" := by
  unfold SphincsMinusVerifiers.SegmentSeed.stepSeed
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigOff" "sigBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "sigBase" _ (by decide)]

theorem stepSeed_preserves_htIdx (st : RuntimeState) :
    lookupValue (SphincsMinusVerifiers.SegmentSeed.stepSeed st).bindings "htIdx"
      = lookupValue st.bindings "htIdx" := by
  unfold SphincsMinusVerifiers.SegmentSeed.stepSeed
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigOff" "htIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "htIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "htIdx" _ (by decide)]

theorem stepSeed_preserves_selector_calldata (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st
      (SphincsMinusVerifiers.SegmentSeed.stepSeed st) := by
  unfold SphincsMinusVerifiers.SegmentSeed.stepSeed
  exact ⟨rfl, rfl⟩

theorem stepSeed_preserves_memory_zero (st : RuntimeState) :
    ((SphincsMinusVerifiers.SegmentSeed.stepSeed st).world.memory 0).val =
      (st.world.memory 0).val := by
  unfold SphincsMinusVerifiers.SegmentSeed.stepSeed
  rfl

theorem afterSeed_sigBase_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
        "sigBase" = sigDataOffset := by
  unfold afterSeed
  rw [stepSeed_preserves_sigBase]
  exact afterFinalize_sigBase_mkC13State pkSeed pkRoot message sig

theorem afterSeed_htIdx_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
        "htIdx"
      =
        (C13Concrete.hMsgC13 c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.read16 sig 0) message).hyperIndex := by
  unfold afterSeed
  rw [stepSeed_preserves_htIdx]
  exact afterFinalize_htIdx_mkC13State pkSeed pkRoot message sig

theorem afterSeed_selector_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterSeed (mkC13State pkSeed pkRoot message sig)).selector = 0
      ∧ (afterSeed (mkC13State pkSeed pkRoot message sig)).world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold afterSeed
  have hseed := stepSeed_preserves_selector_calldata
    (afterFinalize (mkC13State pkSeed pkRoot message sig))
  have hfin := afterFinalize_selector_calldata_mkC13State pkSeed pkRoot message sig
  exact ⟨by rw [hseed.1]; exact hfin.1, by rw [hseed.2]; exact hfin.2⟩

theorem afterSeed_selector_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterSeed (mkC13State pkSeed pkRoot message sig)).selector = 0 :=
  (afterSeed_selector_calldata_mkC13State pkSeed pkRoot message sig).1

theorem afterSeed_calldata_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    (afterSeed (mkC13State pkSeed pkRoot message sig)).world.calldata
      = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig :=
  (afterSeed_selector_calldata_mkC13State pkSeed pkRoot message sig).2

theorem afterSeed_seed_slot_mkC13State
    (pkSeed pkRoot message sig : ByteArray) :
    ((afterSeed (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  unfold afterSeed
  rw [stepSeed_preserves_memory_zero]
  exact afterFinalize_seed_slot_mkC13State pkSeed pkRoot message sig

/-- Loop-plumbing adapter for the FORS outer loop: once the per-iteration
`forsLeafStep` memory-frame fact is available for a seed cell, the whole
`afterFors` fold preserves that cell back to `afterS3`. -/
theorem afterFors_seed_slot_of_forsLeafStep_preserves
    (st : RuntimeState)
    (hLeaf : ∀ s,
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep s).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors st).world.memory 0).val = ((afterForsSetup st).world.memory 0).val := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_memory_val "i"
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep 0 hLeaf
    { (afterForsSetup st) with bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)]

/-- Bounded-index version of the FORS seed-cell loop plumbing.  This is the
shape needed by the real outer loop: the final leaf store is known non-aliasing
only after the loop binds `"i"` to its concrete iteration value. -/
theorem afterFors_seed_slot_of_forsLeafStep_bound_preserves
    (st : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat),
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors st).world.memory 0).val = ((afterForsSetup st).world.memory 0).val := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_memory_val_bound "i"
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep 0 hLeaf
    { (afterForsSetup st) with bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)]

/-- Range-gated FORS seed-cell loop plumbing.  The real statement-14 loop runs
six iterations, so callers only need a leaf-step memory frame for `idx < 6`. -/
theorem afterFors_seed_slot_of_forsLeafStep_range_preserves
    (st : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors st).world.memory 0).val = ((afterForsSetup st).world.memory 0).val := by
  unfold afterFors
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i"
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep 0 (fun idx => idx < 6)
    (fun s idx hidx => hLeaf s idx hidx)
    { (afterForsSetup st) with bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)
    (fun i _ hi => by
      have hbound : i < 6 := by
        simpa using hi
      exact hbound)]

/-- Frozen-entry version of `afterFors_seed_slot_of_forsLeafStep_preserves`,
composed with the S2/S3 seed endpoint. -/
theorem afterFors_seed_slot_mkC13State_of_forsLeafStep_preserves
    (pkSeed pkRoot message sig : ByteArray)
    (hLeaf : ∀ s,
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep s).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_seed_slot_of_forsLeafStep_preserves _ hLeaf]
  exact afterForsSetup_seed_slot_mkC13State pkSeed pkRoot message sig

/-- Frozen-entry bounded-index version of
`afterFors_seed_slot_of_forsLeafStep_bound_preserves`. -/
theorem afterFors_seed_slot_mkC13State_of_forsLeafStep_bound_preserves
    (pkSeed pkRoot message sig : ByteArray)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat),
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_seed_slot_of_forsLeafStep_bound_preserves _ hLeaf]
  exact afterS3_seed_slot_mkC13State pkSeed pkRoot message sig

/-- Frozen-entry range-gated version of
`afterFors_seed_slot_of_forsLeafStep_range_preserves`. -/
theorem afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
    (pkSeed pkRoot message sig : ByteArray)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [afterFors_seed_slot_of_forsLeafStep_range_preserves _ hLeaf]
  exact afterS3_seed_slot_mkC13State pkSeed pkRoot message sig

/-! ## FORS root cells. -/

/-- Normal FORS root-cell adapter for the six non-forced roots.  The outer FORS
loop and finalize pre-copy prefix are discharged here; callers only need the
substantive per-iteration data fact identifying the post-inner-climb `"node"`
with the intended root word, plus the local suffix-preservation frame for later
outer iterations. -/
theorem normalRootCell_eq_of_outer_iteration_node
    (st : RuntimeState) (j root : Nat) (hj : j < 6)
    (hPres : ∀ (s : RuntimeState) (idx : Nat), j < idx → idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
          (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val)
    (hNode :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { (afterForsSetup st) with
                    bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { (afterForsSetup st) with
                        bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") = root) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors st)).world.memory (0x80 + 32 * j)).val = root := by
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_preserves_root_source_slot
    (afterFors st) j hj]
  unfold afterFors
  rw [SphincsMinusVerifiers.SegmentS4Fors.forsOuter_root_cell_eq_iteration_node_of_suffix_preserves
    (afterForsSetup st) j hj hPres]
  exact hNode

/-- Quantified C13-shaped version of
`normalRootCell_eq_of_outer_iteration_node`.  This packages the six ordinary
FORS root slots exactly as the accept-path `hmRlo` premise expects: the only
remaining content is a per-index post-inner-climb node equality against
`forsAllRootsC13`. -/
theorem normalRootCells_eq_forsAllRootsC13_of_iteration_nodes
    (st : RuntimeState) (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    (hPres : ∀ j, j < 6 → ∀ (s : RuntimeState) (idx : Nat), j < idx → idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
          (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val)
    (hNode : ∀ j, (hj : j < 6) →
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { (afterForsSetup st) with
                    bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { (afterForsSetup st) with
                        bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") =
        (C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)) :
    ∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors st)).world.memory (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  intro j hj
  exact normalRootCell_eq_of_outer_iteration_node st j
    ((C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
      rw [C13Concrete.forsAllRootsC13_length]
      omega))
    hj (hPres j hj) (hNode j hj)

/-- Frozen-calldata normal-root adapter for one of the six non-forced FORS root
slots.  This version discharges the later-iteration root-cell frame from the
C13 calldata/auth-path shape, so callers only provide the threaded setup-site
facts and the data equality for iteration `j`'s post-inner `"node"`. -/
theorem normalRootCell_eq_of_fors_frozen_calldata_node
    (st : RuntimeState) (j root : Nat) (hj : j < 6)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig ∧
        lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hNode :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { (afterForsSetup st) with
                    bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { (afterForsSetup st) with
                        bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") = root) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors st)).world.memory (0x80 + 32 * j)).val = root := by
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_preserves_root_source_slot
    (afterFors st) j hj]
  unfold afterFors
  rw [SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata
      (afterForsSetup st) j hj pkSeed pkRoot message sig hsite]
  exact hNode

/-- Quantified C13-shaped normal-root adapter with the ordinary-root frame
discharged from frozen calldata/auth-path facts.  This is the `hmRlo` shape
needed by the accept path for the first six FORS roots. -/
theorem normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes
    (st : RuntimeState) (pk : PublicKey) (digest : HMsg) (fors : ForsSig)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig ∧
        lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hNode : ∀ j, (hj : j < 6) →
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { (afterForsSetup st) with
                    bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { (afterForsSetup st) with
                        bindings := bindValue (afterForsSetup st).bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") =
        (C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)) :
    ∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors st)).world.memory (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  intro j hj
  exact normalRootCell_eq_of_fors_frozen_calldata_node st j
    ((C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
      rw [C13Concrete.forsAllRootsC13_length]
      omega))
    hj pkSeed pkRoot message sig hsite (hNode j hj)

/-- Concrete frozen-entry normal-root adapter for one of the six non-forced
FORS root slots.  The suffix carry is discharged from the actual C13 outer-loop
prefix states, so callers only identify iteration `j`'s post-inner `"node"`. -/
theorem normalRootCell_eq_of_mkC13State_iteration_node
    (pkSeed pkRoot message sig : ByteArray) (j root : Nat) (hj : j < 6)
    (hNode :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pkSeed pkRoot message sig j))).bindings "node") = root) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val = root := by
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_preserves_root_source_slot
    (afterFors (mkC13State pkSeed pkRoot message sig)) j hj]
  rw [afterFors_eq_forsOuterPrefixState_mkC13State]
  have hsplit :=
    forsOuterPrefix_root_cell_suffix_mkC13State
      pkSeed pkRoot message sig j (5 - j) (by omega)
  have hwrite :=
    forsOuterPrefix_root_cell_iteration_node_mkC13State
      pkSeed pkRoot message sig j hj
  have hidx : j + 1 + (5 - j) = 6 := by omega
  calc
    ((forsOuterPrefixState pkSeed pkRoot message sig 6).world.memory
        (0x80 + 32 * j)).val
        =
      ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1 + (5 - j))).world.memory
        (0x80 + 32 * j)).val := by rw [hidx]
    _ = ((forsOuterPrefixState pkSeed pkRoot message sig (j + 1)).world.memory
          (0x80 + 32 * j)).val := hsplit
    _ =
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pkSeed pkRoot message sig j))).bindings "node") := hwrite
    _ = root := hNode

/-- Quantified concrete frozen-entry adapter for the six non-forced FORS root
slots.  This is the normal-root half of the C13 root-cell handoff with all
outer-loop memory framing discharged from `mkC13State`. -/
theorem normalRootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes
    (pk : PublicKey) (digest : HMsg) (message sig : ByteArray) (fors : ForsSig)
    (hNode : ∀ j, (hj : j < 6) →
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node") =
        (C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)) :
    ∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  intro j hj
  exact normalRootCell_eq_of_mkC13State_iteration_node
    pk.pkSeed pk.pkRoot message sig j
    ((C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
      rw [C13Concrete.forsAllRootsC13_length]
      omega))
    hj (hNode j hj)

/-- Concrete C13 node correspondence for one normal FORS leaf iteration.  This
adapter discharges the actual `mkC13State` seed slot and the parsed auth-path
`MerkleClimbData` range; callers still supply the setup-eval facts and the
per-step `MerkleClimbRel` preservation fact. -/
theorem forsOuterLeafState_node_eq_forsAllRootsC13_of_eval_parse
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (j : Nat) (hj : j < 6)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((sigParsed.fors.authPath[j]?).getD [])
          (forsAuthCdAt pk.pkSeed pk.pkRoot message sig j) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            (wordOfHash16 pk.pkSeed) j
            (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest)
            ((sigParsed.fors.authPath[j]?).getD []) idx a))
    (hAdrLt : C13Concrete.adrsForsLeaf
        (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest)
        j ((digest.forsIndex[j]?).getD 0) < 2 ^ 256)
    (hTree : evalExpr [] (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some ((digest.forsIndex[j]?).getD 0))
    (hSecret : evalExpr []
        { (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j) with
          bindings :=
            bindValue
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings
              "treeIdx" ((digest.forsIndex[j]?).getD 0) }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩)))
    (hLeaf : evalExpr []
        { (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j) with
          bindings :=
            (bindValue
              (bindValue
                (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings
                "treeIdx" ((digest.forsIndex[j]?).getD 0))
              "secretVal" (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩))) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (C13Concrete.adrsForsLeaf
              (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest)
              j ((digest.forsIndex[j]?).getD 0))) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node")
      =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  let cdAt : Nat → Nat := forsAuthCdAt pk.pkSeed pk.pkRoot message sig j
  have hD0 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.fors_climb_data_range_getD
      pk.pkSeed pk.pkRoot message sig v sigParsed j
      (sigDataOffset + (128 + 304 * j)) hparse hj rfl
  have hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        ((sigParsed.fors.authPath[j]?).getD []) cdAt idx := by
    intro idx _ hidx
    simpa [cdAt, forsAuthCdAt] using hD0 idx (by omega)
  have hm0 :
      ((forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).world.memory 0).val
        = wordOfHash16 pk.pkSeed := by
    simpa [forsOuterLeafState] using
      forsOuterPrefix_seed_slot_mkC13State pk.pkSeed pk.pkRoot message sig j (by omega)
  have hSkLt :
      wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩) < 2 ^ 256 :=
    SphincsMinusVerifiers.SegmentS2.wordOfHash16_lt _
  exact
    SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval
      (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
      pk digest sigParsed.fors j hj cdAt hstep hD hm0 hAdrLt hSkLt
      hTree hSecret hLeaf

/-- Concrete C13 `H_msg` specialization of
`forsOuterLeafState_node_eq_forsAllRootsC13_of_eval_parse`.  The FORS leaf
address bound is discharged from the 19-bit concrete digest index, so callers
only supply the setup eval facts and the per-step relation preservation. -/
theorem forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_eval_parse
    {v : Variant} (pk : PublicKey)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (j : Nat) (hj : j < 6)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((sigParsed.fors.authPath[j]?).getD [])
          (forsAuthCdAt pk.pkSeed pk.pkRoot message sig j) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            (wordOfHash16 pk.pkSeed) j
            (C13Concrete.idxTree0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            (C13Concrete.idxLeaf0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            ((sigParsed.fors.authPath[j]?).getD []) idx a))
    (hTree : evalExpr [] (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19))
            (.localVar "dVal"))
          (.literal 0x7FFFF))
          = some (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0))
    (hSecret : evalExpr []
        { (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j) with
          bindings :=
            bindValue
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings
              "treeIdx"
              (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0) }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩)))
    (hLeaf : evalExpr []
        { (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j) with
          bindings :=
            (bindValue
              (bindValue
                (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings
                "treeIdx"
                (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0))
              "secretVal" (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩))) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (C13Concrete.adrsForsLeaf
            (C13Concrete.idxTree0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            (C13Concrete.idxLeaf0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            j (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0))) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node")
      =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) :=
  forsOuterLeafState_node_eq_forsAllRootsC13_of_eval_parse
    pk (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
    message sig hparse j hj hstep
    (C13Concrete.adrsForsLeaf_hMsgC13_normal_lt pk sigParsed.R message hj)
    hTree hSecret hLeaf

/-- The concrete FIPS FORS leaf-address expression evaluates to the spec leaf
ADRS word once the hoisted `"forsBase"`, the outer-loop index, and the decoded
`treeIdx` binding are known. -/
theorem forsLeafAddress_eval_eq_adrsForsLeaf
    (st : RuntimeState) {t0 l0 i treeIdx secretVal : Nat}
    (hbase : lookupValue st.bindings "forsBase" = C13Concrete.adrsForsBase t0 l0)
    (ht0 : t0 < 2 ^ 64) (hl0 : l0 < 2 ^ 32)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hTreeIdxLt : treeIdx < 2 ^ 19) :
    evalExpr []
        { st with
          bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx)
              "secretVal" secretVal }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
      = some (C13Concrete.adrsForsLeaf t0 l0 i treeIdx) := by
  let st' : RuntimeState :=
    { st with
      bindings :=
        bindValue (bindValue st.bindings "treeIdx" treeIdx)
          "secretVal" secretVal }
  have hbase' : lookupValue st'.bindings "forsBase" = C13Concrete.adrsForsBase t0 l0 := by
    dsimp [st']
    rw [MemoryKit.lookupValue_bindValue_ne _ "secretVal" "forsBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "treeIdx" "forsBase" _ (by decide)]
    exact hbase
  have hi' : lookupValue st'.bindings "i" = i := by
    dsimp [st']
    rw [MemoryKit.lookupValue_bindValue_ne _ "secretVal" "i" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "treeIdx" "i" _ (by decide)]
    exact hi
  have ht' : lookupValue st'.bindings "treeIdx" = treeIdx := by
    dsimp [st']
    rw [MemoryKit.lookupValue_bindValue_ne _ "secretVal" "treeIdx" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
  have hbaseLt : C13Concrete.adrsForsBase t0 l0 < 2 ^ 256 :=
    lt_trans (C13Concrete.adrsForsBase_lt_of_bounds ht0 hl0)
      (by decide : (2 : Nat) ^ 192 < 2 ^ 256)
  have heval :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafAdrs_eval_eq
      st' hbase' hbaseLt hi' hiLt ht' hTreeIdxLt
  exact heval.trans (congrArg some
    (SphincsMinusVerifiers.SegmentS4Fors.forsLeafAdrs_value_eq_spec t0 l0 i treeIdx))

/-- Concrete C13 `H_msg` specialization that additionally discharges the
FORS leaf-address setup eval from the actual outer-loop `"i"` binding and the
19-bit digest index. -/
theorem forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_eval_parse
    (pk : PublicKey)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (j : Nat) (hj : j < 6)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((sigParsed.fors.authPath[j]?).getD [])
          (forsAuthCdAt pk.pkSeed pk.pkRoot message sig j) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            (wordOfHash16 pk.pkSeed) j
            (C13Concrete.idxTree0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            (C13Concrete.idxLeaf0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            ((sigParsed.fors.authPath[j]?).getD []) idx a))
    (hTree : evalExpr [] (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19))
            (.localVar "dVal"))
          (.literal 0x7FFFF))
          = some (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0))
    (hSecret : evalExpr []
        { (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j) with
          bindings :=
            bindValue
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings
              "treeIdx"
              (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0) }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩))) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node")
      =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  have hi :
      lookupValue (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings "i" = j :=
    (forsOuterLeafState_setupFacts_mkC13State pk.pkSeed pk.pkRoot message sig j hj).1
  have hbase :=
    (forsOuterLeafState_setupFacts_mkC13State pk.pkSeed pk.pkRoot message sig j hj).2.2.2.2
  rw [← C13Concrete.parseSignatureC13_R hparse] at hbase
  have hTreeIdxLt :
      ((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0
        < 2 ^ 19 :=
    C13Concrete.hMsgC13_forsIndex_getD_lt pk sigParsed.R message
      (lt_trans hj (by decide : 6 < 7))
  have hLeaf :=
    forsLeafAddress_eval_eq_adrsForsLeaf
      (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
      hbase
      (lt_trans (C13Concrete.idxTree0C13_lt pk sigParsed.R message)
        (by decide : (2 : Nat) ^ 11 < 2 ^ 64))
      (lt_trans (C13Concrete.idxLeaf0C13_lt _)
        (by decide : (2 : Nat) ^ 11 < 2 ^ 32))
      hi hj hTreeIdxLt
      (secretVal := wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩))
  exact
    forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_eval_parse
      pk message sig hparse j hj hstep hTree hSecret hLeaf

/-- S3 binds `"dVal"` to the digest word produced by S2, and the frozen C13 S2
digest is the concrete `H_msg` keccak preimage word over the byte-level inputs. -/
theorem afterS3_dVal_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterS3 (mkC13State pkSeed pkRoot message sig)).bindings "dVal"
      = keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot,
          wordOfHash16 (C13Concrete.read16 sig 0), C13Concrete.baToNatBE message % C13Concrete.wordMod,
          C13Concrete.hMsgPad ] := by
  unfold afterS3 SegmentS3.stepS3 afterS2
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigBase" "dVal" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  exact SphincsMinusVerifiers.SegmentS2R.s2_digest_mkC13State_final
    pkSeed pkRoot message sig

/-- The FORS pre-loop setup preserves the S3 `"dVal"` digest alias. -/
theorem afterForsSetup_dVal_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings "dVal"
      = keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot,
          wordOfHash16 (C13Concrete.read16 sig 0), C13Concrete.baToNatBE message % C13Concrete.wordMod,
          C13Concrete.hMsgPad ] := by
  unfold afterForsSetup
  rw [SegmentForsSetup.stepForsSetup_preserves_dVal_step]
  exact afterS3_dVal_mkC13State pkSeed pkRoot message sig

/-- Every actual C13 FORS outer-loop prefix carries the S3 `"dVal"` digest alias. -/
theorem forsOuterPrefix_dVal_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (n : Nat) :
    lookupValue (forsOuterPrefixState pkSeed pkRoot message sig n).bindings "dVal"
      = keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot,
          wordOfHash16 (C13Concrete.read16 sig 0), C13Concrete.baToNatBE message % C13Concrete.wordMod,
          C13Concrete.hMsgPad ] := by
  unfold forsOuterPrefixState
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "dVal"
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        (by decide) SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_dVal
        _ 0 n]
  rw [MemoryKit.lookupValue_bindValue_ne
        (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
        "i" "dVal" (wordNormalize 0) (by decide)]
  exact afterForsSetup_dVal_mkC13State pkSeed pkRoot message sig

/-- Named-state projection of the C13 FORS-prefix `"dVal"` frame. -/
theorem forsOuterLeafState_dVal_mkC13State
    (pkSeed pkRoot message sig : ByteArray) (t : Nat) :
    lookupValue (forsOuterLeafState pkSeed pkRoot message sig t).bindings "dVal"
      = keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot,
          wordOfHash16 (C13Concrete.read16 sig 0), C13Concrete.baToNatBE message % C13Concrete.wordMod,
          C13Concrete.hMsgPad ] := by
  unfold forsOuterLeafState
  rw [MemoryKit.lookupValue_bindValue_ne
        (forsOuterPrefixState pkSeed pkRoot message sig t).bindings
        "i" "dVal" (wordNormalize t) (by decide)]
  exact forsOuterPrefix_dVal_mkC13State pkSeed pkRoot message sig t

/-- The concrete FORS setup expression for `"treeIdx"` evaluates, at the actual
C13 outer-loop leaf state, to the matching concrete `H_msg` FORS index. -/
theorem forsOuterLeafState_treeIdx_eval_eq_hMsg_parse
    (pk : PublicKey) (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (j : Nat) (hj : j < 6) :
    evalExpr [] (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19))
            (.localVar "dVal"))
          (.literal 0x7FFFF))
      = some (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0) := by
  let st := forsOuterLeafState pk.pkSeed pk.pkRoot message sig j
  let digest :=
    keccakWords [ wordOfHash16 pk.pkSeed, wordOfHash16 pk.pkRoot,
      wordOfHash16 (C13Concrete.read16 sig 0), C13Concrete.baToNatBE message % C13Concrete.wordMod,
      C13Concrete.hMsgPad ]
  have hi : lookupValue st.bindings "i" = j := by
    dsimp [st]
    exact (forsOuterLeafState_setupFacts_mkC13State pk.pkSeed pk.pkRoot message sig j hj).1
  have hdVal : lookupValue st.bindings "dVal" = digest := by
    dsimp [st, digest]
    exact forsOuterLeafState_dVal_mkC13State pk.pkSeed pk.pkRoot message sig j
  have hiEval : evalExpr [] st (.localVar "i") = some j := by
    exact congrArg some hi
  have hdValEval : evalExpr [] st (.localVar "dVal") = some digest := by
    exact congrArg some hdVal
  have hmul :
      evalExpr [] st (.mul (.localVar "i") (.literal 19)) = some (19 * j) := by
    show (do
      let lhs : Verity.Core.Uint256 := ← evalExpr [] st (.localVar "i")
      let rhs : Verity.Core.Uint256 := ← evalExpr [] st (.literal 19)
      pure (lhs * rhs).val) = some (19 * j)
    rw [hiEval]
    show some ((Verity.Core.Uint256.ofNat j * Verity.Core.Uint256.ofNat 19).val)
      = some (19 * j)
    show some (((Verity.Core.Uint256.ofNat j).val * (Verity.Core.Uint256.ofNat 19).val)
          % Verity.Core.Uint256.modulus) = some (19 * j)
    have hjv : (Verity.Core.Uint256.ofNat j).val = j :=
      Nat.mod_eq_of_lt (lt_trans hj (by decide : 6 < 2 ^ 256))
    have h19v : (Verity.Core.Uint256.ofNat 19).val = 19 :=
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)
    have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
    rw [hjv, h19v, hmod, Nat.mul_comm,
      Nat.mod_eq_of_lt (by
        calc
          19 * j ≤ 19 * 5 := Nat.mul_le_mul_left 19 (Nat.le_of_lt_succ hj)
          _ < 2 ^ 256 := by decide)]
  have hshiftLt : 19 * j < 2 ^ 256 := by
    calc
      19 * j ≤ 19 * 5 := Nat.mul_le_mul_left 19 (Nat.le_of_lt_succ hj)
      _ < 2 ^ 256 := by decide
  have hdigestLt : digest < 2 ^ 256 := by
    dsimp [digest]
    simpa [Compiler.Constants.evmModulus] using
      KeccakBridge.keccakWords_lt
        [ wordOfHash16 pk.pkSeed, wordOfHash16 pk.pkRoot,
          wordOfHash16 (C13Concrete.read16 sig 0),
          C13Concrete.baToNatBE message % C13Concrete.wordMod, C13Concrete.hMsgPad ]
  have hshr :
      evalExpr [] st
        (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
        = some (digest >>> (19 * j)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (.mul (.localVar "i") (.literal 19)) (.localVar "dVal")
      (19 * j) digest hmul hdValEval hshiftLt hdigestLt
  have hland :
      evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF))
        = some ((digest >>> (19 * j)) % (2 ^ 19)) := by
    rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      st (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
      (digest >>> (19 * j)) 0x7FFFF hshr
      (by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self digest (2 ^ (19 * j))) hdigestLt)
      (by decide : 0x7FFFF < 2 ^ 256)]
    rw [SegmentS3.nat_land_low19]
  have hidx :=
    C13Concrete.hMsgC13_forsIndex_getD_eq pk sigParsed.R message
      (lt_trans hj (by decide : 6 < 7))
  rw [hland]
  change some (digest >>> (19 * j) % 2 ^ 19) =
    some (((C13Concrete.hMsgC13 c13 pk sigParsed.R message).forsIndex[j]?).getD 0)
  rw [hidx]
  rw [C13Concrete.parseSignatureC13_R hparse]

/-- `afterSeed` starts the hypertree climb at the FORS public-key word. -/
theorem afterSeed_currentNode (st : RuntimeState) :
    lookupValue (afterSeed st).bindings "currentNode"
      = lookupValue (afterFinalize st).bindings "forsPk" := by
  unfold afterSeed
  exact SegmentSeed.stepSeed_currentNode (afterFinalize st)

/-- `afterSeed` starts the hypertree index from the digest-derived `htIdx`. -/
theorem afterSeed_idxTree (st : RuntimeState) :
    lookupValue (afterSeed st).bindings "idxTree"
      = lookupValue (afterFinalize st).bindings "htIdx" := by
  unfold afterSeed
  exact SegmentSeed.stepSeed_idxTree (afterFinalize st)

/-- `afterSeed` starts the layer signature offset at the first XMSS layer. -/
theorem afterSeed_sigOff (st : RuntimeState) :
    lookupValue (afterSeed st).bindings "sigOff" = wordNormalize 1952 := by
  unfold afterSeed
  exact SegmentSeed.stepSeed_sigOff (afterFinalize st)

/-! ## FORS-finalize boundary. -/

/-- The model word produced by statement 21's FORS-root compression keccak, exposed
at the `afterFors`/`afterFinalize` boundary. -/
def forsPkCompressWord (st : RuntimeState) : Nat :=
  (Verity.Core.Uint256.and
    (keccakMemorySlice
      (SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory
      (wordNormalize 0x00) (wordNormalize 0x120))
    (wordNormalize N_MASK)).val

/-- If the S4 memory-compression word equals the spec FORS public key word, then
`afterFinalize` binds `"forsPk"` to that spec word.  This isolates the remaining
S4 data-correspondence obligation from the seed/layer composition. -/
theorem afterFinalize_forsPk_of_compress
    (st : RuntimeState) (forsPk : ByteArray)
    (hCompress : forsPkCompressWord (afterFors st) = wordOfHash16 forsPk) :
    lookupValue (afterFinalize st).bindings "forsPk" = wordOfHash16 forsPk := by
  unfold afterFinalize
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizeStep_forsPk]
  exact hCompress

/-- If the pre-`forsPk` scratch frame contains
`seed ‖ FORS_ROOTS adrs ‖ root_0..root_6`, then the model's FORS public-key
compression word is exactly the spec kernel's masked compression word.  This is
the final keccak/masking half of the S4 obligation; the caller still has to prove
that the seven scratch roots are the roots produced by the FORS climbs. -/
theorem forsPkCompressWord_eq_of_memory
    (st : RuntimeState) (seed : Nat) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hm0 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0).val
        = seed)
    (hm1 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0x20).val
        = adrsForsRootsC13 digest)
    (hmR : ∀ j, (h : j < 7) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory
          (0x40 + 32 * j)).val = roots[j]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRootsC13 digest :: roots)) := by
  unfold forsPkCompressWord
  rw [show wordNormalize 0x00 = 0 by rfl]
  rw [show wordNormalize 0x120 = 0x120 by rfl]
  rw [show (N_MASK : Nat) = nMask from rfl]
  have hnmask : wordNormalize nMask = nMask := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide)
  rw [hnmask]
  have hlen9 : (seed :: adrsForsRootsC13 digest :: roots).length = 9 := by
    simp [hlen]
  have hsz : 32 * (seed :: adrsForsRootsC13 digest :: roots).length = 0x120 := by
    rw [hlen9]
  rw [← hsz]
  rw [KeccakBridge.keccakMemorySlice_eq_keccakWords]
  · unfold maskN Verity.Core.Uint256.and Verity.Core.Uint256.ofNat
    simp only
    have hklt : keccakWords (seed :: adrsForsRootsC13 digest :: roots) < Verity.Core.Uint256.modulus := by
      simpa [Compiler.Constants.evmModulus] using
        KeccakBridge.keccakWords_lt (seed :: adrsForsRootsC13 digest :: roots)
    have hnlt : nMask < Verity.Core.Uint256.modulus := by
      decide
    rw [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hnlt]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hklt)
  · intro i hi
    rw [hlen9] at hi
    match i with
    | 0 => simpa using hm0
    | 1 => simpa using hm1
    | j + 2 =>
      have hj : j < 7 := by omega
      have hoff : 0 + 32 * (j + 2) = 0x40 + 32 * j := by omega
      rw [hoff]
      exact hmR j hj

/-- Variant of `forsPkCompressWord_eq_of_memory` that consumes the seven FORS
root words from the state before the copy loop.  `SegmentS4Finalize` proves the
copy loop moves those words into the compression preimage slots without changing
their values. -/
theorem forsPkCompressWord_eq_of_preCopy_roots
    (st : RuntimeState) (seed : Nat) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hm0 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0).val
        = seed)
    (hm1 :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep st).world.memory 0x20).val
        = adrsForsRootsC13 digest)
    (hmR : ∀ j, (h : j < 7) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_memory st seed digest roots hlen hm0 hm1
    (fun j hj => by
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep_copy_slot st j hj]
      exact hmR j hj)

/-- Full S4-finalize compression adapter phrased at the most useful boundary:
the seed cell is read from the incoming state, the FORS_ROOTS ADRS cell is
discharged by `SegmentS4Finalize`, the roots are read from the state immediately
before the copy loop, and the copy loop itself is discharged by
`SegmentS4Finalize`.  The remaining S4 data facts are thus the seed value and the
actual root contents of the pre-copy cells. -/
theorem forsPkCompressWord_eq_of_preCopy_frame
    (st : RuntimeState) (seed : Nat) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hT : lookupValue st.bindings "idxTree0" = C13Concrete.idxTree0C13 digest)
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hL : lookupValue st.bindings "idxLeaf0" = C13Concrete.idxLeaf0C13 digest)
    (hmSeed : (st.world.memory 0).val = seed)
    (hmR : ∀ j, (h : j < 7) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_roots st seed digest roots hlen
    (by
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep_preserves_low_slot st 0
        (by decide)]
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_seed_slot st]
      exact hmSeed)
    (by
      rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePrePkStep_preserves_low_slot st 0x20
        (by decide)]
      simpa [SphincsMinusVerifierSpec.C13Concrete.adrsForsRootsC13] using
        SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_adrsRoots_slot st
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest)
          hT hTlt hL (C13Concrete.idxLeaf0C13_lt digest))
    hmR

/-- Variant of `forsPkCompressWord_eq_of_preCopy_frame` matching the concrete S4
layout just before the copy loop: the first six FORS roots live in
`0x80 + 32*j`, while the seventh forced-zero tree root lives at `0x140`
(`0x80 + 32*6`).  The FORS_ROOTS address word is proved by the finalize segment,
so callers only supply seed and root-cell facts. -/
theorem forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (st : RuntimeState) (seed : Nat) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hT : lookupValue st.bindings "idxTree0" = C13Concrete.idxTree0C13 digest)
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hL : lookupValue st.bindings "idxLeaf0" = C13Concrete.idxLeaf0C13 digest)
    (hmSeed : (st.world.memory 0).val = seed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep st).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord st = maskN (keccakWords (seed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame st seed digest roots hlen hT hTlt hL hmSeed
    (fun j hj => by
      by_cases hj6 : j < 6
      · exact hmRlo j hj6
      · have hjeq : j = 6 := by omega
        simpa [hjeq] using hmRlast)

/-- Frozen-entry FORS-compression adapter: the seed word is supplied by the
S2/S3 seed-cell endpoint plus the outer-FORS loop memory-frame hypothesis, while
the root-cell facts remain the substantive FORS climb correspondence obligations. -/
theorem forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last
    (pkSeed pkRoot message sig : ByteArray) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hT : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
      = C13Concrete.idxTree0C13 digest)
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hL : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
      = C13Concrete.idxLeaf0C13 digest)
    (hLeaf : ∀ s,
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep s).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (afterFors (mkC13State pkSeed pkRoot message sig)) (wordOfHash16 pkSeed) digest roots hlen
    hT hTlt hL
    (afterFors_seed_slot_mkC13State_of_forsLeafStep_preserves pkSeed pkRoot message sig hLeaf)
    hmRlo hmRlast

/-- Range-gated frozen-entry FORS-compression adapter.  This is the same
boundary as `forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last`, but
the seed preservation premise matches the real statement-14 loop range (`i < 6`)
instead of requiring a globally quantified leaf-step fact. -/
theorem forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last_range
    (pkSeed pkRoot message sig : ByteArray) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hT : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
      = C13Concrete.idxTree0C13 digest)
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hL : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
      = C13Concrete.idxLeaf0C13 digest)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (afterFors (mkC13State pkSeed pkRoot message sig)) (wordOfHash16 pkSeed) digest roots hlen
    hT hTlt hL
    (afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
      pkSeed pkRoot message sig hLeaf)
    hmRlo hmRlast

/-- Seed-cell frozen-entry FORS-compression adapter.  This is the narrowest
S4/FORS-compression boundary: callers supply the single seed-cell fact at
`afterFors`, plus the six normal root cells and the forced-root cell. -/
theorem forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
    (pkSeed pkRoot message sig : ByteArray) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hT : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
      = C13Concrete.idxTree0C13 digest)
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hL : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
      = C13Concrete.idxLeaf0C13 digest)
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
    (afterFors (mkC13State pkSeed pkRoot message sig)) (wordOfHash16 pkSeed) digest roots hlen
    hT hTlt hL hmSeed hmRlo hmRlast

/-- Concrete frozen-entry FORS-compression adapter with the seed-cell fact
discharged internally from the actual six C13 outer-loop prefixes. -/
theorem forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last
    (pkSeed pkRoot message sig : ByteArray) (digest : SphincsMinusVerifierSpec.HMsg) (roots : List Nat)
    (hlen : roots.length = 7)
    (hT : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
      = C13Concrete.idxTree0C13 digest)
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hL : lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
      = C13Concrete.idxLeaf0C13 digest)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega)) :
    forsPkCompressWord (afterFors (mkC13State pkSeed pkRoot message sig))
      = maskN (keccakWords (wordOfHash16 pkSeed :: adrsForsRootsC13 digest :: roots)) :=
  forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
    pkSeed pkRoot message sig digest roots hlen hT hTlt hL
    (afterFors_seed_slot_mkC13State pkSeed pkRoot message sig)
    hmRlo hmRlast

/-- Normal FORS secret-key calldata read resolves against the frozen C13 calldata
image and the parsed signature's `fors.sk[j]` projection. -/
theorem forsSecret_eval_eq_wordOfHash16_parse
    (st : RuntimeState) (pkSeed pkRoot message sig : ByteArray)
    {v : Variant} {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    {j treeIdx : Nat} (hj : j < 6)
    (hi : lookupValue st.bindings "i" = j)
    (hbase : lookupValue st.bindings "sigBase" = sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) :
    evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal N_MASK))
      = some (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩)) := by
  let st' : RuntimeState := { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
  let image := headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
  let sOff : Nat := 16 + 16 * j
  have hiEval : evalExpr [] st' (.localVar "i") = some j := by
    dsimp [st']
    change some (lookupValue (bindValue st.bindings "treeIdx" treeIdx) "i") = some j
    rw [MemoryKit.lookupValue_bindValue_ne _ "treeIdx" "i" _ (by decide)]
    exact congrArg some hi
  have hsh :
      evalExpr [] st' (.shl (.literal 4) (.localVar "i")) = some (j <<< 4) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st' (.literal 4) (.localVar "i") 4 j rfl hiEval
      (by decide)
      (lt_trans hj (by decide : 6 < 2 ^ 256))
      (by
        rw [Nat.shiftLeft_eq]
        calc
          j * 2 ^ 4 ≤ 5 * 2 ^ 4 :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hj)
          _ < 2 ^ 256 := by decide)
  have hshLt : j <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      j * 2 ^ 4 ≤ 5 * 2 ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hj)
      _ < 2 ^ 256 := by decide
  have hinnerLt : 16 + (j <<< 4) < 2 ^ 256 := by
    calc
      16 + (j <<< 4) ≤ 16 + (5 * 2 ^ 4) := by
        rw [Nat.shiftLeft_eq]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hj)) 16
      _ < 2 ^ 256 := by decide
  have hinner :
      evalExpr [] st' (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))
        = some (16 + (j <<< 4)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st' (.literal 16) (.shl (.literal 4) (.localVar "i"))
      16 (j <<< 4) rfl hsh (by decide) hshLt hinnerLt
  have hbaseEval : evalExpr [] st' (.localVar "sigBase") = some sigDataOffset := by
    dsimp [st']
    change some (lookupValue (bindValue st.bindings "treeIdx" treeIdx) "sigBase")
      = some sigDataOffset
    rw [MemoryKit.lookupValue_bindValue_ne _ "treeIdx" "sigBase" _ (by decide)]
    exact congrArg some hbase
  have hoff :
      evalExpr [] st'
        (.add (.localVar "sigBase")
          (.add (.literal 16) (.shl (.literal 4) (.localVar "i"))))
        = some (sigDataOffset + sOff) := by
    have hadd :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
        st' (.localVar "sigBase") (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))
        sigDataOffset (16 + (j <<< 4)) hbaseEval hinner
        (by decide) hinnerLt (by
          calc
            sigDataOffset + (16 + (j <<< 4)) ≤ sigDataOffset + (16 + (5 * 2 ^ 4)) := by
              rw [Nat.shiftLeft_eq]
              exact Nat.add_le_add_left
                (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hj)) 16)
                sigDataOffset
            _ < 2 ^ 256 := by decide)
    simpa [sOff, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hadd
  have hraw :
      evalExpr [] st'
        (.calldataload
          (.add (.localVar "sigBase")
            (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
        = some (Compiler.Proofs.YulGeneration.calldataloadWord 0 image
          (sigDataOffset + sOff)) := by
    show (do
      let resolvedOffset ← evalExpr [] st'
        (.add (.localVar "sigBase")
          (.add (.literal 16) (.shl (.literal 4) (.localVar "i"))))
      some (Compiler.Proofs.YulGeneration.calldataloadWord st'.selector st'.world.calldata
        resolvedOffset)) = some (Compiler.Proofs.YulGeneration.calldataloadWord 0 image
          (sigDataOffset + sOff))
    rw [hoff]
    dsimp [st', image]
    rw [hsel, hcd]
  have hword_lt :
      Compiler.Proofs.YulGeneration.calldataloadWord 0 image (sigDataOffset + sOff)
        < 2 ^ 256 :=
    calldataloadWord_lt_of_ge4 0 image (sigDataOffset + sOff) (by omega)
  have hmask :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      st'
      (.calldataload
        (.add (.localVar "sigBase")
          (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 image (sigDataOffset + sOff))
      N_MASK hraw hword_lt (by decide)
  rw [hmask]
  have hsig :=
    SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
      pkSeed pkRoot message sig sOff
  have hsk :
      (sigParsed.fors.sk[j]?).getD ⟨#[]⟩ = C13Concrete.read16 sig sOff := by
    have hsome :=
      C13Concrete.parseSignatureC13_fors_sk_getElem? hparse
        (lt_trans hj (by decide : 6 < 7))
    simpa [sOff] using congrArg (fun o => o.getD ⟨#[]⟩) hsome
  simpa [image, hsk] using congrArg some hsig

/-- Concrete C13 `H_msg` normal-root adapter with the local leaf-address and
secret-key calldata setup evals discharged from the actual outer-loop state. -/
theorem forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_secret_parse
    (pk : PublicKey)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (j : Nat) (hj : j < 6)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((sigParsed.fors.authPath[j]?).getD [])
          (forsAuthCdAt pk.pkSeed pk.pkRoot message sig j) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            (wordOfHash16 pk.pkSeed) j
            (C13Concrete.idxTree0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            (C13Concrete.idxLeaf0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            ((sigParsed.fors.authPath[j]?).getD []) idx a))
    (hTree : evalExpr [] (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19))
            (.localVar "dVal"))
          (.literal 0x7FFFF))
          = some (((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node")
      =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  rcases forsOuterLeafState_setupFacts_mkC13State
      pk.pkSeed pk.pkRoot message sig j hj with
    ⟨hi, hsigB, hsel, hcd, _hbase⟩
  let treeIdx :=
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).forsIndex[j]?).getD 0
  have hSecret :
      evalExpr []
        { (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j) with
          bindings :=
            bindValue
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j).bindings
              "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩)) := by
    simpa [treeIdx] using
      forsSecret_eval_eq_wordOfHash16_parse
        (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j)
        pk.pkSeed pk.pkRoot message sig hparse hj hi hsigB hsel hcd
        (treeIdx := treeIdx)
  exact
    forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_eval_parse
      pk message sig hparse j hj hstep hTree hSecret

/-- Concrete C13 `H_msg` normal-root adapter with the actual outer-loop tree-index
setup eval discharged from the S2/S3 digest binding and the parser's `R` field,
in addition to the local leaf-address and secret-key calldata setup evals.  The
remaining caller obligation is the per-height Merkle-climb step preservation. -/
theorem forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse
    (pk : PublicKey) (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (j : Nat) (hj : j < 6)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((sigParsed.fors.authPath[j]?).getD [])
          (forsAuthCdAt pk.pkSeed pk.pkRoot message sig j) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            (wordOfHash16 pk.pkSeed) j
            (C13Concrete.idxTree0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            (C13Concrete.idxLeaf0C13 (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message))
            ((sigParsed.fors.authPath[j]?).getD []) idx a)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node")
      =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  have hTree :=
    forsOuterLeafState_treeIdx_eval_eq_hMsg_parse pk message sig hparse j hj
  exact
    forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_secret_parse
      pk message sig hparse j hj hstep hTree

/-- Concrete C13 normal-root adapter with the actual frozen calldata Merkle-step
frame discharged.  This removes the remaining per-height `MerkleClimbRel`
callback from the outer leaf node correspondence by using the C13 auth-path
calldata layout and the range/path-index bounded inner FORS frame theorem. -/
theorem forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse_concrete
    (pk : PublicKey) (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (j : Nat) (hj : j < 6) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node")
      =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega) := by
  let st := forsOuterLeafState pk.pkSeed pk.pkRoot message sig j
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let treeIdx := (digest.forsIndex[j]?).getD 0
  rcases forsOuterLeafState_setupFacts_mkC13State
      pk.pkSeed pk.pkRoot message sig j hj with
    ⟨hi, hsigB, hsel, hcd, hbase0⟩
  have hbase :
      lookupValue st.bindings "forsBase"
        = C13Concrete.adrsForsBase
            (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest) := by
    dsimp [st, digest]
    rw [← C13Concrete.parseSignatureC13_R hparse] at hbase0
    exact hbase0
  have hD0 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.fors_climb_data_range_getD
      pk.pkSeed pk.pkRoot message sig c13 sigParsed j
      (sigDataOffset + (128 + 304 * j)) hparse hj rfl
  have hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        ((sigParsed.fors.authPath[j]?).getD [])
        (fun h =>
          Compiler.Proofs.YulGeneration.calldataloadWord 0
            (SphincsMinusVerifiers.MkC13State.headWords
              pk.pkSeed pk.pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
            (SphincsMinusVerifiers.MkC13State.sigDataOffset
              + (128 + 304 * j) + 16 * h)) idx := by
    intro idx _ hidx
    simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hD0 idx (by omega)
  have hm0 : (st.world.memory 0).val = wordOfHash16 pk.pkSeed := by
    dsimp [st]
    simpa [forsOuterLeafState] using
      forsOuterPrefix_seed_slot_mkC13State pk.pkSeed pk.pkRoot message sig j (by omega)
  have hTreeIdxLt : treeIdx < 2 ^ 256 := by
    dsimp [treeIdx, digest]
    exact lt_trans
      (C13Concrete.hMsgC13_forsIndex_getD_lt pk sigParsed.R message
        (lt_trans hj (by decide : 6 < 7)))
      (by decide : 2 ^ 19 < 2 ^ 256)
  have hTreeIdx19 : treeIdx < 2 ^ 19 := by
    dsimp [treeIdx, digest]
    exact C13Concrete.hMsgC13_forsIndex_getD_lt pk sigParsed.R message
      (lt_trans hj (by decide : 6 < 7))
  have hAdrLt : C13Concrete.adrsForsLeaf
      (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest)
      j treeIdx < 2 ^ 256 := by
    dsimp [treeIdx, digest]
    exact C13Concrete.adrsForsLeaf_hMsgC13_normal_lt pk sigParsed.R message hj
  have hSkLt :
      wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩) < 2 ^ 256 :=
    SphincsMinusVerifiers.SegmentS2.wordOfHash16_lt _
  have hTree :
      evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19))
            (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx := by
    dsimp [st, treeIdx, digest]
    exact forsOuterLeafState_treeIdx_eval_eq_hMsg_parse pk message sig hparse j hj
  have hSecret :
      evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩)) := by
    exact
      forsSecret_eval_eq_wordOfHash16_parse
        st pk.pkSeed pk.pkRoot message sig hparse hj hi hsigB hsel hcd
        (treeIdx := treeIdx)
  have hLeaf :
      evalExpr []
        { st with bindings :=
            (bindValue
              (bindValue st.bindings "treeIdx" treeIdx)
              "secretVal" (wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩))) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (C13Concrete.adrsForsLeaf
              (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest)
              j treeIdx) := by
    exact
      forsLeafAddress_eval_eq_adrsForsLeaf st hbase
        (lt_trans (C13Concrete.idxTree0C13_lt pk sigParsed.R message)
          (by decide : (2 : Nat) ^ 11 < 2 ^ 64))
        (lt_trans (C13Concrete.idxLeaf0C13_lt _)
          (by decide : (2 : Nat) ^ 11 < 2 ^ 32))
        hi hj hTreeIdx19
        (secretVal := wordOfHash16 ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩))
  have hsigBst : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset := hsigB
  rw [C13Concrete.forsAllRootsC13_getElem_normal
    (pk := pk) (digest := digest) (fors := sigParsed.fors) hj]
  exact
    SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata
      st (wordOfHash16 pk.pkSeed) j
      (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest) treeIdx
      ((sigParsed.fors.sk[j]?).getD ⟨#[]⟩)
      pk.pkSeed pk.pkRoot message sig
      ((sigParsed.fors.authPath[j]?).getD [])
      hi hj hTreeIdxLt hbase
      (lt_trans (C13Concrete.idxTree0C13_lt pk sigParsed.R message)
        (by decide : (2 : Nat) ^ 11 < 2 ^ 64))
      (lt_trans (C13Concrete.idxLeaf0C13_lt _)
        (by decide : (2 : Nat) ^ 11 < 2 ^ 32))
      hsigBst hsel hcd hD hm0 hAdrLt hSkLt hTree hSecret hLeaf

/-- The final forced-root secret-key read resolves against the frozen C13 calldata
image.  This is the calldata half of statement 15's `lastSecret` binding:
`and(calldataload(sigBase + 16 + (4 << 6)), N_MASK)` is the spec word
`wordOfHash16 (read16 sig 112)`. -/
theorem finalSecret_eval_eq_wordOfHash16
    (st : RuntimeState) (pkSeed pkRoot message sig : ByteArray)
    (hbase : lookupValue st.bindings "sigBase" = sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) :
    evalExpr [] st
      (.bitAnd
        (.calldataload
          (.add (.localVar "sigBase")
            (.add (.literal 16) (.shl (.literal 4) (.literal 6)))))
        (.literal N_MASK))
      = some (wordOfHash16 (C13Concrete.read16 sig (16 + 16 * 6))) := by
  let image := headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
  let sOff : Nat := 16 + 16 * 6
  have hsh :
      evalExpr [] st (.shl (.literal 4) (.literal 6)) = some (6 <<< 4) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 4) (.literal 6) 4 6 rfl rfl (by decide) (by decide) (by decide)
  have hinner :
      evalExpr [] st (.add (.literal 16) (.shl (.literal 4) (.literal 6)))
        = some (16 + (6 <<< 4)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (.literal 16) (.shl (.literal 4) (.literal 6))
      16 (6 <<< 4) rfl hsh (by decide) (by decide) (by decide)
  have hbaseEval : evalExpr [] st (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue st.bindings "sigBase") = some sigDataOffset
    rw [hbase]
  have hoff :
      evalExpr [] st
        (.add (.localVar "sigBase")
          (.add (.literal 16) (.shl (.literal 4) (.literal 6))))
        = some (sigDataOffset + sOff) := by
    have hadd :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
        st (.localVar "sigBase") (.add (.literal 16) (.shl (.literal 4) (.literal 6)))
        sigDataOffset (16 + (6 <<< 4)) hbaseEval hinner
        (by decide) (by decide) (by decide)
    simpa [sOff, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hadd
  have hraw :
      evalExpr [] st
        (.calldataload
          (.add (.localVar "sigBase")
            (.add (.literal 16) (.shl (.literal 4) (.literal 6)))))
        = some (Compiler.Proofs.YulGeneration.calldataloadWord 0 image
          (sigDataOffset + sOff)) := by
    show (do
      let resolvedOffset ← evalExpr [] st
        (.add (.localVar "sigBase")
          (.add (.literal 16) (.shl (.literal 4) (.literal 6))))
      some (Compiler.Proofs.YulGeneration.calldataloadWord st.selector st.world.calldata
        resolvedOffset)) = some (Compiler.Proofs.YulGeneration.calldataloadWord 0 image
          (sigDataOffset + sOff))
    rw [hoff, hsel, hcd]
    rfl
  have hword_lt :
      Compiler.Proofs.YulGeneration.calldataloadWord 0 image (sigDataOffset + sOff)
        < 2 ^ 256 :=
    calldataloadWord_lt_of_ge4 0 image (sigDataOffset + sOff) (by decide)
  have hmask :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      st
      (.calldataload
        (.add (.localVar "sigBase")
          (.add (.literal 16) (.shl (.literal 4) (.literal 6)))))
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 image (sigDataOffset + sOff))
      N_MASK hraw hword_lt (by decide)
  rw [hmask]
  have hsig :=
    SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
      pkSeed pkRoot message sig sOff
  simpa [image, sOff] using congrArg some hsig

/-- Forced-root cell bridge at the accept boundary.  Once the caller supplies the
`afterFors` seed cell and the final masked secret-key calldata read, the local
finalize proof identifies slot `0x140` with the named seventh root in
`forsAllRootsC13`.  The parse premise turns the raw signature byte offset
`16 + 16*6` into the parsed `fors.sk[6]` field. -/
theorem forcedRootCell_eq_forsAllRootsC13_of_parse
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hmSeed :
      ((afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pk.pkSeed)
    (hLastSecret :
      evalExpr [] (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.literal 6)))))
          (.literal N_MASK))
        = some (wordOfHash16 (C13Concrete.read16 sig (16 + 16 * 6)))) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) := by
  have hSk := C13Concrete.parseSignatureC13_fors_sk_getElem?
    (v := v) (sig := sig) (s := sigParsed) hparse (i := 6) (by decide)
  have hSkGetD :
      (sigParsed.fors.sk[6]?).getD ⟨#[]⟩
        = C13Concrete.read16 sig (16 + 16 * 6) := by
    rw [hSk]
    rfl
  have hBaseLt : C13Concrete.adrsForsBase
      (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest) < 2 ^ 256 :=
    lt_trans
      (C13Concrete.adrsForsBase_lt_of_bounds
        (lt_trans hTlt (by decide : (2 : Nat) ^ 11 < 2 ^ 64))
        (lt_trans (C13Concrete.idxLeaf0C13_lt _) (by decide : (2 : Nat) ^ 11 < 2 ^ 32)))
      (by decide : (2 : Nat) ^ 192 < 2 ^ 256)
  have hcell :=
    SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_forced_root_cell
      (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))
      (wordOfHash16 pk.pkSeed)
      (C13Concrete.adrsForsBase
        (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
      (wordOfHash16 (C13Concrete.read16 sig (16 + 16 * 6)))
      hmSeed hbaseF hBaseLt hLastSecret
  rw [hcell]
  rw [C13Concrete.forsAllRootsC13_getElem_forced]
  unfold C13Concrete.forsForcedRootC13
  rw [hSkGetD]
  simp [C13Concrete.adrsForsLeaf]

/-- Calldata-framed forced-root cell bridge.  This composes
`finalSecret_eval_eq_wordOfHash16` with
`forcedRootCell_eq_forsAllRootsC13_of_parse`, so callers only need to show that
`afterFors` still carries the frozen calldata image and `sigBase` binding. -/
theorem forcedRootCell_eq_forsAllRootsC13_of_parse_calldata
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hmSeed :
      ((afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pk.pkSeed)
    (hbase :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "sigBase" = sigDataOffset)
    (hsel : (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).selector = 0)
    (hcd :
      (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).world.calldata
        = headWords pk.pkSeed pk.pkRoot message sig.size ++ bytesToWords sig) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) := by
  exact forcedRootCell_eq_forsAllRootsC13_of_parse pk digest message sig hparse
    hbaseF hTlt hmSeed
    (finalSecret_eval_eq_wordOfHash16
      (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))
      pk.pkSeed pk.pkRoot message sig hbase hsel hcd)

/-- Static-frame forced-root cell bridge.  The only remaining premise is the
`afterFors` seed cell; the signature base, selector, and calldata image are
supplied by the frozen `mkC13State` frame lemmas above. -/
theorem forcedRootCell_eq_forsAllRootsC13_of_parse_static
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hmSeed :
      ((afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pk.pkSeed) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) :=
  forcedRootCell_eq_forsAllRootsC13_of_parse_calldata pk digest message sig hparse
    hbaseF hTlt hmSeed
    (afterFors_sigBase_mkC13State pk.pkSeed pk.pkRoot message sig)
    (afterFors_selector_mkC13State pk.pkSeed pk.pkRoot message sig)
    (afterFors_calldata_mkC13State pk.pkSeed pk.pkRoot message sig)

/-- Range-seed version of the forced-root cell bridge.  This is the shape needed
by the final accept adapter: once the range-gated FORS leaf-step seed frame is
available, the forced seventh root cell is fully pinned to
`forsAllRootsC13[6]`. -/
theorem forcedRootCell_eq_forsAllRootsC13_of_parse_range_seed
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) :=
  forcedRootCell_eq_forsAllRootsC13_of_parse_static pk digest message sig hparse
    hbaseF hTlt
    (afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
      pk.pkSeed pk.pkRoot message sig hLeaf)

/-- Concrete forced-root cell bridge with the `afterFors` seed cell discharged
from the actual six C13 outer-loop prefixes. -/
theorem forcedRootCell_eq_forsAllRootsC13_of_parse_concrete
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11) :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) :=
  forcedRootCell_eq_forsAllRootsC13_of_parse_static pk digest message sig hparse
    hbaseF hTlt
    (afterFors_seed_slot_mkC13State pk.pkSeed pk.pkRoot message sig)

/-- Combined C13 FORS root-cell handoff: the six ordinary roots are discharged by
the frozen-calldata node facts, and the forced seventh root is discharged from the
parse-shaped forced-root bridge plus the range-gated seed-cell frame.  This is
the exact `hmRlo`/`hmRlast` pair expected by the final accept-path obligations. -/
theorem rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse_range_seed
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = headWords pk.pkSeed pk.pkRoot message sig.size ++ bytesToWords sig ∧
        lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hNode : ∀ j, (hj : j < 6) →
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)) with
                    bindings :=
                      bindValue (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
                        "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)) with
                        bindings :=
                          bindValue
                            (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
                            "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega))
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    (∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega))
      ∧
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) := by
  constructor
  · exact normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes
      (mkC13State pk.pkSeed pk.pkRoot message sig) pk digest sigParsed.fors
      pk.pkSeed pk.pkRoot message sig hsite hNode
  · exact forcedRootCell_eq_forsAllRootsC13_of_parse_range_seed
      pk digest message sig hparse hbaseF hTlt hLeaf

/-- Concrete combined C13 FORS root-cell handoff.  The six ordinary roots remain
the frozen-calldata node obligations; the forced root no longer needs an external
range-gated seed-frame premise because the concrete `afterFors` seed cell is
proved from the actual C13 outer-loop prefixes. -/
theorem rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = headWords pk.pkSeed pk.pkRoot message sig.size ++ bytesToWords sig ∧
        lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (hNode : ∀ j, (hj : j < 6) →
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)) with
                    bindings :=
                      bindValue (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
                        "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)) with
                        bindings :=
                          bindValue
                            (afterForsSetup (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
                            "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)) :
    (∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega))
      ∧
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) := by
  constructor
  · exact normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes
      (mkC13State pk.pkSeed pk.pkRoot message sig) pk digest sigParsed.fors
      pk.pkSeed pk.pkRoot message sig hsite hNode
  · exact forcedRootCell_eq_forsAllRootsC13_of_parse_concrete
      pk digest message sig hparse hbaseF hTlt

/-- Concrete frozen-entry root-cell handoff for all seven FORS roots.  The six
ordinary roots are reduced to the six post-inner `"node"` correspondences, and
the forced seventh root is discharged from parsing plus the concrete
`afterFors` seed-cell theorem. -/
theorem rootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes_and_parse
    {v : Variant} (pk : PublicKey) (digest : HMsg)
    (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 v sig = some sigParsed)
    (hbaseF :
      lookupValue (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig)).bindings
        "forsBase"
      = C13Concrete.adrsForsBase
          (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest))
    (hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11)
    (hNode : ∀ j, (hj : j < 6) →
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              (forsOuterLeafState pk.pkSeed pk.pkRoot message sig j))).bindings "node") =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)) :
    (∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega))
      ∧
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) := by
  constructor
  · exact normalRootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes
      pk digest message sig sigParsed.fors hNode
  · exact forcedRootCell_eq_forsAllRootsC13_of_parse_concrete
      pk digest message sig hparse hbaseF hTlt

/-- Fully concrete C13 FORS root-cell handoff for the actual parsed `H_msg`.
The six normal roots are supplied by the concrete outer-leaf node theorem, and
the forced root is supplied by the concrete forced-root parse bridge. -/
theorem rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
    (pk : PublicKey) (message sig : ByteArray) {sigParsed : Signature}
    (hparse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    (∀ j, (hj : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega))
      ∧
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pk.pkSeed pk.pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
        rw [C13Concrete.forsAllRootsC13_length]
        decide) := by
  have hbaseF :=
    afterFors_forsBase_mkC13State pk.pkSeed pk.pkRoot message sig
  rw [← C13Concrete.parseSignatureC13_R hparse] at hbaseF
  exact
    rootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes_and_parse
      pk (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
      message sig hparse hbaseF
      (C13Concrete.idxTree0C13_lt pk sigParsed.R message)
      (fun j hj =>
        forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse_concrete
          pk message sig hparse j hj)

/-! ## Layer-loop lift for `currentNode`. -/

/-- A compact relation saying that a runtime state's `"currentNode"` binding is
the word encoding of a spec-side byte node. -/
def CurrentNodeRel {α : Type} (toWord : α → Nat) (st : RuntimeState) (a : α) : Prop :=
  lookupValue st.bindings "currentNode" = toWord a

/-- One-layer adapter from the structural `stepLayer` fact to the relation used
by the final accept composition.  The caller supplies the real data proof that
the post-layer `"merkleNode"` is the spec step's word image; this lemma handles
the final assignment `currentNode := merkleNode`. -/
theorem stepLayer_currentNodeRel_of_merkleNode
    (s : RuntimeState) (specStep : Nat → Bytes → Bytes) (node : Bytes) (idx : Nat)
    (hMerkle :
      lookupValue
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
          "merkleNode"
        = wordOfHash16 (specStep idx node)) :
    CurrentNodeRel wordOfHash16
      (SegmentLayer3.stepLayer
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
      (specStep idx node) := by
  unfold CurrentNodeRel
  rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
  exact hMerkle

/-- If one `stepLayer` iteration tracks a spec step on the `"currentNode"` word,
then the whole `afterLayer` fold tracks the corresponding `specFold`.

This is the layer-loop shape needed for the eventual `hCurrent` proof.  The
per-layer hypothesis is deliberately abstract: callers can instantiate `α` with a
rich spec accumulator carrying `idxTree`, `sigOff`, parsed layer data, or just the
current byte node, depending on how the WOTS/XMSS correspondence is packaged. -/
theorem afterLayer_currentNode_of_step
    {α : Type} (st : RuntimeState)
    (specStep : Nat → α → α) (toWord : α → Nat) (a0 afinal : α)
    (hStart : lookupValue (afterSeed st).bindings "currentNode" = toWord a0)
    (hStep : ∀ (s : RuntimeState) (a : α) (idx : Nat),
        CurrentNodeRel toWord s a →
        CurrentNodeRel toWord
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx a))
    (hFinal : ClimbLoop.specFold specStep a0 0 (wordNormalize 2) = afinal) :
    lookupValue (afterLayer st).bindings "currentNode" = toWord afinal := by
  let init : RuntimeState :=
    { (afterSeed st) with
      bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
  have hStartInit : CurrentNodeRel toWord init a0 := by
    unfold CurrentNodeRel init
    rw [MemoryKit.lookupValue_bindValue_ne
      (afterSeed st).bindings "layer" "currentNode" (wordNormalize 0) (by decide)]
    exact hStart
  have hFold := ClimbLoop.foldLoop_invariant "layer" SegmentLayer3.stepLayer
    specStep (CurrentNodeRel toWord) hStep init a0 0 (wordNormalize 2) hStartInit
  unfold afterLayer
  change CurrentNodeRel toWord
      (ClimbLoop.foldLoop "layer" SegmentLayer3.stepLayer init 0 (wordNormalize 2)) afinal
  rw [← hFinal]
  exact hFold

/-- Same loop adapter, with the start fact supplied at the FORS-finalize boundary:
if `afterFinalize.forsPk` is the word image of the initial spec accumulator, and
each layer step preserves the relation, then the final compare's left operand is
the word image of the folded spec accumulator. -/
theorem afterLayer_currentNode_of_forsPk_step
    {α : Type} (st : RuntimeState)
    (specStep : Nat → α → α) (toWord : α → Nat) (a0 afinal : α)
    (hForsPk : lookupValue (afterFinalize st).bindings "forsPk" = toWord a0)
    (hStep : ∀ (s : RuntimeState) (a : α) (idx : Nat),
        CurrentNodeRel toWord s a →
        CurrentNodeRel toWord
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx a))
    (hFinal : ClimbLoop.specFold specStep a0 0 (wordNormalize 2) = afinal) :
    lookupValue (afterLayer st).bindings "currentNode" = toWord afinal :=
  afterLayer_currentNode_of_step st specStep toWord a0 afinal
    (by rw [afterSeed_currentNode, hForsPk]) hStep hFinal

/-- Byte-node specialization of `afterLayer_currentNode_of_forsPk_step`, phrased
exactly in the `wordOfHash16` form expected by `SegmentAcceptSpec`. -/
theorem afterLayer_currentNode_wordOfHash16_of_forsPk_step
    (st : RuntimeState)
    (specStep : Nat → Bytes → Bytes) (startNode finalNode : Bytes)
    (hForsPk : lookupValue (afterFinalize st).bindings "forsPk" = wordOfHash16 startNode)
    (hStep : ∀ (s : RuntimeState) (node : Bytes) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hFinal : ClimbLoop.specFold specStep startNode 0 (wordNormalize 2) = finalNode) :
    lookupValue (afterLayer st).bindings "currentNode" = wordOfHash16 finalNode :=
  afterLayer_currentNode_of_forsPk_step st specStep wordOfHash16 startNode finalNode
    hForsPk hStep hFinal

/-- Initial layer-loop state used by concrete C13 after binding the loop counter
to the loop's start value. -/
def c13LayerStartState (st : RuntimeState) : RuntimeState :=
  { (afterSeed st) with
    bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }

/-- First concrete layer iteration state, with `"layer" = 0`. -/
def c13LayerLoopState0 (st : RuntimeState) : RuntimeState :=
  { c13LayerStartState st with
    bindings := bindValue (c13LayerStartState st).bindings "layer" (wordNormalize 0) }

/-- Concrete state after executing C13 layer `0`. -/
def c13LayerAfterStep0 (st : RuntimeState) : RuntimeState :=
  SegmentLayer3.stepLayer (c13LayerLoopState0 st)

/-- Second concrete layer iteration state, with `"layer" = 1`. -/
def c13LayerLoopState1 (st : RuntimeState) : RuntimeState :=
  { c13LayerAfterStep0 st with
    bindings := bindValue (c13LayerAfterStep0 st).bindings "layer" (wordNormalize 1) }

/-- Two-step C13 specialization of
`afterLayer_currentNode_wordOfHash16_of_forsPk_step`.

The generic theorem above asks for a layer-step relation for every natural
`idx`.  The actual C13 loop is `forEach "layer" 2`, so the final comparison
only depends on the threaded facts for layer `0` and layer `1`.  This bounded
form is the handoff used by the concrete C13 bridge, where parsed signatures
only contain two XMSS layers and no fact can be supplied for `idx >= 2`. -/
theorem afterLayer_currentNode_wordOfHash16_of_forsPk_two_steps
    (st : RuntimeState)
    (specStep : Nat → Bytes → Bytes) (startNode finalNode : Bytes)
    (hForsPk : lookupValue (afterFinalize st).bindings "forsPk" = wordOfHash16 startNode)
    (hStep0 :
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer (c13LayerLoopState0 st))
        (specStep 0 startNode))
    (hStep1 :
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer (c13LayerLoopState1 st))
        (specStep 1 (specStep 0 startNode)))
    (hFinal : ClimbLoop.specFold specStep startNode 0 (wordNormalize 2) = finalNode) :
    lookupValue (afterLayer st).bindings "currentNode" = wordOfHash16 finalNode := by
  have _hStep0 := hStep0
  have hStart :
      lookupValue (afterSeed st).bindings "currentNode" = wordOfHash16 startNode := by
    rw [afterSeed_currentNode, hForsPk]
  have hStartInit : CurrentNodeRel wordOfHash16 (c13LayerStartState st) startNode := by
    unfold CurrentNodeRel c13LayerStartState
    rw [MemoryKit.lookupValue_bindValue_ne
      (afterSeed st).bindings "layer" "currentNode" (wordNormalize 0) (by decide)]
    exact hStart
  have hTwo : wordNormalize 2 = 2 := by
    exact SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256)
  have hSpec :
      specStep 1 (specStep 0 startNode) = finalNode := by
    rw [← hFinal, hTwo]
    rfl
  unfold afterLayer
  rw [hTwo]
  rw [ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_zero]
  unfold CurrentNodeRel c13LayerLoopState1 c13LayerAfterStep0 c13LayerLoopState0 c13LayerStartState at hStep1
  rw [hSpec] at hStep1
  simpa [Nat.zero_add] using hStep1

/-! ## Axiom audit. -/

#print axioms afterSeed_currentNode
#print axioms afterS2_seed_slot_mkC13State
#print axioms afterS3_seed_slot_mkC13State
#print axioms s2Step_preserves_sig_data_offset
#print axioms s2Step_preserves_selector_calldata
#print axioms afterS2_sig_data_offset_mkC13State
#print axioms afterS3_sigBase_mkC13State
#print axioms afterS2_selector_calldata_mkC13State
#print axioms afterS3_selector_calldata_mkC13State
#print axioms forsOuterPrefixState
#print axioms forsOuterLeafState
#print axioms forsOuterPrefix_sigBase_mkC13State
#print axioms forsOuterPrefix_selector_calldata_mkC13State
#print axioms forsOuterPrefix_leafSetupFacts_mkC13State
#print axioms forsOuterLeafState_setupFacts_mkC13State
#print axioms forsLeafStep_preserves_seed_slot_of_mkC13State_prefix
#print axioms forsLeafStep_preserves_root_cell_ne_of_mkC13State_prefix
#print axioms forsOuterPrefix_root_cell_succ_ne_mkC13State
#print axioms forsOuterPrefix_root_cell_suffix_mkC13State
#print axioms forsOuterPrefix_root_cell_iteration_node_mkC13State
#print axioms afterFors_eq_forsOuterPrefixState_mkC13State
#print axioms forsOuterPrefix_seed_slot_mkC13State
#print axioms afterFors_seed_slot_mkC13State
#print axioms afterFors_sigBase_mkC13State
#print axioms afterFors_htIdx_mkC13State
#print axioms afterFors_selector_calldata_mkC13State
#print axioms afterFors_selector_mkC13State
#print axioms afterFors_calldata_mkC13State
#print axioms forsFinalizeStep_preserves_sigBase
#print axioms forsFinalizeStep_preserves_htIdx
#print axioms forsFinalizeStep_preserves_selector_calldata
#print axioms afterFinalize_sigBase_mkC13State
#print axioms afterFinalize_htIdx_mkC13State
#print axioms afterFinalize_seed_slot_mkC13State
#print axioms afterFinalize_selector_calldata_mkC13State
#print axioms stepSeed_preserves_sigBase
#print axioms stepSeed_preserves_htIdx
#print axioms stepSeed_preserves_selector_calldata
#print axioms stepSeed_preserves_memory_zero
#print axioms afterSeed_sigBase_mkC13State
#print axioms afterSeed_htIdx_mkC13State
#print axioms afterSeed_selector_calldata_mkC13State
#print axioms afterSeed_selector_mkC13State
#print axioms afterSeed_calldata_mkC13State
#print axioms afterSeed_seed_slot_mkC13State
#print axioms afterFors_seed_slot_of_forsLeafStep_preserves
#print axioms afterFors_seed_slot_of_forsLeafStep_bound_preserves
#print axioms afterFors_seed_slot_of_forsLeafStep_range_preserves
#print axioms afterFors_seed_slot_mkC13State_of_forsLeafStep_preserves
#print axioms afterFors_seed_slot_mkC13State_of_forsLeafStep_bound_preserves
#print axioms afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
#print axioms normalRootCell_eq_of_outer_iteration_node
#print axioms normalRootCells_eq_forsAllRootsC13_of_iteration_nodes
#print axioms normalRootCell_eq_of_fors_frozen_calldata_node
#print axioms normalRootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes
#print axioms normalRootCell_eq_of_mkC13State_iteration_node
#print axioms normalRootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes
#print axioms forsAuthCdAt
#print axioms forsOuterLeafState_node_eq_forsAllRootsC13_of_eval_parse
#print axioms forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_eval_parse
#print axioms forsLeafAddress_eval_eq_adrsForsLeaf
#print axioms forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_eval_parse
#print axioms afterS3_dVal_mkC13State
#print axioms afterS3_htIdx_mkC13State
#print axioms forsOuterPrefix_dVal_mkC13State
#print axioms forsOuterLeafState_dVal_mkC13State
#print axioms forsOuterLeafState_treeIdx_eval_eq_hMsg_parse
#print axioms forsSecret_eval_eq_wordOfHash16_parse
#print axioms forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_secret_parse
#print axioms forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse
#print axioms forsOuterLeafState_node_eq_forsAllRootsC13_of_hMsg_setup_tree_secret_parse_concrete
#print axioms afterSeed_idxTree
#print axioms afterSeed_sigOff
#print axioms afterFinalize_forsPk_of_compress
#print axioms forsPkCompressWord_eq_of_memory
#print axioms forsPkCompressWord_eq_of_preCopy_roots
#print axioms forsPkCompressWord_eq_of_preCopy_frame
#print axioms forsPkCompressWord_eq_of_preCopy_frame_six_plus_last
#print axioms forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last
#print axioms forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last_range
#print axioms forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
#print axioms forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last
#print axioms finalSecret_eval_eq_wordOfHash16
#print axioms forcedRootCell_eq_forsAllRootsC13_of_parse
#print axioms forcedRootCell_eq_forsAllRootsC13_of_parse_calldata
#print axioms forcedRootCell_eq_forsAllRootsC13_of_parse_static
#print axioms forcedRootCell_eq_forsAllRootsC13_of_parse_range_seed
#print axioms forcedRootCell_eq_forsAllRootsC13_of_parse_concrete
#print axioms rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse_range_seed
#print axioms rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse
#print axioms rootCells_eq_forsAllRootsC13_of_mkC13State_iteration_nodes_and_parse
#print axioms rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
#print axioms stepLayer_currentNodeRel_of_merkleNode
#print axioms afterLayer_currentNode_of_step
#print axioms afterLayer_currentNode_of_forsPk_step
#print axioms afterLayer_currentNode_wordOfHash16_of_forsPk_step
#print axioms afterLayer_currentNode_wordOfHash16_of_forsPk_two_steps

end SphincsMinusVerifiers.CurrentNodeFrame
