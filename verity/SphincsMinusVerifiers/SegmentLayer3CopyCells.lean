/-
  SegmentLayer3CopyCells — lightweight WOTS/copy chain-cell lemmas for the
  Layer-3 XMSS body.

  This module contains the WOTS outer-loop and WOTS-PK copy-loop facts needed by
  the C13 chain-cell closure.  It avoids importing the full `SegmentLayer3`
  layer-body reconstruction, so downstream closure proofs can use these facts
  without rebuilding the whole layer module.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.ClimbMemFrame
import SphincsMinusVerifiers.InitialNodeKeccak
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentLayer3CopyCells

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK wotsChainBody stepWots
  wotsChainStep execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmt_letVar_continue)
open SphincsMinusVerifiers.ClimbLoop (foldLoop execStmt_forEach_of_step)
open SphincsMinusVerifiers.BindingFrame

/-! ## EDSL constructors for the WOTS/copy slice. -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def cdload (off : Expr) : Expr := .calldataload off
private def mloadE (off : Expr) : Expr := .mload off
private def mstoreE (off val : Expr) : Stmt := .mstore off val

/-- Low-three-bit mask used by the WOTS+C checksum loop. -/
theorem nat_land_low3 (x : Nat) : Nat.land x 0x7 = x % 8 := by
  change (x &&& (2 ^ 3 - 1)) = x % 2 ^ 3
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 3
  · have hmask : (2 ^ 3 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 3 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

/-- Low-eleven-bit mask used by the C13 hypertree layer split. -/
theorem nat_land_low11 (x : Nat) : Nat.land x 0x7FF = x % 2 ^ 11 := by
  change (x &&& (2 ^ 11 - 1)) = x % 2 ^ 11
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 11
  · have hmask : (2 ^ 11 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 11 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

/-- The WOTS-chain outer-loop body (`forEach "i" (u 43)`), with its inner
variable-bound chain `forEach "step" (v "steps")` written as `wotsChainBody`. -/
def wotsOuterBody : List Stmt :=
  [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 0x7))
  , .letVar "steps" (subE (u 7) (v "digit"))
  , .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
  , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
  , .forEach "step" (v "steps") wotsChainBody
  , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ]

/-- The WOTS outer-loop body before the final public-key scratch store. -/
def wotsOuterPrefix : List Stmt :=
  [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 0x7))
  , .letVar "steps" (subE (u 7) (v "digit"))
  , .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
  , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
  , .forEach "step" (v "steps") wotsChainBody ]

def wotsOuterStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st wotsOuterBody with | .continue s' => s' | _ => st

theorem wotsOuterStepLemma (st : RuntimeState) :
    execStmtList [] st wotsOuterBody = .continue (wotsOuterStep st) := by
  unfold wotsOuterStep wotsOuterBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "digit" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "steps" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "val" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "chainBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "step" (v "steps") wotsChainBody _ _ stepWots rfl wotsChainStep)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- One WOTS outer-loop step preserves any binding not written by the body or
its inner chain loop. -/
theorem wotsOuterStep_preserves_lookup_of_ne
    (st : RuntimeState) (key : String)
    (hneDigit : "digit" ≠ key) (hneSteps : "steps" ≠ key)
    (hneVal : "val" ≠ key) (hneChainBase : "chainBase" ≠ key)
    (hneStep : "step" ≠ key) :
    lookupValue (wotsOuterStep st).bindings key =
      lookupValue st.bindings key := by
  refine execStmtList_preserves_lookup key wotsOuterBody st (wotsOuterStep st) ?_
    (wotsOuterStepLemma st)
  intro s s'' stmt hmem hexec
  simp [wotsOuterBody, mstoreE] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup s s'' "digit" key _ hneDigit hexec
  · exact execStmt_letVar_preserves_lookup s s'' "steps" key _ hneSteps hexec
  · exact execStmt_letVar_preserves_lookup s s'' "val" key _ hneVal hexec
  · exact execStmt_letVar_preserves_lookup s s'' "chainBase" key _ hneChainBase hexec
  · exact execStmt_forEach_preserves_lookup "step" key _ _ _ _ hneStep
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsChainBody] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact execStmt_mstore_preserves_lookup t t'' key _ _ hexec'
        · exact execStmt_mstore_preserves_lookup t t'' key _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup t t'' "val" key _ hneVal hexec')
      hexec
  · exact execStmt_mstore_preserves_lookup s s'' key _ _ hexec

/-- One WOTS chain step preserves lookups other than its `"val"` assignment. -/
theorem stepWots_preserves_lookup_of_ne
    (st : RuntimeState) (key : String) (hne : "val" ≠ key) :
    lookupValue (stepWots st).bindings key =
      lookupValue st.bindings key := by
  refine execStmtList_preserves_lookup key wotsChainBody st (stepWots st) ?_
    (wotsChainStep st)
  intro s s'' stmt hmem hexec
  simp [wotsChainBody] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact execStmt_mstore_preserves_lookup s s'' key _ _ hexec
  · exact execStmt_mstore_preserves_lookup s s'' key _ _ hexec
  · exact execStmt_assignVar_preserves_lookup s s'' "val" key _ hne hexec

/-- The WOTS-pk copy loop body (`forEach "i" (u 43)`). -/
def copyBody : List Stmt :=
  [ mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) ]

def copyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st copyBody with | .continue s' => s' | _ => st

theorem copyStepLemma (st : RuntimeState) :
    execStmtList [] st copyBody = .continue (copyStep st) := by
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

private theorem copyIdxNorm43 (idx : Nat) (hidx : idx < 43) :
    wordNormalize idx = idx :=
  SegmentS2.wordNormalize_of_lt (lt_trans hidx (by decide : 43 < 2 ^ 256))

private theorem copyIdxShl5_lt43 (idx : Nat) (hidx : idx < 43) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have : idx * 2 ^ 5 < 43 * 2 ^ 5 :=
    Nat.mul_lt_mul_of_pos_right hidx (by decide : 0 < 2 ^ 5)
  exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)

private theorem copyAddIdxShl5_lt43 (base idx : Nat) (hbase : base ≤ 0x80)
    (hidx : idx < 43) :
    base + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : base + idx * 2 ^ 5 < 0x80 + 43 * 2 ^ 5 := by
    nlinarith [hbase,
      Nat.mul_lt_mul_of_pos_right hidx (by decide : 0 < 2 ^ 5)]
  exact lt_trans hle (by decide : 0x80 + 43 * 2 ^ 5 < 2 ^ 256)

private theorem copyOffset43 (s : RuntimeState) (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 43) :
    evalExpr [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      (addE (u base) (shlE (u 5) (v "i"))) = some (base + 32 * idx) := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have h5 : evalExpr [] st (u 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [SegmentS2.wordNormalize_of_lt (by decide : 5 < 2 ^ 256)]
  have hi : evalExpr [] st (v "i") = some idx := by
    show some (lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i") = some idx
    rw [MemoryKit.lookupValue_bindValue_self, copyIdxNorm43 idx hidx]
  have hsh : evalExpr [] st (shlE (u 5) (v "i")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded st (u 5) (v "i")
      5 idx h5 hi (by decide) (lt_trans hidx (by decide : 43 < 2 ^ 256))
      (copyIdxShl5_lt43 idx hidx)
  have hbaseLit : evalExpr [] st (u base) = some base := by
    show some (wordNormalize base) = some base
    rw [SegmentS2.wordNormalize_of_lt (lt_of_le_of_lt hbase (by decide : 0x80 < 2 ^ 256))]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded st (u base)
    (shlE (u 5) (v "i")) base (idx <<< 5) hbaseLit hsh
    (lt_of_le_of_lt hbase (by decide : 0x80 < 2 ^ 256)) (copyIdxShl5_lt43 idx hidx)
    (copyAddIdxShl5_lt43 base idx hbase hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

/-- One WOTS chain step only writes scratch cells `0x20` and `0x40`, so it
preserves seed cell `0x00`. -/
theorem stepWots_preserves_memory_zero (st : RuntimeState) :
    ((stepWots st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 wotsChainBody st (stepWots st) ?_ (wotsChainStep st)
  intro s s'' stmt hmem hexec
  simp [wotsChainBody] at hmem
  rcases hmem with rfl | rfl | rfl
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    cases hoff
    decide
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    cases hoff
    decide
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
      s s'' 0x00 "val" _ hexec

/-- A folded WOTS chain preserves seed cell `0x00`. -/
theorem wotsChainFold_preserves_memory_zero (st : RuntimeState) (n : Nat) :
    ((foldLoop "step" stepWots
        { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
        0 (wordNormalize n)).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val
    "step" stepWots 0x00 stepWots_preserves_memory_zero
    { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
    0 (wordNormalize n)]

/-- A folded WOTS chain preserves outer-loop index `"i"`. -/
theorem wotsChainFold_preserves_i_lookup (st : RuntimeState) (n : Nat) :
    lookupValue
        (foldLoop "step" stepWots
          { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
          0 n).bindings "i" =
      lookupValue st.bindings "i" := by
  rw [ClimbLoop.foldLoop_preserves_lookup "step" "i" stepWots (by decide)
    (fun s => stepWots_preserves_lookup_of_ne s "i" (by decide))
    { st with bindings := bindValue st.bindings "step" (wordNormalize 0) }
    0 n]
  exact MemoryKit.lookupValue_bindValue_ne st.bindings "step" "i" (wordNormalize 0) (by decide)

/-- **`wotsChainFold_val_eq_chainHash`** — the C13 WOTS chain fold-loop value:
`remaining` iterations of `stepWots` thread the spec one-step transformer
`wotsSpecStep seed chainBase digit` over the `"val"` binding, equalling
`chainHash seed chainBase digit remaining index val₀` by `chainHash_eq_specFold`.

Hypothesis form for the C13 WOTS chain fold:
the loop entry carries `seed` at scratch `0x00`, `chainBase`/`digit` in its
bindings, an inbound `"val"` `< 2^256`, and `index + remaining ≤ 7` (digits are
3-bit so chain depth is at most `7`).  Bounds on `chainBase`, `digit`, `index`,
and the OR-assembled ADRS sub-word are all derivable from the conjunction
`chainBase < 2^256 ∧ digit ≤ 7 ∧ index + remaining ≤ 7`, so the caller supplies
only this minimal package. -/
theorem wotsChainFold_val_eq_chainHash
    (seed chainBase digit : Nat)
    (hCBlt : chainBase < 2 ^ 256) (hDigitLe : digit ≤ 7) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (state.world.memory 0x00).val = seed →
      lookupValue state.bindings "chainBase" = chainBase →
      lookupValue state.bindings "digit" = digit →
      lookupValue state.bindings "val" < 2 ^ 256 →
      index + remaining ≤ 7 →
      lookupValue
          (ClimbLoop.foldLoop "step" stepWots state index remaining).bindings "val" =
        SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
          remaining index (lookupValue state.bindings "val") := by
  intro state index remaining
  induction remaining generalizing state index with
  | zero =>
      intro _ _ _ _ _
      rw [ClimbLoop.foldLoop_zero]
      rfl
  | succ r ih =>
      intro hSeed hCB hDigit hValLt hSum
      rw [ClimbLoop.foldLoop_succ]
      -- Bound derivations.
      have hIdxLe : index ≤ 7 := by omega
      have hIdxLt256 : index < 2 ^ 256 := by
        have h7 : (7 : Nat) < 2 ^ 256 := by decide
        omega
      have hWnIdx : wordNormalize index = index := by
        rw [wordNormalize_eq_mod,
          show (Compiler.Constants.evmModulus : Nat) = 2 ^ 256 from rfl]
        exact Nat.mod_eq_of_lt hIdxLt256
      have hDigitLt256 : digit < 2 ^ 256 := by
        have h7 : (7 : Nat) < 2 ^ 256 := by decide
        omega
      have hSumLe : digit + index ≤ 14 := by omega
      have hSumLt256 : digit + index < 2 ^ 256 := by
        have h14 : (14 : Nat) < 2 ^ 256 := by decide
        omega
      have hAdrsLt : chainBase ||| (digit + index) < 2 ^ 256 := by
        show Nat.bitwise or chainBase (digit + index) < 2 ^ 256
        exact Nat.bitwise_lt_two_pow hCBlt hSumLt256
      -- The state immediately after binding "step" := wordNormalize index.
      set state1 : RuntimeState :=
        { state with bindings := bindValue state.bindings "step" (wordNormalize index) }
        with hst1
      have hCB1 : lookupValue state1.bindings "chainBase" = chainBase := by
        show lookupValue (bindValue state.bindings "step" _) "chainBase" = chainBase
        rw [MemoryKit.lookupValue_bindValue_ne state.bindings "step" "chainBase" _ (by decide)]
        exact hCB
      have hDigit1 : lookupValue state1.bindings "digit" = digit := by
        show lookupValue (bindValue state.bindings "step" _) "digit" = digit
        rw [MemoryKit.lookupValue_bindValue_ne state.bindings "step" "digit" _ (by decide)]
        exact hDigit
      have hVal1 : lookupValue state1.bindings "val" = lookupValue state.bindings "val" := by
        show lookupValue (bindValue state.bindings "step" _) "val" = _
        rw [MemoryKit.lookupValue_bindValue_ne state.bindings "step" "val" _ (by decide)]
      have hStep1 : lookupValue state1.bindings "step" = index := by
        show lookupValue (bindValue state.bindings "step" _) "step" = index
        rw [MemoryKit.lookupValue_bindValue_self, hWnIdx]
      have hMem1 : (state1.world.memory 0x00).val = seed := hSeed
      have hPrevLt : lookupValue state.bindings "val" < 2 ^ 256 := hValLt
      -- One spec-shape step.
      have hVal2 :
          lookupValue (stepWots state1).bindings "val" =
            SphincsMinusVerifiers.ClimbMemFrame.wotsSpecStep seed chainBase digit index
              (lookupValue state.bindings "val") :=
        SphincsMinusVerifiers.ClimbMemFrame.stepWots_val_eq_wotsSpecStep state1
          seed chainBase digit index (lookupValue state.bindings "val")
          hMem1 hCB1 hDigit1 hStep1 hVal1
          hCBlt hDigitLt256 hIdxLt256 hSumLt256 hAdrsLt hPrevLt
      -- Preserve facts on state2 := stepWots state1, propagating into the IH.
      have hMem2 : ((stepWots state1).world.memory 0x00).val = seed := by
        rw [stepWots_preserves_memory_zero state1]; exact hMem1
      have hCB2 :
          lookupValue (stepWots state1).bindings "chainBase" = chainBase := by
        rw [stepWots_preserves_lookup_of_ne state1 "chainBase" (by decide)]; exact hCB1
      have hDigit2 : lookupValue (stepWots state1).bindings "digit" = digit := by
        rw [stepWots_preserves_lookup_of_ne state1 "digit" (by decide)]; exact hDigit1
      have hVal2Lt : lookupValue (stepWots state1).bindings "val" < 2 ^ 256 := by
        rw [hVal2]
        show Nat.bitwise and _ SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
        apply Nat.bitwise_lt_two_pow
        · have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
            [seed, chainBase ||| (digit + index), lookupValue state.bindings "val"]
          rwa [show (Compiler.Constants.evmModulus : Nat) = 2 ^ 256 from rfl] at this
        · exact SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt
      have hSum2 : (index + 1) + r ≤ 7 := by omega
      have hIH := ih (stepWots state1) (index + 1)
        hMem2 hCB2 hDigit2 hVal2Lt hSum2
      -- Reshape the IH result against `chainHash` definition.
      show lookupValue
          (ClimbLoop.foldLoop "step" stepWots
            (stepWots state1) (index + 1) r).bindings "val" =
        SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
          (r + 1) index (lookupValue state.bindings "val")
      rw [hIH, hVal2]
      rfl

/-- The WOTS outer prefix preserves seed cell `0x00`. -/
theorem wotsOuterPrefix_preserves_memory_zero
    (st s' : RuntimeState)
    (hExec : execStmtList [] st wotsOuterPrefix = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 wotsOuterPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterPrefix] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "chainBase" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "step" 0x00 (v "steps") wotsChainBody s s'' ?_ hexec
    intro t t'' stmt hmem' hexec'
    simp [wotsChainBody] at hmem'
    rcases hmem' with rfl | rfl | rfl
    · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
        t t'' 0x00 _ _ ?_ hexec'
      intro ro rv hoff hval
      cases hoff
      decide
    · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
        t t'' 0x00 _ _ ?_ hexec'
      intro ro rv hoff hval
      cases hoff
      decide
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
        t t'' 0x00 "val" _ hexec'

/-- The WOTS outer prefix preserves the outer-loop index binding `"i"`. -/
theorem wotsOuterPrefix_preserves_i_lookup
    (st s' : RuntimeState)
    (hExec : execStmtList [] st wotsOuterPrefix = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" wotsOuterPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterPrefix] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup s s'' "digit" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "steps" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "val" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "chainBase" "i" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "step" "i" _ _ s s'' (by decide)
      (by
        intro t t'' stmt hmem' hexec'
        simp [wotsChainBody] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact execStmt_mstore_preserves_lookup t t'' "i" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup t t'' "i" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup t t'' "val" "i" _ (by decide) hexec')
      hexec

/-- The WOTS outer prefix only updates bindings and the inner WOTS scratch
cells `0x20`/`0x40`; it preserves every outer source slot
`0x80 + 32*j`. -/
theorem wotsOuterPrefix_preserves_source_slot
    (st s' : RuntimeState) (j : Nat)
    (hExec : execStmtList [] st wotsOuterPrefix = .continue s') :
    (s'.world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    (0x80 + 32 * j) wotsOuterPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterPrefix] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "digit" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "steps" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "val" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "chainBase" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val
      "step" (0x80 + 32 * j) (v "steps") wotsChainBody s s'' ?_ hexec
    intro t t'' stmt hmem' hexec'
    simp [wotsChainBody] at hmem'
    rcases hmem' with rfl | rfl | rfl
    · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
        t t'' (0x80 + 32 * j) _ _ ?_ hexec'
      intro ro rv hoff hval
      cases hoff
      rw [SegmentS2.wordNormalize_of_lt (by decide : 0x20 < 2 ^ 256)]
      omega
    · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
        t t'' (0x80 + 32 * j) _ _ ?_ hexec'
      intro ro rv hoff hval
      cases hoff
      rw [SegmentS2.wordNormalize_of_lt (by decide : 0x40 < 2 ^ 256)]
      omega
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
        t t'' (0x80 + 32 * j) "val" _ hexec'

/-- The final WOTS outer-loop tail store writes the already-computed chain
result into the public-key scratch slot for the current outer index. -/
theorem wotsOuterTail_mstore_mem_at_i
    (st : RuntimeState) (i chainHashResult : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = i)
    (hVal : lookupValue st.bindings "val" = chainHashResult)
    (hValLt : chainHashResult < 2 ^ 256) :
    ∃ s', execStmtList [] st
      [mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")] =
        .continue s'
    ∧ (s'.world.memory (0x80 + 32 * i)).val = chainHashResult := by
  have hIeval : evalExpr [] st (v "i") = some i := by
    change some (lookupValue st.bindings "i") = some i
    rw [hI]
  have hShiftBound : i <<< 5 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have : i * 2 ^ 5 < 43 * 2 ^ 5 := by
      exact Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 2 ^ 5)
    exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)
  have hShift :
      evalExpr [] st (shlE (u 5) (v "i")) = some (i <<< 5) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (u 5) (v "i") 5 i rfl hIeval
      (by decide : 5 < 2 ^ 256)
      (lt_trans hi (by decide : 43 < 2 ^ 256))
      hShiftBound
  have hOff :
      evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
        some (0x80 + (i <<< 5)) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (u 0x80) (shlE (u 5) (v "i")) 0x80 (i <<< 5)
      rfl hShift (by decide : 0x80 < 2 ^ 256) hShiftBound
      (by
        rw [Nat.shiftLeft_eq]
        have : 0x80 + i * 2 ^ 5 < 0x80 + 43 * 2 ^ 5 := by omega
        exact lt_trans this (by decide : 0x80 + 43 * 2 ^ 5 < 2 ^ 256))
  have hValExpr : evalExpr [] st (v "val") = some chainHashResult := by
    change some (lookupValue st.bindings "val") = some chainHashResult
    rw [hVal]
  let sFinal : RuntimeState :=
    { st with world :=
        { st.world with
          memory := MemoryKit.memUpdate st.world.memory (0x80 + 32 * i)
            chainHashResult } }
  have hOff32 : 0x80 + (i <<< 5) = 0x80 + 32 * i := by
    rw [Nat.shiftLeft_eq]
    omega
  have hMstore : execStmt [] st
      (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
      .continue sFinal := by
    unfold sFinal mstoreE
    rw [← hOff32]
    exact execStmt_mstore_continue st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
      (0x80 + (i <<< 5)) chainHashResult hOff hValExpr
  refine ⟨sFinal, ?_, ?_⟩
  · rw [execStmtList_cons_continue _ _ _ _ hMstore]
    rfl
  · unfold sFinal
    rw [MemoryKit.memUpdate_val_same, wordNormalize_eq_mod,
      show (Compiler.Constants.evmModulus : Nat) = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hValLt]

private theorem c13_evalExpr_mul_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) (hprod : k * l < 2 ^ 256) :
    evalExpr [] st (.mul a b) = some (k * l) := by
  show (do
        let lhs : Verity.Core.Uint256 := ← evalExpr [] st a
        let rhs : Verity.Core.Uint256 := ← evalExpr [] st b
        pure (lhs * rhs).val) = some (k * l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat k * Verity.Core.Uint256.ofNat l).val)
    = some (k * l)
  show some (((Verity.Core.Uint256.ofNat k).val * (Verity.Core.Uint256.ofNat l).val)
        % Verity.Core.Uint256.modulus) = some (k * l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hkv, hlv, hmod, Nat.mod_eq_of_lt hprod]

private theorem c13_evalExpr_sub_le_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) (hle : l ≤ k) :
    evalExpr [] st (.sub a b) = some (k - l) := by
  show (do
        let lhs : Verity.Core.Uint256 := ← evalExpr [] st a
        let rhs : Verity.Core.Uint256 := ← evalExpr [] st b
        pure (lhs - rhs).val) = some (k - l)
  rw [ha, hb]
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  show some (Verity.Core.Uint256.sub
      (Verity.Core.Uint256.ofNat k) (Verity.Core.Uint256.ofNat l)).val =
    some (k - l)
  unfold Verity.Core.Uint256.sub
  rw [hkv, hlv, if_pos hle]
  show some (Verity.Core.Uint256.ofNat (k - l)).val = some (k - l)
  exact congrArg some (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le k l) hk))

private theorem c13_evalExpr_subE_7_v_digit
    (st : RuntimeState) (digit : Nat)
    (hDigit : lookupValue st.bindings "digit" = digit) (hDigitLe : digit ≤ 7) :
    evalExpr [] st (subE (u 7) (v "digit")) = some (7 - digit) := by
  have h7 : evalExpr [] st (u 7) = some 7 := by
    show some (wordNormalize 7) = some 7
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 7 < 2 ^ 256)]
  have hd : evalExpr [] st (v "digit") = some digit := by
    show some (lookupValue st.bindings "digit") = some digit
    rw [hDigit]
  have hDigitLt : digit < 2 ^ 256 := by
    have : (7 : Nat) < 2 ^ 256 := by decide
    omega
  exact c13_evalExpr_sub_le_bounded st (u 7) (v "digit") 7 digit h7 hd
    (by decide : 7 < 2 ^ 256) hDigitLt hDigitLe

private theorem c13_execStmt_letVar_steps_eq
    (st : RuntimeState) (digit : Nat)
    (hDigit : lookupValue st.bindings "digit" = digit) (hDigitLe : digit ≤ 7) :
    execStmt [] st (.letVar "steps" (subE (u 7) (v "digit"))) =
      .continue
        { st with bindings := bindValue st.bindings "steps" (7 - digit) } :=
  execStmt_letVar_continue st "steps" (subE (u 7) (v "digit")) (7 - digit)
    (c13_evalExpr_subE_7_v_digit st digit hDigit hDigitLe)

private theorem c13_evalExpr_val_calldata_mask_eq
    (st : RuntimeState) (raw : Nat)
    (hcdload : evalExpr [] st
        (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hraw : raw < 2 ^ 256) :
    evalExpr [] st
        (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK)) =
      some (SphincsMinusVerifierSpec.C13Concrete.maskN raw) :=
  SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedCalldata
    st (addE (v "wotsPtr") (shlE (u 4) (v "i"))) raw hcdload hraw

private theorem c13_execStmt_letVar_val_eq
    (st : RuntimeState) (raw : Nat)
    (hcdload : evalExpr [] st
        (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hraw : raw < 2 ^ 256) :
    execStmt [] st
        (.letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))) =
      .continue
        { st with bindings := (bindValue st.bindings "val"
            (SphincsMinusVerifierSpec.C13Concrete.maskN raw)) } :=
  execStmt_letVar_continue st "val"
    (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
    (SphincsMinusVerifierSpec.C13Concrete.maskN raw)
    (c13_evalExpr_val_calldata_mask_eq st raw hcdload hraw)

private theorem c13_evalExpr_chainBase_eq
    (st : RuntimeState) (wotsAdrs i : Nat)
    (hAdrs : lookupValue st.bindings "wotsAdrs" = wotsAdrs)
    (hI : lookupValue st.bindings "i" = i)
    (hAdrsLt : wotsAdrs < 2 ^ 256) (hILt : i < 2 ^ 256)
    (hShiftLt : i <<< 32 < 2 ^ 256) :
    evalExpr [] st (orE (v "wotsAdrs") (shlE (u 32) (v "i"))) =
      some (wotsAdrs ||| (i <<< 32)) := by
  have h32 : evalExpr [] st (u 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 32 < 2 ^ 256)]
  have hAdrsEval : evalExpr [] st (v "wotsAdrs") = some wotsAdrs := by
    show some (lookupValue st.bindings "wotsAdrs") = some wotsAdrs
    rw [hAdrs]
  have hIEval : evalExpr [] st (v "i") = some i := by
    show some (lookupValue st.bindings "i") = some i
    rw [hI]
  have hShl : evalExpr [] st (shlE (u 32) (v "i")) = some (i <<< 32) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (u 32) (v "i") 32 i h32 hIEval (by decide : 32 < 2 ^ 256)
      hILt hShiftLt
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    st (v "wotsAdrs") (shlE (u 32) (v "i")) wotsAdrs (i <<< 32)
    hAdrsEval hShl hAdrsLt hShiftLt

private theorem c13_execStmt_letVar_chainBase_eq
    (st : RuntimeState) (wotsAdrs i : Nat)
    (hAdrs : lookupValue st.bindings "wotsAdrs" = wotsAdrs)
    (hI : lookupValue st.bindings "i" = i)
    (hAdrsLt : wotsAdrs < 2 ^ 256) (hILt : i < 2 ^ 256)
    (hShiftLt : i <<< 32 < 2 ^ 256) :
    execStmt [] st (.letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))) =
      .continue
        { st with bindings := (bindValue st.bindings "chainBase"
            (wotsAdrs ||| (i <<< 32))) } :=
  execStmt_letVar_continue st "chainBase"
    (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
    (wotsAdrs ||| (i <<< 32))
    (c13_evalExpr_chainBase_eq st wotsAdrs i hAdrs hI hAdrsLt hILt hShiftLt)

theorem wotsOuterDigit_le_seven (x : Nat) : x &&& 7 ≤ 7 := Nat.and_le_right

private theorem c13_evalExpr_digit_eq
    (st : RuntimeState) (i d : Nat)
    (hI : lookupValue st.bindings "i" = i)
    (hD : lookupValue st.bindings "d" = d)
    (hILt : i < 2 ^ 256) (hDLt : d < 2 ^ 256)
    (hMulLt : i * 3 < 2 ^ 256) :
    evalExpr [] st
        (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 7)) =
      some ((d >>> (i * 3)) &&& 7) := by
  have h3 : evalExpr [] st (u 3) = some 3 := by
    show some (wordNormalize 3) = some 3
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 256)]
  have hIEval : evalExpr [] st (v "i") = some i := by
    show some (lookupValue st.bindings "i") = some i
    rw [hI]
  have hDEval : evalExpr [] st (v "d") = some d := by
    show some (lookupValue st.bindings "d") = some d
    rw [hD]
  have hMul : evalExpr [] st (mulE (v "i") (u 3)) = some (i * 3) :=
    c13_evalExpr_mul_bounded st (v "i") (u 3) i 3 hIEval h3
      hILt (by decide : 3 < 2 ^ 256) hMulLt
  have hShr : evalExpr [] st (shrE (mulE (v "i") (u 3)) (v "d")) =
      some (d >>> (i * 3)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (mulE (v "i") (u 3)) (v "d") (i * 3) d hMul hDEval
      hMulLt hDLt
  have hShrLt : d >>> (i * 3) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.shiftRight_le d (i * 3)) hDLt
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
    st (shrE (mulE (v "i") (u 3)) (v "d")) (d >>> (i * 3)) 7 hShr
    hShrLt (by decide : 7 < 2 ^ 256)

private theorem c13_execStmt_letVar_digit_eq
    (st : RuntimeState) (i d : Nat)
    (hI : lookupValue st.bindings "i" = i)
    (hD : lookupValue st.bindings "d" = d)
    (hILt : i < 2 ^ 256) (hDLt : d < 2 ^ 256)
    (hMulLt : i * 3 < 2 ^ 256) :
    execStmt [] st
        (.letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 7))) =
      .continue
        { st with bindings := (bindValue st.bindings "digit"
            ((d >>> (i * 3)) &&& 7)) } :=
  execStmt_letVar_continue st "digit"
    (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 7))
    ((d >>> (i * 3)) &&& 7)
    (c13_evalExpr_digit_eq st i d hI hD hILt hDLt hMulLt)

private theorem c13_chainHash_lt_two_pow
    (seed chainBase digit : Nat) :
    ∀ (fuel step val : Nat), val < 2 ^ 256 →
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
        fuel step val < 2 ^ 256
  | 0, _, val, hval => hval
  | f + 1, step, val, _hval => by
      unfold SphincsMinusVerifierSpec.C13Concrete.chainHash
      apply c13_chainHash_lt_two_pow seed chainBase digit f (step + 1)
      show Nat.bitwise and _ SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
      apply Nat.bitwise_lt_two_pow
      · have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
          [seed, chainBase ||| (digit + step), val]
        rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
      · exact SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt

theorem wotsOuter_chainTail_mem_at_i
    (st : RuntimeState) (i seed chainBase digit val0 : Nat) (hi : i < 43)
    (hCBlt : chainBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hVal0Lt : val0 < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hI : lookupValue st.bindings "i" = i)
    (hCB : lookupValue st.bindings "chainBase" = chainBase)
    (hDigit : lookupValue st.bindings "digit" = digit)
    (hSteps : lookupValue st.bindings "steps" = 7 - digit)
    (hVal : lookupValue st.bindings "val" = val0) :
    ∃ s', execStmtList [] st
      [ .forEach "step" (v "steps") wotsChainBody
      , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ] = .continue s'
    ∧ (s'.world.memory (0x80 + 32 * i)).val =
        SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
          (7 - digit) 0 val0 := by
  set stInit : RuntimeState :=
    { st with bindings := bindValue st.bindings "step" (wordNormalize 0) } with hStInit
  set sLoop : RuntimeState := foldLoop "step" stepWots stInit 0 (7 - digit) with hSLoop
  have hSteps_eval : evalExpr [] st (v "steps") = some (7 - digit) := by
    show some (lookupValue st.bindings "steps") = some (7 - digit)
    rw [hSteps]
  have hForEach : execStmt [] st (.forEach "step" (v "steps") wotsChainBody) =
      .continue sLoop :=
    execStmt_forEach_of_step "step" (v "steps") wotsChainBody st (7 - digit)
      stepWots hSteps_eval wotsChainStep
  have hCB_b : lookupValue stInit.bindings "chainBase" = chainBase := by
    show lookupValue (bindValue st.bindings "step" (wordNormalize 0)) "chainBase" =
      chainBase
    rw [MemoryKit.lookupValue_bindValue_ne _ "step" "chainBase" _ (by decide)]
    exact hCB
  have hDigit_b : lookupValue stInit.bindings "digit" = digit := by
    show lookupValue (bindValue st.bindings "step" (wordNormalize 0)) "digit" = digit
    rw [MemoryKit.lookupValue_bindValue_ne _ "step" "digit" _ (by decide)]
    exact hDigit
  have hVal_b : lookupValue stInit.bindings "val" = val0 := by
    show lookupValue (bindValue st.bindings "step" (wordNormalize 0)) "val" = val0
    rw [MemoryKit.lookupValue_bindValue_ne _ "step" "val" _ (by decide)]
    exact hVal
  have hI_b : lookupValue stInit.bindings "i" = i := by
    show lookupValue (bindValue st.bindings "step" (wordNormalize 0)) "i" = i
    rw [MemoryKit.lookupValue_bindValue_ne _ "step" "i" _ (by decide)]
    exact hI
  have hMemB : (stInit.world.memory 0x00).val = seed := hSeed
  have hValLt_b : lookupValue stInit.bindings "val" < 2 ^ 256 := by
    rw [hVal_b]; exact hVal0Lt
  have hSum_b : 0 + (7 - digit) ≤ 7 := by omega
  have hValChain : lookupValue sLoop.bindings "val" =
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
        (7 - digit) 0 val0 := by
    have hIH := wotsChainFold_val_eq_chainHash seed chainBase digit hCBlt hDigitLe
      stInit 0 (7 - digit) hMemB hCB_b hDigit_b hValLt_b hSum_b
    show lookupValue (foldLoop "step" stepWots stInit 0 (7 - digit)).bindings "val" = _
    rw [hIH, hVal_b]
  have hI_loop : lookupValue sLoop.bindings "i" = i := by
    show lookupValue (foldLoop "step" stepWots stInit 0 (7 - digit)).bindings "i" = i
    rw [wotsChainFold_preserves_i_lookup st (7 - digit)]
    exact hI
  have hResultLt :
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
        (7 - digit) 0 val0 < 2 ^ 256 :=
    c13_chainHash_lt_two_pow seed chainBase digit (7 - digit) 0 val0 hVal0Lt
  obtain ⟨sFinal, hExecMstore, hMemFinal⟩ :=
    wotsOuterTail_mstore_mem_at_i sLoop i
      (SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
        (7 - digit) 0 val0)
      hi hI_loop hValChain hResultLt
  refine ⟨sFinal, ?_, hMemFinal⟩
  rw [execStmtList_cons_continue _ _ _ _ hForEach]
  exact hExecMstore

theorem wotsOuterStep_mem_at_i_via_prefix4
    (st state4 : RuntimeState) (i seed chainBase digit val0 : Nat) (hi : i < 43)
    (hCBlt : chainBase < 2 ^ 256) (hDigitLe : digit ≤ 7)
    (hVal0Lt : val0 < 2 ^ 256)
    (hPrefix4 : execStmtList [] st
      [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 7))
      , .letVar "steps" (subE (u 7) (v "digit"))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
      ] = .continue state4)
    (hMem4 : (state4.world.memory 0x00).val = seed)
    (hI4 : lookupValue state4.bindings "i" = i)
    (hCB4 : lookupValue state4.bindings "chainBase" = chainBase)
    (hDigit4 : lookupValue state4.bindings "digit" = digit)
    (hSteps4 : lookupValue state4.bindings "steps" = 7 - digit)
    (hVal4 : lookupValue state4.bindings "val" = val0) :
    ((wotsOuterStep st).world.memory (0x80 + 32 * i)).val =
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit
        (7 - digit) 0 val0 := by
  obtain ⟨sFinal, hExecTail, hMemFinal⟩ :=
    wotsOuter_chainTail_mem_at_i state4 i seed chainBase digit val0 hi
      hCBlt hDigitLe hVal0Lt hMem4 hI4 hCB4 hDigit4 hSteps4 hVal4
  have hBody : wotsOuterBody =
      [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 7))
      , .letVar "steps" (subE (u 7) (v "digit"))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
      ] ++
      [ .forEach "step" (v "steps") wotsChainBody
      , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ] := rfl
  have hExecBody : execStmtList [] st wotsOuterBody = .continue sFinal := by
    rw [hBody, MemoryKit.execStmtList_append_continue _ _ _ _ hPrefix4]
    exact hExecTail
  unfold wotsOuterStep
  rw [hExecBody]
  exact hMemFinal

set_option maxHeartbeats 600000 in
theorem wotsOuterStep_mem_at_i_eq
    (st : RuntimeState) (i seed d wotsAdrs wotsPtr raw : Nat)
    (hi : i < 43)
    (hDLt : d < 2 ^ 256) (hAdrsLt : wotsAdrs < 2 ^ 256)
    (hRaw : raw < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hI : lookupValue st.bindings "i" = i)
    (hD : lookupValue st.bindings "d" = d)
    (hAdrs : lookupValue st.bindings "wotsAdrs" = wotsAdrs)
    (hWPtr : lookupValue st.bindings "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = i →
        s.world = st.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw) :
    ((wotsOuterStep st).world.memory (0x80 + 32 * i)).val =
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed
        (wotsAdrs ||| (i <<< 32))
        ((d >>> (i * 3)) &&& 7)
        (7 - ((d >>> (i * 3)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw) := by
  have hILt : i < 2 ^ 256 := lt_trans hi (by decide : 43 < 2 ^ 256)
  have hMulLt : i * 3 < 2 ^ 256 := by
    have h1 : i * 3 < 43 * 3 := Nat.mul_lt_mul_of_pos_right hi (by decide)
    exact lt_trans h1 (by decide : 43 * 3 < 2 ^ 256)
  have hShlLt : i <<< 32 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have h1 : i * 2 ^ 32 < 43 * 2 ^ 32 :=
      Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 2 ^ 32)
    exact lt_trans h1 (by decide : 43 * 2 ^ 32 < 2 ^ 256)
  let digit : Nat := (d >>> (i * 3)) &&& 7
  have hDigitLe : digit ≤ 7 := wotsOuterDigit_le_seven _
  have hStep1 := c13_execStmt_letVar_digit_eq st i d hI hD hILt hDLt hMulLt
  let state1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "digit" digit }
  have hDigit1 : lookupValue state1.bindings "digit" = digit := by
    show lookupValue (bindValue st.bindings "digit" digit) "digit" = digit
    rw [MemoryKit.lookupValue_bindValue_self]
  have hStep2 := c13_execStmt_letVar_steps_eq state1 digit hDigit1 hDigitLe
  let state2 : RuntimeState :=
    { state1 with bindings := bindValue state1.bindings "steps" (7 - digit) }
  have hWPtr2 : lookupValue state2.bindings "wotsPtr" = wotsPtr := by
    show lookupValue (bindValue _ "steps" _) "wotsPtr" = wotsPtr
    rw [MemoryKit.lookupValue_bindValue_ne _ "steps" "wotsPtr" _ (by decide)]
    show lookupValue (bindValue st.bindings "digit" _) "wotsPtr" = wotsPtr
    rw [MemoryKit.lookupValue_bindValue_ne _ "digit" "wotsPtr" _ (by decide)]
    exact hWPtr
  have hI2 : lookupValue state2.bindings "i" = i := by
    show lookupValue (bindValue _ "steps" _) "i" = i
    rw [MemoryKit.lookupValue_bindValue_ne _ "steps" "i" _ (by decide)]
    show lookupValue (bindValue st.bindings "digit" _) "i" = i
    rw [MemoryKit.lookupValue_bindValue_ne _ "digit" "i" _ (by decide)]
    exact hI
  have hWorld2 : state2.world = st.world := rfl
  have hcdload2 := hCdLoad state2 hWPtr2 hI2 hWorld2
  have hStep3 := c13_execStmt_letVar_val_eq state2 raw hcdload2 hRaw
  let state3 : RuntimeState :=
    { state2 with bindings := (bindValue state2.bindings "val"
        (SphincsMinusVerifierSpec.C13Concrete.maskN raw)) }
  have hAdrs3 : lookupValue state3.bindings "wotsAdrs" = wotsAdrs := by
    show lookupValue (bindValue _ "val" _) "wotsAdrs" = wotsAdrs
    rw [MemoryKit.lookupValue_bindValue_ne _ "val" "wotsAdrs" _ (by decide)]
    show lookupValue (bindValue _ "steps" _) "wotsAdrs" = wotsAdrs
    rw [MemoryKit.lookupValue_bindValue_ne _ "steps" "wotsAdrs" _ (by decide)]
    show lookupValue (bindValue st.bindings "digit" _) "wotsAdrs" = wotsAdrs
    rw [MemoryKit.lookupValue_bindValue_ne _ "digit" "wotsAdrs" _ (by decide)]
    exact hAdrs
  have hI3 : lookupValue state3.bindings "i" = i := by
    show lookupValue (bindValue _ "val" _) "i" = i
    rw [MemoryKit.lookupValue_bindValue_ne _ "val" "i" _ (by decide)]
    exact hI2
  have hStep4 := c13_execStmt_letVar_chainBase_eq state3 wotsAdrs i hAdrs3 hI3
    hAdrsLt hILt hShlLt
  let state4 : RuntimeState :=
    { state3 with bindings := (bindValue state3.bindings "chainBase"
        (wotsAdrs ||| (i <<< 32))) }
  have hPrefix4 : execStmtList [] st
      [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 7))
      , .letVar "steps" (subE (u 7) (v "digit"))
      , .letVar "val"
          (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
      , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
      ] = .continue state4 := by
    rw [execStmtList_cons_continue _ _ _ _ hStep1]
    rw [execStmtList_cons_continue _ _ _ _ hStep2]
    rw [execStmtList_cons_continue _ _ _ _ hStep3]
    rw [execStmtList_cons_continue _ _ _ _ hStep4]
    rfl
  have hMem4 : (state4.world.memory 0x00).val = seed := hSeed
  have hI4 : lookupValue state4.bindings "i" = i := by
    show lookupValue (bindValue _ "chainBase" _) "i" = i
    rw [MemoryKit.lookupValue_bindValue_ne _ "chainBase" "i" _ (by decide)]
    exact hI3
  have hCB4 : lookupValue state4.bindings "chainBase" = wotsAdrs ||| (i <<< 32) := by
    show lookupValue (bindValue _ "chainBase" _) "chainBase" = _
    rw [MemoryKit.lookupValue_bindValue_self]
  have hDigit4 : lookupValue state4.bindings "digit" = digit := by
    show lookupValue (bindValue _ "chainBase" _) "digit" = digit
    rw [MemoryKit.lookupValue_bindValue_ne _ "chainBase" "digit" _ (by decide)]
    show lookupValue (bindValue _ "val" _) "digit" = digit
    rw [MemoryKit.lookupValue_bindValue_ne _ "val" "digit" _ (by decide)]
    show lookupValue (bindValue _ "steps" _) "digit" = digit
    rw [MemoryKit.lookupValue_bindValue_ne _ "steps" "digit" _ (by decide)]
    exact hDigit1
  have hSteps4 : lookupValue state4.bindings "steps" = 7 - digit := by
    show lookupValue (bindValue _ "chainBase" _) "steps" = 7 - digit
    rw [MemoryKit.lookupValue_bindValue_ne _ "chainBase" "steps" _ (by decide)]
    show lookupValue (bindValue _ "val" _) "steps" = 7 - digit
    rw [MemoryKit.lookupValue_bindValue_ne _ "val" "steps" _ (by decide)]
    show lookupValue (bindValue _ "steps" _) "steps" = 7 - digit
    rw [MemoryKit.lookupValue_bindValue_self]
  have hVal4 : lookupValue state4.bindings "val" =
      SphincsMinusVerifierSpec.C13Concrete.maskN raw := by
    show lookupValue (bindValue _ "chainBase" _) "val" = _
    rw [MemoryKit.lookupValue_bindValue_ne _ "chainBase" "val" _ (by decide)]
    show lookupValue (bindValue _ "val" _) "val" = _
    rw [MemoryKit.lookupValue_bindValue_self]
  have hCBlt : wotsAdrs ||| (i <<< 32) < 2 ^ 256 := by
    show Nat.bitwise or wotsAdrs (i <<< 32) < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hAdrsLt hShlLt
  have hVal0Lt : SphincsMinusVerifierSpec.C13Concrete.maskN raw < 2 ^ 256 := by
    show Nat.bitwise and raw SphincsMinusVerifierSpec.C13Concrete.nMask < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hRaw
      SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt
  exact wotsOuterStep_mem_at_i_via_prefix4 st state4 i seed
    (wotsAdrs ||| (i <<< 32)) digit
    (SphincsMinusVerifierSpec.C13Concrete.maskN raw)
    hi hCBlt hDigitLe hVal0Lt hPrefix4 hMem4 hI4 hCB4 hDigit4 hSteps4 hVal4

/-- Spec-shaped C13 WOTS outer-loop iteration memory fact.

This wraps `wotsOuterStep_mem_at_i_eq` with the layer WOTS digest/address
bindings and the calldata-to-WOTS-chain-word bridge.  It is the per-index
chain-end word that later WOTS-PK preimage lemmas consume. -/
theorem wotsOuterStep_mem_at_i_eq_wotsChainEnd
    (st : RuntimeState) (i seed layer treeIdx leafIdx node wotsPtr raw : Nat)
    (wots : SphincsMinusVerifierSpec.WotsSig)
    (hi : i < 43)
    (hDigestLt :
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node < 2 ^ 256)
    (hAdrsLt :
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer treeIdx leafIdx < 2 ^ 256)
    (hRaw : raw < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hI : lookupValue st.bindings "i" = i)
    (hD : lookupValue st.bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node)
    (hAdrs : lookupValue st.bindings "wotsAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx)
    (hWPtr : lookupValue st.bindings "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = i →
        s.world = st.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hRawChain :
      SphincsMinusVerifierSpec.C13Concrete.maskN raw =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[i]?).getD ⟨#[]⟩)) :
    ((wotsOuterStep st).world.memory (0x80 + 32 * i)).val =
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed
        (SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
          layer treeIdx leafIdx ||| (i <<< 32))
        ((SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
          wots.count node >>> (i * 3)) &&& 7)
        (7 - ((SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
          wots.count node >>> (i * 3)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[i]?).getD ⟨#[]⟩)) := by
  have hStep :=
    wotsOuterStep_mem_at_i_eq st i seed
      (SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node)
      (SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx)
      wotsPtr raw hi hDigestLt hAdrsLt hRaw hSeed hI hD hAdrs hWPtr hCdLoad
  rw [hStep, hRawChain]

/-- Executing one WOTS outer-loop body preserves seed cell `0x00` for the actual
C13 outer-loop index range. -/
theorem wotsOuterBody_preserves_memory_zero_of_i
    (st s' : RuntimeState) (i : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = wordNormalize i)
    (hExec : execStmtList [] st wotsOuterBody = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  have hSplit :
      wotsOuterBody =
        wotsOuterPrefix ++
          [mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")] := rfl
  rw [hSplit, MemoryKit.execStmtList_append] at hExec
  cases hPrefix : execStmtList [] st wotsOuterPrefix with
  | «continue» mid =>
      rw [hPrefix] at hExec
      have hPrefixMem := wotsOuterPrefix_preserves_memory_zero st mid hPrefix
      have hPrefixI := wotsOuterPrefix_preserves_i_lookup st mid hPrefix
      have hINorm : wordNormalize i = i :=
        SegmentS2.wordNormalize_of_lt (lt_trans hi (by decide : 43 < 2 ^ 256))
      have hIeval : evalExpr [] mid (v "i") = some i := by
        change some (lookupValue mid.bindings "i") = some i
        rw [hPrefixI, hI, hINorm]
      have hShiftBound : i <<< 5 < 2 ^ 256 := by
        rw [Nat.shiftLeft_eq]
        have : i * 2 ^ 5 < 43 * 2 ^ 5 := by
          exact Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 2 ^ 5)
        exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)
      have hShift :
          evalExpr [] mid (shlE (u 5) (v "i")) = some (i <<< 5) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
          mid (u 5) (v "i") 5 i rfl hIeval
          (by decide : 5 < 2 ^ 256)
          (lt_trans hi (by decide : 43 < 2 ^ 256))
          hShiftBound
      have hOff :
          evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
            some (0x80 + (i <<< 5)) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          mid (u 0x80) (shlE (u 5) (v "i")) 0x80 (i <<< 5)
          rfl hShift (by decide : 0x80 < 2 ^ 256) hShiftBound
          (by
            rw [Nat.shiftLeft_eq]
            have : 0x80 + i * 2 ^ 5 < 0x80 + 43 * 2 ^ 5 := by omega
            exact lt_trans this (by decide : 0x80 + 43 * 2 ^ 5 < 2 ^ 256))
      have hVal : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let mid' : RuntimeState :=
        { mid with world := { mid.world with
          memory := MemoryKit.memUpdate mid.world.memory (0x80 + (i <<< 5))
            (lookupValue mid.bindings "val") } }
      have hStore :
          execStmt [] mid
              (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
            .continue mid' := by
        unfold mid' mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + (i <<< 5)) (lookupValue mid.bindings "val") hOff hVal
      change
        (match execStmt [] mid
            (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
          | .continue n => execStmtList [] n []
          | .stop n => .stop n
          | .return rv rs => .return rv rs
          | .revert => .revert) = .continue s' at hExec
      rw [hStore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs'
      subst s'
      unfold mid'
      change
        (MemoryKit.memUpdate mid.world.memory (0x80 + (i <<< 5))
            (lookupValue mid.bindings "val") 0x00).val =
          (st.world.memory 0x00).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + (i <<< 5)) 0x00 _ (by omega)]
      exact hPrefixMem
  | stop stopped =>
      rw [hPrefix] at hExec
      simp at hExec
  | «return» rv rst =>
      rw [hPrefix] at hExec
      simp at hExec
  | revert =>
      rw [hPrefix] at hExec
      simp at hExec

/-- One WOTS outer-loop step preserves seed cell `0x00` for the actual C13
outer-loop index range. -/
theorem wotsOuterStep_preserves_memory_zero_of_i
    (st : RuntimeState) (i : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = wordNormalize i) :
    ((wotsOuterStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val :=
  wotsOuterBody_preserves_memory_zero_of_i st (wotsOuterStep st) i hi hI
    (wotsOuterStepLemma st)

/-- Executing one WOTS outer-loop body preserves the outer-loop index binding
`"i"`. -/
theorem wotsOuterBody_preserves_i_lookup (st s' : RuntimeState)
    (hExec : execStmtList [] st wotsOuterBody = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" wotsOuterBody st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp [wotsOuterBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup s s'' "digit" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "steps" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "val" "i" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup s s'' "chainBase" "i" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "step" "i" _ _ s s'' (by decide)
      (by
        intro s' s''' stmt hmem' hexec'
        simp [wotsChainBody] at hmem'
        rcases hmem' with rfl | rfl | rfl
        · exact execStmt_mstore_preserves_lookup s' s''' "i" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup s' s''' "i" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup s' s''' "val" "i" _ (by decide) hexec')
      hexec
  · exact execStmt_mstore_preserves_lookup s s'' "i" _ _ hexec

/-- One WOTS outer-loop step preserves the outer-loop index binding `"i"`. -/
theorem wotsOuterStep_preserves_i_lookup (st : RuntimeState) :
    lookupValue (wotsOuterStep st).bindings "i" =
      lookupValue st.bindings "i" :=
  wotsOuterBody_preserves_i_lookup st (wotsOuterStep st) (wotsOuterStepLemma st)

/-- One WOTS outer-loop step preserves the EVM selector and calldata image: the
body only reads calldata and writes memory/bindings, never the static frame. -/
theorem wotsOuterStep_preserves_sc (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st (wotsOuterStep st) := by
  refine StateFrame.execStmtList_preserves_selector_calldata
    wotsOuterBody st (wotsOuterStep st) ?_ (wotsOuterStepLemma st)
  intro s s'' stmt hmem hexec
  simp [wotsOuterBody, mstoreE] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata s s'' "digit" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata s s'' "steps" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata s s'' "val" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata s s'' "chainBase" _ hexec
  · refine StateFrame.execStmt_forEach_preserves_selector_calldata "step" _ wotsChainBody
      s s'' ?_ hexec
    intro t t'' stmt' hmem' hexec'
    simp [wotsChainBody] at hmem'
    rcases hmem' with rfl | rfl | rfl
    · exact StateFrame.execStmt_mstore_preserves_selector_calldata t t'' _ _ hexec'
    · exact StateFrame.execStmt_mstore_preserves_selector_calldata t t'' _ _ hexec'
    · exact StateFrame.execStmt_assignVar_preserves_selector_calldata t t'' "val" _ hexec'
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata s s'' _ _ hexec

/-- The 43-step WOTS outer fold preserves seed cell `0x00`. -/
theorem wotsOuterFold_preserves_memory_zero (st : RuntimeState) :
    ((foldLoop "i" wotsOuterStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 43)).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i" wotsOuterStep 0x00
    (fun i => i < 43)
    (fun s i hi => by
      have hI :
          lookupValue ({ s with bindings := bindValue s.bindings "i" (wordNormalize i) }).bindings
              "i" =
            wordNormalize i := by
        exact MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize i)
      exact wotsOuterStep_preserves_memory_zero_of_i
        { s with bindings := bindValue s.bindings "i" (wordNormalize i) } i hi hI)
    { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
    0 (wordNormalize 43)
    (fun i _ hi => by simpa using hi)]

/-- The actual WOTS outer-loop statement preserves seed cell `0x00`.  This uses
the interpreter-loop memory frame directly instead of converting the loop to a
pure fold at each call site. -/
theorem wotsOuterForEach_preserves_memory_zero
    (s s'' : RuntimeState)
    (hexec : execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'') :
    (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
    "i" 0x00 (u 43) wotsOuterBody (fun i => i < 43) s s'' ?_ ?_ hexec
  · intro t i hi t'' hbody
    have hI :
        lookupValue ({ t with bindings := bindValue t.bindings "i" (wordNormalize i) }).bindings
            "i" = wordNormalize i := by
      exact MemoryKit.lookupValue_bindValue_self t.bindings "i" (wordNormalize i)
    exact wotsOuterBody_preserves_memory_zero_of_i
      { t with bindings := bindValue t.bindings "i" (wordNormalize i) } t'' i hi hI hbody
  · intro bound i hbound _ hi
    change some (wordNormalize 43) = some bound at hbound
    injection hbound with hbound'
    rw [← hbound'] at hi
    simpa using hi

/-- One WOTS outer-loop body preserves every source slot
`0x80 + 32*j` except the slot written by the current outer index. -/
theorem wotsOuterBody_preserves_source_slot_of_ne
    (st s' : RuntimeState) (idx j : Nat)
    (hidx : idx < 43)
    (hne : j ≠ idx)
    (hI : lookupValue st.bindings "i" = wordNormalize idx)
    (hExec : execStmtList [] st wotsOuterBody = .continue s') :
    (s'.world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  have hSplit :
      wotsOuterBody =
        wotsOuterPrefix ++
          [mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")] := rfl
  rw [hSplit, MemoryKit.execStmtList_append] at hExec
  cases hPrefix : execStmtList [] st wotsOuterPrefix with
  | «continue» mid =>
      rw [hPrefix] at hExec
      have hPrefixMem := wotsOuterPrefix_preserves_source_slot st mid j hPrefix
      have hPrefixI := wotsOuterPrefix_preserves_i_lookup st mid hPrefix
      have hINorm : wordNormalize idx = idx :=
        SegmentS2.wordNormalize_of_lt (lt_trans hidx (by decide : 43 < 2 ^ 256))
      have hIeval : evalExpr [] mid (v "i") = some idx := by
        change some (lookupValue mid.bindings "i") = some idx
        rw [hPrefixI, hI, hINorm]
      have hShiftBound : idx <<< 5 < 2 ^ 256 := by
        rw [Nat.shiftLeft_eq]
        have : idx * 2 ^ 5 < 43 * 2 ^ 5 := by
          exact Nat.mul_lt_mul_of_pos_right hidx (by decide : 0 < 2 ^ 5)
        exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)
      have hShift :
          evalExpr [] mid (shlE (u 5) (v "i")) = some (idx <<< 5) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
          mid (u 5) (v "i") 5 idx rfl hIeval
          (by decide : 5 < 2 ^ 256)
          (lt_trans hidx (by decide : 43 < 2 ^ 256))
          hShiftBound
      have hOff :
          evalExpr [] mid (addE (u 0x80) (shlE (u 5) (v "i"))) =
            some (0x80 + (idx <<< 5)) := by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          mid (u 0x80) (shlE (u 5) (v "i")) 0x80 (idx <<< 5)
          rfl hShift (by decide : 0x80 < 2 ^ 256) hShiftBound
          (by
            rw [Nat.shiftLeft_eq]
            have : 0x80 + idx * 2 ^ 5 < 0x80 + 43 * 2 ^ 5 := by omega
            exact lt_trans this (by decide : 0x80 + 43 * 2 ^ 5 < 2 ^ 256))
      have hVal : evalExpr [] mid (v "val") = some (lookupValue mid.bindings "val") := rfl
      let mid' : RuntimeState :=
        { mid with world := { mid.world with
          memory := MemoryKit.memUpdate mid.world.memory (0x80 + (idx <<< 5))
            (lookupValue mid.bindings "val") } }
      have hStore :
          execStmt [] mid
              (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) =
            .continue mid' := by
        unfold mid' mstoreE
        exact execStmt_mstore_continue mid
          (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")
          (0x80 + (idx <<< 5)) (lookupValue mid.bindings "val") hOff hVal
      change
        (match execStmt [] mid
            (mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val")) with
          | .continue n => execStmtList [] n []
          | .stop n => .stop n
          | .return rv rs => .return rv rs
          | .revert => .revert) = .continue s' at hExec
      rw [hStore] at hExec
      simp only [execStmtList] at hExec
      injection hExec with hs'
      subst s'
      unfold mid'
      change
        (MemoryKit.memUpdate mid.world.memory (0x80 + (idx <<< 5))
            (lookupValue mid.bindings "val") (0x80 + 32 * j)).val =
          (st.world.memory (0x80 + 32 * j)).val
      rw [MemoryKit.memUpdate_diff _ (0x80 + (idx <<< 5)) (0x80 + 32 * j) _
        (by
          rw [Nat.shiftLeft_eq]
          omega)]
      exact hPrefixMem
  | stop stopped =>
      rw [hPrefix] at hExec
      simp at hExec
  | «return» rv rst =>
      rw [hPrefix] at hExec
      simp at hExec
  | revert =>
      rw [hPrefix] at hExec
      simp at hExec

/-- One WOTS outer-loop step preserves every source slot `0x80 + 32*j` except
the slot written by the current outer index. -/
theorem wotsOuterStep_preserves_source_slot_of_ne
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 43) (hne : j ≠ idx) :
    ((wotsOuterStep
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val =
      (s.world.memory (0x80 + 32 * j)).val := by
  have hI :
      lookupValue ({ s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).bindings
          "i" =
        wordNormalize idx := by
    exact MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize idx)
  have hBody :=
    wotsOuterBody_preserves_source_slot_of_ne
      { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      (wotsOuterStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) })
      idx j hidx hne hI
      (wotsOuterStepLemma { s with bindings := bindValue s.bindings "i" (wordNormalize idx) })
  simpa using hBody

/-- Later WOTS outer-loop iterations preserve source slots that have already
been written by earlier iterations. -/
theorem wotsOuterStep_preserves_past_source_slot
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 43) (hlt : j < idx) :
    ((wotsOuterStep
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val =
      (s.world.memory (0x80 + 32 * j)).val :=
  wotsOuterStep_preserves_source_slot_of_ne s idx j hidx (by omega)

set_option maxHeartbeats 1000000 in
/-- Spec-shaped value of one WOTS outer step as the `j`th element of
`InitialNodeKeccak.wotsChainsEnd`. -/
theorem wotsOuterStep_mem_at_i_eq_wotsChainsEnd_cell
    (st : RuntimeState) (i seed layer treeIdx leafIdx node wotsPtr raw : Nat)
    (wots : SphincsMinusVerifierSpec.WotsSig)
    (hi : i < 43)
    (hDigestLt :
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node < 2 ^ 256)
    (hAdrsLt :
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer treeIdx leafIdx < 2 ^ 256)
    (hRaw : raw < 2 ^ 256)
    (hSeed : (st.world.memory 0x00).val = seed)
    (hI : lookupValue st.bindings "i" = i)
    (hD : lookupValue st.bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node)
    (hAdrs : lookupValue st.bindings "wotsAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx)
    (hWPtr : lookupValue st.bindings "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = i →
        s.world = st.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some raw)
    (hRawChain :
      SphincsMinusVerifierSpec.C13Concrete.maskN raw =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[i]?).getD ⟨#[]⟩)) :
    ((wotsOuterStep st).world.memory (0x80 + 32 * i)).val =
      (SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
        seed layer treeIdx leafIdx node wots)[i]'(by
          rw [SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd_length]
          omega) := by
  have hStep :=
    wotsOuterStep_mem_at_i_eq_wotsChainEnd st i seed layer treeIdx leafIdx node
      wotsPtr raw wots hi hDigestLt hAdrsLt hRaw hSeed hI hD hAdrs hWPtr
      hCdLoad hRawChain
  rw [hStep]
  unfold SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem_map_range
    (fun k =>
      let digit :=
        (SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
          wots.count node >>> (3 * k)) % 8
      let steps := 7 - digit
      let val :=
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[k]?).getD ⟨#[]⟩)
      let chainBase :=
        SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx |||
          (k <<< 32)
      SphincsMinusVerifierSpec.C13Concrete.chainHash seed chainBase digit steps 0 val)
    hi]
  let d :=
    SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
      wots.count node
  have hDigit : (d >>> (i * 3) &&& 7) = (d >>> (3 * i)) % 8 := by
    change Nat.land (d >>> (i * 3)) 7 = (d >>> (3 * i)) % 8
    rw [Nat.mul_comm i 3]
    exact nat_land_low3 (d >>> (3 * i))
  dsimp only
  rw [hDigit]

/-- The 43-step WOTS outer fold materializes every reconstructed WOTS chain end
in source slots `0x80 + 32*j`.  The hypotheses expose the state at the target
iteration; suffix preservation carries that target write to the final fold. -/
theorem wotsOuterFold43_source_cells_eq_wotsChainsEnd
    (st : RuntimeState) (seed layer treeIdx leafIdx node wotsPtr : Nat)
    (rawAt : Nat → Nat)
    (wots : SphincsMinusVerifierSpec.WotsSig)
    (hDigestLt :
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node < 2 ^ 256)
    (hAdrsLt :
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer treeIdx leafIdx < 2 ^ 256)
    (hRaw : ∀ j, j < 43 → rawAt j < 2 ^ 256)
    (hSeed : ∀ j, j < 43 →
      ((foldLoop "i" wotsOuterStep st 0 j).world.memory 0x00).val = seed)
    (hD : ∀ j, j < 43 →
      lookupValue (foldLoop "i" wotsOuterStep st 0 j).bindings "d" =
        SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
          wots.count node)
    (hAdrs : ∀ j, j < 43 →
      lookupValue (foldLoop "i" wotsOuterStep st 0 j).bindings "wotsAdrs" =
        SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx)
    (hWPtr : ∀ j, j < 43 →
      lookupValue (foldLoop "i" wotsOuterStep st 0 j).bindings "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ j, j < 43 → ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world = (foldLoop "i" wotsOuterStep st 0 j).world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some (rawAt j))
    (hRawChain : ∀ j, j < 43 →
      SphincsMinusVerifierSpec.C13Concrete.maskN (rawAt j) =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[j]?).getD ⟨#[]⟩)) :
    ∀ j, (hj : j < 43) →
      ((foldLoop "i" wotsOuterStep st 0 43).world.memory (0x80 + 32 * j)).val =
        (SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
          seed layer treeIdx leafIdx node wots)[j]'(by
            rw [SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd_length]
            omega) := by
  intro j hj
  let beforeJ : RuntimeState := foldLoop "i" wotsOuterStep st 0 j
  let atJ : RuntimeState :=
    { beforeJ with bindings := bindValue beforeJ.bindings "i" (wordNormalize j) }
  have hStepAt :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves
      "i" wotsOuterStep (0x80 + 32 * j) st 0 43 j hj
      (fun s idx hgt hlt =>
        wotsOuterStep_preserves_past_source_slot s idx j (by omega) (by simpa using hgt))
  have hJNorm : wordNormalize j = j :=
    SegmentS2.wordNormalize_of_lt (lt_trans hj (by decide : 43 < 2 ^ 256))
  have hIAt : lookupValue atJ.bindings "i" = j := by
    dsimp [atJ]
    rw [MemoryKit.lookupValue_bindValue_self, hJNorm]
  have hSeedAt : (atJ.world.memory 0x00).val = seed := by
    dsimp [atJ, beforeJ]
    exact hSeed j hj
  have hDAt : lookupValue atJ.bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node := by
    dsimp [atJ, beforeJ]
    rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
    exact hD j hj
  have hAdrsAt : lookupValue atJ.bindings "wotsAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx := by
    dsimp [atJ, beforeJ]
    rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
    exact hAdrs j hj
  have hWPtrAt : lookupValue atJ.bindings "wotsPtr" = wotsPtr := by
    dsimp [atJ, beforeJ]
    rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
    exact hWPtr j hj
  have hCdLoadAt : ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world = atJ.world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some (rawAt j) := by
    intro s hw hi hworld
    exact hCdLoad j hj s hw hi (by simpa [atJ, beforeJ] using hworld)
  have hStepMem :
      ((wotsOuterStep atJ).world.memory (0x80 + 32 * j)).val =
        (SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
          seed layer treeIdx leafIdx node wots)[j]'(by
            rw [SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd_length]
            omega) :=
    wotsOuterStep_mem_at_i_eq_wotsChainsEnd_cell atJ j seed layer treeIdx leafIdx
      node wotsPtr (rawAt j) wots hj hDigestLt hAdrsLt (hRaw j hj) hSeedAt
      hIAt hDAt hAdrsAt hWPtrAt hCdLoadAt (hRawChain j hj)
  calc
    ((foldLoop "i" wotsOuterStep st 0 43).world.memory (0x80 + 32 * j)).val
        = ((wotsOuterStep
            { (foldLoop "i" wotsOuterStep st 0 j) with
              bindings :=
                bindValue (foldLoop "i" wotsOuterStep st 0 j).bindings
                  "i" (wordNormalize (0 + j)) }).world.memory
            (0x80 + 32 * j)).val := hStepAt
    _ = ((wotsOuterStep atJ).world.memory (0x80 + 32 * j)).val := by
      simp [atJ, beforeJ]
    _ = (SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
          seed layer treeIdx leafIdx node wots)[j]'(by
            rw [SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd_length]
            omega) := hStepMem

/-- One WOTS public-key copy step preserves seed cell `0x00` for the actual C13
loop-index range. -/
theorem copyStep_preserves_memory_zero_of_i
    (st : RuntimeState) (i : Nat)
    (hi : i < 43)
    (hI : lookupValue st.bindings "i" = wordNormalize i) :
    ((copyStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  have hINorm : wordNormalize i = i :=
    SegmentS2.wordNormalize_of_lt (lt_trans hi (by decide : 43 < 2 ^ 256))
  have hIeval : evalExpr [] st (v "i") = some i := by
    change some (lookupValue st.bindings "i") = some i
    rw [hI, hINorm]
  have hShiftBound : i <<< 5 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have : i * 2 ^ 5 < 43 * 2 ^ 5 := by
      exact Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 2 ^ 5)
    exact lt_trans this (by decide : 43 * 2 ^ 5 < 2 ^ 256)
  have hShift :
      evalExpr [] st (shlE (u 5) (v "i")) = some (i <<< 5) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (u 5) (v "i") 5 i rfl hIeval
      (by decide : 5 < 2 ^ 256)
      (lt_trans hi (by decide : 43 < 2 ^ 256))
      hShiftBound
  have hOff :
      evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
        some (0x40 + (i <<< 5)) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (u 0x40) (shlE (u 5) (v "i")) 0x40 (i <<< 5)
      rfl hShift (by decide : 0x40 < 2 ^ 256) hShiftBound
      (by
        rw [Nat.shiftLeft_eq]
        have : 0x40 + i * 2 ^ 5 < 0x40 + 43 * 2 ^ 5 := by omega
        exact lt_trans this (by decide : 0x40 + 43 * 2 ^ 5 < 2 ^ 256))
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ (0x40 + (i <<< 5)) _ hOff rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ (0x40 + (i <<< 5)) 0x00 _ (by omega)]

/-- The 43-step WOTS public-key copy fold preserves seed cell `0x00`. -/
theorem copyFold_preserves_memory_zero (st : RuntimeState) :
    ((foldLoop "i" copyStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 43)).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i" copyStep 0x00
    (fun i => i < 43)
    (fun s i hi => by
      have hI :
          lookupValue ({ s with bindings := bindValue s.bindings "i" (wordNormalize i) }).bindings
              "i" =
            wordNormalize i := by
        exact MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize i)
      exact copyStep_preserves_memory_zero_of_i
        { s with bindings := bindValue s.bindings "i" (wordNormalize i) } i hi hI)
    { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
    0 (wordNormalize 43)
    (fun i _ hi => by simpa using hi)]

/-- The actual WOTS-public-key copy statement preserves seed cell `0x00`. -/
theorem copyForEach_preserves_memory_zero
    (s s'' : RuntimeState)
    (hexec : execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'') :
    (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
    "i" 0x00 (u 43) copyBody (fun i => i < 43) s s'' ?_ ?_ hexec
  · intro t i hi t'' hbody
    have hI :
        lookupValue ({ t with bindings := bindValue t.bindings "i" (wordNormalize i) }).bindings
            "i" = wordNormalize i := by
      exact MemoryKit.lookupValue_bindValue_self t.bindings "i" (wordNormalize i)
    rw [copyStepLemma] at hbody
    cases hbody
    exact copyStep_preserves_memory_zero_of_i
      { t with bindings := bindValue t.bindings "i" (wordNormalize i) } i hi hI
  · intro bound i hbound _ hi
    change some (wordNormalize 43) = some bound at hbound
    injection hbound with hbound'
    rw [← hbound'] at hi
    simpa using hi

/-- One C13 WOTS-PK copy-loop iteration writes destination slot `0x40 + 32*idx`
from the corresponding source slot `0x80 + 32*idx`. -/
theorem copyStep_copied_slot (s : RuntimeState) (idx : Nat) (hidx : idx < 43) :
    ((copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x40 + 32 * idx)).val
      = (s.world.memory (0x80 + 32 * idx)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    copyOffset43 s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    copyOffset43 s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x40 + 32 * idx)).val =
    (s.world.memory (0x80 + 32 * idx)).val
  rw [MemoryKit.memUpdate_val_same, wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt (s.world.memory (0x80 + 32 * idx)).isLt

/-- One C13 copy-loop iteration preserves every other destination slot
`0x40 + 32*j`. -/
theorem copyStep_preserves_copy_slot
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 43) (hne : j ≠ idx) :
    ((copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x40 + 32 * j)).val
      = (s.world.memory (0x40 + 32 * j)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    copyOffset43 s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    copyOffset43 s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x40 + 32 * j)).val =
    (s.world.memory (0x40 + 32 * j)).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- Copy iterations before `j` preserve source slot `0x80 + 32*j`, so the loop
still reads the original source word when it reaches iteration `j`. -/
theorem copyStep_preserves_future_source_slot
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 43) (hlt : idx < j) :
    ((copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    copyOffset43 s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    copyOffset43 s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x80 + 32 * j)).val =
    (s.world.memory (0x80 + 32 * j)).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- One C13 WOTS-PK copy-loop iteration preserves the WOTS-PK address slot
`0x20`; copy iterations only write the destination range starting at `0x40`. -/
theorem copyStep_preserves_memory_0x20
    (s : RuntimeState) (idx : Nat) (hidx : idx < 43) :
    ((copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        0x20).val
      = (s.world.memory 0x20).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i"))) =
      some (0x40 + 32 * idx) :=
    copyOffset43 s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) =
      some (0x80 + 32 * idx) :=
    copyOffset43 s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val 0x20).val =
    (s.world.memory 0x20).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- The actual WOTS-public-key copy statement preserves the WOTS-PK address
slot `0x20`. -/
theorem copyForEach_preserves_memory_0x20
    (s s'' : RuntimeState)
    (hexec : execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'') :
    (s''.world.memory 0x20).val = (s.world.memory 0x20).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
    "i" 0x20 (u 43) copyBody (fun i => i < 43) s s'' ?_ ?_ hexec
  · intro t i hi t'' hbody
    rw [copyStepLemma] at hbody
    cases hbody
    exact copyStep_preserves_memory_0x20 t i hi
  · intro bound i hbound _ hi
    change some (wordNormalize 43) = some bound at hbound
    injection hbound with hbound'
    rw [← hbound'] at hi
    simpa using hi

/-- The folded 43-iteration copy loop preserves the WOTS-PK address slot
`0x20`. -/
theorem copyFold43_preserves_memory_0x20 (s : RuntimeState) :
    ((foldLoop "i" copyStep s 0 43).world.memory 0x20).val =
      (s.world.memory 0x20).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "i" copyStep 0x20
    (fun i => i < 43)
    (fun t i hi => copyStep_preserves_memory_0x20 t i hi)
    s 0 43
    (fun i _ hi => by simpa using hi)]

/-- Later copy-loop iterations preserve destination slots that have already been
written. -/
theorem copyLoop_preserves_past_copy_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      j < idx →
      idx + remaining ≤ 43 →
      ((foldLoop "i" copyStep s idx remaining).world.memory (0x40 + 32 * j)).val
        = (s.world.memory (0x40 + 32 * j)).val
  | s, idx, 0, j, _, _ => by
      rw [ClimbLoop.foldLoop_zero]
  | s, idx, remaining + 1, j, hj, hbound => by
      have hidx : idx < 43 := by omega
      let s1 : RuntimeState :=
        copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      change ((foldLoop "i" copyStep s1 (idx + 1) remaining).world.memory
          (0x40 + 32 * j)).val = (s.world.memory (0x40 + 32 * j)).val
      rw [copyLoop_preserves_past_copy_slot s1 (idx + 1) remaining j (by omega) (by omega)]
      exact copyStep_preserves_copy_slot s idx j hidx (by omega)

/-- Copy-loop iterations before `j` preserve source slot `0x80 + 32*j`. -/
theorem copyLoop_preserves_future_source_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      idx + remaining ≤ j →
      j < 43 →
      ((foldLoop "i" copyStep s idx remaining).world.memory (0x80 + 32 * j)).val
        = (s.world.memory (0x80 + 32 * j)).val
  | s, idx, 0, j, _, _ => by
      rw [ClimbLoop.foldLoop_zero]
  | s, idx, remaining + 1, j, hfuture, hj => by
      have hidx : idx < 43 := by omega
      let s1 : RuntimeState :=
        copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      change ((foldLoop "i" copyStep s1 (idx + 1) remaining).world.memory
          (0x80 + 32 * j)).val = (s.world.memory (0x80 + 32 * j)).val
      rw [copyLoop_preserves_future_source_slot s1 (idx + 1) remaining j (by omega) hj]
      exact copyStep_preserves_future_source_slot s idx j hidx (by omega)

/-- Whole C13 WOTS-PK copy-loop slot correspondence: if `j` lies in the loop
range, final destination slot `0x40 + 32*j` contains the original source word at
`0x80 + 32*j`. -/
theorem copyLoop_copied_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      idx ≤ j →
      j < idx + remaining →
      idx + remaining ≤ 43 →
      ((foldLoop "i" copyStep s idx remaining).world.memory (0x40 + 32 * j)).val
        = (s.world.memory (0x80 + 32 * j)).val
  | _, _, 0, _, _, hj, _ => by omega
  | s, idx, remaining + 1, j, hle, hlt, hbound => by
      have hidx : idx < 43 := by omega
      let s1 : RuntimeState :=
        copyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      by_cases hji : j = idx
      · change ((foldLoop "i" copyStep s1 (idx + 1) remaining).world.memory
            (0x40 + 32 * j)).val = (s.world.memory (0x80 + 32 * j)).val
        rw [copyLoop_preserves_past_copy_slot s1 (idx + 1) remaining j (by omega) (by omega)]
        simpa [hji] using copyStep_copied_slot s idx hidx
      · have hgt : idx < j := by omega
        change ((foldLoop "i" copyStep s1 (idx + 1) remaining).world.memory
            (0x40 + 32 * j)).val = (s.world.memory (0x80 + 32 * j)).val
        rw [copyLoop_copied_slot s1 (idx + 1) remaining j (by omega) (by omega) (by omega)]
        exact copyStep_preserves_future_source_slot s idx j hidx hgt

/-- The concrete 43-iteration C13 WOTS-PK copy loop copies each source chain-end
slot `0x80 + 32*j` to the final preimage slot `0x40 + 32*j`. -/
theorem copyFold43_copied_slot (s : RuntimeState) (j : Nat) (hj : j < 43) :
    ((foldLoop "i" copyStep s 0 43).world.memory (0x40 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val :=
  copyLoop_copied_slot s 0 43 j (by omega) (by omega) (by omega)

/-- Value-parametric form of `copyFold43_copied_slot`, convenient for threading
spec chain-end words from the WOTS outer fold into the final WOTS-PK preimage. -/
theorem copyFold43_copied_cells
    (s : RuntimeState) (cells : Nat → Nat)
    (hSrc : ∀ j, j < 43 → (s.world.memory (0x80 + 32 * j)).val = cells j) :
    ∀ j, (hj : j < 43) →
      ((foldLoop "i" copyStep s 0 43).world.memory (0x40 + 32 * j)).val =
        cells j := by
  intro j hj
  rw [copyFold43_copied_slot s j hj]
  exact hSrc j hj

/-- Narrow WOTS-outer/copy handoff: if the WOTS outer fold has materialized the
43 spec chain-end words in source slots `0x80 + 32*j`, the following 43-step
copy fold places those same words in the WOTS-PK preimage slots
`0x40 + 32*j`. -/
theorem copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    (st : RuntimeState) (seed layer treeIdx leafIdx node wotsPtr : Nat)
    (rawAt : Nat → Nat)
    (wots : SphincsMinusVerifierSpec.WotsSig)
    (hDigestLt :
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
        wots.count node < 2 ^ 256)
    (hAdrsLt :
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer treeIdx leafIdx < 2 ^ 256)
    (hRaw : ∀ j, j < 43 → rawAt j < 2 ^ 256)
    (hSeed : ∀ j, j < 43 →
      ((foldLoop "i" wotsOuterStep st 0 j).world.memory 0x00).val = seed)
    (hD : ∀ j, j < 43 →
      lookupValue (foldLoop "i" wotsOuterStep st 0 j).bindings "d" =
        SphincsMinusVerifierSpec.C13Concrete.wotsDigest seed layer treeIdx leafIdx
          wots.count node)
    (hAdrs : ∀ j, j < 43 →
      lookupValue (foldLoop "i" wotsOuterStep st 0 j).bindings "wotsAdrs" =
        SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer treeIdx leafIdx)
    (hWPtr : ∀ j, j < 43 →
      lookupValue (foldLoop "i" wotsOuterStep st 0 j).bindings "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ j, j < 43 → ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world = (foldLoop "i" wotsOuterStep st 0 j).world →
        evalExpr [] s
            (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) = some (rawAt j))
    (hRawChain : ∀ j, j < 43 →
      SphincsMinusVerifierSpec.C13Concrete.maskN (rawAt j) =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[j]?).getD ⟨#[]⟩)) :
    ∀ j, (hj : j < 43) →
      ((foldLoop "i" copyStep
          (foldLoop "i" wotsOuterStep st 0 43) 0 43).world.memory
          (0x40 + 32 * j)).val =
        (SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
          seed layer treeIdx leafIdx node wots)[j]'(by
            rw [SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd_length]
            omega) := by
  intro j hj
  rw [copyFold43_copied_slot (foldLoop "i" wotsOuterStep st 0 43) j hj]
  exact wotsOuterFold43_source_cells_eq_wotsChainsEnd
    st seed layer treeIdx leafIdx node wotsPtr rawAt wots hDigestLt hAdrsLt
    hRaw hSeed hD hAdrs hWPtr hCdLoad hRawChain j hj


#print axioms wotsChainFold_val_eq_chainHash
#print axioms wotsOuter_chainTail_mem_at_i
#print axioms wotsOuterStep_mem_at_i_eq_wotsChainsEnd_cell
#print axioms wotsOuterFold43_source_cells_eq_wotsChainsEnd
#print axioms copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43

end SphincsMinusVerifiers.SegmentLayer3CopyCells
