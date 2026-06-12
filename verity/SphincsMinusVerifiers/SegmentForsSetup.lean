/-
  SegmentForsSetup — S4 (FORS) pre-loop hoist segment for the FIPS 205
  uncompressed 32-byte ADRS layout.

  Three statements (13..15 of `c13VerifyBodyTail`):

  ```
  13. letVar "idxLeaf0" := and(htIdx, 0x7FF)    -- low 11 bits of htIdx
  14. letVar "idxTree0" := shr(11, htIdx)       -- high 11 bits of htIdx
  15. letVar "forsBase" := or(shl(128, idxTree0),
                             or(shl(96, 3), shl(64, idxLeaf0)))
                                                -- FIPS 205 §11.2.2 ADRS base
  ```

  These are pure binder writes: no guard, no memory, no calldata — the
  *loop-invariant* ADRS base for the `forEach "i" (u 6)` FORS outer
  loop (statement 16).  In the spec mirror this is the construction of
  `C13Concrete.adrsForsBase idxTree0 idxLeaf0` that the per-tree
  `forsLeafSetupStep` (`SegmentS4Fors.lean`) reads via `"forsBase"`
  and the inner climb's `mstore 0x20` (`ClimbKit.forsAdrs`) reads from.

  Structure (mirrors `SegmentS4Fors.forsLeafSetupStep` exactly):
  `stepForsSetup` is the `match execStmtList` transformer; the headline
  `execForsSetup` has *no* bound hypotheses (the word-normalizing
  interpreter is total, `letVar_continue … rfl` discharges each step).
  The tight `htIdx < 2^22` bound needed for spec identification is
  parametrised in `stepForsSetup_forsBase_eq` and discharged at the
  call site (`SegmentCompose` etc.) from the S3-segment hypertree-index
  bound.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.Model
import SphincsMinusVerifierSpec.C13Concrete
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifiers.MemoryKit
import SphincsMinusVerifiers.ClimbKit
import SphincsMinusVerifiers.ClimbKeccakStep

namespace SphincsMinusVerifiers.SegmentForsSetup

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (lookupValue_bindValue_self lookupValue_bindValue_ne)

/-! Local EDSL helpers (private, file-scoped — see `Model.lean` for the
canonical versions). -/
private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shrE (a b : Expr) : Expr := .shr a b
private def shlE (a b : Expr) : Expr := .shl a b

/-! ## 0. The three setup statements, replicated with bare public constructors. -/

/-- The FORS pre-loop setup segment (statements 13..15 of `c13VerifyBodyTail`). -/
def forsSetupBody : List Stmt :=
  [ .letVar "idxLeaf0" (andE (v "htIdx") (u 0x7FF))
  , .letVar "idxTree0" (shrE (u 11) (v "htIdx"))
  , .letVar "forsBase"
      (orE (shlE (u 128) (v "idxTree0"))
        (orE (shlE (u 96) (u 3)) (shlE (u 64) (v "idxLeaf0")))) ]

/-- Faithfulness: `forsSetupBody` is *exactly* statements 13..15 of
`c13VerifyBodyTail`. -/
theorem forsSetup_eq_slice :
    forsSetupBody = (c13VerifyBodyTail.drop 13).take 3 := rfl

/-! ## 1. The accept-path state transformer. -/

/-- Pure transformer for the FORS pre-loop setup (repo-standard
`match execStmtList` pattern, see `SegmentS4Fors.forsLeafSetupStep`). -/
def stepForsSetup (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsSetupBody with
  | .continue s' => s'
  | _ => st

private theorem letVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.letVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-! ## 2. The headline segment lemma. -/

/-- **`execForsSetup`** — running statements 13..15 of `c13VerifyBodyTail`
over the real interpreter unconditionally continues to `stepForsSetup st`.
Pure binder writes (no guard), so there is no revert branch and no bound
hypotheses are needed: the word-normalizing interpreter is total, so each
`letVar_continue … rfl` discharges definitionally. -/
theorem execForsSetup (st : RuntimeState) :
    execStmtList [] st forsSetupBody = .continue (stepForsSetup st) := by
  unfold stepForsSetup forsSetupBody u v andE orE shrE shlE
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "idxLeaf0" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "idxTree0" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "forsBase" _ _ rfl)]
  rfl

/-! ## 3. Bound helpers for the spec identification. -/

private theorem shr11_lt (htIdx : Nat) (hhtLt : htIdx < 2 ^ 22) :
    htIdx >>> 11 < 2 ^ 11 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul
    (by rw [show (2 : Nat) ^ 11 * 2 ^ 11 = 2 ^ 22 from by norm_num]; exact hhtLt)

private theorem shr11_shl128_lt (htIdx : Nat) (hhtLt : htIdx < 2 ^ 22) :
    (htIdx >>> 11) <<< 128 < 2 ^ 256 := by
  have h11 : htIdx >>> 11 ≤ 2047 := by
    have := shr11_lt htIdx hhtLt
    rw [show (2 : Nat) ^ 11 = 2048 from by norm_num] at this
    omega
  rw [Nat.shiftLeft_eq]
  calc
    (htIdx >>> 11) * 2 ^ 128 ≤ 2047 * 2 ^ 128 := Nat.mul_le_mul_right _ h11
    _ < 2 ^ 256 := by norm_num

private theorem and7FF_lt (htIdx : Nat) : htIdx &&& 0x7FF < 2 ^ 11 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem and7FF_shl64_lt (htIdx : Nat) :
    (htIdx &&& 0x7FF) <<< 64 < 2 ^ 256 := by
  have h11 : htIdx &&& 0x7FF ≤ 2047 := Nat.and_le_right
  rw [Nat.shiftLeft_eq]
  calc
    (htIdx &&& 0x7FF) * 2 ^ 64 ≤ 2047 * 2 ^ 64 := Nat.mul_le_mul_right _ h11
    _ < 2 ^ 256 := by norm_num

/-! ## 4. Accessor corollaries — the loop-invariant ADRS base for the FORS
outer loop.  Each unwinds the three `letVar`s with explicit eval witnesses
(the `forsLeafSetupStep_pathIdx_eq_of_eval` style from `SegmentS4Fors`). -/

section Accessors

variable (st : RuntimeState) (htIdx : Nat)

private theorem htIdx_lt256 (hhtLt : htIdx < 2 ^ 22) : htIdx < 2 ^ 256 :=
  lt_trans hhtLt (by norm_num)

/-- The post-setup bindings as an explicit three-deep `bindValue` chain with
spec-form digit values.  The single unwinding all three accessors read off. -/
private theorem stepForsSetup_bindings_eq
    (hht : lookupValue st.bindings "htIdx" = htIdx) (hhtLt : htIdx < 2 ^ 22) :
    (stepForsSetup st).bindings =
      bindValue
        (bindValue
          (bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF))
          "idxTree0" (htIdx >>> 11))
        "forsBase"
        (((htIdx >>> 11) <<< 128)
          ||| ((3 <<< 96) ||| ((htIdx &&& 0x7FF) <<< 64))) := by
  -- Eval witness for statement 13: `and(htIdx, 0x7FF) ↦ htIdx &&& 0x7FF`.
  have h1 : evalExpr [] st (andE (v "htIdx") (u 0x7FF)) = some (htIdx &&& 0x7FF) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      st (v "htIdx") htIdx 0x7FF
      (by show some (lookupValue st.bindings "htIdx") = some htIdx; rw [hht])
      (htIdx_lt256 htIdx hhtLt) (by norm_num)
  -- Eval witness for statement 14 over the post-13 state.
  have h2 : evalExpr []
      ({ st with bindings := bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF) })
      (shrE (u 11) (v "htIdx")) = some (htIdx >>> 11) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      _ (u 11) (v "htIdx") 11 htIdx rfl
      (by
        show some (lookupValue
            (bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF)) "htIdx") = some htIdx
        rw [lookupValue_bindValue_ne _ "idxLeaf0" "htIdx" _ (by decide), hht])
      (by norm_num) (htIdx_lt256 htIdx hhtLt)
  -- Eval witness for statement 15 over the post-14 state.
  have h3 : evalExpr []
      ({ st with bindings := (bindValue
            (bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF))
            "idxTree0" (htIdx >>> 11)) })
      (orE (shlE (u 128) (v "idxTree0"))
        (orE (shlE (u 96) (u 3)) (shlE (u 64) (v "idxLeaf0"))))
      = some (((htIdx >>> 11) <<< 128)
          ||| ((3 <<< 96) ||| ((htIdx &&& 0x7FF) <<< 64))) := by
    set s : RuntimeState :=
      { st with bindings := (bindValue
            (bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF))
            "idxTree0" (htIdx >>> 11)) } with hs
    have hT0 : evalExpr [] s (v "idxTree0") = some (htIdx >>> 11) := by
      show some (lookupValue
          (bindValue (bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF))
            "idxTree0" (htIdx >>> 11)) "idxTree0") = _
      rw [lookupValue_bindValue_self]
    have hL0 : evalExpr [] s (v "idxLeaf0") = some (htIdx &&& 0x7FF) := by
      show some (lookupValue
          (bindValue (bindValue st.bindings "idxLeaf0" (htIdx &&& 0x7FF))
            "idxTree0" (htIdx >>> 11)) "idxLeaf0") = _
      rw [lookupValue_bindValue_ne _ "idxTree0" "idxLeaf0" _ (by decide),
          lookupValue_bindValue_self]
    have hShlT : evalExpr [] s (shlE (u 128) (v "idxTree0"))
        = some ((htIdx >>> 11) <<< 128) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
        s (u 128) (v "idxTree0") 128 (htIdx >>> 11) rfl hT0 (by norm_num)
        (lt_trans (shr11_lt htIdx hhtLt) (by norm_num))
        (shr11_shl128_lt htIdx hhtLt)
    have hShlM : evalExpr [] s (shlE (u 96) (u 3)) = some ((3 : Nat) <<< 96) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
        s (u 96) (u 3) 96 3 rfl rfl (by norm_num) (by norm_num) (by decide)
    have hShlL : evalExpr [] s (shlE (u 64) (v "idxLeaf0"))
        = some ((htIdx &&& 0x7FF) <<< 64) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
        s (u 64) (v "idxLeaf0") 64 (htIdx &&& 0x7FF) rfl hL0 (by norm_num)
        (lt_trans (and7FF_lt htIdx) (by norm_num))
        (and7FF_shl64_lt htIdx)
    have hInner : evalExpr [] s (orE (shlE (u 96) (u 3)) (shlE (u 64) (v "idxLeaf0")))
        = some ((3 <<< 96) ||| ((htIdx &&& 0x7FF) <<< 64)) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
        s _ _ _ _ hShlM hShlL (by decide) (and7FF_shl64_lt htIdx)
    have hInnerLt : (3 <<< 96) ||| ((htIdx &&& 0x7FF) <<< 64) < 2 ^ 256 :=
      Nat.bitwise_lt_two_pow (by decide) (and7FF_shl64_lt htIdx)
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      s _ _ _ _ hShlT hInner (shr11_shl128_lt htIdx hhtLt) hInnerLt
  unfold stepForsSetup forsSetupBody
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "idxLeaf0" _ _ h1)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "idxTree0" _ _ h2)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "forsBase" _ _ h3)]
  rfl

/-- After the FORS pre-loop setup the `"idxLeaf0"` binding is the low 11 bits
of `htIdx`. -/
theorem stepForsSetup_idxLeaf0
    (hht : lookupValue st.bindings "htIdx" = htIdx) (hhtLt : htIdx < 2 ^ 22) :
    lookupValue (stepForsSetup st).bindings "idxLeaf0" = htIdx &&& 0x7FF := by
  rw [stepForsSetup_bindings_eq st htIdx hht hhtLt,
      lookupValue_bindValue_ne _ "forsBase" "idxLeaf0" _ (by decide),
      lookupValue_bindValue_ne _ "idxTree0" "idxLeaf0" _ (by decide),
      lookupValue_bindValue_self]

/-- After the FORS pre-loop setup the `"idxTree0"` binding is the high 11 bits
of `htIdx`. -/
theorem stepForsSetup_idxTree0
    (hht : lookupValue st.bindings "htIdx" = htIdx) (hhtLt : htIdx < 2 ^ 22) :
    lookupValue (stepForsSetup st).bindings "idxTree0" = htIdx >>> 11 := by
  rw [stepForsSetup_bindings_eq st htIdx hht hhtLt,
      lookupValue_bindValue_ne _ "forsBase" "idxTree0" _ (by decide),
      lookupValue_bindValue_self]

/-- The keystone corollary.  After the FORS pre-loop setup the `"forsBase"`
binding is exactly `C13Concrete.adrsForsBase (htIdx >>> 11) (htIdx &&& 0x7FF)`.
The `htIdx < 2^22` bound is discharged at the call site from the S3-segment
hypertree-index bound (C13: `htIdx = and(…, 0x3FFFFF)` is 22-bit masked). -/
theorem stepForsSetup_forsBase_eq
    (hht : lookupValue st.bindings "htIdx" = htIdx) (hhtLt : htIdx < 2 ^ 22) :
    lookupValue (stepForsSetup st).bindings "forsBase"
      = SphincsMinusVerifierSpec.C13Concrete.adrsForsBase
          (htIdx >>> 11) (htIdx &&& 0x7FF) := by
  rw [stepForsSetup_bindings_eq st htIdx hht hhtLt, lookupValue_bindValue_self]
  simp [SphincsMinusVerifierSpec.C13Concrete.adrsForsBase, Nat.lor_assoc]

end Accessors

/-! ## 5. Binding/memory/state-frame preservation.

The pre-loop setup binds three fresh keys (`"idxLeaf0"`, `"idxTree0"`,
`"forsBase"`) and touches nothing else: no memory writes, no rebinding of
earlier accept-path keys (`"sigBase"`, `"dVal"`, `"htIdx"`), no
selector/calldata mutation. -/

private theorem forsSetup_preserves_key
    (key : String)
    (h1 : "idxLeaf0" ≠ key) (h2 : "idxTree0" ≠ key) (h3 : "forsBase" ≠ key)
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings key = lookupValue st.bindings key := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key forsSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsSetupBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "idxLeaf0" key _ h1 hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "idxTree0" key _ h2 hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "forsBase" key _ h3 hexec

/-- Generic public step-form binding frame for the FORS pre-loop setup: any
key other than the three fresh binders is preserved. -/
theorem stepForsSetup_preserves_key
    (key : String)
    (h1 : "idxLeaf0" ≠ key) (h2 : "idxTree0" ≠ key) (h3 : "forsBase" ≠ key)
    (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings key = lookupValue st.bindings key :=
  forsSetup_preserves_key key h1 h2 h3 st (stepForsSetup st) (execForsSetup st)

theorem forsSetup_preserves_sigBase
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings "sigBase" = lookupValue st.bindings "sigBase" :=
  forsSetup_preserves_key "sigBase" (by decide) (by decide) (by decide) st s' h

theorem forsSetup_preserves_dVal
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings "dVal" = lookupValue st.bindings "dVal" :=
  forsSetup_preserves_key "dVal" (by decide) (by decide) (by decide) st s' h

theorem forsSetup_preserves_htIdx
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings "htIdx" = lookupValue st.bindings "htIdx" :=
  forsSetup_preserves_key "htIdx" (by decide) (by decide) (by decide) st s' h

/-- The setup is all `letVar`s, so every memory cell is preserved. -/
theorem forsSetup_preserves_memory
    (st s' : RuntimeState) (addr : Nat)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    addr forsSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsSetupBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' addr "idxLeaf0" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' addr "idxTree0" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' addr "forsBase" _ hexec

/-- The setup never touches the dispatch selector or the calldata. -/
theorem forsSetup_preserves_selector_calldata
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    s'.selector = st.selector ∧ s'.world.calldata = st.world.calldata := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    forsSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsSetupBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "idxLeaf0" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "idxTree0" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "forsBase" _ hexec

/-! Step-forms: combine the transformer `stepForsSetup` with the preservation
facts into single, easy-to-chain statements.  No bounds needed — the headline
`execForsSetup` has none. -/

theorem stepForsSetup_preserves_sigBase_step (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "sigBase"
      = lookupValue st.bindings "sigBase" :=
  forsSetup_preserves_sigBase st (stepForsSetup st) (execForsSetup st)

theorem stepForsSetup_preserves_dVal_step (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "dVal"
      = lookupValue st.bindings "dVal" :=
  forsSetup_preserves_dVal st (stepForsSetup st) (execForsSetup st)

theorem stepForsSetup_preserves_htIdx_step (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "htIdx"
      = lookupValue st.bindings "htIdx" :=
  forsSetup_preserves_htIdx st (stepForsSetup st) (execForsSetup st)

theorem stepForsSetup_preserves_memory_step (st : RuntimeState) (addr : Nat) :
    ((stepForsSetup st).world.memory addr).val = (st.world.memory addr).val :=
  forsSetup_preserves_memory st (stepForsSetup st) addr (execForsSetup st)

theorem stepForsSetup_preserves_selector_calldata_step (st : RuntimeState) :
    (stepForsSetup st).selector = st.selector ∧
      (stepForsSetup st).world.calldata = st.world.calldata :=
  forsSetup_preserves_selector_calldata st (stepForsSetup st) (execForsSetup st)

/-! ## 6. Axiom audit. -/

#print axioms execForsSetup
#print axioms forsSetup_eq_slice
#print axioms stepForsSetup_idxLeaf0
#print axioms stepForsSetup_idxTree0
#print axioms stepForsSetup_forsBase_eq
#print axioms stepForsSetup_preserves_key
#print axioms forsSetup_preserves_sigBase
#print axioms forsSetup_preserves_dVal
#print axioms forsSetup_preserves_htIdx
#print axioms forsSetup_preserves_memory
#print axioms forsSetup_preserves_selector_calldata

end SphincsMinusVerifiers.SegmentForsSetup
