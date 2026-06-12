/-
  SegmentLayer3 — the Layer-3 hypertree-climb loop body (statement 25 of
  `c13VerifyBody`, the `forEach "layer" (u 2)` outer climb).

  The layer body is *guarded*: after accumulating the WOTS checksum `digitSum`
  it reverts unless `digitSum = 208` (Model.lean:167).  So unlike the totally
  continuing FORS/Merkle loops, this body has the shape

  ```
  execStmtList [] ls layerBody = if layerGuard ls then .continue (stepLayer ls) else .revert
  ```

  proved here as `execLayerBody`.  This is exactly the `hstep` hypothesis of the
  guarded loop-threading engine `ClimbLoopGuarded.execForEachLoop_of_guarded_step`,
  so once the per-iteration guards are discharged the whole `forEach "layer"`
  folds to a pure `foldLoop` over `stepLayer` (`execLayerLoop`).

  Faithfulness is machine-checked: `layerStmt_eq_slice` (`rfl`) shows the
  reconstructed statement — loop header and full body, every inner `forEach` and
  the checksum-guard `ite` included — is exactly statement 25 of `c13VerifyBody`.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbLoopGuarded
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.ClimbMemFrame
import SphincsMinusVerifiers.InitialNodeKeccak
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.Model
import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentLayer3

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK merkleClimbBody wotsChainBody stepMerkle stepWots
  wotsChainStep execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmt_letVar_continue)
open SphincsMinusVerifiers.ClimbLoop (foldLoop execStmt_forEach_of_step execStmt_forEach_merkleClimb)
open SphincsMinusVerifierSpec.C13Concrete (wotsDigitSum)
open SphincsMinusVerifiers.BindingFrame

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def notE (x : Expr) : Expr := .logicalNot x
private def eqE (a b : Expr) : Expr := .eq a b
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def xorE (a b : Expr) : Expr := .bitXor a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

private def revert0 : List Stmt :=
  [ .unsafeYul <|
      UnsafeYulFragment.rawRevert (.lit 0) (.lit 0)
        { name := "raw_yul_revert_0_0_refines_solidity_assembly"
          obligation := "The handwritten Yul revert(0, 0) must match the Solidity assembly observable revert behavior."
          proofStatus := .assumed }
        "raw_yul_revert_0_0" ]

/-- The checksum-guard condition: `digitSum ≠ 208`. -/
private def condE : Expr := notE (eqE (v "digitSum") (u 208))

/-! ## 1. Per-statement `.continue` combinator for `assignVar`. -/

/-- `assignVar` shares the interpreter's `letVar` step semantics. -/
private theorem assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-! ## 2. Inner-loop body step lemmas. -/

/-- The digit-sum accumulation loop body (`forEach "ii" (u 43)`). -/
def digitSumBody : List Stmt :=
  [ .assignVar "digitSum" (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7))) ]

def digitSumStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st digitSumBody with | .continue s' => s' | _ => st

theorem digitSumStepLemma (st : RuntimeState) :
    execStmtList [] st digitSumBody = .continue (digitSumStep st) := by
  unfold digitSumStep digitSumBody
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  rfl

/-- One executable digit-sum iteration stores the value of the checksum update
expression.  This is the per-step data fact needed before reducing the
`forEach "ii" 43` checksum loop to `C13Concrete.wotsDigitSum`. -/
theorem digitSumStep_digitSum_expr (st : RuntimeState) :
    lookupValue (digitSumStep st).bindings "digitSum" =
      (evalExpr [] st
        (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7)))).getD 0 := by
  unfold digitSumStep digitSumBody addE andE shrE mulE v u
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  rfl

/-- One checksum-loop step only writes `"digitSum"`. -/
theorem digitSumStep_preserves_lookup_of_ne
    (st : RuntimeState) (key : String) (hne : key ≠ "digitSum") :
    lookupValue (digitSumStep st).bindings key = lookupValue st.bindings key := by
  unfold digitSumStep digitSumBody addE andE shrE mulE v u
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  simp only [execStmtList]
  exact MemoryKit.lookupValue_bindValue_ne _ "digitSum" key _
    (fun h => hne h.symm)

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

/-- One checksum-loop iteration adds the low 3-bit digit selected by `"ii"`.
The bound hypotheses are exactly the C13 checksum range (`43 * 7 < 2^256`) and
the EVM word bound for `"d"`. -/
theorem digitSumStep_digitSum_eq_add_digit
    (st : RuntimeState) (i acc d : Nat)
    (hii : lookupValue st.bindings "ii" = i)
    (hacc : lookupValue st.bindings "digitSum" = acc)
    (hd : lookupValue st.bindings "d" = d)
    (hi : i < 43)
    (haccBound : acc ≤ 7 * i)
    (hdBound : d < 2 ^ 256) :
    lookupValue (digitSumStep st).bindings "digitSum" =
      acc + ((d >>> (3 * i)) % 8) := by
  rw [digitSumStep_digitSum_expr]
  unfold addE andE shrE mulE v u
  have hmul : evalExpr [] st (.mul (.localVar "ii") (.literal 3)) = some (i * 3) := by
    have hiWord : i < 2 ^ 256 := lt_trans hi (by decide : 43 < 2 ^ 256)
    have h3 : wordNormalize 3 = 3 := by
      rw [wordNormalize_eq_mod]
      exact Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 256)
    change (do
      let lhs : Verity.Core.Uint256 := ← some (lookupValue st.bindings "ii")
      let rhs : Verity.Core.Uint256 := ← some (wordNormalize 3)
      pure (lhs * rhs).val) = some (i * 3)
    rw [hii, h3]
    show some ((Verity.Core.Uint256.ofNat i * Verity.Core.Uint256.ofNat 3).val)
      = some (i * 3)
    show some (((Verity.Core.Uint256.ofNat i).val * (Verity.Core.Uint256.ofNat 3).val)
        % Verity.Core.Uint256.modulus) = some (i * 3)
    have hiv : (Verity.Core.Uint256.ofNat i).val = i := Nat.mod_eq_of_lt hiWord
    have h3v : (Verity.Core.Uint256.ofNat 3).val = 3 := Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 256)
    have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
    rw [hiv, h3v, hmod, Nat.mod_eq_of_lt]
    exact lt_trans (Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 3))
      (by decide : 43 * 3 < 2 ^ 256)
  have hshr : evalExpr [] st (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d"))
      = some (d >>> (i * 3)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (.mul (.localVar "ii") (.literal 3)) (.localVar "d")
      (i * 3) d hmul (by
        change some (lookupValue st.bindings "d") = some d
        rw [hd])
      (lt_trans (Nat.mul_lt_mul_of_pos_right hi (by decide : 0 < 3))
        (by decide : 43 * 3 < 2 ^ 256))
      hdBound
  have hland : evalExpr [] st
      (.bitAnd (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d")) (.literal 7))
        = some ((d >>> (i * 3)) % 8) := by
    have hraw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        st (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d"))
        (d >>> (i * 3)) 7 hshr
        (by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self d (2 ^ (i * 3))) hdBound)
        (by decide : 7 < 2 ^ 256)
    rw [hraw, nat_land_low3]
  have hadd : evalExpr [] st
      (.add (.localVar "digitSum")
        (.bitAnd (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d")) (.literal 7)))
      = some (acc + ((d >>> (i * 3)) % 8) ) := by
    refine SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (.localVar "digitSum")
      (.bitAnd (.shr (.mul (.localVar "ii") (.literal 3)) (.localVar "d")) (.literal 7))
      acc ((d >>> (i * 3)) % 8) (by
        change some (lookupValue st.bindings "digitSum") = some acc
        rw [hacc]) hland ?_ ?_ ?_
    · exact lt_of_le_of_lt haccBound
        (by
          have : 7 * i < 7 * 43 := by omega
          exact lt_trans this (by decide : 7 * 43 < 2 ^ 256))
    · exact lt_trans (Nat.mod_lt _ (by decide : 0 < 8)) (by decide : 8 < 2 ^ 256)
    · have hdigit : (d >>> (i * 3)) % 8 < 8 := Nat.mod_lt _ (by decide : 0 < 8)
      exact lt_of_le_of_lt (Nat.add_le_add haccBound (Nat.le_of_lt_succ hdigit))
        (by
          have : 7 * i + 7 ≤ 7 * 43 := by omega
          exact lt_of_le_of_lt this (by decide : 7 * 43 < 2 ^ 256))
  rw [hadd]
  simp only [Option.getD_some]
  rw [Nat.mul_comm i 3]

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

/-! ## 3. The Layer-3 body reconstruction (Model.lean:154-203), split around the
checksum-guard `ite` as `prefix11 ++ (ite :: suffix14)`. -/

/-- Statements 154-163 + the digit-sum loop (everything before the guard). -/
def prefix11 : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  , .letVar "d" (keccak 0x00 0x80)
  , .letVar "digitSum" (u 0)
  , .forEach "ii" (u 43) digitSumBody ]

/-- The straight-line part of `prefix11` before the checksum accumulation loop. -/
def prefixBeforeDigitLoop : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  , .letVar "d" (keccak 0x00 0x80)
  , .letVar "digitSum" (u 0) ]

def beforeDigitLoop (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeDigitLoop with | .continue s' => s' | _ => ls

def prefixBeforeDigest : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count") ]

def beforeDigest (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeDigest with | .continue s' => s' | _ => ls

def afterDigitFold (ls : RuntimeState) : RuntimeState :=
  foldLoop "ii" digitSumStep
    { beforeDigitLoop ls with
      bindings := bindValue (beforeDigitLoop ls).bindings "ii" (wordNormalize 0) }
    0 (wordNormalize 43)

/-- The executable checksum fold preserves every binding except the accumulator. -/
theorem afterDigitFold_preserves_lookup_of_ne
    (ls : RuntimeState) (key : String) (hne : "ii" ≠ key) (hneDigit : key ≠ "digitSum") :
    lookupValue (afterDigitFold ls).bindings key =
      lookupValue (beforeDigitLoop ls).bindings key := by
  unfold afterDigitFold
  rw [ClimbLoop.foldLoop_preserves_lookup "ii" key digitSumStep hne
    (fun s => digitSumStep_preserves_lookup_of_ne s key hneDigit)]
  exact MemoryKit.lookupValue_bindValue_ne _ "ii" key _ hne

/-- The executable checksum fold only changes bindings, so it preserves scratch
cell `0x00` from the state before the fold. -/
theorem afterDigitFold_preserves_memory_zero (ls : RuntimeState) :
    ((afterDigitFold ls).world.memory 0x00).val =
      ((beforeDigitLoop ls).world.memory 0x00).val := by
  unfold afterDigitFold
  rw [ClimbLoop.foldLoop_preserves_memory_val "ii" digitSumStep 0 (by
    intro s
    unfold digitSumStep digitSumBody addE andE shrE mulE v u
    rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue s "digitSum" _ _ rfl)]
    rfl)]

/-- Statements 168-203 (everything after the guard). -/
def suffix14 : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK))
  , .letVar "authOff" (addE (v "countOff") (u 4))
  , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
  , .letVar "merkleNode" (v "wotsPk")
  , .letVar "mIdx" (v "idxLeaf")
  , .letVar "merklePtr" (addE (v "sigBase") (v "authOff"))
  , .forEach "h" (u 11) (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
  , .assignVar "currentNode" (v "merkleNode")
  , .assignVar "sigOff" (addE (v "authOff") (u 176)) ]

/-- The straight-line suffix prefix before `authOff := countOff + 4`. -/
def suffixBeforeAuthOff : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK)) ]

/-- The straight-line part of `suffix14` before the XMSS Merkle-climb loop.
This state carries the concrete WOTS public-key word and the initialized
`merkleNode`/`mIdx`/`treeAdrs`/`merklePtr` cells consumed by the generic
Merkle-climb frame lemmas. -/
def suffixBeforeMerkle : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK))
  , .letVar "authOff" (addE (v "countOff") (u 4))
  , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
  , .letVar "merkleNode" (v "wotsPk")
  , .letVar "mIdx" (v "idxLeaf")
  , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ]

/-- The accepting suffix up to, but not including, the `"mIdx"` binding. -/
def suffixBeforeMIdx : List Stmt :=
  suffixBeforeAuthOff ++
    [ .letVar "authOff" (addE (v "countOff") (u 4))
    , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
    , .letVar "merkleNode" (v "wotsPk") ]

def layerBody : List Stmt := prefix11 ++ (.ite condE revert0 [] :: suffix14)

def layerStmt : Stmt := .forEach "layer" (u 2) layerBody

set_option maxHeartbeats 8000000 in
/-- Faithfulness: `layerStmt` is *exactly* statement 25 of `c13VerifyBody`
(loop header, full body, every inner `forEach` and the checksum-guard `ite`). -/
theorem layerStmt_eq_slice :
    [layerStmt] = (c13VerifyBodyTail.drop 27).take 1 := rfl

/-- One-step unfold of `execStmtList` on a cons, kept generic so the head
`execStmt` stays symbolic (no reduction of concrete loop-states). -/
private theorem execStmtList_cons_eq (st : RuntimeState) (s : Stmt) (rest : List Stmt) :
    execStmtList [] st (s :: rest) =
      (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = _
  rfl

/-! ## 4. Threading the guard-free prefix and suffix. -/

/-- The state after running `prefix11` (always continues). -/
def afterDigit (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefix11 with | .continue s' => s' | _ => ls

/-- The named pre-checksum prefix always continues to `beforeDigitLoop`. -/
theorem beforeDigitLoop_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeDigitLoop = .continue (beforeDigitLoop ls) := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  rfl

/-- The pre-checksum prefix does not rebind `"sigBase"`. -/
theorem beforeDigitLoop_preserves_sigBase (ls : RuntimeState) :
    lookupValue (beforeDigitLoop ls).bindings "sigBase" =
      lookupValue ls.bindings "sigBase" := by
  refine execStmtList_preserves_lookup "sigBase" prefixBeforeDigitLoop
    ls (beforeDigitLoop ls) ?_ (beforeDigitLoop_eq ls)
  intro s s'' stmt hmem hexec
  simp [prefixBeforeDigitLoop, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "idxLeaf" "sigBase" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "idxTree" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "countOff" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "count" "sigBase" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "d" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "digitSum" "sigBase" _ (by decide) hexec

/-- The pre-checksum prefix does not rebind `"layer"`. -/
theorem beforeDigitLoop_preserves_layer (ls : RuntimeState) :
    lookupValue (beforeDigitLoop ls).bindings "layer" =
      lookupValue ls.bindings "layer" := by
  refine execStmtList_preserves_lookup "layer" prefixBeforeDigitLoop
    ls (beforeDigitLoop ls) ?_ (beforeDigitLoop_eq ls)
  intro s s'' stmt hmem hexec
  simp [prefixBeforeDigitLoop, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "idxLeaf" "layer" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "idxTree" "layer" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "layer" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "countOff" "layer" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "count" "layer" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "d" "layer" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "digitSum" "layer" _ (by decide) hexec

/-- The pre-checksum prefix binds `"countOff"` to the incoming `"sigOff" + 688`. -/
theorem beforeDigitLoop_countOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256) :
    lookupValue (beforeDigitLoop ls).bindings "countOff" = sigOff + 688 := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u addE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ (by
    refine SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      _ (v "sigOff") (u 688) sigOff 688 ?_ rfl
      hSigOffLt (by decide : 688 < 2 ^ 256) hCountOffLt
    change some (lookupValue _ "sigOff") = some sigOff
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "sigOff" _ (by decide)]
    rw [hSigOff]))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "countOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" "countOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "countOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- The straight-line WOTS digest setup always continues to `beforeDigest`. -/
theorem beforeDigest_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeDigest = .continue (beforeDigest ls) := by
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- The pre-digest WOTS prefix never writes scratch cell `0x00`; it only writes
`0x20`, `0x40`, and `0x60`. -/
theorem beforeDigest_preserves_memory_zero (ls : RuntimeState) :
    ((beforeDigest ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide)]

/-- The straight-line WOTS prefix before the checksum loop preserves scratch
cell `0x00`; it only writes `0x20`, `0x40`, and `0x60`. -/
theorem beforeDigitLoop_preserves_memory_zero (ls : RuntimeState) :
    ((beforeDigitLoop ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide),
      MemoryKit.memUpdate_diff _ _ _ _ (by decide)]

/-- The pre-digest WOTS prefix splits the low 11 bits of the incoming
`"idxTree"` binding into `"idxLeaf"`. -/
theorem beforeDigest_idxLeaf_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigest ls).bindings "idxLeaf" = idxTree % 2048 := by
  unfold beforeDigest prefixBeforeDigest mstore u andE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr [] ls (andE (v "idxTree") (u 0x7FF))).getD 0 = idxTree % 2048
  have hAnd :
      evalExpr [] ls (andE (v "idxTree") (u 0x7FF)) =
        some (idxTree % 2048) := by
    have hLocal : evalExpr [] ls (v "idxTree") = some idxTree := by
      change some (lookupValue ls.bindings "idxTree") = some idxTree
      rw [hIdxTree]
    have hRaw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        ls (v "idxTree") idxTree 0x7FF hLocal hIdxTreeLt
        (by decide : 0x7FF < 2 ^ 256)
    simpa [andE, u, nat_land_low11] using hRaw
  rw [hAnd]
  rfl

/-- The pre-digest WOTS prefix shifts the incoming `"idxTree"` binding by the
C13 subtree height for the layer address. -/
theorem beforeDigest_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigest ls).bindings "idxTree" = idxTree / 2048 := by
  unfold beforeDigest prefixBeforeDigest mstore u shrE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (shrE (u 11) (v "idxTree"))).getD 0 = idxTree / 2048
  have hLit : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (u 11) = some 11 := by
    rfl
  have hLocal : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (v "idxTree") = some idxTree := by
    change some (lookupValue
        (bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0))
        "idxTree") = some idxTree
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "idxTree" _ (by decide)]
    rw [hIdxTree]
  have hShr :
      evalExpr []
        { ls with
          bindings := bindValue ls.bindings "idxLeaf"
            ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
        (shrE (u 11) (v "idxTree")) = some (idxTree >>> 11) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      _ (u 11) (v "idxTree") 11 idxTree hLit hLocal
      (by decide : 11 < 2 ^ 256) hIdxTreeLt
  rw [hShr]
  rw [Nat.shiftRight_eq_div_pow]
  rfl

/-- The longer pre-checksum prefix has the same shifted `"idxTree"` binding as
the pre-digest prefix; the extra statements only bind `"d"` and `"digitSum"`. -/
theorem beforeDigitLoop_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigitLoop ls).bindings "idxTree" = idxTree / 2048 := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u shrE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (shrE (u 11) (v "idxTree"))).getD 0 = idxTree / 2048
  have hLit : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (u 11) = some 11 := by
    rfl
  have hLocal : evalExpr []
      { ls with
        bindings := bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
      (v "idxTree") = some idxTree := by
    change some (lookupValue
        (bindValue ls.bindings "idxLeaf"
          ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0))
        "idxTree") = some idxTree
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "idxTree" _ (by decide)]
    rw [hIdxTree]
  have hShr :
      evalExpr []
        { ls with
          bindings := bindValue ls.bindings "idxLeaf"
            ((evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0) }
        (shrE (u 11) (v "idxTree")) = some (idxTree >>> 11) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      _ (u 11) (v "idxTree") 11 idxTree hLit hLocal
      (by decide : 11 < 2 ^ 256) hIdxTreeLt
  rw [hShr]
  rw [Nat.shiftRight_eq_div_pow]
  rfl

/-- The longer pre-checksum prefix has the same low-11-bit `"idxLeaf"` binding
as the pre-digest prefix; the extra statements only bind `"d"` and `"digitSum"`. -/
theorem beforeDigitLoop_idxLeaf_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeDigitLoop ls).bindings "idxLeaf" = idxTree % 2048 := by
  unfold beforeDigitLoop prefixBeforeDigitLoop mstore u andE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  change (evalExpr [] ls (andE (v "idxTree") (u 0x7FF))).getD 0 = idxTree % 2048
  have hAnd :
      evalExpr [] ls (andE (v "idxTree") (u 0x7FF)) =
        some (idxTree % 2048) := by
    have hLocal : evalExpr [] ls (v "idxTree") = some idxTree := by
      change some (lookupValue ls.bindings "idxTree") = some idxTree
      rw [hIdxTree]
    have hRaw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        ls (v "idxTree") idxTree 0x7FF hLocal hIdxTreeLt
        (by decide : 0x7FF < 2 ^ 256)
    simpa [andE, u, nat_land_low11] using hRaw
  rw [hAnd]
  rfl

/-- The pre-digest WOTS prefix assembles the WOTS hash-base address from the
layer and the split C13 hypertree index. -/
theorem beforeDigest_wotsAdrs_eq_of_layer_idxTree
    (ls : RuntimeState) (layer idxTree : Nat)
    (hLayer : lookupValue ls.bindings "layer" = layer)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 22) :
    lookupValue (beforeDigest ls).bindings "wotsAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer (idxTree / 2048) (idxTree % 2048) := by
  unfold beforeDigest prefixBeforeDigest mstore u andE shrE shlE orE v
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  let idxLeafVal :=
    (evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0
  let st1 : RuntimeState := { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
  let idxTreeVal := (evalExpr [] st1 (.shr (.literal 11) (.localVar "idxTree"))).getD 0
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "idxTree" idxTreeVal }
  change (evalExpr [] st2
      (.bitOr (.shl (.literal 224) (.localVar "layer"))
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 64) (.localVar "idxLeaf"))))).getD 0 =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase
        layer (idxTree / 2048) (idxTree % 2048)
  have hIdxLeafVal : idxLeafVal = idxTree % 2048 := by
    unfold idxLeafVal
    have hLocal : evalExpr [] ls (.localVar "idxTree") = some idxTree := by
      change some (lookupValue ls.bindings "idxTree") = some idxTree
      rw [hIdxTree]
    have hRaw :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
        ls (.localVar "idxTree") idxTree 0x7FF hLocal
        (lt_trans hIdxTreeLt (by decide : 2 ^ 22 < 2 ^ 256))
        (by decide : 0x7FF < 2 ^ 256)
    rw [hRaw]
    simp [nat_land_low11]
  have hIdxTreeVal : idxTreeVal = idxTree / 2048 := by
    unfold idxTreeVal st1
    have hLit : evalExpr []
        { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
        (.literal 11) = some 11 := by
      rfl
    have hLocal : evalExpr []
        { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
        (.localVar "idxTree") = some idxTree := by
      change some (lookupValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree")
        = some idxTree
      rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "idxTree" _ (by decide)]
      rw [hIdxTree]
    have hShr :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
        { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
        (.literal 11) (.localVar "idxTree") 11 idxTree hLit hLocal
        (by decide : 11 < 2 ^ 256)
        (lt_trans hIdxTreeLt (by decide : 2 ^ 22 < 2 ^ 256))
    rw [hShr, Nat.shiftRight_eq_div_pow]
    norm_num
  have hLayerEval : evalExpr [] st2 (.localVar "layer") = some layer := by
    unfold st2 st1
    change some (lookupValue
        (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
        "layer") = some layer
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "layer" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "layer" _ (by decide)]
    rw [hLayer]
  have hIdxTreeEval : evalExpr [] st2 (.localVar "idxTree") = some (idxTree / 2048) := by
    unfold st2
    change some (lookupValue (bindValue st1.bindings "idxTree" idxTreeVal) "idxTree")
      = some (idxTree / 2048)
    rw [MemoryKit.lookupValue_bindValue_self]
    exact congrArg some hIdxTreeVal
  have hIdxLeafEval : evalExpr [] st2 (.localVar "idxLeaf") = some (idxTree % 2048) := by
    unfold st2 st1
    change some (lookupValue
        (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
        "idxLeaf") = some (idxTree % 2048)
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "idxLeaf" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    exact congrArg some hIdxLeafVal
  have h224 :
      evalExpr [] st2 (.shl (.literal 224) (.localVar "layer")) =
        some (layer <<< 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 224) (.localVar "layer") 224 layer rfl hLayerEval
      (by decide : 224 < 2 ^ 256)
      (lt_trans hLayerLt (by decide : 2 ^ 32 < 2 ^ 256))
      (by
        rw [Nat.shiftLeft_eq]
        calc
          layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
            Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
          _ = 2 ^ 256 := by norm_num [Nat.pow_add])
  have h128 :
      evalExpr [] st2 (.shl (.literal 128) (.localVar "idxTree")) =
        some ((idxTree / 2048) <<< 128) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 128) (.localVar "idxTree") 128 (idxTree / 2048) rfl hIdxTreeEval
      (by decide : 128 < 2 ^ 256)
      (lt_trans (Nat.div_lt_of_lt_mul hIdxTreeLt) (by decide : 2048 < 2 ^ 256))
      (by
        have hnext : idxTree / 2048 < 2 ^ 11 := by
          exact Nat.div_lt_of_lt_mul hIdxTreeLt
        rw [Nat.shiftLeft_eq]
        calc
          (idxTree / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
            Nat.mul_lt_mul_of_pos_right hnext (by decide)
          _ < 2 ^ 256 := by decide)
  have h64 :
      evalExpr [] st2 (.shl (.literal 64) (.localVar "idxLeaf")) =
        some ((idxTree % 2048) <<< 64) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st2 (.literal 64) (.localVar "idxLeaf") 64 (idxTree % 2048) rfl hIdxLeafEval
      (by decide : 64 < 2 ^ 256)
      (lt_trans (Nat.mod_lt _ (by decide : 0 < 2048)) (by decide : 2048 < 2 ^ 256))
      (by
        have hleaf : idxTree % 2048 < 2048 := Nat.mod_lt _ (by decide : 0 < 2048)
        rw [Nat.shiftLeft_eq]
        calc
          (idxTree % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_pos_right hleaf (by decide)
          _ < 2 ^ 256 := by decide)
  have h224lt : layer <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
  have h128lt : (idxTree / 2048) <<< 128 < 2 ^ 256 := by
    have hnext : idxTree / 2048 < 2 ^ 11 := Nat.div_lt_of_lt_mul hIdxTreeLt
    rw [Nat.shiftLeft_eq]
    calc
      (idxTree / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h64lt : (idxTree % 2048) <<< 64 < 2 ^ 256 := by
    have hleaf : idxTree % 2048 < 2048 := Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      (idxTree % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have hinner :
      evalExpr [] st2
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 64) (.localVar "idxLeaf"))) =
        some (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st2 (.shl (.literal 128) (.localVar "idxTree"))
      (.shl (.literal 64) (.localVar "idxLeaf"))
      ((idxTree / 2048) <<< 128) ((idxTree % 2048) <<< 64)
      h128 h64 h128lt h64lt
  have hinnerLt :
      (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128lt h64lt
  have hfull :
      evalExpr [] st2
        (.bitOr (.shl (.literal 224) (.localVar "layer"))
          (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
            (.shl (.literal 64) (.localVar "idxLeaf")))) =
        some ((layer <<< 224) |||
          (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64))) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st2 (.shl (.literal 224) (.localVar "layer"))
      (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
        (.shl (.literal 64) (.localVar "idxLeaf")))
      (layer <<< 224)
      (((idxTree / 2048) <<< 128) ||| ((idxTree % 2048) <<< 64))
      h224 hinner h224lt hinnerLt
  rw [hfull]
  simp [SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase, Nat.lor_assoc]

/-- The pre-digest WOTS prefix binds `"count"` to the high 32 bits of the
signature calldata word at `sigBase + sigOff + 688`. -/
theorem beforeDigest_count_eq_of_sigBase_sigOff_calldata
    (ls : RuntimeState) (sigBase sigOff : Nat) (calldata : List Nat)
    (hSigBase : lookupValue ls.bindings "sigBase" = sigBase)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSelector : ls.selector = 0)
    (hCalldata : ls.world.calldata = calldata)
    (hSigBaseLt : sigBase < 2 ^ 256)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hOffsetLt : sigBase + (sigOff + 688) < 2 ^ 256) :
    lookupValue (beforeDigest ls).bindings "count" =
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688))) >>> 224 := by
  unfold beforeDigest prefixBeforeDigest mstore u andE shrE shlE orE v addE cdload
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  let idxLeafVal :=
    (evalExpr [] ls (.bitAnd (.localVar "idxTree") (.literal 0x7FF))).getD 0
  let st1 : RuntimeState := { ls with bindings := bindValue ls.bindings "idxLeaf" idxLeafVal }
  let idxTreeVal := (evalExpr [] st1 (.shr (.literal 11) (.localVar "idxTree"))).getD 0
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "idxTree" idxTreeVal }
  let wotsAdrsVal :=
    (evalExpr [] st2
      (.bitOr (.shl (.literal 224) (.localVar "layer"))
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 64) (.localVar "idxLeaf"))))).getD 0
  let st3 : RuntimeState := { st2 with bindings := bindValue st2.bindings "wotsAdrs" wotsAdrsVal }
  let countOffVal := (evalExpr [] st3 (.add (.localVar "sigOff") (.literal 688))).getD 0
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "countOff" countOffVal }
  change (evalExpr [] st4
      (.shr (.literal 224)
        (.calldataload (.add (.localVar "sigBase") (.localVar "countOff"))))).getD 0 =
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688))) >>> 224
  have hSigOffEval : evalExpr [] st3 (.localVar "sigOff") = some sigOff := by
    unfold st3 st2 st1
    change some (lookupValue
        (bindValue
          (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
          "wotsAdrs" wotsAdrsVal)
        "sigOff") = some sigOff
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigOff" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "sigOff" _ (by decide)]
    rw [hSigOff]
  have h688 : evalExpr [] st3 (.literal 688) = some 688 := by
    show some (wordNormalize 688) = some 688
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 688 < 2 ^ 256)]
  have hCountOffEval :
      evalExpr [] st3 (.add (.localVar "sigOff") (.literal 688)) =
        some (sigOff + 688) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st3 (.localVar "sigOff") (.literal 688) sigOff 688
      hSigOffEval h688 hSigOffLt (by decide : 688 < 2 ^ 256) hCountOffLt
  have hCountOffVal : countOffVal = sigOff + 688 := by
    unfold countOffVal
    rw [hCountOffEval]
    rfl
  have hSigBaseEval : evalExpr [] st4 (.localVar "sigBase") = some sigBase := by
    unfold st4 st3 st2 st1
    change some (lookupValue
        (bindValue
          (bindValue
            (bindValue (bindValue ls.bindings "idxLeaf" idxLeafVal) "idxTree" idxTreeVal)
            "wotsAdrs" wotsAdrsVal)
          "countOff" countOffVal)
        "sigBase") = some sigBase
    rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "sigBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "sigBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "sigBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "sigBase" _ (by decide)]
    rw [hSigBase]
  have hCountOffEval4 : evalExpr [] st4 (.localVar "countOff") =
      some (sigOff + 688) := by
    unfold st4
    change some (lookupValue (bindValue st3.bindings "countOff" countOffVal) "countOff")
      = some (sigOff + 688)
    rw [MemoryKit.lookupValue_bindValue_self]
    exact congrArg some hCountOffVal
  have hOffset :
      evalExpr [] st4 (.add (.localVar "sigBase") (.localVar "countOff")) =
        some (sigBase + (sigOff + 688)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st4 (.localVar "sigBase") (.localVar "countOff") sigBase (sigOff + 688)
      hSigBaseEval hCountOffEval4 hSigBaseLt hCountOffLt hOffsetLt
  have hLoad :
      evalExpr [] st4 (.calldataload (.add (.localVar "sigBase") (.localVar "countOff"))) =
        some (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
          (sigBase + (sigOff + 688))) := by
    change (do
        let resolvedOffset ←
          evalExpr [] st4 (.add (.localVar "sigBase") (.localVar "countOff"))
        some (Compiler.Proofs.YulGeneration.calldataloadWord st4.selector
          st4.world.calldata resolvedOffset)) =
      some (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688)))
    rw [hOffset]
    unfold st4 st3 st2 st1
    rw [hSelector, hCalldata]
    rfl
  have hLoadLt :
      Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
          (sigBase + (sigOff + 688)) < 2 ^ 256 := by
    by_cases hsmall : sigBase + (sigOff + 688) < 4
    · simp [Compiler.Proofs.YulGeneration.calldataloadWord, hsmall]
    · simp [Compiler.Proofs.YulGeneration.calldataloadWord, hsmall,
        Compiler.Constants.evmModulus]
      split <;> exact Nat.mod_lt _ (by decide : 0 < 2 ^ 256)
  have h224 : evalExpr [] st4 (.literal 224) = some 224 := by
    show some (wordNormalize 224) = some 224
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 224 < 2 ^ 256)]
  have hShr :
      evalExpr [] st4
        (.shr (.literal 224)
          (.calldataload (.add (.localVar "sigBase") (.localVar "countOff")))) =
        some ((Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
          (sigBase + (sigOff + 688))) >>> 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st4 (.literal 224)
      (.calldataload (.add (.localVar "sigBase") (.localVar "countOff")))
      224
      (Compiler.Proofs.YulGeneration.calldataloadWord 0 calldata
        (sigBase + (sigOff + 688)))
      h224 hLoad (by decide : 224 < 2 ^ 256) hLoadLt
  rw [hShr]
  rfl

/-- If the named WOTS address binding has been identified, the pre-digest
scratch cell `0x20` contains that word. -/
theorem beforeDigest_memory_0x20_eq_of_wotsAdrs
    (ls : RuntimeState) (wotsAdrs : Nat)
    (hWotsAdrs : lookupValue (beforeDigest ls).bindings "wotsAdrs" = wotsAdrs) :
    ((beforeDigest ls).world.memory 0x20).val = wordNormalize wotsAdrs := by
  rw [← hWotsAdrs]
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  change (MemoryKit.memUpdate _ (wordNormalize 32) _ (wordNormalize 32)).val =
    wordNormalize (lookupValue _ "wotsAdrs")
  rw [MemoryKit.memUpdate_val_same]

/-- The pre-digest WOTS prefix writes scratch cell `0x40` from the incoming
`"currentNode"` binding. -/
theorem beforeDigest_memory_0x40_eq_currentNode (ls : RuntimeState) :
    ((beforeDigest ls).world.memory 0x40).val =
      wordNormalize (lookupValue ls.bindings "currentNode") := by
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  change (MemoryKit.memUpdate _ (wordNormalize 64) _ (wordNormalize 64)).val =
    wordNormalize (lookupValue ls.bindings "currentNode")
  rw [MemoryKit.memUpdate_val_same]
  rw [MemoryKit.lookupValue_bindValue_ne _ "count" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "countOff" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsAdrs" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxTree" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "idxLeaf" "currentNode" _ (by decide)]

/-- Word-shaped specialization of `beforeDigest_memory_0x40_eq_currentNode`. -/
theorem beforeDigest_memory_0x40_eq_wordOfHash16
    (ls : RuntimeState) (node : ByteArray)
    (hCurrent : lookupValue ls.bindings "currentNode" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node) :
    ((beforeDigest ls).world.memory 0x40).val =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node := by
  rw [beforeDigest_memory_0x40_eq_currentNode, hCurrent]
  exact SegmentS2.wordNormalize_of_lt (SegmentS2.wordOfHash16_lt node)

/-- If the named WOTS count binding has been identified, the pre-digest scratch
cell `0x60` contains that word. -/
theorem beforeDigest_memory_0x60_eq_of_count
    (ls : RuntimeState) (count : Nat)
    (hCount : lookupValue (beforeDigest ls).bindings "count" = count) :
    ((beforeDigest ls).world.memory 0x60).val = wordNormalize count := by
  rw [← hCount]
  unfold beforeDigest prefixBeforeDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  change (MemoryKit.memUpdate _ (wordNormalize 96) _ (wordNormalize 96)).val =
    wordNormalize (lookupValue _ "count")
  rw [MemoryKit.memUpdate_val_same]

/-- The pre-checksum prefix binds `"d"` to the Keccak word over the four C13 WOTS
digest scratch cells.  Cell `0` is prepared by earlier segments; this prefix
writes `0x20`, `0x40`, and `0x60` before hashing `0x00..0x80`. -/
theorem beforeDigitLoop_d_eq_keccakWords (ls : RuntimeState) :
    lookupValue (beforeDigitLoop ls).bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.keccakWords
        [ ((beforeDigest ls).world.memory 0x00).val
        , ((beforeDigest ls).world.memory 0x20).val
        , ((beforeDigest ls).world.memory 0x40).val
        , ((beforeDigest ls).world.memory 0x60).val ] := by
  unfold beforeDigitLoop
  rw [show prefixBeforeDigitLoop = prefixBeforeDigest ++
      [.letVar "d" (keccak 0x00 0x80), .letVar "digitSum" (u 0)] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeDigest_eq ls)]
  unfold beforeDigest
  rw [beforeDigest_eq ls]
  simp only
  unfold keccak u
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "d" _ _
      (SphincsMinusVerifiers.KeccakBridge.evalExpr_keccak256_eq_keccakWords
        _ 0x00 0x80
        [ ((beforeDigest ls).world.memory 0x00).val
        , ((beforeDigest ls).world.memory 0x20).val
        , ((beforeDigest ls).world.memory 0x40).val
        , ((beforeDigest ls).world.memory 0x60).val ]
        rfl rfl (by
          intro i hi
          rcases i with _ | i
          · simp
          rcases i with _ | i
          · simp
          rcases i with _ | i
          · simp
          rcases i with _ | i
          · simp
          · simp at hi
            omega)))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- WOTS-digest specialization of `beforeDigitLoop_d_eq_keccakWords` once the
four scratch cells have been identified. -/
theorem beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (ls : RuntimeState) (seed layer idxTree idxLeaf count node : Nat)
    (hSeed : ((beforeDigest ls).world.memory 0x00).val = seed)
    (hAdrs :
      ((beforeDigest ls).world.memory 0x20).val =
        SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer idxTree idxLeaf)
    (hNode : ((beforeDigest ls).world.memory 0x40).val = node)
    (hCount : ((beforeDigest ls).world.memory 0x60).val = count) :
    lookupValue (beforeDigitLoop ls).bindings "d" =
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest
        seed layer idxTree idxLeaf count node := by
  rw [beforeDigitLoop_d_eq_keccakWords]
  rw [hSeed, hAdrs, hNode, hCount]
  rfl

theorem afterDigit_eq (ls : RuntimeState) :
    execStmtList [] ls prefix11 = .continue (afterDigit ls) := by
  unfold afterDigit prefix11 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
  rfl

/-- The checksum prefix only updates bindings and scratch memory; it preserves
the ABI selector and calldata image. -/
theorem afterDigit_preserves_selector_calldata (ls : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata ls (afterDigit ls) := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    prefix11 ls (afterDigit ls) ?_ (afterDigit_eq ls)
  intro s s'' stmt hmem hexec
  simp [prefix11, mstore] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "idxLeaf" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "idxTree" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsAdrs" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "countOff" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "count" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "d" _ hexec
  · subst h
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "digitSum" _ hexec
  · subst h
    refine SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "ii" (u 43) digitSumBody s s'' ?_ hexec
    intro t t'' stmt' hmem' hexec'
    simp [digitSumBody] at hmem'
    subst hmem'
    exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      t t'' "digitSum" _ hexec'

/-- Frame obligation for statement bodies that preserve selector/calldata. -/
abbrev PreservesSelectorCalldataBody (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata s s''

theorem digitSumBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody digitSumBody := by
  intro s s'' stmt hmem hexec
  simp [digitSumBody] at hmem
  subst hmem
  exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
    s s'' "digitSum" _ hexec

theorem wotsChainBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody wotsChainBody := by
  intro s s'' stmt hmem hexec
  simp [wotsChainBody] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "val" _ hexec

theorem copyBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody copyBody := by
  intro s s'' stmt hmem hexec
  simp [copyBody] at hmem
  subst hmem
  exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
    s s'' _ _ hexec

theorem merkleClimbBody_preserves_selector_calldata
    (nodeVar idxVar adrsBaseVar authPtrVar : String) :
    PreservesSelectorCalldataBody
      (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar) := by
  intro s s'' stmt hmem hexec
  simp [merkleClimbBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "sibling" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "parentIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "s" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' nodeVar _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' idxVar _ hexec

theorem wotsOuterBody_preserves_selector_calldata :
    PreservesSelectorCalldataBody wotsOuterBody := by
  intro s s'' stmt hmem hexec
  simp [wotsOuterBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "digit" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "steps" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "val" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "chainBase" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "step" _ wotsChainBody s s'' wotsChainBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec

/-- The accepting layer suffix preserves selector/calldata. -/
theorem suffix14_preserves_selector_calldata :
    PreservesSelectorCalldataBody suffix14 := by
  intro s s'' stmt hmem hexec
  simp [suffix14, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsPtr" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ wotsOuterBody s s'' wotsOuterBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "pkAdrs" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ copyBody s s'' copyBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsPk" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "authOff" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "treeAdrs" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "merkleNode" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "mIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "merklePtr" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "h" _ (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
      s s'' (merkleClimbBody_preserves_selector_calldata
        "merkleNode" "mIdx" "treeAdrs" "merklePtr") hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "currentNode" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      s s'' "sigOff" _ hexec

/-- The full checksum prefix continues to the named pure fold state. -/
theorem prefix11_eq_afterDigitFold (ls : RuntimeState) :
    execStmtList [] ls prefix11 = .continue (afterDigitFold ls) := by
  rw [show prefix11 = prefixBeforeDigitLoop ++
      [.forEach "ii" (u 43) digitSumBody] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeDigitLoop_eq ls)]
  unfold afterDigitFold
  unfold u
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
  rfl

/-- `afterDigit` is definitionally the pure fold image of the executable checksum
loop once the straight-line prefix has been named. -/
theorem afterDigit_eq_afterDigitFold (ls : RuntimeState) :
    afterDigit ls = afterDigitFold ls := by
  unfold afterDigit
  rw [prefix11_eq_afterDigitFold ls]

/-- The full checksum prefix preserves scratch cell `0x00`. -/
theorem afterDigit_preserves_memory_zero (ls : RuntimeState) :
    ((afterDigit ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  rw [afterDigit_eq_afterDigitFold]
  rw [afterDigitFold_preserves_memory_zero]
  exact beforeDigitLoop_preserves_memory_zero ls

/-- The executable checksum prefix and the named pure fold expose the same
`digitSum` binding. -/
theorem afterDigit_digitSum_eq_afterDigitFold (ls : RuntimeState) :
    lookupValue (afterDigit ls).bindings "digitSum" =
      lookupValue (afterDigitFold ls).bindings "digitSum" := by
  rw [afterDigit_eq_afterDigitFold ls]

/-- The executable checksum prefix preserves every non-loop, non-accumulator
binding from the named state immediately before the checksum fold. -/
theorem afterDigit_preserves_lookup_of_ne
    (ls : RuntimeState) (key : String) (hne : "ii" ≠ key)
    (hneDigit : key ≠ "digitSum") :
    lookupValue (afterDigit ls).bindings key =
      lookupValue (beforeDigitLoop ls).bindings key := by
  rw [afterDigit_eq_afterDigitFold ls]
  exact afterDigitFold_preserves_lookup_of_ne ls key hne hneDigit

/-- The checksum fold preserves the low-11-bit `"idxLeaf"` binding prepared by
the straight-line digest prefix. -/
theorem afterDigit_idxLeaf_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (afterDigit ls).bindings "idxLeaf" = idxTree % 2048 := by
  rw [afterDigit_preserves_lookup_of_ne ls "idxLeaf" (by decide) (by decide)]
  exact beforeDigitLoop_idxLeaf_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

private def digitSumPrefix (d : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + ((d >>> (3 * i)) % 8)) 0

private theorem digitSumPrefix_le (d n : Nat) :
    digitSumPrefix d n ≤ 7 * n := by
  unfold digitSumPrefix
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hdigit : (d >>> (3 * n)) % 8 ≤ 7 := by
        exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 8))
      calc
        (List.range n).foldl (fun acc i => acc + (d >>> (3 * i)) % 8) 0
            + (d >>> (3 * n)) % 8
            ≤ 7 * n + 7 := Nat.add_le_add ih hdigit
        _ = 7 * (n + 1) := by ring

/-- The executable checksum fold computes the same 43-digit WOTS+C checksum as
`C13Concrete.wotsDigitSum`, for any state whose straight-line prefix has already
bound `"d"` and initialized `"digitSum"` to zero. -/
theorem afterDigitFold_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
    (ls : RuntimeState) (d : Nat)
    (hd : lookupValue (beforeDigitLoop ls).bindings "d" = d)
    (hdBound : d < 2 ^ 256) :
    lookupValue (afterDigitFold ls).bindings "digitSum" = wotsDigitSum d := by
  unfold afterDigitFold wotsDigitSum
  have h43 : wordNormalize 43 = 43 :=
    SegmentS2.wordNormalize_of_lt (by decide : 43 < 2 ^ 256)
  rw [h43]
  let init : RuntimeState :=
    { beforeDigitLoop ls with
      bindings := bindValue (beforeDigitLoop ls).bindings "ii" (wordNormalize 0) }
  have hInitAcc : lookupValue init.bindings "digitSum" = 0 := by
    unfold init
    rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "digitSum" _ (by decide)]
    unfold beforeDigitLoop prefixBeforeDigitLoop mstore u
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
    simp only [execStmtList]
    rw [MemoryKit.lookupValue_bindValue_self]
    rfl
  have hInitD : lookupValue init.bindings "d" = d := by
    unfold init
    rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "d" _ (by decide)]
    exact hd
  have h :
      ∀ n, n ≤ 43 →
        lookupValue (foldLoop "ii" digitSumStep init 0 n).bindings "digitSum"
          = digitSumPrefix d n ∧
        lookupValue (foldLoop "ii" digitSumStep init 0 n).bindings "d" = d := by
    intro n hn
    induction n with
    | zero =>
        simp [ClimbLoop.foldLoop_zero, digitSumPrefix, hInitAcc, hInitD]
    | succ n ih =>
        have hn' : n ≤ 43 := by omega
        rcases ih hn' with ⟨hAcc, hD⟩
        rw [show foldLoop "ii" digitSumStep init 0 (n + 1) =
            digitSumStep
              { foldLoop "ii" digitSumStep init 0 n with
                bindings := bindValue (foldLoop "ii" digitSumStep init 0 n).bindings
                  "ii" (wordNormalize n) } by
          rw [ClimbLoop.foldLoop_append "ii" digitSumStep init 0 n 1]
          simp [ClimbLoop.foldLoop_succ, ClimbLoop.foldLoop_zero]]
        have hi : n < 43 := by omega
        have hii :
            lookupValue
              (bindValue (foldLoop "ii" digitSumStep init 0 n).bindings "ii"
                (wordNormalize n)) "ii" = n := by
          rw [MemoryKit.lookupValue_bindValue_self]
          exact SegmentS2.wordNormalize_of_lt (lt_trans hi (by decide : 43 < 2 ^ 256))
        have hacc' :
            lookupValue
              (bindValue (foldLoop "ii" digitSumStep init 0 n).bindings "ii"
                (wordNormalize n)) "digitSum" = digitSumPrefix d n := by
          rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "digitSum" _ (by decide)]
          exact hAcc
        have hd' :
            lookupValue
              (bindValue (foldLoop "ii" digitSumStep init 0 n).bindings "ii"
                (wordNormalize n)) "d" = d := by
          rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "d" _ (by decide)]
          exact hD
        constructor
        · rw [digitSumStep_digitSum_eq_add_digit
            { (foldLoop "ii" digitSumStep init 0 n) with
              bindings := bindValue (foldLoop "ii" digitSumStep init 0 n).bindings
                "ii" (wordNormalize n) }
            n (digitSumPrefix d n) d hii hacc' hd' hi (digitSumPrefix_le d n) hdBound]
          unfold digitSumPrefix
          rw [List.range_succ, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
        · rw [digitSumStep_preserves_lookup_of_ne _ "d" (by decide)]
          exact hd'
  exact (h 43 (by rfl)).1

theorem afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
    (ls : RuntimeState) (d : Nat)
    (hd : lookupValue (beforeDigitLoop ls).bindings "d" = d)
    (hdBound : d < 2 ^ 256) :
    lookupValue (afterDigit ls).bindings "digitSum" = wotsDigitSum d := by
  rw [afterDigit_digitSum_eq_afterDigitFold]
  exact afterDigitFold_digitSum_eq_wotsDigitSum_of_beforeDigitLoop ls d hd hdBound

/-- The pure transformer for one accepting layer iteration: the `.continue`
payload of `suffix14` run from `afterDigit ls`. -/
def stepLayer (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffix14 with | .continue s' => s' | _ => afterDigit ls

/-- The state immediately before the XMSS Merkle-climb loop inside one accepting
layer iteration. -/
def beforeMerkle (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeMerkle with
  | .continue s' => s'
  | _ => afterDigit ls

/-- The state immediately before binding `"mIdx"`. -/
def beforeMIdx (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeMIdx with
  | .continue s' => s'
  | _ => afterDigit ls

/-- The state immediately before binding `"authOff"`. -/
def beforeAuthOff (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeAuthOff with
  | .continue s' => s'
  | _ => afterDigit ls

theorem beforeAuthOff_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeAuthOff = .continue (beforeAuthOff ls) := by
  unfold beforeAuthOff suffixBeforeAuthOff mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rfl

/-! ## 4a. The cutpoint immediately before the final `"wotsPk"` binding.

The accept-suffix `suffixBeforeAuthOff` ends in `.letVar "wotsPk" (andE (keccak
0x00 0x5A0) (u N_MASK))`.  The state immediately before this letVar is the
finest natural boundary at which the WOTS+C public-key Keccak preimage cells are
fully populated for the C13 layer boundary
infrastructure used to break the `wotsPk`-binding obligation away from the
final-Keccak preimage obligation. -/

/-- The straight-line prefix of `suffixBeforeAuthOff` minus the trailing
`.letVar "wotsPk"`. -/
def suffixBeforeWotsPk : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody ]

/-- The straight-line prefix of `suffixBeforeWotsPk` through the WOTS-PK address
store, stopping immediately before the final copy loop. -/
def suffixBeforeWotsPkCopy : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs") ]

/-- The state after the WOTS-PK address has been stored at `0x20`, but before
the WOTS chain-end copy loop. -/
def beforeWotsPkCopy (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeWotsPkCopy with
  | .continue s' => s'
  | _ => afterDigit ls

/-- The state immediately before binding `"wotsPk"` in the accept layer
suffix. -/
def beforeWotsPk (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeWotsPk with
  | .continue s' => s'
  | _ => afterDigit ls

def wotsPkAdrsExpr : Expr :=
  orE (shlE (u 224) (v "layer"))
    (orE (shlE (u 128) (v "idxTree"))
      (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf"))))

def beforeWotsPkWotsPtr (ls : RuntimeState) : RuntimeState :=
  { (afterDigit ls) with
    bindings := bindValue (afterDigit ls).bindings "wotsPtr"
      ((evalExpr [] (afterDigit ls)
        (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0) }

def beforeWotsPkAfterWots (ls : RuntimeState) : RuntimeState :=
  foldLoop "i" wotsOuterStep
    { (beforeWotsPkWotsPtr ls) with
      bindings := bindValue (beforeWotsPkWotsPtr ls).bindings "i" (wordNormalize 0) }
    0 43

/-- Splitting the WOTS-PK prebind prefix at the chain-end copy loop. -/
theorem suffixBeforeWotsPk_eq_beforeWotsPkCopy_append :
    suffixBeforeWotsPk =
      suffixBeforeWotsPkCopy ++ [ .forEach "i" (u 43) copyBody ] := rfl

/-- The prefix through the WOTS-PK address store always continues. -/
theorem beforeWotsPkCopy_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeWotsPkCopy =
      .continue (beforeWotsPkCopy ls) := by
  unfold beforeWotsPkCopy suffixBeforeWotsPkCopy mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

theorem beforeWotsPkAfterWots_lookup_of_ne
    (ls : RuntimeState) (key : String)
    (hneI : "i" ≠ key)
    (hneWotsPtr : "wotsPtr" ≠ key)
    (hneDigit : "digit" ≠ key)
    (hneSteps : "steps" ≠ key)
    (hneVal : "val" ≠ key)
    (hneChainBase : "chainBase" ≠ key)
    (hneStep : "step" ≠ key) :
    lookupValue (beforeWotsPkAfterWots ls).bindings key =
      lookupValue (afterDigit ls).bindings key := by
  unfold beforeWotsPkAfterWots
  rw [ClimbLoop.foldLoop_preserves_lookup "i" key wotsOuterStep hneI
    (fun s => wotsOuterStep_preserves_lookup_of_ne s key
      hneDigit hneSteps hneVal hneChainBase hneStep)]
  unfold beforeWotsPkWotsPtr
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" key _ hneI]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" key _ hneWotsPtr]

/-- Splitting the accept suffix at the final `"wotsPk"` letVar.  Purely
syntactic (`rfl`); the right factor is the single `.letVar "wotsPk"` statement. -/
theorem suffixBeforeAuthOff_eq_beforeWotsPk_append :
    suffixBeforeAuthOff =
      suffixBeforeWotsPk ++
        [ .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK)) ] := rfl

/-- The prefix before `"wotsPk"` always continues; same machinery as
`beforeAuthOff_eq` minus its final letVar step. -/
theorem beforeWotsPk_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeWotsPk = .continue (beforeWotsPk ls) := by
  unfold beforeWotsPk suffixBeforeWotsPk mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rfl

/-- The final WOTS-PK copy loop preserves the address slot written immediately
before it. -/
theorem beforeWotsPk_memory_0x20_eq_beforeWotsPkCopy (ls : RuntimeState) :
    ((beforeWotsPk ls).world.memory 0x20).val =
      ((beforeWotsPkCopy ls).world.memory 0x20).val := by
  have hCopy :
      execStmtList [] (beforeWotsPkCopy ls) [ .forEach "i" (u 43) copyBody ] =
        .continue (foldLoop "i" copyStep
          { (beforeWotsPkCopy ls) with
            bindings := bindValue (beforeWotsPkCopy ls).bindings "i" (wordNormalize 0) }
          0 43) := by
    unfold u
    rw [execStmtList_cons_continue _ _ _ []
        (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
    rfl
  unfold beforeWotsPk
  rw [suffixBeforeWotsPk_eq_beforeWotsPkCopy_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeWotsPkCopy_eq ls)]
  rw [hCopy]
  simpa using
    copyFold43_preserves_memory_0x20
      { (beforeWotsPkCopy ls) with
        bindings := bindValue (beforeWotsPkCopy ls).bindings "i" (wordNormalize 0) }

/-- The WOTS-PK-address expression evaluates to the spec address when the
threaded layer/tree/leaf bindings have been identified. -/
theorem evalExpr_pkAdrs_eq_of_layer_idxTree_idxLeaf
    (st : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue st.bindings "layer" = layer)
    (hIdxTree : lookupValue st.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue st.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    evalExpr [] st
      (orE (shlE (u 224) (v "layer"))
        (orE (shlE (u 128) (v "idxTree"))
          (orE (shlE (u 96) (u 1))
            (shlE (u 64) (v "idxLeaf"))))) =
      some (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf) := by
  unfold orE shlE u v
  have hLayerEval : evalExpr [] st (.localVar "layer") = some layer := by
    change some (lookupValue st.bindings "layer") = some layer
    rw [hLayer]
  have hIdxTreeEval : evalExpr [] st (.localVar "idxTree") = some idxTree := by
    change some (lookupValue st.bindings "idxTree") = some idxTree
    rw [hIdxTree]
  have hIdxLeafEval : evalExpr [] st (.localVar "idxLeaf") = some idxLeaf := by
    change some (lookupValue st.bindings "idxLeaf") = some idxLeaf
    rw [hIdxLeaf]
  have h224 :
      evalExpr [] st (.shl (.literal 224) (.localVar "layer")) =
        some (layer <<< 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 224) (.localVar "layer") 224 layer rfl hLayerEval
      (by decide : 224 < 2 ^ 256)
      (lt_trans hLayerLt (by decide : 2 ^ 32 < 2 ^ 256))
      (by
        rw [Nat.shiftLeft_eq]
        calc
          layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
            Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
          _ = 2 ^ 256 := by norm_num [Nat.pow_add])
  have h128 :
      evalExpr [] st (.shl (.literal 128) (.localVar "idxTree")) =
        some (idxTree <<< 128) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 128) (.localVar "idxTree") 128 idxTree rfl hIdxTreeEval
      (by decide : 128 < 2 ^ 256)
      (lt_trans hIdxTreeLt (by decide : 2 ^ 32 < 2 ^ 256))
      (by
        rw [Nat.shiftLeft_eq]
        calc
          idxTree * 2 ^ 128 < 2 ^ 32 * 2 ^ 128 :=
            Nat.mul_lt_mul_of_pos_right hIdxTreeLt (by decide)
          _ < 2 ^ 256 := by decide)
  have h96 :
      evalExpr [] st (.shl (.literal 96) (.literal 1)) =
        some ((1 : Nat) <<< 96) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 96) (.literal 1) 96 1 rfl rfl
      (by decide : 96 < 2 ^ 256)
      (by decide : 1 < 2 ^ 256)
      (by norm_num [Nat.shiftLeft_eq])
  have h64 :
      evalExpr [] st (.shl (.literal 64) (.localVar "idxLeaf")) =
        some (idxLeaf <<< 64) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 64) (.localVar "idxLeaf") 64 idxLeaf rfl hIdxLeafEval
      (by decide : 64 < 2 ^ 256)
      (lt_trans hIdxLeafLt (by decide : 2 ^ 32 < 2 ^ 256))
      (by
        rw [Nat.shiftLeft_eq]
        calc
          idxLeaf * 2 ^ 64 < 2 ^ 32 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_pos_right hIdxLeafLt (by decide)
          _ < 2 ^ 256 := by decide)
  have h224lt : layer <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
  have h128lt : idxTree <<< 128 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      idxTree * 2 ^ 128 < 2 ^ 32 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hIdxTreeLt (by decide)
      _ < 2 ^ 256 := by decide
  have h96lt : (1 : Nat) <<< 96 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have h64lt : idxLeaf <<< 64 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      idxLeaf * 2 ^ 64 < 2 ^ 32 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hIdxLeafLt (by decide)
      _ < 2 ^ 256 := by decide
  have h96_64 :
      evalExpr [] st
        (.bitOr (.shl (.literal 96) (.literal 1))
          (.shl (.literal 64) (.localVar "idxLeaf"))) =
        some (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st (.shl (.literal 96) (.literal 1))
      (.shl (.literal 64) (.localVar "idxLeaf"))
      ((1 : Nat) <<< 96) (idxLeaf <<< 64) h96 h64 h96lt h64lt
  have h96_64_lt :
      (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h96lt h64lt
  have hinner :
      evalExpr [] st
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.bitOr (.shl (.literal 96) (.literal 1))
            (.shl (.literal 64) (.localVar "idxLeaf")))) =
        some ((idxTree <<< 128) |||
          (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64))) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st (.shl (.literal 128) (.localVar "idxTree"))
      (.bitOr (.shl (.literal 96) (.literal 1))
        (.shl (.literal 64) (.localVar "idxLeaf")))
      (idxTree <<< 128)
      (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64))
      h128 h96_64 h128lt h96_64_lt
  have hinnerLt :
      ((idxTree <<< 128) ||| (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128lt h96_64_lt
  have hfull :
      evalExpr [] st
        (.bitOr (.shl (.literal 224) (.localVar "layer"))
          (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
            (.bitOr (.shl (.literal 96) (.literal 1))
              (.shl (.literal 64) (.localVar "idxLeaf"))))) =
        some ((layer <<< 224) |||
          ((idxTree <<< 128) ||| (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)))) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st (.shl (.literal 224) (.localVar "layer"))
      (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
        (.bitOr (.shl (.literal 96) (.literal 1))
          (.shl (.literal 64) (.localVar "idxLeaf")))
      )
      (layer <<< 224)
      ((idxTree <<< 128) ||| (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)))
      h224 hinner h224lt hinnerLt
  rw [hfull]
  simp [SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk, Nat.lor_assoc]

theorem beforeWotsPkAfterWots_eval_pkAdrs_eq_of_afterDigit_bindings
    (ls : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue (afterDigit ls).bindings "layer" = layer)
    (hIdxTree : lookupValue (afterDigit ls).bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue (afterDigit ls).bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    evalExpr [] (beforeWotsPkAfterWots ls) wotsPkAdrsExpr =
      some (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf) := by
  unfold wotsPkAdrsExpr
  exact evalExpr_pkAdrs_eq_of_layer_idxTree_idxLeaf
    (beforeWotsPkAfterWots ls) layer idxTree idxLeaf
    (by
      rw [beforeWotsPkAfterWots_lookup_of_ne ls "layer"
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hLayer)
    (by
      rw [beforeWotsPkAfterWots_lookup_of_ne ls "idxTree"
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hIdxTree)
    (by
      rw [beforeWotsPkAfterWots_lookup_of_ne ls "idxLeaf"
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hIdxLeaf)
    hLayerLt hIdxTreeLt hIdxLeafLt

/-- The WOTS-PK address word assembled from bounded layer/tree/leaf components
is already normalized as an EVM word. -/
theorem adrsWotsPk_wordNormalize_of_bounds
    (layer idxTree idxLeaf : Nat)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    wordNormalize
        (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
          layer idxTree idxLeaf) =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  have h224 : layer <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
  have h128 : idxTree <<< 128 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      idxTree * 2 ^ 128 < 2 ^ 32 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hIdxTreeLt (by decide)
      _ < 2 ^ 256 := by decide
  have h96 : (1 : Nat) <<< 96 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have h64 : idxLeaf <<< 64 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      idxLeaf * 2 ^ 64 < 2 ^ 32 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hIdxLeafLt (by decide)
      _ < 2 ^ 256 := by decide
  have h96_64 :
      (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h96 h64
  have hinner :
      ((idxTree <<< 128) ||| (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64))) <
        2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h96_64
  have haddr :
      ((layer <<< 224) |||
        ((idxTree <<< 128) ||| (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)))) <
        2 ^ 256 :=
    Nat.bitwise_lt_two_pow h224 hinner
  simpa [SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

/-- At the pre-copy WOTS-PK cutpoint, cell `0x20` contains the WOTS-PK address
assembled from the current layer/tree/leaf bindings. -/
theorem beforeWotsPkCopy_memory_0x20_eq_of_afterDigit_bindings
    (ls : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue (afterDigit ls).bindings "layer" = layer)
    (hIdxTree : lookupValue (afterDigit ls).bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue (afterDigit ls).bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    ((beforeWotsPkCopy ls).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  have hEval :=
    beforeWotsPkAfterWots_eval_pkAdrs_eq_of_afterDigit_bindings
      ls layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
      hLayerLt hIdxTreeLt hIdxLeafLt
  unfold wotsPkAdrsExpr u at hEval
  -- Thread the 2-statement prefix to the *named* cutpoint, introducing the
  -- `wotsPtr` value in its `.getD` form so the closing `rfl` never has to
  -- align a whnf'd eval against `beforeWotsPkWotsPtr`'s `getD` (that defeq
  -- whnf-unfolds the 64-iteration digit fold and exhausts memory).
  have hpre : execStmtList [] (afterDigit ls)
      [ (.letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")) : Stmt)
      , .forEach "i" (u 43) wotsOuterBody ]
      = .continue (beforeWotsPkAfterWots ls) := by
    unfold beforeWotsPkAfterWots beforeWotsPkWotsPtr u addE v
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue _ "wotsPtr"
        (.add (.localVar "sigBase") (.localVar "sigOff"))
        ((evalExpr [] (afterDigit ls)
          (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0)
        rfl)]
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _
        wotsOuterStep rfl wotsOuterStepLemma)]
    rw [show wordNormalize 43 = 43 from rfl]
    rfl
  unfold beforeWotsPkCopy
  rw [show suffixBeforeWotsPkCopy
      = [ (.letVar "wotsPtr" (addE (v "sigBase") (v "sigOff")) : Stmt)
        , .forEach "i" (u 43) wotsOuterBody ]
        ++ [ .letVar "pkAdrs"
              (orE (shlE (u 224) (v "layer"))
                (orE (shlE (u 128) (v "idxTree"))
                  (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
           , mstore 0x20 (v "pkAdrs") ] from rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hpre]
  unfold mstore u
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_letVar_continue _ "pkAdrs" _ _ hEval)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self,
    show wordNormalize 32 = 32 from rfl,
    MemoryKit.memUpdate_val_same]
  exact adrsWotsPk_wordNormalize_of_bounds
    layer idxTree idxLeaf hLayerLt hIdxTreeLt hIdxLeafLt

/-- The final copy loop preserves the WOTS-PK address cell at `0x20`, so the
full pre-`wotsPk` cutpoint has the same address word as the pre-copy cutpoint. -/
theorem beforeWotsPk_memory_0x20_eq_of_afterDigit_bindings
    (ls : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue (afterDigit ls).bindings "layer" = layer)
    (hIdxTree : lookupValue (afterDigit ls).bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue (afterDigit ls).bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    ((beforeWotsPk ls).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  rw [beforeWotsPk_memory_0x20_eq_beforeWotsPkCopy]
  exact beforeWotsPkCopy_memory_0x20_eq_of_afterDigit_bindings
    ls layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
    hLayerLt hIdxTreeLt hIdxLeafLt

/-- The prefix before `"wotsPk"` preserves seed cell `0x00` once the two loop
statements are supplied as bounded frame facts. -/
theorem beforeWotsPk_preserves_memory_zero_of_loop_frames
    (ls : RuntimeState)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val) :
    ((beforeWotsPk ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 suffixBeforeWotsPk (afterDigit ls) (beforeWotsPk ls) ?_
    (beforeWotsPk_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeWotsPk, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPtr" _ hexec
  · exact hWots s s'' hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "pkAdrs" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff _
    cases hoff
    decide
  · exact hCopy s s'' hexec

/-- The `"wotsPk"` binding at `beforeAuthOff` is exactly the masked Keccak
evaluated at the smaller `beforeWotsPk` boundary. This splits the
binding equation away from the substantive WOTS+C Keccak-preimage obligation:
the binding equation is now unconditional, and the residual is the value-only
final-Keccak fact at the smaller boundary. -/
theorem beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "wotsPk" =
      (evalExpr [] (beforeWotsPk ls)
        (andE (keccak 0x00 0x5A0) (u N_MASK))).getD 0 := by
  unfold beforeAuthOff
  rw [suffixBeforeAuthOff_eq_beforeWotsPk_append]
  rw [SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue _ _ _ _
        (beforeWotsPk_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _
        (execStmt_letVar_continue (beforeWotsPk ls) "wotsPk" _ _ rfl)]
  change lookupValue
      (bindValue (beforeWotsPk ls).bindings "wotsPk"
        ((evalExpr [] (beforeWotsPk ls)
          (andE (keccak 0x00 0x5A0) (u N_MASK))).getD 0))
      "wotsPk" =
    (evalExpr [] (beforeWotsPk ls)
      (andE (keccak 0x00 0x5A0) (u N_MASK))).getD 0
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]

/-- World-state preservation: the only effect of executing the final
`.letVar "wotsPk"` step between `beforeWotsPk` and `beforeAuthOff` is to add the
`"wotsPk"` binding; the world (memory, calldata, selector) is unchanged.  This
is the bridge that lets callers swap `beforeAuthOff` for `beforeWotsPk` inside
an `evalExpr` whose only data dependency is on memory. -/
theorem beforeAuthOff_world_eq_beforeWotsPk (ls : RuntimeState) :
    (beforeAuthOff ls).world = (beforeWotsPk ls).world := by
  have hEq : execStmtList [] (afterDigit ls) suffixBeforeAuthOff =
      .continue (beforeAuthOff ls) := beforeAuthOff_eq ls
  have hSplit : suffixBeforeAuthOff =
      suffixBeforeWotsPk ++
        [ .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK)) ] :=
    suffixBeforeAuthOff_eq_beforeWotsPk_append
  rw [hSplit] at hEq
  rw [SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue _ _ _ _
        (beforeWotsPk_eq ls)] at hEq
  rw [execStmtList_cons_continue _ _ _ _
        (execStmt_letVar_continue (beforeWotsPk ls) "wotsPk" _ _ rfl)] at hEq
  -- After the cons-continue rewrite, hEq states
  --   execStmtList [] {beforeWotsPk ls with bindings := bindValue …} [] = .continue (beforeAuthOff ls)
  -- which definitionally reduces to .continue {beforeWotsPk ls with bindings := bindValue …}.
  -- Injecting the .continue payload gives the structural equality on RuntimeState.
  have hEqState : ({(beforeWotsPk ls) with
        bindings :=
          bindValue (beforeWotsPk ls).bindings "wotsPk"
            ((evalExpr [] (beforeWotsPk ls)
              (andE (keccak 0x00 0x5A0) (u N_MASK))).getD 0) } : RuntimeState)
      = beforeAuthOff ls := by
    have := hEq
    -- both sides are .continue-wrapped RuntimeStates; strip the constructor
    simpa [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList] using this
  rw [← hEqState]

/-- Final WOTS-PK masked-Keccak evaluation at the `beforeWotsPk` cutpoint,
provided the 45-word scratch preimage has already been materialized in memory.

This is the reusable endpoint for the WOTS outer-loop/copy-loop facts: once
`0x00` holds the seed, `0x20` holds the WOTS-PK address, and
`0x40 + 32*j` holds the `j`th reconstructed chain end, the executable
`keccak256(0x00, 0x5A0) & N_MASK` is exactly the spec `wotsPkWord`. -/
theorem beforeWotsPk_keccak_eq_wotsPkWord_of_cells
    (ls : RuntimeState) (seed layer treeIdx leafIdx node : Nat)
    (wots : SphincsMinusVerifierSpec.WotsSig)
    (hm0 : ((beforeWotsPk ls).world.memory 0x00).val = seed)
    (hm1 : ((beforeWotsPk ls).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk layer treeIdx leafIdx)
    (hmC : ∀ j, (h : j < 43) →
      ((beforeWotsPk ls).world.memory (0x40 + 32 * j)).val =
        (SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd
          seed layer treeIdx leafIdx node wots)[j]'(by
            rw [SphincsMinusVerifiers.InitialNodeKeccak.wotsChainsEnd_length]
            omega)) :
    evalExpr [] (beforeWotsPk ls)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal N_MASK))
      =
        some (SphincsMinusVerifierSpec.C13Concrete.wotsPkWord
          seed layer treeIdx leafIdx node wots) := by
  exact SphincsMinusVerifiers.InitialNodeKeccak.wots_pk_node_eq_spec
    (beforeWotsPk ls) seed layer treeIdx leafIdx node wots hm0 hm1 hmC

/-- The prefix before binding `"authOff"` preserves seed cell `0x00` once the two
loop statements are supplied as bounded frame facts. This keeps the straight-line
frame separate from the heavier WOTS/copy loop adapters. -/
theorem beforeAuthOff_preserves_memory_zero_of_loop_frames
    (ls : RuntimeState)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val) :
    ((beforeAuthOff ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 suffixBeforeAuthOff (afterDigit ls) (beforeAuthOff ls) ?_
    (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPtr" _ hexec
  · exact hWots s s'' hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "pkAdrs" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff _
    cases hoff
    decide
  · exact hCopy s s'' hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPk" _ hexec

/-- The suffix prefix before `"authOff"` does not rebind `"countOff"`. -/
theorem suffixBeforeAuthOff_preserves_countOff (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "countOff" =
      lookupValue (afterDigit ls).bindings "countOff" := by
  refine execStmtList_preserves_lookup "countOff" suffixBeforeAuthOff
    (afterDigit ls) (beforeAuthOff ls) ?_ (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "countOff" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "countOff" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "countOff" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "countOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "countOff" _ (by decide) hexec

/-- The suffix prefix before `"authOff"` does not rebind the layer leaf index. -/
theorem suffixBeforeAuthOff_preserves_idxLeaf (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "idxLeaf" =
      lookupValue (afterDigit ls).bindings "idxLeaf" := by
  refine execStmtList_preserves_lookup "idxLeaf" suffixBeforeAuthOff
    (afterDigit ls) (beforeAuthOff ls) ?_ (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "idxLeaf" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxLeaf" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "idxLeaf" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "idxLeaf" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "idxLeaf" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "idxLeaf" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "idxLeaf" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "idxLeaf" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "idxLeaf" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "idxLeaf" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxLeaf" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "idxLeaf" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "idxLeaf" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxLeaf" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "idxLeaf" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "idxLeaf" _ (by decide) hexec

/-- The suffix prefix before `"authOff"` does not rebind `"sigBase"`. -/
theorem suffixBeforeAuthOff_preserves_sigBase (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "sigBase" =
      lookupValue (afterDigit ls).bindings "sigBase" := by
  refine execStmtList_preserves_lookup "sigBase" suffixBeforeAuthOff
    (afterDigit ls) (beforeAuthOff ls) ?_ (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "sigBase" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "sigBase" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "sigBase" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "sigBase" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "sigBase" _ (by decide) hexec

/-- The suffix prefix before `"authOff"` does not rebind `"idxTree"`. -/
theorem suffixBeforeAuthOff_preserves_idxTree (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "idxTree" =
      lookupValue (afterDigit ls).bindings "idxTree" := by
  refine execStmtList_preserves_lookup "idxTree" suffixBeforeAuthOff
    (afterDigit ls) (beforeAuthOff ls) ?_ (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "idxTree" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "idxTree" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "idxTree" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "idxTree" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "idxTree" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "idxTree" _ (by decide) hexec

/-- The suffix prefix before `"authOff"` does not rebind `"layer"`. -/
theorem suffixBeforeAuthOff_preserves_layer (ls : RuntimeState) :
    lookupValue (beforeAuthOff ls).bindings "layer" =
      lookupValue (afterDigit ls).bindings "layer" := by
  refine execStmtList_preserves_lookup "layer" suffixBeforeAuthOff
    (afterDigit ls) (beforeAuthOff ls) ?_ (beforeAuthOff_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeAuthOff, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "layer" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "layer" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "layer" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "layer" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "layer" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "layer" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "layer" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "layer" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "layer" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "layer" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "layer" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "layer" _ (by decide) hexec

/-- The state before binding `"authOff"` still carries the count offset computed
from the incoming `"sigOff"`. -/
theorem beforeAuthOff_countOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256) :
    lookupValue (beforeAuthOff ls).bindings "countOff" = sigOff + 688 := by
  rw [suffixBeforeAuthOff_preserves_countOff]
  rw [afterDigit_preserves_lookup_of_ne ls "countOff" (by decide) (by decide)]
  exact beforeDigitLoop_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt

/-- The state before binding `"authOff"` still carries the low-11-bit leaf index
computed from the incoming `"idxTree"`. -/
theorem beforeAuthOff_idxLeaf_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeAuthOff ls).bindings "idxLeaf" = idxTree % 2048 := by
  rw [suffixBeforeAuthOff_preserves_idxLeaf]
  exact afterDigit_idxLeaf_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

/-- The state before binding `"authOff"` still carries the shifted hypertree
index computed from the incoming `"idxTree"`. -/
theorem beforeAuthOff_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeAuthOff ls).bindings "idxTree" = idxTree / 2048 := by
  rw [suffixBeforeAuthOff_preserves_idxTree]
  rw [afterDigit_preserves_lookup_of_ne ls "idxTree" (by decide) (by decide)]
  exact beforeDigitLoop_idxTree_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

/-- The state before binding `"authOff"` still carries the incoming layer index. -/
theorem beforeAuthOff_layer_eq
    (ls : RuntimeState) (layer : Nat)
    (hLayer : lookupValue ls.bindings "layer" = layer) :
    lookupValue (beforeAuthOff ls).bindings "layer" = layer := by
  rw [suffixBeforeAuthOff_preserves_layer]
  rw [afterDigit_preserves_lookup_of_ne ls "layer" (by decide) (by decide)]
  rw [beforeDigitLoop_preserves_layer]
  exact hLayer

theorem beforeMerkle_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeMerkle = .continue (beforeMerkle ls) := by
  unfold beforeMerkle suffixBeforeMerkle mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rfl

/-- The accepting suffix reaches the cutpoint just before `"mIdx"`. -/
theorem beforeMIdx_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeMIdx = .continue (beforeMIdx ls) := by
  unfold beforeMIdx suffixBeforeMIdx u
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rfl

/-- The cutpoint before `"mIdx"` still carries the low-11-bit leaf index. -/
theorem beforeMIdx_idxLeaf_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeMIdx ls).bindings "idxLeaf" = idxTree % 2048 := by
  unfold beforeMIdx suffixBeforeMIdx u
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "treeAdrs" "idxLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "idxLeaf" _ (by decide)]
  exact beforeAuthOff_idxLeaf_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

/-- The cutpoint before `"mIdx"` carries the XMSS tree-address base assembled
from the layer index and shifted hypertree index. -/
theorem beforeMIdx_treeAdrs_eq_of_layer_idxTree
    (ls : RuntimeState) (layer idxTree : Nat)
    (hLayer : lookupValue ls.bindings "layer" = layer)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 22) :
    lookupValue (beforeMIdx ls).bindings "treeAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsXmssTree layer (idxTree / 2048) := by
  unfold beforeMIdx suffixBeforeMIdx u shlE orE v
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue _ "treeAdrs" _
        (SphincsMinusVerifierSpec.C13Concrete.adrsXmssTree layer (idxTree / 2048)) (by
    let authVal : Nat := (evalExpr [] (beforeAuthOff ls) (addE (v "countOff") (u 4))).getD 0
    let stA : RuntimeState :=
      { beforeAuthOff ls with
        bindings := bindValue (beforeAuthOff ls).bindings "authOff" authVal }
    change evalExpr [] stA
        (.bitOr (.shl (.literal 224) (.localVar "layer"))
          (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
            (.shl (.literal 96) (.literal 2)))) =
        some (SphincsMinusVerifierSpec.C13Concrete.adrsXmssTree layer (idxTree / 2048))
    have hLayerEval : evalExpr [] stA (.localVar "layer") = some layer := by
      change some (lookupValue stA.bindings "layer") = some layer
      dsimp [stA]
      rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "layer" _ (by decide)]
      rw [beforeAuthOff_layer_eq ls layer hLayer]
    have hIdxTreeEval : evalExpr [] stA (.localVar "idxTree") = some (idxTree / 2048) := by
      change some (lookupValue stA.bindings "idxTree") = some (idxTree / 2048)
      dsimp [stA]
      rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "idxTree" _ (by decide)]
      exact congrArg some (beforeAuthOff_idxTree_eq_of_idxTree ls idxTree hIdxTree
        (lt_trans hIdxTreeLt (by decide : 2 ^ 22 < 2 ^ 256)))
    have hLit2 : evalExpr [] stA (.literal 2) = some 2 := by
      show some (wordNormalize 2) = some 2
      rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
    have h224 :
        evalExpr [] stA (.shl (.literal 224) (.localVar "layer")) =
          some (layer <<< 224) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
        stA (.literal 224) (.localVar "layer") 224 layer rfl hLayerEval
        (by decide : 224 < 2 ^ 256)
        (lt_trans hLayerLt (by decide : 2 ^ 32 < 2 ^ 256))
        (by
          rw [Nat.shiftLeft_eq]
          calc
            layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
              Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
            _ = 2 ^ 256 := by norm_num [Nat.pow_add])
    have h128 :
        evalExpr [] stA (.shl (.literal 128) (.localVar "idxTree")) =
          some ((idxTree / 2048) <<< 128) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
        stA (.literal 128) (.localVar "idxTree") 128 (idxTree / 2048) rfl hIdxTreeEval
        (by decide : 128 < 2 ^ 256)
        (lt_trans (Nat.div_lt_of_lt_mul hIdxTreeLt) (by decide : 2048 < 2 ^ 256))
        (by
          have hnext : idxTree / 2048 < 2 ^ 11 := Nat.div_lt_of_lt_mul hIdxTreeLt
          rw [Nat.shiftLeft_eq]
          calc
            (idxTree / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
              Nat.mul_lt_mul_of_pos_right hnext (by decide)
            _ < 2 ^ 256 := by decide)
    have h96 :
        evalExpr [] stA (.shl (.literal 96) (.literal 2)) =
          some (2 <<< 96) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
        stA (.literal 96) (.literal 2) 96 2 rfl hLit2
        (by decide : 96 < 2 ^ 256)
        (by decide : 2 < 2 ^ 256)
        (by
          rw [Nat.shiftLeft_eq]
          decide)
    have h224lt : layer <<< 224 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
          Nat.mul_lt_mul_of_pos_right hLayerLt (by decide)
        _ = 2 ^ 256 := by norm_num [Nat.pow_add]
    have h128lt : (idxTree / 2048) <<< 128 < 2 ^ 256 := by
      have hnext : idxTree / 2048 < 2 ^ 11 := Nat.div_lt_of_lt_mul hIdxTreeLt
      rw [Nat.shiftLeft_eq]
      calc
        (idxTree / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
          Nat.mul_lt_mul_of_pos_right hnext (by decide)
        _ < 2 ^ 256 := by decide
    have h96lt : 2 <<< 96 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      decide
    have hinner :
        evalExpr [] stA
          (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
            (.shl (.literal 96) (.literal 2))) =
          some (((idxTree / 2048) <<< 128) ||| (2 <<< 96)) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
        stA (.shl (.literal 128) (.localVar "idxTree"))
        (.shl (.literal 96) (.literal 2))
        ((idxTree / 2048) <<< 128) (2 <<< 96)
        h128 h96 h128lt h96lt
    have hinnerLt :
        (((idxTree / 2048) <<< 128) ||| (2 <<< 96)) < 2 ^ 256 :=
      Nat.bitwise_lt_two_pow h128lt h96lt
    have hfull :
        evalExpr [] stA
          (.bitOr (.shl (.literal 224) (.localVar "layer"))
            (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
              (.shl (.literal 96) (.literal 2)))) =
          some ((layer <<< 224) ||| (((idxTree / 2048) <<< 128) ||| (2 <<< 96))) :=
      SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
        stA (.shl (.literal 224) (.localVar "layer"))
        (.bitOr (.shl (.literal 128) (.localVar "idxTree"))
          (.shl (.literal 96) (.literal 2)))
        (layer <<< 224) (((idxTree / 2048) <<< 128) ||| (2 <<< 96))
        h224 hinner h224lt hinnerLt
    simpa [SphincsMinusVerifierSpec.C13Concrete.adrsXmssTree, Nat.lor_assoc] using hfull))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "treeAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- The Merkle-climb prefix initializes `"mIdx"` from the low-11-bit leaf index. -/
theorem beforeMerkle_mIdx_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (beforeMerkle ls).bindings "mIdx" = idxTree % 2048 := by
  unfold beforeMerkle
  rw [show suffixBeforeMerkle =
      suffixBeforeMIdx ++
        [ .letVar "mIdx" (v "idxLeaf")
        , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeMIdx_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "mIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  exact beforeMIdx_idxLeaf_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

/-- The Merkle-climb prefix keeps the XMSS tree-address base assembled before
`"mIdx"` and `"merklePtr"` are bound. -/
theorem beforeMerkle_treeAdrs_eq_of_layer_idxTree
    (ls : RuntimeState) (layer idxTree : Nat)
    (hLayer : lookupValue ls.bindings "layer" = layer)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 22) :
    lookupValue (beforeMerkle ls).bindings "treeAdrs" =
      SphincsMinusVerifierSpec.C13Concrete.adrsXmssTree layer (idxTree / 2048) := by
  unfold beforeMerkle
  rw [show suffixBeforeMerkle =
      suffixBeforeMIdx ++
        [ .letVar "mIdx" (v "idxLeaf")
        , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeMIdx_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "treeAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "treeAdrs" _ (by decide)]
  exact beforeMIdx_treeAdrs_eq_of_layer_idxTree
    ls layer idxTree hLayer hIdxTree hLayerLt hIdxTreeLt

/-- The state before the Merkle loop preserves seed cell `0x00` once the WOTS and
copy loops are supplied as bounded frame facts. -/
theorem beforeMerkle_preserves_memory_zero_of_loop_frames
    (ls : RuntimeState)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val) :
    ((beforeMerkle ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  let tail : List Stmt :=
    [ .letVar "authOff" (addE (v "countOff") (u 4))
    , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
    , .letVar "merkleNode" (v "wotsPk")
    , .letVar "mIdx" (v "idxLeaf")
    , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ]
  have hTailExec :
      execStmtList [] (beforeAuthOff ls) tail = .continue (beforeMerkle ls) := by
    have h := beforeMerkle_eq ls
    have hSplit : suffixBeforeMerkle = suffixBeforeAuthOff ++ tail := by
      unfold tail
      rfl
    rw [hSplit] at h
    rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)] at h
    exact h
  have hTailMem :
      ((beforeMerkle ls).world.memory 0x00).val =
        ((beforeAuthOff ls).world.memory 0x00).val := by
    refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
      0x00 tail (beforeAuthOff ls) (beforeMerkle ls) ?_ hTailExec
    intro s s'' stmt hmem hexec
    simp [tail] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
        s s'' 0x00 "authOff" _ hexec
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
        s s'' 0x00 "treeAdrs" _ hexec
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
        s s'' 0x00 "merkleNode" _ hexec
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
        s s'' 0x00 "mIdx" _ hexec
    · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
        s s'' 0x00 "merklePtr" _ hexec
  rw [hTailMem]
  exact beforeAuthOff_preserves_memory_zero_of_loop_frames ls hWots hCopy

/-- The suffix prefix leading to the Merkle loop preserves selector/calldata. -/
theorem suffixBeforeMerkle_preserves_selector_calldata :
    PreservesSelectorCalldataBody suffixBeforeMerkle := by
  intro s s'' stmt hmem hexec
  simp [suffixBeforeMerkle, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsPtr" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ wotsOuterBody s s'' wotsOuterBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "pkAdrs" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "i" _ copyBody s s'' copyBody_preserves_selector_calldata hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "wotsPk" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "authOff" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "treeAdrs" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "merkleNode" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "mIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "merklePtr" _ hexec

/-- The cutpoint before the Merkle loop preserves selector/calldata from the
incoming layer state. -/
theorem beforeMerkle_preserves_selector_calldata (ls : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata ls (beforeMerkle ls) := by
  have hPrefix := afterDigit_preserves_selector_calldata ls
  have hSuffix :=
    SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
      suffixBeforeMerkle (afterDigit ls) (beforeMerkle ls)
      suffixBeforeMerkle_preserves_selector_calldata (beforeMerkle_eq ls)
  exact ⟨by rw [hSuffix.1, hPrefix.1], by rw [hSuffix.2, hPrefix.2]⟩

/-- The suffix leading to the Merkle loop does not rebind `"countOff"`. -/
theorem suffixBeforeMerkle_preserves_countOff (ls : RuntimeState) :
    lookupValue (beforeMerkle ls).bindings "countOff" =
      lookupValue (afterDigit ls).bindings "countOff" := by
  refine execStmtList_preserves_lookup "countOff" suffixBeforeMerkle
    (afterDigit ls) (beforeMerkle ls) ?_ (beforeMerkle_eq ls)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeMerkle, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "countOff" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "countOff" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "countOff" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "countOff" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "countOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "countOff" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "countOff" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "countOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "countOff" _ (by decide) hexec

/-- The state before the Merkle loop still carries the count offset computed
from the incoming `"sigOff"`. -/
theorem beforeMerkle_countOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256) :
    lookupValue (beforeMerkle ls).bindings "countOff" = sigOff + 688 := by
  rw [suffixBeforeMerkle_preserves_countOff]
  rw [afterDigit_preserves_lookup_of_ne ls "countOff" (by decide) (by decide)]
  exact beforeDigitLoop_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt

/-- The state before the Merkle loop binds `"authOff"` to incoming
`"sigOff" + 692`. -/
theorem beforeMerkle_authOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256) :
    lookupValue (beforeMerkle ls).bindings "authOff" = sigOff + 692 := by
  unfold beforeMerkle
  rw [show suffixBeforeMerkle =
      suffixBeforeAuthOff ++
        [ .letVar "authOff" (addE (v "countOff") (u 4))
        , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
        , .letVar "merkleNode" (v "wotsPk")
        , .letVar "mIdx" (v "idxLeaf")
        , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue _ "authOff" _ (sigOff + 692) (by
    have hCountOff :
        evalExpr [] (beforeAuthOff ls) (v "countOff") = some (sigOff + 688) := by
      change some (lookupValue (beforeAuthOff ls).bindings "countOff") = some (sigOff + 688)
      rw [beforeAuthOff_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt]
    have hSum : sigOff + 688 + 4 = sigOff + 692 := by omega
    rw [← hSum]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      _ (v "countOff") (u 4) (sigOff + 688) 4 hCountOff rfl
      hCountOffLt (by decide : 4 < 2 ^ 256) (by simpa [hSum] using hAuthOffLt)))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "treeAdrs" "authOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- The state before the Merkle loop binds `"merklePtr"` to
`"sigBase" + ("sigOff" + 692)`. -/
theorem beforeMerkle_merklePtr_eq_of_sigBase_sigOff
    (ls : RuntimeState) (sigBase sigOff : Nat)
    (hSigBase : lookupValue ls.bindings "sigBase" = sigBase)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigBaseLt : sigBase < 2 ^ 256)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256)
    (hMerklePtrLt : sigBase + (sigOff + 692) < 2 ^ 256) :
    lookupValue (beforeMerkle ls).bindings "merklePtr" = sigBase + (sigOff + 692) := by
  unfold beforeMerkle
  rw [show suffixBeforeMerkle =
      suffixBeforeAuthOff ++
        [ .letVar "authOff" (addE (v "countOff") (u 4))
        , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
        , .letVar "merkleNode" (v "wotsPk")
        , .letVar "mIdx" (v "idxLeaf")
        , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeAuthOff_eq ls)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue _ "authOff" _ (sigOff + 692) (by
    have hCountOff :
        evalExpr [] (beforeAuthOff ls) (v "countOff") = some (sigOff + 688) := by
      change some (lookupValue (beforeAuthOff ls).bindings "countOff") = some (sigOff + 688)
      rw [beforeAuthOff_countOff_eq_of_sigOff ls sigOff hSigOff hSigOffLt hCountOffLt]
    have hSum : sigOff + 688 + 4 = sigOff + 692 := by omega
    rw [← hSum]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      _ (v "countOff") (u 4) (sigOff + 688) 4 hCountOff rfl
      hCountOffLt (by decide : 4 < 2 ^ 256) (by simpa [hSum] using hAuthOffLt)))]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue _ "merklePtr" _ (sigBase + (sigOff + 692)) (by
    have hBase :
        evalExpr []
          { (beforeAuthOff ls) with
            bindings :=
              bindValue
                (bindValue
                  (bindValue (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                    "treeAdrs"
                    ((evalExpr []
                      { (beforeAuthOff ls) with
                        bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                      (orE (shlE (u 224) (v "layer"))
                        (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                  "merkleNode"
                  (lookupValue
                    (bindValue
                      (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                      "treeAdrs"
                      ((evalExpr []
                        { (beforeAuthOff ls) with
                          bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                        (orE (shlE (u 224) (v "layer"))
                          (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                    "wotsPk"))
                "mIdx"
                (lookupValue
                  (bindValue
                    (bindValue
                      (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                      "treeAdrs"
                      ((evalExpr []
                        { (beforeAuthOff ls) with
                          bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                        (orE (shlE (u 224) (v "layer"))
                          (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                    "merkleNode"
                    (lookupValue
                      (bindValue
                        (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                        "treeAdrs"
                        ((evalExpr []
                          { (beforeAuthOff ls) with
                            bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                          (orE (shlE (u 224) (v "layer"))
                            (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                      "wotsPk"))
                  "idxLeaf") }
          (v "sigBase") = some sigBase := by
      change some (lookupValue _ "sigBase") = some sigBase
      repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "sigBase" _ (by decide)]
      rw [suffixBeforeAuthOff_preserves_sigBase]
      rw [afterDigit_preserves_lookup_of_ne ls "sigBase" (by decide) (by decide)]
      rw [beforeDigitLoop_preserves_sigBase]
      rw [hSigBase]
    have hAuth :
        evalExpr []
          { (beforeAuthOff ls) with
            bindings :=
              bindValue
                (bindValue
                  (bindValue (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                    "treeAdrs"
                    ((evalExpr []
                      { (beforeAuthOff ls) with
                        bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                      (orE (shlE (u 224) (v "layer"))
                        (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                  "merkleNode"
                  (lookupValue
                    (bindValue
                      (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                      "treeAdrs"
                      ((evalExpr []
                        { (beforeAuthOff ls) with
                          bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                        (orE (shlE (u 224) (v "layer"))
                          (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                    "wotsPk"))
                "mIdx"
                (lookupValue
                  (bindValue
                    (bindValue
                      (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                      "treeAdrs"
                      ((evalExpr []
                        { (beforeAuthOff ls) with
                          bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                        (orE (shlE (u 224) (v "layer"))
                          (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                    "merkleNode"
                    (lookupValue
                      (bindValue
                        (bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692))
                        "treeAdrs"
                        ((evalExpr []
                          { (beforeAuthOff ls) with
                            bindings := bindValue (beforeAuthOff ls).bindings "authOff" (sigOff + 692) }
                          (orE (shlE (u 224) (v "layer"))
                            (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))).getD 0))
                      "wotsPk"))
                  "idxLeaf") }
          (v "authOff") = some (sigOff + 692) := by
      change some (lookupValue _ "authOff") = some (sigOff + 692)
      rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "authOff" _ (by decide)]
      rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "authOff" _ (by decide)]
      rw [MemoryKit.lookupValue_bindValue_ne _ "treeAdrs" "authOff" _ (by decide)]
      rw [MemoryKit.lookupValue_bindValue_self]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      _ (v "sigBase") (v "authOff") sigBase (sigOff + 692)
      hBase hAuth hSigBaseLt hAuthOffLt hMerklePtrLt))]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]

/-- One XMSS Merkle-climb step does not rebind `"authOff"`. -/
theorem merkleStep_preserves_authOff (st : RuntimeState) :
    lookupValue
        (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" st).bindings
        "authOff" =
      lookupValue st.bindings "authOff" := by
  refine execStmtList_preserves_lookup "authOff"
    (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    st (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" st)
    ?_ (SphincsMinusVerifiers.ClimbKit.merkleClimbStep
      "merkleNode" "mIdx" "treeAdrs" "merklePtr" st)
  intro s s'' stmt hmem hexec
  simp [merkleClimbBody] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "sibling" "authOff" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "authOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "authOff" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "s" "authOff" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "authOff" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "authOff" _ _ hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "merkleNode" "authOff" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "mIdx" "authOff" _ (by decide) hexec

/-- The exact folded XMSS Merkle-climb state inside one accepting layer iteration. -/
def afterMerkle (ls : RuntimeState) : RuntimeState :=
  foldLoop "h" (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    { beforeMerkle ls with
      bindings := bindValue (beforeMerkle ls).bindings "h" (wordNormalize 0) }
    0 (wordNormalize 11)

/-- The folded XMSS Merkle climb preserves the `"authOff"` binding initialized
before the loop. -/
theorem afterMerkle_authOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256) :
    lookupValue (afterMerkle ls).bindings "authOff" = sigOff + 692 := by
  unfold afterMerkle
  rw [ClimbLoop.foldLoop_preserves_lookup "h" "authOff"
      (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
      (by decide) (fun s => merkleStep_preserves_authOff s)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "authOff" _ (by decide)]
  exact beforeMerkle_authOff_eq_of_sigOff
    ls sigOff hSigOff hSigOffLt hCountOffLt hAuthOffLt

/-- The folded Merkle climb preserves seed cell `0x00` once the layer prefix
loops and each Merkle step are supplied as frame facts. -/
theorem afterMerkle_preserves_memory_zero_of_loop_frames
    (ls : RuntimeState)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hMerkle :
      ∀ (s : RuntimeState),
        ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" s).world.memory
            0x00).val =
          (s.world.memory 0x00).val) :
    ((afterMerkle ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  unfold afterMerkle
  rw [ClimbLoop.foldLoop_preserves_memory_val "h"
    (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr") 0x00 hMerkle
    { beforeMerkle ls with
      bindings := bindValue (beforeMerkle ls).bindings "h" (wordNormalize 0) }
    0 (wordNormalize 11)]
  exact beforeMerkle_preserves_memory_zero_of_loop_frames ls hWots hCopy

/-- Range-gated variant of `afterMerkle_preserves_memory_zero_of_loop_frames`.
The Merkle-step frame may depend on the concrete height bound to `"h"`. -/
theorem afterMerkle_preserves_memory_zero_of_loop_frames_range
    (ls : RuntimeState) (D : Nat → Prop)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hMerkle :
      ∀ (s : RuntimeState) (idx : Nat), D idx →
        ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
            0x00).val =
          (s.world.memory 0x00).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 11 → D i) :
    ((afterMerkle ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  unfold afterMerkle
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "h"
    (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr") 0x00 D hMerkle
    { beforeMerkle ls with
      bindings := bindValue (beforeMerkle ls).bindings "h" (wordNormalize 0) }
    0 (wordNormalize 11) hD]
  exact beforeMerkle_preserves_memory_zero_of_loop_frames ls hWots hCopy

set_option maxHeartbeats 4000000 in
theorem suffix14_continues (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffix14 = .continue (stepLayer ls) := by
  unfold stepLayer suffix14 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 _)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  rfl

/-- Once the Merkle loop state has been named, the final two layer assignments
continue to `stepLayer`. -/
theorem finalLayerTail_continues_from_afterMerkle (ls : RuntimeState) :
    execStmtList [] (afterMerkle ls)
        [ .assignVar "currentNode" (v "merkleNode")
        , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] =
      .continue (stepLayer ls) := by
  let suffixMerkleAndTail : List Stmt :=
    [ .forEach "h" (u 11) (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    , .assignVar "currentNode" (v "merkleNode")
    , .assignVar "sigOff" (addE (v "authOff") (u 176)) ]
  have h := suffix14_continues ls
  have hSplit : suffix14 = suffixBeforeMerkle ++ suffixMerkleAndTail := by
    rfl
  rw [hSplit] at h
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeMerkle_eq ls)] at h
  unfold suffixMerkleAndTail at h
  have hMerkle :
      execStmt [] (beforeMerkle ls)
          (.forEach "h" (u 11)
            (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")) =
        .continue (afterMerkle ls) := by
    simpa [afterMerkle, u] using
      (execStmt_forEach_merkleClimb
        "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 (beforeMerkle ls))
  rw [execStmtList_cons_continue _ _ _ _ hMerkle] at h
  simpa [afterMerkle] using h

/-- The accepting layer suffix does not rebind `"idxTree"`. -/
theorem suffix14_preserves_idxTree (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "idxTree" =
      lookupValue (afterDigit ls).bindings "idxTree" := by
  refine execStmtList_preserves_lookup "idxTree" suffix14
    (afterDigit ls) (stepLayer ls) ?_ (suffix14_continues ls)
  intro s s'' stmt hmem hexec
  simp [suffix14, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "idxTree" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "idxTree" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "idxTree" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "idxTree" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "idxTree" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "idxTree" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "idxTree" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "h" "idxTree" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [merkleClimbBody] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "sibling" "idxTree" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "idxTree" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "s" "idxTree" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "idxTree" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "merkleNode" "idxTree" _ (by decide) hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "mIdx" "idxTree" _ (by decide) hexec')
      hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "currentNode" "idxTree" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "sigOff" "idxTree" _ (by decide) hexec

/-- The accepting layer suffix does not rebind `"sigBase"`. -/
theorem suffix14_preserves_sigBase (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "sigBase" =
      lookupValue (afterDigit ls).bindings "sigBase" := by
  refine execStmtList_preserves_lookup "sigBase" suffix14
    (afterDigit ls) (stepLayer ls) ?_ (suffix14_continues ls)
  intro s s'' stmt hmem hexec
  simp [suffix14, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "sigBase" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [wotsOuterBody, mstoreE] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "digit" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "steps" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "val" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "sigBase" _ (by decide) hexec'
        · exact execStmt_forEach_preserves_lookup "step" "sigBase" _ _ _ _ (by decide)
            (by
              intro u u'' stmt'' hmem'' hexec''
              simp [wotsChainBody] at hmem''
              rcases hmem'' with rfl | rfl | rfl
              · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec''
              · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec''
              · exact execStmt_assignVar_preserves_lookup _ _ "val" "sigBase" _ (by decide) hexec'')
            hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [copyBody, mstoreE] at hmem'
        subst hmem'
        exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec')
      hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "sigBase" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "sigBase" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "h" "sigBase" _ _ _ _ (by decide)
      (by
        intro t t'' stmt' hmem' hexec'
        simp [merkleClimbBody] at hmem'
        rcases hmem' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact execStmt_letVar_preserves_lookup _ _ "sibling" "sigBase" _ (by decide) hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "sigBase" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec'
        · exact execStmt_letVar_preserves_lookup _ _ "s" "sigBase" _ (by decide) hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec'
        · exact execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "merkleNode" "sigBase" _ (by decide) hexec'
        · exact execStmt_assignVar_preserves_lookup _ _ "mIdx" "sigBase" _ (by decide) hexec')
      hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "currentNode" "sigBase" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "sigOff" "sigBase" _ (by decide) hexec

/-- One accepting layer iteration preserves selector/calldata from the incoming
guard state through the checksum prefix and layer suffix. -/
theorem stepLayer_preserves_selector_calldata (ls : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata ls (stepLayer ls) := by
  have hPrefix := afterDigit_preserves_selector_calldata ls
  have hSuffix :
      SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata
        (afterDigit ls) (stepLayer ls) :=
    SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
      suffix14 (afterDigit ls) (stepLayer ls)
      suffix14_preserves_selector_calldata (suffix14_continues ls)
  exact ⟨by rw [hSuffix.1, hPrefix.1], by rw [hSuffix.2, hPrefix.2]⟩

/-- One accepting layer iteration shifts the incoming `"idxTree"` by the C13
subtree height and carries that shifted value through the suffix. -/
theorem stepLayer_idxTree_eq_of_idxTree
    (ls : RuntimeState) (idxTree : Nat)
    (hIdxTree : lookupValue ls.bindings "idxTree" = idxTree)
    (hIdxTreeLt : idxTree < 2 ^ 256) :
    lookupValue (stepLayer ls).bindings "idxTree" = idxTree / 2048 := by
  rw [suffix14_preserves_idxTree]
  rw [afterDigit_preserves_lookup_of_ne ls "idxTree" (by decide) (by decide)]
  exact beforeDigitLoop_idxTree_eq_of_idxTree ls idxTree hIdxTree hIdxTreeLt

/-- One accepting layer iteration preserves the `"sigBase"` binding. -/
theorem stepLayer_sigBase_eq (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "sigBase" =
      lookupValue ls.bindings "sigBase" := by
  rw [suffix14_preserves_sigBase]
  rw [afterDigit_preserves_lookup_of_ne ls "sigBase" (by decide) (by decide)]
  rw [beforeDigitLoop_preserves_sigBase]

/-- The final two layer assignments do not rebind `"merkleNode"`.  This is the
cheap tail brick used by structural layer-suffix proofs without replaying the
whole WOTS/XMSS prefix. -/
theorem finalLayerTail_preserves_merkleNode (st : RuntimeState) :
    lookupValue
        (match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).bindings
        "merkleNode"
      = lookupValue st.bindings "merkleNode" := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne,
    ne_eq, String.reduceEq, not_false_eq_true]

/-- The final two layer assignments preserve scratch cell `0x00`. -/
theorem finalLayerTail_preserves_memory_zero (st : RuntimeState) :
    ((match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  rfl

/-- One accepting layer iteration preserves seed cell `0x00` once the WOTS,
copy, and Merkle loops are supplied as frame facts. -/
theorem stepLayer_preserves_memory_zero_of_loop_frames
    (ls : RuntimeState)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hMerkle :
      ∀ (s : RuntimeState),
        ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" s).world.memory
            0x00).val =
          (s.world.memory 0x00).val) :
    ((stepLayer ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  have hTail := finalLayerTail_preserves_memory_zero (afterMerkle ls)
  rw [finalLayerTail_continues_from_afterMerkle ls] at hTail
  rw [hTail]
  exact afterMerkle_preserves_memory_zero_of_loop_frames ls hWots hCopy hMerkle

/-- Range-gated variant of `stepLayer_preserves_memory_zero_of_loop_frames`.
The Merkle-step frame may depend on the concrete height bound to `"h"`. -/
theorem stepLayer_preserves_memory_zero_of_loop_frames_range
    (ls : RuntimeState) (D : Nat → Prop)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (u 43) copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hMerkle :
      ∀ (s : RuntimeState) (idx : Nat), D idx →
        ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
            0x00).val =
          (s.world.memory 0x00).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 11 → D i) :
    ((stepLayer ls).world.memory 0x00).val =
      ((afterDigit ls).world.memory 0x00).val := by
  have hTail := finalLayerTail_preserves_memory_zero (afterMerkle ls)
  rw [finalLayerTail_continues_from_afterMerkle ls] at hTail
  rw [hTail]
  exact afterMerkle_preserves_memory_zero_of_loop_frames_range
    ls D hWots hCopy hMerkle hD

/-- The final two layer assignments bind `"sigOff"` to `"authOff" + 176`. -/
theorem finalLayerTail_sigOff_eq_of_authOff
    (st : RuntimeState) (authOff : Nat)
    (hAuthOff : lookupValue st.bindings "authOff" = authOff)
    (hAuthOffLt : authOff < 2 ^ 256)
    (hSigOffLt : authOff + 176 < 2 ^ 256) :
    lookupValue
        (match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).bindings
        "sigOff"
      = authOff + 176 := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (assignVar_continue _ "sigOff" _ (authOff + 176) (by
        exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
          _ (v "authOff") (u 176) authOff 176
          (by
            change some (lookupValue (bindValue st.bindings "currentNode"
              (lookupValue st.bindings "merkleNode")) "authOff") = some authOff
            rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "authOff" _ (by decide)]
            rw [hAuthOff])
          rfl hAuthOffLt (by decide : 176 < 2 ^ 256) hSigOffLt))]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_self]

/-- Running the final layer tail from the folded Merkle state advances
`"sigOff"` to the next layer's signature offset. -/
theorem afterMerkleTail_sigOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256)
    (hNextSigOffLt : sigOff + 868 < 2 ^ 256) :
    lookupValue
        (match execStmtList [] (afterMerkle ls)
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => afterMerkle ls).bindings
        "sigOff" = sigOff + 868 := by
  have hAuth :
      lookupValue (afterMerkle ls).bindings "authOff" = sigOff + 692 :=
    afterMerkle_authOff_eq_of_sigOff
      ls sigOff hSigOff hSigOffLt hCountOffLt hAuthOffLt
  have hTail := finalLayerTail_sigOff_eq_of_authOff
    (afterMerkle ls) (sigOff + 692) hAuth hAuthOffLt
    (by
      have hSum : sigOff + 692 + 176 = sigOff + 868 := by omega
      simpa [hSum] using hNextSigOffLt)
  have hSum : sigOff + 692 + 176 = sigOff + 868 := by omega
  simpa [hSum] using hTail

/-- One accepting layer iteration advances `"sigOff"` past the WOTS count word
and XMSS auth path for that layer. -/
theorem stepLayer_sigOff_eq_of_sigOff
    (ls : RuntimeState) (sigOff : Nat)
    (hSigOff : lookupValue ls.bindings "sigOff" = sigOff)
    (hSigOffLt : sigOff < 2 ^ 256)
    (hCountOffLt : sigOff + 688 < 2 ^ 256)
    (hAuthOffLt : sigOff + 692 < 2 ^ 256)
    (hNextSigOffLt : sigOff + 868 < 2 ^ 256) :
    lookupValue (stepLayer ls).bindings "sigOff" = sigOff + 868 := by
  have hTail := afterMerkleTail_sigOff_eq_of_sigOff
    ls sigOff hSigOff hSigOffLt hCountOffLt hAuthOffLt hNextSigOffLt
  rw [finalLayerTail_continues_from_afterMerkle ls] at hTail
  exact hTail

set_option maxHeartbeats 4000000 in
/-- **`stepLayer_currentNode_eq_merkleNode`** — structural identification of the
*left* operand of the final `currentNode == root` compare.  The last two statements
of `suffix14` are `currentNode := merkleNode; sigOff := …`; neither reassigns
`merkleNode`, so in the post-iteration state the `"currentNode"` binding equals the
`"merkleNode"` binding — the output of the Merkle-climb `forEach "h"` loop.  This
pins the compare's left operand to the climb result *structurally*, without
evaluating any keccak (the climbed value is carried as an opaque bound term, peeled
by key only).  It is the first Phase-3b sub-brick on the open (left-operand) half:
the remaining obligation is to identify that climbed `merkleNode` value with the
abstract spec's `foldHypertree`/`xmssRootFromSig` root — the genuine keccak data
correspondence. -/
theorem stepLayer_currentNode_eq_merkleNode (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "currentNode"
      = lookupValue (stepLayer ls).bindings "merkleNode" := by
  unfold stepLayer suffix14 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 _)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne, MemoryKit.lookupValue_bindValue_self,
    ne_eq, String.reduceEq, not_false_eq_true]

/-! ## 5. The guarded layer-body step lemma. -/

/-- The per-iteration guard: the checksum condition resolves to `0`
(`digitSum = 208`), i.e. the layer body does *not* revert. -/
def layerGuard (ls : RuntimeState) : Bool :=
  evalExpr [] (afterDigit ls) condE == some 0

/-- If the guard-free prefix's accumulated checksum binding is the C13 target
`208`, the executable layer guard passes.  This is a small public bridge from the
data-cell fact callers naturally prove (`"digitSum"` after `prefix11`) to the
guard predicate consumed by the guarded loop engine. -/
theorem layerGuard_of_afterDigit_digitSum_eq
    (ls : RuntimeState)
    (hDigit : lookupValue (afterDigit ls).bindings "digitSum" = 208) :
    layerGuard ls = true := by
  have hEq :
      evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208)) = some 1 := by
    unfold eqE v u
    show (do
      let lhs ← some (lookupValue (afterDigit ls).bindings "digitSum")
      let rhs ← some (wordNormalize 208)
      pure (boolWord (decide (lhs = rhs)))) = some 1
    rw [hDigit]
    rfl
  have hCond : evalExpr [] (afterDigit ls) condE = some 0 := by
    unfold condE notE
    show (do
      let value ← evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208))
      pure (boolWord (decide (value = 0)))) = some 0
    rw [hEq]
    rfl
  unfold layerGuard
  rw [hCond]
  rfl

/-- If the guard-free prefix's accumulated checksum binding is not the C13
target `208`, the executable layer guard fails. -/
theorem layerGuard_of_afterDigit_digitSum_ne
    (ls : RuntimeState)
    (hDigit : lookupValue (afterDigit ls).bindings "digitSum" ≠ 208) :
    layerGuard ls = false := by
  have hEq :
      evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208)) = some 0 := by
    unfold eqE v u
    have hNorm : wordNormalize 208 = 208 := by rfl
    change
      some (boolWord
        (decide (lookupValue (afterDigit ls).bindings "digitSum" = wordNormalize 208)))
        = some 0
    rw [hNorm]
    have hDec : decide (lookupValue (afterDigit ls).bindings "digitSum" = 208) = false := by
      exact decide_eq_false hDigit
    rw [hDec]
    rfl
  have hCond : evalExpr [] (afterDigit ls) condE = some 1 := by
    unfold condE notE
    show (do
      let value ← evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208))
      pure (boolWord (decide (value = 0)))) = some 1
    rw [hEq]
    rfl
  unfold layerGuard
  rw [hCond]
  rfl

/-- The checksum-guard `ite` (then = `revert0`, else = `[]`): continues with the
same state when its condition resolves to `0`, reverts otherwise. -/
private theorem ite_revert0_branch (st : RuntimeState) (cond : Expr) :
    execStmt [] st (.ite cond revert0 []) =
      match evalExpr [] st cond with
      | some r => if r != 0 then .revert else .continue st
      | none => .revert := by
  show (match evalExpr [] st cond with
        | some resolved =>
            if resolved != 0 then execStmtList [] st revert0 else execStmtList [] st []
        | none => .revert) = _
  cases evalExpr [] st cond with
  | none => rfl
  | some r => cases hr : r != 0 <;> simp only [hr, Bool.false_eq_true, if_true, if_false] <;> rfl

/-- **`execLayerBody`** — the guarded layer body: continues to `stepLayer ls`
when the checksum guard passes, reverts otherwise.  This is the `hstep`
hypothesis consumed by `ClimbLoopGuarded.execForEachLoop_of_guarded_step`. -/
theorem execLayerBody (ls : RuntimeState) :
    execStmtList [] ls layerBody
      = if layerGuard ls then .continue (stepLayer ls) else .revert := by
  unfold layerBody
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (afterDigit_eq ls)]
  rw [execStmtList_cons_eq, ite_revert0_branch]
  unfold layerGuard
  cases hc : evalExpr [] (afterDigit ls) condE with
  | none => rfl
  | some r =>
      by_cases hr : r = 0
      · subst hr
        simp only [bne_self_eq_false, beq_self_eq_true, reduceIte]
        exact suffix14_continues ls
      · have hb : (r != 0) = true := by simp [hr]
        have hb2 : (some r == some (0 : Nat)) = false := by simp [hr]
        simp only [hb, hb2]; rfl

/-! ## 6. The full guarded layer-loop fold. -/

/-- **`execLayerLoop`** — given that every threaded layer iteration's checksum
guard passes (`allGuardsPass`), the whole `forEach "layer" (u 2)` statement folds
to the pure `foldLoop` over `stepLayer`, exactly as the unguarded engine. -/
theorem execLayerLoop (state : RuntimeState)
    (hguards : ClimbLoopGuarded.allGuardsPass "layer" stepLayer layerGuard
        { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0 (wordNormalize 2)) :
    execStmt [] state layerStmt
      = .continue
          (foldLoop "layer" stepLayer
            { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) }
            0 (wordNormalize 2)) :=
  ClimbLoopGuarded.execStmt_forEach_of_guarded_step "layer" (u 2) layerBody state (wordNormalize 2)
    stepLayer layerGuard rfl execLayerBody hguards

/-- The C13 two-layer climb loop reverts immediately when the first WOTS+C
checksum guard fails. -/
theorem execLayerLoop_reverts_on_first_guard
    (state : RuntimeState)
    (hguard :
      layerGuard
        (ClimbLoopGuarded.loopState "layer"
          { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0)
        = false) :
    execStmt [] state layerStmt = .revert := by
  exact
    ClimbLoopGuarded.execStmt_forEach_revert_on_first_guard
      "layer" (u 2) layerBody state (wordNormalize 2)
      stepLayer layerGuard rfl
      1
      (SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256))
      execLayerBody hguard

/-- The C13 two-layer climb loop reverts on the second iteration when the first
WOTS+C checksum guard passes but the second one fails after the first
`stepLayer`. -/
theorem execLayerLoop_reverts_on_second_guard
    (state : RuntimeState)
    (hguard0 :
      layerGuard
        (ClimbLoopGuarded.loopState "layer"
          { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0)
        = true)
    (hguard1 :
      layerGuard
        (ClimbLoopGuarded.loopState "layer"
          (stepLayer
            (ClimbLoopGuarded.loopState "layer"
              { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0))
          1)
        = false) :
    execStmt [] state layerStmt = .revert := by
  exact
    ClimbLoopGuarded.execStmt_forEach_revert_on_second_guard
      "layer" (u 2) layerBody state (wordNormalize 2)
      stepLayer layerGuard rfl
      0
      (SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256))
      execLayerBody hguard0 hguard1

/-! ## 7. Axiom audit. -/

#print axioms layerStmt_eq_slice
#print axioms digitSumStep_digitSum_expr
#print axioms digitSumStep_preserves_lookup_of_ne
#print axioms nat_land_low3
#print axioms nat_land_low11
#print axioms digitSumStep_digitSum_eq_add_digit
#print axioms afterDigitFold_preserves_lookup_of_ne
#print axioms beforeDigitLoop_eq
#print axioms beforeDigitLoop_preserves_sigBase
#print axioms beforeDigitLoop_preserves_layer
#print axioms beforeDigitLoop_countOff_eq_of_sigOff
#print axioms beforeDigest_eq
#print axioms beforeDigest_preserves_memory_zero
#print axioms beforeDigitLoop_preserves_memory_zero
#print axioms afterDigitFold_preserves_memory_zero
#print axioms afterDigit_preserves_memory_zero
#print axioms stepWots_preserves_lookup_of_ne
#print axioms stepWots_preserves_memory_zero
#print axioms wotsChainFold_preserves_memory_zero
#print axioms wotsChainFold_preserves_i_lookup
#print axioms wotsChainFold_val_eq_chainHash
#print axioms wotsOuterPrefix_preserves_memory_zero
#print axioms wotsOuterPrefix_preserves_i_lookup
#print axioms wotsOuterPrefix_preserves_source_slot
#print axioms wotsOuterTail_mstore_mem_at_i
#print axioms wotsOuterDigit_le_seven
#print axioms wotsOuter_chainTail_mem_at_i
#print axioms wotsOuterStep_mem_at_i_via_prefix4
#print axioms wotsOuterStep_mem_at_i_eq
#print axioms wotsOuterStep_mem_at_i_eq_wotsChainEnd
#print axioms wotsOuterBody_preserves_memory_zero_of_i
#print axioms wotsOuterStep_preserves_memory_zero_of_i
#print axioms wotsOuterBody_preserves_i_lookup
#print axioms wotsOuterStep_preserves_i_lookup
#print axioms wotsOuterFold_preserves_memory_zero
#print axioms wotsOuterForEach_preserves_memory_zero
#print axioms wotsOuterBody_preserves_source_slot_of_ne
#print axioms wotsOuterStep_preserves_source_slot_of_ne
#print axioms wotsOuterStep_preserves_past_source_slot
#print axioms wotsOuterStep_mem_at_i_eq_wotsChainsEnd_cell
#print axioms wotsOuterFold43_source_cells_eq_wotsChainsEnd
#print axioms copyStep_preserves_memory_zero_of_i
#print axioms copyFold_preserves_memory_zero
#print axioms copyForEach_preserves_memory_zero
#print axioms copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
#print axioms beforeDigest_idxLeaf_eq_of_idxTree
#print axioms beforeDigest_idxTree_eq_of_idxTree
#print axioms beforeDigitLoop_idxTree_eq_of_idxTree
#print axioms beforeDigitLoop_idxLeaf_eq_of_idxTree
#print axioms afterDigit_idxLeaf_eq_of_idxTree
#print axioms beforeDigest_wotsAdrs_eq_of_layer_idxTree
#print axioms beforeDigest_count_eq_of_sigBase_sigOff_calldata
#print axioms beforeDigest_memory_0x20_eq_of_wotsAdrs
#print axioms beforeDigest_memory_0x40_eq_currentNode
#print axioms beforeDigest_memory_0x40_eq_wordOfHash16
#print axioms beforeDigest_memory_0x60_eq_of_count
#print axioms beforeDigitLoop_d_eq_keccakWords
#print axioms beforeDigitLoop_d_eq_wotsDigest_of_scratch
#print axioms afterDigit_preserves_selector_calldata
#print axioms digitSumBody_preserves_selector_calldata
#print axioms wotsChainBody_preserves_selector_calldata
#print axioms copyBody_preserves_selector_calldata
#print axioms merkleClimbBody_preserves_selector_calldata
#print axioms wotsOuterBody_preserves_selector_calldata
#print axioms suffix14_preserves_selector_calldata
#print axioms suffix14_preserves_idxTree
#print axioms suffix14_preserves_sigBase
#print axioms prefix11_eq_afterDigitFold
#print axioms afterDigit_eq_afterDigitFold
#print axioms afterDigit_digitSum_eq_afterDigitFold
#print axioms afterDigit_preserves_lookup_of_ne
#print axioms afterDigitFold_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
#print axioms afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
#print axioms layerGuard_of_afterDigit_digitSum_eq
#print axioms layerGuard_of_afterDigit_digitSum_ne
#print axioms beforeAuthOff_eq
#print axioms beforeAuthOff_preserves_memory_zero_of_loop_frames
#print axioms suffixBeforeAuthOff_preserves_countOff
#print axioms suffixBeforeAuthOff_preserves_idxLeaf
#print axioms suffixBeforeAuthOff_preserves_sigBase
#print axioms suffixBeforeAuthOff_preserves_idxTree
#print axioms suffixBeforeAuthOff_preserves_layer
#print axioms beforeAuthOff_countOff_eq_of_sigOff
#print axioms beforeAuthOff_idxLeaf_eq_of_idxTree
#print axioms beforeAuthOff_idxTree_eq_of_idxTree
#print axioms beforeAuthOff_layer_eq
#print axioms beforeMerkle_eq
#print axioms beforeMIdx_eq
#print axioms beforeMIdx_idxLeaf_eq_of_idxTree
#print axioms beforeMIdx_treeAdrs_eq_of_layer_idxTree
#print axioms beforeMerkle_mIdx_eq_of_idxTree
#print axioms beforeMerkle_treeAdrs_eq_of_layer_idxTree
#print axioms beforeMerkle_preserves_memory_zero_of_loop_frames
#print axioms suffixBeforeMerkle_preserves_selector_calldata
#print axioms beforeMerkle_preserves_selector_calldata
#print axioms suffixBeforeMerkle_preserves_countOff
#print axioms beforeMerkle_countOff_eq_of_sigOff
#print axioms beforeMerkle_authOff_eq_of_sigOff
#print axioms beforeMerkle_merklePtr_eq_of_sigBase_sigOff
#print axioms merkleStep_preserves_authOff
#print axioms afterMerkle_authOff_eq_of_sigOff
#print axioms afterMerkle_preserves_memory_zero_of_loop_frames
#print axioms afterMerkle_preserves_memory_zero_of_loop_frames_range
#print axioms finalLayerTail_continues_from_afterMerkle
#print axioms stepLayer_sigOff_eq_of_sigOff
#print axioms stepLayer_preserves_selector_calldata
#print axioms stepLayer_idxTree_eq_of_idxTree
#print axioms stepLayer_sigBase_eq
#print axioms finalLayerTail_preserves_merkleNode
#print axioms finalLayerTail_preserves_memory_zero
#print axioms stepLayer_preserves_memory_zero_of_loop_frames
#print axioms stepLayer_preserves_memory_zero_of_loop_frames_range
#print axioms finalLayerTail_sigOff_eq_of_authOff
#print axioms afterMerkleTail_sigOff_eq_of_sigOff
#print axioms execLayerBody
#print axioms execLayerLoop
#print axioms execLayerLoop_reverts_on_first_guard
#print axioms execLayerLoop_reverts_on_second_guard
#print axioms stepLayer_currentNode_eq_merkleNode

end SphincsMinusVerifiers.SegmentLayer3
