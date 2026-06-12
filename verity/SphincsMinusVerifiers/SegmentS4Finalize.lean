/-
  SegmentS4Finalize — the FORS finalize block (statements 15..21 of
  `c13VerifyBody`), run after the FORS outer loop (`SegmentS4Fors.execForsOuter`)
  and before the climb seed (`SegmentSeed.execSegmentSeed`).

  Per `INTERFACE_CONTRACT.md` (the S4b/S4c rows), these seven statements are:

  ```
  15  letVar "lastSecret"  := and (cdload (sigBase + 16 + (4<<6))) N_MASK
  16  mstore 0x20          := (96<<3) | (64<<6)        -- FORS_TREE adrs, 7th leaf
  17  mstore 0x40          := lastSecret
  18  mstore 0x140         := and (keccak 0x00 0x60) N_MASK   -- forced-zero leaf
  19  mstore 0x20          := 96<<4                     -- FORS_ROOTS adrs
  20  forEach "i" (u 7)    [ mstore (0x40 + 32*i) := mload (0x80 + 32*i) ]
  21  letVar "forsPk"      := and (keccak 0x00 0x120) N_MASK  -- 7-root compress
  ```

  Statement 20 is the root-compression copy loop; it threads through
  `ClimbLoop.execStmt_forEach_of_step` exactly as the FORS / hypertree climbs do,
  with a one-statement `mstore` body (`forsCopyBody`).  Everything else is a
  `letVar` / `mstore` that continues unconditionally, so the whole block reduces
  to a single pure transformer `forsFinalizeStep`.

  Faithfulness is machine-checked: `forsFinalizeBody_eq_slice` (`rfl`) shows the
  reconstructed seven statements are exactly statements 15..21 of the real
  `c13VerifyBody`.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.InitialNodeKeccak
import SphincsMinusVerifiers.Model
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentS4Finalize

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK)
open SphincsMinusVerifiers.ClimbLoop (foldLoop)
open SphincsMinusVerifierSpec.C13Concrete (adrsForsRoots adrsForsLeaf maskN keccakWords)

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

/-! ## 1. The root-compression copy loop body (statement 20's body). -/

/-- The body of `forEach "i" (u 7)`: copy FORS root slot `0x80 + 32*i` into the
compression slot `0x40 + 32*i`.  A single total `mstore`. -/
def forsCopyBody : List Stmt :=
  [ mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) ]

/-- Case eliminator for membership in `forsCopyBody`.

Downstream frame files use this instead of unfolding `forsCopyBody`, so the
generated equation theorem for this definition is owned by this module. -/
theorem forsCopyBody_mem_cases {P : Stmt → Prop} {stmt : Stmt}
    (hmem : stmt ∈ forsCopyBody)
    (hstore :
      P (mstoreE (addE (u 0x40) (shlE (u 5) (v "i")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))))) :
    P stmt := by
  simp only [forsCopyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact hstore

/-- The pure transformer for one copy-loop iteration. -/
def forsCopyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsCopyBody with
  | .continue s' => s'
  | _ => st

open SphincsMinusVerifiers.ClimbKit (execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmt_letVar_continue)

private theorem idxNorm (idx : Nat) (hidx : idx < 7) :
    wordNormalize idx = idx := by
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt (lt_trans hidx (by decide))

private theorem idxShl5_lt (idx : Nat) (hidx : idx < 7) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  calc idx * 2 ^ 5 ≤ 6 * 2 ^ 5 :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
    _ < 2 ^ 256 := by decide

private theorem addIdxShl5_lt (base idx : Nat) (hbase : base ≤ 0x80) (hidx : idx < 7) :
    base + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : base + idx * 2 ^ 5 ≤ 128 + 6 * 2 ^ 5 :=
    Nat.add_le_add hbase (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx))
  exact lt_of_le_of_lt hle (by decide)

private theorem evalExpr_bitAnd_result_lt
    {st : RuntimeState} {e : Expr} {m r : Nat}
    (h : evalExpr [] st (.bitAnd e (.literal m)) = some r) :
    r < Verity.Core.Uint256.modulus := by
  change (do
        let lhs ← evalExpr [] st e
        let rhs ← evalExpr [] st (.literal m)
        pure (Verity.Core.Uint256.and lhs rhs).val) = some r at h
  cases he : evalExpr [] st e with
  | none =>
      simp [he] at h
  | some lhs =>
      cases hm : evalExpr [] st (.literal m) with
      | none =>
          simp [he, hm] at h
      | some rhs =>
          simp [he, hm] at h
          subst r
          exact (Verity.Core.Uint256.and lhs rhs).isLt

private theorem evalCopyOffset (s : RuntimeState) (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 7) :
    evalExpr [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      (addE (u base) (shlE (u 5) (v "i"))) = some (base + 32 * idx) := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have h5 : evalExpr [] st (u 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hi : evalExpr [] st (v "i") = some idx := by
    show some (lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i") = some idx
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self, idxNorm idx hidx]
  have hsh : evalExpr [] st (shlE (u 5) (v "i")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded st (u 5) (v "i")
      5 idx h5 hi (by decide) (lt_trans hidx (by decide)) (idxShl5_lt idx hidx)
  have hbaseLit : evalExpr [] st (u base) = some base := by
    show some (wordNormalize base) = some base
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_of_le_of_lt hbase (by decide))]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded st (u base)
    (shlE (u 5) (v "i")) base (idx <<< 5) hbaseLit hsh
    (lt_of_le_of_lt hbase (by decide)) (idxShl5_lt idx hidx)
    (addIdxShl5_lt base idx hbase hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

/-- Running the copy-loop body continues to `forsCopyStep st` (the single
`mstore` reads a memory cell and writes another — both total). -/
theorem execForsCopy (st : RuntimeState) :
    execStmtList [] st forsCopyBody = .continue (forsCopyStep st) := by
  unfold forsCopyStep forsCopyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- One copy-loop iteration writes compression slot `0x40 + 32*i` from the
corresponding FORS-root slot `0x80 + 32*i`, for the concrete loop-index state.
This is the local memory-frame brick needed to fold the seven-copy loop into the
`forsPk` compression preimage. -/
theorem forsCopyStep_copied (s : RuntimeState) (idx : Nat) (hidx : idx < 7) :
    ((forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x40 + 32 * idx)).val
      = (s.world.memory (0x80 + 32 * idx)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i")))
      = some (0x40 + 32 * idx) :=
    evalCopyOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
      = some (0x80 + 32 * idx) :=
    evalCopyOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      = some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold forsCopyStep forsCopyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (SphincsMinusVerifiers.MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x40 + 32 * idx)).val
    = (s.world.memory (0x80 + 32 * idx)).val
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_val_same]
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt (s.world.memory (0x80 + 32 * idx)).isLt

/-- A copy-loop iteration only writes its own compression slot.  Any other
compression slot `0x40 + 32*j` is framed through unchanged. -/
theorem forsCopyStep_preserves_copy_slot
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 7) (hne : j ≠ idx) :
    ((forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x40 + 32 * j)).val
      = (s.world.memory (0x40 + 32 * j)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i")))
      = some (0x40 + 32 * idx) :=
    evalCopyOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
      = some (0x80 + 32 * idx) :=
    evalCopyOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      = some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold forsCopyStep forsCopyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (SphincsMinusVerifiers.MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x40 + 32 * j)).val
    = (s.world.memory (0x40 + 32 * j)).val
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- A copy-loop iteration preserves any root-source slot `0x80 + 32*j` that it
has not reached yet (`idx < j`).  This is the overlap-safe frame fact for the
copy loop: destination `idx` aliases source `idx-2`, never a future source. -/
theorem forsCopyStep_preserves_future_source_slot
    (s : RuntimeState) (idx j : Nat) (hidx : idx < 7) (hlt : idx < j) :
    ((forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i")))
      = some (0x40 + 32 * idx) :=
    evalCopyOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
      = some (0x80 + 32 * idx) :=
    evalCopyOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      = some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold forsCopyStep forsCopyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (SphincsMinusVerifiers.MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val (0x80 + 32 * j)).val
    = (s.world.memory (0x80 + 32 * j)).val
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- A copy-loop iteration preserves any low scratch slot below `0x40`; the loop
only writes `0x40 + 32*i`.  This covers the seed cell `0x00` and the address
cell `0x20` used by the final FORS public-key compression. -/
theorem forsCopyStep_preserves_low_slot
    (s : RuntimeState) (idx addr : Nat) (hidx : idx < 7) (haddr : addr < 0x40) :
    ((forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
        addr).val
      = (s.world.memory addr).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "i")))
      = some (0x40 + 32 * idx) :=
    evalCopyOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
      = some (0x80 + 32 * idx) :=
    evalCopyOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      = some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "i"))) (0x80 + 32 * idx) hsrc
  unfold forsCopyStep forsCopyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st (addE (u 0x40) (shlE (u 5) (v "i")))
      (mloadE (addE (u 0x80) (shlE (u 5) (v "i"))))
      (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val hoff hval)]
  show (SphincsMinusVerifiers.MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val addr).val
    = (s.world.memory addr).val
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

/-- Later copy-loop iterations preserve copy slots that were already written
before the current loop index. -/
theorem forsCopyLoop_preserves_past_copy_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      j < idx →
      idx + remaining ≤ 7 →
      ((foldLoop "i" forsCopyStep s idx remaining).world.memory (0x40 + 32 * j)).val
        = (s.world.memory (0x40 + 32 * j)).val
  | s, idx, 0, j, _, _ => by
      rw [ClimbLoop.foldLoop_zero]
  | s, idx, remaining + 1, j, hj, hbound => by
      have hidx : idx < 7 := by omega
      let s1 : RuntimeState :=
        forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      change ((foldLoop "i" forsCopyStep s1 (idx + 1) remaining).world.memory
          (0x40 + 32 * j)).val = (s.world.memory (0x40 + 32 * j)).val
      rw [forsCopyLoop_preserves_past_copy_slot s1 (idx + 1) remaining j (by omega) (by omega)]
      exact forsCopyStep_preserves_copy_slot s idx j hidx (by omega)

/-- Copy-loop iterations before `j` preserve source slot `0x80 + 32*j`.
This handles the overlap between the copy-loop destination and source ranges:
the source for slot `j` can only be overwritten by a later destination `j + 2`,
so it is intact when iteration `j` reads it. -/
theorem forsCopyLoop_preserves_future_source_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      idx + remaining ≤ j →
      j < 7 →
      ((foldLoop "i" forsCopyStep s idx remaining).world.memory (0x80 + 32 * j)).val
        = (s.world.memory (0x80 + 32 * j)).val
  | s, idx, 0, j, _, _ => by
      rw [ClimbLoop.foldLoop_zero]
  | s, idx, remaining + 1, j, hfuture, hj => by
      have hidx : idx < 7 := by omega
      let s1 : RuntimeState :=
        forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      change ((foldLoop "i" forsCopyStep s1 (idx + 1) remaining).world.memory
          (0x80 + 32 * j)).val = (s.world.memory (0x80 + 32 * j)).val
      rw [forsCopyLoop_preserves_future_source_slot s1 (idx + 1) remaining j (by omega) hj]
      exact forsCopyStep_preserves_future_source_slot s idx j hidx (by omega)

/-- Whole-copy-loop slot correspondence: if `j` lies in the loop range, the
final compression slot `0x40 + 32*j` contains the source word originally at
`0x80 + 32*j`. -/
theorem forsCopyLoop_copied_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      idx ≤ j →
      j < idx + remaining →
      idx + remaining ≤ 7 →
      ((foldLoop "i" forsCopyStep s idx remaining).world.memory (0x40 + 32 * j)).val
        = (s.world.memory (0x80 + 32 * j)).val
  | _, _, 0, _, _, hj, _ => by omega
  | s, idx, remaining + 1, j, hle, hlt, hbound => by
      have hidx : idx < 7 := by omega
      let s1 : RuntimeState :=
        forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      by_cases hji : j = idx
      · change ((foldLoop "i" forsCopyStep s1 (idx + 1) remaining).world.memory
            (0x40 + 32 * j)).val = (s.world.memory (0x80 + 32 * j)).val
        rw [forsCopyLoop_preserves_past_copy_slot s1 (idx + 1) remaining j (by omega) (by omega)]
        simpa [hji] using forsCopyStep_copied s idx hidx
      · have hgt : idx < j := by omega
        change ((foldLoop "i" forsCopyStep s1 (idx + 1) remaining).world.memory
            (0x40 + 32 * j)).val = (s.world.memory (0x80 + 32 * j)).val
        rw [forsCopyLoop_copied_slot s1 (idx + 1) remaining j (by omega) (by omega) (by omega)]
        exact forsCopyStep_preserves_future_source_slot s idx j hidx hgt

/-- The concrete seven-iteration copy loop used by S4 finalize: every
compression slot `0x40 + 32*j`, `j < 7`, contains the corresponding original
FORS-root slot `0x80 + 32*j`. -/
theorem forsCopyLoop7_copied_slot (s : RuntimeState) (j : Nat) (hj : j < 7) :
    ((foldLoop "i" forsCopyStep s 0 7).world.memory (0x40 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val :=
  forsCopyLoop_copied_slot s 0 7 j (by omega) (by omega) (by omega)

/-- The concrete seven-iteration copy loop preserves low scratch slots below
`0x40`, in particular `0x00` and `0x20`. -/
theorem forsCopyLoop7_preserves_low_slot
    (s : RuntimeState) (addr : Nat) (haddr : addr < 0x40) :
    ((foldLoop "i" forsCopyStep s 0 7).world.memory addr).val
      = (s.world.memory addr).val := by
  have h :
      ∀ (idx remaining : Nat) (s : RuntimeState),
        idx + remaining ≤ 7 →
        ((foldLoop "i" forsCopyStep s idx remaining).world.memory addr).val
          = (s.world.memory addr).val := by
    intro idx remaining
    induction remaining generalizing idx with
    | zero =>
        intro s hbound
        rw [ClimbLoop.foldLoop_zero]
    | succ remaining ih =>
        intro s hbound
        have hidx : idx < 7 := by omega
        let s1 : RuntimeState :=
          forsCopyStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
        rw [ClimbLoop.foldLoop_succ]
        change ((foldLoop "i" forsCopyStep s1 (idx + 1) remaining).world.memory addr).val
          = (s.world.memory addr).val
        rw [ih (idx + 1) s1 (by omega)]
        exact forsCopyStep_preserves_low_slot s idx addr hidx haddr
  exact h 0 7 s (by omega)

/-! ## 2. The full FORS finalize block (statements 15..21). -/

/-- Statements 15..21 of `c13VerifyBody`: the forced-zero 7th FORS leaf, the
root-compression copy loop, and the `forsPk` compression keccak. -/
def forsFinalizeBody : List Stmt :=
  [ .letVar "lastSecret" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6))))) (u N_MASK))
  , mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6)))
  , mstore 0x40 (v "lastSecret")
  , mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK))
  , mstore 0x20 (orE (shlE (u 128) (v "idxTree0")) (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0"))))
  , .forEach "i" (u 7) forsCopyBody
  , .letVar "forsPk" (andE (keccak 0x00 0x120) (u N_MASK)) ]

/-- Case eliminator for membership in `forsFinalizeBody`.

Keeping the list decomposition in this module prevents multiple downstream
modules from generating duplicate imported equation theorems for
`forsFinalizeBody`. -/
theorem forsFinalizeBody_mem_cases {P : Stmt → Prop} {stmt : Stmt}
    (hmem : stmt ∈ forsFinalizeBody)
    (hlastSecret :
      P (.letVar "lastSecret"
        (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6)))))
          (u N_MASK))))
    (hadrsLeaf :
      P (mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6)))))
    (hlastSecretStore : P (mstore 0x40 (v "lastSecret")))
    (hforcedRoot : P (mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK))))
    (hadrsRoots : P (mstore 0x20 (orE (shlE (u 128) (v "idxTree0")) (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0"))))))
    (hcopy : P (.forEach "i" (u 7) forsCopyBody))
    (hforsPk : P (.letVar "forsPk" (andE (keccak 0x00 0x120) (u N_MASK)))) :
    P stmt := by
  simp only [forsFinalizeBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlastSecret
  · exact hadrsLeaf
  · exact hlastSecretStore
  · exact hforcedRoot
  · exact hadrsRoots
  · exact hcopy
  · exact hforsPk

/-- The finalize prefix before statement 21 (`forsPk := masked keccak`).  This
materialises the exact state whose memory is compressed into the FORS public key. -/
def forsFinalizePrePkBody : List Stmt :=
  [ .letVar "lastSecret" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6))))) (u N_MASK))
  , mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6)))
  , mstore 0x40 (v "lastSecret")
  , mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK))
  , mstore 0x20 (orE (shlE (u 128) (v "idxTree0")) (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0"))))
  , .forEach "i" (u 7) forsCopyBody ]

/-- The finalize prefix before statement 20's copy loop.  This is the state whose
`0x80 + 32*i` root slots are copied into the final compression preimage. -/
def forsFinalizePreCopyBody : List Stmt :=
  [ .letVar "lastSecret" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6))))) (u N_MASK))
  , mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6)))
  , mstore 0x40 (v "lastSecret")
  , mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK))
  , mstore 0x20 (orE (shlE (u 128) (v "idxTree0")) (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0")))) ]

/-- Faithfulness: `forsFinalizeBody` is *exactly* statements 15..21 of
`c13VerifyBody` (the FORS finalize block, copy loop included). -/
theorem forsFinalizeBody_eq_slice :
    forsFinalizeBody = (c13VerifyBodyTail.drop 17).take 7 := rfl

/-! ## 4. The finalize-block step lemma. -/

/-- The pure transformer for the FORS finalize block: the `.continue` payload of
running `forsFinalizeBody`.  Total because every statement is a
`letVar`/`mstore`/total-`forEach` (the copy loop cannot revert). -/
def forsFinalizeStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsFinalizeBody with
  | .continue s' => s'
  | _ => st

/-- The pure transformer for the prefix before the final `forsPk` binding. -/
def forsFinalizePrePkStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsFinalizePrePkBody with
  | .continue s' => s'
  | _ => st

/-- The pure transformer for the prefix before the copy loop. -/
def forsFinalizePreCopyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsFinalizePreCopyBody with
  | .continue s' => s'
  | _ => st

/-- The final expression that binds `"forsPk"`: masked keccak over bytes
`[0x00, 0x120)`, evaluated in the pre-`forsPk` state. -/
def forsPkExpr : Expr := andE (keccak 0x00 0x120) (u N_MASK)

/-- The finalize block is the pre-compression prefix followed by the single
`forsPk` binding. -/
theorem forsFinalizeBody_eq_prePk_append :
    forsFinalizeBody = forsFinalizePrePkBody ++ [(.letVar "forsPk" forsPkExpr : Stmt)] := rfl

/-- The pre-`forsPk` prefix is the pre-copy straight-line prefix followed by the
single copy-loop statement. -/
theorem forsFinalizePrePkBody_eq_preCopy_append :
    forsFinalizePrePkBody = forsFinalizePreCopyBody ++ [(.forEach "i" (u 7) forsCopyBody : Stmt)] := rfl

open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_of_step)

set_option maxHeartbeats 4000000 in
/-- Running the finalize prefix before the copy loop continues to
`forsFinalizePreCopyStep st`. -/
theorem execForsFinalizePreCopy (st : RuntimeState) :
    execStmtList [] st forsFinalizePreCopyBody = .continue (forsFinalizePreCopyStep st) := by
  unfold forsFinalizePreCopyStep forsFinalizePreCopyBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

set_option maxHeartbeats 4000000 in
/-- The pre-copy finalize prefix does not touch the seed cell `0x00`. -/
theorem forsFinalizePreCopyStep_seed_slot (st : RuntimeState) :
    ((forsFinalizePreCopyStep st).world.memory 0).val = (st.world.memory 0).val := by
  unfold forsFinalizePreCopyStep forsFinalizePreCopyBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp [execStmtList, MemoryKit.memUpdate, Compiler.Constants.evmModulus]

set_option maxHeartbeats 4000000 in
/-- For the six ordinary FORS roots, the pre-copy finalize prefix preserves the
source slots `0x80 + 32*j`.  The seventh source slot is special: `j = 6` is
`0x140`, overwritten by the forced-zero leaf hash immediately before the copy
loop. -/
theorem forsFinalizePreCopyStep_preserves_root_source_slot
    (st : RuntimeState) (j : Nat) (hj : j < 6) :
    ((forsFinalizePreCopyStep st).world.memory (0x80 + 32 * j)).val
      = (st.world.memory (0x80 + 32 * j)).val := by
  unfold forsFinalizePreCopyStep forsFinalizePreCopyBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  have hne32 : 0x80 + 32 * j ≠ 0x20 := by omega
  have hne64 : 0x80 + 32 * j ≠ 0x40 := by omega
  have hne320 : 0x80 + 32 * j ≠ 0x140 := by omega
  simp [execStmtList, MemoryKit.memUpdate, Compiler.Constants.evmModulus,
    hne32, hne64, hne320]

private theorem shl128_lt_of_lt11 (x : Nat) (h : x < 2 ^ 11) :
    x <<< 128 < 2 ^ 256 := by
  have h11 : x ≤ 2047 := by
    rw [show (2 : Nat) ^ 11 = 2048 from by norm_num] at h
    omega
  rw [Nat.shiftLeft_eq]
  calc
    x * 2 ^ 128 ≤ 2047 * 2 ^ 128 := Nat.mul_le_mul_right _ h11
    _ < 2 ^ 256 := by norm_num

private theorem shl64_lt_of_lt11 (x : Nat) (h : x < 2 ^ 11) :
    x <<< 64 < 2 ^ 256 := by
  have h11 : x ≤ 2047 := by
    rw [show (2 : Nat) ^ 11 = 2048 from by norm_num] at h
    omega
  rw [Nat.shiftLeft_eq]
  calc
    x * 2 ^ 64 ≤ 2047 * 2 ^ 64 := Nat.mul_le_mul_right _ h11
    _ < 2 ^ 256 := by norm_num

set_option maxHeartbeats 4000000 in
/-- The pre-copy finalize prefix leaves the final FORS-roots address word in
scratch slot `0x20`, exactly the address preimage used by the `forsPk`
compression.  Parametric in the hoisted FIPS digits `idxTree0`/`idxLeaf0`
(11-bit, supplied by `SegmentForsSetup.stepForsSetup_idxTree0/_idxLeaf0`). -/
theorem forsFinalizePreCopyStep_adrsRoots_slot
    (st : RuntimeState) (it0 il0 : Nat)
    (hT : lookupValue st.bindings "idxTree0" = it0) (hTlt : it0 < 2 ^ 11)
    (hL : lookupValue st.bindings "idxLeaf0" = il0) (hLlt : il0 < 2 ^ 11) :
    ((forsFinalizePreCopyStep st).world.memory 0x20).val
      = SphincsMinusVerifierSpec.C13Concrete.adrsForsRoots it0 il0 := by
  -- Pin the binder-write values so later states are syntactic records.
  obtain ⟨w1, hw1⟩ : ∃ w, evalExpr [] st
      (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6))))) (u N_MASK))
        = some w := ⟨_, rfl⟩
  set st1 : RuntimeState := { st with bindings := bindValue st.bindings "lastSecret" w1 }
    with hst1
  obtain ⟨w2, hw2⟩ : ∃ w, evalExpr [] st1
      (orE (v "forsBase") (shlE (u 19) (u 6))) = some w := ⟨_, rfl⟩
  set st2 : RuntimeState := { st1 with world := { st1.world with
      memory := MemoryKit.memUpdate st1.world.memory 0x20 w2 } } with hst2
  obtain ⟨w3, hw3⟩ : ∃ w, evalExpr [] st2 (v "lastSecret") = some w := ⟨_, rfl⟩
  set st3 : RuntimeState := { st2 with world := { st2.world with
      memory := MemoryKit.memUpdate st2.world.memory 0x40 w3 } } with hst3
  obtain ⟨w4, hw4⟩ : ∃ w, evalExpr [] st3
      (andE (keccak 0x00 0x60) (u N_MASK)) = some w := ⟨_, rfl⟩
  set st4 : RuntimeState := { st3 with world := { st3.world with
      memory := MemoryKit.memUpdate st3.world.memory 0x140 w4 } } with hst4
  -- Eval witness for the FORS_ROOTS address word in `st4`.
  have hT4 : evalExpr [] st4 (v "idxTree0") = some it0 := by
    show some (lookupValue (bindValue st.bindings "lastSecret" w1) "idxTree0") = some it0
    rw [MemoryKit.lookupValue_bindValue_ne _ "lastSecret" "idxTree0" _ (by decide), hT]
  have hL4 : evalExpr [] st4 (v "idxLeaf0") = some il0 := by
    show some (lookupValue (bindValue st.bindings "lastSecret" w1) "idxLeaf0") = some il0
    rw [MemoryKit.lookupValue_bindValue_ne _ "lastSecret" "idxLeaf0" _ (by decide), hL]
  have hShlT : evalExpr [] st4 (shlE (u 128) (v "idxTree0")) = some (it0 <<< 128) :=
    ClimbKeccakStep.evalExpr_shl_bounded st4 (u 128) (v "idxTree0") 128 it0 rfl hT4
      (by norm_num) (lt_trans hTlt (by norm_num)) (shl128_lt_of_lt11 it0 hTlt)
  have hShlM : evalExpr [] st4 (shlE (u 96) (u 4)) = some ((4 : Nat) <<< 96) :=
    ClimbKeccakStep.evalExpr_shl_bounded st4 (u 96) (u 4) 96 4 rfl rfl
      (by norm_num) (by norm_num) (by decide)
  have hShlL : evalExpr [] st4 (shlE (u 64) (v "idxLeaf0")) = some (il0 <<< 64) :=
    ClimbKeccakStep.evalExpr_shl_bounded st4 (u 64) (v "idxLeaf0") 64 il0 rfl hL4
      (by norm_num) (lt_trans hLlt (by norm_num)) (shl64_lt_of_lt11 il0 hLlt)
  have hInner : evalExpr [] st4 (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0")))
      = some ((4 <<< 96) ||| (il0 <<< 64)) :=
    ClimbKeccakStep.evalExpr_bitOr_bounded st4 _ _ _ _ hShlM hShlL
      (by decide) (shl64_lt_of_lt11 il0 hLlt)
  have hInnerLt : (4 <<< 96) ||| (il0 <<< 64) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (by decide) (shl64_lt_of_lt11 il0 hLlt)
  have hRoots : evalExpr [] st4
      (orE (shlE (u 128) (v "idxTree0"))
        (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0"))))
      = some ((it0 <<< 128) ||| ((4 <<< 96) ||| (il0 <<< 64))) :=
    ClimbKeccakStep.evalExpr_bitOr_bounded st4 _ _ _ _ hShlT hInner
      (shl128_lt_of_lt11 it0 hTlt) hInnerLt
  have hVLt : (it0 <<< 128) ||| ((4 <<< 96) ||| (il0 <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (shl128_lt_of_lt11 it0 hTlt) hInnerLt
  have h2 : execStmt [] st1 (mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6))))
      = .continue st2 :=
    execStmt_mstore_continue st1 (u 0x20) _ 0x20 w2 rfl hw2
  have h3 : execStmt [] st2 (mstore 0x40 (v "lastSecret")) = .continue st3 :=
    execStmt_mstore_continue st2 (u 0x40) _ 0x40 w3 rfl hw3
  have h4 : execStmt [] st3 (mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK)))
      = .continue st4 :=
    execStmt_mstore_continue st3 (u 0x140) _ 0x140 w4 rfl hw4
  have h5 : execStmt [] st4
      (mstore 0x20 (orE (shlE (u 128) (v "idxTree0"))
        (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0")))))
      = .continue { st4 with world := { st4.world with
          memory := MemoryKit.memUpdate st4.world.memory 0x20
            ((it0 <<< 128) ||| ((4 <<< 96) ||| (il0 <<< 64))) } } :=
    execStmt_mstore_continue st4 (u 0x20) _ 0x20 _ rfl hRoots
  unfold forsFinalizePreCopyStep forsFinalizePreCopyBody
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ hw1)]
  rw [execStmtList_cons_continue _ _ _ _ h2]
  rw [execStmtList_cons_continue _ _ _ _ h3]
  rw [execStmtList_cons_continue _ _ _ _ h4]
  rw [execStmtList_cons_continue _ _ _ _ h5]
  simp only [execStmtList]
  simp [MemoryKit.memUpdate,
    SphincsMinusVerifierSpec.C13Concrete.adrsForsRoots, Nat.lor_assoc]
  exact Nat.mod_eq_of_lt (by simpa using hVLt)

set_option maxHeartbeats 4000000 in
/-- The pre-copy finalize prefix computes the forced-zero seventh FORS root in
source slot `0x140`, provided the incoming seed cell, the hoisted `"forsBase"`
ADRS-base binding, and the seventh secret word are the expected spec words.
Stated over a generic bounded base word so it is layout-agnostic; instantiate
`base := adrsForsBase idxTree0 idxLeaf0` and identify
`base ||| (6 <<< 19) = adrsForsLeaf idxTree0 idxLeaf0 6 0` via
`adrsForsLeaf_eq_of_forsBase` + `Nat.lor_zero` at the call site. -/
theorem forsFinalizePreCopyStep_forced_root_cell
    (st : RuntimeState) (seed base sk : Nat)
    (hmSeed : (st.world.memory 0).val = seed)
    (hFB : lookupValue st.bindings "forsBase" = base)
    (hBaseLt : base < 2 ^ 256)
    (hLastSecret :
      evalExpr [] st
        (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6)))))
          (u N_MASK)) = some sk) :
    ((forsFinalizePreCopyStep st).world.memory 0x140).val
      = maskN (keccakWords [seed, base ||| (6 <<< 19), sk]) := by
  have hLeafLt : base ||| (6 <<< 19) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow hBaseLt (by decide)
  let st1 : RuntimeState := { st with bindings := bindValue st.bindings "lastSecret" sk }
  let st2 : RuntimeState :=
    { st1 with world := { st1.world with
        memory := MemoryKit.memUpdate st1.world.memory 0x20 (base ||| (6 <<< 19)) } }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with
        memory := MemoryKit.memUpdate st2.world.memory 0x40 sk } }
  let node : Nat := maskN (keccakWords [seed, base ||| (6 <<< 19), sk])
  let st4 : RuntimeState :=
    { st3 with world := { st3.world with
        memory := MemoryKit.memUpdate st3.world.memory 0x140 node } }
  have h1 : execStmt [] st
      (.letVar "lastSecret"
        (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6)))))
          (u N_MASK))) = .continue st1 := by
    unfold st1
    exact execStmt_letVar_continue st "lastSecret" _ _ hLastSecret
  have h2 : execStmt [] st1
      (mstore 0x20 (orE (v "forsBase") (shlE (u 19) (u 6))))
        = .continue st2 := by
    unfold st2 mstore
    refine execStmt_mstore_continue st1 (u 0x20)
      (orE (v "forsBase") (shlE (u 19) (u 6))) 0x20 (base ||| (6 <<< 19)) rfl ?_
    have hFB1 : evalExpr [] st1 (v "forsBase") = some base := by
      show some (lookupValue (bindValue st.bindings "lastSecret" sk) "forsBase") = some base
      rw [MemoryKit.lookupValue_bindValue_ne _ "lastSecret" "forsBase" _ (by decide), hFB]
    have hShl : evalExpr [] st1 (shlE (u 19) (u 6)) = some ((6 : Nat) <<< 19) :=
      ClimbKeccakStep.evalExpr_shl_bounded st1 (u 19) (u 6) 19 6 rfl rfl
        (by norm_num) (by norm_num) (by decide)
    exact ClimbKeccakStep.evalExpr_bitOr_bounded st1 _ _ _ _ hFB1 hShl
      hBaseLt (by decide)
  have h3 : execStmt [] st2 (mstore 0x40 (v "lastSecret")) = .continue st3 := by
    unfold st3 mstore u v
    refine execStmt_mstore_continue st2 (.literal 0x40) (.localVar "lastSecret")
      0x40 sk rfl ?_
    unfold st2 st1
    show some (lookupValue (bindValue st.bindings "lastSecret" sk) "lastSecret") = some sk
    rw [MemoryKit.lookupValue_bindValue_self]
  have hNode :
      evalExpr [] st3
        (andE (keccak 0x00 0x60) (u N_MASK)) = some node := by
    unfold node
    have hsk_lt : sk < Verity.Core.Uint256.modulus :=
      evalExpr_bitAnd_result_lt hLastSecret
    unfold andE keccak u
    refine SphincsMinusVerifiers.InitialNodeKeccak.fors_leaf_node_eq
      _ seed (base ||| (6 <<< 19)) sk ?_ ?_ ?_
    · simp [st3, st2, st1, MemoryKit.memUpdate, hmSeed]
    · simp [st3, st2, MemoryKit.memUpdate]
      exact Nat.mod_eq_of_lt hLeafLt
    · simp [st3, MemoryKit.memUpdate, Nat.mod_eq_of_lt hsk_lt]
  have h4 : execStmt [] st3
      (mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK))) = .continue st4 := by
    unfold st4 mstore u
    exact execStmt_mstore_continue st3 (.literal 0x140)
      (andE (keccak 0x00 0x60) (.literal N_MASK)) 0x140 node rfl hNode
  obtain ⟨w5, hw5⟩ : ∃ w, evalExpr [] st4
      (orE (shlE (u 128) (v "idxTree0"))
        (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0")))) = some w := ⟨_, rfl⟩
  have h5 : execStmt [] st4
      (mstore 0x20 (orE (shlE (u 128) (v "idxTree0"))
        (orE (shlE (u 96) (u 4)) (shlE (u 64) (v "idxLeaf0")))))
      = .continue { st4 with world := { st4.world with
          memory := MemoryKit.memUpdate st4.world.memory 0x20 w5 } } :=
    execStmt_mstore_continue st4 (u 0x20) _ 0x20 w5 rfl hw5
  have hExec : execStmtList [] st forsFinalizePreCopyBody
      = .continue { st4 with world := { st4.world with
          memory := MemoryKit.memUpdate st4.world.memory 0x20 w5 } } := by
    unfold forsFinalizePreCopyBody
    rw [execStmtList_cons_continue _ _ _ _ h1]
    rw [execStmtList_cons_continue _ _ _ _ h2]
    rw [execStmtList_cons_continue _ _ _ _ h3]
    rw [execStmtList_cons_continue _ _ _ _ h4]
    rw [execStmtList_cons_continue _ _ _ _ h5]
    rfl
  unfold forsFinalizePreCopyStep
  rw [hExec]
  have hnode_lt : node < Verity.Core.Uint256.modulus :=
    evalExpr_bitAnd_result_lt hNode
  unfold st4
  simp [MemoryKit.memUpdate]
  unfold node at hnode_lt ⊢
  exact Nat.mod_eq_of_lt hnode_lt

set_option maxHeartbeats 4000000 in
/-- Running the finalize prefix continues to `forsFinalizePrePkStep st`. -/
theorem execForsFinalizePrePk (st : RuntimeState) :
    execStmtList [] st forsFinalizePrePkBody = .continue (forsFinalizePrePkStep st) := by
  unfold forsFinalizePrePkStep forsFinalizePrePkBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 7) forsCopyBody _ (wordNormalize 7)
        forsCopyStep rfl execForsCopy)]
  rfl

set_option maxHeartbeats 4000000 in
/-- The real pre-`forsPk` state has the copy-loop image in its compression slots:
for every `j < 7`, slot `0x40 + 32*j` equals the pre-copy root slot
`0x80 + 32*j`. -/
theorem forsFinalizePrePkStep_copy_slot (st : RuntimeState) (j : Nat) (hj : j < 7) :
    ((forsFinalizePrePkStep st).world.memory (0x40 + 32 * j)).val
      = ((forsFinalizePreCopyStep st).world.memory (0x80 + 32 * j)).val := by
  have h7 : wordNormalize 7 = 7 := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide)
  have hstep :
      forsFinalizePrePkStep st
        = foldLoop "i" forsCopyStep
            { (forsFinalizePreCopyStep st) with
              bindings := bindValue (forsFinalizePreCopyStep st).bindings "i" (wordNormalize 0) }
            0 (wordNormalize 7) := by
    unfold forsFinalizePrePkStep
    rw [forsFinalizePrePkBody_eq_preCopy_append]
    rw [MemoryKit.execStmtList_append_continue _ _ _ _ (execForsFinalizePreCopy st)]
    unfold u
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 7) forsCopyBody _ (wordNormalize 7)
        forsCopyStep rfl execForsCopy)]
    simp [execStmtList]
  rw [hstep, h7]
  exact forsCopyLoop7_copied_slot
    { (forsFinalizePreCopyStep st) with
      bindings := bindValue (forsFinalizePreCopyStep st).bindings "i" (wordNormalize 0) }
    j hj

set_option maxHeartbeats 4000000 in
/-- The real pre-`forsPk` state preserves the low scratch cells from the pre-copy
state.  This covers the seed word at `0x00` and the FORS_ROOTS address word at
`0x20`; the copy loop only writes from `0x40` upward. -/
theorem forsFinalizePrePkStep_preserves_low_slot
    (st : RuntimeState) (addr : Nat) (haddr : addr < 0x40) :
    ((forsFinalizePrePkStep st).world.memory addr).val
      = ((forsFinalizePreCopyStep st).world.memory addr).val := by
  have h7 : wordNormalize 7 = 7 := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide)
  have hstep :
      forsFinalizePrePkStep st
        = foldLoop "i" forsCopyStep
            { (forsFinalizePreCopyStep st) with
              bindings := bindValue (forsFinalizePreCopyStep st).bindings "i" (wordNormalize 0) }
            0 (wordNormalize 7) := by
    unfold forsFinalizePrePkStep
    rw [forsFinalizePrePkBody_eq_preCopy_append]
    rw [MemoryKit.execStmtList_append_continue _ _ _ _ (execForsFinalizePreCopy st)]
    unfold u
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 7) forsCopyBody _ (wordNormalize 7)
        forsCopyStep rfl execForsCopy)]
    simp [execStmtList]
  rw [hstep, h7]
  exact forsCopyLoop7_preserves_low_slot
    { (forsFinalizePreCopyStep st) with
      bindings := bindValue (forsFinalizePreCopyStep st).bindings "i" (wordNormalize 0) }
    addr haddr

theorem forsFinalizePrePkStep_seed_slot (st : RuntimeState) :
    ((forsFinalizePrePkStep st).world.memory 0).val = (st.world.memory 0).val := by
  rw [forsFinalizePrePkStep_preserves_low_slot st 0 (by decide : 0 < 0x40)]
  exact forsFinalizePreCopyStep_seed_slot st

set_option maxHeartbeats 4000000 in
/-- **`execForsFinalize`** — running the FORS finalize block over the real
interpreter continues to `forsFinalizeStep st`.  The leaf-hash setup chains via
per-statement `.continue` lemmas; the copy loop is dispatched by
`execStmt_forEach_of_step` over `execForsCopy`; the `forsPk` keccak finishes. -/
theorem execForsFinalize (st : RuntimeState) :
    execStmtList [] st forsFinalizeBody = .continue (forsFinalizeStep st) := by
  unfold forsFinalizeStep forsFinalizeBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 7) forsCopyBody _ (wordNormalize 7)
        forsCopyStep rfl execForsCopy)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "forsPk" _ _ rfl)]
  rfl

/-- `forsFinalizeStep` is exactly the pre-`forsPk` state with `"forsPk"` bound to
`forsPkExpr` evaluated in that pre-state.  This is a structural boundary lemma:
it does not yet identify the compressed memory words with the spec's FORS roots,
but it exposes the precise model word that the S4 correspondence must prove is
`wordOfHash16 forsPk`. -/
theorem forsFinalizeStep_forsPk
    (st : RuntimeState) :
    lookupValue (forsFinalizeStep st).bindings "forsPk"
      = (Verity.Core.Uint256.and
          (keccakMemorySlice (forsFinalizePrePkStep st).world.memory
            (wordNormalize 0x00) (wordNormalize 0x120))
          (wordNormalize N_MASK)).val := by
  unfold forsFinalizeStep
  rw [forsFinalizeBody_eq_prePk_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (execForsFinalizePrePk st)]
  unfold forsPkExpr
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue (forsFinalizePrePkStep st) "forsPk" _ _ rfl)]
  rfl

theorem forsFinalizeStep_seed_slot (st : RuntimeState) :
    ((forsFinalizeStep st).world.memory 0).val = (st.world.memory 0).val := by
  unfold forsFinalizeStep
  rw [forsFinalizeBody_eq_prePk_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (execForsFinalizePrePk st)]
  unfold forsPkExpr
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_letVar_continue (forsFinalizePrePkStep st) "forsPk" _ _ rfl)]
  simp only [execStmtList]
  exact forsFinalizePrePkStep_seed_slot st

/-! ## 5. Axiom audit. -/

#print axioms forsFinalizeBody_eq_slice
#print axioms forsFinalizeBody_eq_prePk_append
#print axioms forsFinalizePrePkBody_eq_preCopy_append
#print axioms execForsCopy
#print axioms forsCopyStep_copied
#print axioms forsCopyStep_preserves_copy_slot
#print axioms forsCopyStep_preserves_future_source_slot
#print axioms forsCopyStep_preserves_low_slot
#print axioms forsCopyLoop_preserves_past_copy_slot
#print axioms forsCopyLoop_preserves_future_source_slot
#print axioms forsCopyLoop_copied_slot
#print axioms forsCopyLoop7_copied_slot
#print axioms forsCopyLoop7_preserves_low_slot
#print axioms execForsFinalizePreCopy
#print axioms forsFinalizePreCopyStep_seed_slot
#print axioms forsFinalizePreCopyStep_preserves_root_source_slot
#print axioms forsFinalizePreCopyStep_adrsRoots_slot
#print axioms forsFinalizePreCopyStep_forced_root_cell
#print axioms execForsFinalizePrePk
#print axioms forsFinalizePrePkStep_copy_slot
#print axioms forsFinalizePrePkStep_preserves_low_slot
#print axioms forsFinalizePrePkStep_seed_slot
#print axioms execForsFinalize
#print axioms forsFinalizeStep_forsPk
#print axioms forsFinalizeStep_seed_slot

end SphincsMinusVerifiers.SegmentS4Finalize
