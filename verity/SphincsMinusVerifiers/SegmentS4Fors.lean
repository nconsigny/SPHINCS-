/-
  SegmentS4Fors — the FORS outer-loop body step lemma (statement 14 of
  `c13VerifyBody`, the `forEach "i" (u 6)` FORS tree-root reconstruction).

  This is the S4 double-loop's *outer* per-iteration body.  Its structure is:

  ```
  117..125  leaf setup        (7 letVar + 2 mstore — pure binder/memory writes)
  126       forEach "h" (u 19)  ← inner Merkle climb = ClimbKit.forsClimbBody
                                   (merkleClimbBodyA at the FIPS forsAdrs)
  136       mstore  scratch[i]  := node           (store the reconstructed leaf)
  ```

  We prove the whole body runs to a `.continue` of a pure transformer
  (`forsLeafStep`), dispatching the inner climb in a single rewrite via
  `ClimbLoop.execStmt_forEach_merkleClimb`, and then thread the *outer*
  `forEach "i" (u 6)` through `ClimbLoop.execStmt_forEach_of_step`, giving the
  full statement-14 reduction `execForsOuter`.

  Faithfulness is machine-checked: `forsOuterStmt_eq_slice` (`rfl`) shows the
  reconstructed statement — loop header *and* full body, including the inner
  `forEach` — is exactly statement 14 of the real `c13VerifyBody`.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.InitialNodeKeccak
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers.SegmentS4Fors

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK merkleClimbBody stepMerkle forsClimbBody stepForsMerkle)
open SphincsMinusVerifiers.ClimbLoop (foldLoop)
open SphincsMinusVerifierSpec.C13Concrete (adrsForsLeaf maskN keccakWords wordOfHash16)

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

/-! ## 1. The FORS outer-loop body (statement 14's body), with the inner Merkle
climb written as `forsClimbBody` so `execStmt_forEach_forsClimb` applies. -/

/-- The body of `forEach "i" (u 6)` (FORS tree-root reconstruction, stmts
117..136 of `c13VerifyBody`). -/
def forsLeafBody : List Stmt :=
  [ .letVar "treeIdx" (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF))
  , .letVar "secretVal" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK))
  , .letVar "leafAdrs" (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx")))
  , mstore 0x20 (v "leafAdrs")
  , mstore 0x40 (v "secretVal")
  , .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK))
  , .letVar "pathIdx" (v "treeIdx")
  , .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304))))
  , .forEach "h" (u 19) forsClimbBody
  , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") ]

/-- The straight-line setup before the inner Merkle climb in one FORS tree. -/
def forsLeafSetupBody : List Stmt :=
  [ .letVar "treeIdx" (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF))
  , .letVar "secretVal" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK))
  , .letVar "leafAdrs" (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx")))
  , mstore 0x20 (v "leafAdrs")
  , mstore 0x40 (v "secretVal")
  , .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK))
  , .letVar "pathIdx" (v "treeIdx")
  , .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ]

/-- The inner Merkle climb statement in one FORS tree. -/
def forsLeafInnerStmt : Stmt :=
  .forEach "h" (u 19) forsClimbBody

/-- The final store of one reconstructed FORS tree root into the root array. -/
def forsLeafStoreStmt : Stmt :=
  mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node")

/-- Structural split of the FORS leaf body into setup, inner climb, and final store. -/
theorem forsLeafBody_eq_segments :
    forsLeafBody = forsLeafSetupBody ++ [forsLeafInnerStmt, forsLeafStoreStmt] := rfl

/-! ## 1a. Setup-frame facts. -/

/-- Pure transformer for the straight-line setup prefix. -/
def forsLeafSetupStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsLeafSetupBody with
  | .continue s' => s'
  | _ => st

open SphincsMinusVerifiers.ClimbKit (execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue)
open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_merkleClimb)

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

/-- The setup prefix always continues to `forsLeafSetupStep`. -/
theorem execForsLeafSetup (st : RuntimeState) :
    execStmtList [] st forsLeafSetupBody = .continue (forsLeafSetupStep st) := by
  unfold forsLeafSetupStep forsLeafSetupBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  rfl

/-- The straight-line FORS leaf setup writes only `0x20` and `0x40`, so it
preserves the seed cell `mem[0x00]`. -/
theorem forsLeafSetup_preserves_seed_slot
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0 forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "treeIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "secretVal" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "leafAdrs" _ hexec

  · subst stmt
    refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0 (u 0x20) (v "leafAdrs") ?_ hexec
    intro ro rv hoff _
    change some (wordNormalize 0x20) = some ro at hoff
    injection hoff with hro
    rw [show wordNormalize 0x20 = 0x20 by rfl] at hro
    subst ro
    decide
  · subst stmt
    refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0 (u 0x40) (v "secretVal") ?_ hexec
    intro ro rv hoff _
    change some (wordNormalize 0x40) = some ro at hoff
    injection hoff with hro
    rw [show wordNormalize 0x40 = 0x40 by rfl] at hro
    subst ro
    decide
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "node" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "pathIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "authPtr" _ hexec

/-- The straight-line FORS leaf setup never rebinds the outer loop variable
`"i"`. -/
theorem forsLeafSetup_preserves_i
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "i" _ (by decide) hexec

/-- Step-form seed-cell frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_seed_slot (st : RuntimeState) :
    ((forsLeafSetupStep st).world.memory 0).val = (st.world.memory 0).val :=
  forsLeafSetup_preserves_seed_slot st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- The straight-line FORS leaf setup preserves every ordinary root-array slot:
it writes only scratch cells `0x20` and `0x40`, while ordinary roots live at
`0x80 + 32*j`. -/
theorem forsLeafSetup_preserves_root_cell_range
    (st s' : RuntimeState) (j : Nat)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    (s'.world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    (0x80 + 32 * j) forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "treeIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "secretVal" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "leafAdrs" _ hexec

  · subst stmt
    refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' (0x80 + 32 * j) (u 0x20) (v "leafAdrs") ?_ hexec
    intro ro rv hoff _
    change some (wordNormalize 0x20) = some ro at hoff
    injection hoff with hro
    rw [show wordNormalize 0x20 = 0x20 by rfl] at hro
    subst ro
    omega
  · subst stmt
    refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' (0x80 + 32 * j) (u 0x40) (v "secretVal") ?_ hexec
    intro ro rv hoff _
    change some (wordNormalize 0x40) = some ro at hoff
    injection hoff with hro
    rw [show wordNormalize 0x40 = 0x40 by rfl] at hro
    subst ro
    omega
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "node" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "pathIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' (0x80 + 32 * j) "authPtr" _ hexec

/-- Step-form setup frame for ordinary FORS root-array cells. -/
theorem forsLeafSetupStep_preserves_root_cell_range
    (st : RuntimeState) (j : Nat) :
    ((forsLeafSetupStep st).world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val :=
  forsLeafSetup_preserves_root_cell_range
    st (forsLeafSetupStep st) j (execForsLeafSetup st)

/-- Step-form outer-index binding frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_i (st : RuntimeState) :
    lookupValue (forsLeafSetupStep st).bindings "i" = lookupValue st.bindings "i" :=
  forsLeafSetup_preserves_i st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- The straight-line FORS leaf setup never rebinds `"sigBase"`. -/
theorem forsLeafSetup_preserves_sigBase
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    lookupValue s'.bindings "sigBase" = lookupValue st.bindings "sigBase" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigBase" forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "sigBase" _ (by decide) hexec

/-- Step-form signature-base binding frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_sigBase (st : RuntimeState) :
    lookupValue (forsLeafSetupStep st).bindings "sigBase"
      = lookupValue st.bindings "sigBase" :=
  forsLeafSetup_preserves_sigBase st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- The straight-line FORS leaf setup never rebinds the digest word `"dVal"`. -/
theorem forsLeafSetup_preserves_dVal
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    lookupValue s'.bindings "dVal" = lookupValue st.bindings "dVal" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "dVal" forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "dVal" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "dVal" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "dVal" _ (by decide) hexec

/-- Step-form digest-word binding frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_dVal (st : RuntimeState) :
    lookupValue (forsLeafSetupStep st).bindings "dVal" = lookupValue st.bindings "dVal" :=
  forsLeafSetup_preserves_dVal st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- Step-form selector/calldata frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_selector_calldata (st : RuntimeState) :
    (forsLeafSetupStep st).selector = st.selector ∧
      (forsLeafSetupStep st).world.calldata = st.world.calldata := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    forsLeafSetupBody st (forsLeafSetupStep st) ?_ (execForsLeafSetup st)
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "treeIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "secretVal" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "leafAdrs" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "node" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "pathIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "authPtr" _ hexec

private theorem authPtr_offset_lt_six (idx : Nat) (hidx : idx < 6) :
    164 + (128 + 304 * idx) < 2 ^ 256 := by
  calc
    164 + (128 + 304 * idx) ≤ 164 + (128 + 304 * 5) := by
      omega
    _ < 2 ^ 256 := by decide

private theorem uint256_mul_304_lt_six (idx : Nat) (hidx : idx < 6) :
    (Verity.Core.Uint256.ofNat idx * Verity.Core.Uint256.ofNat 304).val = 304 * idx := by
  show (((Verity.Core.Uint256.ofNat idx).val *
        (Verity.Core.Uint256.ofNat 304).val) % Verity.Core.Uint256.modulus) = 304 * idx
  have hidxv : (Verity.Core.Uint256.ofNat idx).val = idx :=
    Nat.mod_eq_of_lt (lt_trans hidx (by decide))
  have h304v : (Verity.Core.Uint256.ofNat 304).val = 304 :=
    Nat.mod_eq_of_lt (by decide)
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hidxv, h304v, hmod, Nat.mul_comm idx 304]
  rw [Nat.mod_eq_of_lt]
  calc
    304 * idx ≤ 304 * 5 := by omega
    _ < 2 ^ 256 := by decide

private theorem uint256_add_128_mul304_lt_six (idx : Nat) (hidx : idx < 6) :
    (Verity.Core.Uint256.ofNat 128 +
        Verity.Core.Uint256.ofNat
          (Verity.Core.Uint256.ofNat idx * Verity.Core.Uint256.ofNat 304).val).val
      = 128 + 304 * idx := by
  rw [uint256_mul_304_lt_six idx hidx]
  show (((Verity.Core.Uint256.ofNat 128).val +
        (Verity.Core.Uint256.ofNat (304 * idx)).val) % Verity.Core.Uint256.modulus)
      = 128 + 304 * idx
  have h128v : (Verity.Core.Uint256.ofNat 128).val = 128 :=
    Nat.mod_eq_of_lt (by decide)
  have hprodv : (Verity.Core.Uint256.ofNat (304 * idx)).val = 304 * idx := by
    refine Nat.mod_eq_of_lt ?_
    calc
      304 * idx ≤ 304 * 5 := by omega
      _ < 2 ^ 256 := by decide
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [h128v, hprodv, hmod, Nat.mod_eq_of_lt]
  calc
    128 + 304 * idx ≤ 128 + 304 * 5 := by omega
    _ < 2 ^ 256 := by decide

private theorem uint256_authPtr_expr_eq_sigDataOffset (idx : Nat) (hidx : idx < 6) :
    (Verity.Core.Uint256.ofNat 164 +
        Verity.Core.Uint256.ofNat
          (Verity.Core.Uint256.ofNat 128 +
              Verity.Core.Uint256.ofNat
                (Verity.Core.Uint256.ofNat idx * Verity.Core.Uint256.ofNat 304).val).val).val
      = 164 + (128 + 304 * idx) := by
  rw [uint256_add_128_mul304_lt_six idx hidx]
  show (((Verity.Core.Uint256.ofNat 164).val +
        (Verity.Core.Uint256.ofNat (128 + 304 * idx)).val) %
        Verity.Core.Uint256.modulus) = 164 + (128 + 304 * idx)
  have h164v : (Verity.Core.Uint256.ofNat 164).val = 164 :=
    Nat.mod_eq_of_lt (by decide)
  have hoffv : (Verity.Core.Uint256.ofNat (128 + 304 * idx)).val =
      128 + 304 * idx := by
    refine Nat.mod_eq_of_lt ?_
    calc
      128 + 304 * idx ≤ 128 + 304 * 5 := by omega
      _ < 2 ^ 256 := by decide
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [h164v, hoffv, hmod, Nat.mod_eq_of_lt (authPtr_offset_lt_six idx hidx)]

private theorem uint256_and_val_lt (a b : Verity.Core.Uint256) :
    (a.and b).val < 2 ^ 256 := by
  simpa [Verity.Core.UINT256_MODULUS] using (a.and b).isLt

/-- C13-shaped setup fact for the FORS auth-path pointer: the straight-line
setup prefix binds `"authPtr"` to the signature-data base plus the per-FORS-tree
authentication-path offset. -/
theorem forsLeafSetupStep_authPtr_eq_sigDataOffset
    (st : RuntimeState) (idx : Nat)
    (hi : lookupValue st.bindings "i" = idx)
    (hsigBase : lookupValue st.bindings "sigBase" = 164)
    (hidx : idx < 6) :
    lookupValue (forsLeafSetupStep st).bindings "authPtr"
      = 164 + (128 + 304 * idx) := by
  unfold forsLeafSetupStep forsLeafSetupBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  simpa [execStmtList,
    SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
    SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne, hi, hsigBase]
    using uint256_authPtr_expr_eq_sigDataOffset idx hidx

/-- C13-shaped setup fact for the FORS path index: the straight-line setup
prefix binds `"pathIdx"` to the masked 19-bit tree index, hence the value is a
bounded EVM word. -/
theorem forsLeafSetupStep_pathIdx_lt
    (st : RuntimeState) (idx : Nat)
    (hi : lookupValue st.bindings "i" = idx) :
    lookupValue (forsLeafSetupStep st).bindings "pathIdx" < 2 ^ 256 := by
  unfold forsLeafSetupStep forsLeafSetupBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  simpa [execStmtList,
    SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
    SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne, hi,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    using (uint256_and_val_lt
      (Verity.Core.Uint256.ofNat
        ((Verity.Core.Uint256.ofNat
            (Verity.Core.Uint256.ofNat idx *
              Verity.Core.Uint256.ofNat (19 % Compiler.Constants.evmModulus)).val).shr
          (Verity.Core.Uint256.ofNat (lookupValue st.bindings "dVal"))).val)
      (Verity.Core.Uint256.ofNat (524287 % Compiler.Constants.evmModulus)))

/-- If the setup prefix decodes `treeIdx`, the post-setup `"pathIdx"` binding is
exactly that tree index. -/
theorem forsLeafSetupStep_pathIdx_eq_of_eval
    (st : RuntimeState) (treeIdx : Nat)
    (hTree : evalExpr [] st
        (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF)) = some treeIdx) :
    lookupValue (forsLeafSetupStep st).bindings "pathIdx" = treeIdx := by
  unfold forsLeafSetupStep forsLeafSetupBody mstore
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ hTree)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  simp only [execStmtList]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne _ "authPtr" "pathIdx" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne _ "node" "treeIdx" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne _ "leafAdrs" "treeIdx" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne _ "secretVal" "treeIdx" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]

private theorem idxShl19_lt (idx : Nat) (hidx : idx < 6) :
    idx <<< 19 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  calc
    idx * 2 ^ 19 ≤ 5 * 2 ^ 19 :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
    _ < 2 ^ 256 := by decide

/-- The FIPS C13 FORS leaf-address expression
`or(forsBase, or(shl(19, i), treeIdx))` evaluates to
`base ||| ((idx <<< 19) ||| treeIdx)` once the carried `"forsBase"`, `"i"`,
and `"treeIdx"` bindings are identified and bounded.  This is the single eval
lemma that replaces the retired pre-FIPS `forsTreeAdrsBase_eval_eq`. -/
theorem forsLeafAdrs_eval_eq
    (st : RuntimeState) {base idx treeIdx : Nat}
    (hbase : lookupValue st.bindings "forsBase" = base)
    (hbaseLt : base < 2 ^ 256)
    (hi : lookupValue st.bindings "i" = idx)
    (hidx : idx < 6)
    (ht : lookupValue st.bindings "treeIdx" = treeIdx)
    (htLt : treeIdx < 2 ^ 19) :
    evalExpr [] st
        (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx")))
      = some (base ||| ((idx <<< 19) ||| treeIdx)) := by
  have hiEval : evalExpr [] st (v "i") = some idx := by
    show some (lookupValue st.bindings "i") = some idx
    rw [hi]
  have hbaseEval : evalExpr [] st (v "forsBase") = some base := by
    show some (lookupValue st.bindings "forsBase") = some base
    rw [hbase]
  have htEval : evalExpr [] st (v "treeIdx") = some treeIdx := by
    show some (lookupValue st.bindings "treeIdx") = some treeIdx
    rw [ht]
  have hsh :
      evalExpr [] st (shlE (u 19) (v "i")) = some (idx <<< 19) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (u 19) (v "i") 19 idx rfl hiEval
      (by decide)
      (lt_trans hidx (by decide : 6 < 2 ^ 256))
      (idxShl19_lt idx hidx)
  have htLt256 : treeIdx < 2 ^ 256 :=
    lt_trans htLt (by decide : 2 ^ 19 < 2 ^ 256)
  have hinner :
      evalExpr [] st (orE (shlE (u 19) (v "i")) (v "treeIdx"))
        = some ((idx <<< 19) ||| treeIdx) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st (shlE (u 19) (v "i")) (v "treeIdx")
      (idx <<< 19) treeIdx hsh htEval (idxShl19_lt idx hidx) htLt256
  have hinnerLt : (idx <<< 19) ||| treeIdx < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (idxShl19_lt idx hidx) htLt256
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    st (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx"))
    base ((idx <<< 19) ||| treeIdx) hbaseEval hinner hbaseLt hinnerLt

/-- The right-associated eval value above is exactly the spec FORS leaf
address once `"forsBase"` carries the spec ADRS base. -/
theorem forsLeafAdrs_value_eq_spec
    (idxTree0 idxLeaf0 idx treeIdx : Nat) :
    SphincsMinusVerifierSpec.C13Concrete.adrsForsBase idxTree0 idxLeaf0
        ||| ((idx <<< 19) ||| treeIdx)
      = SphincsMinusVerifierSpec.C13Concrete.adrsForsLeaf idxTree0 idxLeaf0 idx treeIdx := by
  rw [SphincsMinusVerifierSpec.C13Concrete.adrsForsLeaf_eq_of_forsBase,
    Nat.lor_assoc]

/-- The straight-line FORS leaf setup never rebinds the hoisted FIPS ADRS base
`"forsBase"` (it is bound once, before the outer loop, by the fors-setup
segment).  Under the FIPS layout this *preservation* fact replaces the retired
per-iteration `forsLeafSetupStep_forsBase_eq_of_i`. -/
theorem forsLeafSetup_preserves_forsBase
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    lookupValue s'.bindings "forsBase" = lookupValue st.bindings "forsBase" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "forsBase" forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "forsBase" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "forsBase" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "forsBase" _ (by decide) hexec

/-- Step-form FIPS ADRS-base binding frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_forsBase (st : RuntimeState) :
    lookupValue (forsLeafSetupStep st).bindings "forsBase"
      = lookupValue st.bindings "forsBase" :=
  forsLeafSetup_preserves_forsBase st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- If the setup prefix's decoded FORS leaf address word `leafW` and secret-key
word are already identified with their spec values, the setup `"node"` binding
is exactly the spec FORS leaf hash.  Stated over an *arbitrary* bounded address
word `leafW`, so it is layout-agnostic: instantiate `leafW :=
adrsForsLeaf idxTree0 idxLeaf0 i treeIdx` via `forsLeafAdrs_eval_eq` +
`forsLeafAdrs_value_eq_spec`.  This is the initial-relation seed for the later
inner-climb `forsClimb` correspondence. -/
theorem forsLeafSetupStep_node_eq_spec_of_eval
    (st : RuntimeState) (seed leafW treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : leafW < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx")))
          = some leafW) :
    lookupValue (forsLeafSetupStep st).bindings "node"
      = maskN (keccakWords [seed, leafW, wordOfHash16 sk]) := by
  let st1 : RuntimeState := { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
  let st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "secretVal" (wordOfHash16 sk) }
  let st3 : RuntimeState :=
    { st2 with bindings := bindValue st2.bindings "leafAdrs" leafW }
  let st4 : RuntimeState :=
    { st3 with
      world := { st3.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate st3.world.memory 0x20
          leafW } }
  let st5 : RuntimeState :=
    { st4 with
      world := { st4.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory 0x40
          (wordOfHash16 sk) } }
  have hm0' : (st5.world.memory 0).val = seed := by
    simpa [st5, st4, st3, st2, st1] using hm0
  have hm1' : (st5.world.memory 0x20).val = leafW := by
    simpa [st5, st4, st3, st2, st1, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS] using Nat.mod_eq_of_lt hAdrLt
  have hm2' : (st5.world.memory 0x40).val = wordOfHash16 sk := by
    simpa [st5, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      using Nat.mod_eq_of_lt hSkLt
  have hNode : evalExpr [] st5
        (andE (keccak 0x00 0x60) (u N_MASK))
      = some (maskN (keccakWords [seed, leafW, wordOfHash16 sk])) := by
    simpa [andE, keccak, u, SphincsMinusVerifiers.ClimbKit.N_MASK,
      SphincsMinusVerifierSpec.C13Concrete.nMask]
      using SphincsMinusVerifiers.InitialNodeKeccak.fors_leaf_node_eq
        st5 seed leafW (wordOfHash16 sk) hm0' hm1' hm2'
  unfold forsLeafSetupStep forsLeafSetupBody mstore
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ hTree)]
  change lookupValue
      (match execStmtList [] st1
        [ .letVar "secretVal"
            (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK)),
          .letVar "leafAdrs"
            (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx"))),
          .mstore (u 0x20) (v "leafAdrs"), .mstore (u 0x40) (v "secretVal"),
          .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
          .letVar "pathIdx" (v "treeIdx"),
          .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ] with
       | .continue s' => s'
       | _ => st).bindings "node" = _
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st1 "secretVal" _ _ hSecret)]
  change lookupValue
      (match execStmtList [] st2
        [ .letVar "leafAdrs"
            (orE (v "forsBase") (orE (shlE (u 19) (v "i")) (v "treeIdx"))),
          .mstore (u 0x20) (v "leafAdrs"), .mstore (u 0x40) (v "secretVal"),
          .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
          .letVar "pathIdx" (v "treeIdx"),
          .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ] with
       | .continue s' => s'
       | _ => st).bindings "node" = _
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st2 "leafAdrs" _ _ hLeaf)]
  change lookupValue
      (match execStmtList [] st3
        [ .mstore (u 0x20) (v "leafAdrs"), .mstore (u 0x40) (v "secretVal"),
          .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
          .letVar "pathIdx" (v "treeIdx"),
          .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ] with
       | .continue s' => s'
       | _ => st).bindings "node" = _
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st3 (u 0x20) (v "leafAdrs") 0x20
      leafW rfl rfl)]
  change lookupValue
      (match execStmtList [] st4
        [ .mstore (u 0x40) (v "secretVal"),
          .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
          .letVar "pathIdx" (v "treeIdx"),
          .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ] with
       | .continue s' => s'
       | _ => st).bindings "node" = _
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue st4 (u 0x40) (v "secretVal") 0x40
      (wordOfHash16 sk) rfl rfl)]
  change lookupValue
      (match execStmtList [] st5
        [ .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
          .letVar "pathIdx" (v "treeIdx"),
          .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ] with
       | .continue s' => s'
       | _ => st).bindings "node" = _
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st5 "node" _ _ hNode)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  simp only [execStmtList]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne _ "authPtr" "node" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne _ "pathIdx" "node" _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]

/-- Pure transformer for the inner Merkle climb statement (FIPS FORS address,
via the address-parametric `ClimbKit.stepForsMerkle`). -/
def forsLeafInnerStep (st : RuntimeState) : RuntimeState :=
  foldLoop "h" stepForsMerkle
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
    0 (wordNormalize 19)

/-- The inner Merkle climb statement always continues to `forsLeafInnerStep`. -/
theorem execForsLeafInner (st : RuntimeState) :
    execStmt [] st forsLeafInnerStmt = .continue (forsLeafInnerStep st) := by
  unfold forsLeafInnerStmt forsLeafInnerStep u
  exact ClimbLoop.execStmt_forEach_forsClimb "h" 19 st

/-- The inner Merkle climb does not modify the outer FORS loop binding `"i"`. -/
theorem forsLeafInner_preserves_i
    (st s' : RuntimeState)
    (h : execStmt [] st forsLeafInnerStmt = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  unfold forsLeafInnerStmt u at h
  refine SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
    "h" "i" (.literal 19)
    SphincsMinusVerifiers.ClimbKit.forsClimbBody
    st s' (by decide) ?_ h
  intro s s'' stmt hmem hexec
  simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
    SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "sibling" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "parentIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x20) _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "s" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      s s'' "node" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      s s'' "pathIdx" "i" _ (by decide) hexec

/-- Pure transformer for the final FORS root-array store. -/
def forsLeafStoreStep (st : RuntimeState) : RuntimeState :=
  match execStmt [] st forsLeafStoreStmt with
  | .continue s' => s'
  | _ => st

/-- The final root-array store always continues to `forsLeafStoreStep`. -/
theorem execForsLeafStore (st : RuntimeState) :
    execStmt [] st forsLeafStoreStmt = .continue (forsLeafStoreStep st) := by
  unfold forsLeafStoreStep forsLeafStoreStmt mstoreE u
  rw [execStmt_mstore_continue _ _ _ _ _ rfl rfl]

/-- The final FORS root-array store preserves `mem[0x00]` once its dynamic
offset is known not to alias zero.  This isolates the remaining arithmetic fact
about `0x80 + (i << 5)` from the generic mstore frame argument. -/
theorem forsLeafStore_preserves_seed_slot_of_offset
    (st s' : RuntimeState)
    (hOff : ∀ ro,
      evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) = some ro →
      0 ≠ ro)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
    st s' 0 (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") ?_
    (by simpa [forsLeafStoreStmt, mstoreE] using h)
  intro ro rv hoff _
  exact hOff ro hoff

/-- The final FORS root-array store does not modify the outer loop binding
`"i"`. -/
theorem forsLeafStore_preserves_i
    (st s' : RuntimeState)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
    st s' "i" (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node")
    (by simpa [forsLeafStoreStmt, mstoreE] using h)

/-- The whole FORS leaf body preserves the carried outer loop binding `"i"`.
This composes the straight-line setup frame, inner Merkle-climb frame, and final
root-array store frame without unfolding the pure `forsLeafStep`. -/
theorem forsLeafBody_preserves_i
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "i" _ (by decide) hexec
  · subst stmt
    exact forsLeafInner_preserves_i s s'' hexec
  · subst stmt
    exact forsLeafStore_preserves_i s s'' hexec

/-- The whole FORS leaf body preserves the carried signature base binding
`"sigBase"`.  The body reads it to form secret/auth-path calldata pointers, but
never writes it. -/
theorem forsLeafBody_preserves_sigBase
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    lookupValue s'.bindings "sigBase" = lookupValue st.bindings "sigBase" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigBase" forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "sigBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "sigBase" _ _ s s'' (by decide)
      (fun s s'' stmt hmem hexec => by
        simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
          SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hmem
        rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "sibling" "sigBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "parentIdx" "sigBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "sigBase" (u 0x20) _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "s" "sigBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "sigBase" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "sigBase" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "node" "sigBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "pathIdx" "sigBase" _ (by decide) hexec) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "sigBase" (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") hexec

/-- The whole FORS leaf body never rebinds the hoisted FIPS ADRS base
`"forsBase"` (bound once by the fors-setup segment, before the outer loop). -/
theorem forsLeafBody_preserves_forsBase
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    lookupValue s'.bindings "forsBase" = lookupValue st.bindings "forsBase" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "forsBase" forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "forsBase" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "forsBase" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "forsBase" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "forsBase" _ _ s s'' (by decide)
      (fun s s'' stmt hmem hexec => by
        simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
          SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hmem
        rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "sibling" "forsBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "parentIdx" "forsBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "forsBase" (u 0x20) _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "s" "forsBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "forsBase" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "forsBase" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "node" "forsBase" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "pathIdx" "forsBase" _ (by decide) hexec) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "forsBase" (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") hexec

/-- The whole FORS leaf body never rebinds the hoisted FIPS digit `"idxTree0"`. -/
theorem forsLeafBody_preserves_idxTree0
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    lookupValue s'.bindings "idxTree0" = lookupValue st.bindings "idxTree0" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "idxTree0" forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "idxTree0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "idxTree0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "idxTree0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "idxTree0" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "idxTree0" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "idxTree0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "idxTree0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "idxTree0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "idxTree0" _ _ s s'' (by decide)
      (fun s s'' stmt hmem hexec => by
        simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
          SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hmem
        rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "sibling" "idxTree0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "parentIdx" "idxTree0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "idxTree0" (u 0x20) _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "s" "idxTree0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "idxTree0" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "idxTree0" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "node" "idxTree0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "pathIdx" "idxTree0" _ (by decide) hexec) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "idxTree0" (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") hexec

/-- The whole FORS leaf body never rebinds the hoisted FIPS digit `"idxLeaf0"`. -/
theorem forsLeafBody_preserves_idxLeaf0
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    lookupValue s'.bindings "idxLeaf0" = lookupValue st.bindings "idxLeaf0" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "idxLeaf0" forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "idxLeaf0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "idxLeaf0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "idxLeaf0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "idxLeaf0" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "idxLeaf0" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "idxLeaf0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "idxLeaf0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "idxLeaf0" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "idxLeaf0" _ _ s s'' (by decide)
      (fun s s'' stmt hmem hexec => by
        simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
          SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hmem
        rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "sibling" "idxLeaf0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "parentIdx" "idxLeaf0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "idxLeaf0" (u 0x20) _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
            s s'' "s" "idxLeaf0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "idxLeaf0" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
            s s'' "idxLeaf0" _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "node" "idxLeaf0" _ (by decide) hexec
        · subst stmt
          exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
            s s'' "pathIdx" "idxLeaf0" _ (by decide) hexec) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "idxLeaf0" (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") hexec

/-- The whole FORS leaf body preserves the EVM selector and calldata image. -/
theorem forsLeafBody_preserves_selector_calldata
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata st s' := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "treeIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "secretVal" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "leafAdrs" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "node" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "pathIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      s s'' "authPtr" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "h" _ _ s s''
      (fun s s'' stmt hmem hexec => by
        simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
          SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hmem
        rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
            s s'' "sibling" _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
            s s'' "parentIdx" _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
            s s'' (u 0x20) _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
            s s'' "s" _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
            s s'' _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
            s s'' _ _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
            s s'' "node" _ hexec
        · subst stmt
          exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
            s s'' "pathIdx" _ hexec) hexec
  · subst stmt
    exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      s s'' (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") hexec

private theorem idxShl5_lt_six (idx : Nat) (hidx : idx < 6) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  calc idx * 2 ^ 5 ≤ 5 * 2 ^ 5 :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
    _ < 2 ^ 256 := by decide

private theorem storeOffset_lt_six (idx : Nat) (hidx : idx < 6) :
    0x80 + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : 0x80 + idx * 2 ^ 5 ≤ 0x80 + 5 * 2 ^ 5 :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)) _
  exact lt_of_le_of_lt hle (by decide)

/-- The final FORS store offset evaluates to the concrete root-array slot
`0x80 + 32*i` whenever the carried outer-loop binding `"i"` is the in-range
index `i < 6`. -/
theorem eval_forsLeafStore_offset
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) :
    evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
      = some (0x80 + 32 * idx) := by
  have h5 : evalExpr [] st (u 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hI : evalExpr [] st (v "i") = some idx := by
    show some (lookupValue st.bindings "i") = some idx
    rw [hi]
  have hsh : evalExpr [] st (shlE (u 5) (v "i")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded st (u 5) (v "i")
      5 idx h5 hI (by decide) (lt_trans hidx (by decide)) (idxShl5_lt_six idx hidx)
  have hbase : evalExpr [] st (u 0x80) = some 0x80 := by
    show some (wordNormalize 0x80) = some 0x80
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded st (u 0x80)
    (shlE (u 5) (v "i")) 0x80 (idx <<< 5) hbase hsh
    (by decide) (idxShl5_lt_six idx hidx) (storeOffset_lt_six idx hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

/-- The final FORS store offset cannot alias `0x00` over the real six-iteration
outer loop range. -/
theorem forsLeafStore_offset_ne_zero
    (st : RuntimeState) (idx ro : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hoff : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) = some ro) :
    0 ≠ ro := by
  rw [eval_forsLeafStore_offset st idx hidx hi] at hoff
  injection hoff with hro
  rw [← hro]
  omega

/-- Range-specialized final-store seed-cell frame: if the carried outer loop
binding is an executed FORS index `idx < 6`, then the final root-array store
preserves `mem[0x00]`. -/
theorem forsLeafStore_preserves_seed_slot_range
    (st s' : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact forsLeafStore_preserves_seed_slot_of_offset st s'
    (fun ro hoff => forsLeafStore_offset_ne_zero st idx ro hidx hi hoff) h

/-- The final FORS root-array store writes the current `"node"` binding to the
slot selected by the carried outer-loop index. -/
theorem forsLeafStore_root_cell_range
    (st s' : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    (s'.world.memory (0x80 + 32 * idx)).val =
      wordNormalize (lookupValue st.bindings "node") := by
  have hoff :
      evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
        = some (0x80 + 32 * idx) :=
    eval_forsLeafStore_offset st idx hidx hi
  have hval : evalExpr [] st (v "node") = some (lookupValue st.bindings "node") := rfl
  unfold forsLeafStoreStmt mstoreE at h
  change execStmt [] st
      (.mstore (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node")) =
        .continue s' at h
  rw [show execStmt [] st
        (.mstore (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node"))
        = (match evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))),
                 evalExpr [] st (v "node") with
           | some ro, some rv =>
               .continue { st with world := { st.world with
                   memory := fun o => if o = ro then rv else st.world.memory o } }
           | _, _ => .revert) from rfl] at h
  rw [hoff, hval] at h
  injection h with hs
  subst hs
  simp [wordNormalize]

/-- Distinct in-range FORS root-array indices select distinct scratch cells. -/
theorem fors_root_cell_ne_of_ne
    (j idx : Nat) (hne : j ≠ idx) :
    0x80 + 32 * j ≠ 0x80 + 32 * idx := by
  intro h
  exact hne (by omega)

/-- The final FORS root-array store preserves every other in-range root cell. -/
theorem forsLeafStore_preserves_root_cell_range_ne
    (st s' : RuntimeState) (j idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) (hne : j ≠ idx)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    (s'.world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
    st s' (0x80 + 32 * j) (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") ?_
    (by simpa [forsLeafStoreStmt, mstoreE] using h)
  intro ro rv hoff _
  rw [eval_forsLeafStore_offset st idx hidx hi] at hoff
  injection hoff with hro
  rw [← hro]
  exact fors_root_cell_ne_of_ne j idx hne

/-- The full statement 14: the FORS outer `forEach "i" (u 6)`. -/
def forsOuterStmt : Stmt := .forEach "i" (u 6) forsLeafBody

/-- Faithfulness: `forsOuterStmt` is *exactly* statement 14 of `c13VerifyBody`
(loop header and full body, inner `forEach` included). -/
theorem forsOuterStmt_eq_slice :
    [forsOuterStmt] = (c13VerifyBodyTail.drop 16).take 1 := rfl

/-! ## 3. The FORS outer-loop body step lemma. -/

/-- The pure transformer for one FORS outer-loop iteration: the `.continue`
payload of running `forsLeafBody`.  Total because every statement is a
`letVar`/`mstore`/total-`forEach` (the inner climb cannot revert). -/
def forsLeafStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsLeafBody with
  | .continue s' => s'
  | _ => st

set_option maxHeartbeats 4000000 in
/-- **`execForsLeaf`** — running the FORS outer-loop body over the real
interpreter continues to `forsLeafStep st`.  The leaf-setup prefix chains via
per-statement `.continue` lemmas; the inner Merkle climb is dispatched in one
rewrite by `execStmt_forEach_merkleClimb`; the suffix stores the leaf. -/
theorem execForsLeaf (st : RuntimeState) :
    execStmtList [] st forsLeafBody = .continue (forsLeafStep st) := by
  unfold forsLeafStep forsLeafBody mstore mstoreE u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (ClimbLoop.execStmt_forEach_forsClimb "h" 19 _)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- A full FORS leaf iteration never rebinds the digest word `"dVal"`.  The
setup prefix already exposes this fact; this version includes the inner Merkle
climb and final root-cell store so outer-loop prefixes can carry the S3 digest
alias without opening the body. -/
theorem forsLeafStep_preserves_dVal (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "dVal" = lookupValue st.bindings "dVal" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "dVal" forsLeafBody st (forsLeafStep st) ?_ (execForsLeaf st)
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstoreE] at hmem
  rcases hmem with
    hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "dVal" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "dVal" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "dVal" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "dVal" _ (by decide) hexec
  · subst stmt
    refine SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "dVal" (.literal 19)
      SphincsMinusVerifiers.ClimbKit.forsClimbBody
      s s'' (by decide) ?_ hexec
    intro t t'' inner hinner hinnerExec
    simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
      SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hinner
    rcases hinner with
      hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
        t t'' "sibling" "dVal" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
        t t'' "parentIdx" "dVal" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
        t t'' "dVal" _ _ hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
        t t'' "s" "dVal" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
        t t'' "dVal" _ _ hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
        t t'' "dVal" _ _ hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
        t t'' "node" "dVal" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
        t t'' "pathIdx" "dVal" _ (by decide) hinnerExec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "dVal" _ _ hexec

/-- A full FORS leaf iteration never rebinds the hypertree index `"htIdx"`.
This is the same binding-frame fact as `forsLeafStep_preserves_dVal`, specialized
to the S3 hypertree-index binding consumed by the later layer seed. -/
theorem forsLeafStep_preserves_htIdx (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "htIdx" = lookupValue st.bindings "htIdx" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "htIdx" forsLeafBody st (forsLeafStep st) ?_ (execForsLeaf st)
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstoreE] at hmem
  rcases hmem with
    hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "htIdx" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "htIdx" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "htIdx" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "htIdx" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "htIdx" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "htIdx" _ (by decide) hexec
  · subst stmt
    refine SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "h" "htIdx" (.literal 19)
      SphincsMinusVerifiers.ClimbKit.forsClimbBody
      s s'' (by decide) ?_ hexec
    intro t t'' inner hinner hinnerExec
    simp [SphincsMinusVerifiers.ClimbKit.forsClimbBody,
      SphincsMinusVerifiers.ClimbKit.merkleClimbBodyA] at hinner
    rcases hinner with
      hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
        t t'' "sibling" "htIdx" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
        t t'' "parentIdx" "htIdx" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
        t t'' "htIdx" _ _ hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
        t t'' "s" "htIdx" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
        t t'' "htIdx" _ _ hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
        t t'' "htIdx" _ _ hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
        t t'' "node" "htIdx" _ (by decide) hinnerExec
    · subst inner
      exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
        t t'' "pathIdx" "htIdx" _ (by decide) hinnerExec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "htIdx" _ _ hexec

/-- The final FORS store writes the post-inner-climb `"node"` value to the
root-array slot selected by the carried outer-loop index.  This is the local
store half of the six ordinary FORS root-cell correspondence; the remaining data
obligation is to identify that post-inner `"node"` with the spec tree root. -/
theorem forsLeafStep_root_cell_range
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) :
    ((forsLeafStep st).world.memory (0x80 + 32 * idx)).val =
      wordNormalize
        (lookupValue (forsLeafInnerStep (forsLeafSetupStep st)).bindings "node") := by
  have hbody : execStmtList [] st forsLeafBody = .continue (forsLeafStep st) :=
    execForsLeaf st
  rw [forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (forsLeafSetupStep st) forsLeafSetupBody [forsLeafInnerStmt, forsLeafStoreStmt]
      (execForsLeafSetup st)] at hbody
  have hInnerExec : execStmt [] (forsLeafSetupStep st) forsLeafInnerStmt =
      .continue (forsLeafInnerStep (forsLeafSetupStep st)) :=
    execForsLeafInner (forsLeafSetupStep st)
  rw [execStmtList_cons_continue _ _ _ [forsLeafStoreStmt] hInnerExec] at hbody
  have hStoreExec :
      execStmt [] (forsLeafInnerStep (forsLeafSetupStep st)) forsLeafStoreStmt =
        .continue (forsLeafStep st) := by
    simpa using hbody
  have hiSetup :
      lookupValue (forsLeafSetupStep st).bindings "i" = idx := by
    rw [forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue (forsLeafInnerStep (forsLeafSetupStep st)).bindings "i" = idx := by
    rw [forsLeafInner_preserves_i (forsLeafSetupStep st)
      (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec, hiSetup]
  exact forsLeafStore_root_cell_range
    (forsLeafInnerStep (forsLeafSetupStep st)) (forsLeafStep st) idx hidx hiInner hStoreExec

/-- If the setup prefix preserves the target root cell and the inner Merkle climb
does too, one leaf iteration preserves any *different* in-range root cell.  This
is the non-alias half needed to carry previously written ordinary roots through
later FORS iterations. -/
theorem forsLeafBody_preserves_root_cell_range_ne_of_inner
    (st s' : RuntimeState) (j idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) (hne : j ≠ idx)
    (hSetup : ((forsLeafSetupStep st).world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val)
    (hInner : ∀ (s s'' : RuntimeState),
      execStmt [] s forsLeafInnerStmt = .continue s'' →
      (s''.world.memory (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    (s'.world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  rw [forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (forsLeafSetupStep st) forsLeafSetupBody [forsLeafInnerStmt, forsLeafStoreStmt]
      (execForsLeafSetup st)] at h
  have hInnerExec : execStmt [] (forsLeafSetupStep st) forsLeafInnerStmt =
      .continue (forsLeafInnerStep (forsLeafSetupStep st)) :=
    execForsLeafInner (forsLeafSetupStep st)
  rw [execStmtList_cons_continue _ _ _ [forsLeafStoreStmt] hInnerExec] at h
  have hStoreExec :
      execStmt [] (forsLeafInnerStep (forsLeafSetupStep st)) forsLeafStoreStmt =
        .continue s' := by
    simpa using h
  have hiSetup :
      lookupValue (forsLeafSetupStep st).bindings "i" = idx := by
    rw [forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue (forsLeafInnerStep (forsLeafSetupStep st)).bindings "i" = idx := by
    rw [forsLeafInner_preserves_i (forsLeafSetupStep st)
      (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec, hiSetup]
  have hStoreRoot := forsLeafStore_preserves_root_cell_range_ne
    (forsLeafInnerStep (forsLeafSetupStep st)) s' j idx hidx hiInner hne hStoreExec
  have hInnerRoot := hInner (forsLeafSetupStep st)
    (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec
  rw [hStoreRoot, hInnerRoot, hSetup]

/-- Step-form non-alias root-cell frame for one FORS leaf iteration. -/
theorem forsLeafStep_preserves_root_cell_range_ne_of_inner
    (st : RuntimeState) (j idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) (hne : j ≠ idx)
    (hSetup : ((forsLeafSetupStep st).world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val)
    (hInner : ∀ (s s'' : RuntimeState),
      execStmt [] s forsLeafInnerStmt = .continue s'' →
      (s''.world.memory (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val) :
    ((forsLeafStep st).world.memory (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val :=
  forsLeafBody_preserves_root_cell_range_ne_of_inner
    st (forsLeafStep st) j idx hidx hi hne hSetup hInner (execForsLeaf st)

/-- Step-form binding frame for one FORS leaf iteration. -/
theorem forsLeafStep_preserves_i (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "i" = lookupValue st.bindings "i" :=
  forsLeafBody_preserves_i st (forsLeafStep st) (execForsLeaf st)

/-- Step-form binding frame for the signature base through one FORS leaf
iteration. -/
theorem forsLeafStep_preserves_sigBase (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "sigBase"
      = lookupValue st.bindings "sigBase" :=
  forsLeafBody_preserves_sigBase st (forsLeafStep st) (execForsLeaf st)

/-- Step-form FIPS ADRS-base binding frame for one FORS leaf iteration. -/
theorem forsLeafStep_preserves_forsBase (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "forsBase"
      = lookupValue st.bindings "forsBase" :=
  forsLeafBody_preserves_forsBase st (forsLeafStep st) (execForsLeaf st)

/-- Step-form FIPS digit binding frames for one FORS leaf iteration. -/
theorem forsLeafStep_preserves_idxTree0 (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "idxTree0"
      = lookupValue st.bindings "idxTree0" :=
  forsLeafBody_preserves_idxTree0 st (forsLeafStep st) (execForsLeaf st)

theorem forsLeafStep_preserves_idxLeaf0 (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "idxLeaf0"
      = lookupValue st.bindings "idxLeaf0" :=
  forsLeafBody_preserves_idxLeaf0 st (forsLeafStep st) (execForsLeaf st)

/-- Step-form selector/calldata frame for one FORS leaf iteration. -/
theorem forsLeafStep_preserves_selector_calldata (st : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata st (forsLeafStep st) :=
  forsLeafBody_preserves_selector_calldata st (forsLeafStep st) (execForsLeaf st)

/-- Conditional whole-leaf seed-cell frame.  Once the inner Merkle climb is known
to preserve `mem[0x00]`, setup and final-store preservation compose to show the
entire leaf body preserves the seed cell for the real outer range `idx < 6`. -/
theorem forsLeafBody_preserves_seed_slot_range_of_inner
    (st s' : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hInner : ∀ (s s'' : RuntimeState),
      execStmt [] s forsLeafInnerStmt = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  rw [forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (forsLeafSetupStep st) forsLeafSetupBody [forsLeafInnerStmt, forsLeafStoreStmt]
      (execForsLeafSetup st)] at h
  have hInnerExec : execStmt [] (forsLeafSetupStep st) forsLeafInnerStmt =
      .continue (forsLeafInnerStep (forsLeafSetupStep st)) :=
    execForsLeafInner (forsLeafSetupStep st)
  rw [execStmtList_cons_continue _ _ _ [forsLeafStoreStmt] hInnerExec] at h
  have hStoreExec :
      execStmt [] (forsLeafInnerStep (forsLeafSetupStep st)) forsLeafStoreStmt =
        .continue s' := by
    simpa using h
  have hiSetup :
      lookupValue (forsLeafSetupStep st).bindings "i" = idx := by
    rw [forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue (forsLeafInnerStep (forsLeafSetupStep st)).bindings "i" = idx := by
    rw [forsLeafInner_preserves_i (forsLeafSetupStep st)
      (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec, hiSetup]
  have hStoreSeed := forsLeafStore_preserves_seed_slot_range
    (forsLeafInnerStep (forsLeafSetupStep st)) s' idx hidx hiInner hStoreExec
  have hInnerSeed := hInner (forsLeafSetupStep st)
    (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec
  have hSetupSeed := forsLeafSetupStep_preserves_seed_slot st
  rw [hStoreSeed, hInnerSeed, hSetupSeed]

/-- Step-form conditional seed-cell frame for one FORS leaf iteration.  This is
the shape needed by callers that reason over `forsLeafStep`. -/
theorem forsLeafStep_preserves_seed_slot_range_of_inner
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hInner : ∀ (s s'' : RuntimeState),
      execStmt [] s forsLeafInnerStmt = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val) :
    ((forsLeafStep st).world.memory 0).val = (st.world.memory 0).val :=
  forsLeafBody_preserves_seed_slot_range_of_inner st (forsLeafStep st) idx hidx hi
    hInner (execForsLeaf st)

/-! ## 4. The outer-loop reduction (statement 14). -/

set_option maxHeartbeats 4000000 in
/-- **`execForsOuter`** — statement 14 (`forEach "i" (u 6)`) of `c13VerifyBody`
runs to the pure `foldLoop` over `forsLeafStep`, seeded by the `i := 0` bind. -/
theorem execForsOuter (st : RuntimeState) :
    execStmt [] st forsOuterStmt
      = .continue
          (foldLoop "i" forsLeafStep
            { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
            0 (wordNormalize 6)) :=
  ClimbLoop.execStmt_forEach_of_step "i" (u 6) forsLeafBody st (wordNormalize 6)
    forsLeafStep rfl execForsLeaf

set_option maxHeartbeats 4000000 in
/-- Outer-loop carry for an ordinary FORS root cell: after the six-iteration
outer fold, root slot `j` is exactly the value written by iteration `j`, provided
every later iteration preserves that slot.  The conclusion is still local to the
model state: the remaining data obligation is to identify the post-inner-climb
`"node"` with `forsAllRootsC13[j]`. -/
theorem forsOuter_root_cell_eq_iteration_node_of_suffix_preserves
    (st : RuntimeState) (j : Nat) (hj : j < 6)
    (hPres : ∀ (s : RuntimeState) (idx : Nat), j < idx → idx < 6 →
      ((forsLeafStep { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory
          (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val) :
    ((foldLoop "i" forsLeafStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 6)).world.memory (0x80 + 32 * j)).val =
      wordNormalize
        (lookupValue
          (forsLeafInnerStep
            (forsLeafSetupStep
              { (foldLoop "i" forsLeafStep
                  { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (foldLoop "i" forsLeafStep
                      { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") := by
  have hcarry := ClimbLoop.foldLoop_memory_val_eq_step_at_of_suffix_preserves
    "i" forsLeafStep (0x80 + 32 * j)
    { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6) j (by simpa using hj)
    (fun s idx hgt hlt => hPres s idx (by simpa using hgt) (by simpa using hlt))
  rw [hcarry]
  have hj256 : j < 2 ^ 256 := lt_trans hj (by decide)
  have hnormj : wordNormalize j = j := by
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hj256]
  have hi :
      lookupValue
          (bindValue
            (foldLoop "i" forsLeafStep
              { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
              0 j).bindings "i" (wordNormalize j))
          "i" = j := by
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self, hnormj]
  simpa [Nat.zero_add] using
    (forsLeafStep_root_cell_range
      { (foldLoop "i" forsLeafStep
          { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
          0 j) with
        bindings :=
          bindValue
            (foldLoop "i" forsLeafStep
              { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
              0 j).bindings "i" (wordNormalize j) }
      j hj hi)

/-- Statement-level range-gated FORS outer-loop seed-cell frame.  Callers only
need to prove the leaf body preserves `mem[0x00]` for concrete outer-loop
indices in the real six-iteration range. -/
theorem execForsOuter_preserves_seed_slot_range
    (st s' : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < wordNormalize 6 → ∀ (s'' : RuntimeState),
      execStmtList [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } forsLeafBody
        = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val)
    (h : execStmt [] st forsOuterStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
    "i" 0 (u 6) forsLeafBody (fun idx => idx < wordNormalize 6) st s' hLeaf
    (fun bound i hc _ hi => by
      unfold u at hc
      rw [show evalExpr [] st (.literal 6) = some (wordNormalize 6) from rfl] at hc
      injection hc with hbw
      have htarget : i < wordNormalize 6 := by
        rw [hbw]
        exact hi
      exact htarget)
    h

/-- Same statement-level FORS outer-loop seed-cell frame, exposed with the
natural six-iteration range used by the accept-path adapters. -/
theorem execForsOuter_preserves_seed_slot_range_six
    (st s' : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 → ∀ (s'' : RuntimeState),
      execStmtList [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } forsLeafBody
        = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val)
    (h : execStmt [] st forsOuterStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  execForsOuter_preserves_seed_slot_range st s'
    (fun s idx hidx s'' hexec => hLeaf s idx (by simpa using hidx) s'' hexec)
    h

/-! ## 5. Axiom audit. -/

#print axioms forsOuterStmt_eq_slice
#print axioms forsLeafBody_eq_segments
#print axioms execForsLeafSetup
#print axioms forsLeafSetup_preserves_seed_slot
#print axioms forsLeafSetup_preserves_root_cell_range
#print axioms forsLeafSetup_preserves_i
#print axioms forsLeafSetupStep_preserves_seed_slot
#print axioms forsLeafSetupStep_preserves_root_cell_range
#print axioms forsLeafSetupStep_preserves_i
#print axioms forsLeafSetup_preserves_sigBase
#print axioms forsLeafSetupStep_preserves_sigBase
#print axioms forsLeafSetup_preserves_dVal
#print axioms forsLeafSetupStep_preserves_dVal
#print axioms forsLeafStep_preserves_dVal
#print axioms forsLeafStep_preserves_htIdx
#print axioms forsLeafSetupStep_preserves_selector_calldata
#print axioms forsLeafSetupStep_authPtr_eq_sigDataOffset
#print axioms forsLeafSetupStep_pathIdx_lt
#print axioms forsLeafSetupStep_pathIdx_eq_of_eval
#print axioms forsLeafAdrs_eval_eq
#print axioms forsLeafAdrs_value_eq_spec
#print axioms forsLeafSetup_preserves_forsBase
#print axioms forsLeafSetupStep_preserves_forsBase
#print axioms forsLeafSetupStep_node_eq_spec_of_eval
#print axioms execForsLeafInner
#print axioms forsLeafInner_preserves_i
#print axioms execForsLeafStore
#print axioms forsLeafStore_preserves_seed_slot_of_offset
#print axioms forsLeafStore_preserves_i
#print axioms forsLeafBody_preserves_i
#print axioms forsLeafBody_preserves_sigBase
#print axioms forsLeafBody_preserves_forsBase
#print axioms forsLeafStep_preserves_forsBase
#print axioms forsLeafStep_preserves_idxTree0
#print axioms forsLeafStep_preserves_idxLeaf0
#print axioms forsLeafBody_preserves_selector_calldata
#print axioms forsLeafStep_preserves_i
#print axioms forsLeafStep_preserves_sigBase
#print axioms forsLeafStep_preserves_selector_calldata
#print axioms forsLeafBody_preserves_seed_slot_range_of_inner
#print axioms forsLeafStep_preserves_seed_slot_range_of_inner
#print axioms eval_forsLeafStore_offset
#print axioms forsLeafStore_offset_ne_zero
#print axioms forsLeafStore_preserves_seed_slot_range
#print axioms forsLeafStore_root_cell_range
#print axioms fors_root_cell_ne_of_ne
#print axioms forsLeafStore_preserves_root_cell_range_ne
#print axioms forsLeafStep_root_cell_range
#print axioms forsLeafBody_preserves_root_cell_range_ne_of_inner
#print axioms forsLeafStep_preserves_root_cell_range_ne_of_inner
#print axioms execForsLeaf
#print axioms execForsOuter
#print axioms forsOuter_root_cell_eq_iteration_node_of_suffix_preserves
#print axioms execForsOuter_preserves_seed_slot_range
#print axioms execForsOuter_preserves_seed_slot_range_six

end SphincsMinusVerifiers.SegmentS4Fors
