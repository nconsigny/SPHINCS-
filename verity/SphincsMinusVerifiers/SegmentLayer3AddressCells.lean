/-
  SegmentLayer3AddressCells — lightweight C13 WOTS-PK address cutpoints.

  This module deliberately avoids importing `SegmentLayer3`.  It exposes the
  post-digit-to-before-WOTS-PK prefix over an already-materialized post-digit
  state, parallel to `SegmentLayer3CopyCells`, so C13 residuals can ask only for
  the exact address/copy facts they need instead of rebuilding the full layer
  body.
-/

import SphincsMinusVerifiers.SegmentLayer3CopyCells
import SphincsMinusVerifiers.C13AddressArithmetic

namespace SphincsMinusVerifiers.SegmentLayer3AddressCells

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val

/-- Lightweight WOTS-PK-address expression for the C13 layer body. -/
def wotsPkAdrsExpr : Expr :=
  orE (shlE (u 224) (v "layer"))
    (orE (shlE (u 128) (v "idxTree"))
      (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf"))))

/-- Prefix from the post-digit state through the WOTS outer loop and WOTS-PK
address store, stopping before the final 43-cell copy loop. -/
def suffixBeforeWotsPkCopyFrom : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (.literal 43) SegmentLayer3CopyCells.wotsOuterBody
  , .letVar "pkAdrs" wotsPkAdrsExpr
  , mstore 0x20 (v "pkAdrs") ]

/-- Full prefix from the post-digit state through the WOTS outer loop, address
store, and final 43-cell WOTS-PK copy loop. -/
def suffixBeforeWotsPkFrom : List Stmt :=
  suffixBeforeWotsPkCopyFrom ++
    [ .forEach "i" (.literal 43) SegmentLayer3CopyCells.copyBody ]

def beforeWotsPkWotsPtrFrom (afterDigit : RuntimeState) : RuntimeState :=
  { afterDigit with
    bindings := bindValue afterDigit.bindings "wotsPtr"
      ((evalExpr [] afterDigit
        (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0) }

def beforeWotsPkAfterWotsFrom (afterDigit : RuntimeState) : RuntimeState :=
  ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
    { (beforeWotsPkWotsPtrFrom afterDigit) with
      bindings := bindValue (beforeWotsPkWotsPtrFrom afterDigit).bindings "i" (wordNormalize 0) }
    0 43

def suffixWotsPkAddressStoreFrom : List Stmt :=
  [ .letVar "pkAdrs" wotsPkAdrsExpr
  , mstore 0x20 (v "pkAdrs") ]

def suffixWotsPkCopyFrom : List Stmt :=
  [ .forEach "i" (.literal 43) SegmentLayer3CopyCells.copyBody ]

def beforeWotsPkCopyAfterWotsFrom (afterDigit : RuntimeState) : RuntimeState :=
  match execStmtList [] (beforeWotsPkAfterWotsFrom afterDigit)
      suffixWotsPkAddressStoreFrom with
  | .continue s' => s'
  | _ => afterDigit

def beforeWotsPkAfterWotsCopyFrom (afterDigit : RuntimeState) : RuntimeState :=
  match execStmtList [] (beforeWotsPkCopyAfterWotsFrom afterDigit)
      suffixWotsPkCopyFrom with
  | .continue s' => s'
  | _ => afterDigit

def beforeWotsPkCopyFrom (afterDigit : RuntimeState) : RuntimeState :=
  match execStmtList [] afterDigit suffixBeforeWotsPkCopyFrom with
  | .continue s' => s'
  | _ => afterDigit

def beforeWotsPkFrom (afterDigit : RuntimeState) : RuntimeState :=
  match execStmtList [] afterDigit suffixBeforeWotsPkFrom with
  | .continue s' => s'
  | _ => afterDigit

/-- The prefix through the WOTS-PK address store always continues. -/
theorem beforeWotsPkCopyFrom_eq (afterDigit : RuntimeState) :
    execStmtList [] afterDigit suffixBeforeWotsPkCopyFrom =
      .continue (beforeWotsPkCopyFrom afterDigit) := by
  unfold beforeWotsPkCopyFrom suffixBeforeWotsPkCopyFrom mstore u
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.wotsOuterBody _ _
      SegmentLayer3CopyCells.wotsOuterStep rfl
      SegmentLayer3CopyCells.wotsOuterStepLemma)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- The full prefix through the WOTS-PK copy loop always continues. -/
theorem beforeWotsPkFrom_eq (afterDigit : RuntimeState) :
    execStmtList [] afterDigit suffixBeforeWotsPkFrom =
      .continue (beforeWotsPkFrom afterDigit) := by
  unfold beforeWotsPkFrom suffixBeforeWotsPkFrom
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (beforeWotsPkCopyFrom_eq afterDigit)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ []
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.copyBody _ _
      SegmentLayer3CopyCells.copyStep rfl
      SegmentLayer3CopyCells.copyStepLemma)]
  rfl

theorem beforeWotsPkCopyAfterWotsFrom_eq (afterDigit : RuntimeState) :
    execStmtList [] (beforeWotsPkAfterWotsFrom afterDigit)
      suffixWotsPkAddressStoreFrom =
      .continue (beforeWotsPkCopyAfterWotsFrom afterDigit) := by
  unfold beforeWotsPkCopyAfterWotsFrom suffixWotsPkAddressStoreFrom mstore u
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

theorem beforeWotsPkAfterWotsCopyFrom_eq (afterDigit : RuntimeState) :
    execStmtList [] (beforeWotsPkCopyAfterWotsFrom afterDigit)
      suffixWotsPkCopyFrom =
      .continue (beforeWotsPkAfterWotsCopyFrom afterDigit) := by
  unfold beforeWotsPkAfterWotsCopyFrom suffixWotsPkCopyFrom
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ []
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.copyBody _ _
      SegmentLayer3CopyCells.copyStep rfl
      SegmentLayer3CopyCells.copyStepLemma)]
  rfl

/-- The folded WOTS outer loop preserves any binding not written by the loop
body or its inner chain loop. -/
theorem beforeWotsPkAfterWots_lookup_of_ne
    (afterDigit : RuntimeState) (key : String)
    (hneI : "i" ≠ key)
    (hneWotsPtr : "wotsPtr" ≠ key)
    (hneDigit : "digit" ≠ key) (hneSteps : "steps" ≠ key)
    (hneVal : "val" ≠ key) (hneChainBase : "chainBase" ≠ key)
    (hneStep : "step" ≠ key) :
    lookupValue (beforeWotsPkAfterWotsFrom afterDigit).bindings key =
      lookupValue afterDigit.bindings key := by
  unfold beforeWotsPkAfterWotsFrom
  rw [ClimbLoop.foldLoop_preserves_lookup "i" key
    SegmentLayer3CopyCells.wotsOuterStep hneI
    (fun s => SegmentLayer3CopyCells.wotsOuterStep_preserves_lookup_of_ne
      s key hneDigit hneSteps hneVal hneChainBase hneStep)
    { beforeWotsPkWotsPtrFrom afterDigit with
      bindings := bindValue (beforeWotsPkWotsPtrFrom afterDigit).bindings
        "i" (wordNormalize 0) }
    0 43]
  unfold beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" key _ hneI]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" key _ hneWotsPtr]

/-- WOTS-PK-address expression evaluation, imported from the tiny arithmetic
module so this prefix module does not elaborate that proof next to the WOTS
loop/copy machinery. -/
theorem evalExpr_pkAdrs_eq_of_layer_idxTree_idxLeaf
    (st : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue st.bindings "layer" = layer)
    (hIdxTree : lookupValue st.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue st.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    evalExpr [] st wotsPkAdrsExpr =
      some (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf) := by
  change evalExpr [] st C13AddressArithmetic.wotsPkAdrsExpr =
    some (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk layer idxTree idxLeaf)
  exact C13AddressArithmetic.evalExpr_wotsPkAdrs_eq_of_layer_idxTree_idxLeaf
    st layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
    hLayerLt hIdxTreeLt hIdxLeafLt

theorem beforeWotsPkAfterWots_eval_pkAdrs_eq_of_bindings
    (afterDigit : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue afterDigit.bindings "layer" = layer)
    (hIdxTree : lookupValue afterDigit.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue afterDigit.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    evalExpr [] (beforeWotsPkAfterWotsFrom afterDigit) wotsPkAdrsExpr =
      some (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf) := by
  exact evalExpr_pkAdrs_eq_of_layer_idxTree_idxLeaf
    (beforeWotsPkAfterWotsFrom afterDigit) layer idxTree idxLeaf
    (by
      rw [beforeWotsPkAfterWots_lookup_of_ne afterDigit "layer"
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hLayer)
    (by
      rw [beforeWotsPkAfterWots_lookup_of_ne afterDigit "idxTree"
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hIdxTree)
    (by
      rw [beforeWotsPkAfterWots_lookup_of_ne afterDigit "idxLeaf"
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hIdxLeaf)
    hLayerLt hIdxTreeLt hIdxLeafLt

/-- The assembled WOTS-PK address is already an EVM word under the C13 component
bounds. -/
theorem adrsWotsPk_wordNormalize_of_bounds
    (layer idxTree idxLeaf : Nat)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    wordNormalize
        (SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
          layer idxTree idxLeaf) =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf :=
  C13AddressArithmetic.adrsWotsPk_wordNormalize_of_bounds
    layer idxTree idxLeaf hLayerLt hIdxTreeLt hIdxLeafLt

theorem beforeWotsPkFrom_memory_0x20_eq_beforeWotsPkCopyFrom
    (afterDigit : RuntimeState) :
    ((beforeWotsPkFrom afterDigit).world.memory 0x20).val =
      ((beforeWotsPkCopyFrom afterDigit).world.memory 0x20).val := by
  unfold beforeWotsPkFrom suffixBeforeWotsPkFrom
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (beforeWotsPkCopyFrom_eq afterDigit)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ []
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.copyBody _ _
      SegmentLayer3CopyCells.copyStep rfl
      SegmentLayer3CopyCells.copyStepLemma)]
  rw [show wordNormalize 43 = 43 by rfl]
  simp only [execStmtList]
  rw [SegmentLayer3CopyCells.copyFold43_preserves_memory_0x20]

theorem beforeWotsPkAfterWotsCopyFrom_memory_0x20_eq_beforeCopy
    (afterDigit : RuntimeState) :
    ((beforeWotsPkAfterWotsCopyFrom afterDigit).world.memory 0x20).val =
      ((beforeWotsPkCopyAfterWotsFrom afterDigit).world.memory 0x20).val := by
  unfold beforeWotsPkAfterWotsCopyFrom suffixWotsPkCopyFrom
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ []
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.copyBody _ _
      SegmentLayer3CopyCells.copyStep rfl
      SegmentLayer3CopyCells.copyStepLemma)]
  rw [show wordNormalize 43 = 43 by rfl]
  simp only [execStmtList]
  rw [SegmentLayer3CopyCells.copyFold43_preserves_memory_0x20]

/-- The lightweight prefix before `"wotsPk"` preserves seed cell `0x00`. -/
theorem beforeWotsPkFrom_preserves_memory_zero
    (afterDigit : RuntimeState) :
    ((beforeWotsPkFrom afterDigit).world.memory 0x00).val =
      (afterDigit.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 suffixBeforeWotsPkFrom afterDigit (beforeWotsPkFrom afterDigit) ?_
    (beforeWotsPkFrom_eq afterDigit)
  intro s s'' stmt hmem hexec
  simp [suffixBeforeWotsPkFrom, suffixBeforeWotsPkCopyFrom, mstore] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "wotsPtr" _ hexec
  · exact SegmentLayer3CopyCells.wotsOuterForEach_preserves_memory_zero
      s s'' hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0x00 "pkAdrs" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 _ _ ?_ hexec
    intro ro rv hoff _
    cases hoff
    decide
  · exact SegmentLayer3CopyCells.copyForEach_preserves_memory_zero
      s s'' hexec

theorem beforeWotsPkCopyAfterWotsFrom_memory_0x20_eq_of_bindings
    (afterDigit : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue afterDigit.bindings "layer" = layer)
    (hIdxTree : lookupValue afterDigit.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue afterDigit.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    ((beforeWotsPkCopyAfterWotsFrom afterDigit).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  have hEval :=
    beforeWotsPkAfterWots_eval_pkAdrs_eq_of_bindings
      afterDigit layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
      hLayerLt hIdxTreeLt hIdxLeafLt
  unfold beforeWotsPkCopyAfterWotsFrom suffixWotsPkAddressStoreFrom mstore u
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "pkAdrs" _ _ hEval)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  simp only [execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [show wordNormalize 32 = 32 by rfl]
  rw [MemoryKit.memUpdate_val_same]
  exact adrsWotsPk_wordNormalize_of_bounds
    layer idxTree idxLeaf hLayerLt hIdxTreeLt hIdxLeafLt

theorem beforeWotsPkAfterWotsCopyFrom_memory_0x20_eq_of_bindings
    (afterDigit : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue afterDigit.bindings "layer" = layer)
    (hIdxTree : lookupValue afterDigit.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue afterDigit.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    ((beforeWotsPkAfterWotsCopyFrom afterDigit).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  rw [beforeWotsPkAfterWotsCopyFrom_memory_0x20_eq_beforeCopy]
  exact beforeWotsPkCopyAfterWotsFrom_memory_0x20_eq_of_bindings
    afterDigit layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
    hLayerLt hIdxTreeLt hIdxLeafLt

/-- State bridge: the pre-copy WOTS-PK cutpoint built by running the whole
`suffixBeforeWotsPkCopyFrom` statement list on `afterDigit` is the *same* state
reached by folding the WOTS outer loop first (`beforeWotsPkAfterWotsFrom`) and
then running only the address-store suffix.  Proven by reducing the two leading
statements (the `wotsPtr` binding and the `forEach`→`foldLoop` step) without
unfolding the 43 loop iterations, so the heavy prefix never elaborates. -/
theorem beforeWotsPkCopyFrom_eq_afterWots (afterDigit : RuntimeState) :
    beforeWotsPkCopyFrom afterDigit = beforeWotsPkCopyAfterWotsFrom afterDigit := by
  have hbridge :
      execStmtList [] afterDigit suffixBeforeWotsPkCopyFrom =
        execStmtList [] (beforeWotsPkAfterWotsFrom afterDigit)
          suffixWotsPkAddressStoreFrom := by
    unfold suffixBeforeWotsPkCopyFrom mstore u
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
        SegmentLayer3CopyCells.wotsOuterBody _ _
        SegmentLayer3CopyCells.wotsOuterStep rfl
        SegmentLayer3CopyCells.wotsOuterStepLemma)]
    rfl
  rw [beforeWotsPkCopyFrom_eq afterDigit,
    beforeWotsPkCopyAfterWotsFrom_eq afterDigit] at hbridge
  injection hbridge

/-- Narrow bridge, now discharged: at the lightweight pre-copy WOTS-PK cutpoint,
cell `0x20` contains the address assembled from the post-digit
layer/tree/leaf bindings.  Routed through `beforeWotsPkCopyFrom_eq_afterWots` to
the already-framed `beforeWotsPkCopyAfterWotsFrom` proof, so no WOTS outer loop
iteration is ever unfolded. -/
theorem beforeWotsPkCopyFrom_memory_0x20_eq_of_bindings
    (afterDigit : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue afterDigit.bindings "layer" = layer)
    (hIdxTree : lookupValue afterDigit.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue afterDigit.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    ((beforeWotsPkCopyFrom afterDigit).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  rw [beforeWotsPkCopyFrom_eq_afterWots]
  exact beforeWotsPkCopyAfterWotsFrom_memory_0x20_eq_of_bindings
    afterDigit layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
    hLayerLt hIdxTreeLt hIdxLeafLt

theorem beforeWotsPkFrom_memory_0x20_eq_of_bindings
    (afterDigit : RuntimeState) (layer idxTree idxLeaf : Nat)
    (hLayer : lookupValue afterDigit.bindings "layer" = layer)
    (hIdxTree : lookupValue afterDigit.bindings "idxTree" = idxTree)
    (hIdxLeaf : lookupValue afterDigit.bindings "idxLeaf" = idxLeaf)
    (hLayerLt : layer < 2 ^ 32)
    (hIdxTreeLt : idxTree < 2 ^ 32)
    (hIdxLeafLt : idxLeaf < 2 ^ 32) :
    ((beforeWotsPkFrom afterDigit).world.memory 0x20).val =
      SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk
        layer idxTree idxLeaf := by
  rw [beforeWotsPkFrom_memory_0x20_eq_beforeWotsPkCopyFrom]
  exact beforeWotsPkCopyFrom_memory_0x20_eq_of_bindings
    afterDigit layer idxTree idxLeaf hLayer hIdxTree hIdxLeaf
    hLayerLt hIdxTreeLt hIdxLeafLt

#print axioms beforeWotsPkCopyFrom_memory_0x20_eq_of_bindings
#print axioms beforeWotsPkFrom_memory_0x20_eq_of_bindings

end SphincsMinusVerifiers.SegmentLayer3AddressCells
