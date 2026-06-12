/-
  C13AddressArithmetic — lightweight arithmetic facts for C13 WOTS-PK
  addresses.

  This file intentionally avoids the layer-body and WOTS/copy-loop modules.  It
  contains only expression evaluation and normalization lemmas for the
  layer/tree/leaf WOTS-PK address word.
-/

import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.C13AddressArithmetic

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr)

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b

def wotsPkAdrsExpr : Expr :=
  orE (shlE (u 224) (v "layer"))
    (orE (shlE (u 128) (v "idxTree"))
      (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf"))))

theorem evalExpr_wotsPkAdrs_eq_of_layer_idxTree_idxLeaf
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
  unfold wotsPkAdrsExpr orE shlE u v
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
          (.shl (.literal 64) (.localVar "idxLeaf"))))
      (layer <<< 224)
      ((idxTree <<< 128) ||| (((1 : Nat) <<< 96) ||| (idxLeaf <<< 64)))
      h224 hinner h224lt hinnerLt
  rw [hfull]
  simp [SphincsMinusVerifierSpec.C13Concrete.adrsWotsPk, Nat.lor_assoc]

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
    SphincsMinusVerifiers.SegmentS2.wordNormalize_of_lt haddr

#print axioms evalExpr_wotsPkAdrs_eq_of_layer_idxTree_idxLeaf
#print axioms adrsWotsPk_wordNormalize_of_bounds

end SphincsMinusVerifiers.C13AddressArithmetic
