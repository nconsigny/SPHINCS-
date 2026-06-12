/-
  SegmentS4ForsMerkleFrame — lightweight adapters connecting the S4 FORS inner
  climb statement to the generic Merkle memory-frame loop adapters, on the
  FIPS 205 §11.2.2 FORS address layout.

  The FORS inner climb is `forEach "h" (u 19) ClimbKit.forsClimbBody` — the
  address-parametric `merkleClimbBodyA` instantiated at `ClimbKit.forsAdrs`
  (`or(forsBase, or(shl(32, add(h,1)), or(shl(sub(18,h), i), parentIdx)))`).
  Unlike the retired pre-FIPS layout, the per-level address depends on the
  outer loop binding `"i"`, so the frame-carrying node-correspondence lemmas
  thread `"i"` alongside the `MerkleClimbFrame` invariant.

  This file intentionally sits outside `SegmentS4Fors`: it imports the heavier
  `ClimbMemFrameMerkle` module without adding that import to the core S4 segment
  module.  The lemmas here are standalone bridge bricks; they do not touch
  `execC13` or `c13_refines_byte_spec`.  No `sorry`, no new `axiom`, no
  `native_decide`.
-/

import SphincsMinusVerifiers.SegmentS4Fors
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers.SegmentS4ForsMerkleFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (stepForsMerkle forsAdrs N_MASK)
open SphincsMinusVerifierSpec.C13Concrete
  (adrsForsBase adrsForsLeaf adrsForsNode maskN keccakWords wordOfHash16)

/-- Frozen C13 FORS Merkle-site facts for one outer tree `t`: static
selector/calldata, fixed auth pointer, a bounded ADRS-base witness, and bounded
moving `pathIdx`.  (The FIPS per-level address also reads `"i"`, but the
interpreter's address expression is total, so the *memory-frame* half of this
file never needs its value; only the node-correspondence lemmas thread `"i"`.) -/
def ForsFrozenSite
    (t : Nat) (pkSeed pkRoot message sig : ByteArray) (s : RuntimeState) : Prop :=
  ∃ base,
    s.selector = 0 ∧
    s.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
    lookupValue s.bindings "authPtr"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
    lookupValue s.bindings "forsBase" = base ∧
    base < 2 ^ 256 ∧
    lookupValue s.bindings "pathIdx" < 2 ^ 256

/-! ## 1. The FIPS FORS per-level address word.

`ClimbKit.forsAdrs` is total on the interpreter (`ClimbKit.adrsEval_fors`), so
memory-frame lemmas get their `vadr` witness for free.  For the
node-correspondence half we additionally *identify* the value: given the
carried bindings it is the right-associated OR image of the spec
`adrsForsNode` (re-associated by `ClimbStepSpec.forsBase_node_address`). -/

private theorem hShl32_lt (idx : Nat) (hidx : idx < 19) :
    (idx + 1) <<< 32 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right (2 ^ 32) (Nat.succ_le_of_lt hidx))
    (by decide : 19 * 2 ^ 32 < 2 ^ 256)

private theorem iShl18_lt (i idx : Nat) (hi : i < 6) (hidx : idx < 19) :
    i <<< (18 - idx) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  calc
    i * 2 ^ (18 - idx) ≤ 5 * 2 ^ 18 :=
      Nat.mul_le_mul (Nat.le_of_lt_succ hi)
        (Nat.pow_le_pow_right (by decide) (by omega))
    _ < 2 ^ 256 := by decide

/-- The FIPS FORS per-level address value is a bounded EVM word. -/
theorem forsAdrs_value_lt
    (base i idx p : Nat)
    (hbaseLt : base < 2 ^ 256) (hi : i < 6) (hidx : idx < 19)
    (hpLt : p < 2 ^ 256) :
    base ||| (((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| p)) < 2 ^ 256 := by
  have h1 : (i <<< (18 - idx)) ||| p < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (iShl18_lt i idx hi hidx) hpLt
  have h2 : ((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| p) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (hShl32_lt idx hidx) h1
  exact Nat.bitwise_lt_two_pow hbaseLt h2

/-- **`forsAdrs_eval_eq`** — the FIPS FORS per-level address expression
evaluates to the right-associated OR of its four carried components.  This is
the FORS analogue of `ClimbKeccakStep.evalExpr_merkleAdrsWord`, with the extra
`shl(sub(18, h), i)` tree-number fold. -/
theorem forsAdrs_eval_eq
    (st : RuntimeState) {base i idx p : Nat}
    (hbase : lookupValue st.bindings "forsBase" = base) (hbaseLt : base < 2 ^ 256)
    (hh : lookupValue st.bindings "h" = idx) (hidx : idx < 19)
    (hi : lookupValue st.bindings "i" = i) (hiLt : i < 6)
    (hp : lookupValue st.bindings "parentIdx" = p) (hpLt : p < 2 ^ 256) :
    evalExpr [] st forsAdrs
      = some (base ||| (((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| p))) := by
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hbaseEval : evalExpr [] st (.localVar "forsBase") = some base := by
    show some (lookupValue st.bindings "forsBase") = some base
    rw [hbase]
  have hhEval : evalExpr [] st (.localVar "h") = some idx := by
    show some (lookupValue st.bindings "h") = some idx
    rw [hh]
  have hiEval : evalExpr [] st (.localVar "i") = some i := by
    show some (lookupValue st.bindings "i") = some i
    rw [hi]
  have hpEval : evalExpr [] st (.localVar "parentIdx") = some p := by
    show some (lookupValue st.bindings "parentIdx") = some p
    rw [hp]
  have hlit1 : evalExpr [] st (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hlit18 : evalExpr [] st (.literal 18) = some 18 := by
    show some (wordNormalize 18) = some 18
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hlit32 : evalExpr [] st (.literal 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  -- shl(32, add(h, 1)) ↦ (idx + 1) <<< 32
  have hplus : evalExpr [] st (.add (.localVar "h") (.literal 1)) = some (idx + 1) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (.localVar "h") (.literal 1) idx 1 hhEval hlit1 hidx256 (by decide)
      (by omega)
  have hsh32 : evalExpr [] st (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      = some ((idx + 1) <<< 32) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 32) (.add (.localVar "h") (.literal 1)) 32 (idx + 1)
      hlit32 hplus (by decide) (by omega) (hShl32_lt idx hidx)
  -- shl(sub(18, h), i) ↦ i <<< (18 - idx)
  have hsub : evalExpr [] st (.sub (.literal 18) (.localVar "h")) = some (18 - idx) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_sub_bounded
      st (.literal 18) (.localVar "h") 18 idx hlit18 hhEval (by decide) hidx256
      (by omega)
  have hshi : evalExpr [] st (.shl (.sub (.literal 18) (.localVar "h")) (.localVar "i"))
      = some (i <<< (18 - idx)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.sub (.literal 18) (.localVar "h")) (.localVar "i") (18 - idx) i
      hsub hiEval (by omega) (lt_trans hiLt (by decide)) (iShl18_lt i idx hiLt hidx)
  -- inner OR: shl(sub(18,h), i) ||| parentIdx
  have hinner1 : evalExpr [] st
      (.bitOr (.shl (.sub (.literal 18) (.localVar "h")) (.localVar "i"))
        (.localVar "parentIdx"))
      = some ((i <<< (18 - idx)) ||| p) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st _ _ _ _ hshi hpEval (iShl18_lt i idx hiLt hidx) hpLt
  have hinner1Lt : (i <<< (18 - idx)) ||| p < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (iShl18_lt i idx hiLt hidx) hpLt
  -- middle OR: shl(32, h+1) ||| (…)
  have hinner2 : evalExpr [] st
      (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
        (.bitOr (.shl (.sub (.literal 18) (.localVar "h")) (.localVar "i"))
          (.localVar "parentIdx")))
      = some (((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| p)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st _ _ _ _ hsh32 hinner1 (hShl32_lt idx hidx) hinner1Lt
  have hinner2Lt : ((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| p) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (hShl32_lt idx hidx) hinner1Lt
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    st _ _ _ _ hbaseEval hinner2 hbaseLt hinner2Lt

/-! ## 2. Per-step memory frames (seed cell, ordinary root cells).

The FIPS address expression is total, so unlike the pre-FIPS file no `vadr`
hypothesis is threaded: the witness comes from `ClimbKit.adrsEval_fors`. -/

/-- One FIPS FORS Merkle step preserves the seed cell `mem[0x00]`, given only
the moving-index bound and the masked sibling calldata read. -/
theorem stepFors_preserves_seed_slot_of_s4_eval
    (s : RuntimeState) (idx mIdx vsib : Nat)
    (hpath : lookupValue s.bindings "pathIdx" = mIdx)
    (hmlt : mIdx < 2 ^ 256)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
          = some vsib) :
    ((stepForsMerkle
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let vadr : Nat := SphincsMinusVerifiers.ClimbKit.adrsEval_fors.val st2
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
    exact hpath
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hmlt
  have h3 : evalExpr [] st2 forsAdrs = some vadr :=
    SphincsMinusVerifiers.ClimbKit.adrsEval_fors.eval st2
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hmlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") =
      some (lookupValue st5.bindings "sibling") := by
    rfl
  have hpar : mIdx % 2 = 0 ∨ mIdx % 2 = 1 := by
    have hlt : mIdx % 2 < 2 := Nat.mod_lt mIdx (by decide)
    omega
  have hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even mIdx hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd mIdx hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  show ((SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs
      stH).world.memory 0).val = (stH.world.memory 0).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_mem_zero_val_of_parity
    "node" "pathIdx" "authPtr" forsAdrs stH
    vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
    mIdx hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- One FIPS FORS Merkle step preserves ordinary FORS root cells.  These root
slots live at `0x80 + 32*j`, so they cannot alias the Merkle scratch cells
`0x20`, `0x40`, or `0x60` used by one branchless climb step. -/
theorem stepFors_preserves_root_cell_of_s4_eval
    (s : RuntimeState) (j idx mIdx vsib : Nat)
    (hpath : lookupValue s.bindings "pathIdx" = mIdx)
    (hmlt : mIdx < 2 ^ 256)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
          = some vsib) :
    ((stepForsMerkle
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let vadr : Nat := SphincsMinusVerifiers.ClimbKit.adrsEval_fors.val st2
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
    exact hpath
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hmlt
  have h3 : evalExpr [] st2 forsAdrs = some vadr :=
    SphincsMinusVerifiers.ClimbKit.adrsEval_fors.eval st2
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hmlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") =
      some (lookupValue st5.bindings "sibling") := by
    rfl
  have hpar : mIdx % 2 = 0 ∨ mIdx % 2 = 1 := by
    have hlt : mIdx % 2 < 2 := Nat.mod_lt mIdx (by decide)
    omega
  have hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even mIdx hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd mIdx hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  have h20 : 0x80 + 32 * j ≠ 0x20 := by omega
  have ho5 : 0x80 + 32 * j ≠ o5 := by
    rcases hparOff with ⟨_, ho5, _⟩ | ⟨_, ho5, _⟩ <;> rw [ho5] <;> omega
  have ho6 : 0x80 + 32 * j ≠ o6 := by
    rcases hparOff with ⟨_, _, ho6⟩ | ⟨_, _, ho6⟩ <;> rw [ho6] <;> omega
  show ((SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs
      stH).world.memory (0x80 + 32 * j)).val = (stH.world.memory (0x80 + 32 * j)).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_mem_val_of_ne
    "node" "pathIdx" "authPtr" forsAdrs stH
    (0x80 + 32 * j) vsib vpar vadr sval o5 vnode o6
    (lookupValue st5.bindings "sibling")
    h20 ho5 ho6 h1 h2 h3 h4 h5off h5val h6off h6val

/-! ## 3. forEach-statement adapters for the FORS inner climb. -/

/-- S4-shaped bounded-index adapter for the FORS inner Merkle climb: if each
`stepForsMerkle` iteration preserves `mem[0x00]` after the loop binds the
concrete height to `"h"`, then the whole `forsLeafInnerStmt` preserves the seed
cell. -/
theorem forsLeafInner_preserves_seed_slot_bound_of_step
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_forsClimb_preserves_memory_val_bound
      0 19 hstep st s'
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- S4-shaped bounded-index adapter for arbitrary memory cells through the FORS
inner Merkle climb. -/
theorem forsLeafInner_preserves_memory_val_bound_of_step
    (addr : Nat)
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_forsClimb_preserves_memory_val_bound
      addr 19 hstep st s'
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- Range-gated memory-frame variant for the FORS inner Merkle climb. -/
theorem forsLeafInner_preserves_memory_val_range_of_step
    (addr : Nat) (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i)
    (st s' : RuntimeState)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt
        = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.execStmt_forEach_h_forsClimb_preserves_memory_val_range
      addr 19 D hstep st s' hD
      (by simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt] using h)

/-- One FORS leaf iteration preserves every other ordinary root slot, provided
the inner Merkle step frame preserves that slot at each Merkle height. -/
theorem forsLeafStep_preserves_root_cell_range_ne_of_inner_step
    (st : RuntimeState) (j idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) (hne : j ≠ idx)
    (hstep : ∀ (s : RuntimeState) (h : Nat),
      ((stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize h) }).world.memory
            (0x80 + 32 * j)).val =
        (s.world.memory (0x80 + 32 * j)).val) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_root_cell_range_ne_of_inner
    st j idx hidx hi hne
    (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range st j)
    (forsLeafInner_preserves_memory_val_bound_of_step (0x80 + 32 * j) hstep)

/-! ## 4. Frozen-calldata site packaging.

The only site-specific eval fact a memory-frame step needs is the masked
sibling calldata read (`h1`); the FIPS address expression is total. -/

/-- Masked sibling calldata read from the frozen C13 calldata image, for tree
`t < 6` at climb height `idx < 19`. -/
theorem s4_sibling_read_of_fors_frozen_calldata
    (s : RuntimeState) (t idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    (ht : t < 6)
    (hidx : idx < 19) :
    evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "authPtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
      = some
        (SphincsMinusVerifierSpec.C13Concrete.maskN
          (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
            (SphincsMinusVerifiers.MkC13State.sigDataOffset
              + (128 + 304 * t) + 16 * idx))) := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let ap : Nat := SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t)
  let sOff : Nat := 128 + 304 * t + 16 * idx
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have haplt : ap < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have hshift : idx <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    omega
  have hsum : ap + idx <<< 4 < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset, Nat.shiftLeft_eq]
    omega
  have hoff : ap + idx <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff := by
    dsimp [ap, sOff]
    rw [Nat.shiftLeft_eq]
    omega
  have hoff4 : 4 ≤ SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff := by
    dsimp [sOff]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have hapH : evalExpr [] stH (.localVar "authPtr") = some ap := by
    show some (lookupValue stH.bindings "authPtr") = some ap
    dsimp [stH, ap]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "authPtr" (wordNormalize idx) (by decide)]
    exact congrArg some hap
  have hhH : evalExpr [] stH (.localVar "h") = some idx := by
    show some (lookupValue stH.bindings "h") = some idx
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have hraw :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_sibling_read_frozen
      stH "authPtr" pkSeed pkRoot message sig ap idx sOff
      (by dsimp [stH]; exact hsel)
      (by dsimp [stH]; exact hcd)
      hapH hhH haplt hidx256 hshift hsum hoff hoff4
  have hsOff :
      SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff
        = SphincsMinusVerifiers.MkC13State.sigDataOffset
            + (128 + 304 * t) + 16 * idx := by
    dsimp [sOff]
    omega
  rw [hsOff] at hraw
  exact hraw

/-- One FORS Merkle step preserves the seed slot when its setup bindings and
frozen calldata frame match the C13 FORS auth-path layout. -/
theorem stepFors_preserves_seed_slot_of_fors_frozen_calldata
    (s : RuntimeState) (t idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (ht : t < 6)
    (hidx : idx < 19) :
    ((stepForsMerkle
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  have h1 := s4_sibling_read_of_fors_frozen_calldata
    s t idx pkSeed pkRoot message sig hsel hcd hap ht hidx
  exact stepFors_preserves_seed_slot_of_s4_eval
    s idx (lookupValue s.bindings "pathIdx") _ rfl hpathlt h1

/-- One FORS Merkle step preserves an ordinary root-array slot when its setup
bindings and frozen calldata frame match the C13 FORS auth-path layout. -/
theorem stepFors_preserves_root_cell_of_fors_frozen_calldata
    (s : RuntimeState) (j t idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "authPtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t))
    (hpathlt : lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (ht : t < 6)
    (hidx : idx < 19) :
    ((stepForsMerkle
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
        (0x80 + 32 * j)).val
      = (s.world.memory (0x80 + 32 * j)).val := by
  have h1 := s4_sibling_read_of_fors_frozen_calldata
    s t idx pkSeed pkRoot message sig hsel hcd hap ht hidx
  exact stepFors_preserves_root_cell_of_s4_eval
    s j idx (lookupValue s.bindings "pathIdx") _ rfl hpathlt h1

/-! ## 5. Frozen-site invariance through one step and the inner loop. -/

/-- One inner FORS Merkle step preserves the frozen-site invariant.  The moving
`pathIdx` is rebound to `pathIdx >>> 1`, hence remains a bounded EVM word; the
static selector/calldata and fixed `authPtr`/`forsBase` bindings are framed
through the step. -/
theorem stepFors_preserves_forsFrozenSite
    (s : RuntimeState) (t idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ForsFrozenSite t pkSeed pkRoot message sig s)
    (ht : t < 6)
    (hidx : idx < 19) :
    ForsFrozenSite t pkSeed pkRoot message sig
      (stepForsMerkle
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }) := by
  rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
  have h1 := s4_sibling_read_of_fors_frozen_calldata
    s t idx pkSeed pkRoot message sig hsel hcd hap ht hidx
  set vsib := SphincsMinusVerifierSpec.C13Concrete.maskN
    (Compiler.Proofs.YulGeneration.calldataloadWord 0
      (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
        ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) + 16 * idx))
    with hvsib
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let mIdx : Nat := lookupValue s.bindings "pathIdx"
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let vadr : Nat := SphincsMinusVerifiers.ClimbKit.adrsEval_fors.val st2
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory :=
        SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory :=
        SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH, mIdx]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hpathlt
  have h3 : evalExpr [] st2 forsAdrs = some vadr :=
    SphincsMinusVerifiers.ClimbKit.adrsEval_fors.eval st2
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hpathlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") =
      some (lookupValue st5.bindings "sibling") := by
    rfl
  have hsc :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_selector_calldata
      "node" "pathIdx" "authPtr" forsAdrs stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      h1 h2 h3 h4 h5off h5val h6off h6val
  have hapStep :
      lookupValue
        (SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs
          stH).bindings "authPtr"
        = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_binding_frozen
      "node" "pathIdx" "authPtr" "authPtr" forsAdrs stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "authPtr" (wordNormalize idx) (by decide)]
    exact hap
  have hbaseStep :
      lookupValue
        (SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs
          stH).bindings "forsBase" = base := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_binding_frozen
      "node" "pathIdx" "authPtr" "forsBase" forsAdrs stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "forsBase" (wordNormalize idx) (by decide)]
    exact hbase
  have hpathStepEq :
      lookupValue
        (SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs
          stH).bindings "pathIdx" = vpar :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_idx_binding
      "node" "pathIdx" "authPtr" forsAdrs stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) h1 h2 h3 h4 h5off h5val h6off h6val
  have hvparlt : vpar < 2 ^ 256 := by
    dsimp [vpar, mIdx]
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hpathlt
  show ForsFrozenSite t pkSeed pkRoot message sig
    (SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs stH)
  refine ⟨base, hsc.1.trans hsel, hsc.2.trans hcd, hapStep, hbaseStep, hbaselt, ?_⟩
  rw [hpathStepEq]
  exact hvparlt

/-- Pure inner-loop site invariant: if the C13 FORS frozen-site facts hold at
the loop entry, they hold after every executed `stepForsMerkle` iteration in a
range whose heights satisfy `idx < 19`. -/
theorem foldLoop_preserves_forsFrozenSite_range
    (t : Nat) (pkSeed pkRoot message sig : ByteArray) (ht : t < 6) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 19) →
      ForsFrozenSite t pkSeed pkRoot message sig state →
      ForsFrozenSite t pkSeed pkRoot message sig
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
          state index remaining)
  | state, _, 0, _, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
      exact hsite
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      exact foldLoop_preserves_forsFrozenSite_range t pkSeed pkRoot message sig ht
        (stepForsMerkle
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) })
        (index + 1) remaining
        (fun i hi1 hi2 => hD i (by omega) (by omega))
        (stepFors_preserves_forsFrozenSite
          state t index pkSeed pkRoot message sig hsite ht
          (hD index (by omega) (by omega)))

/-- Pure inner-loop seed-cell frame from the concrete C13 FORS frozen-site
invariant. -/
theorem foldLoop_preserves_seed_slot_of_forsFrozenSite_range
    (t : Nat) (pkSeed pkRoot message sig : ByteArray) (ht : t < 6) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 19) →
      ForsFrozenSite t pkSeed pkRoot message sig state →
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
          state index remaining).world.memory 0).val
        = (state.world.memory 0).val
  | state, _, 0, _, _ => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let stepState : RuntimeState :=
        stepForsMerkle
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) }
      have hstepMem : (stepState.world.memory 0).val = (state.world.memory 0).val := by
        rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
        exact stepFors_preserves_seed_slot_of_fors_frozen_calldata
          state t index pkSeed pkRoot message sig
          hsel hcd hap hpathlt ht
          (hD index (by omega) (by omega))
      have hstepSite :
          ForsFrozenSite t pkSeed pkRoot message sig stepState := by
        exact stepFors_preserves_forsFrozenSite
          state t index pkSeed pkRoot message sig hsite ht
          (hD index (by omega) (by omega))
      have hrec :
          ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
              stepState (index + 1) remaining).world.memory 0).val
            = (stepState.world.memory 0).val :=
        foldLoop_preserves_seed_slot_of_forsFrozenSite_range
          t pkSeed pkRoot message sig ht stepState (index + 1) remaining
          (fun i hi1 hi2 => hD i (by omega) (by omega))
          hstepSite
      exact hrec.trans hstepMem

/-- Pure inner-loop ordinary-root-cell frame from the concrete C13 FORS
frozen-site invariant. -/
theorem foldLoop_preserves_root_cell_of_forsFrozenSite_range
    (j t : Nat) (pkSeed pkRoot message sig : ByteArray) (ht : t < 6) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 19) →
      ForsFrozenSite t pkSeed pkRoot message sig state →
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
          state index remaining).world.memory (0x80 + 32 * j)).val
        = (state.world.memory (0x80 + 32 * j)).val
  | state, _, 0, _, _ => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let stepState : RuntimeState :=
        stepForsMerkle
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) }
      have hstepMem :
          (stepState.world.memory (0x80 + 32 * j)).val
            = (state.world.memory (0x80 + 32 * j)).val := by
        rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
        exact stepFors_preserves_root_cell_of_fors_frozen_calldata
          state j t index pkSeed pkRoot message sig
          hsel hcd hap hpathlt ht
          (hD index (by omega) (by omega))
      have hstepSite :
          ForsFrozenSite t pkSeed pkRoot message sig stepState := by
        exact stepFors_preserves_forsFrozenSite
          state t index pkSeed pkRoot message sig hsite ht
          (hD index (by omega) (by omega))
      have hrec :
          ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
              stepState (index + 1) remaining).world.memory (0x80 + 32 * j)).val
            = (stepState.world.memory (0x80 + 32 * j)).val :=
        foldLoop_preserves_root_cell_of_forsFrozenSite_range
          j t pkSeed pkRoot message sig ht stepState (index + 1) remaining
          (fun i hi1 hi2 => hD i (by omega) (by omega))
          hstepSite
      exact hrec.trans hstepMem

/-! ## 6. The setup → frozen-site package. -/

/-- Bundle the local `forsLeafSetupStep` facts into the frozen-calldata site
shape consumed by the C13 FORS Merkle frame adapters.  The hoisted FIPS ADRS
base `"forsBase"` is bound before the outer loop (the fors-setup segment), so
its value and bound are taken at `st` and framed through the setup prefix. -/
theorem forsLeafSetupStep_fors_frozen_calldata_site
    (st : RuntimeState) (t base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hbase : lookupValue st.bindings "forsBase" = base)
    (hbaseLt : base < 2 ^ 256)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ∃ base',
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).selector = 0 ∧
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).world.calldata
        = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings "authPtr"
        = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
        "forsBase" = base' ∧
      base' < 2 ^ 256 ∧
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
        "pathIdx" < 2 ^ 256 := by
  rcases SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_selector_calldata
      st with ⟨hselStep, hcdStep⟩
  refine ⟨base, ?_, ?_, ?_, ?_, hbaseLt, ?_⟩
  · rw [hselStep, hsel]
  · rw [hcdStep, hcd]
  · have hsigBase164 : lookupValue st.bindings "sigBase" = 164 := by
      simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hsigBase
    have hap :=
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_authPtr_eq_sigDataOffset
        st t hi hsigBase164 ht
    simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hap
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_forsBase st]
    exact hbase
  · exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_pathIdx_lt st t hi

/-- Predicate-form wrapper for the local setup-site package. -/
theorem forsLeafSetupStep_forsFrozenSite
    (st : RuntimeState) (t base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hbase : lookupValue st.bindings "forsBase" = base)
    (hbaseLt : base < 2 ^ 256)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ForsFrozenSite t pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st) :=
  forsLeafSetupStep_fors_frozen_calldata_site st t base pkSeed pkRoot message sig
    hi ht hsigBase hbase hbaseLt hsel hcd

/-! ## 7. Inner-step / leaf-step / outer-loop memory carries. -/

/-- Exact `forsLeafInnerStep` seed-cell adapter from the C13 FORS frozen-site
invariant. -/
theorem forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite
    (st : RuntimeState) (t : Nat) (pkSeed pkRoot message sig : ByteArray)
    (ht : t < 6)
    (hsite : ForsFrozenSite t pkSeed pkRoot message sig st) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep st).world.memory 0).val
      = (st.world.memory 0).val := by
  let stH : RuntimeState :=
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
  have hsiteH : ForsFrozenSite t pkSeed pkRoot message sig stH := by
    rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
    refine ⟨base, hsel, hcd, ?_, ?_, hbaselt, ?_⟩
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "authPtr" (wordNormalize 0) (by decide)]
      exact hap
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "forsBase" (wordNormalize 0) (by decide)]
      exact hbase
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "pathIdx" (wordNormalize 0) (by decide)]
      exact hpathlt
  have hinner :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
          stH 0 (wordNormalize 19)).world.memory 0).val
        = (stH.world.memory 0).val :=
    foldLoop_preserves_seed_slot_of_forsFrozenSite_range
      t pkSeed pkRoot message sig ht stH 0 (wordNormalize 19)
      (fun i _ hi => by
        have hnorm : wordNormalize 19 = 19 := by
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (by decide)]
        rw [hnorm] at hi
        omega)
      hsiteH
  simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep, stH] using hinner

/-- Exact `forsLeafInnerStep` ordinary-root-cell adapter from the C13 FORS
frozen-site invariant. -/
theorem forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite
    (st : RuntimeState) (j t : Nat) (pkSeed pkRoot message sig : ByteArray)
    (ht : t < 6)
    (hsite : ForsFrozenSite t pkSeed pkRoot message sig st) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep st).world.memory
        (0x80 + 32 * j)).val
      = (st.world.memory (0x80 + 32 * j)).val := by
  let stH : RuntimeState :=
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
  have hsiteH : ForsFrozenSite t pkSeed pkRoot message sig stH := by
    rcases hsite with ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
    refine ⟨base, hsel, hcd, ?_, ?_, hbaselt, ?_⟩
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "authPtr" (wordNormalize 0) (by decide)]
      exact hap
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "forsBase" (wordNormalize 0) (by decide)]
      exact hbase
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        st.bindings "h" "pathIdx" (wordNormalize 0) (by decide)]
      exact hpathlt
  have hinner :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
          stH 0 (wordNormalize 19)).world.memory (0x80 + 32 * j)).val
        = (stH.world.memory (0x80 + 32 * j)).val :=
    foldLoop_preserves_root_cell_of_forsFrozenSite_range
      j t pkSeed pkRoot message sig ht stH 0 (wordNormalize 19)
      (fun i _ hi => by
        have hnorm : wordNormalize 19 = 19 := by
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (by decide)]
        rw [hnorm] at hi
        omega)
      hsiteH
  simpa [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep, stH] using hinner

/-- One concrete FORS leaf iteration preserves `mem[0x00]` from the actual local
setup facts: setup packages `ForsFrozenSite`, the inner pure step preserves the
seed slot, and the final store is non-aliasing for `t < 6`. -/
theorem forsLeafStep_preserves_seed_slot_of_forsFrozenSetup
    (st : RuntimeState) (t base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hbase : lookupValue st.bindings "forsBase" = base)
    (hbaseLt : base < 2 ^ 256)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val := by
  have hbody :
      execStmtList [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody
        = .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeaf st
  rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupBody
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt,
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt]
      (SphincsMinusVerifiers.SegmentS4Fors.execForsLeafSetup st)] at hbody
  have hInnerExec :
      execStmt [] (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt =
        .continue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeafInner
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt] hInnerExec] at hbody
  have hStoreExec :
      execStmt []
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt =
        .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) := by
    simpa using hbody
  have hiSetup :
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInner_preserves_i
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) hInnerExec,
      hiSetup]
  have hStoreSeed :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStore_preserves_seed_slot_range
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) t ht hiInner hStoreExec
  have hsetupSite :
      ForsFrozenSite t pkSeed pkRoot message sig
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st) :=
    forsLeafSetupStep_forsFrozenSite st t base pkSeed pkRoot message sig
      hi ht hsigBase hbase hbaseLt hsel hcd
  have hInnerSeed :=
    forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      t pkSeed pkRoot message sig ht hsetupSite
  have hSetupSeed :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_seed_slot st
  rw [hStoreSeed, hInnerSeed, hSetupSeed]

/-- One concrete FORS leaf iteration preserves an ordinary root slot different
from the leaf being stored, using the actual local setup facts. -/
theorem forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup
    (st : RuntimeState) (j t base : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = t)
    (ht : t < 6)
    (hne : j ≠ t)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hbase : lookupValue st.bindings "forsBase" = base)
    (hbaseLt : base < 2 ^ 256)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val
      = (st.world.memory (0x80 + 32 * j)).val := by
  have hbody :
      execStmtList [] st SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody
        = .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeaf st
  rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupBody
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt,
        SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt]
      (SphincsMinusVerifiers.SegmentS4Fors.execForsLeafSetup st)] at hbody
  have hInnerExec :
      execStmt [] (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStmt =
        .continue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) :=
    SphincsMinusVerifiers.SegmentS4Fors.execForsLeafInner
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _
      [SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt] hInnerExec] at hbody
  have hStoreExec :
      execStmt []
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
          SphincsMinusVerifiers.SegmentS4Fors.forsLeafStoreStmt =
        .continue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) := by
    simpa using hbody
  have hiSetup :
      lookupValue (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings
          "i" = t := by
    rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafInner_preserves_i
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)) hInnerExec,
      hiSetup]
  have hStoreRoot :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafStore_preserves_root_cell_range_ne
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st))
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st) j t ht hiInner hne hStoreExec
  have hsetupSite :
      ForsFrozenSite t pkSeed pkRoot message sig
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st) :=
    forsLeafSetupStep_forsFrozenSite st t base pkSeed pkRoot message sig
      hi ht hsigBase hbase hbaseLt hsel hcd
  have hInnerRoot :=
    forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      j t pkSeed pkRoot message sig ht hsetupSite
  have hSetupRoot :=
    SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range st j
  rw [hStoreRoot, hInnerRoot, hSetupRoot]

/-- One FORS leaf iteration preserves every other ordinary root slot over the
real outer range when each inner Merkle step carries the frozen C13
calldata/auth-path frame. -/
theorem forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata
    (st : RuntimeState) (j t : Nat) (ht : t < 6)
    (hi : lookupValue st.bindings "i" = t) (hne : j ≠ t)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (idx : Nat), idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory
        (0x80 + 32 * j)).val =
      (st.world.memory (0x80 + 32 * j)).val := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_root_cell_range_ne_of_inner
    st j t ht hi hne
    (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_root_cell_range st j)
    (forsLeafInner_preserves_memory_val_range_of_step
      (0x80 + 32 * j) (fun idx => idx < 19)
      (fun s idx hidx => by
        rcases hsite s idx hidx with
          ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
        exact stepFors_preserves_root_cell_of_fors_frozen_calldata
          s j t idx pkSeed pkRoot message sig
          hsel hcd hap hpathlt ht hidx)
      (fun i _ hi => by
        have hnorm : wordNormalize 19 = 19 := by
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (by decide)]
        rw [hnorm] at hi
        omega))

/-- Outer FORS carry for an ordinary root cell with the suffix-preservation
premise discharged from frozen C13 calldata/auth-path facts. -/
theorem forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata
    (st : RuntimeState) (j : Nat) (hj : j < 6)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
        0 (wordNormalize 6)).world.memory (0x80 + 32 * j)).val =
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
              { (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                  { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                  0 j) with
                bindings :=
                  bindValue
                    (SphincsMinusVerifiers.ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                      { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
                      0 j).bindings "i" (wordNormalize j) })).bindings "node") := by
  exact SphincsMinusVerifiers.SegmentS4Fors.forsOuter_root_cell_eq_iteration_node_of_suffix_preserves
    st j hj
    (fun s t hgt ht => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize t)) "i" = t := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans ht (by decide))]
      exact forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata
        { s with bindings := bindValue s.bindings "i" (wordNormalize t) }
        j t ht hi (by omega) pkSeed pkRoot message sig
        (fun s idx hidx => hsite s t idx ht hidx))

/-- One FORS leaf iteration preserves `mem[0x00]` over the real outer range once
the inner Merkle step has a bounded-index seed-frame proof. -/
theorem forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat),
      ((stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_seed_slot_range_of_inner
    st idx hidx hi
    (forsLeafInner_preserves_seed_slot_bound_of_step hstep)

/-- Range-gated version of
`forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound`. -/
theorem forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
    (D : Nat → Prop)
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hstep : ∀ (s : RuntimeState) (hidx : Nat), D hidx →
      ((stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 19 → D i) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep_preserves_seed_slot_range_of_inner
    st idx hidx hi
    (forsLeafInner_preserves_memory_val_range_of_step 0 D hstep hD)

/-- One FORS leaf iteration preserves `mem[0x00]` over the real outer range once
each inner Merkle step carries the frozen C13 calldata/auth-path frame. -/
theorem forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata
    (st : RuntimeState) (t : Nat) (ht : t < 6)
    (hi : lookupValue st.bindings "i" = t)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (idx : Nat), idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256) :
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep st).world.memory 0).val
      = (st.world.memory 0).val :=
  forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
    (fun idx => idx < 19) st t ht hi
    (fun s idx hidx => by
      rcases hsite s idx hidx with
        ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
      exact stepFors_preserves_seed_slot_of_fors_frozen_calldata
        s t idx pkSeed pkRoot message sig hsel hcd hap hpathlt ht hidx)
    (fun i _ hi => by
      have hnorm : wordNormalize 19 = 19 := by
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (by decide)]
      rw [hnorm] at hi
      omega)

/-- Full FORS outer-loop seed-cell frame reduced to frozen C13 calldata/auth-path
facts for the inner Merkle states. -/
theorem execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata
    (st s' : RuntimeState) (pkSeed pkRoot message sig : ByteArray)
    (hsite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
      ∃ base,
        s.selector = 0 ∧
        s.world.calldata
          = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
        lookupValue s.bindings "authPtr"
          = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t) ∧
        lookupValue s.bindings "forsBase" = base ∧
        base < 2 ^ 256 ∧
        lookupValue s.bindings "pathIdx" < 2 ^ 256)
    (h : execStmt [] st SphincsMinusVerifiers.SegmentS4Fors.forsOuterStmt
        = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  SphincsMinusVerifiers.SegmentS4Fors.execForsOuter_preserves_seed_slot_range_six
    st s'
    (fun s t ht s'' hexec => by
      have hi : lookupValue (bindValue s.bindings "i" (wordNormalize t)) "i" = t := by
        rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (lt_trans ht (by decide))]
      exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafBody_preserves_seed_slot_range_of_inner
        { s with bindings := bindValue s.bindings "i" (wordNormalize t) }
        s'' t ht hi
        (forsLeafInner_preserves_memory_val_range_of_step 0
          (fun idx => idx < 19)
          (fun s idx hidx => by
            rcases hsite s t idx ht hidx with
              ⟨base, hsel, hcd, hap, hbase, hbaselt, hpathlt⟩
            exact stepFors_preserves_seed_slot_of_fors_frozen_calldata
              s t idx pkSeed pkRoot message sig
              hsel hcd hap hpathlt ht hidx)
          (fun i _ hi => by
            have hnorm : wordNormalize 19 = 19 := by
              rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
                Nat.mod_eq_of_lt (by decide)]
            rw [hnorm] at hi
            omega))
        hexec)
    h

/-! ## 8. Node correspondence: the FORS inner climb against the spec
`forsClimb`.

The FIPS per-level address reads the outer loop binding `"i"` (the
`i <<< (18 - h)` tree-number fold), which the bare `MerkleClimbFrame` does not
carry.  `ForsClimbFrameI` strengthens the frame with the `"i"` binding and a
moving-index word bound; the conditional fold engine threads it through the 19
climb iterations. -/

/-- Frame-carrying FORS climb invariant: the static `MerkleClimbFrame` at the
hoisted FIPS ADRS base `adrsForsBase t0 l0`, plus the outer tree binding `"i"`
and the bounded moving path index. -/
def ForsClimbFrameI
    (i t0 l0 seed merklePtr : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (s : RuntimeState) (a : Nat × Nat) : Prop :=
  SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
    "node" "pathIdx" "forsBase" "authPtr"
    pkSeed pkRoot message sig seed (adrsForsBase t0 l0) merklePtr s a
  ∧ lookupValue s.bindings "i" = i
  ∧ a.1 < 2 ^ 256

/-- The strengthened invariant survives the loop's `"h"` rebind. -/
theorem ForsClimbFrameI.h_inject
    {i t0 l0 seed merklePtr : Nat}
    {pkSeed pkRoot message sig : ByteArray}
    {s : RuntimeState} {a : Nat × Nat} (v : Nat)
    (h : ForsClimbFrameI i t0 l0 seed merklePtr pkSeed pkRoot message sig s a) :
    ForsClimbFrameI i t0 l0 seed merklePtr pkSeed pkRoot message sig
      { s with bindings := bindValue s.bindings "h" v } a := by
  refine ⟨SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_h_inject
    "node" "pathIdx" "forsBase" "authPtr"
    pkSeed pkRoot message sig seed (adrsForsBase t0 l0) merklePtr s a v h.1, ?_, h.2.2⟩
  rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
    s.bindings "h" "i" v (by decide)]
  exact h.2.1

/-- **`stepFors_forsClimbFrameI_hstep_of_fors_frozen_calldata`** — the master
per-iteration advance for the FIPS FORS inner climb: one `stepForsMerkle` at the
`"h"`-injected state carries `ForsClimbFrameI` forward together with one
`forsSpecStep`, from the frozen C13 calldata layout and the per-height
`MerkleClimbData` fact alone. -/
theorem stepFors_forsClimbFrameI_hstep_of_fors_frozen_calldata
    (s : RuntimeState) (i t0 l0 idx mIdx node seed : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes)
    (hinv : ForsClimbFrameI i t0 l0 seed
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
      pkSeed pkRoot message sig s (mIdx, node))
    (hiLt : i < 6)
    (hidx : idx < 19)
    (ht0 : t0 < 2 ^ 64) (hl0 : l0 < 2 ^ 32)
    (hdata : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (fun h =>
          Compiler.Proofs.YulGeneration.calldataloadWord 0
            (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
            (SphincsMinusVerifiers.MkC13State.sigDataOffset
              + (128 + 304 * i) + 16 * h)) idx) :
    ForsClimbFrameI i t0 l0 seed
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
      pkSeed pkRoot message sig
      (stepForsMerkle
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
        seed i t0 l0 auth idx (mIdx, node)) := by
  obtain ⟨hframe, hi, hmlt⟩ := hinv
  have hsel : s.selector = 0 := hframe.2.2.2.2.1
  have hcd : s.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig := hframe.2.2.2.2.2.1
  have hap : lookupValue s.bindings "authPtr"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i) :=
    hframe.2.2.1
  have hbaseS : lookupValue s.bindings "forsBase" = adrsForsBase t0 l0 := hframe.2.1
  have hpath : lookupValue s.bindings "pathIdx" = mIdx :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.idx hframe.1
  have hbaseLt : adrsForsBase t0 l0 < 2 ^ 256 :=
    lt_trans (SphincsMinusVerifierSpec.C13Concrete.adrsForsBase_lt_of_bounds ht0 hl0)
      (by decide : (2 : Nat) ^ 192 < 2 ^ 256)
  -- The masked sibling calldata read at the h-injected state.
  have h1 := s4_sibling_read_of_fors_frozen_calldata
    s i idx pkSeed pkRoot message sig hsel hcd hap hiLt hidx
  set vsib := SphincsMinusVerifierSpec.C13Concrete.maskN
    (Compiler.Proofs.YulGeneration.calldataloadWord 0
      (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
        ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i) + 16 * idx))
    with hvsibDef
  -- The local step states.
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let vadr : Nat :=
    adrsForsBase t0 l0 ||| (((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| vpar))
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "node"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hpathH : lookupValue stH.bindings "pathIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "pathIdx" (wordNormalize idx) (by decide)]
    exact hpath
  have hpath1 : lookupValue st1.bindings "pathIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "pathIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "pathIdx" st1 mIdx hpath1 hmlt
  have hvparlt : vpar < 2 ^ 256 := by
    dsimp [vpar]
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hmlt
  -- The FIPS per-level address word at st2, identified with its OR image.
  have hbase2 : lookupValue st2.bindings "forsBase" = adrsForsBase t0 l0 := by
    dsimp [st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "forsBase" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "forsBase" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "forsBase" (wordNormalize idx) (by decide)]
    exact hbaseS
  have hh2 : lookupValue st2.bindings "h" = idx := by
    dsimp [st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "h" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "h" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have hi2 : lookupValue st2.bindings "i" = i := by
    dsimp [st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "i" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "i" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "i" (wordNormalize idx) (by decide)]
    exact hi
  have hp2 : lookupValue st2.bindings "parentIdx" = vpar := by
    dsimp [st2]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h3 : evalExpr [] st2 forsAdrs = some vadr :=
    forsAdrs_eval_eq st2 hbase2 hbaseLt hh2 hidx hi2 hiLt hp2 hvparlt
  have hpath3 : lookupValue st3.bindings "pathIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "pathIdx" vsib (by decide)]
    exact hpathH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "pathIdx" st3 mIdx hpath3 hmlt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "node") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") = some vsib := by
    show some (lookupValue st5.bindings "sibling") = some vsib
    dsimp [st5, st4, st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
      "s" "sibling" sval (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "sibling" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hpar : mIdx % 2 = 0 ∨ mIdx % 2 = 1 := by
    have hlt : mIdx % 2 < 2 := Nat.mod_lt mIdx (by decide)
    omega
  have hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even mIdx hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd mIdx hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((mIdx &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  have hvparEq : vpar = mIdx / 2 := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.parentIdx_shiftRight mIdx
  have hnode : wordNormalize vnode = node := by
    dsimp [vnode, st4, st3, st2, st1, stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
        "parentIdx" vpar) "s" "node" sval (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "node" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx)) "sibling" "node" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "node" (wordNormalize idx) (by decide)]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.node hframe.1
  have hseed : (stH.world.memory 0x00).val = seed := by
    dsimp [stH]
    exact hframe.2.2.2.1
  -- The address-word data obligation: the eval value is the spec node address.
  have hVlt : vadr < 2 ^ 256 :=
    forsAdrs_value_lt (adrsForsBase t0 l0) i idx vpar hbaseLt hiLt hidx hvparlt
  have hadrW : wordNormalize vadr
      = adrsForsNode t0 l0 i idx (mIdx / 2) := by
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hVlt]
    show adrsForsBase t0 l0 ||| (((idx + 1) <<< 32) ||| ((i <<< (18 - idx)) ||| vpar))
        = adrsForsNode t0 l0 i idx (mIdx / 2)
    rw [hvparEq]
    exact SphincsMinusVerifiers.ClimbStepSpec.forsBase_node_address t0 l0 i idx (mIdx / 2)
  have hsib : wordNormalize vsib
      = wordOfHash16 ((auth[idx]?).getD ⟨#[]⟩) := by
    rw [hvsibDef, SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_maskN]
    exact hdata
  have hstepData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligationsW
        stH vadr vsib seed (adrsForsNode t0 l0 i idx (mIdx / 2)) idx mIdx auth :=
    ⟨hseed, hadrW, hsib⟩
  have hframeH := SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_h_inject
    "node" "pathIdx" "forsBase" "authPtr"
    pkSeed pkRoot message sig seed (adrsForsBase t0 l0)
    (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
    s (mIdx, node) (wordNormalize idx) hframe
  have hfinal := SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrameA_step
    "node" "pathIdx" "forsBase" "authPtr" forsAdrs
    pkSeed pkRoot message sig seed (adrsForsBase t0 l0)
    (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
    (adrsForsNode t0 l0 i idx (mIdx / 2))
    stH vsib vpar vadr sval o5 vnode o6 vsib idx mIdx node auth
    hframeH hparOff hvparEq hnode hstepData h1 h2 h3 h4 h5off h5val h6off h6val
  -- "i" is framed through the step.
  have hiStep :
      lookupValue
        (SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs
          stH).bindings "i" = i := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkleA_binding_frozen
      "node" "pathIdx" "authPtr" "i" forsAdrs stH
      vsib vpar vadr sval o5 vnode o6 vsib
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "i" (wordNormalize idx) (by decide)]
    exact hi
  refine ⟨?_, ?_, ?_⟩
  · show SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed (adrsForsBase t0 l0)
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
      (SphincsMinusVerifiers.ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" forsAdrs stH)
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
        seed i t0 l0 auth idx (mIdx, node))
    simp only [SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep]
    exact hfinal
  · exact hiStep
  · show (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
        seed i t0 l0 auth idx (mIdx, node)).1 < 2 ^ 256
    simp only [SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self mIdx 2) hmlt

/-- Initial FORS climb relation after the straight-line setup prefix.  The index
component is the decoded `treeIdx`, and the node component is the concrete spec
FORS leaf hash word under the FIPS leaf address `adrsForsLeaf t0 l0 i treeIdx`. -/
theorem forsLeafSetupStep_initial_forsClimbRel_of_eval
    (st : RuntimeState) (seed i t0 l0 treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf t0 l0 i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf t0 l0 i treeIdx)) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (treeIdx, maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])) := by
  refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.intro ?_ ?_
  · exact SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_pathIdx_eq_of_eval
      st treeIdx hTree
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_node_eq_spec_of_eval
      st seed (adrsForsLeaf t0 l0 i treeIdx) treeIdx sk hm0 hAdrLt hSkLt hTree hSecret hLeaf]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_maskN _

/-- Initial frame-carrying FORS climb invariant after the straight-line setup:
the relation component from the setup evaluators, the static frame from the
frozen C13 layout, and the `"i"` binding framed through the setup prefix. -/
theorem forsLeafSetupStep_initial_forsClimbFrameI
    (st : RuntimeState) (seed i t0 l0 treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hTreeIdxLt : treeIdx < 2 ^ 256)
    (hbaseSt : lookupValue st.bindings "forsBase" = adrsForsBase t0 l0)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf t0 l0 i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf t0 l0 i treeIdx)) :
    ForsClimbFrameI i t0 l0 seed
      (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
      pkSeed pkRoot message sig
      (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)
      (treeIdx, maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])) := by
  rcases SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_selector_calldata
      st with ⟨hselStep, hcdStep⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_,
    (by decide), (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide), (by decide)⟩,
    ?_, hTreeIdxLt⟩
  · exact forsLeafSetupStep_initial_forsClimbRel_of_eval
      st seed i t0 l0 treeIdx sk hm0 hAdrLt hSkLt hTree hSecret hLeaf
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_forsBase st]
    exact hbaseSt
  · have hsigBase164 : lookupValue st.bindings "sigBase" = 164 := by
      simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hsigBase
    have hap :=
      SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_authPtr_eq_sigDataOffset
        st i hi hsigBase164 hiLt
    simpa [SphincsMinusVerifiers.MkC13State.sigDataOffset] using hap
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_seed_slot]
    exact hm0
  · rw [hselStep, hsel]
  · rw [hcdStep, hcd]
  · rw [SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep_preserves_i st, hi]

/-- **`forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata`** —
concrete frozen-calldata post-inner FORS node correspondence on the FIPS layout:
after the straight-line setup and 19 climb iterations, the model's `"node"`
binding is exactly the spec `forsClimb` at the FIPS digits `t0`/`l0`.  Callers
provide the parsed auth-path `MerkleClimbData` range and the straight-line setup
eval facts. -/
theorem forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata
    (st : RuntimeState) (seed i t0 l0 treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes)
    (hi : lookupValue st.bindings "i" = i)
    (hiLt : i < 6)
    (hTreeIdxLt : treeIdx < 2 ^ 256)
    (hbaseSt : lookupValue st.bindings "forsBase" = adrsForsBase t0 l0)
    (ht0 : t0 < 2 ^ 64) (hl0 : l0 < 2 ^ 32)
    (hsigBase : lookupValue st.bindings "sigBase"
      = SphincsMinusVerifiers.MkC13State.sigDataOffset)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
          (fun h =>
            Compiler.Proofs.YulGeneration.calldataloadWord 0
              (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
              (SphincsMinusVerifiers.MkC13State.sigDataOffset
                + (128 + 304 * i) + 16 * h)) idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf t0 l0 i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf t0 l0 i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i t0 l0 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  let start : RuntimeState := { setup with bindings := bindValue setup.bindings "h" (wordNormalize 0) }
  let node0 := maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])
  have hInit :
      ForsClimbFrameI i t0 l0 seed
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
        pkSeed pkRoot message sig setup (treeIdx, node0) :=
    forsLeafSetupStep_initial_forsClimbFrameI
      st seed i t0 l0 treeIdx sk pkSeed pkRoot message sig
      hi hiLt hTreeIdxLt hbaseSt hsigBase hsel hcd
      hm0 hAdrLt hSkLt hTree hSecret hLeaf
  have hStart :
      ForsClimbFrameI i t0 l0 seed
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
        pkSeed pkRoot message sig start (treeIdx, node0) :=
    ForsClimbFrameI.h_inject (wordNormalize 0) hInit
  let D : Nat → Prop := fun idx =>
    idx < 19 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (fun h =>
          Compiler.Proofs.YulGeneration.calldataloadWord 0
            (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
              ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
            (SphincsMinusVerifiers.MkC13State.sigDataOffset
              + (128 + 304 * i) + 16 * h)) idx
  have hD' : ∀ idx, 0 ≤ idx → idx < 0 + 19 → D idx := by
    intro idx h0 hlt
    exact ⟨by omega, hD idx h0 hlt⟩
  have hpair :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_invariant_cond "h"
      stepForsMerkle
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep seed i t0 l0 auth)
      (ForsClimbFrameI i t0 l0 seed
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * i))
        pkSeed pkRoot message sig)
      D
      (fun s a idx hDi hR => by
        obtain ⟨mIdx, nd⟩ := a
        exact stepFors_forsClimbFrameI_hstep_of_fors_frozen_calldata
          s i t0 l0 idx mIdx nd seed pkSeed pkRoot message sig auth
          hR hiLt hDi.1 ht0 hl0 hDi.2)
      start (treeIdx, node0) 0 19 hD' hStart
  have hnode :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
            start 0 19).bindings "node")
        =
          (SphincsMinusVerifiers.ClimbLoop.specFold
            (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep seed i t0 l0 auth)
            (treeIdx, node0) 0 19).2 :=
    (SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame.toRel hpair.1).2
  have hmodel :
      wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h" stepForsMerkle
            start 0 19).bindings "node")
        =
          SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i t0 l0 19 0 treeIdx node0 auth :=
    hnode.trans
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsClimb_eq_specFold
        seed i t0 l0 auth 19 0 treeIdx node0).symm
  have h19 : wordNormalize 19 = 19 := by
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)]
  unfold SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
  rw [h19]
  exact hmodel

/-- Conditional post-inner FORS node correspondence for one normal C13 FORS tree
with a caller-supplied per-step relation advance (the bare-relation form used
by the seven-root data obligations). -/
theorem forsLeafInnerStep_node_eq_forsClimb_of_eval
    (st : RuntimeState) (seed i t0 l0 treeIdx : Nat) (sk : SphincsMinusVerifierSpec.Bytes)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            seed i t0 l0 auth idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (hm0 : (st.world.memory 0).val = seed)
    (hAdrLt : adrsForsLeaf t0 l0 i treeIdx < 2 ^ 256)
    (hSkLt : wordOfHash16 sk < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some treeIdx)
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" treeIdx }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal N_MASK))
          = some (wordOfHash16 sk))
    (hLeaf : evalExpr []
        { st with bindings :=
            bindValue (bindValue st.bindings "treeIdx" treeIdx) "secretVal" (wordOfHash16 sk) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf t0 l0 i treeIdx)) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i t0 l0 19 0 treeIdx
          (maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])) auth := by
  let setup := SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st
  let start : RuntimeState := { setup with bindings := bindValue setup.bindings "h" (wordNormalize 0) }
  have hR0 :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
        setup
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])) :=
    forsLeafSetupStep_initial_forsClimbRel_of_eval st seed i t0 l0 treeIdx sk
      hm0 hAdrLt hSkLt hTree hSecret hLeaf
  have hR :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
        start
        (treeIdx, maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk])) := by
    refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.intro ?_ ?_
    · dsimp [start]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        setup.bindings "h" "pathIdx" (wordNormalize 0) (by decide)]
      exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.idx hR0
    · dsimp [start]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        setup.bindings "h" "node" (wordNormalize 0) (by decide)]
      exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.node hR0
  have hmodel :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.forsClimb_model_node
      seed i t0 l0 auth cdAt hstep start treeIdx
      (maskN (keccakWords [seed, adrsForsLeaf t0 l0 i treeIdx, wordOfHash16 sk]))
      0 19 hD hR
  have h19 : wordNormalize 19 = 19 := by
    rw [wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide : 19 < 2 ^ 256)]
  unfold SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
  rw [h19]
  exact hmodel

/-- C13 normal-root form of `forsLeafInnerStep_node_eq_forsClimb_of_eval`, at
the digest-derived FIPS digits.  This is the exact post-inner `"node"` equality
expected by the six normal FORS root-cell adapters. -/
theorem forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval
    (st : RuntimeState) (pk : SphincsMinusVerifierSpec.PublicKey)
    (digest : SphincsMinusVerifierSpec.HMsg)
    (fors : SphincsMinusVerifierSpec.ForsSig) (j : Nat) (hj : j < 6)
    (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((fors.authPath[j]?).getD []) cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel "node" "pathIdx"
          (stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.forsSpecStep
            (wordOfHash16 pk.pkSeed) j
            (SphincsMinusVerifierSpec.C13Concrete.idxTree0C13 digest)
            (SphincsMinusVerifierSpec.C13Concrete.idxLeaf0C13 digest)
            ((fors.authPath[j]?).getD []) idx a))
    (hD : ∀ idx, 0 ≤ idx → idx < 0 + 19 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          ((fors.authPath[j]?).getD []) cdAt idx)
    (hm0 : (st.world.memory 0).val = wordOfHash16 pk.pkSeed)
    (hAdrLt : adrsForsLeaf
        (SphincsMinusVerifierSpec.C13Concrete.idxTree0C13 digest)
        (SphincsMinusVerifierSpec.C13Concrete.idxLeaf0C13 digest)
        j ((digest.forsIndex[j]?).getD 0) < 2 ^ 256)
    (hSkLt : wordOfHash16 ((fors.sk[j]?).getD ⟨#[]⟩) < 2 ^ 256)
    (hTree : evalExpr [] st
        (.bitAnd
          (.shr (.mul (.localVar "i") (.literal 19)) (.localVar "dVal"))
          (.literal 0x7FFFF)) = some ((digest.forsIndex[j]?).getD 0))
    (hSecret : evalExpr []
        { st with bindings := bindValue st.bindings "treeIdx" ((digest.forsIndex[j]?).getD 0) }
        (.bitAnd
          (.calldataload
            (.add (.localVar "sigBase")
              (.add (.literal 16) (.shl (.literal 4) (.localVar "i")))))
          (.literal N_MASK))
          = some (wordOfHash16 ((fors.sk[j]?).getD ⟨#[]⟩)))
    (hLeaf : evalExpr []
        { st with bindings :=
            (bindValue
              (bindValue st.bindings "treeIdx" ((digest.forsIndex[j]?).getD 0))
              "secretVal" (wordOfHash16 ((fors.sk[j]?).getD ⟨#[]⟩))) }
        (.bitOr (.localVar "forsBase")
          (.bitOr (.shl (.literal 19) (.localVar "i")) (.localVar "treeIdx")))
          = some (adrsForsLeaf
              (SphincsMinusVerifierSpec.C13Concrete.idxTree0C13 digest)
              (SphincsMinusVerifierSpec.C13Concrete.idxLeaf0C13 digest)
              j ((digest.forsIndex[j]?).getD 0))) :
    wordNormalize
        (lookupValue
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
            (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep st)).bindings "node")
      =
        (SphincsMinusVerifierSpec.C13Concrete.forsAllRootsC13 pk digest fors)[j]'(by
          rw [SphincsMinusVerifierSpec.C13Concrete.forsAllRootsC13_length]
          omega) := by
  rw [SphincsMinusVerifierSpec.C13Concrete.forsAllRootsC13_getElem_normal
    (pk := pk) (digest := digest) (fors := fors) hj]
  exact forsLeafInnerStep_node_eq_forsClimb_of_eval
    st (wordOfHash16 pk.pkSeed) j
    (SphincsMinusVerifierSpec.C13Concrete.idxTree0C13 digest)
    (SphincsMinusVerifierSpec.C13Concrete.idxLeaf0C13 digest)
    ((digest.forsIndex[j]?).getD 0)
    ((fors.sk[j]?).getD ⟨#[]⟩) ((fors.authPath[j]?).getD []) cdAt
    hstep hD hm0 hAdrLt hSkLt hTree hSecret hLeaf

/-! ## 9. Axiom audit (memory-frame half). -/

#print axioms forsAdrs_eval_eq
#print axioms forsAdrs_value_lt
#print axioms stepFors_preserves_seed_slot_of_s4_eval
#print axioms stepFors_preserves_root_cell_of_s4_eval
#print axioms forsLeafInner_preserves_seed_slot_bound_of_step
#print axioms forsLeafInner_preserves_memory_val_bound_of_step
#print axioms forsLeafInner_preserves_memory_val_range_of_step
#print axioms forsLeafStep_preserves_root_cell_range_ne_of_inner_step
#print axioms s4_sibling_read_of_fors_frozen_calldata
#print axioms stepFors_preserves_seed_slot_of_fors_frozen_calldata
#print axioms stepFors_preserves_root_cell_of_fors_frozen_calldata
#print axioms stepFors_preserves_forsFrozenSite
#print axioms foldLoop_preserves_forsFrozenSite_range
#print axioms foldLoop_preserves_seed_slot_of_forsFrozenSite_range
#print axioms foldLoop_preserves_root_cell_of_forsFrozenSite_range
#print axioms forsLeafSetupStep_fors_frozen_calldata_site
#print axioms forsLeafSetupStep_forsFrozenSite
#print axioms forsLeafInnerStep_preserves_seed_slot_of_forsFrozenSite
#print axioms forsLeafInnerStep_preserves_root_cell_of_forsFrozenSite
#print axioms forsLeafStep_preserves_seed_slot_of_forsFrozenSetup
#print axioms forsLeafStep_preserves_root_cell_ne_of_forsFrozenSetup
#print axioms forsLeafStep_preserves_root_cell_range_ne_of_fors_frozen_calldata
#print axioms forsOuter_root_cell_eq_iteration_node_of_fors_frozen_calldata
#print axioms forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
#print axioms forsLeafStep_preserves_seed_slot_range_of_merkle_step_range
#print axioms forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata
#print axioms execForsOuter_preserves_seed_slot_range_of_fors_frozen_calldata
#print axioms ForsClimbFrameI.h_inject
#print axioms stepFors_forsClimbFrameI_hstep_of_fors_frozen_calldata
#print axioms forsLeafSetupStep_initial_forsClimbRel_of_eval
#print axioms forsLeafSetupStep_initial_forsClimbFrameI
#print axioms forsLeafInnerStep_node_eq_forsClimbFrame_of_fors_frozen_calldata
#print axioms forsLeafInnerStep_node_eq_forsClimb_of_eval
#print axioms forsLeafInnerStep_node_eq_forsAllRootsC13_getElem_of_eval

end SphincsMinusVerifiers.SegmentS4ForsMerkleFrame
