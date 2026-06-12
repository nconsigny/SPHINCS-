/-
  SegmentS4ForsDataObligations — standalone reductions for the remaining FORS
  *data* obligations of `C13SeedNamedAcceptGuardedPkRootSizeLeafObligations`
  (`SegmentAcceptSpec`).

  Two axiom-clean bridge bricks, each phrased exactly against the structure's
  field shapes:

  * `hLeaf_of_stepMerkle_seed_frame` reduces the `hLeaf` field (one FORS
    leaf-step preserves the public-seed cell `mem[0x00]`, for every `idx < 6`)
    to a single *unconditional* per-step `stepMerkle` seed-cell frame for the
    inner FORS Merkle climb.  This is the cleanest residual: it isolates the
    whole FORS leaf seed-frame down to the one branchless Merkle swap step.

  * `hmRlo_of_afterFors_root_slots` reduces the `hmRlo` field (the six ordinary
    FORS root cells `0x80 + 32*j`, `j < 6`, after `forsFinalizePreCopyStep`) to
    the FORS outer-loop root-slot correspondence already holding at `afterFors`:
    the pre-copy finalize prefix is a frame over those six source slots, so the
    substantive obligation is purely the `afterFors` reconstruction.

  These are standalone theorems.  They touch neither `execC13` nor
  `c13_refines_byte_spec`; they introduce no `axiom`, no `sorry`, and no
  `native_decide`.  See `STRATEGY.md` (Layer 2/S4, and the soundness rule).
-/

import SphincsMinusVerifiers.SegmentAcceptSpec
import SphincsMinusVerifiers.SegmentS4ForsMerkleFrame
import SphincsMinusVerifiers.SegmentS4Finalize

namespace SphincsMinusVerifiers.SegmentS4ForsDataObligations

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.CurrentNodeFrame
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete

/-- **`hLeaf` reduction.**  The `hLeaf` obligation of
`C13SeedNamedAcceptGuardedPkRootSizeLeafObligations` reduces to an
*unconditional* per-step `stepMerkle` seed-cell frame for the FORS inner Merkle
climb.  Given that every `stepMerkle` iteration preserves the public-seed cell
`mem[0x00]` (the branchless Merkle swap only ever writes the scratch address slot
`0x20` and the parity-determined child slots `{0x40, 0x60}`), each FORS leaf-step
iteration with `idx < 6` preserves it too.

The remaining proof obligation is therefore the single hypothesis `hstep`: one
branchless Merkle swap step never clobbers `mem[0x00]`. -/
theorem hLeaf_of_stepMerkle_seed_frame
    (hstep : ∀ (s : RuntimeState) (hidx : Nat),
      ((SphincsMinusVerifiers.ClimbKit.stepMerkle "node" "pathIdx" "forsBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize hidx) }).world.memory 0).val
        = (s.world.memory 0).val) :
    ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val := by
  intro s idx hidx
  have hi : lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i" = idx := by
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
  exact SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_merkle_step_bound
    { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } idx hidx hi hstep

/-- **`hmRlo` reduction.**  The `hmRlo` obligation reduces to the FORS
outer-loop root-slot correspondence at `afterFors`.  The pre-copy finalize prefix
(`forsFinalizePreCopyStep`) only writes the scratch slots `0x20`/`0x40` and the
forced-zero-leaf slot `0x140`; it preserves each of the six ordinary FORS root
source slots `0x80 + 32*j` (`j < 6`).  Hence if `afterFors` already places
`forsAllRootsC13[j]` in those slots, so does the post-finalize state.

The remaining substantive obligation is therefore `hAfter`: the FORS outer
double-loop reconstructs `forsAllRootsC13[j]` into the source slot `0x80 + 32*j`.
(The seventh root `j = 6` at slot `0x140` is *not* a frame — it is overwritten by
the forced-zero leaf hash and is the separate `hmRlast` obligation.) -/
theorem hmRlo_of_afterFors_root_slots
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hAfter : ∀ j, (h : j < 6) →
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega)) :
    ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega) := by
  intro j hj
  rw [SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep_preserves_root_source_slot
    (afterFors (mkC13State pkSeed pkRoot message sig)) j hj]
  exact hAfter j hj

/-! ## Bonus — discharging `hstep` unconditionally.

`hLeaf_of_stepMerkle_seed_frame` left one residual hypothesis: that a single
branchless Merkle swap step (`stepMerkle`) never clobbers the public-seed cell
`mem[0x00]`.  The shared per-step kernel
`ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity` already proves this
*given* eight `evalExpr` facts and the parity bracket `hparOff`, but the existing
S4 wrapper `stepMerkle_preserves_seed_slot_of_s4_eval` needs `pathIdx < 2^256` to
identify the `shr`/`and`-selector values.  The two lemmas below remove that
hypothesis:

* The swap writes only `{0x20, o5, o6}` with `{o5, o6} = {0x40, 0x60}` by parity,
  so `mem[0x00]` is preserved for *any* `pathIdx`.  Only `h4` (the parity
  selector) needs an identified value; `h1/h2/h3` need mere existence (the ops
  are total), and `h5/h6` are bound-free already.
* The selector value is read mod `2^256` (`Uint256.ofNat`), so choosing the
  parity witness `n := pathIdx % 2^256` makes `h4` land exactly
  `(Nat.land n 1) <<< 5`, matching `merkle_offsets_even/odd n` with no extra
  bridge.  -/

/-- Bound-free `and(e, literal m)`: with `m < 2^256` but **no** bound on the
value `k` of `e`, the interpreter's `Uint256.and` resolves to
`Nat.land (k % 2^256) m` (the operand is reduced mod `2^256` by `Uint256.ofNat`;
the literal needs no reduction).  Unconditional companion to
`ClimbKeccakStep.evalExpr_bitAnd_literal`. -/
theorem evalExpr_bitAnd_literal_modself
    (st : RuntimeState) (e : Compiler.CompilationModel.Expr) (k m : Nat)
    (hk : evalExpr [] st e = some k) (hmlt : m < 2 ^ 256) :
    evalExpr [] st (.bitAnd e (.literal m)) = some (Nat.land (k % 2 ^ 256) m) := by
  show (do
        let lhs ← evalExpr [] st e
        let rhs ← evalExpr [] st (.literal m)
        pure (Verity.Core.Uint256.and lhs rhs).val) = some (Nat.land (k % 2 ^ 256) m)
  have hlit : evalExpr [] st (.literal m) = some (wordNormalize m) := rfl
  rw [hk, hlit]
  show some (Verity.Core.Uint256.and k (wordNormalize m)).val = some (Nat.land (k % 2 ^ 256) m)
  have hm : wordNormalize m = m := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt hmlt
  rw [hm]
  show some ((Verity.Core.Uint256.ofNat (Nat.land (Verity.Core.Uint256.ofNat k).val
        (Verity.Core.Uint256.ofNat m).val)).val) = some (Nat.land (k % 2 ^ 256) m)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k % 2 ^ 256 := rfl
  have hmv : (Verity.Core.Uint256.ofNat m).val = m := Nat.mod_eq_of_lt hmlt
  rw [hkv, hmv]
  show some (Nat.land (k % 2 ^ 256) m % Verity.Core.Uint256.modulus)
      = some (Nat.land (k % 2 ^ 256) m)
  have hland : Nat.land (k % 2 ^ 256) m < 2 ^ 256 :=
    Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt k (by decide))
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hmod, Nat.mod_eq_of_lt hland]

/-- **Unconditional `stepMerkle` seed-cell frame.**  One branchless FORS/XMSS
Merkle swap step preserves `mem[0x00]` for *every* state — no `pathIdx < 2^256`
hypothesis.  This is exactly the residual `hstep` of
`hLeaf_of_stepMerkle_seed_frame`. -/
theorem stepMerkle_seed_frame_unconditional (s : RuntimeState) (idx : Nat) :
    ((SphincsMinusVerifiers.ClimbKit.stepMerkle "node" "pathIdx" "forsBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let n : Nat := lookupValue stH.bindings "pathIdx" % 2 ^ 256
  let sval : Nat := (Nat.land n 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  have hsvalt : sval < 2 ^ 256 := by
    show (Nat.land n 1) <<< 5 < 2 ^ 256
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  obtain ⟨vsib, h1⟩ : ∃ v, evalExpr [] stH
      (.bitAnd (.calldataload (.add (.localVar "authPtr")
        (.shl (.literal 4) (.localVar "h"))))
        (.literal SphincsMinusVerifiers.ClimbKit.N_MASK)) = some v := ⟨_, rfl⟩
  obtain ⟨vpar, h2⟩ : ∃ v,
      evalExpr [] { stH with bindings := bindValue stH.bindings "sibling" vsib }
        (.shr (.literal 1) (.localVar "pathIdx")) = some v := ⟨_, rfl⟩
  obtain ⟨vadr, h3⟩ : ∃ v, evalExpr []
      { stH with bindings :=
        bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.bitOr (.localVar "forsBase")
        (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
          (.localVar "parentIdx"))) = some v := ⟨_, rfl⟩
  let vnode : Nat :=
    lookupValue (bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
      "parentIdx" vpar) "s" sval) "node"
  let vsib2 : Nat :=
    lookupValue (bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
      "parentIdx" vpar) "s" sval) "sibling"
  have hpathH4 :
      lookupValue (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar) "pathIdx"
        = lookupValue stH.bindings "pathIdx" := by
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        (bindValue stH.bindings "sibling" vsib) "parentIdx" "pathIdx" vpar (by decide),
      SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        stH.bindings "sibling" "pathIdx" vsib (by decide)]
  have hbitand : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.bitAnd (.localVar "pathIdx") (.literal 1)) = some (Nat.land n 1) := by
    have hbase := evalExpr_bitAnd_literal_modself
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.localVar "pathIdx")
      (lookupValue (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar) "pathIdx")
      1 rfl (by decide)
    rw [hpathH4] at hbase
    exact hbase
  have h4 : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval := by
    have hlit5 : evalExpr []
        { stH with
          world := { stH.world with memory :=
            SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
        (.literal 5) = some 5 := by
      show some (wordNormalize 5) = some 5
      rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))
      5 (Nat.land n 1) hlit5 hbitand (by decide)
      (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) hsvalt
  have hs5 : lookupValue
      (bindValue (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar) "s" sval) "s"
      = sval :=
    SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self _ "s" sval
  have h5off : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.bitXor (.literal 0x40) (.localVar "s")) = some o5 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      0x40 sval hs5 (by decide) hsvalt
  have h5val : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.localVar "node") = some vnode := rfl
  have h6off : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate (SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.bitXor (.literal 0x60) (.localVar "s")) = some o6 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate (SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr []
      { stH with
        world := { stH.world with memory :=
          SphincsMinusVerifiers.MemoryKit.memUpdate (SphincsMinusVerifiers.MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue (bindValue (bindValue stH.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval }
      (.localVar "sibling") = some vsib2 := rfl
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  have hparOff : (n % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (n % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even n hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd n hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  show ((SphincsMinusVerifiers.ClimbKit.stepMerkle "node" "pathIdx" "forsBase" "authPtr"
      stH).world.memory 0).val = (stH.world.memory 0).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity
    "node" "pathIdx" "forsBase" "authPtr" stH
    vsib vpar vadr sval o5 vnode o6 vsib2 n hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- **`hLeaf` fully discharged.**  Combining `hLeaf_of_stepMerkle_seed_frame`
with the unconditional step frame: each FORS leaf-step (`idx < 6`) preserves the
public-seed cell `mem[0x00]`, with *no* residual hypothesis. -/
theorem hLeaf_discharged :
    ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val :=
  hLeaf_of_stepMerkle_seed_frame stepMerkle_seed_frame_unconditional

#print axioms hLeaf_of_stepMerkle_seed_frame
#print axioms hmRlo_of_afterFors_root_slots
#print axioms evalExpr_bitAnd_literal_modself
#print axioms stepMerkle_seed_frame_unconditional
#print axioms hLeaf_discharged

end SphincsMinusVerifiers.SegmentS4ForsDataObligations
