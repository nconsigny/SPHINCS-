/-
  SegmentLayer3MerkleFrame: lightweight adapters for the C13 XMSS layer
  Merkle climb.

  This module mirrors the S4 FORS Merkle-frame adapters, but instantiates the
  generic branchless-Merkle memory frame with the layer-body variable names:
  `"merkleNode"`, `"mIdx"`, `"treeAdrs"`, and `"merklePtr"`.  It intentionally
  sits outside `SegmentLayer3` so the core layer-body reconstruction does not
  import the heavier `ClimbMemFrameMerkle` module.
-/

import SphincsMinusVerifiers.SegmentLayer3
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers.SegmentLayer3MerkleFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (stepMerkle)

/-- Layer-shaped local `stepMerkle` seed-cell frame.  For the actual XMSS layer
climb variable names, the pure parent-index, selector, child-offset, and local
load facts are discharged here.  Callers only supply the site-specific masked
sibling calldata read (`h1`) and address assembly eval (`h3`). -/
theorem stepMerkle_preserves_seed_slot_of_layer_eval
    (s : RuntimeState) (idx mIdx vsib vadr : Nat)
    (hmIdx : lookupValue s.bindings "mIdx" = mIdx)
    (hmIdxLt : mIdx < 2 ^ 256)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar "merklePtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib)
    (h3 : evalExpr []
            { s with bindings :=
              (bindValue
                (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
                "parentIdx" (mIdx >>> 1)) }
            (.bitOr (.localVar "treeAdrs")
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr) :
    ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "merkleNode"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hmIdxH : lookupValue stH.bindings "mIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "mIdx" (wordNormalize idx) (by decide)]
    exact hmIdx
  have hmIdx1 : lookupValue st1.bindings "mIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "mIdx" vsib (by decide)]
    exact hmIdxH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "mIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "mIdx" st1 mIdx hmIdx1 hmIdxLt
  have hmIdx3 : lookupValue st3.bindings "mIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "mIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "mIdx" vsib (by decide)]
    exact hmIdxH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "mIdx" st3 mIdx hmIdx3 hmIdxLt
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
  have h5val : evalExpr [] st4 (.localVar "merkleNode") = some vnode := by
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
  change ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH).world.memory 0).val
      = (stH.world.memory 0).val
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero_val_of_parity
    "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH
    vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
    mIdx hparOff h1 h2 h3 h4 h5off h5val h6off h6val

/-- The remaining C13 layer-site facts needed to prove that one XMSS Merkle
step preserves seed cell `0x00`: bounded `"mIdx"`, the masked auth-sibling load,
and the assembled parent ADRS word. -/
def LayerMerkleEvalFacts (s : RuntimeState) (idx : Nat) : Prop :=
  ∃ mIdx vsib vadr,
    lookupValue s.bindings "mIdx" = mIdx ∧
    mIdx < 2 ^ 256 ∧
    evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some vsib ∧
    evalExpr []
        { s with bindings :=
          (bindValue
            (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
            "parentIdx" (mIdx >>> 1)) }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr

/-- Layer-shaped address-assembly evaluator for the XMSS Merkle climb.  Once the
loop has bound `"h"`, stmt 1 has bound `"sibling"`, and stmt 2 has bound
`"parentIdx"`, the stmt-3 ADRS expression evaluates to some word under ordinary
boundedness hypotheses. -/
theorem layer_address_assembly_eval_exists
    (s : RuntimeState) (idx vsib treeAdrs mIdx : Nat)
    (hTree : lookupValue s.bindings "treeAdrs" = treeAdrs)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (hmIdxLt : mIdx < 2 ^ 256)
    (hidx : idx < 11) :
    ∃ vadr,
      evalExpr []
          { s with bindings :=
            (bindValue
              (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
              "parentIdx" (mIdx >>> 1)) }
          (.bitOr (.localVar "treeAdrs")
            (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
              (.localVar "parentIdx"))) = some vadr := by
  let stA : RuntimeState :=
    { s with bindings :=
      (bindValue
        (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
        "parentIdx" (mIdx >>> 1)) }
  let p : Nat := mIdx >>> 1
  let hword : Nat := idx + 1
  let sh : Nat := hword <<< 32
  let inner : Nat := Nat.lor sh p
  let vadr : Nat := Nat.lor treeAdrs inner
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hwordlt : hword < 2 ^ 256 := by
    dsimp [hword]
    omega
  have hshlt : sh < 2 ^ 256 := by
    dsimp [sh, hword]
    rw [Nat.shiftLeft_eq]
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right (2 ^ 32) (Nat.succ_le_of_lt hidx))
      (by decide : 11 * 2 ^ 32 < 2 ^ 256)
  have hplt : p < 2 ^ 256 := by
    dsimp [p]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self mIdx (2 ^ 1)) hmIdxLt
  have htree_eval : evalExpr [] stA (.localVar "treeAdrs") = some treeAdrs := by
    show some (lookupValue stA.bindings "treeAdrs") = some treeAdrs
    dsimp [stA]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "treeAdrs" (mIdx >>> 1) (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "treeAdrs" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "treeAdrs" (wordNormalize idx) (by decide)]
    rw [hTree]
  have hh_eval : evalExpr [] stA (.localVar "h") = some idx := by
    show some (lookupValue stA.bindings "h") = some idx
    dsimp [stA]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "h" (mIdx >>> 1) (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "h" vsib (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have hparent_eval : evalExpr [] stA (.localVar "parentIdx") = some p := by
    show some (lookupValue stA.bindings "parentIdx") = some p
    dsimp [stA, p]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
  have hlit1 : evalExpr [] stA (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hplus : evalExpr [] stA (.add (.localVar "h") (.literal 1)) = some hword := by
    dsimp [hword]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      stA (.localVar "h") (.literal 1) idx 1 hh_eval hlit1 hidx256 (by decide) hwordlt
  have hlit32 : evalExpr [] stA (.literal 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hsh : evalExpr [] stA (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      = some sh := by
    dsimp [sh]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      stA (.literal 32) (.add (.localVar "h") (.literal 1)) 32 hword
      hlit32 hplus (by decide) hwordlt hshlt
  have hinner : evalExpr [] stA
      (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
        (.localVar "parentIdx")) = some inner := by
    dsimp [inner]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      stA (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx") sh p hsh hparent_eval hshlt hplt
  refine ⟨vadr, ?_⟩
  dsimp [vadr]
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    stA (.localVar "treeAdrs")
    (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx")) treeAdrs inner htree_eval hinner hTreeLt
    (Nat.bitwise_lt_two_pow hshlt hplt)

/-- Concrete layer Merkle-site package from the frozen C13 calldata image.  This
combines the masked sibling calldata read with the local ADRS assembly eval into
the exact existential shape consumed by `stepLayer_preserves_memory_zero_of_layer_eval_range`. -/
theorem layer_eval_facts_of_frozen_calldata
    (s : RuntimeState) (idx ap treeAdrs mIdx sOff : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "merklePtr" = ap)
    (hTree : lookupValue s.bindings "treeAdrs" = treeAdrs)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (hmIdx : lookupValue s.bindings "mIdx" = mIdx)
    (hmIdxLt : mIdx < 2 ^ 256)
    (hidx : idx < 11)
    (haplt : ap < 2 ^ 256)
    (hshift : idx <<< 4 < 2 ^ 256)
    (hsum : ap + idx <<< 4 < 2 ^ 256)
    (hoff : ap + idx <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff)
    (hoff4 : 4 ≤ SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff) :
    LayerMerkleEvalFacts s idx := by
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vsib : Nat :=
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (Compiler.Proofs.YulGeneration.calldataloadWord 0
        (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
        (SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff))
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hselH : stH.selector = 0 := by
    dsimp [stH]
    exact hsel
  have hcdH : stH.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig := by
    dsimp [stH]
    exact hcd
  have hapH : evalExpr [] stH (.localVar "merklePtr") = some ap := by
    show some (lookupValue stH.bindings "merklePtr") = some ap
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "merklePtr" (wordNormalize idx) (by decide)]
    rw [hap]
  have hhH : evalExpr [] stH (.localVar "h") = some idx := by
    show some (lookupValue stH.bindings "h") = some idx
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have h1 : evalExpr [] stH
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some vsib := by
    dsimp [vsib]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_sibling_read_frozen
      stH "merklePtr" pkSeed pkRoot message sig ap idx sOff
      hselH hcdH hapH hhH haplt hidx256 hshift hsum hoff hoff4
  rcases layer_address_assembly_eval_exists s idx vsib treeAdrs mIdx
      hTree hTreeLt hmIdxLt hidx with
    ⟨vadr, h3⟩
  exact ⟨mIdx, vsib, vadr, hmIdx, hmIdxLt, h1, h3⟩

/-- Layer-specialized frozen-calldata Merkle-site package.  For `layer < 2`, the
layer setup has `merklePtr = sigDataOffset + (1952 + 868*layer + 692)`, and
height `idx < 11` reads the auth-path word at byte offset
`1952 + 868*layer + 692 + 16*idx` inside the signature. -/
theorem layer_eval_facts_of_c13_frozen_calldata
    (s : RuntimeState) (layer idx treeAdrs mIdx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsel : s.selector = 0)
    (hcd : s.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : lookupValue s.bindings "merklePtr"
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (1952 + 868 * layer + 692))
    (hTree : lookupValue s.bindings "treeAdrs" = treeAdrs)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (hmIdx : lookupValue s.bindings "mIdx" = mIdx)
    (hmIdxLt : mIdx < 2 ^ 256)
    (hlayer : layer < 2)
    (hidx : idx < 11) :
    LayerMerkleEvalFacts s idx := by
  let ap : Nat := SphincsMinusVerifiers.MkC13State.sigDataOffset + (1952 + 868 * layer + 692)
  let sOff : Nat := 1952 + 868 * layer + 692 + 16 * idx
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
  exact layer_eval_facts_of_frozen_calldata s idx ap treeAdrs mIdx sOff
    pkSeed pkRoot message sig hsel hcd hap hTree hTreeLt hmIdx hmIdxLt hidx
    haplt hshift hsum hoff hoff4

/-- Frozen C13 layer Merkle-site invariant threaded through the XMSS climb.  The
selector/calldata and address-pointer bindings are static; `"mIdx"` moves by
`>>> 1` on each step, so the invariant only records its EVM-word bound. -/
def LayerFrozenSite
    (layer : Nat) (pkSeed pkRoot message sig : ByteArray) (s : RuntimeState) : Prop :=
  ∃ treeAdrs,
    s.selector = 0 ∧
    s.world.calldata =
      SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
        ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig ∧
    lookupValue s.bindings "merklePtr" =
      SphincsMinusVerifiers.MkC13State.sigDataOffset + (1952 + 868 * layer + 692) ∧
    lookupValue s.bindings "treeAdrs" = treeAdrs ∧
    treeAdrs < 2 ^ 256 ∧
    lookupValue s.bindings "mIdx" < 2 ^ 256

/-- One layer Merkle step preserves the seed cell from a frozen C13 layer site. -/
theorem stepMerkle_preserves_seed_slot_of_layer_frozen_calldata
    (s : RuntimeState) (layer idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : LayerFrozenSite layer pkSeed pkRoot message sig s)
    (hlayer : layer < 2)
    (hidx : idx < 11) :
    ((stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
        0x00).val =
      (s.world.memory 0x00).val := by
  rcases hsite with ⟨treeAdrs, hsel, hcd, hap, hTree, hTreeLt, hmIdxLt⟩
  rcases layer_eval_facts_of_c13_frozen_calldata
      s layer idx treeAdrs (lookupValue s.bindings "mIdx")
      pkSeed pkRoot message sig hsel hcd hap hTree hTreeLt rfl hmIdxLt hlayer hidx with
    ⟨mIdx, vsib, vadr, hmIdx, hmIdxLt', h1, h3⟩
  exact stepMerkle_preserves_seed_slot_of_layer_eval
    s idx mIdx vsib vadr hmIdx hmIdxLt' h1 h3

/-- One layer Merkle step preserves the frozen-site invariant. -/
theorem stepMerkle_preserves_layerFrozenSite
    (s : RuntimeState) (layer idx : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hsite : LayerFrozenSite layer pkSeed pkRoot message sig s)
    (hlayer : layer < 2)
    (hidx : idx < 11) :
    LayerFrozenSite layer pkSeed pkRoot message sig
      (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }) := by
  rcases hsite with ⟨treeAdrs, hsel, hcd, hap, hTree, hTreeLt, hmIdxLt⟩
  rcases layer_eval_facts_of_c13_frozen_calldata
      s layer idx treeAdrs (lookupValue s.bindings "mIdx")
      pkSeed pkRoot message sig hsel hcd hap hTree hTreeLt rfl hmIdxLt hlayer hidx with
    ⟨mIdx, vsib, vadr, hmIdx, hmIdxLt', h1, h3⟩
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := mIdx >>> 1
  let sval : Nat := (Nat.land mIdx 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory :=
        SphincsMinusVerifiers.MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let vnode : Nat := lookupValue st4.bindings "merkleNode"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory :=
        SphincsMinusVerifiers.MemoryKit.memUpdate st4.world.memory o5 vnode } }
  have hmIdxH : lookupValue stH.bindings "mIdx" = mIdx := by
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "mIdx" (wordNormalize idx) (by decide)]
    exact hmIdx
  have hmIdx1 : lookupValue st1.bindings "mIdx" = mIdx := by
    dsimp [st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "mIdx" vsib (by decide)]
    exact hmIdxH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "mIdx")) = some vpar := by
    dsimp [vpar]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "mIdx" st1 mIdx hmIdx1 hmIdxLt'
  have hmIdx3 : lookupValue st3.bindings "mIdx" = mIdx := by
    dsimp [st3, st2, st1]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      (bindValue stH.bindings "sibling" vsib) "parentIdx" "mIdx" vpar (by decide)]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      stH.bindings "sibling" "mIdx" vsib (by decide)]
    exact hmIdxH
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "mIdx" st3 mIdx hmIdx3 hmIdxLt'
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
  have h5val : evalExpr [] st4 (.localVar "merkleNode") = some vnode := by
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
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_selector_calldata
      "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      h1 h2 h3 h4 h5off h5val h6off h6val
  have hptrStep :
      lookupValue
        (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH).bindings
          "merklePtr" =
        SphincsMinusVerifiers.MkC13State.sigDataOffset + (1952 + 868 * layer + 692) := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_binding_frozen
      "merkleNode" "mIdx" "treeAdrs" "merklePtr" "merklePtr" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "merklePtr" (wordNormalize idx) (by decide)]
    exact hap
  have htreeStep :
      lookupValue
        (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH).bindings
          "treeAdrs" = treeAdrs := by
    rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_binding_frozen
      "merkleNode" "mIdx" "treeAdrs" "merklePtr" "treeAdrs" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h1 h2 h3 h4 h5off h5val h6off h6val]
    dsimp [stH]
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "treeAdrs" (wordNormalize idx) (by decide)]
    exact hTree
  have hmIdxStepEq :
      lookupValue
        (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH).bindings
          "mIdx" = vpar :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_idx_binding
      "merkleNode" "mIdx" "treeAdrs" "merklePtr" stH
      vsib vpar vadr sval o5 vnode o6 (lookupValue st5.bindings "sibling")
      (by decide) h1 h2 h3 h4 h5off h5val h6off h6val
  have hvparlt : vpar < 2 ^ 256 := by
    dsimp [vpar]
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hmIdxLt'
  refine ⟨treeAdrs, hsc.1.trans hsel, hsc.2.trans hcd, hptrStep, htreeStep, hTreeLt, ?_⟩
  rw [hmIdxStepEq]
  exact hvparlt

/-- Pure XMSS layer Merkle-loop site invariant over the actual loop states. -/
theorem foldLoop_preserves_layerFrozenSite_range
    (layer : Nat) (pkSeed pkRoot message sig : ByteArray) (hlayer : layer < 2) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 11) →
      LayerFrozenSite layer pkSeed pkRoot message sig state →
      LayerFrozenSite layer pkSeed pkRoot message sig
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
          state index remaining)
  | state, _, 0, _, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
      exact hsite
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      exact foldLoop_preserves_layerFrozenSite_range layer pkSeed pkRoot message sig hlayer
        (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) })
        (index + 1) remaining
        (fun i hi1 hi2 => hD i (by omega) (by omega))
        (stepMerkle_preserves_layerFrozenSite
          state layer index pkSeed pkRoot message sig hsite hlayer
          (hD index (by omega) (by omega)))

/-- Pure XMSS layer Merkle-loop seed-cell frame from the concrete frozen-site
invariant, threaded over the actual loop states. -/
theorem foldLoop_preserves_seed_slot_of_layerFrozenSite_range
    (layer : Nat) (pkSeed pkRoot message sig : ByteArray) (hlayer : layer < 2) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → i < 11) →
      LayerFrozenSite layer pkSeed pkRoot message sig state →
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
          state index remaining).world.memory 0x00).val
        = (state.world.memory 0x00).val
  | state, _, 0, _, _ => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  | state, index, remaining + 1, hD, hsite => by
      rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ]
      let stepState : RuntimeState :=
        stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          { state with bindings := bindValue state.bindings "h" (wordNormalize index) }
      have hstepMem : (stepState.world.memory 0x00).val = (state.world.memory 0x00).val := by
        exact stepMerkle_preserves_seed_slot_of_layer_frozen_calldata
          state layer index pkSeed pkRoot message sig hsite hlayer
          (hD index (by omega) (by omega))
      have hstepSite : LayerFrozenSite layer pkSeed pkRoot message sig stepState := by
        exact stepMerkle_preserves_layerFrozenSite
          state layer index pkSeed pkRoot message sig hsite hlayer
          (hD index (by omega) (by omega))
      have hrec :
          ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
              (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
              stepState (index + 1) remaining).world.memory 0x00).val
            = (stepState.world.memory 0x00).val :=
        foldLoop_preserves_seed_slot_of_layerFrozenSite_range
          layer pkSeed pkRoot message sig hlayer stepState (index + 1) remaining
          (fun i hi1 hi2 => hD i (by omega) (by omega))
          hstepSite
      exact hrec.trans hstepMem

/-- The folded XMSS layer Merkle climb preserves the seed cell from a frozen
site at `beforeMerkle`.  The initial `"h"` loop binding touches only bindings,
so it preserves the frozen site and the seed cell. -/
theorem afterMerkle_preserves_memory_zero_of_layerFrozenSite_range
    (ls : RuntimeState) (layer : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hlayer : layer < 2)
    (hsite : LayerFrozenSite layer pkSeed pkRoot message sig (SegmentLayer3.beforeMerkle ls)) :
    ((SegmentLayer3.afterMerkle ls).world.memory 0x00).val =
      ((SegmentLayer3.afterDigit ls).world.memory 0x00).val := by
  let stH : RuntimeState :=
    { SegmentLayer3.beforeMerkle ls with
      bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h" (wordNormalize 0) }
  have hsiteH : LayerFrozenSite layer pkSeed pkRoot message sig stH := by
    rcases hsite with ⟨treeAdrs, hsel, hcd, hap, hTree, hTreeLt, hmIdxLt⟩
    refine ⟨treeAdrs, ?_, ?_, ?_, ?_, hTreeLt, ?_⟩
    · dsimp [stH]
      exact hsel
    · dsimp [stH]
      exact hcd
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        (SegmentLayer3.beforeMerkle ls).bindings "h" "merklePtr" (wordNormalize 0) (by decide)]
      exact hap
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        (SegmentLayer3.beforeMerkle ls).bindings "h" "treeAdrs" (wordNormalize 0) (by decide)]
      exact hTree
    · dsimp [stH]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        (SegmentLayer3.beforeMerkle ls).bindings "h" "mIdx" (wordNormalize 0) (by decide)]
      exact hmIdxLt
  have hFold :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
          stH 0 (wordNormalize 11)).world.memory 0x00).val =
        (stH.world.memory 0x00).val := by
    exact foldLoop_preserves_seed_slot_of_layerFrozenSite_range
      layer pkSeed pkRoot message sig hlayer stH 0 (wordNormalize 11)
      (fun i _ hi2 => by
        rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
          Nat.mod_eq_of_lt (by decide : 11 < 2 ^ 256)] at hi2
        omega)
      hsiteH
  unfold SegmentLayer3.afterMerkle
  rw [hFold]
  exact SegmentLayer3.beforeMerkle_preserves_memory_zero_of_loop_frames ls hWots hCopy

/-- One accepting C13 layer iteration preserves seed cell `0x00` from a concrete
frozen site at its `beforeMerkle` cutpoint. -/
theorem stepLayer_preserves_memory_zero_of_layerFrozenSite_range
    (ls : RuntimeState) (layer : Nat)
    (pkSeed pkRoot message sig : ByteArray)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hlayer : layer < 2)
    (hsite : LayerFrozenSite layer pkSeed pkRoot message sig (SegmentLayer3.beforeMerkle ls)) :
    ((SegmentLayer3.stepLayer ls).world.memory 0x00).val =
      ((SegmentLayer3.afterDigit ls).world.memory 0x00).val := by
  have hTail := SegmentLayer3.finalLayerTail_preserves_memory_zero (SegmentLayer3.afterMerkle ls)
  rw [SegmentLayer3.finalLayerTail_continues_from_afterMerkle ls] at hTail
  rw [hTail]
  exact afterMerkle_preserves_memory_zero_of_layerFrozenSite_range
    ls layer pkSeed pkRoot message sig hWots hCopy hlayer hsite

/-- One accepting layer iteration preserves seed cell `0x00` once the WOTS/copy
loop frames are supplied and the Merkle loop's per-height site facts are reduced
to `LayerMerkleEvalFacts`. -/
theorem stepLayer_preserves_memory_zero_of_layer_eval_range
    (ls : RuntimeState) (D : Nat → Prop)
    (hWots :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.wotsOuterBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hCopy :
      ∀ (s s'' : RuntimeState),
        execStmt [] s (.forEach "i" (.literal 43) SegmentLayer3.copyBody) = .continue s'' →
        (s''.world.memory 0x00).val = (s.world.memory 0x00).val)
    (hFacts :
      ∀ (s : RuntimeState) (idx : Nat), D idx → LayerMerkleEvalFacts s idx)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 11 → D i) :
    ((SegmentLayer3.stepLayer ls).world.memory 0x00).val =
      ((SegmentLayer3.afterDigit ls).world.memory 0x00).val := by
  refine SegmentLayer3.stepLayer_preserves_memory_zero_of_loop_frames_range
    ls D hWots hCopy ?_ hD
  intro s idx hidx
  rcases hFacts s idx hidx with ⟨mIdx, vsib, vadr, hmIdx, hmIdxLt, h1, h3⟩
  exact stepMerkle_preserves_seed_slot_of_layer_eval
    s idx mIdx vsib vadr hmIdx hmIdxLt h1 h3

#print axioms stepMerkle_preserves_seed_slot_of_layer_eval
#print axioms LayerMerkleEvalFacts
#print axioms layer_address_assembly_eval_exists
#print axioms layer_eval_facts_of_frozen_calldata
#print axioms layer_eval_facts_of_c13_frozen_calldata
#print axioms LayerFrozenSite
#print axioms stepMerkle_preserves_seed_slot_of_layer_frozen_calldata
#print axioms stepMerkle_preserves_layerFrozenSite
#print axioms foldLoop_preserves_layerFrozenSite_range
#print axioms foldLoop_preserves_seed_slot_of_layerFrozenSite_range
#print axioms afterMerkle_preserves_memory_zero_of_layerFrozenSite_range
#print axioms stepLayer_preserves_memory_zero_of_layerFrozenSite_range
#print axioms stepLayer_preserves_memory_zero_of_layer_eval_range

end SphincsMinusVerifiers.SegmentLayer3MerkleFrame
