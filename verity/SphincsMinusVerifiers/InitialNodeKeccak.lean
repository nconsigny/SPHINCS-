/-
  InitialNodeKeccak — the climb-entry (initial leaf) node correspondences for the
  C13 accept path.

  Each Merkle climb in the C13 verifier starts from an INITIAL leaf node that the
  model computes as a masked keccak over a word-aligned scratch image:

    * the FORS tree climb starts from the FORS *leaf* keccak
      `and(keccak256(0x00, 0x60), N_MASK)` over the 3-word preimage
      `seed ‖ FORS_LEAF adrs ‖ sk` (`SegmentS4Fors.forsLeafBody` stmt `node`);
    * the XMSS hypertree layer climb starts from the WOTS *public-key* keccak
      `and(keccak256(0x00, 0x5A0), N_MASK)` over the 45-word preimage
      `seed ‖ WOTS_PK adrs ‖ chain_0..chain_42` (`SegmentLayer3.suffix14` stmt
      `wotsPk`).

  This file proves that, GIVEN the scratch memory cells hold the spec preimage
  words, the interpreter's masked keccak resolves to exactly the spec kernel's
  initial node value (`C13Concrete.maskN (keccakWords …)` — the FORS leaf of
  `forsPkFromSigC13`, resp. the WOTS public key `wotsPkWord`).  It is the
  `hR` (initial-node) half of the climb-loop lift, isolated from the per-step
  `hstep` frame bookkeeping.

  Both lemmas are thin specialisations of the reusable masking combine
  `ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN` (itself built on
  `KeccakBridge.evalExpr_keccak256_eq_keccakWords`): they evaluate no keccak and
  assert nothing about which words sit in scratch — that memory-frame obligation
  is the hypothesis.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbKeccakStep

namespace SphincsMinusVerifiers.InitialNodeKeccak

open Compiler.Proofs.IRGeneration.SourceSemantics (RuntimeState evalExpr wordNormalize wordNormalize_eq_mod)
open SphincsMinusVerifierSpec (WotsSig Bytes)
open SphincsMinusVerifierSpec.C13Concrete
  (maskN nMask keccakWords adrsForsLeaf adrsWotsPk wotsPkWord wordOfHash16
   wotsDigest adrsWotsHashBase chainHash)
open SphincsMinusVerifiers.ClimbKeccakStep (evalExpr_maskedKeccak_eq_maskN)

/-! ## 1. The FORS leaf initial node (3-word `keccak256(0x00, 0x60)`).

The FORS climb's seed node binding (`SegmentS4Fors.forsLeafBody` `node`) is
`and(keccak256(0x00, 0x60), N_MASK)` over the 3-word scratch
`seed ‖ FORS_LEAF adrs ‖ sk`.  Given those three cells, it resolves to the spec
`maskN (keccakWords [seed, adrs, sk])` — exactly the `leaf` of
`forsPkFromSigC13` when `adrs = adrsForsLeaf 0 0 i treeIdx` and `sk = wordOfHash16 …`. -/
theorem fors_leaf_node_eq (st : RuntimeState) (seed adrs sk : Nat)
    (hm0 : (st.world.memory 0).val = seed)
    (hm1 : (st.world.memory 0x20).val = adrs)
    (hm2 : (st.world.memory 0x40).val = sk) :
    evalExpr [] st (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal nMask))
      = some (maskN (keccakWords [seed, adrs, sk])) := by
  have hoff : wordNormalize (0 : Nat) = 0 := by
    rw [wordNormalize_eq_mod]; exact Nat.zero_mod _
  have hszlt : 32 * ([seed, adrs, sk] : List Nat).length < 2 ^ 256 := by
    show (96 : Nat) < 2 ^ 256; decide
  have hmem : ∀ i, (h : i < ([seed, adrs, sk] : List Nat).length) →
      (st.world.memory (0 + 32 * i)).val = ([seed, adrs, sk] : List Nat)[i] := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i, hi with
    | 0, _ => show (st.world.memory 0).val = seed; exact hm0
    | 1, _ => show (st.world.memory 0x20).val = adrs; exact hm1
    | 2, _ => show (st.world.memory 0x40).val = sk; exact hm2
    | (n + 3), hbad => exact absurd hbad (by omega)
  have key := evalExpr_maskedKeccak_eq_maskN st 0 [seed, adrs, sk] hoff hszlt hmem
  have hsz : 32 * ([seed, adrs, sk] : List Nat).length = 0x60 := rfl
  rw [hsz] at key
  exact key

/-! ## 2. The WOTS public-key initial node (45-word `keccak256(0x00, 0x5A0)`).

The XMSS hypertree layer climb's seed node binding (`SegmentLayer3.suffix14`
`wotsPk`, copied to `merkleNode`) is `and(keccak256(0x00, 0x5A0), N_MASK)` over the
45-word scratch `seed ‖ WOTS_PK adrs ‖ chain_0..chain_42`.  Given those cells, it
resolves to the spec `maskN (keccakWords (seed :: pkAdrs :: chainsEnd))` — exactly
the final keccak of `wotsPkWord` when `pkAdrs = adrsWotsPk layer treeIdx leafIdx`
and `chainsEnd` is the layer's reconstructed WOTS chain ends. -/
theorem wots_pk_node_eq (st : RuntimeState) (seed pkAdrs : Nat) (chainsEnd : List Nat)
    (hlen : chainsEnd.length = 43)
    (hm0 : (st.world.memory 0).val = seed)
    (hm1 : (st.world.memory 0x20).val = pkAdrs)
    (hmC : ∀ j, (h : j < 43) → (st.world.memory (0x40 + 32 * j)).val = chainsEnd[j]) :
    evalExpr [] st (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0)) (.literal nMask))
      = some (maskN (keccakWords (seed :: pkAdrs :: chainsEnd))) := by
  have hoff : wordNormalize (0 : Nat) = 0 := by
    rw [wordNormalize_eq_mod]; exact Nat.zero_mod _
  have hlen45 : (seed :: pkAdrs :: chainsEnd).length = 45 := by
    simp only [List.length_cons, hlen]
  have hszlt : 32 * (seed :: pkAdrs :: chainsEnd).length < 2 ^ 256 := by
    rw [hlen45]; decide
  have hmem : ∀ i, (h : i < (seed :: pkAdrs :: chainsEnd).length) →
      (st.world.memory (0 + 32 * i)).val = (seed :: pkAdrs :: chainsEnd)[i] := by
    intro i hi
    match i with
    | 0 => simpa using hm0
    | 1 => simpa using hm1
    | (j + 2) =>
      have hj : j < 43 := by
        rw [hlen45] at hi; omega
      have hoffj : (0 : Nat) + 32 * (j + 2) = 0x40 + 32 * j := by omega
      rw [hoffj]
      show (st.world.memory (0x40 + 32 * j)).val = chainsEnd[j]
      exact hmC j hj
  have key := evalExpr_maskedKeccak_eq_maskN st 0 (seed :: pkAdrs :: chainsEnd) hoff hszlt hmem
  have hsz : 32 * (seed :: pkAdrs :: chainsEnd).length = 0x5A0 := by rw [hlen45]
  rw [hsz] at key
  exact key

/-! ## 3. Spec-shaped corollaries — pinning the model node to the named kernel
initial-node values (`C13Concrete`'s FORS leaf / `wotsPkWord`). -/

/-- The FORS leaf node in its *spec* shape: with the scratch holding
`seed ‖ adrsForsLeaf idxTree0 idxLeaf0 i treeIdx ‖ wordOfHash16 sk`, the model's
`and(keccak256(0x00,0x60), N_MASK)` resolves to exactly the `leaf` value
`forsPkFromSigC13` builds at the FIPS digits. -/
theorem fors_leaf_node_eq_spec (st : RuntimeState)
    (seed idxTree0 idxLeaf0 i treeIdx : Nat) (sk : Bytes)
    (hm0 : (st.world.memory 0).val = seed)
    (hm1 : (st.world.memory 0x20).val = adrsForsLeaf idxTree0 idxLeaf0 i treeIdx)
    (hm2 : (st.world.memory 0x40).val = wordOfHash16 sk) :
    evalExpr [] st (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal nMask))
      = some (maskN
          (keccakWords [seed, adrsForsLeaf idxTree0 idxLeaf0 i treeIdx, wordOfHash16 sk])) :=
  fors_leaf_node_eq st seed (adrsForsLeaf idxTree0 idxLeaf0 i treeIdx) (wordOfHash16 sk)
    hm0 hm1 hm2

/-- The WOTS chain ends of one layer, extracted verbatim from `wotsPkWord`'s
internal `let chainsEnd`, so the unfolding `wotsPkWord_eq` holds by `rfl`. -/
def wotsChainsEnd (seed : Nat) (layer treeIdx leafIdx : Nat) (node : Nat)
    (wots : WotsSig) : List Nat :=
  let d := wotsDigest seed layer treeIdx leafIdx wots.count node
  let wotsAdrs := adrsWotsHashBase layer treeIdx leafIdx
  (List.range 43).map (fun i =>
    let digit := (d >>> (3 * i)) % 8
    let steps := 7 - digit
    let val := wordOfHash16 ((wots.chains[i]?).getD ⟨#[]⟩)
    let chainBase := wotsAdrs ||| (i <<< 32)
    chainHash seed chainBase digit steps 0 val)

theorem wotsChainsEnd_length (seed : Nat) (layer treeIdx leafIdx node : Nat)
    (wots : WotsSig) : (wotsChainsEnd seed layer treeIdx leafIdx node wots).length = 43 := by
  simp [wotsChainsEnd]

/-- `wotsPkWord` is exactly `maskN (keccakWords (seed :: WOTS_PK adrs :: chainEnds))`. -/
theorem wotsPkWord_eq (seed : Nat) (layer treeIdx leafIdx node : Nat) (wots : WotsSig) :
    wotsPkWord seed layer treeIdx leafIdx node wots
      = maskN (keccakWords (seed :: adrsWotsPk layer treeIdx leafIdx
          :: wotsChainsEnd seed layer treeIdx leafIdx node wots)) := rfl

/-- The WOTS public key node in its *spec* shape: with the scratch holding
`seed ‖ adrsWotsPk layer treeIdx leafIdx ‖ chainEnds`, the model's
`and(keccak256(0x00,0x5A0), N_MASK)` resolves to exactly `wotsPkWord …`. -/
theorem wots_pk_node_eq_spec (st : RuntimeState) (seed : Nat)
    (layer treeIdx leafIdx node : Nat) (wots : WotsSig)
    (hm0 : (st.world.memory 0).val = seed)
    (hm1 : (st.world.memory 0x20).val = adrsWotsPk layer treeIdx leafIdx)
    (hmC : ∀ j, (h : j < 43) →
        (st.world.memory (0x40 + 32 * j)).val
          = (wotsChainsEnd seed layer treeIdx leafIdx node wots)[j]'(by
              rw [wotsChainsEnd_length]; omega)) :
    evalExpr [] st (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0)) (.literal nMask))
      = some (wotsPkWord seed layer treeIdx leafIdx node wots) := by
  rw [wotsPkWord_eq]
  exact wots_pk_node_eq st seed (adrsWotsPk layer treeIdx leafIdx)
    (wotsChainsEnd seed layer treeIdx leafIdx node wots)
    (wotsChainsEnd_length seed layer treeIdx leafIdx node wots) hm0 hm1 hmC

/-! ## 4. Axiom audit. -/

#print axioms fors_leaf_node_eq
#print axioms wots_pk_node_eq
#print axioms fors_leaf_node_eq_spec
#print axioms wotsPkWord_eq
#print axioms wots_pk_node_eq_spec

end SphincsMinusVerifiers.InitialNodeKeccak
