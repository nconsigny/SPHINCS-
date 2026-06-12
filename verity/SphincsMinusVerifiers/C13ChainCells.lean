/-
  C13ChainCells — C13-specialized WOTS outer/copy chain-cell closure.

  This module keeps the C13 calldata/parsing specialization for the WOTS chain
  cells separate from the full `SegmentLayer3` body reconstruction.  It imports
  only the lightweight WOTS/copy loop facts from `SegmentLayer3CopyCells`.
-/

import SphincsMinusVerifiers.SegmentLayer3CopyCells
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

/-- Successful C13 parsing identifies each WOTS chain entry with the matching
16-byte signature slice from the two-layer C13 XMSS layout. -/
theorem c13_layer_wotsChain_read16_of_parse
    (sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (layer k : Nat) (hlayer : layer < 2) (hk : k < 43)
    (lsig : XmssLayerSig)
    (hLayer : sigParsed.layers[layer]? = some lsig) :
    (lsig.wots.chains[k]?).getD ⟨#[]⟩ =
      C13Concrete.read16 sig (1952 + 868 * layer + 16 * k) := by
  have hGet :
      lsig.wots.chains[k]? =
        some (C13Concrete.read16 sig (1952 + 868 * layer + 16 * k)) :=
    C13Concrete.parseSignatureC13_layer_wots_chain_getElem?
      (v := c13) (sig := sig) (s := sigParsed) hParse hlayer hLayer hk
  rw [hGet]
  rfl

/-- Layer-0 WOTS outer/copy-loop cell handoff specialized to C13 calldata.
The caller supplies the executable loop invariants; the raw WOTS chain words are
identified from the parsed C13 layer and frozen ABI calldata image here. -/
theorem c13Layer0_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (hSeed : ∀ j, j < 43 →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hD : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings "d" =
        C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
          0 treeIdx leafIdx lsig.wots.count node)
    (hAdrs : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
          "wotsAdrs" =
        C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx)
    (hWPtr : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
          "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ j, j < 43 → ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world = (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world →
        evalExpr [] s
            (.calldataload
              (.add (.localVar "wotsPtr")
                (.shl (.literal 4) (.localVar "i")))) =
          some (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
            (sigDataOffset + (1952 + 16 * j)))) :
    ∀ j, (hj : j < 43) →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43).world.memory
          (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0 treeIdx leafIdx node
          lsig.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega) := by
  let rawAt : Nat → Nat := fun j =>
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (sigDataOffset + (1952 + 16 * j))
  have hRaw : ∀ j, j < 43 → rawAt j < 2 ^ 256 := by
    intro j hj
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.calldataloadWord_lt_of_ge4 0
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (sigDataOffset + (1952 + 16 * j))
      (by
        show 4 ≤ 164 + (1952 + 16 * j)
        omega)
  have hRawChain : ∀ j, j < 43 →
      C13Concrete.maskN (rawAt j) =
        C13Concrete.wordOfHash16 ((lsig.wots.chains[j]?).getD ⟨#[]⟩) := by
    intro j hj
    have hRead :=
      c13_layer_wotsChain_read16_of_parse sig sigParsed hParse
        0 j (by decide : 0 < 2) hj lsig hLayer0
    have hGen :=
      SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
        pkSeed pkRoot message sig (1952 + 16 * j)
    simpa [rawAt, C13Concrete.maskN, hRead] using hGen
  exact SphincsMinusVerifiers.SegmentLayer3CopyCells.copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    st (C13Concrete.wordOfHash16 pkSeed) 0 treeIdx leafIdx node wotsPtr
    rawAt lsig.wots hDigestLt hAdrsLt hRaw hSeed hD hAdrs hWPtr hCdLoad
    hRawChain

/-- Layer-1 WOTS outer/copy-loop cell handoff specialized to C13 calldata.
This is the layer-1 analogue of
`c13Layer0_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43`; the only
calldata difference is the layer-1 WOTS-chain base offset
`1952 + 868 + 16*j`. -/
theorem c13Layer1_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx < 2 ^ 256)
    (hSeed : ∀ j, j < 43 →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hD : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings "d" =
        C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
          1 treeIdx leafIdx lsig.wots.count node)
    (hAdrs : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
          "wotsAdrs" =
        C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx)
    (hWPtr : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
          "wotsPtr" = wotsPtr)
    (hCdLoad : ∀ j, j < 43 → ∀ (s : RuntimeState),
        lookupValue s.bindings "wotsPtr" = wotsPtr →
        lookupValue s.bindings "i" = j →
        s.world = (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world →
        evalExpr [] s
            (.calldataload
              (.add (.localVar "wotsPtr")
                (.shl (.literal 4) (.localVar "i")))) =
          some (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
            (sigDataOffset + (1952 + 868 + 16 * j)))) :
    ∀ j, (hj : j < 43) →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43).world.memory
          (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 1 treeIdx leafIdx node
          lsig.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega) := by
  let rawAt : Nat → Nat := fun j =>
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (sigDataOffset + (1952 + 868 + 16 * j))
  have hRaw : ∀ j, j < 43 → rawAt j < 2 ^ 256 := by
    intro j hj
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.calldataloadWord_lt_of_ge4 0
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (sigDataOffset + (1952 + 868 + 16 * j))
      (by
        show 4 ≤ 164 + (1952 + 868 + 16 * j)
        omega)
  have hRawChain : ∀ j, j < 43 →
      C13Concrete.maskN (rawAt j) =
        C13Concrete.wordOfHash16 ((lsig.wots.chains[j]?).getD ⟨#[]⟩) := by
    intro j hj
    have hRead :=
      c13_layer_wotsChain_read16_of_parse sig sigParsed hParse
        1 j (by decide : 1 < 2) hj lsig hLayer1
    have hGen :=
      SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
        pkSeed pkRoot message sig (1952 + 868 + 16 * j)
    simpa [rawAt, C13Concrete.maskN, hRead] using hGen
  exact SphincsMinusVerifiers.SegmentLayer3CopyCells.copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    st (C13Concrete.wordOfHash16 pkSeed) 1 treeIdx leafIdx node wotsPtr
    rawAt lsig.wots hDigestLt hAdrsLt hRaw hSeed hD hAdrs hWPtr hCdLoad
    hRawChain

#print axioms c13_layer_wotsChain_read16_of_parse
#print axioms c13Layer0_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
#print axioms c13Layer1_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43

end SphincsMinusVerifiers
