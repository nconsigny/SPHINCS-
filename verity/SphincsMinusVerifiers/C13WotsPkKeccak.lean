/-
  C13WotsPkKeccak — final C13 WOTS-PK Keccak values from compact chain-cell
  closures.

  This module is intentionally separate from `C13ChainCells`: the main
  `Proofs.lean` file imports the older chain-cell closures, while these final
  value lemmas can be checked and cached independently before integration.
-/

import SphincsMinusVerifiers.C13ChainCells
import SphincsMinusVerifiers.C13WotsOuterInputs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

/-- Composed C13 layer-0 final WOTS-PK Keccak from the WOTS-outer/copy-loop
calldata closure.  Given the WOTS-outer hypotheses that feed
`c13Layer0_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43`, plus the seed
and WOTS-PK-address cells at the post-copy state, the masked Keccak at the same
state resolves to the spec `wotsPkWord` for layer 0. -/
theorem c13Layer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
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
            (sigDataOffset + (1952 + 16 * j))))
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 0 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx node lsig.wots) :=
  SphincsMinusVerifiers.InitialNodeKeccak.wots_pk_node_eq_spec
    (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
      (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43)
    (C13Concrete.wordOfHash16 pkSeed) 0 treeIdx leafIdx node lsig.wots
    hMem0 hMem20
    (c13Layer0_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
      pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr lsig
      hParse hLayer0 hDigestLt hAdrsLt hSeed hD hAdrs hWPtr hCdLoad)

/-- Layer-1 analogue of
`c13Layer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43`; the calldata
difference is the layer-1 WOTS-chain base offset `1952 + 868 + 16*j`. -/
theorem c13Layer1_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
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
            (sigDataOffset + (1952 + 868 + 16 * j))))
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 1 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx node lsig.wots) :=
  SphincsMinusVerifiers.InitialNodeKeccak.wots_pk_node_eq_spec
    (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
      (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43)
    (C13Concrete.wordOfHash16 pkSeed) 1 treeIdx leafIdx node lsig.wots
    hMem0 hMem20
    (c13Layer1_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
      pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr lsig
      hParse hLayer1 hDigestLt hAdrsLt hSeed hD hAdrs hWPtr hCdLoad)

/-- Reverted-at-layer-1 path specialization of the layer-0 final WOTS-PK
Keccak lemma.  The only path-specific input consumed here is the concrete
`FoldHypertreeC13RevertedLayer1Data` record, which supplies the layer-0 XMSS
signature and parse fact; the executable loop facts remain the same compact
WOTS-outer inputs as in the accept path. -/
theorem c13RevertedLayer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx d.lsig0.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (hSeed : ∀ j, j < 43 →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hD : ∀ j, j < 43 →
      lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings "d" =
        C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
          0 treeIdx leafIdx d.lsig0.wots.count node)
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
            (sigDataOffset + (1952 + 16 * j))))
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 0 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx node d.lsig0.wots) :=
  c13Layer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr
    d.lsig0 hParse d.hLayer0 hDigestLt hAdrsLt
    hSeed hD hAdrs hWPtr hCdLoad hMem0 hMem20

/-- Record-driven layer-0 assembly: the four prefix loop invariants
(`hSeed`/`hD`/`hAdrs`/`hWPtr`) are discharged from a single compact
`C13WotsOuterEntry` entry-state record, leaving only the calldata-load and
post-copy memory facts as explicit inputs. -/
theorem c13Layer0_copyFold43_wotsPk_keccak_of_entry
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx) wotsPtr)
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
            (sigDataOffset + (1952 + 16 * j))))
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 0 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx node lsig.wots) :=
  c13Layer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr lsig
    hParse hLayer0 hDigestLt hAdrsLt e.hSeed e.hD e.hAdrs e.hWPtr hCdLoad hMem0 hMem20

/-- Record-driven layer-1 assembly (layer-1 calldata base `1952 + 868 + 16*j`). -/
theorem c13Layer1_copyFold43_wotsPk_keccak_of_entry
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx) wotsPtr)
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
            (sigDataOffset + (1952 + 868 + 16 * j))))
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 1 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx node lsig.wots) :=
  c13Layer1_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr lsig
    hParse hLayer1 hDigestLt hAdrsLt e.hSeed e.hD e.hAdrs e.hWPtr hCdLoad hMem0 hMem20

/-- Fully record-driven layer-0 assembly: the `hCdLoad` residual is discharged
from the compact entry-state calldata fact `hCdSt` via `wotsOuterFold_cdload_raw`,
with the WOTS pointer pinned to its layer-0 value `sigDataOffset + 1952`.  All
five WOTS-outer prefix inputs now reduce to the four scalar facts of the entry
record plus `hCdSt`. -/
theorem c13Layer0_copyFold43_wotsPk_keccak_of_inputs
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx) (sigDataOffset + 1952))
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 0 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx node lsig.wots) :=
  c13Layer0_copyFold43_wotsPk_keccak_of_entry
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node
    (sigDataOffset + 1952) lsig hParse hLayer0 hDigestLt hAdrsLt e
    (fun j hj s hWPtrS hIS hWorldS =>
      wotsOuterFold_cdload_raw pkSeed pkRoot message sig st 1952
        (by norm_num [sigDataOffset]) hCdSt j hj s hWPtrS hIS hWorldS)
    hMem0 hMem20

/-- Fully record-driven layer-1 assembly (WOTS pointer pinned to the layer-1
value `sigDataOffset + (1952 + 868)`). -/
theorem c13Layer1_copyFold43_wotsPk_keccak_of_inputs
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx) (sigDataOffset + (1952 + 868)))
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 1 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx node lsig.wots) :=
  c13Layer1_copyFold43_wotsPk_keccak_of_entry
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node
    (sigDataOffset + (1952 + 868)) lsig hParse hLayer1 hDigestLt hAdrsLt e
    (fun j hj s hWPtrS hIS hWorldS =>
      wotsOuterFold_cdload_raw pkSeed pkRoot message sig st (1952 + 868)
        (by norm_num [sigDataOffset]) hCdSt j hj s hWPtrS hIS hWorldS)
    hMem0 hMem20

/-- Fully record-driven reverted-at-layer-1 layer-0 assembly.  The path-specific
input is the concrete `FoldHypertreeC13RevertedLayer1Data` record `d`; the
executable loop inputs reduce to the entry record `e` plus the calldata fact
`hCdSt`, with the WOTS pointer pinned to `sigDataOffset + 1952`. -/
theorem c13RevertedLayer0_copyFold43_wotsPk_keccak_of_inputs
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node : Nat)
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx d.lsig0.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx d.lsig0.wots.count node)
      (C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx) (sigDataOffset + 1952))
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
    (hMem0 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hMem20 :
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory 0x20).val =
        C13Concrete.adrsWotsPk 0 treeIdx leafIdx) :
    evalExpr []
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal C13Concrete.nMask)) =
      some (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx node d.lsig0.wots) :=
  c13RevertedLayer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node
    (sigDataOffset + 1952) pk digest forsPk d hParse hDigestLt hAdrsLt
    e.hSeed e.hD e.hAdrs e.hWPtr
    (fun j hj s hWPtrS hIS hWorldS =>
      wotsOuterFold_cdload_raw pkSeed pkRoot message sig st 1952
        (by norm_num [sigDataOffset]) hCdSt j hj s hWPtrS hIS hWorldS)
    hMem0 hMem20

/-- Record-driven layer-0 chain-cells closure: the four WOTS-outer prefix loop
invariants are discharged from a single compact `C13WotsOuterEntry`, leaving only
the calldata-load residual.  Unlike the keccak assemblies this needs no post-copy
scratch facts (`hMem0`/`hMem20`) — the chain cells are the raw `wotsChainsEnd`
values, not the masked keccak digest. -/
theorem c13Layer0_copyFold43_wotsChainsEnd_cells_of_entry
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx) wotsPtr)
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
            omega) :=
  c13Layer0_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr lsig
    hParse hLayer0 hDigestLt hAdrsLt e.hSeed e.hD e.hAdrs e.hWPtr hCdLoad

/-- Record-driven layer-1 chain-cells closure (layer-1 calldata base
`1952 + 868 + 16*j`). -/
theorem c13Layer1_copyFold43_wotsChainsEnd_cells_of_entry
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node wotsPtr : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx) wotsPtr)
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
            omega) :=
  c13Layer1_copyFold43_wotsChainsEnd_cells_of_wotsOuterFold43
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node wotsPtr lsig
    hParse hLayer1 hDigestLt hAdrsLt e.hSeed e.hD e.hAdrs e.hWPtr hCdLoad

/-- Fully record-driven layer-0 chain-cells closure: the `hCdLoad` residual is
discharged from the compact entry-state calldata fact `hCdSt` via
`wotsOuterFold_cdload_raw`, the WOTS pointer pinned to `sigDataOffset + 1952`. -/
theorem c13Layer0_copyFold43_wotsChainsEnd_cells_of_inputs
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx) (sigDataOffset + 1952))
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) :
    ∀ j, (hj : j < 43) →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43).world.memory
          (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0 treeIdx leafIdx node
          lsig.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega) :=
  c13Layer0_copyFold43_wotsChainsEnd_cells_of_entry
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node
    (sigDataOffset + 1952) lsig hParse hLayer0 hDigestLt hAdrsLt e
    (fun j hj s hWPtrS hIS hWorldS =>
      wotsOuterFold_cdload_raw pkSeed pkRoot message sig st 1952
        (by norm_num [sigDataOffset]) hCdSt j hj s hWPtrS hIS hWorldS)

/-- Fully record-driven layer-1 chain-cells closure (WOTS pointer pinned to the
layer-1 value `sigDataOffset + (1952 + 868)`). -/
theorem c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node : Nat)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 treeIdx leafIdx lsig.wots.count node)
      (C13Concrete.adrsWotsHashBase 1 treeIdx leafIdx) (sigDataOffset + (1952 + 868)))
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) :
    ∀ j, (hj : j < 43) →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43).world.memory
          (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 1 treeIdx leafIdx node
          lsig.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega) :=
  c13Layer1_copyFold43_wotsChainsEnd_cells_of_entry
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node
    (sigDataOffset + (1952 + 868)) lsig hParse hLayer1 hDigestLt hAdrsLt e
    (fun j hj s hWPtrS hIS hWorldS =>
      wotsOuterFold_cdload_raw pkSeed pkRoot message sig st (1952 + 868)
        (by norm_num [sigDataOffset]) hCdSt j hj s hWPtrS hIS hWorldS)

/-- Fully record-driven reverted-at-layer-1 layer-0 chain-cells closure.  The
path-specific input is the `FoldHypertreeC13RevertedLayer1Data` record `d`
(supplying the layer-0 XMSS signature and parse fact); the executable loop
inputs reduce to the entry record `e` plus the calldata fact `hCdSt`, with the
WOTS pointer pinned to `sigDataOffset + 1952`. -/
theorem c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (st : RuntimeState) (treeIdx leafIdx node : Nat)
    (pk : PublicKey) (digest : HMsg) (forsPk : Bytes)
    (d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx d.lsig0.wots.count node < 2 ^ 256)
    (hAdrsLt : C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx < 2 ^ 256)
    (e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 treeIdx leafIdx d.lsig0.wots.count node)
      (C13Concrete.adrsWotsHashBase 0 treeIdx leafIdx) (sigDataOffset + 1952))
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) :
    ∀ j, (hj : j < 43) →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43) 0 43).world.memory
          (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0 treeIdx leafIdx node
          d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega) :=
  c13Layer0_copyFold43_wotsChainsEnd_cells_of_inputs
    pkSeed pkRoot message sig sigParsed st treeIdx leafIdx node
    d.lsig0 hParse d.hLayer0 hDigestLt hAdrsLt e hCdSt

#print axioms c13Layer0_copyFold43_wotsChainsEnd_cells_of_entry
#print axioms c13Layer1_copyFold43_wotsChainsEnd_cells_of_entry
#print axioms c13Layer0_copyFold43_wotsChainsEnd_cells_of_inputs
#print axioms c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs
#print axioms c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs
#print axioms c13Layer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
#print axioms c13Layer1_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
#print axioms c13RevertedLayer0_copyFold43_wotsPk_keccak_eq_of_wotsOuterFold43
#print axioms c13RevertedLayer0_copyFold43_wotsPk_keccak_of_inputs
#print axioms c13Layer0_copyFold43_wotsPk_keccak_of_entry
#print axioms c13Layer1_copyFold43_wotsPk_keccak_of_entry
#print axioms c13Layer0_copyFold43_wotsPk_keccak_of_inputs
#print axioms c13Layer1_copyFold43_wotsPk_keccak_of_inputs

end SphincsMinusVerifiers
