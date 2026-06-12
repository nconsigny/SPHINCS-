/-
  C13WotsOuterInputs — compact entry-state discharge for the C13 WOTS-outer
  loop inputs.

  The WOTS-PK keccak assembly (`C13WotsPkKeccak`) and the chain-cell closure
  (`C13ChainCells`) both consume five universally-quantified facts about every
  prefix `foldLoop "i" wotsOuterStep st 0 j` (j < 43): the seed cell `0x00`, and
  the bindings `d`, `wotsAdrs`, `wotsPtr`, plus a `calldataload` evaluation.

  The first four are loop *frames*: the WOTS-outer step never rewrites those
  sites, so each prefix value equals the corresponding entry-state value.  This
  module isolates that reasoning as four lightweight lemmas driven by the generic
  `foldLoop_preserves_lookup` / `foldLoop_preserves_memory_val_range` engines, so
  the heavy assembly only needs a compact entry record (`C13WotsOuterEntry`)
  rather than five spelled-out invariants.
-/

import SphincsMinusVerifiers.SegmentLayer3CopyCells

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbLoop (foldLoop)
open SphincsMinusVerifiers.MkC13State (headWords bytesToWords sigDataOffset)

/-- Frame lemma: any binding `key` distinct from the WOTS-outer body's writes
(`digit`/`steps`/`val`/`chainBase`/`step`) and the loop variable `i` keeps its
entry value through every prefix of the WOTS-outer fold. -/
theorem wotsOuterFold_preserves_binding
    (st : RuntimeState) (key : String)
    (hneDigit : "digit" ≠ key) (hneSteps : "steps" ≠ key)
    (hneVal : "val" ≠ key) (hneChainBase : "chainBase" ≠ key)
    (hneStep : "step" ≠ key) (hneI : "i" ≠ key) (j : Nat) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings key =
      lookupValue st.bindings key :=
  ClimbLoop.foldLoop_preserves_lookup "i" key SegmentLayer3CopyCells.wotsOuterStep hneI
    (fun s => SegmentLayer3CopyCells.wotsOuterStep_preserves_lookup_of_ne s key
      hneDigit hneSteps hneVal hneChainBase hneStep)
    st 0 j

/-- Frame lemma: the seed cell `0x00` keeps its entry value through every prefix
`j ≤ 43` of the WOTS-outer fold. -/
theorem wotsOuterFold_preserves_seed_cell
    (st : RuntimeState) (j : Nat) (hj : j ≤ 43) :
    ((foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
      (st.world.memory 0x00).val :=
  ClimbLoop.foldLoop_preserves_memory_val_range "i"
    SegmentLayer3CopyCells.wotsOuterStep 0x00 (fun i => i < 43)
    (fun s idx hidx =>
      SegmentLayer3CopyCells.wotsOuterStep_preserves_memory_zero_of_i
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } idx hidx
        (MemoryKit.lookupValue_bindValue_self s.bindings "i" (wordNormalize idx)))
    st 0 j (fun i _ hi => by omega)

/-- Selector-`0` collapse for any byte-region read (`offset ≥ 4`): the selector
plays no role once the offset is past the 4-byte selector prefix. -/
private theorem calldataloadWord_sel_zero_ge4
    (sel : Nat) (cd : List Nat) (off : Nat) (hoff : 4 ≤ off) :
    Compiler.Proofs.YulGeneration.calldataloadWord sel cd off =
      Compiler.Proofs.YulGeneration.calldataloadWord 0 cd off := by
  unfold Compiler.Proofs.YulGeneration.calldataloadWord
  simp [show off ≠ 0 by omega, show ¬ off < 4 by omega]

/-- Fifth WOTS-outer input lemma (the `calldataload`): any state whose world is
the `j`-prefix world of the WOTS-outer fold reads the frozen signature word at
chain index `j` through `calldataload(wotsPtr + (i << 4))`, provided its bindings
expose `wotsPtr = sigDataOffset + baseOff` and `i = j`.  The entry-state calldata
is frozen through the loop by `wotsOuterStep_preserves_sc`; the offset arithmetic
collapses to `sigDataOffset + (baseOff + 16*j)` and the selector to `0`. -/
theorem wotsOuterFold_cdload_raw
    (pkSeed pkRoot message sig : Bytes) (st : RuntimeState) (baseOff : Nat)
    (hBaseLt : sigDataOffset + baseOff + 16 * 42 < 2 ^ 256)
    (hCdSt : st.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
    (j : Nat) (hj : j < 43) (s : RuntimeState)
    (hWPtr : lookupValue s.bindings "wotsPtr" = sigDataOffset + baseOff)
    (hI : lookupValue s.bindings "i" = j)
    (hWorld : s.world =
      (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world) :
    evalExpr [] s
        (.calldataload
          (.add (.localVar "wotsPtr") (.shl (.literal 4) (.localVar "i")))) =
      some
        (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
          (sigDataOffset + (baseOff + 16 * j))) := by
  have hShiftEq : j <<< 4 = 16 * j := by rw [Nat.shiftLeft_eq]; ring
  have hCd : s.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
    rw [hWorld,
      (StateFrame.foldLoop_preserves_selector_calldata "i"
        SegmentLayer3CopyCells.wotsOuterStep
        SegmentLayer3CopyCells.wotsOuterStep_preserves_sc st 0 j).2, hCdSt]
  have hWotsEval :
      evalExpr [] s (.localVar "wotsPtr") = some (sigDataOffset + baseOff) := by
    show some (lookupValue s.bindings "wotsPtr") = _
    rw [hWPtr]
  have hIEval : evalExpr [] s (.localVar "i") = some j := by
    show some (lookupValue s.bindings "i") = _
    rw [hI]
  have hShift : j <<< 4 < 2 ^ 256 := by rw [hShiftEq]; omega
  have haplt : sigDataOffset + baseOff < 2 ^ 256 := by omega
  have hhlt : j < 2 ^ 256 := by omega
  have hSum : sigDataOffset + baseOff + j <<< 4 < 2 ^ 256 := by rw [hShiftEq]; omega
  have hoffset := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_siblingOffset
    s (.localVar "wotsPtr") (.localVar "i") (sigDataOffset + baseOff) j
    hWotsEval hIEval haplt hhlt hShift hSum
  have hoff : sigDataOffset + baseOff + j <<< 4 =
      sigDataOffset + (baseOff + 16 * j) := by rw [hShiftEq]; ring
  show (evalExpr [] s
        (.add (.localVar "wotsPtr") (.shl (.literal 4) (.localVar "i")))).bind
        (fun ro => some (Compiler.Proofs.YulGeneration.calldataloadWord
          s.selector s.world.calldata ro)) = _
  rw [hoffset]
  show some _ = _
  rw [hCd, hoff,
    calldataloadWord_sel_zero_ge4 s.selector _ _
      (show 4 ≤ sigDataOffset + (baseOff + 16 * j) by
        show 4 ≤ 164 + (baseOff + 16 * j); omega)]

/-- Compact entry-state record for the C13 WOTS-outer loop: the seed cell and the
three loop-invariant bindings at the loop's start state.  These four scalar facts
replace the four universally-quantified prefix invariants consumed downstream. -/
structure C13WotsOuterEntry (pkSeed : Bytes) (st : RuntimeState)
    (digest adrs wotsPtr : Nat) : Prop where
  seed0 : (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed
  d0 : lookupValue st.bindings "d" = digest
  adrs0 : lookupValue st.bindings "wotsAdrs" = adrs
  wptr0 : lookupValue st.bindings "wotsPtr" = wotsPtr

namespace C13WotsOuterEntry

variable {pkSeed : Bytes} {st : RuntimeState} {digest adrs wotsPtr : Nat}

/-- Seed cell invariant at every prefix `j < 43`, from the entry record. -/
theorem hSeed (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (hj : j < 43) :
    ((foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [wotsOuterFold_preserves_seed_cell st j (by omega), e.seed0]

/-- `d` binding invariant at every prefix `j < 43`, from the entry record. -/
theorem hD (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (_hj : j < 43) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings "d" =
      digest := by
  rw [wotsOuterFold_preserves_binding st "d"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j, e.d0]

/-- `wotsAdrs` binding invariant at every prefix `j < 43`, from the entry record. -/
theorem hAdrs (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (_hj : j < 43) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
        "wotsAdrs" = adrs := by
  rw [wotsOuterFold_preserves_binding st "wotsAdrs"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j, e.adrs0]

/-- `wotsPtr` binding invariant at every prefix `j < 43`, from the entry record. -/
theorem hWPtr (e : C13WotsOuterEntry pkSeed st digest adrs wotsPtr)
    (j : Nat) (_hj : j < 43) :
    lookupValue (foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
        "wotsPtr" = wotsPtr := by
  rw [wotsOuterFold_preserves_binding st "wotsPtr"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) j, e.wptr0]

end C13WotsOuterEntry

#print axioms wotsOuterFold_preserves_binding
#print axioms wotsOuterFold_preserves_seed_cell
#print axioms wotsOuterFold_cdload_raw
#print axioms C13WotsOuterEntry.hSeed

end SphincsMinusVerifiers
