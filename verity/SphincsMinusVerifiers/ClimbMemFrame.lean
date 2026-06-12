/-
  ClimbMemFrame — the per-step *memory-frame* for the WOTS chain climb.

  `ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN` reduces a contract
  `and(keccak256(off, 32*k), N_MASK)` to the spec `maskN (keccakWords ws)` *given*
  the covered scratch cells hold `ws` (its hypothesis `hmem`).  This file discharges
  that memory obligation for the WOTS chain body (`ClimbKit.wotsChainBody`), the
  cleanest case: three statements, a keccak over the 3-word window `[0x00, 0x60)`,
  no branchless parity swap.

  The body writes `0x20 := chainBase | (digit+step)` and `0x40 := val`, then
  `val := and(keccak 0x00 0x60, N_MASK)`.  The final statement is an `assignVar`,
  which never touches `world.memory`, so the memory of `stepWots st` (= the state
  *after* the whole body) is exactly the memory the keccak reads:

    cell 0x00 — untouched base word (the materialised `seed`),
    cell 0x20 — the resolved address word,
    cell 0x40 — the prior `val`.

  `stepWots_memory` pins that function; `stepWots_hmem` repackages it in the exact
  `∀ i < 3, (memory (0 + 32*i)).val = ws[i]` shape the keccak bridge consumes.  No
  keccak is evaluated here.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbKit
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.ClimbLoop

namespace SphincsMinusVerifiers.ClimbMemFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (wotsChainBody stepWots N_MASK)
open SphincsMinusVerifiers.ClimbKeccakStep (evalExpr_maskedKeccak_eq_maskN)
open SphincsMinusVerifierSpec.C13Concrete (maskN nMask keccakWords)

set_option maxHeartbeats 1000000

/-- An `assignVar name e` whose expression resolves continues, leaving `world`
(hence `world.memory`) untouched — only `bindings` changes. -/
private theorem assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-! ## 1. The WOTS scratch memory function. -/

/-- **`stepWots_memory`** — the memory of the state after one WOTS chain body is the
base memory with `0x20 ↦ v1` (the address word) and `0x40 ↦ val` written, where
`v1` is the resolved value of the address expression and `val` the current chain
word.  The trailing `assignVar "val"` leaves memory unchanged, so this is exactly
the window the body's `keccak 0x00 0x60` reads. -/
theorem stepWots_memory (st : RuntimeState) (v1 : Nat)
    (h1 : evalExpr [] st (.bitOr (.localVar "chainBase")
            (.add (.localVar "digit") (.localVar "step"))) = some v1) :
    (stepWots st).world.memory
      = MemoryKit.memUpdate
          (MemoryKit.memUpdate st.world.memory 0x20 v1)
          0x40 (lookupValue st.bindings "val") := by
  -- State after the first mstore (0x20 := v1).
  have hoff1 : evalExpr [] st (.literal 0x20) = some 0x20 := rfl
  have hstep1 := MemoryKit.execStmt_mstore_continue st (.literal 0x20)
      (.bitOr (.localVar "chainBase") (.add (.localVar "digit") (.localVar "step")))
      0x20 v1 hoff1 h1
  set st1 : RuntimeState :=
    { st with world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 v1 } }
    with hst1
  -- State after the second mstore (0x40 := val).
  have hoff2 : evalExpr [] st1 (.literal 0x40) = some 0x40 := rfl
  have hval2 : evalExpr [] st1 (.localVar "val") = some (lookupValue st.bindings "val") := rfl
  have hstep2 := MemoryKit.execStmt_mstore_continue st1 (.literal 0x40) (.localVar "val")
      0x40 (lookupValue st.bindings "val") hoff2 hval2
  set st2 : RuntimeState :=
    { st1 with world := { st1.world with
        memory := MemoryKit.memUpdate st1.world.memory 0x40 (lookupValue st.bindings "val") } }
    with hst2
  -- The third statement is an assignVar; resolve its keccak-mask value abstractly.
  have hval3 : evalExpr [] st2
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK))
      = some (Verity.Core.Uint256.and
                (keccakMemorySlice st2.world.memory (wordNormalize 0x00) (wordNormalize 0x60))
                (wordNormalize N_MASK)).val := rfl
  have hstep3 := assignVar_continue st2 "val"
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK)) _ hval3
  -- Thread the three statements through `stepWots`.
  show (match execStmtList [] st
          ([ Stmt.mstore (.literal 0x20)
              (.bitOr (.localVar "chainBase") (.add (.localVar "digit") (.localVar "step")))
           , Stmt.mstore (.literal 0x40) (.localVar "val")
           , .assignVar "val"
              (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK)) ]) with
        | .continue s' => s' | _ => st).world.memory = _
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hstep1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hstep2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hstep3]
  -- `execStmtList [] _ [] = .continue _`; the match selects the final state, whose
  -- `world.memory` is `st2.world.memory` (the assignVar left memory alone).
  show st2.world.memory = _
  rfl

/-! ## 2. The `hmem`-shaped repackaging consumed by the keccak bridge. -/

/-- The three-word keccak preimage of the WOTS chain step, in spec word order.
The address word `v1` and the prior chain word are `wordNormalize`-wrapped because
that is exactly what reading the written scratch cells back yields (`memUpdate`
stores a word, so the read is `wordNormalize`d); cell `0x00` is the untouched base
word already in `.val` form. -/
def wotsScratchWords (st : RuntimeState) (v1 : Nat) : List Nat :=
  [ (st.world.memory 0x00).val, wordNormalize v1, wordNormalize (lookupValue st.bindings "val") ]

/-- **`stepWots_hmem`** — the WOTS scratch memory in the exact
`∀ i < ws.length, (memory (0 + 32*i)).val = ws[i]` shape that
`ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN` (and `KeccakBridge`) consumes,
with `ws = wotsScratchWords st v1` and base offset `0`. -/
theorem stepWots_hmem (st : RuntimeState) (v1 : Nat)
    (h1 : evalExpr [] st (.bitOr (.localVar "chainBase")
            (.add (.localVar "digit") (.localVar "step"))) = some v1) :
    ∀ i, (h : i < (wotsScratchWords st v1).length) →
      ((stepWots st).world.memory (0 + 32 * i)).val = (wotsScratchWords st v1)[i] := by
  intro i hi
  rw [stepWots_memory st v1 h1]
  -- `wotsScratchWords` has length 3, so `i ∈ {0,1,2}`.
  simp only [wotsScratchWords, List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ =>
    -- cell 0x00: untouched by both writes.
    show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
            (lookupValue st.bindings "val") (0 + 32 * 0)).val = _
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    rfl
  | 1, _ =>
    -- cell 0x20: the address word `v1`.
    show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
            (lookupValue st.bindings "val") (0 + 32 * 1)).val = _
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    show (MemoryKit.memUpdate st.world.memory 0x20 v1 0x20).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | 2, _ =>
    -- cell 0x40: the prior chain word `val`.
    show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
            (lookupValue st.bindings "val") (0 + 32 * 2)).val = _
    show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
            (lookupValue st.bindings "val") 0x40).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | (n + 3), hbad => exact absurd hbad (by omega)

/-! ## 3. The per-step masked-keccak value at the WOTS call site. -/

/-- **`wots_maskedKeccak_value`** — specialising the reusable masking combine
`ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN` to the concrete WOTS chain-body
literals (`keccak 0x00 0x60` over the 3-word window, masked by `N_MASK`): at any
state whose scratch memory holds the 3-word preimage `ws`, the interpreter's
`and(keccak256 0x00 0x60, N_MASK)` resolves to exactly `maskN (keccakWords ws)`.
The window size `0x60` is `32 * 3` and `ClimbKit.N_MASK = C13Concrete.nMask`, so
this is the glue lemma instantiated, with `ws`'s memory obligation supplied by
`stepWots_hmem`. -/
theorem wots_maskedKeccak_value (st : RuntimeState) (ws : List Nat)
    (hlen : ws.length = 3)
    (hmem : ∀ i, (h : i < ws.length) → (st.world.memory (0 + 32 * i)).val = ws[i]) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK))
      = some (maskN (keccakWords ws)) := by
  have hsz : 32 * ws.length = 0x60 := by rw [hlen]
  have hoff : wordNormalize (0x00 : Nat) = 0x00 := by
    rw [wordNormalize_eq_mod]; exact Nat.zero_mod _
  have hszlt : 32 * ws.length < 2 ^ 256 := by rw [hsz]; decide
  have key := evalExpr_maskedKeccak_eq_maskN st 0x00 ws hoff hszlt hmem
  rw [hsz] at key
  rw [show (N_MASK : Nat) = nMask from rfl]
  exact key

/-- **`stepWots_keccak_value`** — the fully-composed WOTS per-step value:
evaluating the chain body's masked keccak over the *post-step* memory yields
`maskN (keccakWords (wotsScratchWords st v1))`.  This is `wots_maskedKeccak_value`
fed by `stepWots_hmem` (which discharges the 3-word scratch obligation), i.e. the
memory-frame + masking-glue chain closed end to end for the WOTS body.  Cell
`0x00` holds the materialised seed, `0x20` the resolved address word `v1`, `0x40`
the prior chain word — exactly the `chainHash` keccak preimage. -/
theorem stepWots_keccak_value (st : RuntimeState) (v1 : Nat)
    (h1 : evalExpr [] st (.bitOr (.localVar "chainBase")
            (.add (.localVar "digit") (.localVar "step"))) = some v1) :
    evalExpr [] (stepWots st)
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK))
      = some (maskN (keccakWords (wotsScratchWords st v1))) :=
  wots_maskedKeccak_value (stepWots st) (wotsScratchWords st v1) rfl
    (stepWots_hmem st v1 h1)

/-- **`stepWots_val_eq_maskedKeccak`** — the chain-step *binding* value: after
one WOTS chain body, `lookup "val"` of the post-step state equals exactly
`maskN (keccakWords (wotsScratchWords st v1))`, where `v1` is the resolved
chain-address word and the 3-word preimage is `[seed, wordNormalize v1,
wordNormalize (prior val)]`.  This is the projection of `stepWots_keccak_value`
through the final `assignVar "val"` binding, exposing the chain output as a
binding fact rather than as an `evalExpr` — exactly the form consumed by the
outer `forEach` fold-invariant for the C13 single-step chain shape. -/
theorem stepWots_val_eq_maskedKeccak (st : RuntimeState) (v1 : Nat)
    (h1 : evalExpr [] st (.bitOr (.localVar "chainBase")
            (.add (.localVar "digit") (.localVar "step"))) = some v1) :
    lookupValue (stepWots st).bindings "val" =
      maskN (keccakWords (wotsScratchWords st v1)) := by
  -- Replay the three-step chain body, tracking the final state's bindings.
  have hoff1 : evalExpr [] st (.literal 0x20) = some 0x20 := rfl
  have hstep1 := MemoryKit.execStmt_mstore_continue st (.literal 0x20)
      (.bitOr (.localVar "chainBase") (.add (.localVar "digit") (.localVar "step")))
      0x20 v1 hoff1 h1
  set st1 : RuntimeState :=
    { st with world := { st.world with
        memory := MemoryKit.memUpdate st.world.memory 0x20 v1 } }
    with hst1
  have hoff2 : evalExpr [] st1 (.literal 0x40) = some 0x40 := rfl
  have hval2 : evalExpr [] st1 (.localVar "val")
      = some (lookupValue st.bindings "val") := rfl
  have hstep2 := MemoryKit.execStmt_mstore_continue st1 (.literal 0x40)
      (.localVar "val") 0x40 (lookupValue st.bindings "val") hoff2 hval2
  set st2 : RuntimeState :=
    { st1 with world := { st1.world with
        memory := MemoryKit.memUpdate st1.world.memory 0x40
          (lookupValue st.bindings "val") } }
    with hst2
  -- At st2 the 3-word window holds the spec preimage; reuse stepWots_hmem's match.
  have hmem : ∀ i, (h : i < (wotsScratchWords st v1).length) →
      (st2.world.memory (0 + 32 * i)).val = (wotsScratchWords st v1)[i] := by
    intro i hi
    simp only [wotsScratchWords, List.length_cons, List.length_nil] at hi
    match i, hi with
    | 0, _ =>
      show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
              (lookupValue st.bindings "val") (0 + 32 * 0)).val = _
      rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
          MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
      rfl
    | 1, _ =>
      show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
              (lookupValue st.bindings "val") (0 + 32 * 1)).val = _
      rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
      show (MemoryKit.memUpdate st.world.memory 0x20 v1 0x20).val = _
      rw [MemoryKit.memUpdate_val_same]
      rfl
    | 2, _ =>
      show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
              (lookupValue st.bindings "val") (0 + 32 * 2)).val = _
      show (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 v1) 0x40
              (lookupValue st.bindings "val") 0x40).val = _
      rw [MemoryKit.memUpdate_val_same]
      rfl
    | (n + 3), hbad => exact absurd hbad (by omega)
  -- Now resolve the final assignVar's keccak/mask value to the spec word.
  have hval3 : evalExpr [] st2
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK))
      = some (maskN (keccakWords (wotsScratchWords st v1))) :=
    wots_maskedKeccak_value st2 (wotsScratchWords st v1) rfl hmem
  have hstep3 := assignVar_continue st2 "val"
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK))
      _ hval3
  -- Thread the three statements through `stepWots`, then read off `"val"`.
  show lookupValue
        (match execStmtList [] st
            ([ Stmt.mstore (.literal 0x20)
                (.bitOr (.localVar "chainBase") (.add (.localVar "digit") (.localVar "step")))
             , Stmt.mstore (.literal 0x40) (.localVar "val")
             , .assignVar "val"
                (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x60)) (.literal N_MASK)) ]) with
          | .continue s' => s' | _ => st).bindings "val" = _
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hstep1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hstep2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hstep3]
  -- The match selects the post-assignVar state; its bindings = bindValue st2.bindings "val" V.
  show lookupValue
        (bindValue st2.bindings "val"
          (maskN (keccakWords (wotsScratchWords st v1)))) "val" = _
  exact MemoryKit.lookupValue_bindValue_self _ _ _

/-! ## 4. Spec-side normalization: `chainHash` is a `specFold`.

The WOTS analogue of `ClimbMemFrameMerkle.xmssClimb_eq_specFold`: the spec WOTS
chain `chainHash seed chainBase digit fuel step val` equals a `ClimbLoop.specFold`
over `wotsSpecStep` (one chain hash on the `val` accumulator, loop index carrying
the chain `step`).  Simpler than the Merkle case — the accumulator is just the
`Word`, no tuple/projection.  Pure structural `fuel`-induction; no keccak
semantics, no new axioms.  This lets `foldLoop_invariant`'s `specFold` conclusion
rewrite into `chainHash`, hence into `wotsPkWord`. -/

open SphincsMinusVerifierSpec.C13Concrete (chainHash)

/-- One spec WOTS chain step on the `val` accumulator: hash `[seed, chainBase |||
(digit + step), val]` and mask.  Verbatim image of the `chainHash` loop body. -/
def wotsSpecStep (seed chainBase digit : Nat) : Nat → Nat → Nat
  | step, val => maskN (keccakWords [seed, chainBase ||| (digit + step), val])

theorem chainHash_eq_specFold (seed chainBase digit : Nat) :
    ∀ (fuel step val : Nat),
      chainHash seed chainBase digit fuel step val
        = ClimbLoop.specFold (wotsSpecStep seed chainBase digit) val step fuel
  | 0, step, val => by
      simp only [chainHash, ClimbLoop.specFold_zero]
  | fuel + 1, step, val => by
      simp only [chainHash, ClimbLoop.specFold_succ, wotsSpecStep]
      exact chainHash_eq_specFold seed chainBase digit fuel (step + 1) _

/-- **`stepWots_val_eq_wotsSpecStep`** — the per-step spec-shape lemma.  Under
bindings holding `seed` (at scratch 0x00), `chainBase`, `digit`, `step`, and
`prevVal` (the prior `"val"` binding), with the obvious bounds on each value
and on the ADRS-assembly sum `digit + step` plus the OR-assembled
`chainBase ||| (digit + step)`, one `stepWots` updates the `"val"` binding to
exactly `wotsSpecStep seed chainBase digit step prevVal`.

This is the fold-step shape of `stepWots_val_eq_maskedKeccak`: the bindings
mirror the spec arguments verbatim, so the outer `forEach "step"` invariant
can pin `"val"` to `wotsSpecStep …` after each iteration and conclude (via
`chainHash_eq_specFold`) that the full chain folds to `chainHash`.  C13
analogue of the C13 WOTS chain-step value shape. -/
theorem stepWots_val_eq_wotsSpecStep
    (s : RuntimeState) (seed chainBase digit step prevVal : Nat)
    (hSeed : (s.world.memory 0x00).val = seed)
    (hCB : lookupValue s.bindings "chainBase" = chainBase)
    (hDigit : lookupValue s.bindings "digit" = digit)
    (hStep : lookupValue s.bindings "step" = step)
    (hVal : lookupValue s.bindings "val" = prevVal)
    (hCBlt : chainBase < 2 ^ 256)
    (hDigitLt : digit < 2 ^ 256)
    (hStepLt : step < 2 ^ 256)
    (hSum : digit + step < 2 ^ 256)
    (hAdrs : chainBase ||| (digit + step) < 2 ^ 256)
    (hPrevLt : prevVal < 2 ^ 256) :
    lookupValue (stepWots s).bindings "val" =
      wotsSpecStep seed chainBase digit step prevVal := by
  have hCBeval : evalExpr [] s (.localVar "chainBase") = some chainBase := by
    show some (lookupValue s.bindings "chainBase") = some chainBase
    rw [hCB]
  have hDigitEval : evalExpr [] s (.localVar "digit") = some digit := by
    show some (lookupValue s.bindings "digit") = some digit
    rw [hDigit]
  have hStepEval : evalExpr [] s (.localVar "step") = some step := by
    show some (lookupValue s.bindings "step") = some step
    rw [hStep]
  have hSumEval : evalExpr [] s (.add (.localVar "digit") (.localVar "step"))
      = some (digit + step) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded s _ _
      digit step hDigitEval hStepEval hDigitLt hStepLt hSum
  have h1 : evalExpr [] s
        (.bitOr (.localVar "chainBase") (.add (.localVar "digit") (.localVar "step")))
      = some (chainBase ||| (digit + step)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded s _ _
      chainBase (digit + step) hCBeval hSumEval hCBlt hSum
  have hWnAdrs : wordNormalize (chainBase ||| (digit + step))
      = chainBase ||| (digit + step) := by
    rw [wordNormalize_eq_mod]
    show (chainBase ||| (digit + step)) % Compiler.Constants.evmModulus = _
    rw [show (Compiler.Constants.evmModulus : Nat) = 2 ^ 256 from rfl]
    exact Nat.mod_eq_of_lt hAdrs
  have hWnPrev : wordNormalize prevVal = prevVal := by
    rw [wordNormalize_eq_mod]
    show prevVal % Compiler.Constants.evmModulus = _
    rw [show (Compiler.Constants.evmModulus : Nat) = 2 ^ 256 from rfl]
    exact Nat.mod_eq_of_lt hPrevLt
  rw [stepWots_val_eq_maskedKeccak s _ h1]
  unfold wotsScratchWords wotsSpecStep
  rw [hSeed, hVal, hWnAdrs, hWnPrev]

/-! ## 5. Axiom audit. -/

#print axioms stepWots_memory
#print axioms stepWots_hmem
#print axioms wots_maskedKeccak_value
#print axioms stepWots_keccak_value
#print axioms stepWots_val_eq_maskedKeccak
#print axioms chainHash_eq_specFold
#print axioms stepWots_val_eq_wotsSpecStep

end SphincsMinusVerifiers.ClimbMemFrame
