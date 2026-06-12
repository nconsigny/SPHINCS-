/-
  ClimbLoopGuarded — the *guarded* loop-threading engine.

  `ClimbLoop.execForEachLoop_of_step` threads a `forEach` whose body **always**
  continues (`runBody ls = .continue (step ls)`).  The Layer-3 hypertree-climb
  loop (`forEach "layer" (u 2)`, Model.lean:153-204) is NOT of that shape: its
  body contains the WOTS checksum guard

  ```
  .ite (notE (eqE (v "digitSum") (u 208))) revert0 []
  ```

  so each iteration either continues to `step ls` (checksum 208 holds) or reverts.
  This file lifts such a *guarded* body across `execForEachLoop`: if every
  threaded iteration's guard passes (`allGuardsPass`), the whole loop continues to
  the same pure `foldLoop` over `step` that the total engine produces; the accept
  path is then identical to the unguarded case once the guards are discharged.

  This is pure framework-level reasoning over small terms (no giant body term, no
  `rfl` on `c13VerifyBody`), so it carries no heartbeat risk.  No `sorry`, no new
  `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop

namespace SphincsMinusVerifiers.ClimbLoopGuarded

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbLoop (foldLoop foldLoop_zero foldLoop_succ)

/-! ## 1. The per-iteration guard trace.

`allGuardsPass varName step guard state index remaining` mirrors `foldLoop`'s
recursion exactly: at each iteration it binds `varName` to `wordNormalize index`,
asserts `guard` holds on that loop-state, then recurses on `step ·` and the next
index — so it is precisely "every iteration of the threaded fold passes its
guard".  Vacuously true at `remaining = 0`. -/
def allGuardsPass (varName : String) (step : RuntimeState → RuntimeState)
    (guard : RuntimeState → Bool) :
    RuntimeState → Nat → Nat → Prop
  | _, _, 0 => True
  | state, index, remaining + 1 =>
      guard { state with bindings := bindValue state.bindings varName (wordNormalize index) } = true
      ∧ allGuardsPass varName step guard
          (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
          (index + 1) remaining

/-- The loop-state update performed by the source interpreter before each
`forEach` body execution.  Named here so guard-failure lemmas do not duplicate
large record updates in their statements. -/
def loopState (varName : String) (state : RuntimeState) (index : Nat) : RuntimeState :=
  { state with bindings := bindValue state.bindings varName (wordNormalize index) }

theorem loopState_preserves_memory_val
    (varName : String) (state : RuntimeState) (index addr : Nat) :
    ((loopState varName state index).world.memory addr).val =
      (state.world.memory addr).val := by
  unfold loopState
  rfl

/-- If a relation `R` supplies both the guard fact for the current loop state and
the related post-step accumulator, then every threaded guard in the corresponding
fuel-bounded loop passes.  This is the guarded analogue of
`ClimbLoop.foldLoop_invariant`, but it returns only the control-flow trace needed
by `execStmt_forEach_of_guarded_step`. -/
theorem allGuardsPass_of_rel
    {α : Type} (varName : String) (step : RuntimeState → RuntimeState)
    (guard : RuntimeState → Bool) (specStep : Nat → α → α)
    (R : RuntimeState → α → Prop)
    (hstep : ∀ (s : RuntimeState) (a : α) (idx : Nat),
      R s a →
        guard { s with bindings := bindValue s.bindings varName (wordNormalize idx) } = true ∧
        R (step { s with bindings := bindValue s.bindings varName (wordNormalize idx) })
          (specStep idx a)) :
    ∀ (state : RuntimeState) (a : α) (index remaining : Nat),
      R state a →
      allGuardsPass varName step guard state index remaining := by
  intro state a index remaining hR
  induction remaining generalizing state a index with
  | zero => exact True.intro
  | succ remaining ih =>
      exact ⟨(hstep state a index hR).1,
        ih (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
          (specStep index a) (index + 1) (hstep state a index hR).2⟩

/-! ## 2. The headline guarded loop-threading lemma. -/

/-- **`execForEachLoop_of_guarded_step`** — if the loop body either continues to
`step ·` (when `guard` holds) or reverts, and every threaded iteration's guard
passes (`allGuardsPass`), then `execForEachLoop` continues to the pure `foldLoop`
over `step` — exactly as in the unguarded engine.  Proved by induction on the
iteration count, threading `execForEachLoop_succ_continue` per step. -/
theorem execForEachLoop_of_guarded_step
    (varName : String) (runBody : RuntimeState → StmtResult)
    (step : RuntimeState → RuntimeState) (guard : RuntimeState → Bool)
    (hstep : ∀ ls, runBody ls = if guard ls then .continue (step ls) else .revert) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      allGuardsPass varName step guard state index remaining →
      execForEachLoop varName runBody state index remaining
        = .continue (foldLoop varName step state index remaining)
  | state, index, 0, _ => by
      rw [execForEachLoop_zero, foldLoop_zero]
  | state, index, remaining + 1, hg => by
      obtain ⟨hguard, htail⟩ := hg
      have hbody :
          runBody { state with bindings := bindValue state.bindings varName (wordNormalize index) }
            = .continue
                (step { state with bindings := bindValue state.bindings varName (wordNormalize index) }) := by
        rw [hstep, if_pos hguard]
      refine execForEachLoop_succ_continue hbody ?_
      rw [foldLoop_succ]
      exact execForEachLoop_of_guarded_step varName runBody step guard hstep
        _ (index + 1) remaining htail

/-- **`execForEachLoop_revert_on_first_guard`** — dual control-flow fact for the
first threaded iteration: if the guarded body would see a false guard at the
current loop index, the whole loop reverts immediately. -/
theorem execForEachLoop_revert_on_first_guard
    (varName : String) (runBody : RuntimeState → StmtResult)
    (step : RuntimeState → RuntimeState) (guard : RuntimeState → Bool)
    (hstep : ∀ ls, runBody ls = if guard ls then .continue (step ls) else .revert)
    (state : RuntimeState) (index remaining : Nat)
    (hguard : guard (loopState varName state index) = false) :
    execForEachLoop varName runBody state index (remaining + 1) = .revert := by
  show (match runBody
          { state with bindings := bindValue state.bindings varName (wordNormalize index) } with
        | .continue n => execForEachLoop varName runBody n (index + 1) remaining
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = .revert
  rw [hstep]
  have hguard' :
      guard
        { state with bindings := bindValue state.bindings varName (index % Compiler.Constants.evmModulus) }
        = false := by
    simpa [loopState, wordNormalize] using hguard
  simp [hguard']

/-- **`execForEachLoop_revert_on_second_guard`** — the two-iteration C13 layer
case: if the first guard passes but the next threaded guard fails after one
`step`, the whole loop reverts on the second iteration. -/
theorem execForEachLoop_revert_on_second_guard
    (varName : String) (runBody : RuntimeState → StmtResult)
    (step : RuntimeState → RuntimeState) (guard : RuntimeState → Bool)
    (hstep : ∀ ls, runBody ls = if guard ls then .continue (step ls) else .revert)
    (state : RuntimeState) (index remaining : Nat)
    (hguard0 : guard (loopState varName state index) = true)
    (hguard1 : guard (loopState varName (step (loopState varName state index)) (index + 1))
        = false) :
    execForEachLoop varName runBody state index (remaining + 2) = .revert := by
  show (match runBody
          { state with bindings := bindValue state.bindings varName (wordNormalize index) } with
        | .continue n => execForEachLoop varName runBody n (index + 1) (remaining + 1)
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = .revert
  rw [hstep]
  have hguard0' :
      guard
        { state with bindings := bindValue state.bindings varName (index % Compiler.Constants.evmModulus) }
        = true := by
    simpa [loopState, wordNormalize] using hguard0
  simp [hguard0']
  exact execForEachLoop_revert_on_first_guard varName runBody step guard hstep
    (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
    (index + 1) remaining hguard1

/-! ## 3. The `.forEach`-statement bridge. -/

/-- **`execStmt_forEach_of_guarded_step`** — the statement-level form: a
`.forEach varName count body` whose count evaluates to `bound`, whose body steps
guardedly to `step ·`, and all of whose threaded guards pass, continues to the
pure `foldLoop` over `step`.  Mirrors `ClimbLoop.execStmt_forEach_of_step` with a
guard. -/
theorem execStmt_forEach_of_guarded_step
    (varName : String) (count : Expr) (body : List Stmt)
    (state : RuntimeState) (bound : Nat)
    (step : RuntimeState → RuntimeState) (guard : RuntimeState → Bool)
    (hcount : evalExpr [] state count = some bound)
    (hstep : ∀ ls, execStmtList [] ls body = if guard ls then .continue (step ls) else .revert)
    (hguards : allGuardsPass varName step guard
        { state with bindings := bindValue state.bindings varName (wordNormalize 0) } 0 bound) :
    execStmt [] state (.forEach varName count body)
      = .continue
          (foldLoop varName step
            { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            0 bound) := by
  show (match evalExpr [] state count with
        | some bound =>
            execForEachLoop varName
              (fun loopState => execStmtList [] loopState body)
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
              0 bound
        | none => .revert) = _
  rw [hcount]
  exact execForEachLoop_of_guarded_step varName _ step guard hstep _ 0 bound hguards

/-- Statement-level first-guard revert bridge for guarded `.forEach` loops. -/
theorem execStmt_forEach_revert_on_first_guard
    (varName : String) (count : Expr) (body : List Stmt)
    (state : RuntimeState) (bound : Nat)
    (step : RuntimeState → RuntimeState) (guard : RuntimeState → Bool)
    (hcount : evalExpr [] state count = some bound)
    (remaining : Nat)
    (hbound : bound = remaining + 1)
    (hstep : ∀ ls, execStmtList [] ls body = if guard ls then .continue (step ls) else .revert)
    (hguard :
      guard (loopState varName
        { state with bindings := bindValue state.bindings varName (wordNormalize 0) } 0) = false) :
    execStmt [] state (.forEach varName count body) = .revert := by
  subst hbound
  show (match evalExpr [] state count with
        | some bound =>
            execForEachLoop varName
              (fun loopState => execStmtList [] loopState body)
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
              0 bound
        | none => .revert) = .revert
  rw [hcount]
  exact execForEachLoop_revert_on_first_guard varName _ step guard hstep
    { state with bindings := bindValue state.bindings varName (wordNormalize 0) } 0 remaining
    hguard

/-- Statement-level second-guard revert bridge for guarded `.forEach` loops. -/
theorem execStmt_forEach_revert_on_second_guard
    (varName : String) (count : Expr) (body : List Stmt)
    (state : RuntimeState) (bound : Nat)
    (step : RuntimeState → RuntimeState) (guard : RuntimeState → Bool)
    (hcount : evalExpr [] state count = some bound)
    (remaining : Nat)
    (hbound : bound = remaining + 2)
    (hstep : ∀ ls, execStmtList [] ls body = if guard ls then .continue (step ls) else .revert)
    (hguard0 :
      guard (loopState varName
        { state with bindings := bindValue state.bindings varName (wordNormalize 0) } 0) = true)
    (hguard1 :
      guard
        (loopState varName
          (step (loopState varName
            { state with bindings := bindValue state.bindings varName (wordNormalize 0) } 0))
          1) = false) :
    execStmt [] state (.forEach varName count body) = .revert := by
  subst hbound
  show (match evalExpr [] state count with
        | some bound =>
            execForEachLoop varName
              (fun loopState => execStmtList [] loopState body)
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
              0 bound
        | none => .revert) = .revert
  rw [hcount]
  exact execForEachLoop_revert_on_second_guard varName _ step guard hstep
    { state with bindings := bindValue state.bindings varName (wordNormalize 0) } 0 remaining
    hguard0 hguard1

/-! ## 4. Axiom audit. -/

#print axioms execForEachLoop_of_guarded_step
#print axioms execStmt_forEach_of_guarded_step
#print axioms execForEachLoop_revert_on_first_guard
#print axioms execForEachLoop_revert_on_second_guard
#print axioms execStmt_forEach_revert_on_first_guard
#print axioms execStmt_forEach_revert_on_second_guard
#print axioms allGuardsPass_of_rel
#print axioms loopState_preserves_memory_val

end SphincsMinusVerifiers.ClimbLoopGuarded
