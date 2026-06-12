/-
  ClimbLoop — Layer-2 *loop-threading* engine for the `forEach` climbs of
  `c13VerifyBody`.

  ClimbKit proves the per-iteration shape lemmas: running one Merkle-climb body
  (resp. one WOTS-chain body) over the real Verity source interpreter equals one
  application of a pure state transformer (`stepMerkle` / `stepWots`):

  ```
  execStmtList [] st (merkleClimbBody …) = .continue (stepMerkle … st)
  execStmtList [] st  wotsChainBody       = .continue (stepWots st)
  ```

  This file lifts *any* such total-`.continue` body across the interpreter's
  `execForEachLoop` recursion (`SourceSemantics.lean:581`).  The headline
  `execForEachLoop_of_step` says: if the body always continues to `step ·`, the
  whole `forEach` continues to the `n`-fold fold `foldLoop`, which threads the
  loop-variable bind (`bindValue … varName (wordNormalize index)`) and `step`
  through each iteration — exactly mirroring `execForEachLoop`'s own recursion.

  The two corollaries specialise it to the C13 call sites, discharging the
  Layer-3 hypertree-climb / Layer-1 Merkle-climb loops in one stroke each.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbKit

namespace SphincsMinusVerifiers.ClimbLoop

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! ## 1. The pure fold mirroring `execForEachLoop`.

`foldLoop varName step state index remaining` applies, per iteration: bind the
loop variable `varName` to `wordNormalize index` (as the interpreter does in
`execForEachLoop`'s `loopState`), then `step`, then recurse on `index+1` and one
fewer `remaining`.  It is the pure-function image of the loop when the body is a
total `.continue (step ·)`. -/
def foldLoop (varName : String) (step : RuntimeState → RuntimeState) :
    RuntimeState → Nat → Nat → RuntimeState
  | state, _, 0 => state
  | state, index, remaining + 1 =>
      foldLoop varName step
        (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
        (index + 1) remaining

@[simp] theorem foldLoop_zero
    (varName : String) (step : RuntimeState → RuntimeState)
    (state : RuntimeState) (index : Nat) :
    foldLoop varName step state index 0 = state := rfl

theorem foldLoop_succ
    (varName : String) (step : RuntimeState → RuntimeState)
    (state : RuntimeState) (index remaining : Nat) :
    foldLoop varName step state index (remaining + 1) =
      foldLoop varName step
        (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
        (index + 1) remaining := rfl

/-- Splits a pure loop fold after `left` iterations. -/
theorem foldLoop_append
    (varName : String) (step : RuntimeState → RuntimeState)
    (state : RuntimeState) (index left right : Nat) :
    foldLoop varName step state index (left + right)
      = foldLoop varName step
          (foldLoop varName step state index left) (index + left) right := by
  induction left generalizing state index with
  | zero =>
      simp [foldLoop_zero]
  | succ left ih =>
      rw [show left + 1 + right = left + right + 1 by omega]
      rw [foldLoop_succ, foldLoop_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih
          (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
          (index + 1)

/-- **`foldLoop_preserves_lookup`** — the Phase-3b *frame* engine.  If `step`
preserves a given binding `key` and the loop variable `varName` differs from
`key`, then the whole `foldLoop` carries that binding's value through every
iteration untouched.  Crucially this never evaluates any bound *value* (e.g. a
keccak result): it reasons only about which keys are written, so it composes
loops over keccak-laden step transformers without forcing them.  Proved by
induction on `remaining`. -/
theorem foldLoop_preserves_lookup
    (varName key : String) (step : RuntimeState → RuntimeState)
    (hne : varName ≠ key)
    (hstep : ∀ s, lookupValue (step s).bindings key = lookupValue s.bindings key) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      lookupValue (foldLoop varName step state index remaining).bindings key
        = lookupValue state.bindings key
  | state, _, 0 => by rw [foldLoop_zero]
  | state, index, remaining + 1 => by
      rw [foldLoop_succ,
        foldLoop_preserves_lookup varName key step hne hstep _ (index + 1) remaining,
        hstep,
        MemoryKit.lookupValue_bindValue_ne state.bindings varName key (wordNormalize index) hne]

/-- Memory-frame analogue of `foldLoop_preserves_lookup`: if one loop body step
preserves the word value stored at `addr`, then the whole pure `foldLoop` carries
that memory-cell value through every iteration.  The loop-variable bind touches
only bindings, so no name side condition is needed. -/
theorem foldLoop_preserves_memory_val
    (varName : String) (step : RuntimeState → RuntimeState) (addr : Nat)
    (hstep : ∀ s, ((step s).world.memory addr).val = (s.world.memory addr).val) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      ((foldLoop varName step state index remaining).world.memory addr).val
        = (state.world.memory addr).val
  | state, _, 0 => by rw [foldLoop_zero]
  | state, index, remaining + 1 => by
      rw [foldLoop_succ,
        foldLoop_preserves_memory_val varName step addr hstep _ (index + 1) remaining,
        hstep]

/-- Bounded-index memory-frame analogue.  The per-step hypothesis sees the
concrete loop index used for the bind, so callers can prove preservation only
for the actual loop range instead of all possible pre-bound loop-variable values. -/
theorem foldLoop_preserves_memory_val_bound
    (varName : String) (step : RuntimeState → RuntimeState) (addr : Nat)
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((step { s with bindings := bindValue s.bindings varName (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      ((foldLoop varName step state index remaining).world.memory addr).val
        = (state.world.memory addr).val
  | state, _, 0 => by rw [foldLoop_zero]
  | state, index, remaining + 1 => by
      rw [foldLoop_succ,
        foldLoop_preserves_memory_val_bound varName step addr hstep _ (index + 1) remaining,
        hstep]

/-- Range-gated memory-frame fold.  This is the memory analogue of
`foldLoop_invariant_cond`: the per-step preservation proof can depend on a
predicate over the concrete loop index, and callers supply that predicate only
for the executed range `[index, index + remaining)`. -/
theorem foldLoop_preserves_memory_val_range
    (varName : String) (step : RuntimeState → RuntimeState) (addr : Nat)
    (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((step { s with bindings := bindValue s.bindings varName (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → D i) →
      ((foldLoop varName step state index remaining).world.memory addr).val
        = (state.world.memory addr).val
  | state, _, 0, _ => by rw [foldLoop_zero]
  | state, index, remaining + 1, hD => by
      rw [foldLoop_succ,
        foldLoop_preserves_memory_val_range varName step addr D hstep
          _ (index + 1) remaining
        (fun i hi1 hi2 => hD i (by omega) (by omega)),
        hstep _ index (hD index (by omega) (by omega))]

/-- If a loop iteration `target` writes a memory cell and every later iteration
preserves that cell, then the final `foldLoop` cell value equals the post-step
value produced at `target`.  This is the write-once/suffix-carry form used for
the six FORS root-array cells: earlier iterations may do anything to the cell;
the target iteration overwrites it, and the suffix must be non-aliasing. -/
theorem foldLoop_memory_val_eq_step_at_of_suffix_preserves
    (varName : String) (step : RuntimeState → RuntimeState) (addr : Nat) :
    ∀ (state : RuntimeState) (index remaining target : Nat),
      target < remaining →
      (∀ (s : RuntimeState) (idx : Nat), index + target < idx →
        idx < index + remaining →
        ((step { s with bindings := bindValue s.bindings varName (wordNormalize idx) }).world.memory addr).val
          = (s.world.memory addr).val) →
      ((foldLoop varName step state index remaining).world.memory addr).val =
        ((step { (foldLoop varName step state index target) with
            bindings := bindValue (foldLoop varName step state index target).bindings
              varName (wordNormalize (index + target)) }).world.memory addr).val
  | _, _, 0, target, htarget, _ => by
      exact False.elim (Nat.not_lt_zero target htarget)
  | state, index, remaining + 1, 0, _, hPres => by
      rw [foldLoop_succ]
      rw [foldLoop_preserves_memory_val_range varName step addr
        (fun idx => index < idx ∧ idx < index + (remaining + 1))
        (fun s idx hidx => hPres s idx hidx.1 hidx.2)
        (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
        (index + 1) remaining
        (fun i hi1 hi2 => by
          constructor <;> omega)]
      simp [foldLoop_zero]
  | state, index, remaining + 1, target + 1, htarget, hPres => by
      rw [foldLoop_succ]
      have htarget' : target < remaining := by omega
      have hrec :=
        foldLoop_memory_val_eq_step_at_of_suffix_preserves varName step addr
          (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
          (index + 1) remaining target htarget'
          (fun s idx hgt hlt => hPres s idx (by omega) (by omega))
      simpa [foldLoop_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-! ## 1b. The relational climb-induction engine.

`foldLoop_preserves_lookup` is a *frame* (a binding is unchanged).  The headline
Phase-3b obligation is instead a *correspondence*: the interpreter's per-iteration
`step` tracks a spec accumulator (e.g. `xmssClimb`/`forsClimb`/`chainHash`'s
`(h, mIdx, node)` tuple).  `specFold` is the pure spec-side image of `foldLoop`
over a spec step `specStep : Nat → α → α` (the index argument carries the loop
counter the spec address words depend on), and `foldLoop_invariant` folds a
relation `R : RuntimeState → α → Prop` through both in lockstep.  This reduces the
entire loop correspondence to a single per-iteration preservation hypothesis
`hstep`; discharging `hstep` for the concrete Merkle/WOTS/FORS relation (using the
`ClimbMemFrame*` per-step value lemmas) is the residual open work.  The engine
itself is a clean `Nat`-induction — no keccak semantics, no new axioms. -/

def specFold {α : Type} (specStep : Nat → α → α) : α → Nat → Nat → α
  | a, _, 0 => a
  | a, index, remaining + 1 => specFold specStep (specStep index a) (index + 1) remaining

@[simp] theorem specFold_zero {α : Type} (specStep : Nat → α → α) (a : α) (index : Nat) :
    specFold specStep a index 0 = a := rfl

theorem specFold_succ {α : Type} (specStep : Nat → α → α)
    (a : α) (index remaining : Nat) :
    specFold specStep a index (remaining + 1) =
      specFold specStep (specStep index a) (index + 1) remaining := rfl

/-- **`foldLoop_invariant`** — the relational climb-induction engine.  Given a
per-iteration preservation hypothesis `hstep` (the interpreter's one `step`,
applied after the loop-variable bind, advances `R` together with the spec step
`specStep idx`), the whole `foldLoop` advances `R` together with `specFold`.
Proved by induction on `remaining`; the only obligation pushed onto callers is the
single-step `hstep`. -/
theorem foldLoop_invariant
    {α : Type} (varName : String) (step : RuntimeState → RuntimeState)
    (specStep : Nat → α → α) (R : RuntimeState → α → Prop)
    (hstep : ∀ (s : RuntimeState) (a : α) (idx : Nat), R s a →
      R (step { s with bindings := bindValue s.bindings varName (wordNormalize idx) })
        (specStep idx a)) :
    ∀ (state : RuntimeState) (a : α) (index remaining : Nat), R state a →
      R (foldLoop varName step state index remaining) (specFold specStep a index remaining)
  | state, a, _, 0, hR => by rw [foldLoop_zero, specFold_zero]; exact hR
  | state, a, index, remaining + 1, hR => by
      rw [foldLoop_succ, specFold_succ]
      exact foldLoop_invariant varName step specStep R hstep
        _ _ (index + 1) remaining (hstep state a index hR)

/-- **`foldLoop_invariant_cond`** — the *conditional* climb-induction engine.  Same
as `foldLoop_invariant`, but the per-iteration preservation `hstep` is allowed to
depend on an index-indexed data predicate `D : Nat → Prop`, and the conclusion is
gated on `D` holding across the whole climb range `[index, index + remaining)`.  This
is the honest shape for the Merkle/WOTS/FORS climb: the per-step advance
(`ClimbMemFrameMerkle.MerkleClimbRel_step`) needs a per-iteration data bundle
(`StepDataObligations`, bottoming out at the masked calldata word at `authPtr+16·i`
equalling `wordOfHash16 auth[i]` — blocker #20), and that obligation is *naturally
indexed by climb height*.  With this engine the entire climb threads `R` together
with `specFold` conditional on exactly a *range* of those per-iteration data facts —
collapsing blocker #20 for the whole loop into the single range hypothesis
`∀ i, index ≤ i → i < index + remaining → D i`.  Pure `Nat`-induction; no keccak
semantics, no new axioms.  When `D := fun _ => True` this specialises back to
`foldLoop_invariant`. -/
theorem foldLoop_invariant_cond
    {α : Type} (varName : String) (step : RuntimeState → RuntimeState)
    (specStep : Nat → α → α) (R : RuntimeState → α → Prop) (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (a : α) (idx : Nat), D idx → R s a →
      R (step { s with bindings := bindValue s.bindings varName (wordNormalize idx) })
        (specStep idx a)) :
    ∀ (state : RuntimeState) (a : α) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → D i) →
      R state a →
      R (foldLoop varName step state index remaining) (specFold specStep a index remaining)
  | state, a, _, 0, _, hR => by rw [foldLoop_zero, specFold_zero]; exact hR
  | state, a, index, remaining + 1, hD, hR => by
      rw [foldLoop_succ, specFold_succ]
      exact foldLoop_invariant_cond varName step specStep R D hstep
        _ _ (index + 1) remaining
        (fun i hi1 hi2 => hD i (by omega) (by omega))
        (hstep state a index (hD index (by omega) (by omega)) hR)

/-! ## 2. The headline loop-threading lemma. -/

/-- **`execForEachLoop_of_step`** — if the loop body unconditionally continues to
`step ·`, then `execForEachLoop` continues to the pure `foldLoop`.  Proved by
induction on the iteration count `remaining`, threading the framework's
`execForEachLoop_succ_continue` per-step combinator.  No hypotheses on `state`. -/
theorem execForEachLoop_of_step
    (varName : String) (runBody : RuntimeState → StmtResult)
    (step : RuntimeState → RuntimeState)
    (hstep : ∀ ls, runBody ls = .continue (step ls)) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      execForEachLoop varName runBody state index remaining
        = .continue (foldLoop varName step state index remaining)
  | state, index, 0 => by
      rw [execForEachLoop_zero, foldLoop_zero]
  | state, index, remaining + 1 => by
      refine execForEachLoop_succ_continue (hstep _) ?_
      rw [foldLoop_succ]
      exact execForEachLoop_of_step varName runBody step hstep _ (index + 1) remaining

/-! ## 3. The `.forEach`-statement bridge.

`execForEachLoop_of_step` works on the raw loop combinator.  This lifts it to the
actual `.forEach` *statement* as `execStmt` runs it: evaluate the count to a
`bound`, bind the loop variable to `0`, then run the loop.  This is the glue that
discharges any `.forEach` whose body is a total `.continue (step ·)` directly to
the pure `foldLoop`. -/

/-- **`execStmt_forEach_of_step`** — a `.forEach varName count body` statement
whose count evaluates to `bound` and whose body always continues to `step ·`
continues to the `foldLoop` over `step`, starting from the loop-variable bind at
index `0`.  Mirrors the `.forEach` arm of `execStmt` exactly. -/
theorem execStmt_forEach_of_step
    (varName : String) (count : Expr) (body : List Stmt)
    (state : RuntimeState) (bound : Nat)
    (step : RuntimeState → RuntimeState)
    (hcount : evalExpr [] state count = some bound)
    (hstep : ∀ ls, execStmtList [] ls body = .continue (step ls)) :
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
  exact execForEachLoop_of_step varName _ step hstep _ 0 bound

/-! ## 4. C13 call-site corollaries.

The interpreter's `.forEach` case runs the body as
`fun loopState => execStmtList fields loopState body`, with `fields = []` for the
C13 verifier.  Each corollary instantiates `execForEachLoop_of_step` with the
matching ClimbKit shape lemma, so the whole climb loop folds to repeated
`stepMerkle` / `stepWots`. -/

/-- The Merkle-climb `forEach` (FORS `h<19` and XMSS `h<11`, both via the
parametric `ClimbKit.merkleClimbBody`) folds to repeated `ClimbKit.stepMerkle`. -/
theorem execForEachLoop_merkleClimb
    (varName nodeVar idxVar adrsBaseVar authPtrVar : String)
    (state : RuntimeState) (index remaining : Nat) :
    execForEachLoop varName
        (fun ls => execStmtList [] ls
          (ClimbKit.merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar))
        state index remaining
      = .continue
          (foldLoop varName
            (ClimbKit.stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
            state index remaining) :=
  execForEachLoop_of_step varName _
    (ClimbKit.stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
    (ClimbKit.merkleClimbStep nodeVar idxVar adrsBaseVar authPtrVar)
    state index remaining

/-- The FIPS C13 FORS climb `forEach` (body `ClimbKit.forsClimbBody`, the
address-parametric `merkleClimbBodyA` at `forsAdrs`) folds to repeated
`ClimbKit.stepForsMerkle`. -/
theorem execForEachLoop_forsClimb
    (varName : String) (state : RuntimeState) (index remaining : Nat) :
    execForEachLoop varName
        (fun ls => execStmtList [] ls ClimbKit.forsClimbBody)
        state index remaining
      = .continue
          (foldLoop varName ClimbKit.stepForsMerkle state index remaining) :=
  execForEachLoop_of_step varName _ ClimbKit.stepForsMerkle
    ClimbKit.forsClimbStep state index remaining

/-- A literal-count FIPS FORS climb `.forEach varName (.literal n) forsClimbBody`
statement reduces to `foldLoop … stepForsMerkle … (wordNormalize n)`. -/
theorem execStmt_forEach_forsClimb
    (varName : String) (n : Nat) (state : RuntimeState) :
    execStmt [] state
        (.forEach varName (.literal n) ClimbKit.forsClimbBody)
      = .continue
          (foldLoop varName ClimbKit.stepForsMerkle
            { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            0 (wordNormalize n)) :=
  execStmt_forEach_of_step varName (.literal n) _ state (wordNormalize n)
    ClimbKit.stepForsMerkle rfl ClimbKit.forsClimbStep

/-- The WOTS-chain `forEach` folds to repeated `ClimbKit.stepWots`. -/
theorem execForEachLoop_wotsChain
    (varName : String) (state : RuntimeState) (index remaining : Nat) :
    execForEachLoop varName
        (fun ls => execStmtList [] ls ClimbKit.wotsChainBody)
        state index remaining
      = .continue (foldLoop varName ClimbKit.stepWots state index remaining) :=
  execForEachLoop_of_step varName _ ClimbKit.stepWots ClimbKit.wotsChainStep
    state index remaining

/-! ## 5. Statement-level Merkle-climb corollary.

The most directly reusable form: a whole Merkle-climb `.forEach` *statement* (the
FORS `forEach "h" (u 19)` and the XMSS `forEach "h" (u 11)`, both literal counts)
reduces to the pure `foldLoop` over `ClimbKit.stepMerkle`.  This is what the S4
FORS double-loop and the Layer-3 hypertree-climb invariants consume to dispatch
their inner climbs. -/

/-- A literal-count Merkle-climb `.forEach varName (.literal n) (merkleClimbBody …)`
statement reduces to `foldLoop … (wordNormalize n)`. -/
theorem execStmt_forEach_merkleClimb
    (varName nodeVar idxVar adrsBaseVar authPtrVar : String)
    (n : Nat) (state : RuntimeState) :
    execStmt [] state
        (.forEach varName (.literal n)
          (ClimbKit.merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar))
      = .continue
          (foldLoop varName
            (ClimbKit.stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
            { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            0 (wordNormalize n)) :=
  execStmt_forEach_of_step varName (.literal n) _ state (wordNormalize n)
    (ClimbKit.stepMerkle nodeVar idxVar adrsBaseVar authPtrVar) rfl
    (ClimbKit.merkleClimbStep nodeVar idxVar adrsBaseVar authPtrVar)

/-! ## 6. Axiom audit. -/

#print axioms foldLoop_invariant
#print axioms foldLoop_append
#print axioms foldLoop_preserves_memory_val
#print axioms foldLoop_preserves_memory_val_bound
#print axioms foldLoop_preserves_memory_val_range
#print axioms foldLoop_memory_val_eq_step_at_of_suffix_preserves
#print axioms foldLoop_invariant_cond
#print axioms execForEachLoop_of_step
#print axioms execStmt_forEach_of_step
#print axioms execForEachLoop_merkleClimb
#print axioms execForEachLoop_wotsChain
#print axioms execStmt_forEach_merkleClimb

end SphincsMinusVerifiers.ClimbLoop
