/-
  BindingFrame — keccak-free *bindings-frame* lemmas for the Phase-3b data
  correspondence.

  The accept-path step transformers (`s2Step`, `forsLeafStep`, `forsFinalizeStep`,
  `stepLayer`) are defined as `match execStmtList [] st body with | .continue s' …`.
  Several Phase-3b correspondences need to know that a binding the body never
  *writes* (e.g. `"root"`, set once in S2 and read at the final compare) is carried
  through untouched.  Reducing `execStmtList` to read the binding would force the
  body's keccak values (STRATEGY §5 risk #1).  This file avoids that entirely:
  every lemma `cases`-es on the *abstract* `evalExpr [] st e` result, so the bound
  value is introduced as an opaque variable and never evaluated.

  The per-statement lemmas (`letVar`/`assignVar` with a differing key, `mstore`)
  plus the list-level induction (`execStmtList_preserves_lookup`) give a frame
  result for any straight-line body.  The `forEach` case composes with
  `ClimbLoop.foldLoop_preserves_lookup` once a body's loop step is known to
  preserve the key.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
-- `Compiler.Proofs.Frames` is intentionally not imported: all preserves_*
-- lemmas below are proved locally and stay independent of upstream PR #1983
-- even after its merge.  Re-import only if a specific lemma name needs to
-- be shared with another workspace.

namespace SphincsMinusVerifiers.BindingFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! ## 1. Per-statement frame lemmas (keccak-free). -/

/-- A `letVar name e` that continues preserves the lookup of any `key ≠ name`,
without evaluating `e`'s value (the `evalExpr` result is cased abstractly). -/
theorem execStmt_letVar_preserves_lookup
    (st s' : RuntimeState) (name key : String) (e : Expr) (hne : name ≠ key)
    (h : execStmt [] st (.letVar name e) = .continue s') :
    lookupValue s'.bindings key = lookupValue st.bindings key := by
  rw [show execStmt [] st (.letVar name e)
        = (match evalExpr [] st e with
           | some resolved => .continue { st with bindings := bindValue st.bindings name resolved }
           | none => .revert) from rfl] at h
  cases hev : evalExpr [] st e with
  | none => rw [hev] at h; exact absurd h (by simp)
  | some r =>
      rw [hev] at h
      injection h with hh
      subst hh
      exact MemoryKit.lookupValue_bindValue_ne st.bindings name key r hne

/-- An `assignVar name e` that continues preserves the lookup of any `key ≠ name`,
without evaluating `e`'s value. -/
theorem execStmt_assignVar_preserves_lookup
    (st s' : RuntimeState) (name key : String) (e : Expr) (hne : name ≠ key)
    (h : execStmt [] st (.assignVar name e) = .continue s') :
    lookupValue s'.bindings key = lookupValue st.bindings key := by
  rw [show execStmt [] st (.assignVar name e)
        = (match evalExpr [] st e with
           | some resolved => .continue { st with bindings := bindValue st.bindings name resolved }
           | none => .revert) from rfl] at h
  cases hev : evalExpr [] st e with
  | none => rw [hev] at h; exact absurd h (by simp)
  | some r =>
      rw [hev] at h
      injection h with hh
      subst hh
      exact MemoryKit.lookupValue_bindValue_ne st.bindings name key r hne

/-- An `mstore off val` that continues preserves the lookup of *every* key: it
only updates `world.memory`, never `bindings`.  Both `evalExpr`s are cased
abstractly. -/
theorem execStmt_mstore_preserves_lookup
    (st s' : RuntimeState) (key : String) (off val : Expr)
    (h : execStmt [] st (.mstore off val) = .continue s') :
    lookupValue s'.bindings key = lookupValue st.bindings key := by
  rw [show execStmt [] st (.mstore off val)
        = (match evalExpr [] st off, evalExpr [] st val with
           | some ro, some rv =>
               .continue { st with world := { st.world with
                   memory := fun o => if o = ro then rv else st.world.memory o } }
           | _, _ => .revert) from rfl] at h
  cases hoff : evalExpr [] st off with
  | none => rw [hoff] at h; exact absurd h (by simp)
  | some ro =>
      cases hval : evalExpr [] st val with
      | none => rw [hoff, hval] at h; exact absurd h (by simp)
      | some rv =>
          rw [hoff, hval] at h
          injection h with hh
          subst hh
          rfl

/-! ## 2. List-level frame by induction over the body. -/

/-- **`execStmtList_preserves_lookup`** — if every statement in `body` preserves
`key` (per the `hpre` hypothesis, which is discharged statement-by-statement using
the §1 lemmas), then running the whole `body` preserves `key`.  Proved by
induction on `body` via the interpreter's own `cons`/`nil` reduction.  Keccak-free
throughout. -/
theorem execStmtList_preserves_lookup (key : String) :
    ∀ (body : List Stmt) (st s' : RuntimeState),
      (∀ (s s'' : RuntimeState) (stmt : Stmt),
          stmt ∈ body → execStmt [] s stmt = .continue s'' →
          lookupValue s''.bindings key = lookupValue s.bindings key) →
      execStmtList [] st body = .continue s' →
      lookupValue s'.bindings key = lookupValue st.bindings key
  | [], st, s', _, h => by
      rw [show execStmtList [] st ([] : List Stmt) = .continue st from rfl] at h
      injection h with hh; subst hh; rfl
  | stmt :: rest, st, s', hpre, h => by
      rw [show execStmtList [] st (stmt :: rest)
            = (match execStmt [] st stmt with
               | .continue next => execStmtList [] next rest
               | .stop next => .stop next
               | .return rv rs => .return rv rs
               | .revert => .revert) from rfl] at h
      cases hs : execStmt [] st stmt with
      | «continue» next =>
          rw [hs] at h
          have hhead : lookupValue next.bindings key = lookupValue st.bindings key :=
            hpre st next stmt (List.mem_cons.mpr (Or.inl rfl)) hs
          have htail : lookupValue s'.bindings key = lookupValue next.bindings key :=
            execStmtList_preserves_lookup key rest next s'
              (fun s s'' stm hmem hexec =>
                hpre s s'' stm (List.mem_cons.mpr (Or.inr hmem)) hexec)
              h
          rw [htail, hhead]
      | stop next => rw [hs] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hs] at h; exact absurd h (by simp)
      | revert => rw [hs] at h; exact absurd h (by simp)

/-! ## 3. The `forEach` frame (loop var ≠ key, body preserves key). -/

/-- A raw `execForEachLoop` whose loop variable differs from `key` and whose body
preserves `key` on every continuing iteration preserves `key` over the whole loop.
Proved by induction on `remaining`; reuses `lookupValue_bindValue_ne` to discharge
the per-iteration loop-variable bind. -/
theorem execForEachLoop_preserves_lookup
    (varName key : String) (runBody : RuntimeState → StmtResult) (hne : varName ≠ key)
    (hbody : ∀ (s s'' : RuntimeState),
        runBody s = .continue s'' → lookupValue s''.bindings key = lookupValue s.bindings key) :
    ∀ (state s' : RuntimeState) (index remaining : Nat),
      execForEachLoop varName runBody state index remaining = .continue s' →
      lookupValue s'.bindings key = lookupValue state.bindings key
  | state, s', _, 0, h => by
      rw [execForEachLoop_zero] at h; injection h with hh; subst hh; rfl
  | state, s', index, remaining + 1, h => by
      rw [show execForEachLoop varName runBody state index (remaining + 1)
            = (match runBody { state with
                  bindings := bindValue state.bindings varName (wordNormalize index) } with
               | .continue next => execForEachLoop varName runBody next (index + 1) remaining
               | .stop next => .stop next
               | .return value next => .return value next
               | .revert => .revert) from rfl] at h
      cases hb : runBody { state with
          bindings := bindValue state.bindings varName (wordNormalize index) } with
      | «continue» next =>
          rw [hb] at h
          have hhead : lookupValue next.bindings key = lookupValue state.bindings key := by
            rw [hbody _ next hb]
            exact MemoryKit.lookupValue_bindValue_ne state.bindings varName key _ hne
          have htail := execForEachLoop_preserves_lookup varName key runBody hne hbody
            next s' (index + 1) remaining h
          rw [htail, hhead]
      | stop next => rw [hb] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hb] at h; exact absurd h (by simp)
      | revert => rw [hb] at h; exact absurd h (by simp)

/-- **`execStmt_forEach_preserves_lookup`** — a `forEach varName count body`
statement preserves `key` when the loop variable differs from `key` and every
statement of `body` preserves `key`.  Composes `execStmtList_preserves_lookup`
(body) with `execForEachLoop_preserves_lookup` (loop), plus one
`lookupValue_bindValue_ne` for the initial loop-variable bind.  Keccak-free:
`count`'s value is cased abstractly. -/
theorem execStmt_forEach_preserves_lookup
    (varName key : String) (count : Expr) (body : List Stmt) (st s' : RuntimeState)
    (hne : varName ≠ key)
    (hbody : ∀ (s s'' : RuntimeState) (stmt : Stmt),
        stmt ∈ body → execStmt [] s stmt = .continue s'' →
        lookupValue s''.bindings key = lookupValue s.bindings key)
    (h : execStmt [] st (.forEach varName count body) = .continue s') :
    lookupValue s'.bindings key = lookupValue st.bindings key := by
  rw [show execStmt [] st (.forEach varName count body)
        = (match evalExpr [] st count with
           | some bound =>
               execForEachLoop varName (fun ls => execStmtList [] ls body)
                 { st with bindings := bindValue st.bindings varName (wordNormalize 0) } 0 bound
           | none => .revert) from rfl] at h
  cases hc : evalExpr [] st count with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some bound =>
      rw [hc] at h
      have hrun : ∀ (s s'' : RuntimeState),
          (fun ls => execStmtList [] ls body) s = .continue s'' →
          lookupValue s''.bindings key = lookupValue s.bindings key :=
        fun s s'' hh => execStmtList_preserves_lookup key body s s'' hbody hh
      rw [execForEachLoop_preserves_lookup varName key (fun ls => execStmtList [] ls body)
        hne hrun { st with bindings := bindValue st.bindings varName (wordNormalize 0) }
        s' 0 bound h]
      exact MemoryKit.lookupValue_bindValue_ne st.bindings varName key _ hne

/-! ## 4. Axiom audit. -/

#print axioms execStmt_letVar_preserves_lookup
#print axioms execStmt_assignVar_preserves_lookup
#print axioms execStmt_mstore_preserves_lookup
#print axioms execStmtList_preserves_lookup
#print axioms execForEachLoop_preserves_lookup
#print axioms execStmt_forEach_preserves_lookup

end SphincsMinusVerifiers.BindingFrame
-- NOTE (2026-06 factoring): See Compiler.Proofs.Frames (from Verity PR #1983)
-- for the generic versions of the preserves_* lemmas above. SPHINCS- supplies
-- the step spec + range supplier on top of the generic engine.
