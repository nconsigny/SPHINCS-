/-
  MemoryFrame — keccak-free memory-cell frame lemmas for accept-path segments.

  This mirrors `BindingFrame`, but for a fixed memory cell.  The lemmas avoid
  evaluating expression values: `letVar`/`assignVar` preserve all memory cells,
  while `mstore` preserves a cell when the resolved store offset is known not to
  alias it.  This keeps segment proofs from reconstructing large evaluator
  traces just to show a scratch slot is unchanged.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.MemoryKit

namespace SphincsMinusVerifiers.MemoryFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! ## 1. Per-statement memory frame lemmas. -/

/-- A `letVar` that continues preserves every memory cell value. -/
theorem execStmt_letVar_preserves_memory_val
    (st s' : RuntimeState) (addr : Nat) (name : String) (e : Expr)
    (h : execStmt [] st (.letVar name e) = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
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
      rfl

/-- An `assignVar` that continues preserves every memory cell value. -/
theorem execStmt_assignVar_preserves_memory_val
    (st s' : RuntimeState) (addr : Nat) (name : String) (e : Expr)
    (h : execStmt [] st (.assignVar name e) = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
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
      rfl

/-- An `mstore` that continues preserves `addr` when the resolved store offset
cannot equal `addr`.  The offset/value expressions are cased abstractly, so the
stored value is never evaluated. -/
theorem execStmt_mstore_preserves_memory_val
    (st s' : RuntimeState) (addr : Nat) (off val : Expr)
    (hne : ∀ ro rv,
      evalExpr [] st off = some ro →
      evalExpr [] st val = some rv →
      addr ≠ ro)
    (h : execStmt [] st (.mstore off val) = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
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
          have hdiff : addr ≠ ro := hne ro rv hoff hval
          simp [hdiff]

/-! ## 2. List-level memory frame by induction over the body. -/

/-- If every statement in `body` preserves `addr` on continuing executions, then
the whole statement list preserves that memory-cell value. -/
theorem execStmtList_preserves_memory_val (addr : Nat) :
    ∀ (body : List Stmt) (st s' : RuntimeState),
      (∀ (s s'' : RuntimeState) (stmt : Stmt),
          stmt ∈ body → execStmt [] s stmt = .continue s'' →
          (s''.world.memory addr).val = (s.world.memory addr).val) →
      execStmtList [] st body = .continue s' →
      (s'.world.memory addr).val = (st.world.memory addr).val
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
          have hhead : (next.world.memory addr).val = (st.world.memory addr).val :=
            hpre st next stmt (List.mem_cons.mpr (Or.inl rfl)) hs
          have htail : (s'.world.memory addr).val = (next.world.memory addr).val :=
            execStmtList_preserves_memory_val addr rest next s'
              (fun s s'' stm hmem hexec =>
                hpre s s'' stm (List.mem_cons.mpr (Or.inr hmem)) hexec)
              h
          rw [htail, hhead]
      | stop next => rw [hs] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hs] at h; exact absurd h (by simp)
      | revert => rw [hs] at h; exact absurd h (by simp)

/-! ## 3. The `forEach` memory frame. -/

/-- A raw `execForEachLoop` whose body preserves `addr` on every continuing
iteration preserves the memory-cell value over the whole loop.  The loop-variable
bind changes only `bindings`, so there is no name side condition. -/
theorem execForEachLoop_preserves_memory_val
    (varName : String) (addr : Nat) (runBody : RuntimeState → StmtResult)
    (hbody : ∀ (s s'' : RuntimeState),
        runBody s = .continue s'' →
        (s''.world.memory addr).val = (s.world.memory addr).val) :
    ∀ (state s' : RuntimeState) (index remaining : Nat),
      execForEachLoop varName runBody state index remaining = .continue s' →
      (s'.world.memory addr).val = (state.world.memory addr).val
  | state, s', _, 0, h => by
      rw [show execForEachLoop varName runBody state _ 0 = .continue state from rfl] at h
      injection h with hh
      subst hh
      rfl
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
          have hhead :
              (next.world.memory addr).val = (state.world.memory addr).val := by
            rw [hbody _ next hb]
          have htail := execForEachLoop_preserves_memory_val varName addr runBody hbody
            next s' (index + 1) remaining h
          rw [htail, hhead]
      | stop next => rw [hb] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hb] at h; exact absurd h (by simp)
      | revert => rw [hb] at h; exact absurd h (by simp)

/-- Bounded-index raw `execForEachLoop` memory frame.  The body-preservation
hypothesis sees the concrete loop index used for the interpreter's loop-variable
bind, so callers can prove preservation only for the executed bind shape. -/
theorem execForEachLoop_preserves_memory_val_bound
    (varName : String) (addr : Nat) (runBody : RuntimeState → StmtResult)
    (hbody : ∀ (s : RuntimeState) (idx : Nat) (s'' : RuntimeState),
        runBody { s with bindings := bindValue s.bindings varName (wordNormalize idx) }
          = .continue s'' →
        (s''.world.memory addr).val = (s.world.memory addr).val) :
    ∀ (state s' : RuntimeState) (index remaining : Nat),
      execForEachLoop varName runBody state index remaining = .continue s' →
      (s'.world.memory addr).val = (state.world.memory addr).val
  | state, s', _, 0, h => by
      rw [show execForEachLoop varName runBody state _ 0 = .continue state from rfl] at h
      injection h with hh
      subst hh
      rfl
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
          have hhead : (next.world.memory addr).val = (state.world.memory addr).val :=
            hbody state index next hb
          have htail := execForEachLoop_preserves_memory_val_bound
            varName addr runBody hbody next s' (index + 1) remaining h
          rw [htail, hhead]
      | stop next => rw [hb] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hb] at h; exact absurd h (by simp)
      | revert => rw [hb] at h; exact absurd h (by simp)

/-- Range-gated raw `execForEachLoop` memory frame.  The preservation proof may
depend on a predicate over the concrete loop index, and callers supply that
predicate only for the executed range `[index, index + remaining)`. -/
theorem execForEachLoop_preserves_memory_val_range
    (varName : String) (addr : Nat) (runBody : RuntimeState → StmtResult)
    (D : Nat → Prop)
    (hbody : ∀ (s : RuntimeState) (idx : Nat), D idx → ∀ (s'' : RuntimeState),
        runBody { s with bindings := bindValue s.bindings varName (wordNormalize idx) }
          = .continue s'' →
        (s''.world.memory addr).val = (s.world.memory addr).val) :
    ∀ (state s' : RuntimeState) (index remaining : Nat),
      (∀ i, index ≤ i → i < index + remaining → D i) →
      execForEachLoop varName runBody state index remaining = .continue s' →
      (s'.world.memory addr).val = (state.world.memory addr).val
  | state, s', _, 0, _, h => by
      rw [show execForEachLoop varName runBody state _ 0 = .continue state from rfl] at h
      injection h with hh
      subst hh
      rfl
  | state, s', index, remaining + 1, hD, h => by
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
          have hhead : (next.world.memory addr).val = (state.world.memory addr).val :=
            hbody state index (hD index (by omega) (by omega)) next hb
          have htail := execForEachLoop_preserves_memory_val_range
            varName addr runBody D hbody next s' (index + 1) remaining
            (fun i hi1 hi2 => hD i (by omega) (by omega)) h
          rw [htail, hhead]
      | stop next => rw [hb] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hb] at h; exact absurd h (by simp)
      | revert => rw [hb] at h; exact absurd h (by simp)

/-- A `forEach varName count body` statement preserves `addr` when every
statement of `body` preserves that memory-cell value on continuing executions.
The count expression is cased abstractly, so this lemma does not evaluate hash or
calldata content. -/
theorem execStmt_forEach_preserves_memory_val
    (varName : String) (addr : Nat) (count : Expr) (body : List Stmt)
    (st s' : RuntimeState)
    (hbody : ∀ (s s'' : RuntimeState) (stmt : Stmt),
        stmt ∈ body → execStmt [] s stmt = .continue s'' →
        (s''.world.memory addr).val = (s.world.memory addr).val)
    (h : execStmt [] st (.forEach varName count body) = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
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
          (s''.world.memory addr).val = (s.world.memory addr).val :=
        fun s s'' hh => execStmtList_preserves_memory_val addr body s s'' hbody hh
      rw [execForEachLoop_preserves_memory_val varName addr
        (fun ls => execStmtList [] ls body) hrun
        { st with bindings := bindValue st.bindings varName (wordNormalize 0) }
        s' 0 bound h]

/-- Bounded-index statement-level `forEach` memory frame.  The body-preservation
hypothesis sees the concrete loop index used for the bind and the pre-bind state
for that iteration. -/
theorem execStmt_forEach_preserves_memory_val_bound
    (varName : String) (addr : Nat) (count : Expr) (body : List Stmt)
    (st s' : RuntimeState)
    (hbody : ∀ (s : RuntimeState) (idx : Nat) (s'' : RuntimeState),
        execStmtList [] { s with bindings := bindValue s.bindings varName (wordNormalize idx) } body
          = .continue s'' →
        (s''.world.memory addr).val = (s.world.memory addr).val)
    (h : execStmt [] st (.forEach varName count body) = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
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
      have hloop := execForEachLoop_preserves_memory_val_bound varName addr
        (fun ls => execStmtList [] ls body) hbody
        { st with bindings := bindValue st.bindings varName (wordNormalize 0) }
        s' 0 bound h
      simpa using hloop

/-- Range-gated statement-level `forEach` memory frame.  The body-preservation
proof may depend on a predicate over the concrete loop index, and callers supply
that predicate only for the range actually covered by the evaluated count. -/
theorem execStmt_forEach_preserves_memory_val_range
    (varName : String) (addr : Nat) (count : Expr) (body : List Stmt)
    (D : Nat → Prop) (st s' : RuntimeState)
    (hbody : ∀ (s : RuntimeState) (idx : Nat), D idx → ∀ (s'' : RuntimeState),
        execStmtList [] { s with bindings := bindValue s.bindings varName (wordNormalize idx) } body
          = .continue s'' →
        (s''.world.memory addr).val = (s.world.memory addr).val)
    (hD : ∀ (bound i : Nat), evalExpr [] st count = some bound →
        0 ≤ i → i < bound → D i)
    (h : execStmt [] st (.forEach varName count body) = .continue s') :
    (s'.world.memory addr).val = (st.world.memory addr).val := by
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
      have hrange : ∀ i, 0 ≤ i → i < 0 + bound → D i := by
        intro i hi0 hib
        exact hD bound i hc hi0 (by simpa using hib)
      have hloop := execForEachLoop_preserves_memory_val_range varName addr
        (fun ls => execStmtList [] ls body) D hbody
        { st with bindings := bindValue st.bindings varName (wordNormalize 0) }
        s' 0 bound hrange h
      simpa using hloop

/-! ## 4. Axiom audit. -/

#print axioms execStmt_letVar_preserves_memory_val
#print axioms execStmt_assignVar_preserves_memory_val
#print axioms execStmt_mstore_preserves_memory_val
#print axioms execStmtList_preserves_memory_val
#print axioms execForEachLoop_preserves_memory_val
#print axioms execForEachLoop_preserves_memory_val_bound
#print axioms execForEachLoop_preserves_memory_val_range
#print axioms execStmt_forEach_preserves_memory_val
#print axioms execStmt_forEach_preserves_memory_val_bound
#print axioms execStmt_forEach_preserves_memory_val_range

end SphincsMinusVerifiers.MemoryFrame
