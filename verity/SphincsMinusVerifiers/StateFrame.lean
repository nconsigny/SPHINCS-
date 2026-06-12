/-
  StateFrame — selector/calldata frame lemmas for straight-line and loop bodies.

  The verifier's accept-path statements read calldata but do not mutate the EVM
  selector or calldata image.  These lemmas package that structural fact for
  `letVar`/`assignVar`/`mstore`/`forEach`, mirroring `BindingFrame` but over the
  static state fields needed by calldata-read bridges.
-/

import SphincsMinusVerifiers.ClimbLoop

namespace SphincsMinusVerifiers.StateFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

abbrev PreservesSelectorCalldata (st s' : RuntimeState) : Prop :=
  s'.selector = st.selector ∧ s'.world.calldata = st.world.calldata

theorem execStmt_letVar_preserves_selector_calldata
    (st s' : RuntimeState) (name : String) (e : Expr)
    (h : execStmt [] st (.letVar name e) = .continue s') :
    PreservesSelectorCalldata st s' := by
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
      exact ⟨rfl, rfl⟩

theorem execStmt_assignVar_preserves_selector_calldata
    (st s' : RuntimeState) (name : String) (e : Expr)
    (h : execStmt [] st (.assignVar name e) = .continue s') :
    PreservesSelectorCalldata st s' := by
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
      exact ⟨rfl, rfl⟩

theorem execStmt_mstore_preserves_selector_calldata
    (st s' : RuntimeState) (off val : Expr)
    (h : execStmt [] st (.mstore off val) = .continue s') :
    PreservesSelectorCalldata st s' := by
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
          exact ⟨rfl, rfl⟩

theorem execStmtList_preserves_selector_calldata :
    ∀ (body : List Stmt) (st s' : RuntimeState),
      (∀ (s s'' : RuntimeState) (stmt : Stmt),
          stmt ∈ body → execStmt [] s stmt = .continue s'' →
          PreservesSelectorCalldata s s'') →
      execStmtList [] st body = .continue s' →
      PreservesSelectorCalldata st s'
  | [], st, s', _, h => by
      rw [show execStmtList [] st ([] : List Stmt) = .continue st from rfl] at h
      injection h with hh
      subst hh
      exact ⟨rfl, rfl⟩
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
          have hhead : PreservesSelectorCalldata st next :=
            hpre st next stmt (List.mem_cons.mpr (Or.inl rfl)) hs
          have htail : PreservesSelectorCalldata next s' :=
            execStmtList_preserves_selector_calldata rest next s'
              (fun s s'' stm hmem hexec =>
                hpre s s'' stm (List.mem_cons.mpr (Or.inr hmem)) hexec)
              h
          exact ⟨by rw [htail.1, hhead.1], by rw [htail.2, hhead.2]⟩
      | stop next => rw [hs] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hs] at h; exact absurd h (by simp)
      | revert => rw [hs] at h; exact absurd h (by simp)

theorem execForEachLoop_preserves_selector_calldata
    (varName : String) (runBody : RuntimeState → StmtResult)
    (hbody : ∀ (s s'' : RuntimeState),
        runBody s = .continue s'' → PreservesSelectorCalldata s s'') :
    ∀ (state s' : RuntimeState) (index remaining : Nat),
      execForEachLoop varName runBody state index remaining = .continue s' →
      PreservesSelectorCalldata state s'
  | state, s', _, 0, h => by
      rw [execForEachLoop_zero] at h
      injection h with hh
      subst hh
      exact ⟨rfl, rfl⟩
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
          have hhead : PreservesSelectorCalldata state next := by
            have hbody' := hbody _ next hb
            exact ⟨hbody'.1, hbody'.2⟩
          have htail := execForEachLoop_preserves_selector_calldata varName runBody
            hbody next s' (index + 1) remaining h
          exact ⟨by rw [htail.1, hhead.1], by rw [htail.2, hhead.2]⟩
      | stop next => rw [hb] at h; exact absurd h (by simp)
      | «return» rv rs => rw [hb] at h; exact absurd h (by simp)
      | revert => rw [hb] at h; exact absurd h (by simp)

theorem execStmt_forEach_preserves_selector_calldata
    (varName : String) (count : Expr) (body : List Stmt) (st s' : RuntimeState)
    (hbody : ∀ (s s'' : RuntimeState) (stmt : Stmt),
        stmt ∈ body → execStmt [] s stmt = .continue s'' →
        PreservesSelectorCalldata s s'')
    (h : execStmt [] st (.forEach varName count body) = .continue s') :
    PreservesSelectorCalldata st s' := by
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
          PreservesSelectorCalldata s s'' :=
        fun s s'' hh => execStmtList_preserves_selector_calldata body s s'' hbody hh
      exact execForEachLoop_preserves_selector_calldata varName
        (fun ls => execStmtList [] ls body) hrun
        { st with bindings := bindValue st.bindings varName (wordNormalize 0) }
        s' 0 bound h

theorem foldLoop_preserves_selector_calldata
    (varName : String) (step : RuntimeState → RuntimeState)
    (hstep : ∀ s, PreservesSelectorCalldata s (step s)) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      PreservesSelectorCalldata state (ClimbLoop.foldLoop varName step state index remaining)
  | state, _, 0 => by
      rw [ClimbLoop.foldLoop_zero]
      exact ⟨rfl, rfl⟩
  | state, index, remaining + 1 => by
      rw [ClimbLoop.foldLoop_succ]
      have hhead : PreservesSelectorCalldata state
          (step { state with bindings := bindValue state.bindings varName (wordNormalize index) }) := by
        have hs := hstep { state with bindings := bindValue state.bindings varName (wordNormalize index) }
        exact ⟨hs.1, hs.2⟩
      have htail := foldLoop_preserves_selector_calldata varName step hstep
        (step { state with bindings := bindValue state.bindings varName (wordNormalize index) })
        (index + 1) remaining
      exact ⟨by rw [htail.1, hhead.1], by rw [htail.2, hhead.2]⟩

/-! ## Axiom audit. -/

#print axioms execStmt_letVar_preserves_selector_calldata
#print axioms execStmt_assignVar_preserves_selector_calldata
#print axioms execStmt_mstore_preserves_selector_calldata
#print axioms execStmtList_preserves_selector_calldata
#print axioms execForEachLoop_preserves_selector_calldata
#print axioms execStmt_forEach_preserves_selector_calldata
#print axioms foldLoop_preserves_selector_calldata

end SphincsMinusVerifiers.StateFrame
-- NOTE (2026-06 factoring): Generic selector/calldata preservation now in
-- Compiler.Proofs.Frames (Verity PR #1983). This file provides the SPHINCS-
-- specific frame for the C13 accept path.
