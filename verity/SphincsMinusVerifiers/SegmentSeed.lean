/-
  SegmentSeed — Layer-2 segment lemma for the C13 hypertree-climb seed,
  statements 22..24 of `SphincsMinusVerifiers.c13VerifyBody`
  (see `INTERFACE_CONTRACT.md`: the S4 → Layer-3 boundary).

  The three statements are:

  ```
  22. letVar "currentNode" := forsPk        -- climb starts at the FORS public key
  23. letVar "idxTree"     := htIdx          -- climb starts at the hypertree index
  24. letVar "sigOff"      := 1952           -- first XMSS-layer signature offset
  ```

  These are pure binder writes: no guard, no memory, no calldata — the glue that
  seeds the `forEach "layer"` hypertree climb (statement 25) from S4's FORS
  reconstruction output.  In the spec mirror this is exactly the seeding of
  `c13FinalRoot pk digest forsPk layers
     = c13HtClimb pk d 0 digest.hyperIndex forsPk layers`
  (`C13Mirror.c13FinalRoot_eq_climb`): the climb's initial node is `forsPk`
  (`currentNode`) and its initial tree index is `htIdx = digest.hyperIndex`
  (`idxTree`).

  The headline lemma `execSegmentSeed` shows that running these three statements
  over the real Verity source interpreter unconditionally continues to
  `stepSeed st`, and the three accessor corollaries pin the bound values that the
  Layer-3 climb lemma will consume.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers.SegmentSeed

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! ## 0. The three seed statements, written with bare public constructors.

As in `SegmentS3`, we replicate the statements with bare `Expr`/`Stmt`
constructors so this file does not depend on `Model.lean`'s private EDSL
helpers.  `segmentSeed_eq_slice` machine-checks (`rfl`) that this list is exactly
statements 22..24 of the real `c13VerifyBody`, so the replication is faithful by
construction. -/

/-- The seed statement segment (statements 22..24 of `c13VerifyBody`). -/
def segmentSeed : List Stmt :=
  [ .letVar "currentNode" (.localVar "forsPk")
  , .letVar "idxTree" (.localVar "htIdx")
  , .letVar "sigOff" (.literal 1952) ]

/-- Faithfulness: `segmentSeed` is *exactly* statements 22..24 of `c13VerifyBody`. -/
theorem segmentSeed_eq_slice :
    segmentSeed = (c13VerifyBodyTail.drop 24).take 3 := rfl

/-! ## 1. The accept-path state transformer. -/

/-- The seed state transformer: bind `currentNode := forsPk`, `idxTree := htIdx`,
`sigOff := 1952` (the interpreter normalises the literal to `wordNormalize 1952`).
The two `localVar` reads are taken from `st` because their keys differ from the
ones being written, so the chained binds do not shadow them. -/
def stepSeed (st : RuntimeState) : RuntimeState :=
  { st with bindings := bindValue (bindValue (bindValue st.bindings "currentNode" (lookupValue st.bindings "forsPk")) "idxTree" (lookupValue st.bindings "htIdx")) "sigOff" (wordNormalize 1952) }

/-! ## 2. Local interpreter combinators (self-contained copies of the SegmentS3
helpers, re-declared so this file stands alone). -/

private theorem letVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.letVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

private theorem execStmtList_cons_continue
    (st st' : RuntimeState) (s : Stmt) (rest : List Stmt)
    (h : execStmt [] st s = .continue st') :
    execStmtList [] st (s :: rest) = execStmtList [] st' rest := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = execStmtList [] st' rest
  rw [h]

private theorem find_filter_ne
    (bs : List (String × Nat)) (k k' : String) (h : k ≠ k') :
    (bs.filter (fun e => e.1 != k)).find? (fun e => e.1 == k')
      = bs.find? (fun e => e.1 == k') := by
  induction bs with
  | nil => rfl
  | cons e rest ih =>
    by_cases he : e.1 = k
    · have hf : (e.1 != k) = false := by simp [he]
      have hk' : (e.1 == k') = false := by
        subst he; exact beq_eq_false_iff_ne.mpr h
      simp [List.filter_cons, hf, List.find?_cons, hk', ih]
    · have hf : (e.1 != k) = true := by simp [he]
      by_cases hk' : e.1 = k'
      · have hk't : (e.1 == k') = true := beq_iff_eq.mpr hk'
        simp [List.filter_cons, hf, List.find?_cons, hk't]
      · have hk'f : (e.1 == k') = false := beq_eq_false_iff_ne.mpr hk'
        simp [List.filter_cons, hf, List.find?_cons, hk'f, ih]

private theorem lookupValue_bindValue_ne
    (bs : List (String × Nat)) (k k' : String) (val : Nat) (h : k ≠ k') :
    lookupValue (bindValue bs k val) k' = lookupValue bs k' := by
  have hk : (k == k') = false := beq_eq_false_iff_ne.mpr h
  unfold lookupValue bindValue
  rw [List.find?_cons]
  simp only [hk, Bool.false_eq_true, if_false]
  rw [find_filter_ne bs k k' h]

/-! ## 3. The headline segment lemma. -/

/-- **`execSegmentSeed`** — running statements 22..24 of `c13VerifyBody` over the
real interpreter unconditionally continues to `stepSeed st`.  These are pure
binder writes (no guard), so there is no revert branch.  Proved with no
hypotheses on `st`. -/
theorem execSegmentSeed (st : RuntimeState) :
    execStmtList [] st segmentSeed = .continue (stepSeed st) := by
  show execStmtList [] st
        ([ .letVar "currentNode" (.localVar "forsPk")
         , .letVar "idxTree" (.localVar "htIdx")
         , .letVar "sigOff" (.literal 1952) ] : List Stmt)
      = .continue (stepSeed st)
  -- step 22: letVar currentNode := forsPk
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue st "currentNode" (.localVar "forsPk")
          (lookupValue st.bindings "forsPk") rfl)]
  -- step 23: letVar idxTree := htIdx.  The interpreter reads `htIdx` from the
  -- post-step-22 bindings; rewrite it back to `st.bindings` (keys differ).
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue _ "idxTree" (.localVar "htIdx")
          (lookupValue st.bindings "htIdx")
          (by
            show some (lookupValue
                (bindValue st.bindings "currentNode" (lookupValue st.bindings "forsPk"))
                "htIdx") = some (lookupValue st.bindings "htIdx")
            rw [lookupValue_bindValue_ne st.bindings "currentNode" "htIdx"
                  (lookupValue st.bindings "forsPk") (by decide)]))]
  -- step 24: letVar sigOff := 1952 (literal normalises to wordNormalize 1952)
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue _ "sigOff" (.literal 1952) (wordNormalize 1952) rfl)]
  rfl

/-! ## 4. Accessor corollaries — the bound values the Layer-3 climb consumes.

`stepSeed` seeds the hypertree climb; these pin the three reads the climb lemma
needs, mirroring `C13Mirror.c13FinalRoot_eq_climb` (initial node `= forsPk`,
initial tree index `= htIdx = digest.hyperIndex`). -/

/-- The bindings of `stepSeed st` as an explicit three-deep `bindValue` chain
(the structure-update projection reduces by `rfl`). -/
private theorem stepSeed_bindings (st : RuntimeState) :
    (stepSeed st).bindings = bindValue (bindValue (bindValue st.bindings "currentNode" (lookupValue st.bindings "forsPk")) "idxTree" (lookupValue st.bindings "htIdx")) "sigOff" (wordNormalize 1952) := rfl

private theorem lookupValue_bindValue_self
    (bs : List (String × Nat)) (k : String) (val : Nat) :
    lookupValue (bindValue bs k val) k = val := by
  simp [lookupValue, bindValue]

theorem stepSeed_currentNode (st : RuntimeState) :
    lookupValue (stepSeed st).bindings "currentNode" = lookupValue st.bindings "forsPk" := by
  rw [stepSeed_bindings,
      lookupValue_bindValue_ne _ "sigOff" "currentNode" _ (by decide),
      lookupValue_bindValue_ne _ "idxTree" "currentNode" _ (by decide),
      lookupValue_bindValue_self]

theorem stepSeed_idxTree (st : RuntimeState) :
    lookupValue (stepSeed st).bindings "idxTree" = lookupValue st.bindings "htIdx" := by
  rw [stepSeed_bindings,
      lookupValue_bindValue_ne _ "sigOff" "idxTree" _ (by decide),
      lookupValue_bindValue_self]

theorem stepSeed_sigOff (st : RuntimeState) :
    lookupValue (stepSeed st).bindings "sigOff" = wordNormalize 1952 := by
  rw [stepSeed_bindings, lookupValue_bindValue_self]

/-! ## 5. Axiom audit. -/

#print axioms execSegmentSeed
#print axioms segmentSeed_eq_slice
#print axioms stepSeed_currentNode
#print axioms stepSeed_idxTree
#print axioms stepSeed_sigOff

end SphincsMinusVerifiers.SegmentSeed
