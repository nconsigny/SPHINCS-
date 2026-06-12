/-
  SegmentS3 — Layer-2 segment lemma for the C13 index-extraction + forced-zero
  guard, statements 10..13 of `SphincsMinusVerifiers.c13VerifyBody`
  (see `INTERFACE_CONTRACT.md`, segment S3).

  The four statements are:

  ```
  10. letVar "htIdx"   := (digest >> 133) & 0x3FFFFF        -- hypertree leaf index
  11. letVar "dVal"    := digest                            -- alias of the digest
  12. ite ((dVal >> 114) & 0x7FFFF) revert0 []              -- FORS forced-zero guard
  13. letVar "sigBase" := sig_data_offset                   -- signature base pointer
  ```

  Statement 12 is the FIPS-205 "forced zero" check: the last FORS index
  (`(digest >> 19*6) & (2^19-1) = (digest >> 114) & 0x7FFFF`) must be zero, else
  the verifier reverts.  This exactly mirrors `forcedZeroOk` in the byte spec
  (`SphincsMinusVerifierSpec.Spec`, t = 6, forsK = 7).

  The headline lemma `execSegmentS3` shows that running these four statements over
  the real Verity source interpreter either
    * continues to `stepS3 st` (when the guard value is `0`), or
    * reverts (when the guard value is non-zero),
  with the branch predicate being precisely the interpreter's evaluation of the
  guard expression.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers.SegmentS3

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt UnsafeYulFragment)

/-! ## 0. The four S3 statements, written with bare public constructors.

We replicate the statements as bare `Expr`/`Stmt` constructors so that this file
does not depend on `Model.lean`'s private EDSL helpers.  `segmentS3_eq_slice`
below machine-checks (by `rfl`) that this list is *exactly* statements 10..13 of
the real `c13VerifyBody`, so the replication is faithful by construction. -/

/-- `revert0` — the handwritten `revert(0,0)` fragment, copied verbatim from
`Model.lean` so the `rfl` faithfulness check against `c13VerifyBody` succeeds. -/
private def revert0 : List Stmt := [
  .unsafeYul <|
    UnsafeYulFragment.rawRevert (.lit 0) (.lit 0)
      { name := "raw_yul_revert_0_0_refines_solidity_assembly"
        obligation := "The handwritten Yul revert(0, 0) must match the Solidity assembly observable revert behavior."
        proofStatus := .assumed }
      "raw_yul_revert_0_0"
]

/-- The forced-zero guard condition expression: `(dVal >> 114) & 0x7FFFF`. -/
private def s3CondExpr : Expr :=
  .bitAnd (.shr (.literal 114) (.localVar "dVal")) (.literal 0x7FFFF)

/-- The S3 statement segment (statements 9..12 of `c13VerifyBodyTail`). -/
def segmentS3 : List Stmt :=
  [ .letVar "htIdx" (.bitAnd (.shr (.literal 133) (.localVar "digest")) (.literal 0x3FFFFF))
  , .letVar "dVal" (.localVar "digest")
  , .ite s3CondExpr revert0 []
  , .letVar "sigBase" (.localVar "sig_data_offset") ]

/-- Faithfulness: `segmentS3` is *exactly* statements 9..12 of `c13VerifyBodyTail`. -/
theorem segmentS3_eq_slice :
    segmentS3 = (c13VerifyBodyTail.drop 9).take 4 := rfl

/-! ## 1. Resolved values of the three `letVar` writes.

These are the closed-form `Nat` values the interpreter binds, expressed in the
*same* normal form `evalExpr` produces (so the per-statement reductions are
`rfl`-driven). -/

/-- Value bound to `htIdx`: `(digest >> 133) & 0x3FFFFF`, in evaluator normal form. -/
def htIdxVal (st : RuntimeState) : Nat :=
  (Verity.Core.Uint256.and
    (Verity.Core.Uint256.shr (wordNormalize 133) (lookupValue st.bindings "digest")).val
    (wordNormalize 0x3FFFFF)).val

/-- The forced-zero guard value: `(digest >> 114) & 0x7FFFF`, in evaluator normal form. -/
def s3Guard (st : RuntimeState) : Nat :=
  (Verity.Core.Uint256.and
    (Verity.Core.Uint256.shr (wordNormalize 114) (lookupValue st.bindings "digest")).val
    (wordNormalize 0x7FFFF)).val

/-- The accept-path state transformer for S3: bind `htIdx`, `dVal`, `sigBase`. -/
def stepS3 (st : RuntimeState) : RuntimeState :=
  let b1 := bindValue st.bindings "htIdx" (htIdxVal st)
  let b2 := bindValue b1 "dVal" (lookupValue st.bindings "digest")
  let b3 := bindValue b2 "sigBase" (lookupValue st.bindings "sig_data_offset")
  { st with bindings := b3 }

/-! ## 1a. Closed form for the forced-zero guard mask.

The interpreter exposes the guard as a `Uint256.and` with literal mask
`0x7FFFF`.  The byte spec exposes the same value as FORS index 6,
`digest >>> 114` reduced modulo `2^19`.  The two facts below are the pure
arithmetic bridge between those presentations. -/

theorem nat_land_low19 (x : Nat) : Nat.land x 0x7FFFF = x % 2 ^ 19 := by
  change (x &&& (2 ^ 19 - 1)) = x % 2 ^ 19
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 19
  · have hmask : (2 ^ 19 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 19 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

theorem nat_land_low22 (x : Nat) : Nat.land x 0x3FFFFF = x % 2 ^ 22 := by
  change (x &&& (2 ^ 22 - 1)) = x % 2 ^ 22
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 22
  · have hmask : (2 ^ 22 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 22 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

theorem htIdxVal_eq_hyperIndex
    (st : RuntimeState) (digest : Nat)
    (hdigest : lookupValue st.bindings "digest" = digest)
    (hBound : digest < 2 ^ 256) :
    htIdxVal st = (digest >>> 133) % 2 ^ 22 := by
  unfold htIdxVal
  rw [hdigest]
  have h133 : wordNormalize 133 = 133 := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide : 133 < 2 ^ 256)
  have hmask : wordNormalize 0x3FFFFF = 0x3FFFFF := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide : 0x3FFFFF < 2 ^ 256)
  rw [h133, hmask]
  show (Verity.Core.Uint256.and (Verity.Core.Uint256.shr 133 digest).val 0x3FFFFF).val
      = (digest >>> 133) % 2 ^ 22
  show ((Verity.Core.Uint256.ofNat
        (Nat.land (Verity.Core.Uint256.ofNat
          (Verity.Core.Uint256.shr 133 digest).val).val
          (Verity.Core.Uint256.ofNat 0x3FFFFF).val)).val)
      = (digest >>> 133) % 2 ^ 22
  have h133v : (Verity.Core.Uint256.ofNat 133).val = 133 :=
    Nat.mod_eq_of_lt (by decide : 133 < 2 ^ 256)
  have hdv : (Verity.Core.Uint256.ofNat digest).val = digest :=
    Nat.mod_eq_of_lt hBound
  have hshrval : (Verity.Core.Uint256.shr 133 digest).val = digest >>> 133 := by
    show ((Verity.Core.Uint256.ofNat
            ((Verity.Core.Uint256.ofNat digest).val >>>
              (Verity.Core.Uint256.ofNat 133).val)).val)
        = digest >>> 133
    rw [hdv, h133v]
    show (digest >>> 133) % Verity.Core.Uint256.modulus = digest >>> 133
    have hlt : digest >>> 133 < 2 ^ 256 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self digest (2 ^ 133)) hBound
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hlt]
  rw [hshrval]
  have hshrBound : digest >>> 133 < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self digest (2 ^ 133)) hBound
  have hshrv : (Verity.Core.Uint256.ofNat (digest >>> 133)).val = digest >>> 133 :=
    Nat.mod_eq_of_lt hshrBound
  have hmaskv : (Verity.Core.Uint256.ofNat 0x3FFFFF).val = 0x3FFFFF :=
    Nat.mod_eq_of_lt (by decide : 0x3FFFFF < 2 ^ 256)
  rw [hshrv, hmaskv]
  show Nat.land (digest >>> 133) 0x3FFFFF % Verity.Core.Uint256.modulus =
      (digest >>> 133) % 2 ^ 22
  have hlandBound : Nat.land (digest >>> 133) 0x3FFFFF < 2 ^ 256 :=
    Nat.lt_of_le_of_lt Nat.and_le_left hshrBound
  rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hlandBound]
  exact nat_land_low22 (digest >>> 133)

theorem s3Guard_eq_forsIndex6
    (st : RuntimeState) (digest : Nat)
    (hdigest : lookupValue st.bindings "digest" = digest)
    (hBound : digest < 2 ^ 256) :
    s3Guard st = (digest >>> 114) % 2 ^ 19 := by
  unfold s3Guard
  rw [hdigest]
  have h114 : wordNormalize 114 = 114 := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide : 114 < 2 ^ 256)
  have hmask : wordNormalize 0x7FFFF = 0x7FFFF := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide : 0x7FFFF < 2 ^ 256)
  rw [h114, hmask]
  show (Verity.Core.Uint256.and (Verity.Core.Uint256.shr 114 digest).val 0x7FFFF).val
      = (digest >>> 114) % 2 ^ 19
  show ((Verity.Core.Uint256.ofNat
        (Nat.land (Verity.Core.Uint256.ofNat
          (Verity.Core.Uint256.shr 114 digest).val).val
          (Verity.Core.Uint256.ofNat 0x7FFFF).val)).val)
      = (digest >>> 114) % 2 ^ 19
  have h114v : (Verity.Core.Uint256.ofNat 114).val = 114 :=
    Nat.mod_eq_of_lt (by decide : 114 < 2 ^ 256)
  have hdv : (Verity.Core.Uint256.ofNat digest).val = digest :=
    Nat.mod_eq_of_lt hBound
  have hshrval : (Verity.Core.Uint256.shr 114 digest).val = digest >>> 114 := by
    show ((Verity.Core.Uint256.ofNat
            ((Verity.Core.Uint256.ofNat digest).val >>>
              (Verity.Core.Uint256.ofNat 114).val)).val)
        = digest >>> 114
    rw [hdv, h114v]
    show (digest >>> 114) % Verity.Core.Uint256.modulus = digest >>> 114
    have hlt : digest >>> 114 < 2 ^ 256 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self digest (2 ^ 114)) hBound
    rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hlt]
  rw [hshrval]
  have hshrBound : digest >>> 114 < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self digest (2 ^ 114)) hBound
  have hshrv : (Verity.Core.Uint256.ofNat (digest >>> 114)).val = digest >>> 114 :=
    Nat.mod_eq_of_lt hshrBound
  have hmaskv : (Verity.Core.Uint256.ofNat 0x7FFFF).val = 0x7FFFF :=
    Nat.mod_eq_of_lt (by decide : 0x7FFFF < 2 ^ 256)
  rw [hshrv, hmaskv]
  show Nat.land (digest >>> 114) 0x7FFFF % Verity.Core.Uint256.modulus =
      (digest >>> 114) % 2 ^ 19
  have hlandBound : Nat.land (digest >>> 114) 0x7FFFF < 2 ^ 256 :=
    Nat.lt_of_le_of_lt Nat.and_le_left hshrBound
  rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hlandBound]
  exact nat_land_low19 (digest >>> 114)

/-! ## 2. Local interpreter combinators (self-contained copies). -/

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

private theorem execStmtList_cons_revert
    (st : RuntimeState) (s : Stmt) (rest : List Stmt)
    (h : execStmt [] st s = .revert) :
    execStmtList [] st (s :: rest) = .revert := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = .revert
  rw [h]

/-! ## 3. `lookupValue` / `bindValue` interaction lemmas. -/

private theorem lookupValue_bindValue_self
    (bs : List (String × Nat)) (k : String) (val : Nat) :
    lookupValue (bindValue bs k val) k = val := by
  simp [lookupValue, bindValue]

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

/-! ## 4. The forced-zero `ite` reduction. -/

private theorem ite_forcedZero_reduce
    (s : RuntimeState) (g : Nat)
    (hc : evalExpr [] s s3CondExpr = some g) :
    execStmt [] s (.ite s3CondExpr revert0 []) =
      if g = 0 then .continue s else .revert := by
  show (match evalExpr [] s s3CondExpr with
        | some r => if r != 0 then execStmtList [] s revert0 else execStmtList [] s []
        | none => .revert) = _
  rw [hc]
  show (if (g != 0) = true then execStmtList [] s revert0 else execStmtList [] s [])
        = if g = 0 then .continue s else .revert
  by_cases h : g = 0
  · subst h; rfl
  · rw [if_pos (bne_iff_ne.mpr h), if_neg h]
    rfl

/-- The same guard reduction, lifted to the head of a statement list. -/
private theorem ite_cons_reduce
    (s : RuntimeState) (rest : List Stmt) (g : Nat)
    (hc : evalExpr [] s s3CondExpr = some g) :
    execStmtList [] s (.ite s3CondExpr revert0 [] :: rest)
      = if g = 0 then execStmtList [] s rest else .revert := by
  show (match execStmt [] s (.ite s3CondExpr revert0 []) with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = _
  rw [ite_forcedZero_reduce s g hc]
  by_cases h : g = 0
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- Binding `dVal := digest` and then running the forced-zero `ite`: the guard
value is `s3Guard s` (read off `s`'s `digest`), and on the accept branch we
continue in the state with `dVal` bound. -/
private theorem dVal_ite_reduce (s : RuntimeState) (rest : List Stmt) :
    execStmtList [] s
        (.letVar "dVal" (.localVar "digest") :: .ite s3CondExpr revert0 [] :: rest)
      = if s3Guard s = 0
        then execStmtList []
              { s with bindings := bindValue s.bindings "dVal" (lookupValue s.bindings "digest") } rest
        else .revert := by
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue s "dVal" (.localVar "digest") (lookupValue s.bindings "digest") rfl)]
  have hc : evalExpr []
        { s with bindings := bindValue s.bindings "dVal" (lookupValue s.bindings "digest") } s3CondExpr
      = some (s3Guard s) := by
    show some (Verity.Core.Uint256.and
                (Verity.Core.Uint256.shr (wordNormalize 114)
                  (lookupValue (bindValue s.bindings "dVal" (lookupValue s.bindings "digest")) "dVal")).val
                (wordNormalize 0x7FFFF)).val
          = some (s3Guard s)
    rw [lookupValue_bindValue_self]
    rfl
  rw [ite_cons_reduce _ rest (s3Guard s) hc]

/-! ## 5. The headline segment lemma. -/

set_option maxHeartbeats 1000000 in
/-- **`execSegmentS3`** — running statements 10..13 of `c13VerifyBody` over the
real interpreter continues to `stepS3 st` when the FORS forced-zero guard value
is `0`, and reverts otherwise.  Proved unconditionally (no hypotheses on `st`). -/
theorem execSegmentS3 (st : RuntimeState) :
    execStmtList [] st segmentS3
      = if s3Guard st = 0 then .continue (stepS3 st) else .revert := by
  show execStmtList [] st
        ([ .letVar "htIdx" (.bitAnd (.shr (.literal 133) (.localVar "digest")) (.literal 0x3FFFFF))
         , .letVar "dVal" (.localVar "digest")
         , .ite s3CondExpr revert0 []
         , .letVar "sigBase" (.localVar "sig_data_offset") ] : List Stmt)
      = if s3Guard st = 0 then .continue (stepS3 st) else .revert
  -- step 10: letVar htIdx (explicit bound value so the post-state is nameable)
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue st "htIdx"
          (.bitAnd (.shr (.literal 133) (.localVar "digest")) (.literal 0x3FFFFF))
          (htIdxVal st) rfl)]
  -- steps 11-12: letVar dVal then the forced-zero ite
  rw [dVal_ite_reduce]
  -- fold `s3Guard RAW10` back to `s3Guard st` (depends only on the `digest` binding)
  have hgg : s3Guard { st with bindings := bindValue st.bindings "htIdx" (htIdxVal st) }
              = s3Guard st := by
    show (Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr (wordNormalize 114)
              (lookupValue (bindValue st.bindings "htIdx" (htIdxVal st)) "digest")).val
            (wordNormalize 0x7FFFF)).val
          = s3Guard st
    rw [lookupValue_bindValue_ne st.bindings "htIdx" "digest" (htIdxVal st) (by decide)]
    rfl
  rw [hgg]
  by_cases h : s3Guard st = 0
  · -- accept path
    rw [if_pos h, if_pos h]
    -- step 13: letVar sigBase
    rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "sigBase" _ _ rfl)]
    show StmtResult.continue _ = StmtResult.continue (stepS3 st)
    congr 1
    unfold stepS3
    show ({ st with bindings := _ } : RuntimeState) = { st with bindings := _ }
    congr 1
    rw [lookupValue_bindValue_ne
          (bindValue st.bindings "htIdx" (htIdxVal st)) "dVal" "sig_data_offset"
          (lookupValue (bindValue st.bindings "htIdx" (htIdxVal st)) "digest") (by decide),
        lookupValue_bindValue_ne st.bindings "htIdx" "sig_data_offset" (htIdxVal st) (by decide),
        lookupValue_bindValue_ne st.bindings "htIdx" "digest" (htIdxVal st) (by decide)]
  · -- reject path
    rw [if_neg h, if_neg h]

/-! ## 6. Axiom audit. -/

#print axioms execSegmentS3
#print axioms segmentS3_eq_slice
#print axioms nat_land_low19
#print axioms nat_land_low22
#print axioms htIdxVal_eq_hyperIndex
#print axioms s3Guard_eq_forsIndex6

end SphincsMinusVerifiers.SegmentS3
