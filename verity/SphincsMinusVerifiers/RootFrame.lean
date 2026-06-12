/-
  RootFrame — the `"root"` bindings-frame for the post-S2 layer body.

  The accept decision compares `currentNode` against `root`.  `root` is written
  exactly once, in S2 (`Model.lean:101`, `.letVar "root" (p "pkRoot")`), and never
  reassigned.  The Layer-3 hypertree-climb body (`stepLayer`, the `.continue`
  payload of `prefix11 ++ suffix14`) must therefore carry `root` through untouched.

  This file proves that, keccak-free, by feeding the `BindingFrame` kit a
  per-statement frame for every body in the layer iteration.  Each body's frame is
  discharged by enumerating its statements (membership decomposition on the
  concrete list) and applying the matching §1 `BindingFrame` lemma — every written
  name (`"idxLeaf"`, `"digitSum"`, `"val"`, the loop variables `"ii"`/`"i"`/`"h"`/
  `"step"`, the climb's `"merkleNode"`/`"mIdx"`, …) is literally distinct from
  `"root"`, so the bound *values* (keccak digests included) are never evaluated.
  The inner `forEach` statements compose via
  `BindingFrame.execStmt_forEach_preserves_lookup`.

  Headline: `stepLayer_preserves_root`.  No `sorry`, no new `axiom`,
  no `native_decide`.
-/

import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.SegmentLayer3
import SphincsMinusVerifiers.SegmentCompose

namespace SphincsMinusVerifiers.RootFrame

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.BindingFrame
open SphincsMinusVerifiers.SegmentLayer3
open SphincsMinusVerifiers.ClimbKit (merkleClimbBody wotsChainBody)

/-- The frame obligation for a body `b`: every continuing statement preserves
`"root"`.  This is exactly the `hbody` hypothesis the `forEach`/list frame lemmas
consume. -/
abbrev PreservesRoot (b : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ b → execStmt [] s stmt = .continue s'' →
    lookupValue s''.bindings "root" = lookupValue s.bindings "root"

/-! ## 1. Innermost loop bodies. -/

theorem digitSumBody_pres : PreservesRoot digitSumBody := by
  intro s s'' stmt hmem hexec
  simp only [digitSumBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact execStmt_assignVar_preserves_lookup _ _ "digitSum" "root" _ (by decide) hexec

theorem wotsChainBody_pres : PreservesRoot wotsChainBody := by
  intro s s'' stmt hmem hexec
  simp only [wotsChainBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "val" "root" _ (by decide) hexec

theorem copyBody_pres : PreservesRoot copyBody := by
  intro s s'' stmt hmem hexec
  simp only [copyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec

theorem merkleClimbBody_pres
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (hn : nodeVar ≠ "root") (hi : idxVar ≠ "root") :
    PreservesRoot (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar) := by
  intro s s'' stmt hmem hexec
  simp only [merkleClimbBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "sibling" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "s" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_assignVar_preserves_lookup _ _ nodeVar "root" _ hn hexec
  · exact execStmt_assignVar_preserves_lookup _ _ idxVar "root" _ hi hexec

/-- Address-parametric variant: the climb body shape is independent of the
ADRS operand, so the same per-statement frame applies to `merkleClimbBodyA`
(hence to the FIPS `forsClimbBody`). -/
theorem merkleClimbBodyA_pres
    (nodeVar idxVar authPtrVar : String) (adrsE : Compiler.CompilationModel.Expr)
    (hn : nodeVar ≠ "root") (hi : idxVar ≠ "root") :
    PreservesRoot (ClimbKit.merkleClimbBodyA nodeVar idxVar authPtrVar adrsE) := by
  intro s s'' stmt hmem hexec
  simp only [ClimbKit.merkleClimbBodyA, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "sibling" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "parentIdx" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "s" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_assignVar_preserves_lookup _ _ nodeVar "root" _ hn hexec
  · exact execStmt_assignVar_preserves_lookup _ _ idxVar "root" _ hi hexec

theorem forsClimbBody_pres : PreservesRoot ClimbKit.forsClimbBody :=
  merkleClimbBodyA_pres "node" "pathIdx" "authPtr" ClimbKit.forsAdrs
    (by decide) (by decide)

/-! ## 2. The WOTS outer-loop body (contains the inner `forEach "step"`). -/

theorem wotsOuterBody_pres : PreservesRoot wotsOuterBody := by
  intro s s'' stmt hmem hexec
  simp only [wotsOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "digit" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "steps" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "val" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "chainBase" "root" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "step" "root" _ _ _ _ (by decide)
      wotsChainBody_pres hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec

/-! ## 3. The guard-free prefix and suffix of the layer body. -/

theorem prefix11_pres : PreservesRoot prefix11 := by
  intro s s'' stmt hmem hexec
  simp only [prefix11, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "idxLeaf" "root" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "idxTree" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "countOff" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "count" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "d" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "digitSum" "root" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "ii" "root" _ _ _ _ (by decide)
      digitSumBody_pres hexec

theorem suffix14_pres : PreservesRoot suffix14 := by
  intro s s'' stmt hmem hexec
  simp only [suffix14, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPtr" "root" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "i" "root" _ _ _ _ (by decide)
      wotsOuterBody_pres hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pkAdrs" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_forEach_preserves_lookup "i" "root" _ _ _ _ (by decide)
      copyBody_pres hexec
  · exact execStmt_letVar_preserves_lookup _ _ "wotsPk" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authOff" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "treeAdrs" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merkleNode" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "mIdx" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "merklePtr" "root" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "h" "root" _ _ _ _ (by decide)
      (merkleClimbBody_pres "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        (by decide) (by decide)) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "currentNode" "root" _ (by decide) hexec
  · exact execStmt_assignVar_preserves_lookup _ _ "sigOff" "root" _ (by decide) hexec

/-! ## 4. `prefix11`/`suffix14` carry `root` through; hence `stepLayer` does. -/

theorem afterDigit_preserves_root (ls : RuntimeState) :
    lookupValue (afterDigit ls).bindings "root" = lookupValue ls.bindings "root" :=
  execStmtList_preserves_lookup "root" prefix11 ls (afterDigit ls)
    prefix11_pres (afterDigit_eq ls)

/-- **`stepLayer_preserves_root`** — one accepting layer iteration carries the
`"root"` binding through untouched.  Keccak-free: no bound value is evaluated. -/
theorem stepLayer_preserves_root (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "root" = lookupValue ls.bindings "root" := by
  rw [execStmtList_preserves_lookup "root" suffix14 (afterDigit ls) (stepLayer ls)
        suffix14_pres (suffix14_continues ls),
      afterDigit_preserves_root ls]

/-! ## 5. Compose over the guarded `forEach "layer"` fold. -/

/-- **`afterLayer_preserves_root`** — the whole Layer-3 hypertree climb (the pure
`foldLoop "layer" stepLayer` image of the guarded `forEach "layer"`) carries the
`"root"` binding through untouched, back to its post-Seed value.  Composes the
per-iteration `stepLayer_preserves_root` over the fold via
`ClimbLoop.foldLoop_preserves_lookup`, plus one `lookupValue_bindValue_ne` for the
initial `"layer"`-variable bind (`"layer" ≠ "root"`).  Keccak-free. -/
theorem afterLayer_preserves_root (st : RuntimeState) :
    lookupValue (SegmentCompose.afterLayer st).bindings "root"
      = lookupValue (SegmentCompose.afterSeed st).bindings "root" := by
  unfold SegmentCompose.afterLayer
  rw [ClimbLoop.foldLoop_preserves_lookup "layer" "root" stepLayer
        (by decide) stepLayer_preserves_root _ 0 (wordNormalize 2)]
  exact MemoryKit.lookupValue_bindValue_ne (SegmentCompose.afterSeed st).bindings
    "layer" "root" (wordNormalize 0) (by decide)

/-! ## 6. The Seed segment frame (direct `bindValue` chain). -/

/-- `stepSeed` is a direct triple `bindValue` (`currentNode`/`idxTree`/`sigOff`,
all ≠ `root`), so it preserves `root` by peeling the three binds. -/
theorem stepSeed_preserves_root (st : RuntimeState) :
    lookupValue (SegmentSeed.stepSeed st).bindings "root" = lookupValue st.bindings "root" := by
  unfold SegmentSeed.stepSeed
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigOff" "root" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "idxTree" "root" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "currentNode" "root" _ (by decide)]

/-- The post-Seed `root` equals the post-Finalize `root` (Seed never touches it). -/
theorem afterSeed_preserves_root (st : RuntimeState) :
    lookupValue (SegmentCompose.afterSeed st).bindings "root"
      = lookupValue (SegmentCompose.afterFinalize st).bindings "root" := by
  unfold SegmentCompose.afterSeed
  exact stepSeed_preserves_root (SegmentCompose.afterFinalize st)

/-! ## 7. The FORS finalize block frame. -/

theorem forsCopyBody_pres : PreservesRoot SegmentS4Finalize.forsCopyBody := by
  intro s s'' stmt hmem hexec
  refine SegmentS4Finalize.forsCopyBody_mem_cases
    (P := fun stmt => execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "root" = lookupValue s.bindings "root")
    hmem ?_ hexec
  intro hexec
  exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec

theorem forsFinalizeBody_pres : PreservesRoot SegmentS4Finalize.forsFinalizeBody := by
  intro s s'' stmt hmem hexec
  refine SegmentS4Finalize.forsFinalizeBody_mem_cases
    (P := fun stmt => execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "root" = lookupValue s.bindings "root")
    hmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ hexec
  · intro hexec
    exact execStmt_letVar_preserves_lookup _ _ "lastSecret" "root" _ (by decide) hexec
  · intro hexec
    exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · intro hexec
    exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · intro hexec
    exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · intro hexec
    exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · intro hexec
    exact execStmt_forEach_preserves_lookup "i" "root" _ _ _ _ (by decide)
      forsCopyBody_pres hexec
  · intro hexec
    exact execStmt_letVar_preserves_lookup _ _ "forsPk" "root" _ (by decide) hexec

theorem forsFinalizeStep_preserves_root (st : RuntimeState) :
    lookupValue (SegmentS4Finalize.forsFinalizeStep st).bindings "root"
      = lookupValue st.bindings "root" :=
  execStmtList_preserves_lookup "root" SegmentS4Finalize.forsFinalizeBody st
    (SegmentS4Finalize.forsFinalizeStep st) forsFinalizeBody_pres
    (SegmentS4Finalize.execForsFinalize st)

theorem afterFinalize_preserves_root (st : RuntimeState) :
    lookupValue (SegmentCompose.afterFinalize st).bindings "root"
      = lookupValue (SegmentCompose.afterFors st).bindings "root" := by
  unfold SegmentCompose.afterFinalize
  exact forsFinalizeStep_preserves_root (SegmentCompose.afterFors st)

/-! ## 8. The FORS outer-loop frame. -/

theorem forsLeafBody_pres : PreservesRoot SegmentS4Fors.forsLeafBody := by
  intro s s'' stmt hmem hexec
  simp only [SegmentS4Fors.forsLeafBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact execStmt_letVar_preserves_lookup _ _ "treeIdx" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "secretVal" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "leafAdrs" "root" _ (by decide) hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact execStmt_letVar_preserves_lookup _ _ "node" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "pathIdx" "root" _ (by decide) hexec
  · exact execStmt_letVar_preserves_lookup _ _ "authPtr" "root" _ (by decide) hexec
  · exact execStmt_forEach_preserves_lookup "h" "root" _ _ _ _ (by decide)
      forsClimbBody_pres hexec
  · exact execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec

theorem forsLeafStep_preserves_root (st : RuntimeState) :
    lookupValue (SegmentS4Fors.forsLeafStep st).bindings "root"
      = lookupValue st.bindings "root" :=
  execStmtList_preserves_lookup "root" SegmentS4Fors.forsLeafBody st
    (SegmentS4Fors.forsLeafStep st) forsLeafBody_pres (SegmentS4Fors.execForsLeaf st)

theorem afterForsSetup_preserves_root (st : RuntimeState) :
    lookupValue (SegmentCompose.afterForsSetup st).bindings "root"
      = lookupValue (SegmentCompose.afterS3 st).bindings "root" := by
  unfold SegmentCompose.afterForsSetup
  exact SegmentForsSetup.stepForsSetup_preserves_key "root"
    (by decide) (by decide) (by decide) (SegmentCompose.afterS3 st)

theorem afterFors_preserves_root (st : RuntimeState) :
    lookupValue (SegmentCompose.afterFors st).bindings "root"
      = lookupValue (SegmentCompose.afterS3 st).bindings "root" := by
  unfold SegmentCompose.afterFors
  rw [ClimbLoop.foldLoop_preserves_lookup "i" "root" SegmentS4Fors.forsLeafStep
        (by decide) forsLeafStep_preserves_root _ 0 (wordNormalize 6)]
  rw [MemoryKit.lookupValue_bindValue_ne (SegmentCompose.afterForsSetup st).bindings
    "i" "root" (wordNormalize 0) (by decide)]
  exact afterForsSetup_preserves_root st

/-! ## 9. The S3 frame (direct `bindValue` chain) and the full post-S2 chain. -/

theorem stepS3_preserves_root (st : RuntimeState) :
    lookupValue (SegmentS3.stepS3 st).bindings "root" = lookupValue st.bindings "root" := by
  unfold SegmentS3.stepS3
  rw [MemoryKit.lookupValue_bindValue_ne _ "sigBase" "root" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "dVal" "root" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "htIdx" "root" _ (by decide)]

theorem afterS3_preserves_root (st : RuntimeState) :
    lookupValue (SegmentCompose.afterS3 st).bindings "root"
      = lookupValue (SegmentCompose.afterS2 st).bindings "root" := by
  unfold SegmentCompose.afterS3
  exact stepS3_preserves_root (SegmentCompose.afterS2 st)

/-- **`afterLayer_root_eq_afterS2`** — the whole post-S2 portion of the accept
path (S3 forced-zero guard, FORS double loop, finalize compression, seed setup,
and the full Layer-3 hypertree climb) leaves the `"root"` binding exactly at its
post-S2 value.  This is the keccak-free frame backbone of the bounded half of the
residual `hCmp`: `root` is written once in S2 and never touched again, so the
final `currentNode == root` compare reads S2's `pkRoot` word. -/
theorem afterLayer_root_eq_afterS2 (st : RuntimeState) :
    lookupValue (SegmentCompose.afterLayer st).bindings "root"
      = lookupValue (SegmentCompose.afterS2 st).bindings "root" := by
  rw [afterLayer_preserves_root, afterSeed_preserves_root, afterFinalize_preserves_root,
      afterFors_preserves_root, afterS3_preserves_root]

/-- **`afterLayer_root_mkC13State`** — over the frozen Phase-1 entry state, the
`"root"` operand of the final `currentNode == root` compare provably equals the
spec's `pkRoot` word `wordOfHash16 pkRoot`.  Combines the keccak-free post-S2 frame
`afterLayer_root_eq_afterS2` (root unchanged from `afterS2` to `afterLayer`) with
`SegmentS2.s2Step_root_mkC13State` (S2 binds `root` to `wordOfHash16 pkRoot`); since
`afterS2 = s2Step` definitionally, the two compose directly.  This fully closes the
**bounded (right-operand) half** of the residual `hCmp` obligation: the compare's
right side is pinned to the public key's root word.  The open half remains the
`currentNode` data correspondence (the keccak-computed left operand). -/
theorem afterLayer_root_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
        (SegmentCompose.afterLayer
          (MkC13State.mkC13State pkSeed pkRoot message sig)).bindings "root"
      = SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot := by
  rw [afterLayer_root_eq_afterS2]
  exact SegmentS2.s2Step_root_mkC13State pkSeed pkRoot message sig

/-! ## 10. Axiom audit. -/

#print axioms digitSumBody_pres
#print axioms merkleClimbBody_pres
#print axioms prefix11_pres
#print axioms suffix14_pres
#print axioms stepLayer_preserves_root
#print axioms afterLayer_preserves_root
#print axioms stepSeed_preserves_root
#print axioms afterSeed_preserves_root
#print axioms forsFinalizeBody_pres
#print axioms forsFinalizeStep_preserves_root
#print axioms afterFinalize_preserves_root
#print axioms forsLeafBody_pres
#print axioms forsLeafStep_preserves_root
#print axioms afterFors_preserves_root
#print axioms stepS3_preserves_root
#print axioms afterS3_preserves_root
#print axioms afterLayer_root_eq_afterS2
#print axioms afterLayer_root_mkC13State

end SphincsMinusVerifiers.RootFrame
