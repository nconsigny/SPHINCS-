/-
  ClimbMemFrameMerkle — the per-step *memory-frame* for the branchless-Merkle
  climb (`ClimbKit.merkleClimbBody`), the parity-swap companion to the WOTS
  memory-frame in `ClimbMemFrame`.

  Like the WOTS body, the Merkle body's keccak (`keccak 0x00 0x80`, four words)
  is masked by `N_MASK` and reads exactly the scratch window the body writes.
  Unlike WOTS there are *six* binding/memory statements and the two child slots
  are written with a branchless swap: `mstore (0x40 xor s) node` and
  `mstore (0x60 xor s) sibling`, where `s = (idx & 1) << 5`.  When `idx` is even
  `s = 0` so `0x40 ↦ node, 0x60 ↦ sibling`; when odd `s = 0x20` so the writes
  land swapped (`0x40 ↦ sibling, 0x60 ↦ node`).

  `stepMerkle_memory` pins `(stepMerkle …).world.memory` as the three writes
  `0x20 ↦ vadr`, `o5 ↦ vnode`, `o6 ↦ vsib` (the trailing two `assignVar`s — the
  masked keccak and the `idx := parentIdx` update — never touch memory), given
  the resolved offsets/values of each write.  This is the parity-agnostic memory
  frame; the parity case-split into the spec word order is the consumer's job.
  No keccak is evaluated here.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbKit
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbStepSpec
import SphincsMinusVerifiers.SiblingCalldata

namespace SphincsMinusVerifiers.ClimbMemFrameMerkle

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (merkleClimbBody stepMerkle N_MASK)
open SphincsMinusVerifiers.ClimbLoop (foldLoop)
open SphincsMinusVerifiers.ClimbKeccakStep (evalExpr_maskedKeccak_eq_maskN)
open SphincsMinusVerifierSpec.C13Concrete (maskN nMask keccakWords)

set_option maxHeartbeats 2000000

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

/-! ## 1. The branchless-Merkle scratch memory function. -/

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_memory
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).world.memory
      = MemoryKit.memUpdate
          (MemoryKit.memUpdate
            (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode)
          o6 vsib2 := by
  -- statement 1: letVar "sibling"
  have hs1 := MemoryKit.execStmt_letVar_continue st "sibling" _ vsib h1
  set st1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "sibling" vsib } with hst1
  -- statement 2: letVar "parentIdx"
  have hs2 := MemoryKit.execStmt_letVar_continue st1 "parentIdx" _ vpar h2
  set st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "parentIdx" vpar } with hst2
  -- statement 3: mstore 0x20
  have hoff3 : evalExpr [] st2 (.literal 0x20) = some 0x20 := rfl
  have hs3 := MemoryKit.execStmt_mstore_continue st2 (.literal 0x20) _ 0x20 vadr hoff3 h3
  set st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
    with hst3
  -- statement 4: letVar "s"
  have hs4 := MemoryKit.execStmt_letVar_continue st3 "s" _ sval h4
  set st4 : RuntimeState :=
    { st3 with bindings := bindValue st3.bindings "s" sval } with hst4
  -- statement 5: mstore (xor 0x40 s) node
  have hs5 := MemoryKit.execStmt_mstore_continue st4 (.bitXor (.literal 0x40) (.localVar "s")) _
      o5 vnode h5off h5val
  set st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
    with hst5
  -- statement 6: mstore (xor 0x60 s) sibling
  have hs6 := MemoryKit.execStmt_mstore_continue st5 (.bitXor (.literal 0x60) (.localVar "s")) _
      o6 vsib2 h6off h6val
  set st6 : RuntimeState :=
    { st5 with world := { st5.world with memory := MemoryKit.memUpdate st5.world.memory o6 vsib2 } }
    with hst6
  -- statement 7: assignVar nodeVar (and (keccak …) N_MASK) — memory untouched
  set kv : Nat := (Verity.Core.Uint256.and (keccakMemorySlice st6.world.memory (wordNormalize 0x00) (wordNormalize 0x80)) (wordNormalize N_MASK)).val with hkv
  have hval7 : evalExpr [] st6
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some kv := rfl
  have hs7 := assignVar_continue st6 nodeVar _ _ hval7
  set st7 : RuntimeState :=
    { st6 with bindings := bindValue st6.bindings nodeVar kv } with hst7
  -- statement 8: assignVar idxVar parentIdx — memory untouched
  have hval8 : evalExpr [] st7 (.localVar "parentIdx")
      = some (lookupValue st7.bindings "parentIdx") := rfl
  have hs8 := assignVar_continue st7 idxVar _ _ hval8
  -- Thread all eight statements through `stepMerkle`.
  show (match execStmtList [] st
          (ClimbKit.merkleClimbBodyA nodeVar idxVar authPtrVar adrsE) with
        | .continue s' => s' | _ => st).world.memory = _
  show (match execStmtList [] st
          ([ Stmt.letVar "sibling"
              (.bitAnd (.calldataload (.add (.localVar authPtrVar)
                (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
           , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar idxVar))
           , Stmt.mstore (.literal 0x20) adrsE
           , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
           , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar nodeVar)
           , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
           , Stmt.assignVar nodeVar
              (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
           , Stmt.assignVar idxVar (.localVar "parentIdx") ]) with
        | .continue s' => s' | _ => st).world.memory = _
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs3]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs4]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs5]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs6]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs7]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs8]
  -- `execStmtList [] _ [] = .continue _`; the assignVars left memory at st6's.
  show st6.world.memory = _
  rfl

/-- **`stepMerkle_memory`** — the memory of the state after one branchless-Merkle
climb body is the base memory with the three writes `0x20 ↦ vadr`, `o5 ↦ vnode`,
`o6 ↦ vsib` applied in order, where `vadr` is the resolved address word, `o5/o6`
the resolved (parity-xored) child-slot offsets and `vnode/vsib` the node/sibling
values.  The trailing `assignVar nodeVar (keccak…)` and `assignVar idxVar` leave
memory unchanged, so this triple update is exactly the window the body's
`keccak 0x00 0x80` reads.

The resolved quantities are supplied as `evalExpr` hypotheses at the successively
bound states `st1 … st4`; every C13 call site discharges them by `rfl` (the
operands are closed arithmetic over already-bound locals). -/
theorem stepMerkle_memory
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).world.memory
      = MemoryKit.memUpdate
          (MemoryKit.memUpdate
            (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode)
          o6 vsib2 :=
  stepMerkleA_memory nodeVar idxVar authPtrVar (ClimbKit.xmssAdrs adrsBaseVar) st
    vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_node_binding
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hne : nodeVar ≠ idxVar)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = (Verity.Core.Uint256.and
          (keccakMemorySlice
            (MemoryKit.memUpdate
              (MemoryKit.memUpdate
                (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode)
              o6 vsib2)
            (wordNormalize 0x00) (wordNormalize 0x80))
          (wordNormalize N_MASK)).val := by
  -- statement 1: letVar "sibling"
  have hs1 := MemoryKit.execStmt_letVar_continue st "sibling" _ vsib h1
  set st1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "sibling" vsib } with hst1
  -- statement 2: letVar "parentIdx"
  have hs2 := MemoryKit.execStmt_letVar_continue st1 "parentIdx" _ vpar h2
  set st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "parentIdx" vpar } with hst2
  -- statement 3: mstore 0x20
  have hoff3 : evalExpr [] st2 (.literal 0x20) = some 0x20 := rfl
  have hs3 := MemoryKit.execStmt_mstore_continue st2 (.literal 0x20) _ 0x20 vadr hoff3 h3
  set st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
    with hst3
  -- statement 4: letVar "s"
  have hs4 := MemoryKit.execStmt_letVar_continue st3 "s" _ sval h4
  set st4 : RuntimeState :=
    { st3 with bindings := bindValue st3.bindings "s" sval } with hst4
  -- statement 5: mstore (xor 0x40 s) node
  have hs5 := MemoryKit.execStmt_mstore_continue st4 (.bitXor (.literal 0x40) (.localVar "s")) _
      o5 vnode h5off h5val
  set st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
    with hst5
  -- statement 6: mstore (xor 0x60 s) sibling
  have hs6 := MemoryKit.execStmt_mstore_continue st5 (.bitXor (.literal 0x60) (.localVar "s")) _
      o6 vsib2 h6off h6val
  set st6 : RuntimeState :=
    { st5 with world := { st5.world with memory := MemoryKit.memUpdate st5.world.memory o6 vsib2 } }
    with hst6
  -- statement 7: assignVar nodeVar (and (keccak …) N_MASK) — memory untouched
  set kv : Nat := (Verity.Core.Uint256.and (keccakMemorySlice st6.world.memory (wordNormalize 0x00) (wordNormalize 0x80)) (wordNormalize N_MASK)).val with hkv
  have hval7 : evalExpr [] st6
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some kv := rfl
  have hs7 := assignVar_continue st6 nodeVar _ _ hval7
  set st7 : RuntimeState :=
    { st6 with bindings := bindValue st6.bindings nodeVar kv } with hst7
  -- statement 8: assignVar idxVar parentIdx — memory untouched
  have hval8 : evalExpr [] st7 (.localVar "parentIdx")
      = some (lookupValue st7.bindings "parentIdx") := rfl
  have hs8 := assignVar_continue st7 idxVar _ _ hval8
  -- Thread all eight statements through `stepMerkle`, projecting the binding.
  show lookupValue (match execStmtList [] st
          (ClimbKit.merkleClimbBodyA nodeVar idxVar authPtrVar adrsE) with
        | .continue s' => s' | _ => st).bindings nodeVar = _
  show lookupValue (match execStmtList [] st
          ([ Stmt.letVar "sibling"
              (.bitAnd (.calldataload (.add (.localVar authPtrVar)
                (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
           , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar idxVar))
           , Stmt.mstore (.literal 0x20) adrsE
           , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
           , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar nodeVar)
           , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
           , Stmt.assignVar nodeVar
              (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
           , Stmt.assignVar idxVar (.localVar "parentIdx") ]) with
        | .continue s' => s' | _ => st).bindings nodeVar = _
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs3]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs4]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs5]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs6]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs7]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs8]
  -- After stmt 8 the bindings are `bindValue (bindValue st6.bindings nodeVar kv)
  -- idxVar (…)`; reading `nodeVar` skips the idxVar bind (hne) then hits kv.
  show lookupValue
      (bindValue (bindValue st6.bindings nodeVar kv) idxVar
        (lookupValue st7.bindings "parentIdx")) nodeVar = _
  rw [MemoryKit.lookupValue_bindValue_ne _ idxVar nodeVar _ (Ne.symm hne),
      MemoryKit.lookupValue_bindValue_self]

/-- **`stepMerkle_node_binding`** — the binding-projection companion to
`stepMerkle_memory`.  Statement 7 (`assignVar nodeVar (and (keccak 0x00 0x80)
N_MASK)`) sets the `nodeVar` binding to the masked-keccak read of the scratch
window; statement 8 only rebinds `idxVar` (distinct from `nodeVar`, hence the
`hne` hypothesis), so the `nodeVar` binding after `stepMerkle` is exactly that
masked-keccak value over the triple-write memory `0x20 ↦ vadr`, `o5 ↦ vnode`,
`o6 ↦ vsib2`.

Same eight `evalExpr` hypotheses as `stepMerkle_memory` (the operand resolutions
at the successively bound states), discharged by `rfl` at every C13 call site.
This isolates the spec-fold `node'` accumulator component: composed with
`merkle_keccak_value_spec_even/odd` (which rewrite the masked keccak over this
exact memory frame into `maskN (keccakWords [seed, adrs, node, sibling])`), it
gives the new node value of one climb step.  No keccak is evaluated here; pure
state threading.  No `sorry`, no new `axiom`, no `native_decide`. -/
theorem stepMerkle_node_binding
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hne : nodeVar ≠ idxVar)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar
      = (Verity.Core.Uint256.and
          (keccakMemorySlice
            (MemoryKit.memUpdate
              (MemoryKit.memUpdate
                (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode)
              o6 vsib2)
            (wordNormalize 0x00) (wordNormalize 0x80))
          (wordNormalize N_MASK)).val :=
  stepMerkleA_node_binding nodeVar idxVar authPtrVar (ClimbKit.xmssAdrs adrsBaseVar) st
    vsib vpar vadr sval o5 vnode o6 vsib2 hne h1 h2 h3 h4 h5off h5val h6off h6val

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_idx_binding
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hne2 : nodeVar ≠ "parentIdx")
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings idxVar
      = vpar := by
  -- statement 1: letVar "sibling"
  have hs1 := MemoryKit.execStmt_letVar_continue st "sibling" _ vsib h1
  set st1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "sibling" vsib } with hst1
  -- statement 2: letVar "parentIdx"
  have hs2 := MemoryKit.execStmt_letVar_continue st1 "parentIdx" _ vpar h2
  set st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "parentIdx" vpar } with hst2
  -- statement 3: mstore 0x20
  have hoff3 : evalExpr [] st2 (.literal 0x20) = some 0x20 := rfl
  have hs3 := MemoryKit.execStmt_mstore_continue st2 (.literal 0x20) _ 0x20 vadr hoff3 h3
  set st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
    with hst3
  -- statement 4: letVar "s"
  have hs4 := MemoryKit.execStmt_letVar_continue st3 "s" _ sval h4
  set st4 : RuntimeState :=
    { st3 with bindings := bindValue st3.bindings "s" sval } with hst4
  -- statement 5: mstore (xor 0x40 s) node
  have hs5 := MemoryKit.execStmt_mstore_continue st4 (.bitXor (.literal 0x40) (.localVar "s")) _
      o5 vnode h5off h5val
  set st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
    with hst5
  -- statement 6: mstore (xor 0x60 s) sibling
  have hs6 := MemoryKit.execStmt_mstore_continue st5 (.bitXor (.literal 0x60) (.localVar "s")) _
      o6 vsib2 h6off h6val
  set st6 : RuntimeState :=
    { st5 with world := { st5.world with memory := MemoryKit.memUpdate st5.world.memory o6 vsib2 } }
    with hst6
  -- statement 7: assignVar nodeVar (and (keccak …) N_MASK) — memory untouched
  set kv : Nat := (Verity.Core.Uint256.and (keccakMemorySlice st6.world.memory (wordNormalize 0x00) (wordNormalize 0x80)) (wordNormalize N_MASK)).val with hkv
  have hval7 : evalExpr [] st6
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some kv := rfl
  have hs7 := assignVar_continue st6 nodeVar _ _ hval7
  set st7 : RuntimeState :=
    { st6 with bindings := bindValue st6.bindings nodeVar kv } with hst7
  -- The `"parentIdx"` binding survives every later write, so it is still `vpar`.
  have hpval : lookupValue st7.bindings "parentIdx" = vpar := by
    show lookupValue
        (bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
          "parentIdx" vpar) "s" sval) nodeVar kv) "parentIdx" = vpar
    rw [MemoryKit.lookupValue_bindValue_ne _ nodeVar "parentIdx" _ hne2,
        MemoryKit.lookupValue_bindValue_ne _ "s" "parentIdx" _ (by decide),
        MemoryKit.lookupValue_bindValue_self]
  -- statement 8: assignVar idxVar parentIdx — memory untouched
  have hval8 : evalExpr [] st7 (.localVar "parentIdx")
      = some (lookupValue st7.bindings "parentIdx") := rfl
  have hs8 := assignVar_continue st7 idxVar _ _ hval8
  -- Thread all eight statements through `stepMerkle`, projecting the binding.
  show lookupValue (match execStmtList [] st
          (ClimbKit.merkleClimbBodyA nodeVar idxVar authPtrVar adrsE) with
        | .continue s' => s' | _ => st).bindings idxVar = _
  show lookupValue (match execStmtList [] st
          ([ Stmt.letVar "sibling"
              (.bitAnd (.calldataload (.add (.localVar authPtrVar)
                (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
           , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar idxVar))
           , Stmt.mstore (.literal 0x20) adrsE
           , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
           , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar nodeVar)
           , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
           , Stmt.assignVar nodeVar
              (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
           , Stmt.assignVar idxVar (.localVar "parentIdx") ]) with
        | .continue s' => s' | _ => st).bindings idxVar = _
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs3]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs4]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs5]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs6]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs7]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs8]
  -- After stmt 8 the `idxVar` binding is `lookupValue st7.bindings "parentIdx"` = vpar.
  show lookupValue
      (bindValue (bindValue st6.bindings nodeVar kv) idxVar
        (lookupValue st7.bindings "parentIdx")) idxVar = _
  rw [MemoryKit.lookupValue_bindValue_self]
  exact hpval

/-- **`stepMerkle_idx_binding`** — the index-component (`.1`) twin of
`stepMerkle_node_binding`.  Statement 2 binds `"parentIdx"` to `vpar` (the
resolved `idx >>> 1`); statement 8 rebinds `idxVar` to `lookupValue … "parentIdx"`,
which—because the only later writes (statements 3–7) never touch the `"parentIdx"`
binding—is still `vpar`.  Hence the `idxVar` binding after `stepMerkle` is exactly
`vpar`.  The `hne2 : nodeVar ≠ "parentIdx"` hypothesis lets the final read skip the
statement-7 `nodeVar` bind; the `"s"`/`"sibling"` skips are discharged by `decide`.

Same eight `evalExpr` hypotheses as `stepMerkle_memory`/`_node_binding`,
discharged by `rfl` at every C13 call site.  Composed downstream with
`parentIdx_shiftRight` (`idx >>> 1 = idx / 2`) it yields the spec `parentIdx`
accumulator component `mIdx / 2`.  No keccak is evaluated here; pure state
threading.  No `sorry`, no new `axiom`, no `native_decide`. -/
theorem stepMerkle_idx_binding
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hne2 : nodeVar ≠ "parentIdx")
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings idxVar
      = vpar :=
  stepMerkleA_idx_binding nodeVar idxVar authPtrVar (ClimbKit.xmssAdrs adrsBaseVar) st
    vsib vpar vadr sval o5 vnode o6 vsib2 hne2 h1 h2 h3 h4 h5off h5val h6off h6val

/-- **`stepMerkle_sibling_reread_eq`** — the sibling value re-read in statement 6
(`vsib2`, from `mstore (xor 0x60 s) (localVar "sibling")`) is structurally the
value *loaded* in statement 1 (`vsib`, from `letVar "sibling" (and (cdload …)
N_MASK)`).  Statements 2–5 bind only `"parentIdx"` / `"s"` (distinct keys) and
mutate only memory, so the `"sibling"` binding is untouched between the load and
the re-read; hence `evalExpr (localVar "sibling")` at the statement-6 state is
`some vsib`, forcing `vsib2 = vsib`.

This collapses the per-step interface's separate `vsib2` variable onto the loaded
`vsib`: it lets an eventual `hstep` discharge the sibling data-correspondence
`hsib : wordNormalize vsib2 = wordOfHash16 auth[h]` directly against the calldata
load `h1` (the masked word at `authPtr + 16·h`), with no intermediate scratch-word
residue.  Pure binding read, no keccak, no memory reasoning.  Axiom-clean. -/
theorem stepMerkle_sibling_reread_eq
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode vsib2 : Nat)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    vsib2 = vsib := by
  have hread : evalExpr []
      { st with
        world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
        bindings :=
          bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
      (.localVar "sibling")
      = some (lookupValue
          (bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval)
          "sibling") := rfl
  rw [MemoryKit.lookupValue_bindValue_ne _ "s" "sibling" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "sibling" _ (by decide),
      MemoryKit.lookupValue_bindValue_self] at hread
  exact (Option.some.inj (hread.symm.trans h6val)).symm

/-- **`stepMerkle_node_read_eq`** — the climbing node value read in statement 5
(`vnode`, from `mstore (xor 0x40 s) (localVar nodeVar)`) is exactly the *entry*
binding of `nodeVar`.  Statements 1–4 bind only `"sibling"` / `"parentIdx"` / `"s"`
(all distinct from `nodeVar`, the surrounding `forEach`'s carried accumulator name)
and mutate only memory, so `lookupValue st.bindings nodeVar` is untouched up to the
statement-5 read.

Together with `stepMerkle_sibling_reread_eq` this pins down the *inductive* half of
the per-step interface: where the sibling/seed words reduce to a fresh bytes-surface
obligation each step, the node input carries **no** bytes or keccak content of its
own — the step's `hnode : wordNormalize vnode = node` discharges directly against
`wordNormalize (lookupValue st.bindings nodeVar) = node`, i.e. the climb-fold
invariant's node component as established by the *previous* step's output.  This is
what makes the climb a genuine induction (`foldLoop_invariant`) rather than a
per-step recomputation.  Pure binding read, no keccak, no memory reasoning.
Axiom-clean. -/
theorem stepMerkle_node_read_eq
    (nodeVar : String) (st : RuntimeState) (vsib vpar vadr sval vnode : Nat)
    (hns : nodeVar ≠ "s") (hnp : nodeVar ≠ "parentIdx") (hnsib : nodeVar ≠ "sibling")
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode) :
    lookupValue st.bindings nodeVar = vnode := by
  have hread : evalExpr []
      { st with
        world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
        bindings :=
          bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
      (.localVar nodeVar)
      = some (lookupValue
          (bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval)
          nodeVar) := rfl
  rw [MemoryKit.lookupValue_bindValue_ne _ "s" nodeVar _ (Ne.symm hns),
      MemoryKit.lookupValue_bindValue_ne _ "parentIdx" nodeVar _ (Ne.symm hnp),
      MemoryKit.lookupValue_bindValue_ne _ "sibling" nodeVar _ (Ne.symm hnsib)] at hread
  exact Option.some.inj (hread.symm.trans h5val)

/-! ## 2. Parity resolution into the `hmem`-shaped 4-word read. -/

/-- The four-word keccak preimage of one branchless-Merkle climb step, in spec
word order, as a function of the climb parity.  Cell `0x00` is the untouched base
word (the materialised seed); `0x20` the address word; cells `0x40`/`0x60` carry
`[node, sibling]` when the index is even (`s = 0`) and `[sibling, node]` when odd
(`s = 0x20`), exactly the branchless swap.  The written words are read back
through `.val`, hence the `wordNormalize`. -/
def merkleScratchWords (base : Nat → Verity.Core.Uint256)
    (vadr vnode vsib : Nat) (odd : Bool) : List Nat :=
  if odd then
    [ (base 0x00).val, wordNormalize vadr, wordNormalize vsib, wordNormalize vnode ]
  else
    [ (base 0x00).val, wordNormalize vadr, wordNormalize vnode, wordNormalize vsib ]

/-- **Even-parity hmem** (`s = 0`, so `o5 = 0x40`, `o6 = 0x60`): the triple-write
memory of `stepMerkle_memory` read in the `∀ i < 4, (memory (0 + 32*i)).val = ws[i]`
shape that `ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN` consumes, with
`ws = merkleScratchWords base vadr vnode vsib false`. -/
theorem merkle_hmem_even (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat) :
    ∀ i, (h : i < (merkleScratchWords base vadr vnode vsib false).length) →
      ((MemoryKit.memUpdate
          (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x40 vnode)
          0x60 vsib) (0 + 32 * i)).val
        = (merkleScratchWords base vadr vnode vsib false)[i] := by
  intro i hi
  simp only [merkleScratchWords, Bool.false_eq_true, if_false,
    List.length_cons, List.length_nil] at hi ⊢
  match i, hi with
  | 0, _ =>
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    rfl
  | 1, _ =>
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    show (MemoryKit.memUpdate base 0x20 vadr 0x20).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | 2, _ =>
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    show (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x40 vnode 0x40).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | 3, _ =>
    show (MemoryKit.memUpdate
            (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x40 vnode)
            0x60 vsib 0x60).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | (n + 4), hbad => exact absurd hbad (by omega)

/-- **Odd-parity hmem** (`s = 0x20`, so `o5 = 0x60`, `o6 = 0x40`): the swapped
triple-write memory read in the same `∀ i < 4` shape, with
`ws = merkleScratchWords base vadr vnode vsib true`. -/
theorem merkle_hmem_odd (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat) :
    ∀ i, (h : i < (merkleScratchWords base vadr vnode vsib true).length) →
      ((MemoryKit.memUpdate
          (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x60 vnode)
          0x40 vsib) (0 + 32 * i)).val
        = (merkleScratchWords base vadr vnode vsib true)[i] := by
  intro i hi
  simp only [merkleScratchWords, if_true, List.length_cons, List.length_nil] at hi ⊢
  match i, hi with
  | 0, _ =>
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    rfl
  | 1, _ =>
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide),
        MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    show (MemoryKit.memUpdate base 0x20 vadr 0x20).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | 2, _ =>
    show (MemoryKit.memUpdate
            (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x60 vnode)
            0x40 vsib 0x40).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | 3, _ =>
    rw [MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
    show (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x60 vnode 0x60).val = _
    rw [MemoryKit.memUpdate_val_same]
    rfl
  | (n + 4), hbad => exact absurd hbad (by omega)

/-! ## 3. Value-level closure: masked 4-word keccak = spec `maskN (keccakWords ws)`. -/

/-- The Merkle analogue of `ClimbMemFrame.wots_maskedKeccak_value`: a masked
`keccak256 0x00 0x80` over four scratch words (memory `[0x00, 0x80)`) evaluates to
the spec value `maskN (keccakWords ws)`. Specialization of
`evalExpr_maskedKeccak_eq_maskN` to `ws.length = 4` (so `32*4 = 0x80`). -/
theorem merkle_maskedKeccak_value
    (st : RuntimeState) (ws : List Nat) (hlen : ws.length = 4)
    (hmem : ∀ i, (h : i < ws.length) → (st.world.memory (0 + 32 * i)).val = ws[i]) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (maskN (keccakWords ws)) := by
  have hsz : 32 * ws.length = 0x80 := by rw [hlen]
  have hoff : wordNormalize (0x00 : Nat) = 0x00 := by
    rw [wordNormalize_eq_mod]; exact Nat.zero_mod _
  have hszlt : 32 * ws.length < 2 ^ 256 := by rw [hsz]; decide
  have key := evalExpr_maskedKeccak_eq_maskN st 0x00 ws hoff hszlt hmem
  rw [hsz] at key
  rw [show (N_MASK : Nat) = nMask from rfl]
  exact key

/-- Even-parity closure: feed the even triple-write memory shape into the value
lemma via `merkle_hmem_even`. -/
theorem merkle_keccak_value_even
    (st : RuntimeState) (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat)
    (hmemeq : st.world.memory =
      MemoryKit.memUpdate
        (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x40 vnode)
        0x60 vsib) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (maskN (keccakWords (merkleScratchWords base vadr vnode vsib false))) := by
  apply merkle_maskedKeccak_value st (merkleScratchWords base vadr vnode vsib false) rfl
  intro i hi
  rw [hmemeq]
  exact merkle_hmem_even base vadr vnode vsib i hi

/-- Odd-parity closure: feed the swapped triple-write memory shape into the value
lemma via `merkle_hmem_odd`. -/
theorem merkle_keccak_value_odd
    (st : RuntimeState) (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat)
    (hmemeq : st.world.memory =
      MemoryKit.memUpdate
        (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x60 vnode)
        0x40 vsib) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (maskN (keccakWords (merkleScratchWords base vadr vnode vsib true))) := by
  apply merkle_maskedKeccak_value st (merkleScratchWords base vadr vnode vsib true) rfl
  intro i hi
  rw [hmemeq]
  exact merkle_hmem_odd base vadr vnode vsib i hi

/-! ## 4. Per-step value = spec step-function preimage.

These connect the interpreter scratch list `merkleScratchWords …` to the spec's
`xmssClimb`/`forsClimb` keccak preimage `[seed, adrs, node, sibling]` (even) /
`[seed, adrs, sibling, node]` (odd) under per-component value equalities.  They are
the algebraic half of the Phase-3b data correspondence for one Merkle climb step:
the interpreter's masked-keccak read equals the spec body's `node'` whenever the
resolved seed/address/node/sibling values match.  Pure list rewrites — no keccak
semantics, no new axioms. -/

/-- Interpreter even-parity scratch list = spec even-branch preimage. -/
theorem merkleScratchWords_eq_spec_even
    (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat)
    (seed adrs node sibling : Nat)
    (hseed : (base 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib = sibling) :
    merkleScratchWords base vadr vnode vsib false = [seed, adrs, node, sibling] := by
  simp only [merkleScratchWords, Bool.false_eq_true, if_false, hseed, hadr, hnode, hsib]

/-- Interpreter odd-parity scratch list = spec odd-branch (swapped) preimage. -/
theorem merkleScratchWords_eq_spec_odd
    (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat)
    (seed adrs node sibling : Nat)
    (hseed : (base 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib = sibling) :
    merkleScratchWords base vadr vnode vsib true = [seed, adrs, sibling, node] := by
  simp only [merkleScratchWords, if_true, hseed, hadr, hnode, hsib]

/-- **Even-parity per-step value = spec preimage**: the interpreter's masked-keccak
read after an even-index Merkle climb step equals `maskN (keccakWords [seed, adrs,
node, sibling])` — exactly the spec `xmssClimb`/`forsClimb` even-branch `node'`. -/
theorem merkle_keccak_value_spec_even
    (st : RuntimeState) (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat)
    (seed adrs node sibling : Nat)
    (hmemeq : st.world.memory =
      MemoryKit.memUpdate
        (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x40 vnode)
        0x60 vsib)
    (hseed : (base 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib = sibling) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (maskN (keccakWords [seed, adrs, node, sibling])) := by
  rw [← merkleScratchWords_eq_spec_even base vadr vnode vsib seed adrs node sibling
        hseed hadr hnode hsib]
  exact merkle_keccak_value_even st base vadr vnode vsib hmemeq

/-- **Odd-parity per-step value = spec preimage**: the interpreter's masked-keccak
read after an odd-index Merkle climb step equals `maskN (keccakWords [seed, adrs,
sibling, node])` — exactly the spec odd-branch `node'`. -/
theorem merkle_keccak_value_spec_odd
    (st : RuntimeState) (base : Nat → Verity.Core.Uint256) (vadr vnode vsib : Nat)
    (seed adrs node sibling : Nat)
    (hmemeq : st.world.memory =
      MemoryKit.memUpdate
        (MemoryKit.memUpdate (MemoryKit.memUpdate base 0x20 vadr) 0x60 vnode)
        0x40 vsib)
    (hseed : (base 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib = sibling) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (maskN (keccakWords [seed, adrs, sibling, node])) := by
  rw [← merkleScratchWords_eq_spec_odd base vadr vnode vsib seed adrs node sibling
        hseed hadr hnode hsib]
  exact merkle_keccak_value_odd st base vadr vnode vsib hmemeq

/-! ### Per-step node *output* = spec `node'`, composed.

These weld `stepMerkle_node_binding` (the binding-projection: the `nodeVar`
output of one climb step is the masked keccak over the triple-write window) to
`merkle_keccak_value_spec_even/odd` (that masked keccak = `maskN (keccakWords
…)`), giving the new node directly as the spec body's `node'` — `maskN
(keccakWords [seed, adrs, node, sibling])` (even) / `[…, sibling, node]` (odd).
The parity is supplied as the resolved child-slot offsets `o5/o6`
(`merkle_offsets_even/odd` discharge them from `idx & 1`).  This is the exact
per-step accumulator-component the `foldLoop` relation `R` carries; no keccak is
unfolded, no new axioms. -/

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_node_value_spec_even
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrs node sibling : Nat)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x40) (ho6 : o6 = 0x60)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = sibling)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = maskN (keccakWords [seed, adrs, node, sibling]) := by
  rw [stepMerkleA_node_binding nodeVar idxVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 hne h1 h2 h3 h4 h5off h5val h6off h6val,
      ho5, ho6]
  -- The masked-keccak *value* over the even triple-write window equals the spec
  -- preimage's `node'`, via the `evalExpr`-level `merkle_keccak_value_spec_even`.
  set st' : RuntimeState :=
    { st with world := { st.world with memory :=
        (MemoryKit.memUpdate
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) 0x40 vnode)
          0x60 vsib2) } } with hst'
  have hval : evalExpr [] st'
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (Verity.Core.Uint256.and
          (keccakMemorySlice st'.world.memory (wordNormalize 0x00) (wordNormalize 0x80))
          (wordNormalize N_MASK)).val := rfl
  have hspec := merkle_keccak_value_spec_even st' st.world.memory vadr vnode vsib2
      seed adrs node sibling rfl hseed hadr hnode hsib
  exact Option.some.inj (hval.symm.trans hspec)

/-- **Even-parity per-step node output = spec `node'`.** -/
theorem stepMerkle_node_value_spec_even
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrs node sibling : Nat)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x40) (ho6 : o6 = 0x60)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = sibling)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar
      = maskN (keccakWords [seed, adrs, node, sibling]) := by
  rw [stepMerkle_node_binding nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 hne h1 h2 h3 h4 h5off h5val h6off h6val,
      ho5, ho6]
  -- The masked-keccak *value* over the even triple-write window equals the spec
  -- preimage's `node'`, via the `evalExpr`-level `merkle_keccak_value_spec_even`.
  set st' : RuntimeState :=
    { st with world := { st.world with memory :=
        (MemoryKit.memUpdate
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) 0x40 vnode)
          0x60 vsib2) } } with hst'
  have hval : evalExpr [] st'
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (Verity.Core.Uint256.and
          (keccakMemorySlice st'.world.memory (wordNormalize 0x00) (wordNormalize 0x80))
          (wordNormalize N_MASK)).val := rfl
  have hspec := merkle_keccak_value_spec_even st' st.world.memory vadr vnode vsib2
      seed adrs node sibling rfl hseed hadr hnode hsib
  exact Option.some.inj (hval.symm.trans hspec)

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_node_value_spec_odd
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrs node sibling : Nat)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x60) (ho6 : o6 = 0x40)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = sibling)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = maskN (keccakWords [seed, adrs, sibling, node]) := by
  rw [stepMerkleA_node_binding nodeVar idxVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 hne h1 h2 h3 h4 h5off h5val h6off h6val,
      ho5, ho6]
  set st' : RuntimeState :=
    { st with world := { st.world with memory :=
        (MemoryKit.memUpdate
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) 0x60 vnode)
          0x40 vsib2) } } with hst'
  have hval : evalExpr [] st'
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (Verity.Core.Uint256.and
          (keccakMemorySlice st'.world.memory (wordNormalize 0x00) (wordNormalize 0x80))
          (wordNormalize N_MASK)).val := rfl
  have hspec := merkle_keccak_value_spec_odd st' st.world.memory vadr vnode vsib2
      seed adrs node sibling rfl hseed hadr hnode hsib
  exact Option.some.inj (hval.symm.trans hspec)

/-- **Odd-parity per-step node output = spec `node'`** (swapped child slots). -/
theorem stepMerkle_node_value_spec_odd
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrs node sibling : Nat)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x60) (ho6 : o6 = 0x40)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrs)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = sibling)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar
      = maskN (keccakWords [seed, adrs, sibling, node]) := by
  rw [stepMerkle_node_binding nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 hne h1 h2 h3 h4 h5off h5val h6off h6val,
      ho5, ho6]
  set st' : RuntimeState :=
    { st with world := { st.world with memory :=
        (MemoryKit.memUpdate
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) 0x60 vnode)
          0x40 vsib2) } } with hst'
  have hval : evalExpr [] st'
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some (Verity.Core.Uint256.and
          (keccakMemorySlice st'.world.memory (wordNormalize 0x00) (wordNormalize 0x80))
          (wordNormalize N_MASK)).val := rfl
  have hspec := merkle_keccak_value_spec_odd st' st.world.memory vadr vnode vsib2
      seed adrs node sibling rfl hseed hadr hnode hsib
  exact Option.some.inj (hval.symm.trans hspec)

/-! ## 5. Spec-side normalization: `xmssClimb` is a `specFold`.

`foldLoop_invariant` concludes about `ClimbLoop.specFold`; the spec's hypertree
climb is phrased as the recursive `xmssClimb`.  This bridges the two: `xmssClimb`
over `fuel` iterations equals the second projection of a `specFold` whose step is
`merkleSpecStep` (one Merkle climb step on the `(mIdx, node)` accumulator, with the
loop index carrying the tree height `h`).  Pure structural induction on `fuel` — no
keccak semantics, no new axioms.  With this, the eventual
`foldLoop_invariant` instantiation rewrites directly into `xmssClimb`, hence into
`xmssRootFromSigC13`. -/

open SphincsMinusVerifierSpec.C13Concrete (wordOfHash16 xmssClimb)

/-- One spec Merkle-climb step on the `(mIdx, node)` accumulator: read the sibling
from `auth[h]`, halve the index, build the height-`h+1` address word, and hash with
the parity-correct child order.  Verbatim image of the `xmssClimb` loop body. -/
def merkleSpecStep (seed treeAdrs : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) :
    Nat → (Nat × Nat) → (Nat × Nat)
  | h, (mIdx, node) =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := mIdx / 2
    let adrs := treeAdrs ||| ((h + 1) <<< 32) ||| parentIdx
    let node' :=
      if mIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    (parentIdx, node')

theorem xmssClimb_eq_specFold
    (seed treeAdrs : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) :
    ∀ (fuel h mIdx node : Nat),
      xmssClimb seed treeAdrs fuel h mIdx node auth
        = (ClimbLoop.specFold (merkleSpecStep seed treeAdrs auth) (mIdx, node) h fuel).2
  | 0, h, mIdx, node => by
      simp only [xmssClimb, ClimbLoop.specFold_zero]
  | fuel + 1, h, mIdx, node => by
      simp only [xmssClimb, ClimbLoop.specFold_succ, merkleSpecStep]
      exact xmssClimb_eq_specFold seed treeAdrs auth fuel (h + 1) (mIdx / 2) _

/-- One spec FORS-climb step on the `(pathIdx, node)` accumulator: per the FIPS
205 layout the per-level address is `adrsForsNode t0 l0 i h parentIdx` (the
`i <<< (18 - h)` tree-number fold makes it `h`-dependent, so the FORS climb is
*not* `merkleSpecStep` at a fixed base; the `t0`/`l0` digits are the
hypertree-leaf field split carried by the hoisted `forsBase`).  Verbatim image
of the `forsClimb` loop body. -/
def forsSpecStep (seed i t0 l0 : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) :
    Nat → (Nat × Nat) → (Nat × Nat)
  | h, (pathIdx, node) =>
    let sibling := wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)
    let parentIdx := pathIdx / 2
    let adrs := SphincsMinusVerifierSpec.C13Concrete.adrsForsNode t0 l0 i h parentIdx
    let node' :=
      if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
      else maskN (keccakWords [seed, adrs, sibling, node])
    (parentIdx, node')

theorem forsClimb_eq_specFold
    (seed i t0 l0 : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) :
    ∀ (fuel h pathIdx node : Nat),
      SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i t0 l0 fuel h pathIdx node auth
        = (ClimbLoop.specFold (forsSpecStep seed i t0 l0 auth) (pathIdx, node) h fuel).2
  | 0, h, pathIdx, node => by
      simp only [SphincsMinusVerifierSpec.C13Concrete.forsClimb, ClimbLoop.specFold_zero]
  | fuel + 1, h, pathIdx, node => by
      simp only [SphincsMinusVerifierSpec.C13Concrete.forsClimb,
        ClimbLoop.specFold_succ, forsSpecStep]
      exact forsClimb_eq_specFold seed i t0 l0 auth fuel (h + 1) (pathIdx / 2) _


/-! ### Per-step node output = the spec step function `merkleSpecStep`.

The final weld of the per-step node algebra: the interpreter step's `nodeVar`
output equals the *second component* of `merkleSpecStep` — the spec's one-step
`(mIdx, node) ↦ (parentIdx, node')` transformer that `xmssClimb_eq_specFold`
folds.  The spec dispatches `node'` on `mIdx % 2`; the interpreter dispatches on
the resolved child-slot offsets `o5/o6` (parity of `idx & 1`).  Given the parity
hypothesis `hpar` (matching the two — established by `merkle_offsets_even/odd`
from the same index) plus the spec-shaped value equalities (`adrs = treeAdrs |||
((h+1)<<<32) ||| (mIdx/2)`, `sibling = wordOfHash16 auth[h]`), both reduce to the
same `maskN (keccakWords …)`.  This is precisely the `node` half of one
`foldLoop` step relation `R`, now phrased against `merkleSpecStep` itself.  No
keccak unfolded, no new axioms. -/

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_node_eq_specStep_even
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrsW h node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x40) (ho6 : o6 = 0x60)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrsW)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)]) :=
  stepMerkleA_node_value_spec_even nodeVar idxVar authPtrVar adrsE st
    vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW node (wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    hne ho5 ho6 hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val

/-- **Even index ⇒ interpreter node output = `(merkleSpecStep …).2`.** -/
theorem stepMerkle_node_eq_specStep_even
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x40) (ho6 : o6 = 0x60)
    (hpar : mIdx % 2 = 0)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).2 := by
  rw [stepMerkle_node_value_spec_even nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2
        seed (treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2) node
        (wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
        hne ho5 ho6 hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val]
  simp only [merkleSpecStep, hpar, Nat.reduceBEq, if_true]

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_node_eq_specStep_odd
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrsW h node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x60) (ho6 : o6 = 0x40)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrsW)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node]) :=
  stepMerkleA_node_value_spec_odd nodeVar idxVar authPtrVar adrsE st
    vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW node (wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    hne ho5 ho6 hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val

/-- **Odd index ⇒ interpreter node output = `(merkleSpecStep …).2`** (swap). -/
theorem stepMerkle_node_eq_specStep_odd
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (ho5 : o5 = 0x60) (ho6 : o6 = 0x40)
    (hpar : mIdx % 2 = 1)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).2 := by
  rw [stepMerkle_node_value_spec_odd nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2
        seed (treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2) node
        (wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
        hne ho5 ho6 hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val]
  simp only [merkleSpecStep, hpar, Nat.reduceBEq, Bool.false_eq_true, if_false]

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_idx_eq_specStep
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (mIdx : Nat)
    (hne2 : nodeVar ≠ "parentIdx")
    (hvpar : vpar = mIdx / 2)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings idxVar
      = mIdx / 2 := by
  rw [stepMerkleA_idx_binding nodeVar idxVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2
        hne2 h1 h2 h3 h4 h5off h5val h6off h6val]
  exact hvpar

/-- **Interpreter index output = `(merkleSpecStep …).1`.**  The `.1` companion of
`stepMerkle_node_eq_specStep_even/odd`.  Unlike the node output, the first
component of `merkleSpecStep` — `parentIdx = mIdx / 2` — does *not* dispatch on
index parity, so a single lemma covers both cases with no `hpar` hypothesis: only
the index data-correspondence `vpar = mIdx / 2` (the resolved `idx >>> 1`, via
`parentIdx_shiftRight`, equals the spec's `mIdx / 2`).  Composed with the node
lemma this is the *complete* per-step pair `(stepMerkle …) ↦ merkleSpecStep …`
that `foldLoop_invariant`'s `hstep` carries.  Axiom-clean; no keccak unfolded. -/
theorem stepMerkle_idx_eq_specStep
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne2 : nodeVar ≠ "parentIdx")
    (hvpar : vpar = mIdx / 2)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings idxVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).1 := by
  rw [stepMerkle_idx_binding nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2
        hne2 h1 h2 h3 h4 h5off h5val h6off h6val]
  simp only [merkleSpecStep]
  exact hvpar

/-! ### Combined per-step accumulator equality = `merkleSpecStep`.

The full per-step weld: the *pair* of interpreter outputs
`(idxVar binding, nodeVar binding)` after `stepMerkle` equals `merkleSpecStep`
applied to the accumulator `(mIdx, node)`.  This is the exact shape
`foldLoop_invariant`'s `hstep` consumes (the spec step on the accumulator α =
`Nat × Nat`).  Assembled by `Prod.ext` from the two component lemmas
(`stepMerkle_idx_eq_specStep` for `.1`, `stepMerkle_node_eq_specStep_even/odd` for
`.2`), so it inherits exactly their hypotheses: parity (`hpar` + matching offsets
`o5/o6`) and the per-component data-correspondence equalities
(`hseed/hadr/hnode/hsib/hvpar`).  Everything except those value equalities is now
discharged; what an eventual `hstep` must still supply is precisely the
data-correspondence each iteration (blocker #20).  Axiom-clean; no keccak. -/

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_eq_merkleSpecStep_even
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrsW h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (ho5 : o5 = 0x40) (ho6 : o6 = 0x60) (hpar : mIdx % 2 = 0)
    (hvpar : vpar = mIdx / 2)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrsW)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    (lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings idxVar,
        lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar)
      = (mIdx / 2,
          if mIdx % 2 == 0 then
            maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
          else
            maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
  have hnode' : lookupValue
        (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = (if mIdx % 2 == 0 then
          maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
        else
          maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
    rw [stepMerkleA_node_eq_specStep_even nodeVar idxVar authPtrVar adrsE st
          vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW h node auth
          hne ho5 ho6 hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val]
    simp only [hpar, Nat.reduceBEq, if_true]
  exact Prod.ext
    (stepMerkleA_idx_eq_specStep nodeVar idxVar authPtrVar adrsE st
      vsib vpar vadr sval o5 vnode o6 vsib2 mIdx
      hne2 hvpar h1 h2 h3 h4 h5off h5val h6off h6val)
    hnode'

/-- **Even index ⇒ interpreter accumulator pair = `merkleSpecStep …`.** -/
theorem stepMerkle_eq_merkleSpecStep_even
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (ho5 : o5 = 0x40) (ho6 : o6 = 0x60) (hpar : mIdx % 2 = 0)
    (hvpar : vpar = mIdx / 2)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings idxVar,
        lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar)
      = merkleSpecStep seed treeAdrs auth h (mIdx, node) :=
  Prod.ext
    (stepMerkle_idx_eq_specStep nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hne2 hvpar h1 h2 h3 h4 h5off h5val h6off h6val)
    (stepMerkle_node_eq_specStep_even nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hne ho5 ho6 hpar hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val)

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_eq_merkleSpecStep_odd
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrsW h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (ho5 : o5 = 0x60) (ho6 : o6 = 0x40) (hpar : mIdx % 2 = 1)
    (hvpar : vpar = mIdx / 2)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrsW)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    (lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings idxVar,
        lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar)
      = (mIdx / 2,
          if mIdx % 2 == 0 then
            maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
          else
            maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
  have hnode' : lookupValue
        (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = (if mIdx % 2 == 0 then
          maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
        else
          maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
    rw [stepMerkleA_node_eq_specStep_odd nodeVar idxVar authPtrVar adrsE st
          vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW h node auth
          hne ho5 ho6 hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val]
    simp only [hpar, Nat.reduceBEq, Bool.false_eq_true, if_false]
  exact Prod.ext
    (stepMerkleA_idx_eq_specStep nodeVar idxVar authPtrVar adrsE st
      vsib vpar vadr sval o5 vnode o6 vsib2 mIdx
      hne2 hvpar h1 h2 h3 h4 h5off h5val h6off h6val)
    hnode'

/-- **Odd index ⇒ interpreter accumulator pair = `merkleSpecStep …`** (swap). -/
theorem stepMerkle_eq_merkleSpecStep_odd
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (ho5 : o5 = 0x60) (ho6 : o6 = 0x40) (hpar : mIdx % 2 = 1)
    (hvpar : vpar = mIdx / 2)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings idxVar,
        lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar)
      = merkleSpecStep seed treeAdrs auth h (mIdx, node) :=
  Prod.ext
    (stepMerkle_idx_eq_specStep nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hne2 hvpar h1 h2 h3 h4 h5off h5val h6off h6val)
    (stepMerkle_node_eq_specStep_odd nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hne ho5 ho6 hpar hseed hadr hnode hsib h1 h2 h3 h4 h5off h5val h6off h6val)

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_eq_merkleSpecStep
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrsW h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = adrsW)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    (lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings idxVar,
        lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar)
      = (mIdx / 2,
          if mIdx % 2 == 0 then
            maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
          else
            maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
  rcases hparOff with ⟨hpar, ho5, ho6⟩ | ⟨hpar, ho5, ho6⟩
  · exact stepMerkleA_eq_merkleSpecStep_even nodeVar idxVar authPtrVar adrsE st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW h mIdx node auth
      hne hne2 ho5 ho6 hpar hvpar hseed hadr hnode hsib
      h1 h2 h3 h4 h5off h5val h6off h6val
  · exact stepMerkleA_eq_merkleSpecStep_odd nodeVar idxVar authPtrVar adrsE st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW h mIdx node auth
      hne hne2 ho5 ho6 hpar hvpar hseed hadr hnode hsib
      h1 h2 h3 h4 h5off h5val h6off h6val

/-- **Parity-unified per-step accumulator equality.**  A single lemma covering
both index parities, dispatched by the disjunction `hparOff`, which couples the
index parity to the resolved child-slot offsets:

  `(mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60) ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40)`.

This is exactly the coherence `merkle_offsets_even/odd` establish from the index
parity, so an eventual `hstep` supplies one disjunction rather than pre-committing
to an even/odd branch.  `Or.elim` routes to `stepMerkle_eq_merkleSpecStep_even/odd`.
Axiom-clean; no keccak unfolded. -/
theorem stepMerkle_eq_merkleSpecStep
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings idxVar,
        lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings nodeVar)
      = merkleSpecStep seed treeAdrs auth h (mIdx, node) := by
  rcases hparOff with ⟨hpar, ho5, ho6⟩ | ⟨hpar, ho5, ho6⟩
  · exact stepMerkle_eq_merkleSpecStep_even nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hne hne2 ho5 ho6 hpar hvpar hseed hadr hnode hsib
      h1 h2 h3 h4 h5off h5val h6off h6val
  · exact stepMerkle_eq_merkleSpecStep_odd nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hne hne2 ho5 ho6 hpar hvpar hseed hadr hnode hsib
      h1 h2 h3 h4 h5off h5val h6off h6val

/-! ## 6. Branchless-swap offset arithmetic.

The interpreter computes `parentIdx = idx >>> 1` and the swap selector
`s = (idx &&& 1) <<< 5`, then writes `mstore (0x40 ^^^ s)` / `mstore (0x60 ^^^ s)`.
These pure-`Nat` facts resolve those bit ops into the spec's `mIdx / 2` and the
even/odd child-slot offsets, closing the gap between `stepMerkle_memory`'s
parity-agnostic `o5/o6` and the `merkle_*_even/odd` consumers.  Mathlib
`Nat.and_one_is_mod` / `Nat.shiftRight_eq_div_pow`; no new axioms. -/

/-- `idx >>> 1 = idx / 2` — the interpreter's `parentIdx` equals the spec's. -/
theorem parentIdx_shiftRight (n : Nat) : n >>> 1 = n / 2 := by
  rw [Nat.shiftRight_eq_div_pow, pow_one]

/-- **`wordNormalize` is identity on a masked word.**  `maskN w = w &&& nMask ≤
nMask < 2^256 = evmModulus`, so the interpreter's outer `mod 2^256` is a no-op on
any masked sibling/node value.  Lets the data correspondence drop the
`wordNormalize` wrapper when the interpreter-side value is a `maskN`. -/
theorem wordNormalize_maskN (w : Nat) : wordNormalize (maskN w) = maskN w := by
  rw [wordNormalize_eq_mod]
  apply Nat.mod_eq_of_lt
  calc maskN w ≤ nMask := by unfold maskN; exact Nat.and_le_right
    _ < Compiler.Constants.evmModulus := by decide

/-- **`wordNormalize` is identity on `wordOfHash16`.**  `wordOfHash16 b =
(baToNatBE b % 2^128) * 2^128 < 2^128 * 2^128 = 2^256 = evmModulus`, so the
spec-side 16-byte hash word is already EVM-normalized.  Together with
`wordNormalize_maskN` this strips `wordNormalize` from *both* sides of the sibling
data-correspondence `wordNormalize vsib2 = wordOfHash16 auth[h]`. -/
theorem wordNormalize_wordOfHash16 (b : SphincsMinusVerifierSpec.Bytes) :
    wordNormalize (wordOfHash16 b) = wordOfHash16 b := by
  rw [wordNormalize_eq_mod]
  apply Nat.mod_eq_of_lt
  show SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 b < Compiler.Constants.evmModulus
  unfold SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 Compiler.Constants.evmModulus
  calc _ < 2 ^ 128 * 2 ^ 128 :=
        mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) (by positivity)
    _ = 2 ^ 256 := by rw [← pow_add]

/-- **The single bytes-surface obligation for the sibling word.**  This names
exactly what the raw-calldata model must establish for one Merkle-climb step: the
masked 16-byte word loaded from calldata at `authPtr + 16·h` (here abstracted as
`maskN cdval`, the value statement 1 binds to `"sibling"`) equals the spec's
`wordOfHash16` of the abstract auth-path node `b = auth[h]`.  Everything *around*
this predicate — the binding bookkeeping, the `wordNormalize` wrappers, the keccak
preimage layout — is already discharged axiom-free by the lemmas above; this
`Prop` is the lone residue that depends on the `bytes`-calldata surface model
(`sig.length`/`sig.offset` → `read16` → `wordOfHash16`), i.e. the genuinely
open MODEL-EXEC-BRIDGE / blocker #20 piece.  Isolating it as a named predicate
keeps the climb correspondence honest: the step lemma below is *conditional* on
exactly this fact and nothing more. -/
def SiblingBytesCorrespondence (cdval : Nat) (b : SphincsMinusVerifierSpec.Bytes) : Prop :=
  maskN cdval = wordOfHash16 b

/-- **`sibling_correspondence_of_bytes`** — the sibling data-correspondence that an
eventual `hstep` must supply (`wordNormalize vsib2 = wordOfHash16 auth[h]`,
spec-side `wordOfHash16` already `wordNormalize`-stable) is reduced, with *no*
remaining structural residue, to the single bytes-surface obligation
`SiblingBytesCorrespondence`.  The reduction chains three already-proved
axiom-clean facts: `stepMerkle_sibling_reread_eq` (`vsib2 = vsib`, the statement-6
re-read collapses onto the statement-1 load), `hload` (`vsib = maskN cdval`, the
shape of statement 1's masked calldata load), and `wordNormalize_maskN`
(`wordNormalize (maskN _) = maskN _`).  What is left is precisely
`maskN cdval = wordOfHash16 b` — the lone calldata-model fact.  Axiom-clean;
keeps the bridge honest by exposing exactly the open dependency. -/
theorem sibling_correspondence_of_bytes
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode vsib2 cdval : Nat)
    (b : SphincsMinusVerifierSpec.Bytes)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2)
    (hload : vsib = maskN cdval)
    (hbytes : SiblingBytesCorrespondence cdval b) :
    wordNormalize vsib2 = wordOfHash16 b := by
  rw [stepMerkle_sibling_reread_eq st vsib vpar vadr sval o5 vnode vsib2 h6val, hload,
      wordNormalize_maskN]
  exact hbytes

/-- **`seed_correspondence_of_bytes`** — the climb's materialised seed word (the
keccak-preimage cell `0x00`, carried into `merkleScratchWords` as `(base 0x00).val`
with *no* `wordNormalize` wrapper, since a `Uint256.val` is already `< 2^256`)
matches the spec's `seed = wordOfHash16 pk.pkSeed`, *given only* the same
bytes-surface obligation shape the sibling uses — `SiblingBytesCorrespondence cdval
b` (`maskN cdval = wordOfHash16 b`) — plus the ordinary frame-materialisation fact
that the cell holds the masked calldata `pkSeed` word (`seedWord.val = maskN
cdval`).  Unlike the sibling there is no per-step re-read to collapse (the seed is
materialised once at frame setup, not rebound each iteration), so the reduction is
a bare transitivity.  This consolidates a *second* of the three climb hash words
onto the single `SiblingBytesCorrespondence` predicate: both the seed cell and the
per-step sibling now reduce to one identical calldata-model obligation shape, the
lone blocker-#20 residue.  Axiom-clean. -/
theorem seed_correspondence_of_bytes
    (seedWord : Verity.Core.Uint256) (cdval : Nat) (b : SphincsMinusVerifierSpec.Bytes)
    (hframe : seedWord.val = maskN cdval)
    (hbytes : SiblingBytesCorrespondence cdval b) :
    seedWord.val = wordOfHash16 b :=
  hframe.trans hbytes

/-- **`Uint256.or` reads back as bare `Nat.lor`.**  `Uint256.or a b = ofNat
(a.val ||| b.val)` and `a.val ||| b.val < 2^256` (both operands are `< 2^256` by
the `Uint256` invariant, and `Nat.or_lt_two_pow` lifts that to the disjunction), so
the `ofNat` truncation is the identity — no `wordNormalize`/mod residue survives.
This is the EVM-word analogue of `wordNormalize_maskN`, for the bitwise-OR ADRS
assembly rather than the masked hash load. -/
theorem uint256_or_val (a b : Verity.Core.Uint256) :
    (Verity.Core.Uint256.or a b).val = a.val ||| b.val := by
  show (Verity.Core.Uint256.ofNat (Nat.lor a.val b.val)).val = a.val ||| b.val
  rw [Verity.Core.Uint256.val_ofNat]
  apply Nat.mod_eq_of_lt
  show Nat.lor a.val b.val < Verity.Core.Uint256.modulus
  rw [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  exact Nat.or_lt_two_pow a.isLt b.isLt

/-- **`merkle_address_word`** — the interpreter's statement-3 address word
`mstore 0x20 (adrsBase | ((h+1)<<32 | parentIdx))` reads back, with *no*
`wordNormalize`/mod residue, as the spec word-order disjunction
`adrsBase.val | (h+1)<<32 | parentIdx`.  The source nests the OR as
`adrsBase | (sh | parentIdx)` while the spec `merkleSpecStep` builds
`treeAdrs ||| ((h+1)<<<32) ||| parentIdx = (treeAdrs ||| sh) ||| parentIdx`
(left-assoc); `Nat.lor_assoc` reconciles the two groupings.  Unlike the
sibling/seed hash words, this is pure ADRS *integer* arithmetic with **no keccak
and no calldata-bytes dependency** — so once the frame facts `adrsBase.val =
treeAdrs` and `sh = (h+1)<<<32` are in hand (ordinary materialisation bookkeeping,
not blocker #20) the address correspondence closes completely.  Axiom-clean. -/
theorem merkle_address_word (adrsBase sh parentIdx : Verity.Core.Uint256) :
    (Verity.Core.Uint256.or adrsBase (Verity.Core.Uint256.or sh parentIdx)).val
      = adrsBase.val ||| sh.val ||| parentIdx.val := by
  rw [uint256_or_val, uint256_or_val, Nat.lor_assoc]

/-- **`MerkleClimbRel`** — the frozen per-step climb-invariant contract, in exactly
the shape `ClimbLoop.foldLoop_invariant` demands for its relational argument
`R : RuntimeState → α → Prop` with `α = Nat × Nat = (mIdx, node)`.  A runtime state
`s` is related to the abstract climb accumulator `a = (mIdx, node)` iff its index
binding holds `mIdx` exactly and its node binding holds a word that EVM-normalises
to the abstract `node`.  Freezing this as a *named* predicate is the Phase-1
interface deliverable: every climb step lemma below (`stepMerkle_idx_eq_specStep`,
`stepMerkle_node_read_eq`, `stepMerkle_eq_merkleSpecStep`) is phrased so that, once
the per-step sibling bytes obligation (`SiblingBytesCorrespondence`) and the frame
facts are in hand, the `foldLoop_invariant` `hstep` for *this* `R` — advancing it by
one `merkleSpecStep` — is what discharges the climb.  The lone open dependency
remains the per-iteration `SiblingBytesCorrespondence` (blocker #20); the index and
node components are pure binding bookkeeping, already axiom-clean above. -/
def MerkleClimbRel (nodeVar idxVar : String) (s : RuntimeState) (a : Nat × Nat) : Prop :=
  lookupValue s.bindings idxVar = a.1 ∧
  wordNormalize (lookupValue s.bindings nodeVar) = a.2

/-- Build the climb relation from its index and node components. -/
theorem MerkleClimbRel.intro {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (hidx : lookupValue s.bindings idxVar = a.1)
    (hnode : wordNormalize (lookupValue s.bindings nodeVar) = a.2) :
    MerkleClimbRel nodeVar idxVar s a := ⟨hidx, hnode⟩

/-- Index component of the climb relation: the `idxVar` binding is the spec `mIdx`. -/
theorem MerkleClimbRel.idx {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbRel nodeVar idxVar s a) : lookupValue s.bindings idxVar = a.1 := h.1

/-- Node component of the climb relation: the `nodeVar` binding normalises to the
spec `node`. -/
theorem MerkleClimbRel.node {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbRel nodeVar idxVar s a) :
    wordNormalize (lookupValue s.bindings nodeVar) = a.2 := h.2

/-- **`merkleSpecStep_snd_normalized`** — the spec node output `merkleSpecStep.2`
(`node'`) is `wordNormalize`-stable: in *both* parity branches it is
`maskN (keccakWords …)`, and `wordNormalize (maskN _) = maskN _`
(`wordNormalize_maskN`).  This is the bridge that lifts the existing *raw* per-step
node equality `stepMerkle_node_eq_specStep_even/odd`
(`lookupValue (stepMerkle …).bindings nodeVar = merkleSpecStep.2`) into the
`wordNormalize`-wrapped shape the frozen `MerkleClimbRel.node` component demands
(`wordNormalize (lookupValue … nodeVar) = a.2`): apply `wordNormalize` to both sides
of the raw equality, then rewrite the right side by this lemma.  Pure spec-side
arithmetic, no interpreter state, no keccak unfolded.  Axiom-clean. -/
theorem merkleSpecStep_snd_normalized (seed treeAdrs : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) (h : Nat) (a : Nat × Nat) :
    wordNormalize (merkleSpecStep seed treeAdrs auth h a).2
      = (merkleSpecStep seed treeAdrs auth h a).2 := by
  obtain ⟨mIdx, node⟩ := a
  simp only [merkleSpecStep]
  split <;> exact wordNormalize_maskN _

/-- The spec FORS node output `forsSpecStep.2` is `wordNormalize`-stable (both
parity branches are `maskN`-masked). -/
theorem forsSpecStep_snd_normalized (seed i t0 l0 : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) (h : Nat) (a : Nat × Nat) :
    wordNormalize (forsSpecStep seed i t0 l0 auth h a).2
      = (forsSpecStep seed i t0 l0 auth h a).2 := by
  obtain ⟨pathIdx, node⟩ := a
  simp only [forsSpecStep]
  split <;> exact wordNormalize_maskN _

/-- Exact-node variant of `MerkleClimbRel`.  It carries the raw node binding,
not only its EVM normalization, plus the fact that the spec node is already
normalized.  This is useful for consumers that must prove exact data-cell
equality after a Merkle climb. -/
def MerkleClimbRawRel (nodeVar idxVar : String) (s : RuntimeState) (a : Nat × Nat) : Prop :=
  lookupValue s.bindings idxVar = a.1 ∧
  lookupValue s.bindings nodeVar = a.2 ∧
  wordNormalize a.2 = a.2

theorem MerkleClimbRawRel.intro {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (hidx : lookupValue s.bindings idxVar = a.1)
    (hnode : lookupValue s.bindings nodeVar = a.2)
    (hnorm : wordNormalize a.2 = a.2) :
    MerkleClimbRawRel nodeVar idxVar s a := ⟨hidx, hnode, hnorm⟩

theorem MerkleClimbRawRel.idx {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbRawRel nodeVar idxVar s a) :
    lookupValue s.bindings idxVar = a.1 := h.1

theorem MerkleClimbRawRel.node {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbRawRel nodeVar idxVar s a) :
    lookupValue s.bindings nodeVar = a.2 := h.2.1

theorem MerkleClimbRawRel.node_norm {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbRawRel nodeVar idxVar s a) :
    wordNormalize a.2 = a.2 := h.2.2

/-- Forget the exact-node component down to the existing normalized climb relation. -/
theorem MerkleClimbRawRel.toRel {nodeVar idxVar : String} {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbRawRel nodeVar idxVar s a) :
    MerkleClimbRel nodeVar idxVar s a := by
  refine MerkleClimbRel.intro h.idx ?_
  rw [h.node]
  exact h.node_norm

/-- Raw-pair welding lemma: the existing per-step pair equality gives an exact
node relation, and `merkleSpecStep_snd_normalized` supplies the normalization
component for the next iteration. -/
theorem MerkleClimbRawRel_of_pair (nodeVar idxVar : String) (s' : RuntimeState)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hpair : (lookupValue s'.bindings idxVar, lookupValue s'.bindings nodeVar)
              = merkleSpecStep seed treeAdrs auth h (mIdx, node)) :
    MerkleClimbRawRel nodeVar idxVar s' (merkleSpecStep seed treeAdrs auth h (mIdx, node)) := by
  have hidx : lookupValue s'.bindings idxVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).1 := (Prod.ext_iff.mp hpair).1
  have hn : lookupValue s'.bindings nodeVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).2 := (Prod.ext_iff.mp hpair).2
  exact MerkleClimbRawRel.intro hidx hn
    (merkleSpecStep_snd_normalized seed treeAdrs auth h (mIdx, node))

/-- **`MerkleClimbRel_of_pair`** — repackages the per-step accumulator *pair*
equality produced by `stepMerkle_eq_merkleSpecStep`
(`(lookupValue … idxVar, lookupValue … nodeVar) = merkleSpecStep …`) into the
frozen relational `Post_i` shape `MerkleClimbRel nodeVar idxVar s' (merkleSpecStep
…)`.  The index component is the literal `.1` of the pair equality; the node
component lifts the raw `.2` equality through `wordNormalize` and closes the
resulting `wordNormalize merkleSpecStep.2 = merkleSpecStep.2` by
`merkleSpecStep_snd_normalized`.  This is the welding lemma that lets the existing
control-flow step lemma feed `ClimbLoop.foldLoop_invariant` directly: once the
hypotheses of `stepMerkle_eq_merkleSpecStep` are in hand (all bookkeeping plus the
single open per-step data bundle `hseed/hadr/hsib`, the latter bottoming out at one
`SiblingBytesCorrespondence`), the `foldLoop` `hstep` for `MerkleClimbRel` follows.
Pure repackaging, no interpreter re-evaluation.  Axiom-clean. -/
theorem MerkleClimbRel_of_pair (nodeVar idxVar : String) (s' : RuntimeState)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hpair : (lookupValue s'.bindings idxVar, lookupValue s'.bindings nodeVar)
              = merkleSpecStep seed treeAdrs auth h (mIdx, node)) :
    MerkleClimbRel nodeVar idxVar s' (merkleSpecStep seed treeAdrs auth h (mIdx, node)) := by
  have hidx : lookupValue s'.bindings idxVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).1 := (Prod.ext_iff.mp hpair).1
  have hn : lookupValue s'.bindings nodeVar
      = (merkleSpecStep seed treeAdrs auth h (mIdx, node)).2 := (Prod.ext_iff.mp hpair).2
  refine MerkleClimbRel.intro hidx ?_
  rw [hn]
  exact merkleSpecStep_snd_normalized seed treeAdrs auth h (mIdx, node)

/-- **`StepDataObligations`** — the single named bundle of the *only* open per-step
data hypotheses of `stepMerkle_eq_merkleSpecStep`, for one Merkle-climb index `h`.
Everything else that lemma consumes is either pure bookkeeping (`hne`, `hparOff`,
`hvpar`, the `h1..h6` evalExpr facts — all discharged from the frame lemmas) or the
*inductive* node input `hnode` (carried by `MerkleClimbRel`, not a data fact).  What
remains genuinely open — the part the calldata model must eventually supply — is
exactly three facts:

* `seed`  — the seed cell `mem[0x00]` holds the pk-seed word;
* `adr`   — the assembled ADRS word equals the FIPS `tree ‖ (h+1) ‖ parentIdx` layout
            (its value core is *already closed* by `merkle_address_word`; what stays
            open is only that the frame's `vadr` equals that pure-arithmetic word);
* `sib`   — the reread sibling word equals `wordOfHash16 auth[h]` (this is the one
            that bottoms out at `SiblingBytesCorrespondence` = blocker #20).

Bundling them collapses the whole open surface of a single climb step into one
`Prop`, so a future `MerkleClimbRel`-preservation lemma can be stated conditional on
exactly `StepDataObligations` (plus the inductive `MerkleClimbRel` and bookkeeping),
making blocker #20 a single named hypothesis rather than three scattered ones. -/
def StepDataObligations (st : RuntimeState) (vadr vsib2 seed treeAdrs h mIdx : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) : Prop :=
  (st.world.memory 0x00).val = seed
  ∧ wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2
  ∧ wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)

/-- Constructor for `StepDataObligations` from its three component facts. -/
theorem StepDataObligations.intro {st : RuntimeState} {vadr vsib2 seed treeAdrs h mIdx : Nat}
    {auth : List SphincsMinusVerifierSpec.Bytes}
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (hsib : wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)) :
    StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth := ⟨hseed, hadr, hsib⟩

/-- Seed-cell projection of `StepDataObligations`. -/
theorem StepDataObligations.seed {st : RuntimeState} {vadr vsib2 seed treeAdrs h mIdx : Nat}
    {auth : List SphincsMinusVerifierSpec.Bytes}
    (h' : StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth) :
    (st.world.memory 0x00).val = seed := h'.1

/-- ADRS-word projection of `StepDataObligations`. -/
theorem StepDataObligations.adr {st : RuntimeState} {vadr vsib2 seed treeAdrs h mIdx : Nat}
    {auth : List SphincsMinusVerifierSpec.Bytes}
    (h' : StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth) :
    wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2 := h'.2.1

/-- Sibling-word projection of `StepDataObligations` — the one bottoming out at
`SiblingBytesCorrespondence` (blocker #20). -/
theorem StepDataObligations.sib {st : RuntimeState} {vadr vsib2 seed treeAdrs h mIdx : Nat}
    {auth : List SphincsMinusVerifierSpec.Bytes}
    (h' : StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth) :
    wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩) := h'.2.2

/-- Address-word-parametric (`adrsW`) generalization of `StepDataObligations`:
the assembled ADRS word equals an arbitrary spec address word, rather than the
hard-wired XMSS `treeAdrs ||| ((h+1) <<< 32) ||| mIdx / 2` layout.  Used by the
`adrsE`-generalized step lemmas so the FIPS FORS climb (whose per-level address
is `adrsForsNode …`, an `h`-dependent word) can reuse them. -/
def StepDataObligationsW (st : RuntimeState) (vadr vsib2 seed adrsW h mIdx : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) : Prop :=
  (st.world.memory 0x00).val = seed
  ∧ wordNormalize vadr = adrsW
  ∧ wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)

/-- **`MerkleClimbData`** — the *index-indexed* data-obligation family for the whole
Merkle climb, in exactly the `D : Nat → Prop` shape `ClimbLoop.foldLoop_invariant_cond`
ranges its range hypothesis over.  For a calldata reader `cdAt : Nat → Nat` (the masked
auth-path word the interpreter loads at climb height `idx`, i.e. the value at
`authPtr + 16·idx`), height `idx`'s obligation is exactly the sibling bytes-surface
fact `SiblingBytesCorrespondence (cdAt idx) auth[idx]` — the lone open per-iteration
data fact that `StepDataObligations.sib` bottoms out at (blocker #20).  Naming the
whole climb's data surface as this single `Nat`-indexed family is what lets the
conditional engine collapse blocker #20 for the entire loop into one *range*
hypothesis `∀ i ∈ [0, h), MerkleClimbData auth cdAt i` — precisely what the calldata
model must eventually supply, and nothing more. -/
def MerkleClimbData (auth : List SphincsMinusVerifierSpec.Bytes)
    (cdAt : Nat → Nat) (idx : Nat) : Prop :=
  SiblingBytesCorrespondence (cdAt idx) ((auth[idx]?).getD ⟨#[]⟩)

/-- `MerkleClimbData` unfolds to the masked-word ↦ `wordOfHash16` equality at one
height — the per-iteration kernel of blocker #20. -/
theorem MerkleClimbData_iff (auth : List SphincsMinusVerifierSpec.Bytes)
    (cdAt : Nat → Nat) (idx : Nat) :
    MerkleClimbData auth cdAt idx
      ↔ maskN (cdAt idx) = wordOfHash16 ((auth[idx]?).getD ⟨#[]⟩) := Iff.rfl

/-- **`merkleClimbData_of_frozenCalldata`** — discharges the lone open per-height
datum `MerkleClimbData auth cdAt h` (the fully-reduced blocker #20) against the
*frozen* `mkC13State` calldata image, given the two facts the calldata model
supplies: (`hcd`) this height's raw calldata word `cdAt h` is the frozen word read
at signature byte offset `sigDataOffset + sOff`, and (`hauth`) the spec parse fact
that auth node `h` is the 16-byte read at that same offset.  Closes via the
general-offset masked-read correspondence
`SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen` — `maskN` is definitionally
`Nat.land · N_MASK`, so no residue survives.  Works for *any* `sOff` (in particular
the XMSS auth offsets `≡ 4` / `≡ 8 mod 16`, not just 16-aligned reads).
Axiom-clean. -/
theorem merkleClimbData_of_frozenCalldata
    (pkSeed pkRoot message sig : ByteArray)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat) (h sOff : Nat)
    (hcd : cdAt h = Compiler.Proofs.YulGeneration.calldataloadWord 0
              (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
              (SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff))
    (hauth : (auth[h]?).getD ⟨#[]⟩
              = SphincsMinusVerifierSpec.C13Concrete.read16 sig sOff) :
    MerkleClimbData auth cdAt h := by
  rw [MerkleClimbData_iff, hcd, hauth]
  exact SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
    pkSeed pkRoot message sig sOff

/-- **`climb_calldata_read_eq_frozen`** (the `hcd` supplier) — the climb body's raw
per-height calldata read `calldataload(authPtr + (h << 4))` (statement 1 of
`merkleClimbBody`, before the `N_MASK`) resolves, over any state carrying the frozen
C13 calldata image and `selector = 0`, to the frozen word
`calldataloadWord 0 (headWords … ++ bytesToWords sig) (sigDataOffset + sOff)`.

This is the model-side `hcd` premise of `merkleClimbData_of_frozenCalldata` with
`cdAt h` taken to be this raw read.  It is *pure interpreter evaluation* over the
concrete `merkleClimbBody` offset expression — `evalExpr_siblingOffset` threads
`shl`→`add` to the bare byte offset `ap + h<<4`, the `.calldataload` evaluator turns
that into `calldataloadWord state.selector state.world.calldata _`, and the frozen
state's `selector`/`calldata` plus the offset-arithmetic hypothesis
`ap + h<<4 = sigDataOffset + sOff` pin the result.  No `execC13`, no bridge axiom: the
binding values `ap`/`hval` and the offset equation are supplied as hypotheses (the
segment-execution bookkeeping that establishes `merklePtr = sigBase + authOff` etc.
lives in the climb-loop wiring, not here). -/
theorem climb_calldata_read_eq_frozen
    (st : RuntimeState) (authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (ap hval sOff : Nat)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : evalExpr [] st (.localVar authPtrVar) = some ap)
    (hh : evalExpr [] st (.localVar "h") = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256) (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff) :
    evalExpr [] st
        (.calldataload (.add (.localVar authPtrVar) (.shl (.literal 4) (.localVar "h"))))
      = some (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
          (SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff)) := by
  have hoffset := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_siblingOffset
    st (.localVar authPtrVar) (.localVar "h") ap hval hap hh haplt hhlt hshift hsum
  have hcdl : evalExpr [] st
      (.calldataload (.add (.localVar authPtrVar) (.shl (.literal 4) (.localVar "h"))))
        = some (Compiler.Proofs.YulGeneration.calldataloadWord st.selector st.world.calldata
            (ap + hval <<< 4)) := by
    show (evalExpr [] st (.add (.localVar authPtrVar) (.shl (.literal 4) (.localVar "h")))).bind
          (fun ro => some (Compiler.Proofs.YulGeneration.calldataloadWord
            st.selector st.world.calldata ro)) = _
    rw [hoffset]; rfl
  rw [hcdl, hsel, hcd, hoff]

/-- A non-prefix calldata word read (`offset ≥ 4`) is a genuine 256-bit value: both
non-trivial branches of `calldataloadWord` end in `_ % evmModulus`, hence `< 2^256`.
This is the `cw < 2^256` side-condition `ClimbKeccakStep.evalExpr_maskedCalldata`
demands.  Axiom-clean. -/
theorem calldataloadWord_lt_of_ge4 (sel : Nat) (cd : List Nat) (off : Nat)
    (hoff : 4 ≤ off) :
    Compiler.Proofs.YulGeneration.calldataloadWord sel cd off < 2 ^ 256 := by
  have hmod : (0 : Nat) < Compiler.Constants.evmModulus := by
    show 0 < 2 ^ 256; positivity
  unfold Compiler.Proofs.YulGeneration.calldataloadWord
  rw [if_neg (by omega : ¬ off = 0), if_neg (by omega : ¬ off < 4)]
  show (if _ then _ else _) < Compiler.Constants.evmModulus
  split
  · exact Nat.mod_lt _ hmod
  · exact Nat.mod_lt _ hmod

/-- **`merkle_sibling_read_frozen`** — discharges the per-step **h1** frame fact (the
masked sibling `calldataload` read of `MerkleClimbRel_step`) for the *frozen* C13
calldata image, pinning its witnessed value.  Over any state carrying the frozen
image (`hsel`/`hcd`), with `authPtr`/`h` resolved (`hap`/`hh`) and the offset
arithmetic `ap + h<<4 = sigDataOffset + sOff` (`hoff`, `sOff ≥ 4-aligned via `hoff4`),
statement 1's `and(calldataload(authPtr + 16·h), N_MASK)` evaluates to
`maskN (calldataloadWord 0 image (sigDataOffset + sOff))`.

Composes `climb_calldata_read_eq_frozen` (the raw read resolves to the frozen word)
with `ClimbKeccakStep.evalExpr_maskedCalldata` (the literal-`N_MASK` `bitAnd` is
`maskN`).  This is exactly the `h1` shape `MerkleClimbRel_step` consumes, with the
existential `vsib` now pinned to `maskN (frozen word)` — which `MerkleClimbData`
(blocker #20) further equates to `wordOfHash16 auth[h]`.  No `execC13`, no bridge
axiom; pure interpreter evaluation over the concrete climb body.  Axiom-clean. -/
theorem merkle_sibling_read_frozen
    (st : RuntimeState) (authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray) (ap hval sOff : Nat)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
            = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
                ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (hap : evalExpr [] st (.localVar authPtrVar) = some ap)
    (hh : evalExpr [] st (.localVar "h") = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256) (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4 = SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff)
    (hoff4 : 4 ≤ SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff) :
    evalExpr [] st
        (.bitAnd (.calldataload (.add (.localVar authPtrVar)
          (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
      = some (maskN (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
          (SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff))) := by
  have hraw := climb_calldata_read_eq_frozen st authPtrVar pkSeed pkRoot message sig
    ap hval sOff hsel hcd hap hh haplt hhlt hshift hsum hoff
  have hbound := calldataloadWord_lt_of_ge4 0
    (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
      ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
    (SphincsMinusVerifiers.MkC13State.sigDataOffset + sOff) hoff4
  have hmasked := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedCalldata st
    (.add (.localVar authPtrVar) (.shl (.literal 4) (.localVar "h"))) _ hraw hbound
  exact hmasked

/-! ## 6a. STEP-1: the frame-carrying climb invariant `MerkleClimbFrame`.

`MerkleClimbRel` (idx + node bindings only) is too weak to be self-preserved by one
`stepMerkle` step: `MerkleClimbRel_step` consumes eight `evalExpr` frame facts
(`h1..h6`) plus `hparOff`/`hvpar`/`hnode`/`StepDataObligations`, which need the
state to additionally fix the `adrsBaseVar`/`authPtrVar` bindings, the seed cell
`mem[0x00]`, the calldata selector/image, and a battery of name-distinctness
inequalities — *none* carried by `MerkleClimbRel`.  `MerkleClimbFrame` bundles
`MerkleClimbRel` together with exactly that static frame, so that (a) it projects
back to `MerkleClimbRel` (`MerkleClimbFrame.toRel`), and (b) it is preserved by one
`stepMerkle` step (the step writes only `mem 0x20/0x40/0x60` and rebinds
`sibling/parentIdx/s/nodeVar/idxVar`, leaving `selector`, `calldata`, `mem[0x00]`,
and the `adrsBaseVar`/`authPtrVar` bindings untouched).  This is the STEP-1
interface deliverable; the preservation proof (STEP-2) and the loop lift (STEP-3)
build on it. -/
def MerkleClimbFrame
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (s : RuntimeState) (a : Nat × Nat) : Prop :=
  MerkleClimbRel nodeVar idxVar s a
  ∧ lookupValue s.bindings adrsBaseVar = treeAdrs
  ∧ lookupValue s.bindings authPtrVar = merklePtr
  ∧ (s.world.memory 0x00).val = seed
  ∧ s.selector = 0
  ∧ s.world.calldata
      = SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
          ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig
  ∧ nodeVar ≠ idxVar ∧ nodeVar ≠ "parentIdx" ∧ nodeVar ≠ "sibling" ∧ nodeVar ≠ "s"
      ∧ nodeVar ≠ "h"
  ∧ idxVar ≠ "sibling" ∧ idxVar ≠ "parentIdx" ∧ idxVar ≠ "s" ∧ idxVar ≠ "h"
  ∧ adrsBaseVar ≠ "sibling" ∧ adrsBaseVar ≠ "parentIdx" ∧ adrsBaseVar ≠ "s"
      ∧ adrsBaseVar ≠ nodeVar ∧ adrsBaseVar ≠ idxVar ∧ adrsBaseVar ≠ "h"
  ∧ authPtrVar ≠ "sibling" ∧ authPtrVar ≠ "parentIdx" ∧ authPtrVar ≠ "s"
      ∧ authPtrVar ≠ nodeVar ∧ authPtrVar ≠ idxVar ∧ authPtrVar ≠ "h"

/-- **`MerkleClimbFrame.toRel`** — the STEP-1 projection: the frame-carrying
invariant implies the bare `MerkleClimbRel` (its first conjunct).  This is what lets
a frame-threaded loop lift feed the node/idx-only consumers (`xmssClimb_model_node`'s
`.node` projection) unchanged. -/
theorem MerkleClimbFrame.toRel
    {nodeVar idxVar adrsBaseVar authPtrVar : String}
    {pkSeed pkRoot message sig : ByteArray}
    {seed treeAdrs merklePtr : Nat}
    {s : RuntimeState} {a : Nat × Nat}
    (h : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
          pkSeed pkRoot message sig seed treeAdrs merklePtr s a) :
    MerkleClimbRel nodeVar idxVar s a := h.1

/-- **`xmss_climb_data_range`** — the P1+P2 composition: the *whole-loop* range
hypothesis `∀ i ∈ [0,11), MerkleClimbData lsig.authPath cdAt i` that
`ClimbLoop.foldLoop_invariant_cond` consumes for one XMSS hypertree climb, with `cdAt`
the model's per-height frozen calldata read `calldataloadWord 0 (image) (merklePtr+16·i)`.

Each height is discharged by `merkleClimbData_of_frozenCalldata`, fed (hcd) the
offset-arithmetic identity `merklePtr + 16·i = sigDataOffset + (1952+868·layer+692+16·i)`
— `merklePtr = sigBase + authOff` from the layer's straight-line setup — and (hauth) the
pure-spec auth-path extraction `parseSignatureC13_layer_authPath_getElem?`.  This
collapses the per-step "blocker #20" datum for the *entire* XMSS climb loop into the
single parsed-signature + frozen-calldata + `merklePtr`-value premise; it neither runs
`execC13` nor touches any bridge axiom.  (The `merklePtr` value itself is fixed by the
`stepLayer` segment trace, supplied here as `hmp`.) -/
theorem xmss_climb_data_range
    (pkSeed pkRoot message sig : ByteArray)
    (v : SphincsMinusVerifierSpec.Variant) (s : SphincsMinusVerifierSpec.Signature)
    (lsig : SphincsMinusVerifierSpec.XmssLayerSig) (layer merklePtr : Nat)
    (hparse : SphincsMinusVerifierSpec.C13Concrete.parseSignatureC13 v sig = some s)
    (hlayer : layer < 2)
    (hlsig : s.layers[layer]? = some lsig)
    (hmp : merklePtr
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (1952 + 868 * layer + 692)) :
    ∀ i, i < 11 → MerkleClimbData lsig.authPath
        (fun j => Compiler.Proofs.YulGeneration.calldataloadWord 0
          (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
          (merklePtr + 16 * j)) i := by
  intro i hi
  refine merkleClimbData_of_frozenCalldata pkSeed pkRoot message sig lsig.authPath
    _ i (1952 + 868 * layer + 692 + 16 * i) ?_ ?_
  · show Compiler.Proofs.YulGeneration.calldataloadWord 0 _ (merklePtr + 16 * i)
        = Compiler.Proofs.YulGeneration.calldataloadWord 0 _
            (SphincsMinusVerifiers.MkC13State.sigDataOffset + (1952 + 868 * layer + 692 + 16 * i))
    rw [hmp]; congr 1; omega
  · rw [SphincsMinusVerifierSpec.C13Concrete.parseSignatureC13_layer_authPath_getElem?
        hparse hlayer hlsig hi]
    rfl

/-- **`fors_climb_data_range`** — the FORS analog of `xmss_climb_data_range`.  The FORS
outer loop's inner Merkle climb (`SegmentS4Fors.forsLeafBody`, the
`forEach "h" (u 19) (merkleClimbBody "node" "pathIdx" "forsBase" "authPtr")`) is the
*same* `merkleClimbBody`, so its per-height datum is again `MerkleClimbData`.  For FORS
tree `t < 6` the body sets `authPtr = sigBase + (128 + 304·t)`, hence the per-height read
sits at `sigDataOffset + (128 + 304·t + 16·h)`; (hcd) is the offset-arithmetic identity
and (hauth) the FORS auth-path extraction `parseSignatureC13_fors_authPath_getElem?`.
This supplies the whole-inner-loop range hypothesis `∀ h ∈ [0,19), MerkleClimbData tAuth
cdAt h` that the FORS inner climb's `foldLoop_invariant_cond` consumes, one FORS tree at a
time.  No `execC13`, no bridge axiom. -/
theorem fors_climb_data_range
    (pkSeed pkRoot message sig : ByteArray)
    (v : SphincsMinusVerifierSpec.Variant) (s : SphincsMinusVerifierSpec.Signature)
    (tAuth : List SphincsMinusVerifierSpec.Bytes) (t authPtr : Nat)
    (hparse : SphincsMinusVerifierSpec.C13Concrete.parseSignatureC13 v sig = some s)
    (ht : t < 6)
    (htAuth : s.fors.authPath[t]? = some tAuth)
    (hap : authPtr
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t)) :
    ∀ h, h < 19 → MerkleClimbData tAuth
        (fun j => Compiler.Proofs.YulGeneration.calldataloadWord 0
          (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
          (authPtr + 16 * j)) h := by
  intro h hh
  refine merkleClimbData_of_frozenCalldata pkSeed pkRoot message sig tAuth
    _ h (128 + 304 * t + 16 * h) ?_ ?_
  · show Compiler.Proofs.YulGeneration.calldataloadWord 0 _ (authPtr + 16 * h)
        = Compiler.Proofs.YulGeneration.calldataloadWord 0 _
            (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t + 16 * h))
    rw [hap]; congr 1; omega
  · rw [SphincsMinusVerifierSpec.C13Concrete.parseSignatureC13_fors_authPath_getElem?
        hparse ht htAuth hh]
    rfl

/-- `getD`-shaped FORS data range, matching the named C13 normal-root expression
`(s.fors.authPath[t]?).getD []`.  This removes the caller-side need to first
extract `some tAuth` from the parsed auth-path list. -/
theorem fors_climb_data_range_getD
    (pkSeed pkRoot message sig : ByteArray)
    (v : SphincsMinusVerifierSpec.Variant) (s : SphincsMinusVerifierSpec.Signature)
    (t authPtr : Nat)
    (hparse : SphincsMinusVerifierSpec.C13Concrete.parseSignatureC13 v sig = some s)
    (ht : t < 6)
    (hap : authPtr
            = SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t)) :
    ∀ h, h < 19 → MerkleClimbData ((s.fors.authPath[t]?).getD [])
        (fun j => Compiler.Proofs.YulGeneration.calldataloadWord 0
          (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
            ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
          (authPtr + 16 * j)) h := by
  intro h hh
  refine merkleClimbData_of_frozenCalldata pkSeed pkRoot message sig
    ((s.fors.authPath[t]?).getD []) _ h (128 + 304 * t + 16 * h) ?_ ?_
  · show Compiler.Proofs.YulGeneration.calldataloadWord 0 _ (authPtr + 16 * h)
        = Compiler.Proofs.YulGeneration.calldataloadWord 0 _
            (SphincsMinusVerifiers.MkC13State.sigDataOffset + (128 + 304 * t + 16 * h))
    rw [hap]; congr 1; omega
  · rw [SphincsMinusVerifierSpec.C13Concrete.parseSignatureC13_fors_authPath_getD_getElem?
        hparse ht hh]
    rfl

/-- **`merkleClimbData_to_sib`** — the state-dependent seam joining the *index-indexed*
data family `MerkleClimbData auth cdAt h` to the *state-side* sibling component of
`StepDataObligations` (`wordNormalize vsib2 = wordOfHash16 auth[h]`).  Given the frame
load fact that this climb step's masked sibling word `vsib` is the masked calldata read
`maskN (cdAt h)` (the shape of statement 1) and the statement-6 re-read `h6val`, the
single per-height fact `MerkleClimbData auth cdAt h` — which is *definitionally*
`SiblingBytesCorrespondence (cdAt h) auth[h]` — discharges exactly the `.sib` field via
`sibling_correspondence_of_bytes`.  This is the last structural seam: it lets the range
hypothesis `∀ i ∈ [0,h), MerkleClimbData auth cdAt i` (fed to `foldLoop_invariant_cond`)
supply the per-step bundle's sibling obligation, with the calldata-model content
isolated entirely in `MerkleClimbData`.  Pure specialisation, no re-evaluation.
Axiom-clean. -/
theorem merkleClimbData_to_sib
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat) (h : Nat)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode vsib2 : Nat)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2)
    (hload : vsib = maskN (cdAt h))
    (hdata : MerkleClimbData auth cdAt h) :
    wordNormalize vsib2 = wordOfHash16 ((auth[h]?).getD ⟨#[]⟩) :=
  sibling_correspondence_of_bytes st vsib vpar vadr sval o5 vnode vsib2 (cdAt h)
    ((auth[h]?).getD ⟨#[]⟩) h6val hload hdata

/-- **`stepDataObligations_of_calldata`** — assembles the full per-step bundle
`StepDataObligations` from the two *frame* facts that survive as ordinary
materialisation obligations (`hseed`: cell `0x00` holds the seed word; `hadr`: the
assembled ADRS frame value equals the FIPS layout word) plus the single
calldata-model family fact `MerkleClimbData auth cdAt h`, routed through
`merkleClimbData_to_sib` for the sibling component.  This is the assembly seam: it
exhibits precisely how the index-indexed `D`-family entry (the *only* blocker-#20
content) combines with the frame bookkeeping to produce the bundle that
`MerkleClimbRel_step` consumes — so a future climb-specialisation can construct each
iteration's `StepDataObligations` from `(hseed, hadr, hload)` (frame, generic) and the
range entry `MerkleClimbData auth cdAt h` (the lone open per-height datum).  Pure
constructor application.  Axiom-clean. -/
theorem stepDataObligations_of_calldata
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode vsib2 seed treeAdrs h mIdx : Nat)
    (hseed : (st.world.memory 0x00).val = seed)
    (hadr : wordNormalize vadr = treeAdrs ||| ((h + 1) <<< 32) ||| mIdx / 2)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2)
    (hload : vsib = maskN (cdAt h))
    (hdata : MerkleClimbData auth cdAt h) :
    StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth :=
  StepDataObligations.intro hseed hadr
    (merkleClimbData_to_sib auth cdAt h st vsib vpar vadr sval o5 vnode vsib2 h6val hload hdata)

/-- **`sibling_load_eq_maskN`** — discharges the `hload` premise of
`stepDataObligations_of_calldata` (`vsib = maskN (cdAt h)`) as a *pure interpreter
fact*, with `cdAt h` taken to be the raw `calldataload` value `k`.  Statement 1 of the
climb body is `and(calldataload(authPtr + 16·h), N_MASK)`; the interpreter's `bitAnd`
with a literal mask is `Nat.land` of the two operands (`ClimbKeccakStep.evalExpr_bitAnd_literal`),
and `N_MASK = nMask` with `maskN k = Nat.land k nMask` definitionally, so the masked
load evaluates to `maskN k`.  Matching that against statement 1's bound value `vsib`
(via `h1`) gives `vsib = maskN k`.  This is *not* blocker #20: it needs only the raw
load value `k` (an abstract interpreter read, supplied by the calldata frame) and the
calldata-word bound `k < 2^256` (a standing interpreter invariant).  Isolating it here
shrinks the `hload` premise to interpreter facts, leaving `MerkleClimbData` (the
masked-word ↦ `wordOfHash16` content) as the sole standing blocker-#20 assumption of
the per-step bundle. -/
theorem sibling_load_eq_maskN
    (st : RuntimeState) (authPtrVar : String) (vsib k : Nat)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (hk : evalExpr [] st
            (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) = some k)
    (hklt : k < 2 ^ 256) :
    vsib = maskN k := by
  have hmask : evalExpr [] st
      (.bitAnd (.calldataload (.add (.localVar authPtrVar)
        (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some (maskN k) := by
    rw [show (N_MASK : Nat) = nMask from rfl,
        SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal st _ k nMask hk hklt
          SphincsMinusVerifiers.ClimbKeccakStep.nMask_lt]
    rfl
  exact Option.some.inj (h1.symm.trans hmask)

/-- **`address_assembly_eq`** — discharges the `hadr` premise of
`stepDataObligations_of_calldata` (`wordNormalize vadr = A ||| S ||| P`) as a *pure
interpreter fact*.  Statement 3 of the climb body is
`or(adrsBase, or(shl(32, h+1), parentIdx))`; with each sub-operand's value in hand
(`adrsBase ↦ A`, `shl ↦ S`, `parentIdx ↦ P`, all `< 2^256`) the interpreter's two
`bitOr`s compose (`ClimbKeccakStep.evalExpr_bitOr_bounded`, twice) to the bare
`Nat.lor A (Nat.lor S P)`, re-associated to the FIPS left-nested word `A ||| S ||| P`
by `Nat.lor_assoc`; matching against statement 3's bound value `vadr` and using that
the disjunction is `< 2^256` (so `wordNormalize` is the identity) gives the goal.  This
is *not* blocker #20 — it is the address-word analogue of `sibling_load_eq_maskN`, the
value core of which is the already-closed `merkle_address_word`.  The open address
content (that `A = treeAdrs`, `S = (h+1)<<<32`, `P = mIdx/2` are the *right* operand
values) is ordinary ADRS arithmetic / loop bookkeeping, not the keccak/calldata
correspondence.  Axiom-clean. -/
theorem address_assembly_eq
    (st : RuntimeState) (adrsBase shlE parentIdxE : Expr) (vadr A S P : Nat)
    (h3 : evalExpr [] st (.bitOr adrsBase (.bitOr shlE parentIdxE)) = some vadr)
    (hA : evalExpr [] st adrsBase = some A)
    (hS : evalExpr [] st shlE = some S)
    (hP : evalExpr [] st parentIdxE = some P)
    (hAlt : A < 2 ^ 256) (hSlt : S < 2 ^ 256) (hPlt : P < 2 ^ 256) :
    wordNormalize vadr = A ||| S ||| P := by
  have hinner := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    st shlE parentIdxE S P hS hP hSlt hPlt
  have hSPlt : Nat.lor S P < 2 ^ 256 := Nat.bitwise_lt_two_pow hSlt hPlt
  have hfull := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
    st adrsBase (.bitOr shlE parentIdxE) A (Nat.lor S P) hA hinner hAlt hSPlt
  have hvadr : vadr = A ||| S ||| P := by
    have hv : vadr = Nat.lor A (Nat.lor S P) := Option.some.inj (h3.symm.trans hfull)
    rw [hv]; exact (Nat.lor_assoc A S P).symm
  rw [hvadr, Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod,
      show Compiler.Constants.evmModulus = 2 ^ 256 from rfl]
  exact Nat.mod_eq_of_lt (Nat.bitwise_lt_two_pow (Nat.bitwise_lt_two_pow hAlt hSlt) hPlt)

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem MerkleClimbRelA_step
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed adrsW h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata : StepDataObligationsW st vadr vsib2 seed adrsW h mIdx auth)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :

    MerkleClimbRel nodeVar idxVar
      (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st)
      (mIdx / 2,
          if mIdx % 2 == 0 then
            maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
          else
            maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
  obtain ⟨hseed, hadr, hsib⟩ := hdata
  have hpair := stepMerkleA_eq_merkleSpecStep nodeVar idxVar authPtrVar adrsE st
    vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW h mIdx node auth
    hne hne2 hparOff hvpar hseed hadr hnode hsib
    h1 h2 h3 h4 h5off h5val h6off h6val
  have hidx : lookupValue
      (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings idxVar
      = mIdx / 2 := (Prod.ext_iff.mp hpair).1
  have hn : lookupValue
      (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings nodeVar
      = (if mIdx % 2 == 0 then
          maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
        else
          maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) :=
    (Prod.ext_iff.mp hpair).2
  refine MerkleClimbRel.intro hidx ?_
  rw [hn]
  have hsn : wordNormalize
      (if mIdx % 2 == 0 then
        maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
      else
        maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node]))
    = (if mIdx % 2 == 0 then
        maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
      else
        maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
    split <;> exact wordNormalize_maskN _
  exact hsn

/-- **`MerkleClimbRel_step`** — the per-iteration climb-invariant advance, stated with
the entire open per-step data surface collapsed into the single `StepDataObligations`
bundle.  Given the bookkeeping hypotheses of `stepMerkle_eq_merkleSpecStep` (all
`hne`/`hparOff`/`hvpar` plus the `h1..h6` evalExpr frame facts — discharged from the
frame lemmas) and the inductive node input `hnode`, plus the single data bundle
`hdata : StepDataObligations …`, the post-state relates by `MerkleClimbRel` to the
spec-advanced accumulator `merkleSpecStep …`.  This is exactly the `hstep` shape
`ClimbLoop.foldLoop_invariant` consumes for `R = MerkleClimbRel`, with blocker #20
now isolated as the *one* named data premise `hdata` (whose `.sib` projection bottoms
out at `SiblingBytesCorrespondence`).  Proof = unbundle `hdata`, run the existing
control-flow step lemma to the pair equality, lift through `MerkleClimbRel_of_pair`.
No new interpreter evaluation; pure composition.  Axiom-clean. -/
theorem MerkleClimbRel_step
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata : StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    MerkleClimbRel nodeVar idxVar
      (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st)
      (merkleSpecStep seed treeAdrs auth h (mIdx, node)) := by
  obtain ⟨hseed, hadr, hsib⟩ := hdata
  refine MerkleClimbRel_of_pair nodeVar idxVar
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st)
    seed treeAdrs h mIdx node auth ?_
  exact stepMerkle_eq_merkleSpecStep nodeVar idxVar adrsBaseVar authPtrVar st
    vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
    hne hne2 hparOff hvpar hseed hadr hnode hsib
    h1 h2 h3 h4 h5off h5val h6off h6val

/-- **`ForsClimbRel_step`** — the FIPS FORS instantiation of
`MerkleClimbRelA_step` (`adrsE := ClimbKit.forsAdrs`,
`adrsW := adrsForsNode t0 l0 i h (mIdx / 2)`), folded back to the named
`forsSpecStep` accumulator.  This is the per-iteration `hstep` kernel for the
FORS inner Merkle climb (`ClimbKit.stepForsMerkle`). -/
theorem ForsClimbRel_step
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed i t0 l0 h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata : StepDataObligationsW st vadr vsib2 seed
              (SphincsMinusVerifierSpec.C13Concrete.adrsForsNode t0 l0 i h (mIdx / 2))
              h mIdx auth)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar "authPtr")
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar "pathIdx")) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            ClimbKit.forsAdrs = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "node") = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    MerkleClimbRel "node" "pathIdx" (ClimbKit.stepForsMerkle st)
      (forsSpecStep seed i t0 l0 auth h (mIdx, node)) := by
  have hres := MerkleClimbRelA_step "node" "pathIdx" "authPtr" ClimbKit.forsAdrs st
    vsib vpar vadr sval o5 vnode o6 vsib2 seed
    (SphincsMinusVerifierSpec.C13Concrete.adrsForsNode t0 l0 i h (mIdx / 2)) h mIdx node auth
    (by decide) (by decide) hparOff hvpar hnode hdata h1 h2 h3 h4 h5off h5val h6off h6val
  show MerkleClimbRel "node" "pathIdx"
      (ClimbKit.stepMerkleA "node" "pathIdx" "authPtr" ClimbKit.forsAdrs st)
      (forsSpecStep seed i t0 l0 auth h (mIdx, node))
  simp only [forsSpecStep]
  exact hres

/-- Even index ⇒ selector `s = 0`. -/
theorem merkle_selector_even (n : Nat) (h : n % 2 = 0) : (n &&& 1) <<< 5 = 0 := by
  rw [Nat.and_one_is_mod, h]; rfl

/-- Odd index ⇒ selector `s = 0x20`. -/
theorem merkle_selector_odd (n : Nat) (h : n % 2 = 1) : (n &&& 1) <<< 5 = 0x20 := by
  rw [Nat.and_one_is_mod, h]; rfl

/-- Even index ⇒ child slots unswapped: `0x40 ↦ node` slot, `0x60 ↦ sibling` slot. -/
theorem merkle_offsets_even (n : Nat) (h : n % 2 = 0) :
    (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40 ∧
    (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60 := by
  rw [merkle_selector_even n h]; exact ⟨rfl, rfl⟩

/-- Odd index ⇒ child slots swapped: `0x40 ↦ sibling` slot, `0x60 ↦ node` slot. -/
theorem merkle_offsets_odd (n : Nat) (h : n % 2 = 1) :
    (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60 ∧
    (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40 := by
  rw [merkle_selector_odd n h]; exact ⟨rfl, rfl⟩

/-! ## 6a-bis. STEP-2 frame preservation: `stepMerkle` leaves the static frame intact.

The four lemmas below establish that one `stepMerkle` step preserves exactly the
*static* conjuncts of `MerkleClimbFrame` (selector, calldata image, seed cell
`mem[0x00]`, and any binding for a variable distinct from the five the body writes).
Each is a binding/memory-projection of the same eight-statement thread that
`stepMerkle_memory`/`stepMerkle_idx_binding` already run: the body writes only
`mem 0x20/0x40/0x60` (the latter two under the parity-xored offsets `o5/o6 ∈
{0x40,0x60}`, never `0x00`) and rebinds only `sibling/parentIdx/s/nodeVar/idxVar`,
leaving `selector`, `world.calldata`, `mem[0x00]`, and every other binding untouched.
These are the frame half of the eventual `MerkleClimbFrame` preservation; no keccak
or calldata correspondence is involved.  Axiom-clean. -/

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_selector_calldata
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).selector = st.selector
    ∧ (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).world.calldata
        = st.world.calldata := by
  have hs1 := MemoryKit.execStmt_letVar_continue st "sibling" _ vsib h1
  set st1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "sibling" vsib } with hst1
  have hs2 := MemoryKit.execStmt_letVar_continue st1 "parentIdx" _ vpar h2
  set st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "parentIdx" vpar } with hst2
  have hoff3 : evalExpr [] st2 (.literal 0x20) = some 0x20 := rfl
  have hs3 := MemoryKit.execStmt_mstore_continue st2 (.literal 0x20) _ 0x20 vadr hoff3 h3
  set st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
    with hst3
  have hs4 := MemoryKit.execStmt_letVar_continue st3 "s" _ sval h4
  set st4 : RuntimeState :=
    { st3 with bindings := bindValue st3.bindings "s" sval } with hst4
  have hs5 := MemoryKit.execStmt_mstore_continue st4 (.bitXor (.literal 0x40) (.localVar "s")) _
      o5 vnode h5off h5val
  set st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
    with hst5
  have hs6 := MemoryKit.execStmt_mstore_continue st5 (.bitXor (.literal 0x60) (.localVar "s")) _
      o6 vsib2 h6off h6val
  set st6 : RuntimeState :=
    { st5 with world := { st5.world with memory := MemoryKit.memUpdate st5.world.memory o6 vsib2 } }
    with hst6
  set kv : Nat := (Verity.Core.Uint256.and (keccakMemorySlice st6.world.memory (wordNormalize 0x00) (wordNormalize 0x80)) (wordNormalize N_MASK)).val with hkv
  have hval7 : evalExpr [] st6
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some kv := rfl
  have hs7 := assignVar_continue st6 nodeVar _ _ hval7
  set st7 : RuntimeState :=
    { st6 with bindings := bindValue st6.bindings nodeVar kv } with hst7
  have hval8 : evalExpr [] st7 (.localVar "parentIdx")
      = some (lookupValue st7.bindings "parentIdx") := rfl
  have hs8 := assignVar_continue st7 idxVar _ _ hval8
  show ((match execStmtList [] st
            ([ Stmt.letVar "sibling"
                (.bitAnd (.calldataload (.add (.localVar authPtrVar)
                  (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
             , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar idxVar))
             , Stmt.mstore (.literal 0x20) adrsE
             , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
             , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar nodeVar)
             , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
             , Stmt.assignVar nodeVar
                (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
             , Stmt.assignVar idxVar (.localVar "parentIdx") ]) with
          | .continue s' => s' | _ => st).selector = st.selector)
      ∧ ((match execStmtList [] st
            ([ Stmt.letVar "sibling"
                (.bitAnd (.calldataload (.add (.localVar authPtrVar)
                  (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
             , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar idxVar))
             , Stmt.mstore (.literal 0x20) adrsE
             , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
             , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar nodeVar)
             , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
             , Stmt.assignVar nodeVar
                (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
             , Stmt.assignVar idxVar (.localVar "parentIdx") ]) with
          | .continue s' => s' | _ => st).world.calldata = st.world.calldata)
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs3]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs4]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs5]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs6]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs7]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs8]
  exact ⟨rfl, rfl⟩

/-- **`stepMerkle_selector_calldata`** — one climb step preserves both the EVM
`selector` and the `world.calldata` image: the body's eight statements are all
`letVar`/`assignVar`/`mstore`, none of which touches `selector` or the calldata
field (only `bindings` and `world.memory`).  Same eight `evalExpr` hypotheses as
`stepMerkle_memory`, threaded identically; the conclusion projects the two
frame-invariant fields. -/
theorem stepMerkle_selector_calldata
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).selector = st.selector
    ∧ (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).world.calldata
        = st.world.calldata :=
  stepMerkleA_selector_calldata nodeVar idxVar authPtrVar (ClimbKit.xmssAdrs adrsBaseVar) st
    vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_binding_frozen
    (nodeVar idxVar authPtrVar w : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hwsib : w ≠ "sibling") (hwpar : w ≠ "parentIdx") (hws : w ≠ "s")
    (hwnode : w ≠ nodeVar) (hwidx : w ≠ idxVar)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).bindings w
      = lookupValue st.bindings w := by
  have hs1 := MemoryKit.execStmt_letVar_continue st "sibling" _ vsib h1
  set st1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "sibling" vsib } with hst1
  have hs2 := MemoryKit.execStmt_letVar_continue st1 "parentIdx" _ vpar h2
  set st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "parentIdx" vpar } with hst2
  have hoff3 : evalExpr [] st2 (.literal 0x20) = some 0x20 := rfl
  have hs3 := MemoryKit.execStmt_mstore_continue st2 (.literal 0x20) _ 0x20 vadr hoff3 h3
  set st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
    with hst3
  have hs4 := MemoryKit.execStmt_letVar_continue st3 "s" _ sval h4
  set st4 : RuntimeState :=
    { st3 with bindings := bindValue st3.bindings "s" sval } with hst4
  have hs5 := MemoryKit.execStmt_mstore_continue st4 (.bitXor (.literal 0x40) (.localVar "s")) _
      o5 vnode h5off h5val
  set st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
    with hst5
  have hs6 := MemoryKit.execStmt_mstore_continue st5 (.bitXor (.literal 0x60) (.localVar "s")) _
      o6 vsib2 h6off h6val
  set st6 : RuntimeState :=
    { st5 with world := { st5.world with memory := MemoryKit.memUpdate st5.world.memory o6 vsib2 } }
    with hst6
  set kv : Nat := (Verity.Core.Uint256.and (keccakMemorySlice st6.world.memory (wordNormalize 0x00) (wordNormalize 0x80)) (wordNormalize N_MASK)).val with hkv
  have hval7 : evalExpr [] st6
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
      = some kv := rfl
  have hs7 := assignVar_continue st6 nodeVar _ _ hval7
  set st7 : RuntimeState :=
    { st6 with bindings := bindValue st6.bindings nodeVar kv } with hst7
  have hval8 : evalExpr [] st7 (.localVar "parentIdx")
      = some (lookupValue st7.bindings "parentIdx") := rfl
  have hs8 := assignVar_continue st7 idxVar _ _ hval8
  show lookupValue (match execStmtList [] st
          ([ Stmt.letVar "sibling"
              (.bitAnd (.calldataload (.add (.localVar authPtrVar)
                (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK))
           , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar idxVar))
           , Stmt.mstore (.literal 0x20) adrsE
           , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
           , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar nodeVar)
           , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
           , Stmt.assignVar nodeVar
              (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
           , Stmt.assignVar idxVar (.localVar "parentIdx") ]) with
        | .continue s' => s' | _ => st).bindings w = lookupValue st.bindings w
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs1]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs2]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs3]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs4]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs5]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs6]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs7]
  rw [ClimbKit.execStmtList_cons_continue _ _ _ _ hs8]
  show lookupValue
      (bindValue (bindValue st6.bindings nodeVar kv) idxVar
        (lookupValue st7.bindings "parentIdx")) w = lookupValue st.bindings w
  rw [MemoryKit.lookupValue_bindValue_ne _ idxVar w _ (Ne.symm hwidx),
      MemoryKit.lookupValue_bindValue_ne _ nodeVar w _ (Ne.symm hwnode)]
  show lookupValue
      (bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval) w
        = lookupValue st.bindings w
  rw [MemoryKit.lookupValue_bindValue_ne _ "s" w _ (Ne.symm hws),
      MemoryKit.lookupValue_bindValue_ne _ "parentIdx" w _ (Ne.symm hwpar),
      MemoryKit.lookupValue_bindValue_ne _ "sibling" w _ (Ne.symm hwsib)]

/-- **`stepMerkle_binding_frozen`** — one climb step preserves the binding of any
variable `w` distinct from the five the body rebinds (`sibling`, `parentIdx`, `s`,
`nodeVar`, `idxVar`).  This is exactly what carries the frame's `adrsBaseVar` and
`authPtrVar` bindings (the ADRS base and auth-path pointer) across the step.  Same
eight-statement thread; the conclusion skips the five rebinds via
`lookupValue_bindValue_ne`. -/
theorem stepMerkle_binding_frozen
    (nodeVar idxVar adrsBaseVar authPtrVar w : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hwsib : w ≠ "sibling") (hwpar : w ≠ "parentIdx") (hws : w ≠ "s")
    (hwnode : w ≠ nodeVar) (hwidx : w ≠ idxVar)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    lookupValue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).bindings w
      = lookupValue st.bindings w :=
  stepMerkleA_binding_frozen nodeVar idxVar authPtrVar w (ClimbKit.xmssAdrs adrsBaseVar) st
    vsib vpar vadr sval o5 vnode o6 vsib2 hwsib hwpar hws hwnode hwidx
    h1 h2 h3 h4 h5off h5val h6off h6val

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_mem_zero
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (ho5 : (0x00 : Nat) ≠ o5) (ho6 : (0x00 : Nat) ≠ o6)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).world.memory 0x00
      = st.world.memory 0x00 := by
  rw [stepMerkleA_memory nodeVar idxVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val]
  rw [MemoryKit.memUpdate_diff _ o6 0x00 vsib2 ho6,
      MemoryKit.memUpdate_diff _ o5 0x00 vnode ho5,
      MemoryKit.memUpdate_diff _ 0x20 0x00 vadr (by decide)]

/-- **`stepMerkle_mem_zero`** — one climb step preserves the seed cell `mem[0x00]`.
The body's three memory writes land at `0x20` and the parity-xored child slots
`o5`/`o6` (both `∈ {0x40,0x60}`, supplied here as `≠ 0x00`), so a read at `0x00`
falls through all three `memUpdate`s to the entry memory.  Derived from
`stepMerkle_memory` + `memUpdate_diff`. -/
theorem stepMerkle_mem_zero
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (ho5 : (0x00 : Nat) ≠ o5) (ho6 : (0x00 : Nat) ≠ o6)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).world.memory 0x00
      = st.world.memory 0x00 := by
  rw [stepMerkle_memory nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val]
  rw [MemoryKit.memUpdate_diff _ o6 0x00 vsib2 ho6,
      MemoryKit.memUpdate_diff _ o5 0x00 vnode ho5,
      MemoryKit.memUpdate_diff _ 0x20 0x00 vadr (by decide)]

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_mem_val_of_ne
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (addr vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h20 : addr ≠ 0x20) (ho5 : addr ≠ o5) (ho6 : addr ≠ o6)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    ((ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).world.memory addr).val =
      (st.world.memory addr).val := by
  rw [stepMerkleA_memory nodeVar idxVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val]
  rw [MemoryKit.memUpdate_diff _ o6 addr vsib2 ho6,
      MemoryKit.memUpdate_diff _ o5 addr vnode ho5,
      MemoryKit.memUpdate_diff _ 0x20 addr vadr h20]

/-- Generic value-frame form of `stepMerkle_mem_zero`: any address disjoint from
the three Merkle scratch writes (`0x20`, `o5`, `o6`) is preserved by one
branchless-Merkle step. -/
theorem stepMerkle_mem_val_of_ne
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (addr vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h20 : addr ≠ 0x20) (ho5 : addr ≠ o5) (ho6 : addr ≠ o6)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).world.memory addr).val =
      (st.world.memory addr).val := by
  rw [stepMerkle_memory nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val]
  rw [MemoryKit.memUpdate_diff _ o6 addr vsib2 ho6,
      MemoryKit.memUpdate_diff _ o5 addr vnode ho5,
      MemoryKit.memUpdate_diff _ 0x20 addr vadr h20]

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_mem_zero_of_parity
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (mIdx : Nat)
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).world.memory 0x00
      = st.world.memory 0x00 := by
  have ho5 : (0x00 : Nat) ≠ o5 := by
    rcases hparOff with ⟨_, h5, _⟩ | ⟨_, h5, _⟩ <;> rw [h5] <;> decide
  have ho6 : (0x00 : Nat) ≠ o6 := by
    rcases hparOff with ⟨_, _, h6⟩ | ⟨_, _, h6⟩ <;> rw [h6] <;> decide
  exact stepMerkleA_mem_zero nodeVar idxVar authPtrVar adrsE st
    vsib vpar vadr sval o5 vnode o6 vsib2 ho5 ho6
    h1 h2 h3 h4 h5off h5val h6off h6val

/-- Parity-packaged form of `stepMerkle_mem_zero`: the usual Merkle child-slot
offset disjunction (`o5/o6` are `0x40/0x60` in either order) is enough to prove
that one branchless-Merkle step preserves the seed cell `mem[0x00]`. -/
theorem stepMerkle_mem_zero_of_parity
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (mIdx : Nat)
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).world.memory 0x00
      = st.world.memory 0x00 := by
  have ho5 : (0x00 : Nat) ≠ o5 := by
    rcases hparOff with ⟨_, h5, _⟩ | ⟨_, h5, _⟩ <;> rw [h5] <;> decide
  have ho6 : (0x00 : Nat) ≠ o6 := by
    rcases hparOff with ⟨_, _, h6⟩ | ⟨_, _, h6⟩ <;> rw [h6] <;> decide
  exact stepMerkle_mem_zero nodeVar idxVar adrsBaseVar authPtrVar st
    vsib vpar vadr sval o5 vnode o6 vsib2 ho5 ho6
    h1 h2 h3 h4 h5off h5val h6off h6val

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem stepMerkleA_mem_zero_val_of_parity
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (mIdx : Nat)
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    ((ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st).world.memory 0x00).val
      = (st.world.memory 0x00).val := by
  rw [stepMerkleA_mem_zero_of_parity nodeVar idxVar authPtrVar adrsE st
    vsib vpar vadr sval o5 vnode o6 vsib2 mIdx hparOff
    h1 h2 h3 h4 h5off h5val h6off h6val]

/-- Value-projection corollary of `stepMerkle_mem_zero_of_parity`, matching the
memory-frame premise shape used by the loop adapters. -/
theorem stepMerkle_mem_zero_val_of_parity
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (mIdx : Nat)
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st).world.memory 0x00).val
      = (st.world.memory 0x00).val := by
  rw [stepMerkle_mem_zero_of_parity nodeVar idxVar adrsBaseVar authPtrVar st
    vsib vpar vadr sval o5 vnode o6 vsib2 mIdx hparOff
    h1 h2 h3 h4 h5off h5val h6off h6val]

/-! ## 6a-ter. STEP-2 per-fact `evalExpr` discharges for the climb body.

These three generic combinators resolve exactly the `h2`/`h4`/`h5off`/`h6off`
`evalExpr` hypotheses of `MerkleClimbRel_step` from the *binding* of the relevant
variable in the (arbitrary) evaluation state.  They read no memory/calldata
(the climb body's stmts 2/4/5off/6off are pure `shr`/`shl`/`bitXor` over
`idxVar`/`"s"` and small literals), so they hold at any state whose bindings carry
`idxVar`/`"s"` — including each threaded intermediate `stN`.  `h1` is
`merkle_sibling_read_frozen`, `h3` is `address_assembly_eq`; `h5val`/`h6val` are the
bare `.localVar` reads (`some (lookupValue …)`), discharged definitionally at the
assembly site.  Axiom-clean. -/

/-- **`eval_parentIdx_shr`** — climb body stmt 2 `shr(1, idxVar)` resolves to
`mIdx >>> 1` (`= mIdx / 2`, the spec `parentIdx`) whenever `idxVar ↦ mIdx`. -/
theorem eval_parentIdx_shr (idxVar : String) (s : RuntimeState) (mIdx : Nat)
    (hidx : lookupValue s.bindings idxVar = mIdx) (hmlt : mIdx < 2 ^ 256) :
    evalExpr [] s (.shr (.literal 1) (.localVar idxVar)) = some (mIdx >>> 1) := by
  have hlit : evalExpr [] s (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
  have hv : evalExpr [] s (.localVar idxVar) = some mIdx := by
    show some (lookupValue s.bindings idxVar) = some mIdx; rw [hidx]
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded s (.literal 1)
    (.localVar idxVar) 1 mIdx hlit hv (by decide) hmlt

/-- **`eval_selector_shl`** — climb body stmt 4 `shl(5, and(idxVar, 1))` resolves to
`(mIdx &&& 1) <<< 5` (the parity selector `s ∈ {0, 0x20}`) whenever `idxVar ↦ mIdx`. -/
theorem eval_selector_shl (idxVar : String) (s : RuntimeState) (mIdx : Nat)
    (hidx : lookupValue s.bindings idxVar = mIdx) (hmlt : mIdx < 2 ^ 256) :
    evalExpr [] s (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1)))
      = some ((Nat.land mIdx 1) <<< 5) := by
  have hlit5 : evalExpr [] s (.literal 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
  have hv : evalExpr [] s (.localVar idxVar) = some mIdx := by
    show some (lookupValue s.bindings idxVar) = some mIdx; rw [hidx]
  have hand : evalExpr [] s (.bitAnd (.localVar idxVar) (.literal 1)) = some (Nat.land mIdx 1) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal s (.localVar idxVar) mIdx 1
      hv hmlt (by decide)
  have hand_lt : Nat.land mIdx 1 < 2 ^ 256 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hbound : (Nat.land mIdx 1) <<< 5 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded s (.literal 5)
    (.bitAnd (.localVar idxVar) (.literal 1)) 5 (Nat.land mIdx 1) hlit5 hand (by decide)
    hand_lt hbound

/-- **`eval_childOffset_xor`** — climb body stmts 5/6 `xor(off, s)` resolve to
`Nat.xor off sval` whenever `"s" ↦ sval`; with `off ∈ {0x40, 0x60}` and
`sval ∈ {0, 0x20}` this is the parity-swapped child slot. -/
theorem eval_childOffset_xor (s : RuntimeState) (off sval : Nat)
    (hs : lookupValue s.bindings "s" = sval) (hofflt : off < 2 ^ 256)
    (hsvalt : sval < 2 ^ 256) :
    evalExpr [] s (.bitXor (.literal off) (.localVar "s")) = some (Nat.xor off sval) := by
  have hlit : evalExpr [] s (.literal off) = some off := by
    show some (wordNormalize off) = some off
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt hofflt]
  have hv : evalExpr [] s (.localVar "s") = some sval := by
    show some (lookupValue s.bindings "s") = some sval; rw [hs]
  exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitXor_bounded s (.literal off)
    (.localVar "s") off sval hlit hv hofflt hsvalt

/-- Address-parametric (`adrsE`) generalization; the classic lemma is the
`ClimbKit.xmssAdrs adrsBaseVar` instantiation (see the wrapper below). -/
theorem MerkleClimbFrameA_step
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (adrsE : Expr)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr adrsW : Nat)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hframe : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
                pkSeed pkRoot message sig seed treeAdrs merklePtr st (mIdx, node))
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata : StepDataObligationsW st vadr vsib2 seed adrsW h mIdx auth)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            adrsE = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
      pkSeed pkRoot message sig seed treeAdrs merklePtr
      (ClimbKit.stepMerkleA nodeVar idxVar authPtrVar adrsE st)
      (mIdx / 2,
          if mIdx % 2 == 0 then
            maskN (keccakWords [seed, adrsW, node, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
          else
            maskN (keccakWords [seed, adrsW, wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])) := by
  obtain ⟨hN_i, hN_p, hN_sib, hN_s, hN_h, hI_sib, hI_p, hI_s, hI_h,
          hA_sib, hA_p, hA_s, hA_n, hA_i, hA_h,
          hP_sib, hP_p, hP_s, hP_n, hP_i, hP_h⟩ := hframe.2.2.2.2.2.2
  have hrel := hframe.1
  have hadrs := hframe.2.1
  have hauth := hframe.2.2.1
  have hmem0 := hframe.2.2.2.1
  have hsel := hframe.2.2.2.2.1
  have hcd := hframe.2.2.2.2.2.1
  have ho5 : (0x00 : Nat) ≠ o5 := by
    rcases hparOff with ⟨_, h5, _⟩ | ⟨_, h5, _⟩ <;> rw [h5] <;> decide
  have ho6 : (0x00 : Nat) ≠ o6 := by
    rcases hparOff with ⟨_, _, h6⟩ | ⟨_, _, h6⟩ <;> rw [h6] <;> decide
  have hsc := stepMerkleA_selector_calldata nodeVar idxVar authPtrVar adrsE st
    vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    hN_i, hN_p, hN_sib, hN_s, hN_h, hI_sib, hI_p, hI_s, hI_h,
    hA_sib, hA_p, hA_s, hA_n, hA_i, hA_h,
    hP_sib, hP_p, hP_s, hP_n, hP_i, hP_h⟩
  · exact MerkleClimbRelA_step nodeVar idxVar authPtrVar adrsE st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed adrsW h mIdx node auth
      hN_i hN_p hparOff hvpar hnode hdata h1 h2 h3 h4 h5off h5val h6off h6val
  · rw [stepMerkleA_binding_frozen nodeVar idxVar authPtrVar adrsBaseVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 hA_sib hA_p hA_s hA_n hA_i
        h1 h2 h3 h4 h5off h5val h6off h6val]
    exact hadrs
  · rw [stepMerkleA_binding_frozen nodeVar idxVar authPtrVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 hP_sib hP_p hP_s hP_n hP_i
        h1 h2 h3 h4 h5off h5val h6off h6val]
    exact hauth
  · rw [stepMerkleA_mem_zero nodeVar idxVar authPtrVar adrsE st
        vsib vpar vadr sval o5 vnode o6 vsib2 ho5 ho6
        h1 h2 h3 h4 h5off h5val h6off h6val]
    exact hmem0
  · rw [hsc.1]; exact hsel
  · rw [hsc.2]; exact hcd

/-- **`MerkleClimbFrame_step`** — STEP-2 frame self-preservation: one `stepMerkle`
step carries the *whole* `MerkleClimbFrame` (relation + static frame) forward,
given exactly the per-step bundle `MerkleClimbRel_step` already consumes
(`hparOff`/`hvpar`/`hnode`/`StepDataObligations` + the eight `evalExpr` facts
`h1..h6val`).  The relation advance is `MerkleClimbRel_step`; the static conjuncts
are preserved by the three frame-frozen projections
(`stepMerkle_binding_frozen` for the `adrsBaseVar`/`authPtrVar` bindings,
`stepMerkle_mem_zero` for the seed cell, `stepMerkle_selector_calldata` for
selector + calldata image); the name-distinctness tail is state-independent and
carried over verbatim.  This is the STEP-2 deliverable: the frame is preserved by
one step *modulo the same per-step facts* the bare relation step needs — so a
frame-threaded loop lift can use it wherever `MerkleClimbRel_step` was used, with
the static frame now available at every iteration to discharge those facts.  Does
not itself discharge `h1..h6val`/`StepDataObligations` (that is the offset/address/
sibling content, isolated in the per-fact combinators + `MerkleClimbData`).
Axiom-clean. -/
theorem MerkleClimbFrame_step
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (h mIdx node : Nat) (auth : List SphincsMinusVerifierSpec.Bytes)
    (hframe : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
                pkSeed pkRoot message sig seed treeAdrs merklePtr st (mIdx, node))
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata : StepDataObligations st vadr vsib2 seed treeAdrs h mIdx auth)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
      pkSeed pkRoot message sig seed treeAdrs merklePtr
      (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st)
      (merkleSpecStep seed treeAdrs auth h (mIdx, node)) := by
  obtain ⟨hN_i, hN_p, hN_sib, hN_s, hN_h, hI_sib, hI_p, hI_s, hI_h,
          hA_sib, hA_p, hA_s, hA_n, hA_i, hA_h,
          hP_sib, hP_p, hP_s, hP_n, hP_i, hP_h⟩ := hframe.2.2.2.2.2.2
  have hrel := hframe.1
  have hadrs := hframe.2.1
  have hauth := hframe.2.2.1
  have hmem0 := hframe.2.2.2.1
  have hsel := hframe.2.2.2.2.1
  have hcd := hframe.2.2.2.2.2.1
  have ho5 : (0x00 : Nat) ≠ o5 := by
    rcases hparOff with ⟨_, h5, _⟩ | ⟨_, h5, _⟩ <;> rw [h5] <;> decide
  have ho6 : (0x00 : Nat) ≠ o6 := by
    rcases hparOff with ⟨_, _, h6⟩ | ⟨_, _, h6⟩ <;> rw [h6] <;> decide
  have hsc := stepMerkle_selector_calldata nodeVar idxVar adrsBaseVar authPtrVar st
    vsib vpar vadr sval o5 vnode o6 vsib2 h1 h2 h3 h4 h5off h5val h6off h6val
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    hN_i, hN_p, hN_sib, hN_s, hN_h, hI_sib, hI_p, hI_s, hI_h,
    hA_sib, hA_p, hA_s, hA_n, hA_i, hA_h,
    hP_sib, hP_p, hP_s, hP_n, hP_i, hP_h⟩
  · exact MerkleClimbRel_step nodeVar idxVar adrsBaseVar authPtrVar st
      vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
      hN_i hN_p hparOff hvpar hnode hdata h1 h2 h3 h4 h5off h5val h6off h6val
  · rw [stepMerkle_binding_frozen nodeVar idxVar adrsBaseVar authPtrVar adrsBaseVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 hA_sib hA_p hA_s hA_n hA_i
        h1 h2 h3 h4 h5off h5val h6off h6val]
    exact hadrs
  · rw [stepMerkle_binding_frozen nodeVar idxVar adrsBaseVar authPtrVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 hP_sib hP_p hP_s hP_n hP_i
        h1 h2 h3 h4 h5off h5val h6off h6val]
    exact hauth
  · rw [stepMerkle_mem_zero nodeVar idxVar adrsBaseVar authPtrVar st
        vsib vpar vadr sval o5 vnode o6 vsib2 ho5 ho6
        h1 h2 h3 h4 h5off h5val h6off h6val]
    exact hmem0
  · rw [hsc.1]; exact hsel
  · rw [hsc.2]; exact hcd

/-- **`MerkleClimbFrame_h_inject`** — STEP-3 plumbing: the frame survives the loop's
own `h` loop-variable binding.  `ClimbLoop.foldLoop` rebinds `"h"` before each
`stepMerkle`, so the per-step engine hands the step a state of the shape
`{ s with bindings := bindValue s.bindings "h" v }`.  None of the frame's four tracked
variables (`nodeVar`/`idxVar`/`adrsBaseVar`/`authPtrVar`) is `"h"` — that is exactly
what the `≠ "h"` distinctness leaves guarantee — so every binding lookup is unchanged
(`lookupValue_bindValue_ne`); the `world` (seed cell + calldata) and `selector` are
untouched by a `bindings`-only structure update (defeq).  This lets a frame-threaded
loop lift feed `MerkleClimbFrame_step` at the `h`-injected state.  Axiom-clean. -/
theorem MerkleClimbFrame_h_inject
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (s : RuntimeState) (a : Nat × Nat) (v : Nat)
    (hframe : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
                pkSeed pkRoot message sig seed treeAdrs merklePtr s a) :
    MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
      pkSeed pkRoot message sig seed treeAdrs merklePtr
      { s with bindings := bindValue s.bindings "h" v } a := by
  obtain ⟨hN_i, hN_p, hN_sib, hN_s, hN_h, hI_sib, hI_p, hI_s, hI_h,
          hA_sib, hA_p, hA_s, hA_n, hA_i, hA_h,
          hP_sib, hP_p, hP_s, hP_n, hP_i, hP_h⟩ := hframe.2.2.2.2.2.2
  have hrel := hframe.1
  have hadrs := hframe.2.1
  have hauth := hframe.2.2.1
  have hmem0 := hframe.2.2.2.1
  have hsel := hframe.2.2.2.2.1
  have hcd := hframe.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, hmem0, hsel, hcd,
    hN_i, hN_p, hN_sib, hN_s, hN_h, hI_sib, hI_p, hI_s, hI_h,
    hA_sib, hA_p, hA_s, hA_n, hA_i, hA_h,
    hP_sib, hP_p, hP_s, hP_n, hP_i, hP_h⟩
  · refine MerkleClimbRel.intro ?_ ?_
    · show lookupValue (bindValue s.bindings "h" v) idxVar = a.1
      rw [MemoryKit.lookupValue_bindValue_ne s.bindings "h" idxVar v (Ne.symm hI_h)]
      exact hrel.idx
    · show wordNormalize (lookupValue (bindValue s.bindings "h" v) nodeVar) = a.2
      rw [MemoryKit.lookupValue_bindValue_ne s.bindings "h" nodeVar v (Ne.symm hN_h)]
      exact hrel.node
  · show lookupValue (bindValue s.bindings "h" v) adrsBaseVar = treeAdrs
    rw [MemoryKit.lookupValue_bindValue_ne s.bindings "h" adrsBaseVar v (Ne.symm hA_h)]
    exact hadrs
  · show lookupValue (bindValue s.bindings "h" v) authPtrVar = merklePtr
    rw [MemoryKit.lookupValue_bindValue_ne s.bindings "h" authPtrVar v (Ne.symm hP_h)]
    exact hauth

/-- **`MerkleClimbFrame_hstep`** — STEP-3 per-step `hstep` builder: the *exact* body of
the `merkleClimbFrame_foldLoop_correspondence`/`xmssClimbFrame_model_node` `hstep`
premise, derived by composing `MerkleClimbFrame_h_inject` (frame survives the loop's
`"h"` rebind) with `MerkleClimbFrame_step` (frame preserved by one `stepMerkle`).

Given the frame at the iterate `s` and the per-step data bundle *at the `h`-injected
state* (`hparOff`/`hvpar`/`hnode`/`StepDataObligations` + the eight `evalExpr` facts
`h1..h6val`), it produces the frame at `stepMerkle (h-injected state)` paired with the
spec-advanced accumulator.  This packages precisely what the loop's `hstep` premise
demands, with the static frame folded in for free — so a concrete climb-entry
instantiation need only supply the per-step *data* facts (which, for `h1`, bottom out at
the site-specific offset identity `merklePtr + idx<<4 = sigDataOffset + sOff` via
`merkle_sibling_read_frozen`, not carried by the generic frame).  Pure composition, no
new evaluation.  Axiom-clean. -/
theorem MerkleClimbFrame_hstep
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (s : RuntimeState) (mIdx node idx : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes)
    (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hframe : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
                pkSeed pkRoot message sig seed treeAdrs merklePtr s (mIdx, node))
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata : StepDataObligations
              { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
              vadr vsib2 seed treeAdrs idx mIdx auth)
    (h1 : evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr []
            { s with bindings :=
              bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { s with bindings :=
              bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
                "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { s with
              world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
                  "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { s with
              world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
                  "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { s with
              world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
                  "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { s with
              world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
                  "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { s with
              world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
                  "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
      pkSeed pkRoot message sig seed treeAdrs merklePtr
      (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
      (merkleSpecStep seed treeAdrs auth idx (mIdx, node)) :=
  MerkleClimbFrame_step nodeVar idxVar adrsBaseVar authPtrVar pkSeed pkRoot message sig
    seed treeAdrs merklePtr
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
    vsib vpar vadr sval o5 vnode o6 vsib2 idx mIdx node auth
    (MerkleClimbFrame_h_inject nodeVar idxVar adrsBaseVar authPtrVar pkSeed pkRoot message sig
      seed treeAdrs merklePtr s (mIdx, node) (wordNormalize idx) hframe)
    hparOff hvpar hnode hdata h1 h2 h3 h4 h5off h5val h6off h6val

/-! ## 6b. STEP-2 climb-loop lift: whole-loop `MerkleClimbRel` ↔ `specFold`/`xmssClimb`.

The per-step pieces above (`MerkleClimbRel_step`, `stepDataObligations_of_calldata`,
`sibling_load_eq_maskN`, `address_assembly_eq`) and the whole-loop range suppliers
(`xmss_climb_data_range`, `fors_climb_data_range`) are threaded through the conditional
climb-induction engine `ClimbLoop.foldLoop_invariant_cond` here.  These two lemmas are
*conditional* on the per-step advance `hstep` (the `MerkleClimbRel_step` shape, whose
remaining open content is the frame bookkeeping `h1..h6`/seed/adr that holds only at the
concrete climb-entry state from the segment trace) and the initial-node relation `hR`
(the climb's seed node — for XMSS the WOTS-PK keccak, for FORS the leaf keccak).  They do
*not* discharge those; they isolate exactly that residual while showing the range
suppliers plug straight into the loop. -/

/-- **`merkleClimb_foldLoop_correspondence`** — STEP-2 loop lift.  `foldLoop_invariant_cond`
specialised to the Merkle climb (`R = MerkleClimbRel`, `specStep = merkleSpecStep`,
`D = MerkleClimbData auth cdAt`, `step = stepMerkle`): the whole climb loop advances
`MerkleClimbRel` together with `ClimbLoop.specFold`, gated on the per-step advance `hstep`
and the range hypothesis (supplied by `xmss_climb_data_range`/`fors_climb_data_range`).
Pure instantiation of the engine; no new evaluation, no axioms. -/
theorem merkleClimb_foldLoop_correspondence
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (seed treeAdrs : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx → MerkleClimbRel nodeVar idxVar s a →
        MerkleClimbRel nodeVar idxVar
          (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (merkleSpecStep seed treeAdrs auth idx a))
    (state : RuntimeState) (a : Nat × Nat) (index remaining : Nat)
    (hD : ∀ i, index ≤ i → i < index + remaining → MerkleClimbData auth cdAt i)
    (hR : MerkleClimbRel nodeVar idxVar state a) :
    MerkleClimbRel nodeVar idxVar
      (ClimbLoop.foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
        state index remaining)
      (ClimbLoop.specFold (merkleSpecStep seed treeAdrs auth) a index remaining) :=
  ClimbLoop.foldLoop_invariant_cond "h"
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
    (merkleSpecStep seed treeAdrs auth) (MerkleClimbRel nodeVar idxVar)
    (MerkleClimbData auth cdAt) hstep state a index remaining hD hR

/-- Exact-node companion to `merkleClimb_foldLoop_correspondence`.  This keeps
the raw `nodeVar` binding equal to the spec accumulator node, provided the
per-step advance also preserves the raw relation. -/
theorem merkleClimbRaw_foldLoop_correspondence
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (seed treeAdrs : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx → MerkleClimbRawRel nodeVar idxVar s a →
        MerkleClimbRawRel nodeVar idxVar
          (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (merkleSpecStep seed treeAdrs auth idx a))
    (state : RuntimeState) (a : Nat × Nat) (index remaining : Nat)
    (hD : ∀ i, index ≤ i → i < index + remaining → MerkleClimbData auth cdAt i)
    (hR : MerkleClimbRawRel nodeVar idxVar state a) :
    MerkleClimbRawRel nodeVar idxVar
      (ClimbLoop.foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
        state index remaining)
      (ClimbLoop.specFold (merkleSpecStep seed treeAdrs auth) a index remaining) :=
  ClimbLoop.foldLoop_invariant_cond "h"
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
    (merkleSpecStep seed treeAdrs auth) (MerkleClimbRawRel nodeVar idxVar)
    (MerkleClimbData auth cdAt) hstep state a index remaining hD hR

/-- **`xmssClimb_model_node`** — STEP-2 climb-correspondence equality for one XMSS
hypertree layer (or one FORS tree): the model node binding after the whole `forEach "h"`
climb loop EVM-normalises to the spec `xmssClimb` root piece.  Combines
`merkleClimb_foldLoop_correspondence` (node projection) with `xmssClimb_eq_specFold`.
Conditional on the same per-step advance `hstep`, range hypothesis `hD`, and initial-node
relation `hR`.  This is the STEP-2 "model root = spec root piece" equality, modulo the two
isolated residuals carried in `hstep`/`hR`. -/
theorem xmssClimb_model_node
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (seed treeAdrs : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx → MerkleClimbRel nodeVar idxVar s a →
        MerkleClimbRel nodeVar idxVar
          (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (merkleSpecStep seed treeAdrs auth idx a))
    (state : RuntimeState) (mIdx node h fuel : Nat)
    (hD : ∀ i, h ≤ i → i < h + fuel → MerkleClimbData auth cdAt i)
    (hR : MerkleClimbRel nodeVar idxVar state (mIdx, node)) :
    wordNormalize (lookupValue
        (ClimbLoop.foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
          state h fuel).bindings nodeVar)
      = xmssClimb seed treeAdrs fuel h mIdx node auth := by
  have hrel := merkleClimb_foldLoop_correspondence nodeVar idxVar adrsBaseVar authPtrVar
    seed treeAdrs auth cdAt hstep state (mIdx, node) h fuel hD hR
  rw [xmssClimb_eq_specFold]
  exact hrel.node

/-- Exact-node companion to `xmssClimb_model_node`: the model node binding itself,
not only its EVM normalization, is the spec `xmssClimb` result. -/
theorem xmssClimbRaw_model_node
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (seed treeAdrs : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx → MerkleClimbRawRel nodeVar idxVar s a →
        MerkleClimbRawRel nodeVar idxVar
          (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (merkleSpecStep seed treeAdrs auth idx a))
    (state : RuntimeState) (mIdx node h fuel : Nat)
    (hD : ∀ i, h ≤ i → i < h + fuel → MerkleClimbData auth cdAt i)
    (hR : MerkleClimbRawRel nodeVar idxVar state (mIdx, node)) :
    lookupValue
        (ClimbLoop.foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
          state h fuel).bindings nodeVar
      = xmssClimb seed treeAdrs fuel h mIdx node auth := by
  have hrel := merkleClimbRaw_foldLoop_correspondence nodeVar idxVar adrsBaseVar authPtrVar
    seed treeAdrs auth cdAt hstep state (mIdx, node) h fuel hD hR
  rw [xmssClimb_eq_specFold]
  exact hrel.node

/-- **`forsClimb_model_node`** — FORS loop lift.  Under the FIPS 205 layout the
per-level FORS address is `h`-dependent (`i <<< (18 - h)`), so this is a direct
`foldLoop_invariant_cond` instantiation over `ClimbKit.stepForsMerkle` and
`forsSpecStep`, folded to the named C13 `forsClimb` spec function. -/
theorem forsClimb_model_node
    (seed i t0 l0 : Nat) (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx → MerkleClimbRel "node" "pathIdx" s a →
        MerkleClimbRel "node" "pathIdx"
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (forsSpecStep seed i t0 l0 auth idx a))
    (state : RuntimeState) (pathIdx node h fuel : Nat)
    (hD : ∀ idx, h ≤ idx → idx < h + fuel → MerkleClimbData auth cdAt idx)
    (hR : MerkleClimbRel "node" "pathIdx" state (pathIdx, node)) :
    wordNormalize (lookupValue
        (ClimbLoop.foldLoop "h" SphincsMinusVerifiers.ClimbKit.stepForsMerkle
          state h fuel).bindings "node")
      = SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i t0 l0 fuel h pathIdx node auth := by
  have hrel := ClimbLoop.foldLoop_invariant_cond "h"
    SphincsMinusVerifiers.ClimbKit.stepForsMerkle
    (forsSpecStep seed i t0 l0 auth) (MerkleClimbRel "node" "pathIdx")
    (MerkleClimbData auth cdAt) hstep state (pathIdx, node) h fuel hD hR
  rw [forsClimb_eq_specFold]
  exact hrel.node

/-! ## 6c. STEP-3 frame-carrying loop lift: whole-loop `MerkleClimbFrame` ↔
`specFold`/`xmssClimb`.

The STEP-2 lift above threads the *bare* `MerkleClimbRel` through the engine, so its
per-step premise `hstep` must be supplied with the full static frame baked into each
hypothesis instance — the frame is *not* carried by the invariant, so it cannot be
reused across iterations.  The STEP-3 lift threads the *frame* `MerkleClimbFrame`
itself as the loop invariant, so the static frame (adrs/auth bindings, seed cell,
selector, calldata image, name-distinctness) is available at *every* iteration's
`hstep`.  Combined with `MerkleClimbFrame_h_inject` (frame survives the `"h"` rebind)
and `MerkleClimbFrame_step` (frame preserved by one `stepMerkle`), the per-step premise
now reduces to exactly the *data-level* facts (`h1..h6val`/`StepDataObligations`/parity)
at the `h`-injected state — the same residual the STEP-2 lift had, but now with the
frame no longer a separate obligation. -/

/-- **`merkleClimbFrame_foldLoop_correspondence`** — STEP-3 loop lift.
`foldLoop_invariant_cond` specialised with `R = MerkleClimbFrame …`,
`specStep = merkleSpecStep`, `D = MerkleClimbData auth cdAt`, `step = stepMerkle`: the
whole climb loop advances the *frame* `MerkleClimbFrame` together with
`ClimbLoop.specFold`, gated on the frame-shaped per-step advance `hstep` and the range
hypothesis (`xmss_climb_data_range`/`fors_climb_data_range`).  Pure instantiation of the
engine; no new evaluation, no axioms.  Unlike the bare-relation STEP-2 lift, the static
frame rides along the invariant, so each `hstep` instance receives it for free. -/
theorem merkleClimbFrame_foldLoop_correspondence
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx →
        MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
          pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
        MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
          pkSeed pkRoot message sig seed treeAdrs merklePtr
          (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (merkleSpecStep seed treeAdrs auth idx a))
    (state : RuntimeState) (a : Nat × Nat) (index remaining : Nat)
    (hD : ∀ i, index ≤ i → i < index + remaining → MerkleClimbData auth cdAt i)
    (hR : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
            pkSeed pkRoot message sig seed treeAdrs merklePtr state a) :
    MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
      pkSeed pkRoot message sig seed treeAdrs merklePtr
      (ClimbLoop.foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
        state index remaining)
      (ClimbLoop.specFold (merkleSpecStep seed treeAdrs auth) a index remaining) :=
  ClimbLoop.foldLoop_invariant_cond "h"
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
    (merkleSpecStep seed treeAdrs auth)
    (MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
      pkSeed pkRoot message sig seed treeAdrs merklePtr)
    (MerkleClimbData auth cdAt) hstep state a index remaining hD hR

/-- **`xmssClimbFrame_model_node`** — STEP-3 climb-correspondence equality threaded
through the *frame*.  Same conclusion as `xmssClimb_model_node` (model node binding
after the whole `"h"` climb loop EVM-normalises to the spec `xmssClimb` root), but the
loop invariant is `MerkleClimbFrame`, so the per-step premise `hstep` enjoys the static
frame at each iteration.  The node projection goes through `MerkleClimbFrame.toRel` then
`MerkleClimbRel.node`.  Conditional on the frame-shaped per-step advance `hstep`, range
`hD`, and initial-frame `hR`.  Axiom-clean. -/
theorem xmssClimbFrame_model_node
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx →
        MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
          pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
        MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
          pkSeed pkRoot message sig seed treeAdrs merklePtr
          (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (merkleSpecStep seed treeAdrs auth idx a))
    (state : RuntimeState) (mIdx node h fuel : Nat)
    (hD : ∀ i, h ≤ i → i < h + fuel → MerkleClimbData auth cdAt i)
    (hR : MerkleClimbFrame nodeVar idxVar adrsBaseVar authPtrVar
            pkSeed pkRoot message sig seed treeAdrs merklePtr state (mIdx, node)) :
    wordNormalize (lookupValue
        (ClimbLoop.foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
          state h fuel).bindings nodeVar)
      = xmssClimb seed treeAdrs fuel h mIdx node auth := by
  have hframe := merkleClimbFrame_foldLoop_correspondence nodeVar idxVar adrsBaseVar
    authPtrVar pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt
    hstep state (mIdx, node) h fuel hD hR
  rw [xmssClimb_eq_specFold]
  exact hframe.toRel.node

/-- **`forsClimbFrame_model_node`** — frame-carrying FORS loop lift over
`ClimbKit.stepForsMerkle` / `forsSpecStep`, returning the named C13 `forsClimb`
root expression.  The frame's `adrsBaseVar` slot carries the hoisted
`"forsBase"` binding (its value `forsBase` is the FIPS `adrsForsBase`). -/
theorem forsClimbFrame_model_node
    (pkSeed pkRoot message sig : ByteArray)
    (seed i t0 l0 forsBase merklePtr : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes) (cdAt : Nat → Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        MerkleClimbData auth cdAt idx →
        MerkleClimbFrame "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed forsBase merklePtr s a →
        MerkleClimbFrame "node" "pathIdx" "forsBase" "authPtr"
          pkSeed pkRoot message sig seed forsBase merklePtr
          (SphincsMinusVerifiers.ClimbKit.stepForsMerkle
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (forsSpecStep seed i t0 l0 auth idx a))
    (state : RuntimeState) (pathIdx node h fuel : Nat)
    (hD : ∀ idx, h ≤ idx → idx < h + fuel → MerkleClimbData auth cdAt idx)
    (hR : MerkleClimbFrame "node" "pathIdx" "forsBase" "authPtr"
            pkSeed pkRoot message sig seed forsBase merklePtr
            state (pathIdx, node)) :
    wordNormalize (lookupValue
        (ClimbLoop.foldLoop "h" SphincsMinusVerifiers.ClimbKit.stepForsMerkle
          state h fuel).bindings "node")
      = SphincsMinusVerifierSpec.C13Concrete.forsClimb seed i t0 l0 fuel h pathIdx node auth := by
  have hframe := ClimbLoop.foldLoop_invariant_cond "h"
    SphincsMinusVerifiers.ClimbKit.stepForsMerkle
    (forsSpecStep seed i t0 l0 auth)
    (MerkleClimbFrame "node" "pathIdx" "forsBase" "authPtr"
      pkSeed pkRoot message sig seed forsBase merklePtr)
    (MerkleClimbData auth cdAt) hstep state (pathIdx, node) h fuel hD hR
  rw [forsClimb_eq_specFold]
  exact hframe.toRel.node

/-! ## 6d. Memory-frame loop adapters. -/

/-- If one branchless-Merkle step preserves a memory-cell value, then a full
literal-count Merkle climb loop preserves that memory-cell value.  This is the
memory-frame analogue of the node/index relational climb lifts above. -/
theorem merkleFold_preserves_memory_val_of_step
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (addr n : Nat)
    (hstep : ∀ s,
      ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar s).world.memory addr).val
        = (s.world.memory addr).val)
    (state : RuntimeState) :
    ((foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
        { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
        0 (wordNormalize n)).world.memory addr).val
      = (state.world.memory addr).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val "h"
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar) addr hstep
    { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
    0 (wordNormalize n)]

/-- Bounded-index variant of `merkleFold_preserves_memory_val_of_step`: the
per-step premise sees the concrete Merkle height being bound to `"h"`, matching
call sites where the memory frame is proved only for loop-indexed states. -/
theorem merkleFold_preserves_memory_val_bound
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (addr n : Nat)
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (state : RuntimeState) :
    ((foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
        { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
        0 (wordNormalize n)).world.memory addr).val
      = (state.world.memory addr).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_bound "h"
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar) addr hstep
    { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
    0 (wordNormalize n)]

/-- Range-gated variant of `merkleFold_preserves_memory_val_of_step`: callers may
provide a predicate only for the executed Merkle heights `[0, wordNormalize n)`.
This keeps site-specific calldata/auth-path obligations out of the generic loop
adapter while still threading the memory frame through the whole climb. -/
theorem merkleFold_preserves_memory_val_range
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (addr n : Nat)
    (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (state : RuntimeState)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize n → D i) :
    ((foldLoop "h" (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar)
        { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
        0 (wordNormalize n)).world.memory addr).val
      = (state.world.memory addr).val := by
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "h"
    (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar) addr D hstep
    { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
    0 (wordNormalize n) hD]

/-- Statement-level version of `merkleFold_preserves_memory_val_of_step` for the
literal-count `"h"` Merkle climb statement used by FORS and XMSS. -/
theorem execStmt_forEach_h_merkleClimb_preserves_memory_val_of_step
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (addr n : Nat)
    (hstep : ∀ s,
      ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar s).world.memory addr).val
        = (s.world.memory addr).val)
    (state s' : RuntimeState)
    (h : execStmt [] state
        (.forEach "h" (.literal n)
          (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar)) = .continue s') :
    (s'.world.memory addr).val = (state.world.memory addr).val := by
  have hExec := ClimbLoop.execStmt_forEach_merkleClimb
    "h" nodeVar idxVar adrsBaseVar authPtrVar n state
  rw [hExec] at h
  injection h with hs'
  subst s'
  exact merkleFold_preserves_memory_val_of_step
    nodeVar idxVar adrsBaseVar authPtrVar addr n hstep state

/-- Statement-level bounded-index memory-frame adapter for the literal-count
`"h"` Merkle climb statement used by FORS and XMSS. -/
theorem execStmt_forEach_h_merkleClimb_preserves_memory_val_bound
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (addr n : Nat)
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (state s' : RuntimeState)
    (h : execStmt [] state
        (.forEach "h" (.literal n)
          (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar)) = .continue s') :
    (s'.world.memory addr).val = (state.world.memory addr).val := by
  have hExec := ClimbLoop.execStmt_forEach_merkleClimb
    "h" nodeVar idxVar adrsBaseVar authPtrVar n state
  rw [hExec] at h
  injection h with hs'
  subst s'
  exact merkleFold_preserves_memory_val_bound
    nodeVar idxVar adrsBaseVar authPtrVar addr n hstep state

/-- Statement-level range-gated memory-frame adapter for the literal-count `"h"`
Merkle climb statement used by FORS and XMSS. -/
theorem execStmt_forEach_h_merkleClimb_preserves_memory_val_range
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (addr n : Nat)
    (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((stepMerkle nodeVar idxVar adrsBaseVar authPtrVar
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (state s' : RuntimeState)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize n → D i)
    (h : execStmt [] state
        (.forEach "h" (.literal n)
          (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar)) = .continue s') :
    (s'.world.memory addr).val = (state.world.memory addr).val := by
  have hExec := ClimbLoop.execStmt_forEach_merkleClimb
    "h" nodeVar idxVar adrsBaseVar authPtrVar n state
  rw [hExec] at h
  injection h with hs'
  subst s'
  exact merkleFold_preserves_memory_val_range
    nodeVar idxVar adrsBaseVar authPtrVar addr n D hstep state hD

/-! ## 6e. FORS statement-level memory-frame adapters.

The FIPS FORS inner climb statement is `.forEach "h" (.literal n)
ClimbKit.forsClimbBody` (the `forsAdrs`-instantiated body), so the
`merkleClimbBody`-shaped adapters in §6d do not dispatch on it.  These are the
same three foldLoop reductions over `ClimbKit.stepForsMerkle`, dispatched via
`ClimbLoop.execStmt_forEach_forsClimb`. -/

/-- Statement-level memory-frame adapter for the FIPS FORS climb statement. -/
theorem execStmt_forEach_h_forsClimb_preserves_memory_val_of_step
    (addr n : Nat)
    (hstep : ∀ s,
      ((SphincsMinusVerifiers.ClimbKit.stepForsMerkle s).world.memory addr).val
        = (s.world.memory addr).val)
    (state s' : RuntimeState)
    (h : execStmt [] state
        (.forEach "h" (.literal n) SphincsMinusVerifiers.ClimbKit.forsClimbBody)
        = .continue s') :
    (s'.world.memory addr).val = (state.world.memory addr).val := by
  rw [ClimbLoop.execStmt_forEach_forsClimb "h" n state] at h
  injection h with hs'
  subst s'
  rw [ClimbLoop.foldLoop_preserves_memory_val "h"
    SphincsMinusVerifiers.ClimbKit.stepForsMerkle addr hstep
    { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
    0 (wordNormalize n)]

/-- Statement-level bounded-index memory-frame adapter for the FIPS FORS climb
statement. -/
theorem execStmt_forEach_h_forsClimb_preserves_memory_val_bound
    (addr n : Nat)
    (hstep : ∀ (s : RuntimeState) (idx : Nat),
      ((SphincsMinusVerifiers.ClimbKit.stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (state s' : RuntimeState)
    (h : execStmt [] state
        (.forEach "h" (.literal n) SphincsMinusVerifiers.ClimbKit.forsClimbBody)
        = .continue s') :
    (s'.world.memory addr).val = (state.world.memory addr).val := by
  rw [ClimbLoop.execStmt_forEach_forsClimb "h" n state] at h
  injection h with hs'
  subst s'
  rw [ClimbLoop.foldLoop_preserves_memory_val_bound "h"
    SphincsMinusVerifiers.ClimbKit.stepForsMerkle addr hstep
    { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
    0 (wordNormalize n)]

/-- Statement-level range-gated memory-frame adapter for the FIPS FORS climb
statement. -/
theorem execStmt_forEach_h_forsClimb_preserves_memory_val_range
    (addr n : Nat) (D : Nat → Prop)
    (hstep : ∀ (s : RuntimeState) (idx : Nat), D idx →
      ((SphincsMinusVerifiers.ClimbKit.stepForsMerkle
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory addr).val
        = (s.world.memory addr).val)
    (state s' : RuntimeState)
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize n → D i)
    (h : execStmt [] state
        (.forEach "h" (.literal n) SphincsMinusVerifiers.ClimbKit.forsClimbBody)
        = .continue s') :
    (s'.world.memory addr).val = (state.world.memory addr).val := by
  rw [ClimbLoop.execStmt_forEach_forsClimb "h" n state] at h
  injection h with hs'
  subst s'
  rw [ClimbLoop.foldLoop_preserves_memory_val_range "h"
    SphincsMinusVerifiers.ClimbKit.stepForsMerkle addr D hstep
    { state with bindings := bindValue state.bindings "h" (wordNormalize 0) }
    0 (wordNormalize n) hD]

/-! ## 7. Axiom audit. -/

#print axioms StepDataObligations.intro
#print axioms StepDataObligations.seed
#print axioms StepDataObligations.adr
#print axioms StepDataObligations.sib
#print axioms stepMerkle_memory
#print axioms stepMerkle_node_binding
#print axioms stepMerkle_idx_binding
#print axioms stepMerkle_sibling_reread_eq
#print axioms stepMerkle_node_read_eq
#print axioms wordNormalize_maskN
#print axioms wordNormalize_wordOfHash16
#print axioms sibling_correspondence_of_bytes
#print axioms seed_correspondence_of_bytes
#print axioms uint256_or_val
#print axioms merkle_address_word
#print axioms MerkleClimbRel.intro
#print axioms MerkleClimbRel.idx
#print axioms MerkleClimbRel.node
#print axioms merkleSpecStep_snd_normalized
#print axioms MerkleClimbRawRel.intro
#print axioms MerkleClimbRawRel.idx
#print axioms MerkleClimbRawRel.node
#print axioms MerkleClimbRawRel.node_norm
#print axioms MerkleClimbRawRel.toRel
#print axioms MerkleClimbRawRel_of_pair
#print axioms MerkleClimbRel_of_pair
#print axioms MerkleClimbData_iff
#print axioms merkleClimbData_to_sib
#print axioms stepDataObligations_of_calldata
#print axioms sibling_load_eq_maskN
#print axioms address_assembly_eq
#print axioms MerkleClimbRel_step
#print axioms StepDataObligationsW
#print axioms stepMerkleA_memory
#print axioms stepMerkleA_node_binding
#print axioms stepMerkleA_idx_binding
#print axioms stepMerkleA_node_value_spec_even
#print axioms stepMerkleA_node_value_spec_odd
#print axioms stepMerkleA_node_eq_specStep_even
#print axioms stepMerkleA_node_eq_specStep_odd
#print axioms stepMerkleA_idx_eq_specStep
#print axioms stepMerkleA_eq_merkleSpecStep_even
#print axioms stepMerkleA_eq_merkleSpecStep_odd
#print axioms stepMerkleA_eq_merkleSpecStep
#print axioms MerkleClimbRelA_step
#print axioms stepMerkleA_selector_calldata
#print axioms stepMerkleA_binding_frozen
#print axioms stepMerkleA_mem_zero
#print axioms stepMerkleA_mem_val_of_ne
#print axioms stepMerkleA_mem_zero_of_parity
#print axioms stepMerkleA_mem_zero_val_of_parity
#print axioms MerkleClimbFrameA_step
#print axioms ForsClimbRel_step
#print axioms stepMerkle_node_value_spec_even
#print axioms stepMerkle_node_value_spec_odd
#print axioms stepMerkle_node_eq_specStep_even
#print axioms stepMerkle_node_eq_specStep_odd
#print axioms stepMerkle_idx_eq_specStep
#print axioms stepMerkle_eq_merkleSpecStep_even
#print axioms stepMerkle_eq_merkleSpecStep_odd
#print axioms stepMerkle_eq_merkleSpecStep
#print axioms merkle_hmem_even
#print axioms merkle_hmem_odd
#print axioms merkle_maskedKeccak_value
#print axioms merkle_keccak_value_even
#print axioms merkle_keccak_value_odd
#print axioms merkleScratchWords_eq_spec_even
#print axioms merkleScratchWords_eq_spec_odd
#print axioms merkle_keccak_value_spec_even
#print axioms merkle_keccak_value_spec_odd
#print axioms xmssClimb_eq_specFold
#print axioms parentIdx_shiftRight
#print axioms merkle_offsets_even
#print axioms merkle_offsets_odd
#print axioms merkleClimbData_of_frozenCalldata
#print axioms climb_calldata_read_eq_frozen
#print axioms xmss_climb_data_range
#print axioms fors_climb_data_range
#print axioms fors_climb_data_range_getD
#print axioms merkleClimb_foldLoop_correspondence
#print axioms merkleClimbRaw_foldLoop_correspondence
#print axioms xmssClimb_model_node
#print axioms xmssClimbRaw_model_node
#print axioms forsClimb_model_node
#print axioms calldataloadWord_lt_of_ge4
#print axioms merkle_sibling_read_frozen
#print axioms MerkleClimbFrame.toRel
#print axioms stepMerkle_selector_calldata
#print axioms stepMerkle_binding_frozen
#print axioms stepMerkle_mem_zero
#print axioms stepMerkle_mem_val_of_ne
#print axioms stepMerkle_mem_zero_of_parity
#print axioms stepMerkle_mem_zero_val_of_parity
#print axioms eval_parentIdx_shr
#print axioms eval_selector_shl
#print axioms eval_childOffset_xor
#print axioms MerkleClimbFrame_step
#print axioms MerkleClimbFrame_h_inject
#print axioms MerkleClimbFrame_hstep
#print axioms merkleClimbFrame_foldLoop_correspondence
#print axioms xmssClimbFrame_model_node
#print axioms forsClimbFrame_model_node
#print axioms merkleFold_preserves_memory_val_of_step
#print axioms merkleFold_preserves_memory_val_bound
#print axioms merkleFold_preserves_memory_val_range
#print axioms execStmt_forEach_h_merkleClimb_preserves_memory_val_of_step
#print axioms execStmt_forEach_h_merkleClimb_preserves_memory_val_bound
#print axioms execStmt_forEach_h_merkleClimb_preserves_memory_val_range
#print axioms execStmt_forEach_h_forsClimb_preserves_memory_val_of_step
#print axioms execStmt_forEach_h_forsClimb_preserves_memory_val_bound
#print axioms execStmt_forEach_h_forsClimb_preserves_memory_val_range

end SphincsMinusVerifiers.ClimbMemFrameMerkle
