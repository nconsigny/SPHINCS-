/-
  ClimbKit — Layer-1 *parametric* lemmas for the two structurally identical
  per-iteration loop bodies that appear inside `c13VerifyBody`:

    * branchless-Merkle-climb (FORS `forEach h<19` and XMSS `forEach h<11`)
    * WOTS chain step (inner `forEach step<steps` of the WOTS chain in layer 3)

  See `SphincsMinusVerifiers/INTERFACE_CONTRACT.md`, heading
  "Reusable shapes (Layer-1 kit targets)". Both lemmas are stated and proved
  directly against the real Verity source semantics
  (`Compiler.Proofs.IRGeneration.SourceSemantics.execStmt`,
  `execStmtList`, `evalExpr`).  No `sorry`, no new `axiom`, no `native_decide`.

  The Merkle body is parametric in the **local-variable names** used by each
  call site (`node`/`pathIdx`/`treeAdrsBase`/`authPtr` in FORS,
  `merkleNode`/`mIdx`/`treeAdrs`/`merklePtr` in XMSS), so a single lemma
  discharges both Merkle climbs. The WOTS chain body shares one fixed naming
  with the C13 model and is proved directly for that naming.

  Each shape lemma takes the form
  ```
  execStmtList [] st (climbBody …) = .continue (stepMerkle … st)
  ```
  with the step transformer defined directly from the interpreter, so the
  lemma is provable by sequential reduction of each `letVar`/`assignVar`/
  `mstore` step — no path case-split (the branchless `xor 0x40 s` /
  `xor 0x60 s` addresses encode the Merkle sibling swap arithmetically).
-/

import SphincsMinusVerifiers.MemoryKit

namespace SphincsMinusVerifiers.ClimbKit

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! ## 0. Shared EDSL constructors (a small private subset mirroring `Model.lean`) -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def xorE (a b : Expr) : Expr := .bitXor a b
private def subE (a b : Expr) : Expr := .sub a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mstoreE (off val : Expr) : Stmt := .mstore off val
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val

/-- The N_MASK constant (high 16 bytes set, low 16 bytes clear), as in the model. -/
def N_MASK : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

/-! ## 1. A small `cons → continue` chaining lemma

Self-contained copy of the head-step combinator (also proved in
`SphincsMinusVerifiers.Model` and as `execStmtList_append_continue` in
`MemoryKit`), kept here so this file only depends on `MemoryKit`. -/

theorem execStmtList_cons_continue
    (st st' : RuntimeState) (s : Stmt) (rest : List Stmt)
    (h : execStmt [] st s = .continue st') :
    execStmtList [] st (s :: rest) = execStmtList [] st' rest := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = execStmtList [] st' rest
  rw [h]

/-! ## 2. The branchless Merkle climb body (parametric in 4 var names)

This is the body of `forEach h<19` (FORS, Model.lean:126-135) and `forEach h<11`
(XMSS, Model.lean:192-201). Both call sites use literally `"sibling"`,
`"parentIdx"`, `"s"` as ephemeral locals, and `"h"` as the loop var; they
differ only in the *four* names for `node`, `pathIdx`, `treeAdrsBase`, and
`authPtr`.

The body sequence (assuming "h" is already bound by the surrounding `forEach`):

```
1. letVar  "sibling"   := (calldataload (authPtr + (4<<h))) & N_MASK
2. letVar  "parentIdx" := pathIdx >> 1
3. mstore  0x20        := treeAdrsBase | ((h+1)<<32) | parentIdx
4. letVar  "s"         := (pathIdx & 1) << 5
5. mstore  (0x40 xor s):= node          ⟵ branchless swap of …
6. mstore  (0x60 xor s):= sibling       ⟵ … the two child slots
7. assign  node        := (keccak 0x00 0x80) & N_MASK
8. assign  pathIdx     := parentIdx
```

When `pathIdx & 1 = 0` we have `s = 0`, so `node → 0x40`, `sibling → 0x60`.
When `pathIdx & 1 = 1` we have `s = 0x20`, so `0x40 xor 0x20 = 0x60` and
`0x60 xor 0x20 = 0x40`: the writes are **swapped** without a branch. -/
def merkleClimbBody (nodeVar idxVar adrsBaseVar authPtrVar : String) : List Stmt := [
  .letVar "sibling"
    (andE (cdload (addE (v authPtrVar) (shlE (u 4) (v "h")))) (u N_MASK)),
  .letVar "parentIdx" (shrE (u 1) (v idxVar)),
  mstore 0x20 (orE (v adrsBaseVar) (orE (shlE (u 32) (addE (v "h") (u 1))) (v "parentIdx"))),
  .letVar "s" (shlE (u 5) (andE (v idxVar) (u 1))),
  mstoreE (xorE (u 0x40) (v "s")) (v nodeVar),
  mstoreE (xorE (u 0x60) (v "s")) (v "sibling"),
  .assignVar nodeVar (andE (keccak 0x00 0x80) (u N_MASK)),
  .assignVar idxVar (v "parentIdx")
]

/-- Pure state transformer for one branchless-Merkle climb iteration.

Defined by projecting the `.continue` payload of the body's interpreter run.
This is total because every statement in `merkleClimbBody` is a
`letVar`/`assignVar`/`mstore`, every operand expression is built only of
literals/local-var lookups/arithmetic/bitwise ops/`calldataload`/`keccak256`
on resolved literal bounds — none of which can return `none` — so
`execStmtList` cannot revert. The lemma `merkleClimbStep` below shows the
projection coincides with the interpreter output. -/
def stepMerkle (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar) with
  | .continue s' => s'
  | _ => st

/-! ### Per-statement `.continue` lemmas

Each statement in the body steps to `.continue` from any state, because every
operand expression deterministically resolves. -/

private theorem step_letVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.letVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

private theorem step_assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

private theorem step_mstore_continue
    (st : RuntimeState) (offset value : Expr) (ro rv : Nat)
    (hoff : evalExpr [] st offset = some ro)
    (hval : evalExpr [] st value = some rv) :
    execStmt [] st (.mstore offset value) =
      .continue
        { st with world := { st.world with
            memory := MemoryKit.memUpdate st.world.memory ro rv } } :=
  MemoryKit.execStmt_mstore_continue st offset value ro rv hoff hval

/-! ### Evaluator skeleton: every Merkle-body expression returns `some _`

The shapes here are *structural*: every operand reduces by definition. We
therefore expose each step's resolved value by a `rfl`-proof. -/

/-- Generic literal evaluation. -/
private theorem evalExpr_literal (st : RuntimeState) (n : Nat) :
    evalExpr [] st (u n) = some (wordNormalize n) := rfl

/-- Generic local-var evaluation. -/
private theorem evalExpr_localVar (st : RuntimeState) (name : String) :
    evalExpr [] st (v name) = some (lookupValue st.bindings name) := rfl

/-! ### The shape lemma -/

set_option maxHeartbeats 2000000 in
/-- **`merkleClimbStep`** — the parametric branchless-Merkle-climb shape
lemma. Running the per-iteration body of either auth-path loop (FORS `h<19`
or XMSS `h<11`) over the real interpreter equals one application of the pure
state transformer `stepMerkle`. No path case-split on `pathIdx & 1`: the swap
is encoded arithmetically in the `xor 0x40 s` / `xor 0x60 s` addresses.

Proved unconditionally (no preconditions on `st`) by chaining 8 per-statement
`.continue` reductions, each of which holds because the corresponding operand
expression always resolves. -/
theorem merkleClimbStep
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) :
    execStmtList [] st (merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar)
      = .continue (stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st) := by
  -- Unfold `stepMerkle` so the `match`-scrutinee on the RHS is the same
  -- `execStmtList` term as on the LHS. Then every `rw` of
  -- `execStmtList_cons_continue` rewrites BOTH sides in lockstep.
  unfold stepMerkle
  -- Expose the body as an explicit 8-cons list with bare `Stmt.mstore`
  -- constructors (the `mstore`/`mstoreE` helper defs are not unfolded by
  -- `rw`, so we inline them here).
  show execStmtList [] st
      ([ .letVar "sibling"
          (andE (cdload (addE (v authPtrVar) (shlE (u 4) (v "h")))) (u N_MASK))
       , .letVar "parentIdx" (shrE (u 1) (v idxVar))
       , Stmt.mstore (u 0x20)
          (orE (v adrsBaseVar) (orE (shlE (u 32) (addE (v "h") (u 1))) (v "parentIdx")))
       , .letVar "s" (shlE (u 5) (andE (v idxVar) (u 1)))
       , Stmt.mstore (xorE (u 0x40) (v "s")) (v nodeVar)
       , Stmt.mstore (xorE (u 0x60) (v "s")) (v "sibling")
       , .assignVar nodeVar (andE (keccak 0x00 0x80) (u N_MASK))
       , .assignVar idxVar (v "parentIdx") ])
      = .continue
        (match execStmtList [] st
            ([ .letVar "sibling"
                (andE (cdload (addE (v authPtrVar) (shlE (u 4) (v "h")))) (u N_MASK))
             , .letVar "parentIdx" (shrE (u 1) (v idxVar))
             , Stmt.mstore (u 0x20)
                (orE (v adrsBaseVar) (orE (shlE (u 32) (addE (v "h") (u 1))) (v "parentIdx")))
             , .letVar "s" (shlE (u 5) (andE (v idxVar) (u 1)))
             , Stmt.mstore (xorE (u 0x40) (v "s")) (v nodeVar)
             , Stmt.mstore (xorE (u 0x60) (v "s")) (v "sibling")
             , .assignVar nodeVar (andE (keccak 0x00 0x80) (u N_MASK))
             , .assignVar idxVar (v "parentIdx") ]) with
         | .continue s' => s' | _ => st)
  -- statement 1: .letVar "sibling"
  rw [execStmtList_cons_continue _ _ _ _
      (step_letVar_continue st "sibling" _ _ rfl)]
  -- statement 2: .letVar "parentIdx"
  rw [execStmtList_cons_continue _ _ _ _
      (step_letVar_continue _ "parentIdx" _ _ rfl)]
  -- statement 3: .mstore 0x20
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  -- statement 4: .letVar "s"
  rw [execStmtList_cons_continue _ _ _ _
      (step_letVar_continue _ "s" _ _ rfl)]
  -- statement 5: .mstore (xor 0x40 s) node
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  -- statement 6: .mstore (xor 0x60 s) sibling
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  -- statement 7: .assignVar nodeVar (and (keccak …) N_MASK)
  rw [execStmtList_cons_continue _ _ _ _
      (step_assignVar_continue _ nodeVar _ _ rfl)]
  -- statement 8: .assignVar idxVar parentIdx
  rw [execStmtList_cons_continue _ _ _ _
      (step_assignVar_continue _ idxVar _ _ rfl)]
  -- empty tail: execStmtList [] _ [] = .continue _, and the `match` reduces
  rfl

/-! ## 2b. Address-parametric Merkle climb (FIPS FORS support)

The FIPS 205 C13 FORS node address carries a per-iteration `i <<< (18 - h)`
term that the XMSS tree address does not have, so the two climbs can no
longer share a body parametric only in *variable names*.  Instead we make
the body parametric in the whole ADRS word **expression** written to `0x20`
(statement 3).  The classic 4-name `merkleClimbBody` above is definitionally
the `xmssAdrs` instantiation (`merkleClimbBody_eq_adrs`), so nothing on the
XMSS side needs re-proving. -/

/-- Merkle climb body parametric in the full ADRS word expression.  `adrsE`
may freely reference the loop variable `"h"`, the body-local `"parentIdx"`,
and any outer bindings (e.g. `"i"`, `"forsBase"`, a tree-address base var) —
they are plain `localVar` lookups at eval time. -/
def merkleClimbBodyA (nodeVar idxVar authPtrVar : String) (adrsE : Expr) : List Stmt := [
  .letVar "sibling"
    (andE (cdload (addE (v authPtrVar) (shlE (u 4) (v "h")))) (u N_MASK)),
  .letVar "parentIdx" (shrE (u 1) (v idxVar)),
  mstore 0x20 adrsE,
  .letVar "s" (shlE (u 5) (andE (v idxVar) (u 1))),
  mstoreE (xorE (u 0x40) (v "s")) (v nodeVar),
  mstoreE (xorE (u 0x60) (v "s")) (v "sibling"),
  .assignVar nodeVar (andE (keccak 0x00 0x80) (u N_MASK)),
  .assignVar idxVar (v "parentIdx")
]

/-- XMSS / pre-FIPS ADRS word: `base ||| ((h+1) <<< 32) ||| parentIdx`. -/
def xmssAdrs (adrsBaseVar : String) : Expr :=
  .bitOr (.localVar adrsBaseVar)
    (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx"))

/-- FIPS 205 C13 FORS ADRS word:
`forsBase ||| ((h+1) <<< 32) ||| (i <<< (18-h)) ||| parentIdx` —
character-for-character the `mstore 0x20` operand of the FORS inner climb in
`Model.lean` and the Yul
`or(forsBase, or(shl(32, add(h,1)), or(shl(sub(18,h), i), parentIdx)))`. -/
def forsAdrs : Expr :=
  .bitOr (.localVar "forsBase")
    (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.bitOr (.shl (.sub (.literal 18) (.localVar "h")) (.localVar "i"))
        (.localVar "parentIdx")))

/-- The classic 4-name body is exactly the XMSS instantiation. -/
theorem merkleClimbBody_eq_adrs (nodeVar idxVar adrsBaseVar authPtrVar : String) :
    merkleClimbBody nodeVar idxVar adrsBaseVar authPtrVar
      = merkleClimbBodyA nodeVar idxVar authPtrVar (xmssAdrs adrsBaseVar) := rfl

/-- Pure state transformer for one address-parametric climb iteration.
Same projection construction as `stepMerkle`. -/
def stepMerkleA (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st (merkleClimbBodyA nodeVar idxVar authPtrVar adrsE) with
  | .continue s' => s'
  | _ => st

/-- The classic 4-name transformer is exactly the XMSS instantiation. -/
theorem stepMerkle_eq_adrs
    (nodeVar idxVar adrsBaseVar authPtrVar : String) (st : RuntimeState) :
    stepMerkle nodeVar idxVar adrsBaseVar authPtrVar st
      = stepMerkleA nodeVar idxVar authPtrVar (xmssAdrs adrsBaseVar) st := rfl

/-- A deterministic evaluator witness for `adrsE`: a total function giving the
resolved value in every state.  Carrying the function (rather than an
existential) keeps the shape lemma's per-statement `rw` steps choice-free, so
the `#print axioms` audit stays at `propext`-level. -/
structure AdrsEval (adrsE : Expr) where
  val : RuntimeState → Nat
  eval : ∀ st : RuntimeState, evalExpr [] st adrsE = some (val st)

/-- The XMSS address word always resolves (every operand is a literal,
local-var lookup, or arithmetic on those — `evalExpr` is total there). -/
def adrsEval_xmss (adrsBaseVar : String) : AdrsEval (xmssAdrs adrsBaseVar) :=
  ⟨fun st => (evalExpr [] st (xmssAdrs adrsBaseVar)).getD 0, fun _ => rfl⟩

/-- The FIPS FORS address word always resolves (same totality argument; the
extra `.sub`/`.shl` operands are total too). -/
def adrsEval_fors : AdrsEval forsAdrs :=
  ⟨fun st => (evalExpr [] st forsAdrs).getD 0, fun _ => rfl⟩

set_option maxHeartbeats 2000000 in
/-- **`merkleClimbStepA`** — address-parametric branchless-Merkle-climb shape
lemma.  Identical to `merkleClimbStep` except statement 3's operand is the
caller-supplied `adrsE`, discharged by the `AdrsEval` witness instead of
`rfl`. -/
theorem merkleClimbStepA
    (nodeVar idxVar authPtrVar : String) (adrsE : Expr)
    (he : AdrsEval adrsE)
    (st : RuntimeState) :
    execStmtList [] st (merkleClimbBodyA nodeVar idxVar authPtrVar adrsE)
      = .continue (stepMerkleA nodeVar idxVar authPtrVar adrsE st) := by
  unfold stepMerkleA
  show execStmtList [] st
      ([ .letVar "sibling"
          (andE (cdload (addE (v authPtrVar) (shlE (u 4) (v "h")))) (u N_MASK))
       , .letVar "parentIdx" (shrE (u 1) (v idxVar))
       , Stmt.mstore (u 0x20) adrsE
       , .letVar "s" (shlE (u 5) (andE (v idxVar) (u 1)))
       , Stmt.mstore (xorE (u 0x40) (v "s")) (v nodeVar)
       , Stmt.mstore (xorE (u 0x60) (v "s")) (v "sibling")
       , .assignVar nodeVar (andE (keccak 0x00 0x80) (u N_MASK))
       , .assignVar idxVar (v "parentIdx") ])
      = .continue
        (match execStmtList [] st
            ([ .letVar "sibling"
                (andE (cdload (addE (v authPtrVar) (shlE (u 4) (v "h")))) (u N_MASK))
             , .letVar "parentIdx" (shrE (u 1) (v idxVar))
             , Stmt.mstore (u 0x20) adrsE
             , .letVar "s" (shlE (u 5) (andE (v idxVar) (u 1)))
             , Stmt.mstore (xorE (u 0x40) (v "s")) (v nodeVar)
             , Stmt.mstore (xorE (u 0x60) (v "s")) (v "sibling")
             , .assignVar nodeVar (andE (keccak 0x00 0x80) (u N_MASK))
             , .assignVar idxVar (v "parentIdx") ]) with
         | .continue s' => s' | _ => st)
  -- statement 1: .letVar "sibling"
  rw [execStmtList_cons_continue _ _ _ _
      (step_letVar_continue st "sibling" _ _ rfl)]
  -- statement 2: .letVar "parentIdx"
  rw [execStmtList_cons_continue _ _ _ _
      (step_letVar_continue _ "parentIdx" _ _ rfl)]
  -- statement 3: .mstore 0x20 adrsE — value resolves via the AdrsEval witness
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl (he.eval _))]
  -- statement 4: .letVar "s"
  rw [execStmtList_cons_continue _ _ _ _
      (step_letVar_continue _ "s" _ _ rfl)]
  -- statement 5: .mstore (xor 0x40 s) node
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  -- statement 6: .mstore (xor 0x60 s) sibling
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  -- statement 7: .assignVar nodeVar (and (keccak …) N_MASK)
  rw [execStmtList_cons_continue _ _ _ _
      (step_assignVar_continue _ nodeVar _ _ rfl)]
  -- statement 8: .assignVar idxVar parentIdx
  rw [execStmtList_cons_continue _ _ _ _
      (step_assignVar_continue _ idxVar _ _ rfl)]
  rfl

/-! ### The C13 FIPS FORS instantiation -/

/-- C13 FORS inner-climb body: the FIPS instantiation used by `Model.lean`'s
`forEach "h" (u 19)` loop (var names `node`/`pathIdx`/`authPtr`). -/
def forsClimbBody : List Stmt :=
  merkleClimbBodyA "node" "pathIdx" "authPtr" forsAdrs

/-- Pure state transformer for one C13 FORS climb iteration. -/
def stepForsMerkle (st : RuntimeState) : RuntimeState :=
  stepMerkleA "node" "pathIdx" "authPtr" forsAdrs st

/-- **`forsClimbStep`** — the C13 FIPS FORS climb shape lemma. -/
theorem forsClimbStep (st : RuntimeState) :
    execStmtList [] st forsClimbBody = .continue (stepForsMerkle st) :=
  merkleClimbStepA _ _ _ _ adrsEval_fors st

/-! ## 3. The WOTS chain per-iteration body (fixed naming)

This is the body of `forEach step<steps` inside the WOTS chain loop
(Model.lean:174-178). Only one C13 call site uses it, so we hard-code its
names: `chainBase`, `digit`, `val`, `step` (and the address slots `0x20`,
`0x40`). The body:

```
1. mstore 0x20 := chainBase | (digit + step)
2. mstore 0x40 := val
3. assign  val := (keccak 0x00 0x60) & N_MASK
```

Note the keccak preimage is the **whole** 96-byte scratch `[0x00, 0x60)`, so
the new `val` depends transitively on the just-written `0x20` (address)
and `0x40` (current val) words, with `0x00` carrying the seed already
materialised before the WOTS climb began. -/
def wotsChainBody : List Stmt := [
  mstore 0x20 (orE (v "chainBase") (addE (v "digit") (v "step"))),
  mstore 0x40 (v "val"),
  .assignVar "val" (andE (keccak 0x00 0x60) (u N_MASK))
]

/-- Pure state transformer for one WOTS chain iteration. Same construction
as `stepMerkle`: project the `.continue` payload of the interpreter run; the
shape lemma `wotsChainStep` shows it coincides with the interpreter. -/
def stepWots (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st wotsChainBody with
  | .continue s' => s'
  | _ => st

set_option maxHeartbeats 1000000 in
/-- **`wotsChainStep`** — the WOTS chain per-iteration shape lemma. Running
the per-step body over the real interpreter equals one application of the
pure state transformer `stepWots`. Proved unconditionally by chaining 3
per-statement `.continue` reductions. -/
theorem wotsChainStep (st : RuntimeState) :
    execStmtList [] st wotsChainBody = .continue (stepWots st) := by
  unfold stepWots
  show execStmtList [] st
      ([ Stmt.mstore (u 0x20) (orE (v "chainBase") (addE (v "digit") (v "step")))
       , Stmt.mstore (u 0x40) (v "val")
       , .assignVar "val" (andE (keccak 0x00 0x60) (u N_MASK)) ])
      = .continue
        (match execStmtList [] st
            ([ Stmt.mstore (u 0x20) (orE (v "chainBase") (addE (v "digit") (v "step")))
             , Stmt.mstore (u 0x40) (v "val")
             , .assignVar "val" (andE (keccak 0x00 0x60) (u N_MASK)) ]) with
         | .continue s' => s' | _ => st)
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (step_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (step_assignVar_continue _ "val" _ _ rfl)]
  rfl

/-! ## 4. Axiom audit for the two headline lemmas -/

#print axioms merkleClimbStep
#print axioms merkleClimbStepA
#print axioms forsClimbStep
#print axioms wotsChainStep

end SphincsMinusVerifiers.ClimbKit
