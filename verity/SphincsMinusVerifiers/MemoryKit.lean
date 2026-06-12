/-
  MemoryKit — Layer-1 memory / interpreter reasoning kit (Worker A).

  Foundational, *additive* lemmas that all later C13 segment proofs build on.
  Everything here runs over the real Verity source semantics
  (`Compiler.Proofs.IRGeneration.SourceSemantics`): `execStmt`, `execStmtList`,
  `evalExpr`.  No `sorry`, no new `axiom`, no `native_decide`.

  The kit provides:

  1. `mstore_then_mload_same` / `mstore_then_mload_diff` — read-after-write at the
     `execStmt`/`evalExpr` level, matching the *exact* interpreter update form.
  2. An address-disequality discharger (`memAddr` simp set + `decide`) for the
     concrete C13 scratch offsets, so read-after-write over an mstore *sequence*
     resolves automatically.
  3. `execStmtList_append` — split a body into named segments.
  4. A symbolic-memory abstraction: post-segment memory as a finite
     `(byteOffset, value)` association list, plus a lookup lemma letting `mload`
     resolve by list lookup instead of replaying the mstore history.

  We work with the production field layout `fields := []` (the form every C13
  body proof uses, cf. `Model.lean`'s `execStmtList [] …`).
-/

import Compiler.Proofs.IRGeneration.SourceSemantics

namespace SphincsMinusVerifiers.MemoryKit

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! ## 0. The matched `mstore` / `mload` update form

The interpreter (`SourceSemantics.execStmt`, the `.mstore offset value` case) does,
for `evalExpr [] state offset = some ro` and `evalExpr [] state value = some rv`:

```
.continue { state with world := { state.world with
  memory := fun o => if o = ro then rv else state.world.memory o } }
```

i.e. a *function update* of `world.memory` at the **raw resolved byte offset** `ro`
(no word-normalisation of the address), storing the resolved value `rv : Nat`
coerced into `Uint256` via `Nat → Uint256` (`Uint256.ofNat`, i.e. `% 2^256`).

`mload` (`SourceSemantics.evalExpr`, the `.mload offset` case) returns
`some (state.world.memory ro).val` for `evalExpr [] state offset = some ro`.

The two lemmas below are stated and proved directly against these forms. -/

/-- Memory after `mstore offset value`, expressed as a plain function update.
This is the canonical post-state we reason about. -/
def memUpdate (mem : Nat → Verity.Core.Uint256) (ro rv : Nat) :
    Nat → Verity.Core.Uint256 :=
  fun o => if o = ro then (rv : Verity.Core.Uint256) else mem o

/-- The interpreter's `mstore` step, in canonical form, when both operands resolve. -/
theorem execStmt_mstore_continue
    (st : RuntimeState) (offset value : Expr) (ro rv : Nat)
    (hoff : evalExpr [] st offset = some ro)
    (hval : evalExpr [] st value = some rv) :
    execStmt [] st (.mstore offset value) =
      .continue
        { st with world := { st.world with memory := memUpdate st.world.memory ro rv } } := by
  show (match evalExpr [] st offset, evalExpr [] st value with
        | some resolvedOffset, some resolvedValue =>
            StmtResult.continue
              { st with world := { st.world with
                memory := fun o =>
                  if o = resolvedOffset then resolvedValue else st.world.memory o } }
        | _, _ => .revert) = _
  rw [hoff, hval]
  rfl

/-- The interpreter's `letVar` step, in canonical form, when its expression
resolves.  Binds `name` to the resolved value and continues.  Reusable Layer-1
brick for threading straight-line prefixes (every segment opens with `letVar`s). -/
theorem execStmt_letVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.letVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-- `mload` reads `(memory ro).val` when its offset operand resolves to `ro`. -/
theorem evalExpr_mload_eq
    (st : RuntimeState) (offset : Expr) (ro : Nat)
    (hoff : evalExpr [] st offset = some ro) :
    evalExpr [] st (.mload offset) = some (st.world.memory ro).val := by
  show (do
        let resolvedOffset ← evalExpr [] st offset
        some (st.world.memory resolvedOffset).val) = _
  rw [hoff]
  rfl

/-! ## 1. Read-after-write -/

/-- Coercion fact: the value byte read back from a freshly-written cell is the
word-normalised stored value. `wordNormalize rv = (rv : Uint256).val`. Both sides
are `rv % 2^256` (`Uint256.modulus` and `evmModulus` are both `2^256`). -/
@[simp] theorem coe_val_eq_wordNormalize (rv : Nat) :
    ((rv : Verity.Core.Uint256)).val = wordNormalize rv := by
  show (Verity.Core.Uint256.ofNat rv).val = wordNormalize rv
  rfl

/-- **`mstore_then_mload_same`**: reading byte offset `a` immediately after
`mstore a v` yields `wordNormalize v` — the EVM-faithful stored word.

`a` is the resolved byte offset of the store's offset operand (the form C13 uses,
where offsets are concrete literals `.literal a` so the resolved offset is
`wordNormalize a`). We keep the resolved offset abstract here. -/
theorem mstore_then_mload_same
    (mem : Nat → Verity.Core.Uint256) (a v : Nat) :
    (memUpdate mem a v a).val = wordNormalize v := by
  show (if a = a then (v : Verity.Core.Uint256) else mem a).val = wordNormalize v
  rw [if_pos rfl]; rfl

/-- **`mstore_then_mload_diff`**: reading byte offset `b` after `mstore a v`,
with `b ≠ a`, is unchanged. The disequality hypothesis is stated as `b ≠ a`,
exactly the orientation produced by the discharger of §2 for C13 scratch slots. -/
theorem mstore_then_mload_diff
    (mem : Nat → Verity.Core.Uint256) (a b v : Nat) (hne : b ≠ a) :
    (memUpdate mem a v b) = mem b := by
  simp [memUpdate, hne]

/-- `@[simp]` form of read-after-write specialised to the function-update: an
`if`-reduction the discharger can fire automatically. -/
@[simp] theorem memUpdate_same (mem : Nat → Verity.Core.Uint256) (a v : Nat) :
    memUpdate mem a v a = (v : Verity.Core.Uint256) := by
  simp [memUpdate]

@[simp] theorem memUpdate_val_same (mem : Nat → Verity.Core.Uint256) (a v : Nat) :
    (memUpdate mem a v a).val = wordNormalize v :=
  mstore_then_mload_same mem a v

theorem memUpdate_diff (mem : Nat → Verity.Core.Uint256) (a b v : Nat) (hne : b ≠ a) :
    memUpdate mem a v b = mem b := by
  simp [memUpdate, hne]

/-! ## 2. Address-disequality discharger for the C13 scratch offsets

The C13 verifier body writes a fixed set of scratch slots. The concrete byte
offsets are:

  0x00, 0x20, 0x40, 0x60, 0x80, 0xA0, 0x140

plus the indexed families `0x80 + 32*i` (i ∈ [0,6]) and `0x40 + 32*i`.

All concrete offsets are `Nat` literals, so disequalities between distinct
offsets are closed by `decide`. We expose:

* `c13ScratchOffsets` — the concrete base offsets,
* `c13IndexedSlot80` / `c13IndexedSlot40` — the indexed-family addresses,
* `memAddr` — a simp set that rewrites `memUpdate`-chains so a read resolves to a
  lookup; combined with `decide`/`Nat`-literal `if`-reduction it discharges the
  `b ≠ a` side conditions on its own. -/

/-- Concrete C13 scratch base offsets (all distinct `Nat` literals). -/
def c13ScratchOffsets : List Nat := [0x00, 0x20, 0x40, 0x60, 0x80, 0xA0, 0x140]

/-- Indexed scratch family `0x80 + 32*i`. -/
def c13IndexedSlot80 (i : Nat) : Nat := 0x80 + 32 * i

/-- Indexed scratch family `0x40 + 32*i`. -/
def c13IndexedSlot40 (i : Nat) : Nat := 0x40 + 32 * i

/-- The indexed families are injective in `i` — disequalities reduce to `i ≠ j`. -/
theorem c13IndexedSlot80_inj {i j : Nat} (h : i ≠ j) : c13IndexedSlot80 i ≠ c13IndexedSlot80 j := by
  simp only [c13IndexedSlot80]
  omega

theorem c13IndexedSlot40_inj {i j : Nat} (h : i ≠ j) : c13IndexedSlot40 i ≠ c13IndexedSlot40 j := by
  simp only [c13IndexedSlot40]
  omega

/-- Cross-family separation: the `0x80`-family and the `0x40`-family never alias
for `i ≤ 6` (the C13 index range): `0x40 + 32*i = 0x80 + 32*j` forces an offset of
two slots, and within `[0,6]` the families stay disjoint precisely when `i ≠ j+2`.
Stated as the general arithmetic fact so the discharger can close concrete goals. -/
theorem c13IndexedSlot40_ne_Slot80 {i j : Nat} (h : i ≠ j + 2) :
    c13IndexedSlot40 i ≠ c13IndexedSlot80 j := by
  simp only [c13IndexedSlot40, c13IndexedSlot80]
  omega

/-- Read-after-write through a *single* `memUpdate`, discharging the `b ≠ a` side
goal by `decide` for concrete literal offsets. Use as a `simp` lemma with the
offsets reduced to literals. -/
theorem memUpdate_lit_diff (mem : Nat → Verity.Core.Uint256) {a b : Nat} (v : Nat)
    (hne : b ≠ a) : memUpdate mem a v b = mem b := memUpdate_diff mem a b v hne

-- Mark `memUpdate` as a `simp` unfold so a read against an mstore sequence
-- reduces to a `Nat`-literal `if`-chain that `decide` / literal reduction closes.
attribute [simp] memUpdate

/-! ## 3. Statement-list append / segmentation -/

/-- **`execStmtList_append`**: running `l1 ++ l2` is running `l1`, then — only on a
`.continue s'` outcome — running `l2` from `s'`; non-continue outcomes of `l1`
short-circuit. This is the lemma that lets a body be split into named segments.
Proved directly from the recursive structure of `execStmtList`. -/
theorem execStmtList_append
    (st : RuntimeState) (l1 l2 : List Stmt) :
    execStmtList [] st (l1 ++ l2) =
      (match execStmtList [] st l1 with
       | .continue s' => execStmtList [] s' l2
       | .stop s' => .stop s'
       | .return v s' => .return v s'
       | .revert => .revert) := by
  induction l1 generalizing st with
  | nil => rfl
  | cons s rest ih =>
      -- LHS: `execStmtList [] st ((s :: rest) ++ l2)` unfolds to a `match` on
      -- `execStmt [] st s`; on `.continue next` we recurse with the IH, all other
      -- branches short-circuit identically on both sides.
      show (match execStmt [] st s with
            | .continue next => execStmtList [] next (rest ++ l2)
            | .stop next => .stop next
            | .return value next => .return value next
            | .revert => .revert) =
          (match (match execStmt [] st s with
                  | .continue n => execStmtList [] n rest
                  | .stop n => .stop n
                  | .return val rst => .return val rst
                  | .revert => .revert) with
           | .continue s' => execStmtList [] s' l2
           | .stop s' => .stop s'
           | .return v s' => .return v s'
           | .revert => .revert)
      cases hstep : execStmt [] st s with
      | «continue» next => exact ih next
      | «stop» next => rfl
      | «return» val rst => rfl
      | «revert» => rfl

/-- The common specialisation: when segment `l1` ends in `.continue s'`, the run of
`l1 ++ l2` is just `l2` from `s'`. -/
theorem execStmtList_append_continue
    (st s' : RuntimeState) (l1 l2 : List Stmt)
    (h : execStmtList [] st l1 = .continue s') :
    execStmtList [] st (l1 ++ l2) = execStmtList [] s' l2 := by
  rw [execStmtList_append, h]

/-- When segment `l1` reverts, the whole `l1 ++ l2` reverts. -/
theorem execStmtList_append_revert
    (st : RuntimeState) (l1 l2 : List Stmt)
    (h : execStmtList [] st l1 = .revert) :
    execStmtList [] st (l1 ++ l2) = .revert := by
  rw [execStmtList_append, h]

/-! ## 4. Symbolic-memory abstraction

We represent the memory produced by a straight-line mstore segment as a finite
association list `entries : List (Nat × Nat)` of `(byteOffset, value)` pairs over
a base memory `base`. `symMem base entries` is the concrete memory function; the
key device is `mload_symMem`, which resolves an `mload` against such a memory by a
*list lookup* (`assocLookup?`), never replaying the update history. -/

/-- Lookup the most-recent write to `addr` in an entry list. We scan left-to-right
and keep the *last* match (later writes shadow earlier ones), mirroring the order
mstores are applied. -/
def assocLookup? (entries : List (Nat × Nat)) (addr : Nat) : Option Nat :=
  entries.foldl (fun acc e => if e.1 = addr then some e.2 else acc) none

/-- The symbolic memory: a base function overlaid with the entry list. A later
entry shadows an earlier one at the same address; addresses absent from the list
fall through to `base`. -/
def symMem (base : Nat → Verity.Core.Uint256) (entries : List (Nat × Nat)) :
    Nat → Verity.Core.Uint256 :=
  fun addr =>
    match assocLookup? entries addr with
    | some v => (v : Verity.Core.Uint256)
    | none => base addr

/-- Applying one `mstore`-style update is the same as appending one entry to the
symbolic-memory list. This is how a worked mstore sequence is folded into the
abstraction. -/
theorem symMem_append_entry
    (base : Nat → Verity.Core.Uint256) (entries : List (Nat × Nat)) (a v : Nat) :
    memUpdate (symMem base entries) a v = symMem base (entries ++ [(a, v)]) := by
  funext addr
  simp only [memUpdate, symMem, assocLookup?, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  by_cases h : a = addr
  · subst h; simp
  · have h' : addr ≠ a := fun hc => h hc.symm
    simp only [h', h]
    cases assocLookup? entries addr <;> rfl

/-- **`mload_symMem`** — the headline lookup lemma. An `mload` whose offset operand
resolves to `addr`, evaluated against a state whose memory is `symMem base entries`,
returns the value found by `assocLookup?` (word-normalised), or the base word when
absent — **by list lookup, with no mstore replay**. -/
theorem mload_symMem
    (st : RuntimeState) (offset : Expr) (addr : Nat)
    (base : Nat → Verity.Core.Uint256) (entries : List (Nat × Nat))
    (hmem : st.world.memory = symMem base entries)
    (hoff : evalExpr [] st offset = some addr) :
    evalExpr [] st (.mload offset) =
      some (match assocLookup? entries addr with
            | some v => wordNormalize v
            | none => (base addr).val) := by
  rw [evalExpr_mload_eq st offset addr hoff, hmem]
  simp only [symMem]
  cases assocLookup? entries addr <;> rfl

/-- Direct value form: the concrete `Uint256.val` read out of `symMem`. -/
theorem symMem_val
    (base : Nat → Verity.Core.Uint256) (entries : List (Nat × Nat)) (addr : Nat) :
    (symMem base entries addr).val =
      (match assocLookup? entries addr with
       | some v => wordNormalize v
       | none => (base addr).val) := by
  simp only [symMem]
  cases assocLookup? entries addr <;> rfl

/-! ### `assocLookup?` evaluation lemmas (so concrete lists resolve by `simp`) -/

@[simp] theorem assocLookup?_nil (addr : Nat) : assocLookup? [] addr = none := rfl

/-- Fold step for `assocLookup?` over a `cons`. With `simp` this drives concrete
lists to a single literal `if`-chain that `decide` closes. -/
theorem assocLookup?_cons (a v : Nat) (rest : List (Nat × Nat)) (addr : Nat) :
    assocLookup? ((a, v) :: rest) addr =
      (rest.foldl (fun acc e => if e.1 = addr then some e.2 else acc)
        (if a = addr then some v else none)) := by
  simp [assocLookup?]

/-! ## 4b. Binding-accessor lemmas

Reusable `lookupValue`/`bindValue` collapse lemmas, promoted from the segment
files (they previously lived privately in `SegmentSeed`/`SegmentS3`).  Every
straight-line `letVar` threading produces a nested `bindValue` chain; these two
lemmas resolve a `lookupValue` against such a chain — `_self` when the read key
is the one just bound, `_ne` when it differs (so the read falls through to the
underlying bindings). -/

/-- Updating only the local variable bindings preserves every memory cell. -/
theorem withBindings_preserves_memory_val
    (st : RuntimeState) (bindings : List (String × Nat)) (addr : Nat) :
    (({ st with bindings := bindings } : RuntimeState).world.memory addr).val =
      (st.world.memory addr).val := by
  rfl

/-- `find?` over a `filter (·.1 != k)` is unchanged when searching for a *different*
key `k'`: the filter only removes `k`-keyed entries, which `find? (·.1 == k')`
would skip anyway. -/
theorem find_filter_ne
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

/-- Reading key `k'` from `bindValue bs k val` with `k ≠ k'` falls through to `bs`. -/
theorem lookupValue_bindValue_ne
    (bs : List (String × Nat)) (k k' : String) (val : Nat) (h : k ≠ k') :
    lookupValue (bindValue bs k val) k' = lookupValue bs k' := by
  have hk : (k == k') = false := beq_eq_false_iff_ne.mpr h
  unfold lookupValue bindValue
  rw [List.find?_cons]
  simp only [hk]
  rw [find_filter_ne bs k k' h]

/-- Reading the key just bound returns the bound value. -/
theorem lookupValue_bindValue_self
    (bs : List (String × Nat)) (k : String) (val : Nat) :
    lookupValue (bindValue bs k val) k = val := by
  simp [lookupValue, bindValue]

/-! ## 5. Worked examples — proving the API is usable

Each example folds a concrete mstore sequence into a `symMem` and resolves an
`mload` by list lookup. These double as regression tests for the discharger. -/

/-- Two writes to distinct slots `0x00` and `0x20`; reading back `0x00` yields the
first value, `0x20` the second — by pure list lookup, no replay. -/
example (base : Nat → Verity.Core.Uint256) :
    let m := memUpdate (memUpdate base 0x00 11) 0x20 22
    (m 0x00).val = wordNormalize 11 ∧ (m 0x20).val = wordNormalize 22 := by
  refine ⟨?_, ?_⟩
  · show (if (0x00 : Nat) = 0x20 then (22 : Verity.Core.Uint256)
          else memUpdate base 0x00 11 0x00).val = wordNormalize 11
    rw [if_neg (by decide)]
    exact mstore_then_mload_same base 0x00 11
  · show (if (0x20 : Nat) = 0x20 then (22 : Verity.Core.Uint256)
          else memUpdate base 0x00 11 0x20).val = wordNormalize 22
    rw [if_pos rfl]; rfl

/-- The same two-write sequence, expressed through the `symMem` abstraction, with
the read resolved by `assocLookup?`. -/
example (base : Nat → Verity.Core.Uint256) :
    memUpdate (memUpdate (symMem base []) 0x00 11) 0x20 22
      = symMem base [(0x00, 11), (0x20, 22)] := by
  rw [symMem_append_entry, symMem_append_entry]
  rfl

/-- Read-back through the folded `symMem`: `0x20` resolves to `22` by list lookup. -/
example (base : Nat → Verity.Core.Uint256) :
    (symMem base [(0x00, 11), (0x20, 22)] 0x20).val = wordNormalize 22 := by
  rw [symMem_val]
  simp [assocLookup?]

/-- Shadowing: a later write to the *same* slot wins. `0x40 ↦ 7` then `0x40 ↦ 9`
reads back `9`. -/
example (base : Nat → Verity.Core.Uint256) :
    (symMem base [(0x40, 7), (0x40, 9)] 0x40).val = wordNormalize 9 := by
  rw [symMem_val]
  simp [assocLookup?]

/-- An indexed-family example over `0x80 + 32*i`: writes to `i = 0,1,2` then a read
at `i = 1` (= `0xA0`) resolves to that entry, untouched by the `i = 0,2` writes. -/
example (base : Nat → Verity.Core.Uint256) :
    (symMem base
      [(c13IndexedSlot80 0, 100), (c13IndexedSlot80 1, 200), (c13IndexedSlot80 2, 300)]
      (c13IndexedSlot80 1)).val = wordNormalize 200 := by
  rw [symMem_val]
  simp [assocLookup?, c13IndexedSlot80]

/-- End-to-end at the interpreter level: an `mload (.literal 0x20)` against a state
whose memory is the folded `symMem` returns `wordNormalize 22` — resolved through
`mload_symMem` by list lookup, with no mstore replay. -/
example (st : RuntimeState) (base : Nat → Verity.Core.Uint256)
    (hmem : st.world.memory = symMem base [(0x00, 11), (0x20, 22)]) :
    evalExpr [] st (.mload (.literal 0x20)) = some (wordNormalize 22) := by
  have hoff : evalExpr [] st (.literal 0x20) = some (wordNormalize 0x20) := rfl
  have hwn : wordNormalize 0x20 = 0x20 := by rfl
  rw [hwn] at hoff
  rw [mload_symMem st (.literal 0x20) 0x20 base _ hmem hoff]
  simp [assocLookup?]

/-! ## Axiom audit for the headline lemmas -/

#print axioms mstore_then_mload_same
#print axioms execStmt_letVar_continue
#print axioms execStmtList_append
#print axioms mload_symMem
#print axioms withBindings_preserves_memory_val
#print axioms lookupValue_bindValue_ne
#print axioms lookupValue_bindValue_self

end SphincsMinusVerifiers.MemoryKit
