/-
  ClimbStepSpec — spec-side single-step unfold lemmas for the two fuel-bounded
  climbs (`xmssClimb`, `forsClimb`) in `C13Concrete`.

  These name the *step combine* function each climb applies per iteration
  (`xmssClimbStep`/`forsClimbStep`) and prove the fuel-`succ` unfold
  (`xmssClimb_succ`/`forsClimb_succ`).  They are the inductive anchors for the open
  Phase-3b data correspondence: the interpreter's `merkleClimbBody` (ClimbKit) writes
  `nodeVar := (keccak 0x00 0x80) & N_MASK` over the branchless-swapped scratch
  `[seed, adrs, child0, child1]`, which is exactly `xmssClimbStep`'s
  `maskN (keccakWords [seed, adrs, node, sibling])` (even) / `[…, sibling, node]`
  (odd).  Matching one interpreter `stepMerkle` to one `xmssClimbStep` — then folding
  by induction on fuel — is the remaining keccak data correspondence.  This file does
  the spec half of the step structure; it asserts nothing about the interpreter and
  evaluates no keccak.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.ClimbStepSpec

open SphincsMinusVerifierSpec (Bytes)
open SphincsMinusVerifierSpec.C13Concrete

set_option maxRecDepth 4000

/-! ## 1. XMSS (hypertree) climb step. -/

/-- One spec XMSS-climb combine: hash `node` with `sibling` under the level-`h+1`
tree address, branchless-swapped by `mIdx`'s parity — left child when even, right
when odd.  This is the exact spec shape the interpreter's `merkleClimbBody`
realises (the `0x40^s`/`0x60^s` swap with `s = (idx & 1) << 5`). -/
def xmssClimbStep (seed treeAdrs : Word) (h mIdx : Nat) (node sibling : Word) : Word :=
  let parentIdx := mIdx / 2
  let adrs := treeAdrs ||| ((h + 1) <<< 32) ||| parentIdx
  if mIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
  else maskN (keccakWords [seed, adrs, sibling, node])

/-- The `h`-th XMSS auth sibling word (spec source: the auth-path byte list). -/
def xmssSibling (auth : List Bytes) (h : Nat) : Word :=
  wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)

/-- **`xmssClimb_succ`** — the spec `xmssClimb` unfolds one fuel step into a single
`xmssClimbStep` applied to the `h`-th sibling, recursing on `fuel`, `h+1`, and the
halved index.  Pure `rfl` against `xmssClimb`'s `succ` branch.  This is the spec-side
induction anchor: a per-step interpreter↔spec match on `xmssClimbStep` folds through
this equation. -/
theorem xmssClimb_succ (seed treeAdrs : Word) (fuel h mIdx : Nat)
    (node : Word) (auth : List Bytes) :
    xmssClimb seed treeAdrs (fuel + 1) h mIdx node auth
      = xmssClimb seed treeAdrs fuel (h + 1) (mIdx / 2)
          (xmssClimbStep seed treeAdrs h mIdx node (xmssSibling auth h)) auth := by
  simp only [xmssClimb, xmssClimbStep, xmssSibling]

/-- The spec climb on zero fuel is the identity (the climb output is the node). -/
theorem xmssClimb_zero (seed treeAdrs : Word) (h mIdx : Nat)
    (node : Word) (auth : List Bytes) :
    xmssClimb seed treeAdrs 0 h mIdx node auth = node := by
  simp only [xmssClimb]

/-! ## 2. FORS climb step. -/

/-- One spec FORS-climb combine: same branchless-swap shape as `xmssClimbStep`, but
under the FIPS 205 FORS-tree address `adrsForsNode idxTree0 idxLeaf0 i h parentIdx`
(the per-level word folds the tree number as `i <<< (18 - h)` per FIPS 205 Alg 17;
the `idxTree0`/`idxLeaf0` digits come from the hypertree-leaf field split). -/
def forsClimbStep (seed i : Word) (idxTree0 idxLeaf0 : Nat) (h pathIdx : Nat)
    (node sibling : Word) : Word :=
  let parentIdx := pathIdx / 2
  let adrs := adrsForsNode idxTree0 idxLeaf0 i h parentIdx
  if pathIdx % 2 == 0 then maskN (keccakWords [seed, adrs, node, sibling])
  else maskN (keccakWords [seed, adrs, sibling, node])

/-- The `h`-th FORS auth sibling word. -/
def forsSibling (auth : List Bytes) (h : Nat) : Word :=
  wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)

/-- **`forsClimb_succ`** — the spec `forsClimb` unfolds one fuel step into a single
`forsClimbStep`.  Pure `rfl` against `forsClimb`'s `succ` branch. -/
theorem forsClimb_succ (seed i : Word) (idxTree0 idxLeaf0 fuel h pathIdx : Nat)
    (node : Word) (auth : List Bytes) :
    forsClimb seed i idxTree0 idxLeaf0 (fuel + 1) h pathIdx node auth
      = forsClimb seed i idxTree0 idxLeaf0 fuel (h + 1) (pathIdx / 2)
          (forsClimbStep seed i idxTree0 idxLeaf0 h pathIdx node (forsSibling auth h)) auth := by
  simp only [forsClimb, forsClimbStep, forsSibling]

/-- The spec FORS climb on zero fuel is the identity. -/
theorem forsClimb_zero (seed i : Word) (idxTree0 idxLeaf0 h pathIdx : Nat)
    (node : Word) (auth : List Bytes) :
    forsClimb seed i idxTree0 idxLeaf0 0 h pathIdx node auth = node := by
  simp only [forsClimb]

/-! ## 3. FORS node-address decomposition.

Under the FIPS 205 layout the per-level FORS address depends on the loop level
`h` (`i <<< (18 - h)` folds the tree number into the 19-bit `word3`), so the
FORS climb is *not* an XMSS-shaped climb at a fixed base any more (the retired
`forsClimb_eq_xmssClimb` is gone).  Instead, the interpreter-side address
expression (`ClimbKit.forsAdrs`, right-associated `or` chain) is identified
with the spec `adrsForsNode` by re-association. -/

/-- The right-associated interpreter FORS address word is exactly the spec
FORS node address, up to `Nat.lor` associativity. -/
theorem forsBase_node_address (idxTree0 idxLeaf0 i h parentIdx : Nat) :
    adrsForsBase idxTree0 idxLeaf0
        ||| (((h + 1) <<< 32) ||| ((i <<< (18 - h)) ||| parentIdx))
      = adrsForsNode idxTree0 idxLeaf0 i h parentIdx := by
  simp only [adrsForsNode, Nat.lor_assoc]

/-! ## 4. Axiom audit. -/

#print axioms xmssClimb_succ
#print axioms xmssClimb_zero
#print axioms forsClimb_succ
#print axioms forsClimb_zero
#print axioms forsBase_node_address

end SphincsMinusVerifiers.ClimbStepSpec
