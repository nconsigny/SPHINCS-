/-
  SegmentS2 — Layer-2 segment lemma for the C13 H_msg digest block,
  statements 1..9 of `SphincsMinusVerifiers.c13VerifyBody`.

  The nine statements are:

  ```
  1. letVar "seed"   := pkSeed
  2. letVar "root"   := pkRoot
  3. mstore 0x00 seed
  4. letVar "R"      := calldataload(sig_data_offset) & N_MASK
  5. mstore 0x20 root
  6. mstore 0x40 R
  7. mstore 0x60 message
  8. mstore 0x80 0xFF…FF   (the hMsgPad literal)
  9. letVar "digest" := keccak256(0x00, 0xA0)
  ```

  After these statements the local `"digest"` is bound to the interpreter's
  computed keccak of memory `[0x00, 0xA0)`.  The goal is to show that, over the
  REAL Verity source interpreter, this digest equals the spec's
  `C13Concrete.keccakWords` over the five input words (seed, root, R, message,
  pad) — the value `hMsgC13` hashes internally.

  The cryptographic crux (`keccakMemorySlice_eq_keccakWords` and its
  `evalExpr`-level form `evalExpr_keccak256_eq_keccakWords`) now lives in
  `KeccakBridge`, proved once and reused.  This file supplies the two reusable
  bricks that connect the `MemoryKit` symbolic-memory abstraction to that
  keccak bridge:

    * `symMem_keccak_hmem` — a `symMem` whose word-aligned cells `off + 32*i`
      look up to values that word-normalise to `ws[i]` satisfies the keccak
      `hmem` hypothesis; and
    * `evalExpr_keccak_symMem` — composing the two, a literal-offset/size
      `keccak256` evaluated over such a `symMem` returns `some (keccakWords ws)`.

  These are the bricks S2 (and S4-finalize, the FORS leaf hashes, and WOTS) all
  consume once the straight-line mstore prefix has been folded into a `symMem`.
  No `sorry`, no `native_decide`, no new `axiom`.
-/

import SphincsMinusVerifiers.Model
import SphincsMinusVerifiers.MemoryKit
import SphincsMinusVerifiers.ClimbKit
import SphincsMinusVerifiers.KeccakBridge
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentS2

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.MemoryKit
open SphincsMinusVerifiers.KeccakBridge
open SphincsMinusVerifiers.ClimbKit (N_MASK execStmtList_cons_continue)
open SphincsMinusVerifierSpec.C13Concrete
open SphincsMinusVerifiers.MkC13State

/-! ## 1. `symMem` satisfies the keccak `hmem` hypothesis.

Given a symbolic memory whose word-aligned cells `off + 32*i` (`i < |ws|`) look
up to values that word-normalise to `ws[i]`, the per-cell value equality the
keccak bridge needs holds.  `symMem_val` reads each cell back as the
word-normalised stored value, so the hypothesis is exactly the per-index
look-up fact. -/

theorem symMem_keccak_hmem
    (base : Nat → Verity.Core.Uint256) (entries : List (Nat × Nat))
    (off : Nat) (ws : List Nat)
    (hlk : ∀ i, (hi : i < ws.length) →
      ∃ v, assocLookup? entries (off + 32 * i) = some v ∧ wordNormalize v = ws[i]) :
    ∀ i, (h : i < ws.length) → (symMem base entries (off + 32 * i)).val = ws[i] := by
  intro i hi
  obtain ⟨v, hv, hn⟩ := hlk i hi
  rw [symMem_val, hv]
  exact hn

/-! ## 2. The composed interpreter keccak over a symbolic memory.

A literal-offset / literal-size `keccak256` expression, evaluated against a state
whose memory is a `symMem` covering the `ws`-words, equals the spec
`keccakWords ws`.  This is `evalExpr_keccak256_eq_keccakWords` (KeccakBridge)
discharged through §1. -/

theorem evalExpr_keccak_symMem
    (st : RuntimeState) (base : Nat → Verity.Core.Uint256)
    (entries : List (Nat × Nat)) (off sz : Nat) (ws : List Nat)
    (hoff : wordNormalize off = off)
    (hsz : wordNormalize sz = 32 * ws.length)
    (hmemEq : st.world.memory = symMem base entries)
    (hlk : ∀ i, (hi : i < ws.length) →
      ∃ v, assocLookup? entries (off + 32 * i) = some v ∧ wordNormalize v = ws[i]) :
    evalExpr [] st (.keccak256 (.literal off) (.literal sz)) = some (keccakWords ws) := by
  apply evalExpr_keccak256_eq_keccakWords st off sz ws hoff hsz
  rw [hmemEq]
  exact symMem_keccak_hmem base entries off ws hlk

/-! ## 3. The H_msg block threading (statements 1..9 of `c13VerifyBody`).

EDSL constructors matching `Model.lean`'s private helpers, so the reconstructed
block is *defeq* to the real statements (machine-checked by `s2Body_eq_slice`). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def p (name : String) : Expr := .param name
private def andE (a b : Expr) : Expr := .bitAnd a b
private def cdload (off : Expr) : Expr := .calldataload off
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val

/-- Statements 1..9 of `c13VerifyBody`: the H_msg digest block (`seed`/`root`
locals, the five scratch mstores `0x00`/`0x20`/`0x40`/`0x60`/`0x80`, and the
`digest` keccak over `[0x00, 0xA0)`). -/
def s2Body : List Stmt :=
  [ .letVar "seed" (p "pkSeed")
  , .letVar "root" (p "pkRoot")
  , mstore 0x00 (v "seed")
  , .letVar "R" (andE (cdload (v "sig_data_offset")) (u N_MASK))
  , mstore 0x20 (v "root")
  , mstore 0x40 (v "R")
  , mstore 0x60 (p "message")
  , mstore 0x80 (u 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
  , .letVar "digest" (keccak 0x00 0xA0) ]

/-- Faithfulness: `s2Body` is *exactly* the first nine algorithmic C13 statements. -/
theorem s2Body_eq_slice : s2Body = c13VerifyBodyTail.take 9 := rfl

/-- The pure transformer for the H_msg block: the `.continue` payload of running
`s2Body`.  Total — every statement is a `letVar`/`mstore` that continues
unconditionally (the keccak in statement 9 is a total memory read). -/
def s2Step (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st s2Body with
  | .continue s' => s'
  | _ => st

/-- **`execS2`** — running the H_msg block over the real interpreter continues to
`s2Step st`.  Each `letVar`/`mstore` threads via its per-statement `.continue`
lemma; the values resolve by `rfl` against the evolving bindings/memory (the
`digest` keccak reduces to the interpreter's `keccakMemorySlice` read). -/
theorem execS2 (st : RuntimeState) :
    execStmtList [] st s2Body = .continue (s2Step st) := by
  unfold s2Step s2Body mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "R" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digest" _ _ rfl)]
  rfl

/-! ## 4. Digest extraction.

The `digest` local is bound by statement 9 (the last statement of `s2Body`) to the
interpreter's keccak over memory `[0x00, 0xA0)`.  Since statement 9 is a `letVar`
(it does not touch memory), the memory underneath the digest read is exactly
`(s2Step st).world.memory`.  So the bound digest is `keccakMemorySlice` of the final
memory — proved by the same per-statement threading as `execS2`. -/

theorem s2Step_digest_raw (st : RuntimeState) :
    lookupValue (s2Step st).bindings "digest"
      = keccakMemorySlice (s2Step st).world.memory 0 0xA0 := by
  unfold s2Step s2Body mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "R" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digest" _ _ rfl)]
  rfl

/-- The H_msg block's final memory as an explicit five-deep `memUpdate` chain over
the incoming memory: the five scratch slots `0x00`/`0x20`/`0x40`/`0x60`/`0x80`
hold, respectively, the `pkSeed`/`pkRoot` words, the masked first-sig word `R`,
the `message` word, and the H_msg pad literal.  The store values are written in
the *resolved* interpreter forms (the `R` slot keeps the
`calldataload &&& N_MASK` shape, since that is the model's literal computation).
Proved by the same per-statement threading as `s2Step_digest_raw`, closing by
`rfl` against the threaded `memUpdate` chain. -/
theorem s2Step_memory (st : RuntimeState) :
    (s2Step st).world.memory =
      memUpdate (memUpdate (memUpdate (memUpdate (memUpdate
        st.world.memory
        0x00 (lookupValue st.bindings "pkSeed"))
        0x20 (lookupValue st.bindings "pkRoot"))
        0x40 (Verity.Core.Uint256.and
                (Compiler.Proofs.YulGeneration.calldataloadWord st.selector st.world.calldata
                  (lookupValue st.bindings "sig_data_offset"))
                (wordNormalize N_MASK)).val)
        0x60 (lookupValue st.bindings "message"))
        0x80 (wordNormalize 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) := by
  unfold s2Step s2Body mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "R" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digest" _ _ rfl)]
  simp only [execStmtList, lookupValue_bindValue_ne, lookupValue_bindValue_self,
    ne_eq, String.reduceEq, not_false_eq_true, wordNormalize_eq_mod,
    Compiler.Constants.evmModulus, Nat.reducePow, Nat.reduceMod]

/-- The five resolved store values written by the H_msg block, in slot order
`0x00`/`0x20`/`0x40`/`0x60`/`0x80` — i.e. the word-normalised cell contents the
keccak reads back.  Slots 0/1/3 are the `pkSeed`/`pkRoot`/`message` binding reads;
slot 2 is the masked first-sig word `R` (`calldataload &&& N_MASK`); slot 4 is the
H_msg pad.  This is the *interpreter-side* word list; the `mkC13State`
instantiation identifies it with the spec's `hMsgC13` input words. -/
def s2StoreVals (st : RuntimeState) : List Nat :=
  [ wordNormalize (lookupValue st.bindings "pkSeed")
  , wordNormalize (lookupValue st.bindings "pkRoot")
  , wordNormalize (Verity.Core.Uint256.and
        (Compiler.Proofs.YulGeneration.calldataloadWord st.selector st.world.calldata
          (lookupValue st.bindings "sig_data_offset"))
        (wordNormalize N_MASK)).val
  , wordNormalize (lookupValue st.bindings "message")
  , wordNormalize 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ]

theorem s2StoreVals_length (st : RuntimeState) : (s2StoreVals st).length = 5 := rfl

/-- **Per-cell read.**  The H_msg block's final memory at word-aligned slot
`0 + 32*i` (`i < 5`) reads back as the `i`-th resolved store value.  Pure
structural consequence of `s2Step_memory` and the distinct-offset discharge. -/
theorem s2Step_cell (st : RuntimeState) (i : Nat) (h : i < (s2StoreVals st).length) :
    ((s2Step st).world.memory (0 + 32 * i)).val = (s2StoreVals st)[i] := by
  rw [s2Step_memory]
  have hlen : (s2StoreVals st).length = 5 := rfl
  rw [hlen] at h
  match i, h with
  | 0, _ => simp [s2StoreVals, memUpdate, coe_val_eq_wordNormalize, wordNormalize_eq_mod,
      Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Nat.reducePow, Nat.reduceMod]
  | 1, _ => simp [s2StoreVals, memUpdate, coe_val_eq_wordNormalize, wordNormalize_eq_mod,
      Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Nat.reducePow, Nat.reduceMod]
  | 2, _ => simp [s2StoreVals, memUpdate, coe_val_eq_wordNormalize, wordNormalize_eq_mod,
      Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Nat.reducePow, Nat.reduceMod]
  | 3, _ => simp [s2StoreVals, memUpdate, coe_val_eq_wordNormalize, wordNormalize_eq_mod,
      Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Nat.reducePow, Nat.reduceMod]
  | 4, _ => simp [s2StoreVals, memUpdate, coe_val_eq_wordNormalize, wordNormalize_eq_mod,
      Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Nat.reducePow, Nat.reduceMod]
  | n + 5, h => omega

/-- **Digest-extraction bridge.**  If the final memory's word-aligned cells
`32*i` (`i < 5`) read back as `ws[i]`, then the `digest` local equals the spec
`keccakWords ws`.  This isolates the remaining S2 obligation to a pure per-cell
memory characterisation (`hcell`) of `(s2Step st).world.memory` — the five scratch
slots `0x00`/`0x20`/`0x40`/`0x60`/`0x80` — which the `mkC13State` instantiation
discharges (with the R-word `calldataload`↔`read16` correspondence as the one
deeper sub-brick, shared with the spec mirror). -/
theorem s2_digest_of_cells (st : RuntimeState) (ws : List Nat)
    (hlen : ws.length = 5)
    (hcell : ∀ i, (h : i < ws.length) →
      ((s2Step st).world.memory (0 + 32 * i)).val = ws[i]) :
    lookupValue (s2Step st).bindings "digest" = keccakWords ws := by
  rw [s2Step_digest_raw st]
  rw [show (0xA0 : Nat) = 32 * ws.length by rw [hlen]]
  exact keccakMemorySlice_eq_keccakWords (s2Step st).world.memory 0 ws hcell

/-- **Headline S2 digest characterisation (interpreter side, fully proved).**  Over
the real Verity interpreter, the H_msg block binds `"digest"` to the spec keccak of
the five resolved store values `s2StoreVals st`.  No hypotheses on `st`: this is the
complete *structural* S2 obligation.  What remains for any concrete entry state is
purely *value identification* — proving `s2StoreVals st` equals the spec's `hMsgC13`
input words; for `mkC13State` that is slots 0/1/3/4 by the resolution lemmas plus the
slot-2 `R` byte-correspondence (`calldataload(164) &&& N_MASK ↔ wordOfHash16 (read16
sig 0)`), the one remaining deeper sub-brick. -/
theorem s2_digest_storeVals (st : RuntimeState) :
    lookupValue (s2Step st).bindings "digest" = keccakWords (s2StoreVals st) :=
  s2_digest_of_cells st (s2StoreVals st) (s2StoreVals_length st) (s2Step_cell st)

/-! ## 4c. Value identification for `mkC13State`.

The headline `s2_digest_storeVals` is a structural identity over any entry state.
For the frozen Phase-1 entry state `mkC13State pkSeed pkRoot message sig`, the five
store values coincide with the spec's `hMsgC13` input words.  Slots 0/1/3/4 follow
from the `mkC13State_resolves_*` binding word-forms plus `wordNormalize` bounds;
slot 2 (`R`) carries the one deeper sub-brick — the calldata-word ↔ 16-byte read
correspondence `calldataload(164) &&& N_MASK = wordOfHash16 (read16 sig 0)` — which
is taken here as a named hypothesis (`hR`) shared with the spec mirror. -/

/-- `wordNormalize` is the identity on any value already below `2^256`. -/
theorem wordNormalize_of_lt {n : Nat} (h : n < 2 ^ 256) : wordNormalize n = n := by
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt h

/-- A 16-byte hash injected into a word's high half is `< 2^256`. -/
theorem wordOfHash16_lt (b : ByteArray) : wordOfHash16 b < 2 ^ 256 := by
  unfold wordOfHash16
  have h : baToNatBE b % (2 ^ 128) < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  calc (baToNatBE b % (2 ^ 128)) * (2 ^ 128)
      < (2 ^ 128) * (2 ^ 128) := Nat.mul_lt_mul_of_pos_right h (by positivity)
    _ = 2 ^ 256 := by rw [← pow_add]

/-- The H_msg block writes the public seed word to scratch slot `0x00` over the
frozen C13 entry state.  This is the seed-cell endpoint consumed by later FORS and
hypertree memory-frame composition. -/
theorem s2Step_seed_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    ((s2Step (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed := by
  rw [s2Step_memory]
  show wordNormalize (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkSeed")
      = wordOfHash16 pkSeed
  rw [show lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkSeed"
      = wordOfHash16 pkSeed from rfl]
  exact wordNormalize_of_lt (wordOfHash16_lt pkSeed)

/-- **S2 value identification (conditional on the R-word sub-brick).**  Over the
frozen `mkC13State` entry, the five resolved store values equal the spec's
`hMsgC13` input word list.  The sole hypothesis `hR` is the deep R-word
correspondence; everything else is binding resolution + `wordNormalize` bounds. -/
theorem s2StoreVals_mkC13State (pkSeed pkRoot message sig : ByteArray)
    (hR : wordNormalize (Verity.Core.Uint256.and
            (Compiler.Proofs.YulGeneration.calldataloadWord
              (mkC13State pkSeed pkRoot message sig).selector
              (mkC13State pkSeed pkRoot message sig).world.calldata
              (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_data_offset"))
            (wordNormalize N_MASK)).val
          = wordOfHash16 (read16 sig 0)) :
    s2StoreVals (mkC13State pkSeed pkRoot message sig)
      = [ wordOfHash16 pkSeed, wordOfHash16 pkRoot, wordOfHash16 (read16 sig 0),
          baToNatBE message % wordMod, hMsgPad ] := by
  simp only [s2StoreVals]
  rw [hR]
  have e0 : wordNormalize (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkSeed")
      = wordOfHash16 pkSeed := wordNormalize_of_lt (wordOfHash16_lt pkSeed)
  have e1 : wordNormalize (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkRoot")
      = wordOfHash16 pkRoot := wordNormalize_of_lt (wordOfHash16_lt pkRoot)
  have e3 : wordNormalize (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "message")
      = baToNatBE message % wordMod := by
    show wordNormalize (baToNatBE message % wordMod) = baToNatBE message % wordMod
    apply wordNormalize_of_lt
    have hwm : wordMod = 2 ^ 256 := rfl
    rw [hwm]
    exact Nat.mod_lt _ (by positivity)
  have e4 : wordNormalize
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = hMsgPad :=
    wordNormalize_of_lt (by norm_num)
  rw [e0, e1, e3, e4]

/-- **S2 headline over the frozen entry (conditional on the R sub-brick).**  The
H_msg block run from `mkC13State` binds `"digest"` to the spec's `hMsgC13` internal
keccak — `keccakWords` of `[wordOfHash16 pkSeed, wordOfHash16 pkRoot,
wordOfHash16 (read16 sig 0), baToNatBE message % wordMod, hMsgPad]`.  This is the
full S2 segment result modulo the single named R-word correspondence `hR`. -/
theorem s2_digest_mkC13State (pkSeed pkRoot message sig : ByteArray)
    (hR : wordNormalize (Verity.Core.Uint256.and
            (Compiler.Proofs.YulGeneration.calldataloadWord
              (mkC13State pkSeed pkRoot message sig).selector
              (mkC13State pkSeed pkRoot message sig).world.calldata
              (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_data_offset"))
            (wordNormalize N_MASK)).val
          = wordOfHash16 (read16 sig 0)) :
    lookupValue (s2Step (mkC13State pkSeed pkRoot message sig)).bindings "digest"
      = keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot, wordOfHash16 (read16 sig 0),
          baToNatBE message % wordMod, hMsgPad ] := by
  rw [s2_digest_storeVals, s2StoreVals_mkC13State pkSeed pkRoot message sig hR]

/-! ## 4d. The `root` binding (the compare's right operand).

Statement 2 of `s2Body` binds `"root"` to `.param "pkRoot"`, and no later statement
touches it (the remaining bindings are `"R"`/`"digest"`, the mstores touch only
`world.memory`).  So after the whole H_msg block the `"root"` local still holds the
resolved `pkRoot` word — the exact right operand of the final `currentNode == root`
compare.  Proved by the same per-statement threading as `s2Step_memory`, reading the
surviving binding off the threaded `bindValue` chain. -/
theorem s2Step_root (st : RuntimeState) :
    lookupValue (s2Step st).bindings "root" = lookupValue st.bindings "pkRoot" := by
  unfold s2Step s2Body mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "seed" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "root" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "R" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digest" _ _ rfl)]
  simp only [execStmtList, lookupValue_bindValue_ne, lookupValue_bindValue_self,
    ne_eq, String.reduceEq, not_false_eq_true]

/-- **`root` value over the frozen entry.**  From `mkC13State`, the surviving
`"root"` binding is exactly the spec's `pkRoot` word `wordOfHash16 pkRoot` — the
value the final compare tests `currentNode` against.  Unconditional (no R sub-brick):
just `s2Step_root` plus `mkC13State_resolves_pkRoot`. -/
theorem s2Step_root_mkC13State (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (s2Step (mkC13State pkSeed pkRoot message sig)).bindings "root"
      = wordOfHash16 pkRoot := by
  rw [s2Step_root]
  rfl

/-! ## 5. Axiom audit. -/

#print axioms symMem_keccak_hmem
#print axioms evalExpr_keccak_symMem
#print axioms s2Body_eq_slice
#print axioms execS2
#print axioms s2Step_digest_raw
#print axioms s2Step_memory
#print axioms s2_digest_of_cells
#print axioms s2StoreVals_length
#print axioms s2Step_cell
#print axioms s2_digest_storeVals
#print axioms s2Step_seed_mkC13State
#print axioms wordNormalize_of_lt
#print axioms wordOfHash16_lt
#print axioms s2StoreVals_mkC13State
#print axioms s2_digest_mkC13State
#print axioms s2Step_root
#print axioms s2Step_root_mkC13State

end SphincsMinusVerifiers.SegmentS2
