/-
  SegmentS2R — the R-word byte-correspondence sub-brick for S2.

  `SegmentS2.s2_digest_mkC13State` reduced the entire S2 obligation to a single
  named hypothesis `hR`: the model's first 32-byte calldata word, masked with
  `N_MASK`, equals the spec's high-16-byte read `wordOfHash16 (read16 sig 0)`.

  This file discharges `hR` unconditionally and re-exports the S2 headline with
  no remaining hypotheses.  The proof has three reusable bricks, all standalone
  and axiom-clean (`[propext, Classical.choice, Quot.sound]`):

  * `baToNatBE_toArray` — `ByteArray.foldl` over a list-backed array is the
    corresponding `List.foldl` (the only ByteArray↔List fold conversion needed
    for the whole bridge; shared by every future signature read).
  * `land_nmask` — the high-half mask identity
    `Nat.land (H*2^128 + L) N_MASK = H*2^128` for 128-bit `H`, `L`.
  * `bytesToWords_head_split` — the 32-byte big-endian word splits as
    `Hsum*2^128 + Lsum` with `Hsum = baToNatBE (read16 sig 0)`.
-/
import SphincsMinusVerifiers.SegmentS2
import Mathlib.Data.Nat.Bitwise

namespace SphincsMinusVerifiers.SegmentS2R

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifierSpec.C13Concrete
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentS2
open SphincsMinusVerifiers.ClimbKit (N_MASK)
open Compiler.Proofs.YulGeneration
open Compiler.Constants (evmModulus)

/-! ## 0. `ByteArray.foldl` is the `List.foldl` of its backing data. -/

/-- The internal `ByteArray.foldlM` loop coincides with `Array.foldlM`'s loop on
the backing `.data`, by induction on the fuel. -/
theorem ba_loop_eq (f : Nat → UInt8 → Nat) (bs : ByteArray) (stop : Nat)
    (hb : stop ≤ bs.size) (ha : stop ≤ bs.data.size) :
    ∀ (i j : Nat) (acc : Nat),
    ByteArray.foldlM.loop (m := Id) (fun x1 x2 => pure (f x1 x2)) bs stop hb i j acc
      = Array.foldlM.loop (m := Id) (fun x1 x2 => pure (f x1 x2)) bs.data stop ha i j acc := by
  intro i
  induction i with
  | zero => intro j acc; rfl
  | succ i ih =>
    intro j acc
    unfold ByteArray.foldlM.loop Array.foldlM.loop
    by_cases hlt : j < stop
    · simp only [hlt, dif_pos]
      have : bs[j] = bs.data[j]'(Nat.lt_of_lt_of_le hlt ha) := rfl
      rw [this]
      exact ih (j + 1) _
    · simp only [hlt, dif_neg, not_false_iff]

/-- `ByteArray.foldl` reduces to `Array.foldl` on the backing `.data`. -/
theorem ba_foldl_eq (f : Nat → UInt8 → Nat) (init : Nat) (bs : ByteArray) :
    bs.foldl f init = bs.data.foldl f init := by
  simp only [ByteArray.foldl, Id.run, ByteArray.foldlM, Array.foldl, Array.foldlM]
  rw [dif_pos (Nat.le_refl _), dif_pos (Nat.le_refl _)]
  exact ba_loop_eq f bs bs.size (Nat.le_refl _) (Nat.le_refl _) _ 0 init

/-- `baToNatBE` of a list-backed `ByteArray` is the corresponding `List.foldl`. -/
theorem baToNatBE_toArray (l : List UInt8) :
    baToNatBE ⟨l.toArray⟩ = l.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  unfold baToNatBE
  rw [ba_foldl_eq]
  simp [List.foldl_toArray']

/-! ## 1. Big-endian digit-fold algebra. -/

/-- Pulling the initial accumulator out of a base-256 big-endian fold. -/
theorem be_fold_init (g : Nat → Nat) (L : List Nat) (init : Nat) :
    L.foldl (fun acc j => acc * 256 + g j) init
      = init * 256 ^ L.length + L.foldl (fun acc j => acc * 256 + g j) 0 := by
  induction L generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (init * 256 + g a), ih (0 * 256 + g a)]
    ring

/-- A base-256 big-endian fold of `n` digits (each `< 256`) is `< 256^n`. -/
theorem be_fold_lt (g : Nat → Nat) (hg : ∀ j, g j < 256) (L : List Nat) (init a : Nat)
    (hi : init < 256 ^ a) :
    L.foldl (fun acc j => acc * 256 + g j) init < 256 ^ (a + L.length) := by
  induction L generalizing init a with
  | nil => simpa using hi
  | cons x t ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hrw : a + (t.length + 1) = (a + 1) + t.length := by ring
    rw [hrw]
    apply ih (init * 256 + g x) (a + 1)
    calc init * 256 + g x < init * 256 + 256 := by have := hg x; omega
      _ = (init + 1) * 256 := by ring
      _ ≤ 256 ^ a * 256 := Nat.mul_le_mul_right _ hi
      _ = 256 ^ (a + 1) := by rw [pow_succ]

/-! ## 2. The high-half mask identity. -/

/-- `N_MASK` keeps exactly the high 128 bits: for 128-bit halves `H`, `L`,
`(H·2^128 + L) &&& N_MASK = H·2^128`. -/
theorem land_nmask (H L : Nat) (hH : H < 2 ^ 128) (hL : L < 2 ^ 128) :
    Nat.land (H * 2 ^ 128 + L) N_MASK = H * 2 ^ 128 := by
  have hmask : N_MASK = (2 ^ 128 - 1) * 2 ^ 128 := by decide
  rw [hmask]
  have hand : Nat.land (H * 2 ^ 128 + L) ((2 ^ 128 - 1) * 2 ^ 128)
      = (H * 2 ^ 128 + L) &&& ((2 ^ 128 - 1) * 2 ^ 128) := rfl
  rw [hand]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
      Nat.testBit_two_pow_sub_one, mul_comm H (2 ^ 128),
      Nat.testBit_two_pow_mul_add H hL i]
  by_cases h : i < 128
  · simp [h, Nat.not_le.mpr h]
  · push_neg at h
    simp only [Nat.not_lt.mpr h, if_false]
    rcases Nat.lt_or_ge (i - 128) 128 with hlo | hhi
    · simp [hlo, h, Bool.and_comm]
    · have hf : H.testBit (i - 128) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hH (Nat.pow_le_pow_right (by norm_num) hhi))
      simp [hf]

/-- `wordOfHash16` is already in the high half of the EVM word, so masking with
`N_MASK` leaves it unchanged. -/
theorem wordOfHash16_land_nmask (b : ByteArray) :
    Nat.land (wordOfHash16 b) N_MASK = wordOfHash16 b := by
  unfold wordOfHash16
  have hH : baToNatBE b % 2 ^ 128 < 2 ^ 128 :=
    Nat.mod_lt _ (by decide : 0 < 2 ^ 128)
  have hL : 0 < 2 ^ 128 := by decide
  simpa using land_nmask (baToNatBE b % 2 ^ 128) 0 hH hL

/-! ## 3. The 32-byte word splits into high/low 16-byte halves. -/

/-- A byte digit of `sig` (`sig[j]` or `0` past the end), as a `Nat`. -/
private def bAt (sig : ByteArray) (j : Nat) : Nat := (sig[j]?.getD 0).toNat

private theorem bAt_lt (sig : ByteArray) (j : Nat) : bAt sig j < 256 := by
  unfold bAt; exact (sig[j]?.getD 0).toNat_lt_size

/-- The high 16-byte read `baToNatBE (read16 sig 0)` is the base-256 fold of the
first 16 byte digits. -/
theorem read16_eq_fold (sig : ByteArray) :
    baToNatBE (read16 sig 0)
      = (List.range 16).foldl (fun acc j => acc * 256 + bAt sig j) 0 := by
  unfold read16
  rw [baToNatBE_toArray, List.foldl_map]
  simp only [Nat.zero_add, bAt]

/-- The model's first 32-byte big-endian calldata word is the base-256 fold of
the first 32 byte digits. -/
theorem bytesToWords_head_eq_fold (sig : ByteArray) :
    (bytesToWords sig).getD 0 0
      = (List.range 32).foldl (fun acc j => acc * 256 + bAt sig j) 0 := by
  unfold bytesToWords
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : 0 < (sig.size + 31) / 32
  · rw [List.getElem?_range h]
    simp only [Option.map_some, Option.getD_some, Nat.mul_zero, Nat.zero_add, bAt]
  · push_neg at h
    have hz : (sig.size + 31) / 32 = 0 := Nat.le_zero.mp h
    have hs : sig.size = 0 := by
      have hd := (Nat.div_eq_zero_iff (a := sig.size + 31) (b := 32)).mp hz
      omega
    rw [hz, List.range_zero]
    simp only [List.getElem?_nil, Option.map_none, Option.getD_none]
    symm
    have hb : ∀ j, bAt sig j = 0 := by
      intro j; unfold bAt
      rw [getElem?_neg]; · rfl
      · omega
    clear h hz
    have : ∀ (init : Nat), init = 0 →
        (List.range 32).foldl (fun acc j => acc * 256 + bAt sig j) init = 0 := by
      intro init hi
      induction (List.range 32) generalizing init with
      | nil => simpa using hi
      | cons a t ih => apply ih; simp [hb, hi]
    exact this 0 rfl

/-- The 32-byte word `W = Hsum·2^128 + Lsum` with `Hsum` the high 16-byte read
and both halves `< 2^128`. -/
theorem bytesToWords_head_split (sig : ByteArray) :
    ∃ Hsum Lsum,
      (bytesToWords sig).getD 0 0 = Hsum * 2 ^ 128 + Lsum
      ∧ Hsum = baToNatBE (read16 sig 0)
      ∧ Hsum < 2 ^ 128 ∧ Lsum < 2 ^ 128 := by
  set g : Nat → Nat := fun j => bAt sig j with hg
  have hrange : List.range 32 = List.range 16 ++ (List.range 16).map (· + 16) := rfl
  refine ⟨(List.range 16).foldl (fun acc j => acc * 256 + g j) 0,
          (List.range 16).foldl (fun acc j => acc * 256 + g (j + 16)) 0, ?_, ?_, ?_, ?_⟩
  · rw [bytesToWords_head_eq_fold, hrange, List.foldl_append, List.foldl_map]
    rw [be_fold_init (fun j => g (j + 16)) (List.range 16)]
    simp only [List.length_range]
    have : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
    rw [this]
  · rw [read16_eq_fold]
  · have := be_fold_lt g (fun j => bAt_lt sig j) (List.range 16) 0 0 (by norm_num)
    simpa using this
  · have := be_fold_lt (fun j => g (j + 16)) (fun j => bAt_lt sig (j + 16))
      (List.range 16) 0 0 (by norm_num)
    simpa using this

/-! ## 4. The R-word correspondence. -/

/-- **R byte-correspondence (raw).**  The first masked 32-byte calldata word of
`sig` equals the spec's high-16-byte read.  `< 2^256` bound exposed for the
wrapper collapse. -/
theorem R_correspondence (sig : ByteArray) :
    Nat.land ((bytesToWords sig).getD 0 0) N_MASK = wordOfHash16 (read16 sig 0)
    ∧ (bytesToWords sig).getD 0 0 < 2 ^ 256 := by
  obtain ⟨Hsum, Lsum, hW, hH, hHlt, hLlt⟩ := bytesToWords_head_split sig
  have hWlt : (bytesToWords sig).getD 0 0 < 2 ^ 256 := by
    rw [hW]
    calc Hsum * 2 ^ 128 + Lsum
        < Hsum * 2 ^ 128 + 2 ^ 128 := by omega
      _ = (Hsum + 1) * 2 ^ 128 := by ring
      _ ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul_right _ hHlt
      _ = 2 ^ 256 := by norm_num
  refine ⟨?_, hWlt⟩
  rw [hW, land_nmask Hsum Lsum hHlt hLlt]
  unfold wordOfHash16
  rw [← hH, Nat.mod_eq_of_lt hHlt]

/-! ## 5. The aligned calldata read collapses to the head word. -/

/-- `calldataload(164)` over the frozen `mkC13State` calldata image returns the
first signature data word (mod `2^256`) — `164 = 4 + 32·5` is aligned to data
word `0`, past the 5 ABI-head words. -/
theorem calldataload_head (pkSeed pkRoot message sig : ByteArray) :
    calldataloadWord (mkC13State pkSeed pkRoot message sig).selector
        (mkC13State pkSeed pkRoot message sig).world.calldata
        (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_data_offset")
      = (bytesToWords sig).getD 0 0 % evmModulus := by
  show calldataloadWord 0
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig) 164
    = (bytesToWords sig).getD 0 0 % evmModulus
  unfold calldataloadWord
  norm_num
  rw [List.getElem?_append_right (by simp [headWords])]
  simp [headWords]

/-! ## 6. Discharging `hR` and the unconditional S2 headline. -/

/-- **The bridge hypothesis `hR`, discharged.**  Exactly the named hypothesis of
`SegmentS2.s2StoreVals_mkC13State` / `s2_digest_mkC13State`, now a theorem. -/
theorem mkC13State_hR (pkSeed pkRoot message sig : ByteArray) :
    wordNormalize (Verity.Core.Uint256.and
        (calldataloadWord (mkC13State pkSeed pkRoot message sig).selector
          (mkC13State pkSeed pkRoot message sig).world.calldata
          (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_data_offset"))
        (wordNormalize N_MASK)).val
      = wordOfHash16 (read16 sig 0) := by
  obtain ⟨hLand, hWlt⟩ := R_correspondence sig
  have hNlt : N_MASK < 2 ^ 256 := by decide
  have hwo : wordOfHash16 (read16 sig 0) < 2 ^ 256 := wordOfHash16_lt (read16 sig 0)
  have hm : evmModulus = 2 ^ 256 := rfl
  rw [calldataload_head]
  -- collapse the Uint256/coercion/wordNormalize wrappers down to `Nat.land … N_MASK`
  simp only [Verity.Core.Uint256.and, MemoryKit.coe_val_eq_wordNormalize,
    wordNormalize_eq_mod, hm, Nat.mod_mod_of_dvd _ (dvd_refl _)]
  rw [Nat.mod_eq_of_lt hWlt, Nat.mod_eq_of_lt hNlt, hLand, Nat.mod_eq_of_lt hwo]

/-- **The unconditional S2 headline.**  `SegmentS2.s2_digest_mkC13State` with its
sole hypothesis `hR` discharged by `mkC13State_hR`: the H_msg block run from the
frozen `mkC13State` entry binds `"digest"` to the spec's `hMsgC13` internal
keccak, with no remaining hypotheses. -/
theorem s2_digest_mkC13State_final (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (s2Step (mkC13State pkSeed pkRoot message sig)).bindings "digest"
      = keccakWords [ wordOfHash16 pkSeed, wordOfHash16 pkRoot, wordOfHash16 (read16 sig 0),
          baToNatBE message % wordMod, hMsgPad ] :=
  s2_digest_mkC13State pkSeed pkRoot message sig (mkC13State_hR pkSeed pkRoot message sig)

/-! ## 7. Axiom audit. -/

#print axioms baToNatBE_toArray
#print axioms land_nmask
#print axioms wordOfHash16_land_nmask
#print axioms read16_eq_fold
#print axioms bytesToWords_head_split
#print axioms R_correspondence
#print axioms calldataload_head
#print axioms mkC13State_hR
#print axioms s2_digest_mkC13State_final

end SphincsMinusVerifiers.SegmentS2R
