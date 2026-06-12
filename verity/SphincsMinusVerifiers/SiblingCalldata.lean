/-
  SiblingCalldata — the generalized sibling/auth-word byte-correspondence brick
  ("blocker #20"), the per-step keccak-word fact that discharges the `hsib`
  hypothesis of `ClimbMemFrameMerkle.stepMerkle_node_eq_specStep_*`.

  `SegmentS2R` proved the *offset-0* special case (`R_correspondence`): the first
  masked 32-byte calldata word equals `wordOfHash16 (read16 sig 0)`.  Every Merkle
  / FORS climb step needs the SAME fact at the *auth word's* byte offset: reading
  the calldata word at the signature byte offset `sOff`, masked with `N_MASK`,
  equals `wordOfHash16 (read16 sig sOff)` — the spec's high-16-byte sibling read.

  This file generalizes `SegmentS2R`'s reusable bricks to an arbitrary 32-byte
  *word index* `q` and proves, for any **16-byte-aligned** byte offset
  (`sOff % 16 = 0` — which covers `R`, every FORS secret-key read `16 + 16*i`, and
  every FORS auth read `128 + 304*t + 16*h`), the headline correspondence

    `maskN (calldataloadWord 0 (headWords … ++ bytesToWords sig) (164 + sOff))
       = wordOfHash16 (read16 sig sOff)`.

  The proof case-splits on `sOff % 32 ∈ {0, 16}` (forced by `sOff % 16 = 0`): the
  aligned case reads one whole word, the straddle case reads the low half of word
  `q` (which is exactly `read16 sig sOff`) shifted into the high 128 bits.  Both
  collapse under the high-half mask identity `land_nmask`.  Reuses
  `SegmentS2R.{baToNatBE_toArray, be_fold_init, be_fold_lt, land_nmask}`; no
  byte-fold split algebra is needed for the 16-aligned case.

  No `sorry`, no `native_decide`, no new `axiom`.
-/
import SphincsMinusVerifiers.SegmentS2R

namespace SphincsMinusVerifiers.SiblingCalldata

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifierSpec.C13Concrete
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentS2R
open SphincsMinusVerifiers.ClimbKit (N_MASK)
open Compiler.Proofs.YulGeneration
open Compiler.Constants (evmModulus)

/-! ## 0. A byte digit of `sig` (local copy of `SegmentS2R.bAt`, which is private). -/

/-- A byte digit of `sig` (`sig[j]` or `0` past the end), as a `Nat`. -/
private def bAt (sig : ByteArray) (j : Nat) : Nat := (sig[j]?.getD 0).toNat

private theorem bAt_lt (sig : ByteArray) (j : Nat) : bAt sig j < 256 := by
  unfold bAt; exact (sig[j]?.getD 0).toNat_lt_size

/-! ## 1. Generalized byte-fold bricks (arbitrary offset / word index). -/

/-- The 16-byte read `baToNatBE (read16 sig off)` is the base-256 big-endian fold
of the 16 byte digits starting at `off`. -/
theorem read16_eq_fold (sig : ByteArray) (off : Nat) :
    baToNatBE (read16 sig off)
      = (List.range 16).foldl (fun acc j => acc * 256 + bAt sig (off + j)) 0 := by
  unfold read16
  rw [baToNatBE_toArray, List.foldl_map]
  simp only [bAt]

/-- A fold of all-zero digits is the (zero) accumulator. -/
private theorem fold_zero (f : Nat → Nat) (hf : ∀ j, f j = 0) :
    ∀ (L : List Nat) (init : Nat), init = 0 →
      L.foldl (fun acc j => acc * 256 + f j) init = 0 := by
  intro L
  induction L with
  | nil => intro init hi; simpa using hi
  | cons a t ih => intro init hi; apply ih; simp [hf, hi]

/-- The big-endian value of `bytesToWords sig`'s word `q` is the base-256 fold of
the 32 byte digits `[32*q, 32*q+32)` (zero past the end). -/
theorem bytesToWords_eq_fold (sig : ByteArray) (q : Nat) :
    (bytesToWords sig).getD q 0
      = (List.range 32).foldl (fun acc j => acc * 256 + bAt sig (32 * q + j)) 0 := by
  unfold bytesToWords
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : q < (sig.size + 31) / 32
  · rw [List.getElem?_range h]
    simp only [Option.map_some, Option.getD_some, bAt]
  · push_neg at h
    have hge : sig.size ≤ 32 * q := by
      have h2 : 32 * ((sig.size + 31) / 32) ≤ 32 * q := Nat.mul_le_mul (le_refl 32) h
      omega
    rw [List.getElem?_eq_none (by rw [List.length_range]; exact h)]
    simp only [Option.map_none, Option.getD_none]
    symm
    have hf : ∀ j, bAt sig (32 * q + j) = 0 := by
      intro j; unfold bAt
      rw [getElem?_neg sig (32 * q + j) (by omega)]; rfl
    exact fold_zero (fun j => bAt sig (32 * q + j)) hf (List.range 32) 0 rfl

/-! ## 2. The 32-byte word splits into its two 16-byte halves. -/

/-- `bytesToWords sig`'s word `q` is `H·2^128 + L`, where `H` is the high-16-byte
read `baToNatBE (read16 sig (32*q))` and `L` the low-16-byte read
`baToNatBE (read16 sig (32*q+16))`, both `< 2^128`. -/
theorem word_split (sig : ByteArray) (q : Nat) :
    ∃ H L,
      (bytesToWords sig).getD q 0 = H * 2 ^ 128 + L
      ∧ H = baToNatBE (read16 sig (32 * q))
      ∧ L = baToNatBE (read16 sig (32 * q + 16))
      ∧ H < 2 ^ 128 ∧ L < 2 ^ 128 := by
  set g : Nat → Nat := fun j => bAt sig (32 * q + j) with hg
  have hrange : List.range 32 = List.range 16 ++ (List.range 16).map (· + 16) := rfl
  refine ⟨(List.range 16).foldl (fun acc j => acc * 256 + g j) 0,
          (List.range 16).foldl (fun acc j => acc * 256 + g (j + 16)) 0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bytesToWords_eq_fold, hrange, List.foldl_append, List.foldl_map]
    rw [be_fold_init (fun j => g (j + 16)) (List.range 16)]
    simp only [List.length_range]
    have : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
    rw [this]
  · rw [read16_eq_fold]
  · rw [read16_eq_fold]
    have hfe : (fun (acc j : Nat) => acc * 256 + g (j + 16))
             = (fun (acc j : Nat) => acc * 256 + bAt sig (32 * q + 16 + j)) := by
      funext acc j
      simp only [hg]
      rw [show 32 * q + (j + 16) = 32 * q + 16 + j from by omega]
    rw [hfe]
  · have := be_fold_lt g (fun j => bAt_lt sig (32 * q + j)) (List.range 16) 0 0 (by norm_num)
    simpa using this
  · have := be_fold_lt (fun j => g (j + 16)) (fun j => bAt_lt sig (32 * q + (j + 16)))
      (List.range 16) 0 0 (by norm_num)
    simpa using this

/-! ## 3. The frozen-calldata read at a signature word boundary. -/

/-- The frozen `mkC13State` calldata image: 5 ABI-head words then `bytesToWords
sig`.  Reading data word `5 + n` (past the head) returns `bytesToWords sig`'s
word `n`. -/
theorem cd_getD (pkSeed pkRoot message sig : ByteArray) (n : Nat) :
    (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig).getD (5 + n) 0
      = (bytesToWords sig).getD n 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp [headWords])]
  simp [headWords]

/-! ## 3b. Length-indexed byte read and its general split (for arbitrary offsets). -/

/-- The big-endian value of the `len` byte digits of `sig` starting at byte `off`
(zero past the end). -/
def readBE (sig : ByteArray) (off len : Nat) : Nat :=
  (List.range len).foldl (fun acc j => acc * 256 + bAt sig (off + j)) 0

/-- A `len`-byte big-endian read is `< 256 ^ len`. -/
theorem readBE_lt (sig : ByteArray) (off len : Nat) : readBE sig off len < 256 ^ len := by
  have := be_fold_lt (fun j => bAt sig (off + j)) (fun j => bAt_lt sig (off + j))
    (List.range len) 0 0 (by norm_num)
  simpa [readBE, List.length_range] using this

/-- **General byte-fold split.**  Reading `s + t` bytes at `off` splits into the
high `s` bytes (shifted up by `t` byte positions) plus the low `t` bytes at
`off + s`. -/
theorem readBE_split (sig : ByteArray) (off s t : Nat) :
    readBE sig off (s + t)
      = readBE sig off s * 256 ^ t + readBE sig (off + s) t := by
  unfold readBE
  rw [List.range_add, List.foldl_append, List.foldl_map,
      be_fold_init (fun j => bAt sig (off + (s + j))) (List.range t)]
  simp only [List.length_range]
  have hfe : (fun (acc j : Nat) => acc * 256 + bAt sig (off + (s + j)))
           = (fun (acc j : Nat) => acc * 256 + bAt sig (off + s + j)) := by
    funext acc j
    rw [show off + (s + j) = off + s + j from by omega]
  rw [hfe]

/-! ## 3c. Small div/mod and power identities for the straddle algebra. -/

/-- `2 ^ (8 * k) = 256 ^ k`. -/
private theorem pow8 (k : Nat) : (2 : Nat) ^ (8 * k) = 256 ^ k := by
  rw [pow_mul]; norm_num

private theorem mod_helper (a b m : Nat) (hb : b < m) : (a * m + b) % m = b := by
  rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem div_helper (a b m : Nat) (hm : 0 < m) (hb : b < m) : (a * m + b) / m = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right b a hm, Nat.div_eq_of_lt hb, Nat.zero_add]

/-- Taking a `s + t` byte read mod `256 ^ t` keeps the low `t` bytes (at `off + s`). -/
theorem readBE_split_at (sig : ByteArray) (off s t : Nat) :
    readBE sig off (s + t) % 256 ^ t = readBE sig (off + s) t := by
  rw [readBE_split]
  exact mod_helper _ _ _ (readBE_lt sig (off + s) t)

/-- Dividing a `s + t` byte read by `256 ^ t` keeps the high `s` bytes (at `off`). -/
theorem readBE_split_div (sig : ByteArray) (off s t : Nat) :
    readBE sig off (s + t) / 256 ^ t = readBE sig off s := by
  rw [readBE_split]
  exact div_helper _ _ _ (by positivity) (readBE_lt sig (off + s) t)

/-- A `bytesToWords` entry is exactly the 32-byte big-endian read at its byte start. -/
theorem word_eq_readBE (sig : ByteArray) (q : Nat) :
    (bytesToWords sig).getD q 0 = readBE sig (32 * q) 32 := by
  unfold readBE
  rw [bytesToWords_eq_fold]

/-- A 16-byte big-endian read is exactly `baToNatBE (read16 …)`. -/
theorem readBE_eq_read16 (sig : ByteArray) (off : Nat) :
    readBE sig off 16 = baToNatBE (read16 sig off) := by
  unfold readBE
  rw [read16_eq_fold]

/-- A four-byte big-endian read in the public fold form used by the C13 WOTS+C
count parser. -/
theorem readBE4_eq_fold (sig : ByteArray) (off : Nat) :
    readBE sig off 4 =
      (List.range 4).foldl
        (fun acc j => acc * 256 + ((sig[off + j]?).getD 0).toNat) 0 := by
  rfl

/-! ## 4. The headline correspondence (16-byte-aligned offsets). -/

/-- Word-bound helper: any `bytesToWords` entry is `< evmModulus`. -/
private theorem word_lt_evmModulus (sig : ByteArray) (k : Nat) :
    (bytesToWords sig).getD k 0 < evmModulus := by
  obtain ⟨H, L, hW, _, _, hHlt, hLlt⟩ := word_split sig k
  rw [hW, show evmModulus = 2 ^ 256 from rfl]
  calc H * 2 ^ 128 + L
        < H * 2 ^ 128 + 2 ^ 128 := by omega
      _ = (H + 1) * 2 ^ 128 := by ring
      _ ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul_right _ hHlt
      _ = 2 ^ 256 := by norm_num

set_option maxHeartbeats 1000000 in
/-- Aligned sub-case: `sOff % 32 = 0`. -/
private theorem masked_aligned
    (pkSeed pkRoot message sig : ByteArray) (sOff : Nat) (hs : sOff % 32 = 0) :
    Nat.land
      (calldataloadWord 0
        (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
        (sigDataOffset + sOff)) N_MASK
      = wordOfHash16 (read16 sig sOff) := by
  set cd := headWords pkSeed pkRoot message sig.size ++ bytesToWords sig with hcd
  set k := sOff / 32 with hk
  have hsOff : sOff = 32 * k := by omega
  obtain ⟨H, L, hW, hH, _, hHlt, hLlt⟩ := word_split sig k
  have hWlt : (bytesToWords sig).getD k 0 < evmModulus := word_lt_evmModulus sig k
  have hcl : calldataloadWord 0 cd (sigDataOffset + sOff)
      = (bytesToWords sig).getD k 0 := by
    show calldataloadWord 0 cd (164 + sOff) = _
    unfold calldataloadWord
    rw [if_neg (by omega), if_neg (by omega)]
    -- Zeta-reduce the `let p/q/r` bindings (defeq) so the rewrites below can fire.
    show (if (164 + sOff - 4) % 32 = 0 then
            cd.getD ((164 + sOff - 4) / 32) 0 % evmModulus
          else
            (cd.getD ((164 + sOff - 4) / 32) 0 % evmModulus
                % 2 ^ (8 * (32 - (164 + sOff - 4) % 32))
                * 2 ^ (8 * ((164 + sOff - 4) % 32))
              + cd.getD ((164 + sOff - 4) / 32 + 1) 0 % evmModulus
                / 2 ^ (8 * (32 - (164 + sOff - 4) % 32)))
              % evmModulus) = _
    rw [show (164 + sOff - 4) % 32 = 0 from by omega, if_pos rfl,
        show (164 + sOff - 4) / 32 = 5 + k from by omega,
        hcd, cd_getD, Nat.mod_eq_of_lt hWlt]
  rw [hcl, hW, land_nmask H L hHlt hLlt]
  rw [show (32 : Nat) * k = sOff from hsOff.symm] at hH
  rw [wordOfHash16, ← hH, Nat.mod_eq_of_lt hHlt]

set_option maxHeartbeats 1000000 in
/-- Straddle sub-case: `sOff % 32 = 16`. -/
private theorem masked_straddle
    (pkSeed pkRoot message sig : ByteArray) (sOff : Nat) (hs : sOff % 32 = 16) :
    Nat.land
      (calldataloadWord 0
        (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
        (sigDataOffset + sOff)) N_MASK
      = wordOfHash16 (read16 sig sOff) := by
  set cd := headWords pkSeed pkRoot message sig.size ++ bytesToWords sig with hcd
  set k := sOff / 32 with hk
  have hsOff : sOff = 32 * k + 16 := by omega
  obtain ⟨H, L, hW, _, hL, hHlt, hLlt⟩ := word_split sig k
  have hWlt : (bytesToWords sig).getD k 0 < evmModulus := word_lt_evmModulus sig k
  -- the low part of the straddle read is masked out; only need it `< 2^128`.
  have hlolt : (cd.getD (5 + k + 1) 0 % evmModulus) / 2 ^ 128 < 2 ^ 128 := by
    apply Nat.div_lt_of_lt_mul
    have hb : cd.getD (5 + k + 1) 0 % evmModulus < evmModulus := Nat.mod_lt _ (by norm_num)
    calc cd.getD (5 + k + 1) 0 % evmModulus
          < evmModulus := hb
        _ = 2 ^ 128 * 2 ^ 128 := by rw [show evmModulus = 2 ^ 256 from rfl]; norm_num
  have hcl : calldataloadWord 0 cd (sigDataOffset + sOff)
      = L * 2 ^ 128 + (cd.getD (5 + k + 1) 0 % evmModulus) / 2 ^ 128 := by
    show calldataloadWord 0 cd (164 + sOff) = _
    unfold calldataloadWord
    rw [if_neg (by omega), if_neg (by omega)]
    -- Zeta-reduce the `let p/q/r` bindings (defeq) so the rewrites below can fire.
    show (if (164 + sOff - 4) % 32 = 0 then
            cd.getD ((164 + sOff - 4) / 32) 0 % evmModulus
          else
            (cd.getD ((164 + sOff - 4) / 32) 0 % evmModulus
                % 2 ^ (8 * (32 - (164 + sOff - 4) % 32))
                * 2 ^ (8 * ((164 + sOff - 4) % 32))
              + cd.getD ((164 + sOff - 4) / 32 + 1) 0 % evmModulus
                / 2 ^ (8 * (32 - (164 + sOff - 4) % 32)))
              % evmModulus) = _
    rw [show (164 + sOff - 4) % 32 = 16 from by omega, if_neg (by decide),
        show (164 + sOff - 4) / 32 = 5 + k from by omega,
        show (32 : Nat) - 16 = 16 from rfl, show 8 * 16 = 128 from rfl]
    -- LHS now `((hi % 2^128) * 2^128 + lo'/2^128) % evmModulus`, hi = word k
    rw [hcd, cd_getD, Nat.mod_eq_of_lt hWlt, hW,
        show (H * 2 ^ 128 + L) % 2 ^ 128 = L from by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hLlt]]
    apply Nat.mod_eq_of_lt
    rw [show evmModulus = 2 ^ 256 from rfl]
    calc L * 2 ^ 128 + (cd.getD (5 + k + 1) 0 % evmModulus) / 2 ^ 128
          < L * 2 ^ 128 + 2 ^ 128 := by have := hlolt; omega
        _ = (L + 1) * 2 ^ 128 := by ring
        _ ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul_right _ hLlt
        _ = 2 ^ 256 := by norm_num
  rw [hcl, land_nmask L _ hLlt hlolt]
  rw [show (32 : Nat) * k + 16 = sOff from hsOff.symm] at hL
  rw [wordOfHash16, ← hL, Nat.mod_eq_of_lt hLlt]

/-- **Masked sibling read = `wordOfHash16`.**  For any 16-byte-aligned signature
byte offset `sOff` (`sOff % 16 = 0`), reading the frozen `mkC13State` calldata
word at `sigDataOffset + sOff` and masking with `N_MASK` yields exactly the spec's
high-16-byte read `wordOfHash16 (read16 sig sOff)`.

Covers `R` (`sOff = 0`), every FORS secret-key read (`16 + 16*i`), and every FORS
auth-path read (`128 + 304*t + 16*h`).  Axiom-clean. -/
theorem masked_sig_read_eq_wordOfHash16
    (pkSeed pkRoot message sig : ByteArray) (sOff : Nat) (haligned : sOff % 16 = 0) :
    Nat.land
      (calldataloadWord 0
        (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
        (sigDataOffset + sOff)) N_MASK
      = wordOfHash16 (read16 sig sOff) := by
  -- `sOff % 16 = 0` forces `sOff % 32 ∈ {0, 16}`.
  rcases (show sOff % 32 = 0 ∨ sOff % 32 = 16 by omega) with hs | hs
  · exact masked_aligned pkSeed pkRoot message sig sOff hs
  · exact masked_straddle pkSeed pkRoot message sig sOff hs

/-! ## 4b. The general-offset correspondence (arbitrary byte offsets). -/

set_option maxHeartbeats 1000000 in
/-- **Frozen calldata 32-byte read = big-endian byte read.**  For ANY signature
byte offset `sOff`, the frozen `mkC13State` calldata word at `sigDataOffset + sOff`
is exactly the 32-byte big-endian read `readBE sig sOff 32`.  The aligned case
returns one whole word; the straddle case stitches the low `32 - r` bytes of word
`Q` with the high `r` bytes of word `Q + 1` (`r = sOff % 32`, `Q = sOff / 32`). -/
theorem read32BE_calldata
    (pkSeed pkRoot message sig : ByteArray) (sOff : Nat) :
    calldataloadWord 0
        (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
        (sigDataOffset + sOff)
      = readBE sig sOff 32 := by
  set cd := headWords pkSeed pkRoot message sig.size ++ bytesToWords sig with hcd
  set Q := sOff / 32 with hQ
  set r := sOff % 32 with hr
  have hsOff : sOff = 32 * Q + r := by omega
  show calldataloadWord 0 cd (164 + sOff) = readBE sig sOff 32
  unfold calldataloadWord
  rw [if_neg (by omega), if_neg (by omega)]
  -- Zeta-reduce the `let p/q/r` bindings (defeq) so the rewrites below can fire.
  show (if (164 + sOff - 4) % 32 = 0 then
          cd.getD ((164 + sOff - 4) / 32) 0 % evmModulus
        else
          (cd.getD ((164 + sOff - 4) / 32) 0 % evmModulus
              % 2 ^ (8 * (32 - (164 + sOff - 4) % 32))
              * 2 ^ (8 * ((164 + sOff - 4) % 32))
            + cd.getD ((164 + sOff - 4) / 32 + 1) 0 % evmModulus
              / 2 ^ (8 * (32 - (164 + sOff - 4) % 32)))
            % evmModulus) = readBE sig sOff 32
  rw [show (164 + sOff - 4) % 32 = r from by omega,
      show (164 + sOff - 4) / 32 = 5 + Q from by omega]
  by_cases hr0 : r = 0
  · -- Aligned: read returns the whole word `Q`.
    rw [if_pos hr0, hcd, cd_getD pkSeed pkRoot message sig Q,
        Nat.mod_eq_of_lt (word_lt_evmModulus sig Q), word_eq_readBE sig Q,
        show 32 * Q = sOff from by omega]
  · -- Straddle: stitch low `32-r` bytes of word `Q` with high `r` bytes of word `Q+1`.
    rw [if_neg hr0, hcd, show (5 : Nat) + Q + 1 = 5 + (Q + 1) from rfl,
        cd_getD pkSeed pkRoot message sig Q, cd_getD pkSeed pkRoot message sig (Q + 1),
        Nat.mod_eq_of_lt (word_lt_evmModulus sig Q),
        Nat.mod_eq_of_lt (word_lt_evmModulus sig (Q + 1)),
        word_eq_readBE sig Q, word_eq_readBE sig (Q + 1)]
    have hpow1 : (2 : Nat) ^ (8 * (32 - r)) = 256 ^ (32 - r) := pow8 (32 - r)
    have h32a : readBE sig (32 * Q) 32 = readBE sig (32 * Q) (r + (32 - r)) := by
      rw [show r + (32 - r) = 32 from by omega]
    have h32b : readBE sig (32 * (Q + 1)) 32 = readBE sig (32 * (Q + 1)) (r + (32 - r)) := by
      rw [show r + (32 - r) = 32 from by omega]
    have h32c : readBE sig sOff 32 = readBE sig sOff ((32 - r) + r) := by
      rw [show (32 - r) + r = 32 from by omega]
    have hhi : readBE sig (32 * Q) 32 % 2 ^ (8 * (32 - r))
        = readBE sig (32 * Q + r) (32 - r) := by
      rw [hpow1, h32a, readBE_split_at]
    have hlo : readBE sig (32 * (Q + 1)) 32 / 2 ^ (8 * (32 - r))
        = readBE sig (32 * (Q + 1)) r := by
      rw [hpow1, h32b, readBE_split_div]
    rw [hhi, hlo, pow8 r]
    have htgt : readBE sig sOff 32
        = readBE sig (32 * Q + r) (32 - r) * 256 ^ r + readBE sig (32 * (Q + 1)) r := by
      rw [h32c, readBE_split, hsOff, show 32 * Q + r + (32 - r) = 32 * (Q + 1) from by omega]
    rw [← htgt]
    apply Nat.mod_eq_of_lt
    calc readBE sig sOff 32 < 256 ^ 32 := readBE_lt sig sOff 32
      _ = evmModulus := by rw [show evmModulus = 2 ^ 256 from rfl]; norm_num

/-- The WOTS+C count read shape: shifting the frozen calldata word at signature
offset `sOff` right by 224 bits returns the high four-byte big-endian integer. -/
theorem shr224_calldata_eq_readBE4
    (pkSeed pkRoot message sig : ByteArray) (sOff : Nat) :
    (calldataloadWord 0
        (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
        (sigDataOffset + sOff)) >>> 224
      = readBE sig sOff 4 := by
  rw [read32BE_calldata]
  rw [Nat.shiftRight_eq_div_pow]
  have hsplit : readBE sig sOff 32 =
      readBE sig sOff 4 * 256 ^ 28 + readBE sig (sOff + 4) 28 := by
    rw [show (32 : Nat) = 4 + 28 from rfl, readBE_split]
  rw [hsplit]
  have hpow : (2 : Nat) ^ 224 = 256 ^ 28 := by norm_num
  rw [hpow]
  exact div_helper _ _ _ (by positivity) (readBE_lt sig (sOff + 4) 28)

/-- **Masked sibling read = `wordOfHash16`, for ANY byte offset.**  Generalizes
`masked_sig_read_eq_wordOfHash16` to drop the `sOff % 16 = 0` hypothesis: masking
the frozen calldata word at `sigDataOffset + sOff` with `N_MASK` yields the spec's
high-16-byte read `wordOfHash16 (read16 sig sOff)` for every `sOff` (in particular
the XMSS auth offsets `≡ 4` / `≡ 8 mod 16`).  Axiom-clean. -/
theorem masked_sig_read_eq_wordOfHash16_gen
    (pkSeed pkRoot message sig : ByteArray) (sOff : Nat) :
    Nat.land
      (calldataloadWord 0
        (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
        (sigDataOffset + sOff)) N_MASK
      = wordOfHash16 (read16 sig sOff) := by
  rw [read32BE_calldata]
  have hHlt : readBE sig sOff 16 < 2 ^ 128 := by
    have := readBE_lt sig sOff 16
    rwa [show (256 : Nat) ^ 16 = 2 ^ 128 from by norm_num] at this
  have hLlt : readBE sig (sOff + 16) 16 < 2 ^ 128 := by
    have := readBE_lt sig (sOff + 16) 16
    rwa [show (256 : Nat) ^ 16 = 2 ^ 128 from by norm_num] at this
  have hsplit : readBE sig sOff 32
      = readBE sig sOff 16 * 2 ^ 128 + readBE sig (sOff + 16) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, readBE_split,
        show (256 : Nat) ^ 16 = 2 ^ 128 from by norm_num]
  rw [hsplit, land_nmask _ _ hHlt hLlt, wordOfHash16,
      ← readBE_eq_read16 sig sOff, Nat.mod_eq_of_lt hHlt]

/-! ## 5. Axiom audit. -/

#print axioms read16_eq_fold
#print axioms bytesToWords_eq_fold
#print axioms word_split
#print axioms cd_getD
#print axioms masked_aligned
#print axioms masked_straddle
#print axioms masked_sig_read_eq_wordOfHash16
#print axioms read32BE_calldata
#print axioms shr224_calldata_eq_readBE4
#print axioms masked_sig_read_eq_wordOfHash16_gen

end SphincsMinusVerifiers.SiblingCalldata
