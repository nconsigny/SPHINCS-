/-
  KeccakBridge - the foundational hash bridge for the C13 model-to-spec
  refinement.  Every keccak in the contract is a word-aligned
  `keccak256(offset, 32*k)`; the interpreter models it as

      keccakMemorySlice memory offset (32*k)
        = wordNormalize (byteArrayToNatBE (keccak256 (memorySliceBytesBE …)))

  while the spec kernel `C13Concrete.keccakWords` is

      keccakWords ws = byteArrayToNatBE (keccak256 (ws.foldl (· ++ wordToBytesBE ·) …))

  Both wrap the SAME `KeccakEngine.keccak256` over the SAME big-endian word
  encoding (`wordToBytesBE`) and read the digest back with the SAME
  `byteArrayToNatBE`.  The only gaps are:

    1. the byte preimage equality — `memorySliceBytesBE` (a `range`-indexed
       fold + trailing `.extract`) equals the spec's list fold, provided each
       memory cell `offset + 32*i` holds `ws[i]`; and
    2. the interpreter's outer `wordNormalize` (mod 2^256), harmless because a
       32-byte digest is already `< 2^256`.

  This file discharges piece (1) in full (`memorySliceBytesBE_eq_spec_foldl`)
  and assembles the `wordNormalize`-wrapped bridge
  (`keccakMemorySlice_eq_wordNormalize_keccakWords`).  No `sorry`, no new axiom.
-/

import SphincsMinusVerifierSpec.C13Concrete
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Keccak.SpongeProperties
import Compiler.Constants

namespace SphincsMinusVerifiers.KeccakBridge

open Compiler.Proofs.IRGeneration.SourceSemantics
  (wordToBytesBE memorySliceBytesBE keccakMemorySlice wordNormalize RuntimeState evalExpr)
open SphincsMinusVerifierSpec.C13Concrete (keccakWords keccakBytes)
open KeccakEngine (byteArrayToNatBE keccak256 keccak256_size)

/-! ## 1. `wordToBytesBE` always encodes to exactly 32 bytes. -/

theorem wordToBytesBE_size (w : Nat) : (wordToBytesBE w).size = 32 := by
  simp [wordToBytesBE, ByteArray.size, Array.size_toArray]

/-! ## 2. A right-fold of `wordToBytesBE`-encoded words has predictable size. -/

theorem foldl_append_size {α : Type _} (g : α → ByteArray)
    (hg : ∀ a, (g a).size = 32) (l : List α) (init : ByteArray) :
    (l.foldl (fun acc a => acc ++ g a) init).size = init.size + 32 * l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (init ++ g a), ByteArray.size_append, hg a]
    omega

/-! ## 3. `extract 0 size` over a fully-covered array is the identity. -/

theorem extract_self (a : ByteArray) : a.extract 0 a.size = a := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_size

/-! ## 4. The byte-preimage equality (the reusable core). -/

theorem memorySliceBytesBE_eq_spec_foldl
    (memory : Nat → Verity.Core.Uint256) (offset : Nat) (ws : List Nat)
    (hmem : ∀ i, (h : i < ws.length) → (memory (offset + 32 * i)).val = ws[i]) :
    memorySliceBytesBE memory offset (32 * ws.length)
      = ws.foldl (fun acc w => acc ++ wordToBytesBE w) ByteArray.empty := by
  -- Rewrite `ws` as the explicit `range`-indexed list of memory cells.
  have hws : ws = (List.range ws.length).map (fun i => (memory (offset + 32 * i)).val) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      exact (hmem i (by simpa using h₁)).symm
  unfold memorySliceBytesBE
  -- The number of covered words is exactly `ws.length`.
  have hn : (32 * ws.length + 31) / 32 = ws.length := by omega
  simp only [hn]
  -- The covering fold has size `32 * ws.length`, so the trailing extract is identity.
  have hsize :
      ((List.range ws.length).foldl
        (fun acc i => acc ++ wordToBytesBE (memory (offset + 32 * i)).val)
        ByteArray.empty).size = 32 * ws.length := by
    rw [foldl_append_size (fun i => wordToBytesBE (memory (offset + 32 * i)).val)
          (fun _ => wordToBytesBE_size _) (List.range ws.length) ByteArray.empty]
    simp
  rw [← hsize, extract_self]
  -- Collapse the `range` fold against the spec list fold.
  conv_rhs => rw [hws]
  rw [List.foldl_map]

/-! ## 5. The `wordNormalize`-wrapped hash bridge. -/

theorem keccakMemorySlice_eq_wordNormalize_keccakWords
    (memory : Nat → Verity.Core.Uint256) (offset : Nat) (ws : List Nat)
    (hmem : ∀ i, (h : i < ws.length) → (memory (offset + 32 * i)).val = ws[i]) :
    keccakMemorySlice memory offset (32 * ws.length) = wordNormalize (keccakWords ws) := by
  unfold keccakMemorySlice keccakWords keccakBytes
  rw [memorySliceBytesBE_eq_spec_foldl memory offset ws hmem]

/-! ## 6. The digest is `< 2^256`, so the outer `wordNormalize` is the identity.

  The interpreter's hash carries an extra `wordNormalize` (mod `2^256`).  A
  keccak-256 digest is exactly 32 bytes, so its big-endian value is `< 2^256`
  and the mod is harmless.  We prove this from scratch: a hand-rolled bound on
  `ByteArray.foldlM.loop` (no library lemma relates `ByteArray.foldl` to a
  list/Array fold), then `keccak256_size` to fix the length at 32. -/

/-- The accumulator of `byteArrayToNatBE`'s loop stays `< 256^(k+i)`: starting
from `b < 256^k`, each of the remaining `i` bytes multiplies by 256 and adds a
byte `< 256`. -/
private theorem loop_natBE_lt (ba : ByteArray) :
    ∀ (i j : Nat) (b : Nat),
      (∀ k, b < 256 ^ k →
        Id.run (ByteArray.foldlM.loop (m := Id) (fun acc byte => acc * 256 + byte.toNat)
          ba ba.size (Nat.le_refl _) i j b) < 256 ^ (k + i)) := by
  intro i j b
  induction i, j, b using ByteArray.foldlM.loop.induct (stop := ba.size) with
  | case1 j b hlt =>
    intro k hb
    unfold ByteArray.foldlM.loop
    simp [hlt, Id.run]
    simpa using hb
  | case2 j b hlt i' ih =>
    intro k hb
    unfold ByteArray.foldlM.loop
    simp only [hlt, Id.run, ↓reduceDIte]
    have hbyte : ba[j].toNat < 256 := by have := ba[j].toNat_lt; simpa using this
    have hnew : b * 256 + ba[j].toNat < 256 ^ (k + 1) := by
      have : (256 : Nat) ^ (k + 1) = 256 ^ k * 256 := by rw [Nat.pow_succ]
      omega
    have hrec := ih (b * 256 + ba[j].toNat) (k + 1) hnew
    have he : k + 1 + i' = k + i'.succ := by omega
    rw [he] at hrec
    exact hrec
  | case3 t j b hge =>
    intro k hb
    unfold ByteArray.foldlM.loop
    simp [hge, Id.run]
    exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))

/-- A big-endian `ByteArray` of `n` bytes reads back to a value `< 256^n`. -/
theorem byteArrayToNatBE_lt (ba : ByteArray) : byteArrayToNatBE ba < 256 ^ ba.size := by
  unfold byteArrayToNatBE ByteArray.foldl ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  have := loop_natBE_lt ba ba.size 0 0 0 (by simp)
  simpa using this

/-- The long-promised digest bound: a `keccakWords` value is `< 2^256`. -/
theorem keccakWords_lt (ws : List Nat) : keccakWords ws < Compiler.Constants.evmModulus := by
  unfold keccakWords keccakBytes Compiler.Constants.evmModulus
  have hb := byteArrayToNatBE_lt
    (keccak256 (ws.foldl (fun acc w => acc ++ wordToBytesBE w) ByteArray.empty))
  rw [keccak256_size] at hb
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by
    conv_lhs => rw [show (256 : Nat) = 2 ^ 8 from rfl]
    rw [← Nat.pow_mul]
  rwa [h256] at hb

/-! ## 7. The unwrapped hash bridge for the reusable C13 keccak identity. -/

theorem keccakMemorySlice_eq_keccakWords
    (memory : Nat → Verity.Core.Uint256) (offset : Nat) (ws : List Nat)
    (hmem : ∀ i, (h : i < ws.length) → (memory (offset + 32 * i)).val = ws[i]) :
    keccakMemorySlice memory offset (32 * ws.length) = keccakWords ws := by
  rw [keccakMemorySlice_eq_wordNormalize_keccakWords memory offset ws hmem,
    Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod,
    Nat.mod_eq_of_lt (keccakWords_lt ws)]

/-! ## 8. The `evalExpr`-level keccak bridge (the reusable interpreter brick).

  Connects the real interpreter's evaluation of a literal-offset/literal-size
  `keccak256` expression to the spec `keccakWords ws`, given the covered memory
  cells hold `ws`.  Every Phase-2 segment (S2 digest, S4 forsPk, FORS leaf
  hashes, WOTS) consumes this brick. -/

theorem evalExpr_keccak256_eq_keccakWords
    (st : RuntimeState) (off sz : Nat) (ws : List Nat)
    (hoff : wordNormalize off = off)
    (hsz : wordNormalize sz = 32 * ws.length)
    (hmem : ∀ i, (h : i < ws.length) → (st.world.memory (off + 32 * i)).val = ws[i]) :
    evalExpr [] st (.keccak256 (.literal off) (.literal sz)) = some (keccakWords ws) := by
  show some (keccakMemorySlice st.world.memory (wordNormalize off) (wordNormalize sz))
        = some (keccakWords ws)
  rw [hoff, hsz, keccakMemorySlice_eq_keccakWords st.world.memory off ws hmem]

/-! ## 9. Axiom audit. -/

#print axioms wordToBytesBE_size
#print axioms extract_self
#print axioms memorySliceBytesBE_eq_spec_foldl
#print axioms keccakMemorySlice_eq_wordNormalize_keccakWords
#print axioms byteArrayToNatBE_lt
#print axioms keccakWords_lt
#print axioms keccakMemorySlice_eq_keccakWords
#print axioms evalExpr_keccak256_eq_keccakWords

end SphincsMinusVerifiers.KeccakBridge
