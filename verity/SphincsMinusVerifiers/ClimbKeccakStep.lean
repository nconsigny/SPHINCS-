/-
  ClimbKeccakStep — the masked-keccak combine step, the reusable final glue of
  the C13 keccak data correspondence.

  Every C13 tweakable hash the contract performs is, at the interpreter level,
  `and(keccak256(off, 32*k), N_MASK)` — a `keccak256` over word-aligned scratch
  immediately masked to its high 16 bytes.  The spec kernel writes the matching
  value as `maskN (keccakWords ws)` (`C13Concrete.maskN`/`keccakWords`).  This
  file proves the *masking* half of the identity:

    * `evalExpr_bitAnd_literal` — `and(e, literal m)` evaluates to `Nat.land k m`
      whenever `e` resolves to `k` with both `k, m < 2^256`, i.e. the interpreter's
      `Uint256.and` (which reduces mod 2^256) is the identity on already-bounded
      operands; and
    * `evalExpr_maskedKeccak_eq_maskN` — composing that with `KeccakBridge`'s
      `evalExpr_keccak256_eq_keccakWords`, the real interpreter's
      `and(keccak256(off, 32*ws.length), N_MASK)` resolves to exactly
      `maskN (keccakWords ws)`, given the covered memory cells hold `ws`.

  This is the single reusable combine consumed by the per-step Merkle/FORS/WOTS
  keccak correspondences (the `xmssClimbStep`/`forsClimbStep`/`chainHash` step
  values).  It evaluates no keccak and asserts nothing about which words sit in
  scratch — that memory-frame obligation is the hypothesis `hmem`.  No `sorry`,
  no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.KeccakBridge

namespace SphincsMinusVerifiers.ClimbKeccakStep

open Compiler.Proofs.IRGeneration.SourceSemantics (RuntimeState evalExpr wordNormalize)
open Compiler.CompilationModel (Expr)
open SphincsMinusVerifierSpec.C13Concrete (maskN nMask keccakWords)
open SphincsMinusVerifiers.KeccakBridge (keccakWords_lt evalExpr_keccak256_eq_keccakWords)

/-! ## 1. `N_MASK` is a 256-bit constant. -/

/-- The contract's `N_MASK` literal (= `C13Concrete.nMask`) is `< 2^256`. -/
theorem nMask_lt : nMask < 2 ^ 256 := by
  unfold nMask; decide

/-! ## 2. `and(e, literal m)` is `Nat.land` on bounded operands.

The interpreter's `bitAnd` does `(Uint256.and lhs rhs).val`, i.e.
`Nat.land (lhs % 2^256) (rhs % 2^256) % 2^256`.  When both operands are already
`< 2^256` the two outer mods vanish, and `Nat.land k m ≤ k < 2^256` kills the
final mod, leaving `Nat.land k m`. -/
theorem evalExpr_bitAnd_literal
    (st : RuntimeState) (e : Expr) (k m : Nat)
    (hk : evalExpr [] st e = some k) (hklt : k < 2 ^ 256) (hmlt : m < 2 ^ 256) :
    evalExpr [] st (.bitAnd e (.literal m)) = some (Nat.land k m) := by
  show (do
        let lhs ← evalExpr [] st e
        let rhs ← evalExpr [] st (.literal m)
        pure (Verity.Core.Uint256.and lhs rhs).val) = some (Nat.land k m)
  have hlit : evalExpr [] st (.literal m) = some (wordNormalize m) := rfl
  rw [hk, hlit]
  show some (Verity.Core.Uint256.and k (wordNormalize m)).val = some (Nat.land k m)
  have hm : wordNormalize m = m := by
    rw [Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt hmlt
  rw [hm]
  show some ((Verity.Core.Uint256.ofNat (Nat.land (Verity.Core.Uint256.ofNat k).val
        (Verity.Core.Uint256.ofNat m).val)).val) = some (Nat.land k m)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hklt
  have hmv : (Verity.Core.Uint256.ofNat m).val = m := Nat.mod_eq_of_lt hmlt
  rw [hkv, hmv]
  show some (Nat.land k m % Verity.Core.Uint256.modulus) = some (Nat.land k m)
  have hland : Nat.land k m < 2 ^ 256 := Nat.lt_of_le_of_lt Nat.and_le_left hklt
  have : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [this, Nat.mod_eq_of_lt hland]

/-! ## 3. The masked-keccak combine over a word-aligned literal scratch.

Specialising `evalExpr_bitAnd_literal` to the keccak operand: the interpreter's
`and(keccak256(off, 32*ws.length), N_MASK)` resolves to `maskN (keccakWords ws)`
exactly when the covered memory cells hold `ws`.  The size operand `32*ws.length`
must round-trip through `wordNormalize` (i.e. be `< 2^256`); for every C13 call
the word count is a tiny literal (3..5), so `hsz` is discharged by `decide` at
the call site. -/
theorem evalExpr_maskedKeccak_eq_maskN
    (st : RuntimeState) (off : Nat) (ws : List Nat)
    (hoff : wordNormalize off = off)
    (hsz : 32 * ws.length < 2 ^ 256)
    (hmem : ∀ i, (h : i < ws.length) → (st.world.memory (off + 32 * i)).val = ws[i]) :
    evalExpr [] st (.bitAnd (.keccak256 (.literal off) (.literal (32 * ws.length))) (.literal nMask))
      = some (maskN (keccakWords ws)) := by
  have hszn : wordNormalize (32 * ws.length) = 32 * ws.length := by
    rw [Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt hsz
  have hk : evalExpr [] st (.keccak256 (.literal off) (.literal (32 * ws.length)))
      = some (keccakWords ws) :=
    evalExpr_keccak256_eq_keccakWords st off (32 * ws.length) ws hoff hszn hmem
  have hklt : keccakWords ws < 2 ^ 256 := by
    have := keccakWords_lt ws
    rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
  rw [evalExpr_bitAnd_literal st _ (keccakWords ws) nMask hk hklt nMask_lt]
  rfl

/-! ## 4. Address-word combinators: `or`/`shl` on bounded operands.

The C13 ADRS word is assembled by the interpreter as
`or(adrsBase, or(shl(32, h+1), parentIdx))`, mirroring the spec kernel's
`treeAdrs ||| ((h+1) <<< 32) ||| parentIdx`.  The two lemmas below resolve the
interpreter's `bitOr`/`shl` on already-bounded operands to the bare
`Nat.lor`/`<<<`, the same "outer mod vanishes" pattern as
`evalExpr_bitAnd_literal`.  Both keep the bound as an explicit hypothesis so the
caller discharges it from the concrete (tiny) literals. -/

/-- `or(a, b)` evaluates to `Nat.lor k l` when `a ↦ k`, `b ↦ l` with both
`< 2^256`: the interpreter's `Uint256.or` reduces mod `2^256`, and
`Nat.lor k l < 2^256` (`Nat.bitwise_lt_two_pow`) kills the outer mod. -/
theorem evalExpr_bitOr_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) :
    evalExpr [] st (.bitOr a b) = some (Nat.lor k l) := by
  show (do
        let lhs ← evalExpr [] st a
        let rhs ← evalExpr [] st b
        pure (Verity.Core.Uint256.or lhs rhs).val) = some (Nat.lor k l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat (Nat.lor (Verity.Core.Uint256.ofNat k).val
        (Verity.Core.Uint256.ofNat l).val)).val) = some (Nat.lor k l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  rw [hkv, hlv]
  show some (Nat.lor k l % Verity.Core.Uint256.modulus) = some (Nat.lor k l)
  have hlor : Nat.lor k l < 2 ^ 256 := by
    show Nat.bitwise or k l < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hk hl
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hmod, Nat.mod_eq_of_lt hlor]

/-- `xor(a, b)` evaluates to `Nat.xor k l` when `a ↦ k`, `b ↦ l` with both
`< 2^256`: the interpreter's `Uint256.xor` reduces mod `2^256`, and
`Nat.xor k l < 2^256` (`Nat.xor_lt_two_pow`) kills the outer mod.  Resolves the
climb body's parity-xored child slots (`merkleClimbBody` stmts 5/6:
`0x40 ^^^ s`, `0x60 ^^^ s`). -/
theorem evalExpr_bitXor_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) :
    evalExpr [] st (.bitXor a b) = some (Nat.xor k l) := by
  show (do
        let lhs ← evalExpr [] st a
        let rhs ← evalExpr [] st b
        pure (Verity.Core.Uint256.xor lhs rhs).val) = some (Nat.xor k l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat (Nat.xor (Verity.Core.Uint256.ofNat k).val
        (Verity.Core.Uint256.ofNat l).val)).val) = some (Nat.xor k l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  rw [hkv, hlv]
  show some (Nat.xor k l % Verity.Core.Uint256.modulus) = some (Nat.xor k l)
  have hxor : Nat.xor k l < 2 ^ 256 := Nat.xor_lt_two_pow hk hl
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hmod, Nat.mod_eq_of_lt hxor]

/-- `shl(sh, val)` evaluates to `v <<< s` when `sh ↦ s`, `val ↦ v` with both
`< 2^256` and the shifted result still `< 2^256`: the interpreter's
`Uint256.shl shiftVal wordVal = ofNat (wordVal.val <<< shiftVal.val)`, so the
two operand mods vanish and the outer mod is killed by `hbound`. -/
theorem evalExpr_shl_bounded
    (st : RuntimeState) (sh val : Expr) (s v : Nat)
    (hs : evalExpr [] st sh = some s) (hv : evalExpr [] st val = some v)
    (hslt : s < 2 ^ 256) (hvlt : v < 2 ^ 256) (hbound : v <<< s < 2 ^ 256) :
    evalExpr [] st (.shl sh val) = some (v <<< s) := by
  show (do
        let shiftVal ← evalExpr [] st sh
        let wordVal ← evalExpr [] st val
        pure (Verity.Core.Uint256.shl shiftVal wordVal).val) = some (v <<< s)
  rw [hs, hv]
  show some ((Verity.Core.Uint256.ofNat ((Verity.Core.Uint256.ofNat v).val <<<
        (Verity.Core.Uint256.ofNat s).val)).val) = some (v <<< s)
  have hsv : (Verity.Core.Uint256.ofNat s).val = s := Nat.mod_eq_of_lt hslt
  have hvv : (Verity.Core.Uint256.ofNat v).val = v := Nat.mod_eq_of_lt hvlt
  rw [hsv, hvv]
  show some (v <<< s % Verity.Core.Uint256.modulus) = some (v <<< s)
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hmod, Nat.mod_eq_of_lt hbound]

/-- `shr(s, v)` evaluates to `v >>> s` when `s ↦`, `v ↦` with both `< 2^256`:
`Uint256.shr s v = ofNat (v.val >>> s.val)`, and `v >>> s ≤ v < 2^256` kills the
outer mod with no extra hypothesis.  Resolves the climb body's `parentIdx`
(`ClimbKit.merkleClimbBody` stmt 2: `shr(1, idxVar)` = `idxVar >>> 1 = idxVar/2`). -/
theorem evalExpr_shr_bounded
    (st : RuntimeState) (sh val : Expr) (s v : Nat)
    (hs : evalExpr [] st sh = some s) (hv : evalExpr [] st val = some v)
    (hslt : s < 2 ^ 256) (hvlt : v < 2 ^ 256) :
    evalExpr [] st (.shr sh val) = some (v >>> s) := by
  show (do
        let shiftVal ← evalExpr [] st sh
        let wordVal ← evalExpr [] st val
        pure (Verity.Core.Uint256.shr shiftVal wordVal).val) = some (v >>> s)
  rw [hs, hv]
  show some ((Verity.Core.Uint256.ofNat ((Verity.Core.Uint256.ofNat v).val >>>
        (Verity.Core.Uint256.ofNat s).val)).val) = some (v >>> s)
  have hsv : (Verity.Core.Uint256.ofNat s).val = s := Nat.mod_eq_of_lt hslt
  have hvv : (Verity.Core.Uint256.ofNat v).val = v := Nat.mod_eq_of_lt hvlt
  rw [hsv, hvv]
  show some (v >>> s % Verity.Core.Uint256.modulus) = some (v >>> s)
  have hbound : v >>> s < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self v (2 ^ s)) hvlt
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hmod, Nat.mod_eq_of_lt hbound]

/-- `add(a, b)` evaluates to `k + l` when `a ↦ k`, `b ↦ l` with both `< 2^256`
and the sum still `< 2^256`: the interpreter's `Uint256.add = ofNat (·.val + ·.val)`
reduces mod `2^256`, so the operand mods vanish and `hsum` kills the outer mod.
Needed for the ADRS sub-words assembled additively (`h+1`, `digit+step`). -/
theorem evalExpr_add_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) (hsum : k + l < 2 ^ 256) :
    evalExpr [] st (.add a b) = some (k + l) := by
  show (do
        let lhs : Verity.Core.Uint256 := ← evalExpr [] st a
        let rhs : Verity.Core.Uint256 := ← evalExpr [] st b
        pure (lhs + rhs).val) = some (k + l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat k + Verity.Core.Uint256.ofNat l).val)
      = some (k + l)
  show some (((Verity.Core.Uint256.ofNat k).val + (Verity.Core.Uint256.ofNat l).val)
        % Verity.Core.Uint256.modulus) = some (k + l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
  rw [hkv, hlv, hmod, Nat.mod_eq_of_lt hsum]

/-- `sub(a, b)` evaluates to `k - l` when `a ↦ k`, `b ↦ l` with both `< 2^256`
and `l ≤ k` (no wrap): the interpreter's `Uint256.sub` reduces mod `2^256`, the
operand mods vanish, and `k - l ≤ k < 2^256` kills the outer mod.  Needed for
the FIPS FORS per-level shift amount `sub(18, h)` (`ClimbKit.forsAdrs`). -/
theorem evalExpr_sub_bounded
    (st : RuntimeState) (a b : Expr) (k l : Nat)
    (ha : evalExpr [] st a = some k) (hb : evalExpr [] st b = some l)
    (hk : k < 2 ^ 256) (hl : l < 2 ^ 256) (hle : l ≤ k) :
    evalExpr [] st (.sub a b) = some (k - l) := by
  show (do
        let lhs : Verity.Core.Uint256 := ← evalExpr [] st a
        let rhs : Verity.Core.Uint256 := ← evalExpr [] st b
        pure (lhs - rhs).val) = some (k - l)
  rw [ha, hb]
  show some ((Verity.Core.Uint256.ofNat k - Verity.Core.Uint256.ofNat l).val)
      = some (k - l)
  have hkv : (Verity.Core.Uint256.ofNat k).val = k := Nat.mod_eq_of_lt hk
  have hlv : (Verity.Core.Uint256.ofNat l).val = l := Nat.mod_eq_of_lt hl
  rw [Verity.Core.Uint256.sub_eq_of_le (by rw [hkv, hlv]; exact hle), hkv, hlv]

/-! ## 5. The composed ADRS-word resolution.

The merkle/FORS climb body assembles the per-step ADRS word as the interpreter
term (`ClimbKit.merkleClimbBody`, stmt 3):

    or(adrsBase, or(shl(32, add(h, 1)), parentIdx))

i.e. `.bitOr baseE (.bitOr (.shl (.literal 32) (.add hE (.literal 1))) piE)`.
The spec kernel (`C13Concrete.xmssClimb` / `ClimbMemFrameMerkle.merkleSpecStep`)
writes the same word as

    treeAdrs ||| ((h+1) <<< 32) ||| parentIdx

which Lean parses **left**-associatively as `lor (lor treeAdrs ((h+1)<<<32)) pi`,
whereas the interpreter nests it **right**-associatively.  This lemma threads the
three arithmetic combinators above and bridges the associativity gap with
`Nat.lor_assoc`, landing exactly the spec's left-assoc form.  The operand
expressions stay generic (`baseE`/`hE`/`piE`) so the one lemma serves both the
XMSS and FORS climbs (which share `merkleClimbBody`); the bounds are explicit
hypotheses the caller discharges from the concrete ADRS-word ranges. -/
theorem evalExpr_merkleAdrsWord
    (st : RuntimeState) (baseE hE piE : Expr) (tb hval pi : Nat)
    (hbase : evalExpr [] st baseE = some tb)
    (hh : evalExpr [] st hE = some hval)
    (hpi : evalExpr [] st piE = some pi)
    (htb : tb < 2 ^ 256) (hpilt : pi < 2 ^ 256)
    (hh1 : hval + 1 < 2 ^ 256) (hshift : (hval + 1) <<< 32 < 2 ^ 256) :
    evalExpr [] st
        (.bitOr baseE (.bitOr (.shl (.literal 32) (.add hE (.literal 1))) piE))
      = some (Nat.lor (Nat.lor tb ((hval + 1) <<< 32)) pi) := by
  have h1 : evalExpr [] st (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod,
        show Compiler.Constants.evmModulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt (by decide)]
  have h32 : evalExpr [] st (.literal 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod,
        show Compiler.Constants.evmModulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt (by decide)]
  have hvlt : hval < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.le_succ hval) hh1
  have hadd : evalExpr [] st (.add hE (.literal 1)) = some (hval + 1) :=
    evalExpr_add_bounded st hE (.literal 1) hval 1 hh h1 hvlt (by decide) hh1
  have hshl : evalExpr [] st (.shl (.literal 32) (.add hE (.literal 1)))
      = some ((hval + 1) <<< 32) :=
    evalExpr_shl_bounded st (.literal 32) (.add hE (.literal 1)) 32 (hval + 1)
      h32 hadd (by decide) hh1 hshift
  have hinner : evalExpr [] st (.bitOr (.shl (.literal 32) (.add hE (.literal 1))) piE)
      = some (Nat.lor ((hval + 1) <<< 32) pi) :=
    evalExpr_bitOr_bounded st _ piE ((hval + 1) <<< 32) pi hshl hpi hshift hpilt
  have hlor : Nat.lor ((hval + 1) <<< 32) pi < 2 ^ 256 := by
    show Nat.bitwise or ((hval + 1) <<< 32) pi < 2 ^ 256
    exact Nat.bitwise_lt_two_pow hshift hpilt
  have houter : evalExpr [] st
      (.bitOr baseE (.bitOr (.shl (.literal 32) (.add hE (.literal 1))) piE))
      = some (Nat.lor tb (Nat.lor ((hval + 1) <<< 32) pi)) :=
    evalExpr_bitOr_bounded st baseE _ tb (Nat.lor ((hval + 1) <<< 32) pi)
      hbase hinner htb hlor
  rw [houter]
  exact congrArg some (Nat.lor_assoc tb ((hval + 1) <<< 32) pi).symm

/-! ## 6. The masked-calldata sibling word.

The merkle/FORS climb body's first statement (`ClimbKit.merkleClimbBody` stmt 1)
binds the sibling as `and(calldataload(authPtr + (4 << h)), N_MASK)` — a raw
calldata word immediately masked to its high 16 bytes, exactly the spec kernel's
`wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)` once that 16-byte auth word is read out of
the signature.  This lemma proves the *masking* half: given the `calldataload`
resolves to some `cw < 2^256`, the masked term is `maskN cw` — the same
"`Uint256.and` is the identity on bounded operands" shape as
`evalExpr_maskedKeccak_eq_maskN`, specialised to the calldata operand instead of
the keccak operand.  It deliberately leaves *which* calldata word `cw` is (and the
deeper `cw = wordOfHash16 auth[h]` source→model data correspondence) as the open
hypothesis `hcw` — that is the still-unproved #20 obligation, not something this
combine asserts. -/
theorem evalExpr_maskedCalldata
    (st : RuntimeState) (offE : Expr) (cw : Nat)
    (hcw : evalExpr [] st (.calldataload offE) = some cw)
    (hcwlt : cw < 2 ^ 256) :
    evalExpr [] st (.bitAnd (.calldataload offE) (.literal nMask)) = some (maskN cw) := by
  rw [evalExpr_bitAnd_literal st (.calldataload offE) cw nMask hcw hcwlt nMask_lt]
  rfl

/-- The sibling **calldata offset** the stmt-1 `calldataload` reads from
(`ClimbKit.merkleClimbBody` stmt 1): `add(authPtr, shl(4, h))`.  With the C13
`n=128` parameters each auth-path node is a 16-byte word, so the stride is
`h << 4 = 16*h`; this lemma threads `shl`→`add` to resolve the offset to the bare
`ap + hval <<< 4`, the `offE` argument `evalExpr_maskedCalldata` then masks.
Bounds (operands and the shifted/summed results `< 2^256`) stay explicit. -/
theorem evalExpr_siblingOffset
    (st : RuntimeState) (apE hE : Expr) (ap hval : Nat)
    (hap : evalExpr [] st apE = some ap)
    (hh : evalExpr [] st hE = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256) (hsum : ap + hval <<< 4 < 2 ^ 256) :
    evalExpr [] st (.add apE (.shl (.literal 4) hE)) = some (ap + hval <<< 4) := by
  have h4 : evalExpr [] st (.literal 4) = some 4 := by
    show some (wordNormalize 4) = some 4
    rw [Compiler.Proofs.IRGeneration.SourceSemantics.wordNormalize_eq_mod,
        show Compiler.Constants.evmModulus = 2 ^ 256 from rfl, Nat.mod_eq_of_lt (by decide)]
  have hshl : evalExpr [] st (.shl (.literal 4) hE) = some (hval <<< 4) :=
    evalExpr_shl_bounded st (.literal 4) hE 4 hval h4 hh (by decide) hhlt hshift
  exact evalExpr_add_bounded st apE (.shl (.literal 4) hE) ap (hval <<< 4)
    hap hshl haplt hshift hsum

/-! ## 7. Axiom audit. -/

#print axioms nMask_lt
#print axioms evalExpr_bitAnd_literal
#print axioms evalExpr_maskedKeccak_eq_maskN
#print axioms evalExpr_bitOr_bounded
#print axioms evalExpr_bitXor_bounded
#print axioms evalExpr_shl_bounded
#print axioms evalExpr_shr_bounded
#print axioms evalExpr_add_bounded
#print axioms evalExpr_sub_bounded
#print axioms evalExpr_merkleAdrsWord
#print axioms evalExpr_maskedCalldata
#print axioms evalExpr_siblingOffset

end SphincsMinusVerifiers.ClimbKeccakStep
