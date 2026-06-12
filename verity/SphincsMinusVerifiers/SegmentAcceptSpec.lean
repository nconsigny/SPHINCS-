/-
  SegmentAcceptSpec — the compose-stub mandated by STRATEGY (§2, "Worker E stubs
  the compose early to catch drift").

  `SegmentCompose.execC13Body_returns` already reduces the *entire* `c13VerifyBody`
  run, under the three control-flow guards, to a single `.return` whose payload is
  the EVM boolean word of the model's final `currentNode == root` comparison
  (`acceptWord st`).  That closes the **control-flow** side end-to-end.

  This file ties that returned boolean to the **spec** side: `verifyParsed`'s
  accept decision.  It does so under ONE explicit hypothesis, `hCmp`, which states
  that the model's final node/root word comparison agrees with the boolean
  `verifyParsed` returns.  `hCmp` is precisely the residual Phase-3b
  data-correspondence obligation (the months-scale FORS double-loop + hypertree
  keccak matching), surfaced here as a named hypothesis rather than discharged.

  The value of this stub is drift-detection: it is phrased against the REAL
  `verifyParsed`, `c13PrimitivesConcrete`, `c13`, `mkC13State`, and `c13VerifyBody`
  definitions, so any change to the model's return structure or the spec's accept
  shape breaks compilation here.  It touches neither `execC13` nor the bridge
  axiom, and discharges no data correspondence.  No `sorry`, no new `axiom`,
  no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentCompose
import SphincsMinusVerifiers.SegmentS2R
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifiers.RootFrame
import SphincsMinusVerifiers.CurrentNodeFrame
import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentAcceptSpec

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.RootFrame
open SphincsMinusVerifiers.CurrentNodeFrame
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete

private theorem wordOfHash16_and_nmask (b : ByteArray) :
    wordOfHash16 b =
      (Verity.Core.Uint256.and (wordOfHash16 b) (wordNormalize N_MASK)).val := by
  let h : Nat := baToNatBE b % 2 ^ 128
  have hh : h < 2 ^ 128 := Nat.mod_lt _ (by positivity)
  have hWordLt : h * 2 ^ 128 < 2 ^ 256 := by
    calc
      h * 2 ^ 128 < 2 ^ 128 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hh (by positivity)
      _ = 2 ^ 256 := by norm_num
  have hMask :
      Nat.land (h * 2 ^ 128) N_MASK = h * 2 ^ 128 := by
    simpa [Nat.add_zero] using SegmentS2R.land_nmask h 0 hh (by decide : 0 < 2 ^ 128)
  unfold wordOfHash16
  unfold Verity.Core.Uint256.and Verity.Core.Uint256.ofNat
  rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
    Nat.mod_eq_of_lt (by decide : N_MASK < 2 ^ 256)]
  simp only [Verity.Core.Uint256.modulus]
  rw [show h * 2 ^ 128 % Verity.Core.UINT256_MODULUS = h * 2 ^ 128 by
      exact Nat.mod_eq_of_lt (by simpa [Verity.Core.UINT256_MODULUS] using hWordLt)]
  rw [show N_MASK % Verity.Core.UINT256_MODULUS = N_MASK by
      exact Nat.mod_eq_of_lt (by decide : N_MASK < Verity.Core.UINT256_MODULUS)]
  rw [hMask]
  exact (Nat.mod_eq_of_lt (by simpa [Verity.Core.UINT256_MODULUS] using hWordLt)).symm

/-! ## Residual `hCmp` factoring. -/

/-- When the parsed verifier reaches the final `.ok root` branch, its observable
boolean is exactly the variant-specific public-root comparison.  This is the
spec-side branch equation needed by the model-side final-word comparison. -/
theorem verifyParsed_ok_branch
    (p : Primitives) (v : Variant)
    (pk : PublicKey) (message : ByteArray) (sigParsed : Signature)
    (forsPk root : ByteArray)
    (hShape : signatureShapeOk v sigParsed = true)
    (hZero : forcedZeroOk v (p.hMsg v pk sigParsed.R message) = true)
    (hFors : p.forsPkFromSig v pk (p.hMsg v pk sigParsed.R message) sigParsed.fors
              = some forsPk)
    (hFold : foldHypertree p v pk (p.hMsg v pk sigParsed.R message) forsPk sigParsed.layers
              = .ok root) :
    verifyParsed p v pk message sigParsed = some (rootMatchesPk v root pk.pkRoot) := by
  unfold verifyParsed
  simp [hShape, hZero, hFors, hFold]

/-- **`accept_path_returns_verifyParsed_bool`** — under the three control-flow
guards (length, FORS forced-zero, WOTS-checksum climb) AND the single residual
data-correspondence hypothesis `hCmp` (the model's final `currentNode == root`
word comparison decides the same boolean `verifyParsed` returns on this input),
the whole compiled `c13VerifyBody` run over `mkC13State …` returns the EVM-word
encoding of exactly the boolean `verifyParsed` yields.

This is the Phase-3 *compose stub*: it pins the model's observable return to the
spec's accept decision, catching any drift between the two.  It does NOT discharge
`hCmp` — that is the months-scale FORS/hypertree keccak correspondence — and it
neither defines `execC13` nor flips the bridge axiom.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/
theorem accept_path_returns_verifyParsed_bool
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (specBool : Bool)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
              = some specBool)
    (hCmp : decide
        (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
        = specBool) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed = some specBool ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord specBool)) finalState := by
  have hpkSeed :
      lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkSeed" =
        (Verity.Core.Uint256.and
          (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkSeed")
          (wordNormalize N_MASK)).val := by
    exact wordOfHash16_and_nmask pkSeed
  have hpkRoot :
      lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkRoot" =
        (Verity.Core.Uint256.and
          (lookupValue (mkC13State pkSeed pkRoot message sig).bindings "pkRoot")
          (wordNormalize N_MASK)).val := by
    exact wordOfHash16_and_nmask pkRoot
  obtain ⟨fs, hfs⟩ :=
    execC13Body_returns (mkC13State pkSeed pkRoot message sig)
      hlen hpkSeed hpkRoot hg3 hgL
  have hAcc : acceptWord (mkC13State pkSeed pkRoot message sig) = boolWord specBool := by
    unfold acceptWord; rw [hCmp]
  refine ⟨fs, hSpec, ?_⟩
  rw [hfs, hAcc]

/-- **`accept_path_returns_verifyParsed_bool_linked`** — the same compose stub as
`accept_path_returns_verifyParsed_bool`, but with the spec-side inputs *pinned to
the byte inputs* via two linkage hypotheses:

* `hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot }` — the public key is exactly
  what `ByteLevel.parsePublicKey`/`verifyBytes` reconstructs from the two `bytes32`
  arguments (Spec.lean:347–350).
* `hSig : parseSignatureC13 c13 sig = some sigParsed` — the parsed signature is
  exactly what `c13PrimitivesConcrete.parseSignature` yields on the raw bytes.

With these, `specBool` (constrained by `hSpec` over `pk`/`sigParsed`) becomes a
*function of the byte inputs alone*, the same bytes the model's
`currentNode`/`root` bindings are computed from.  This makes the residual
data-correspondence goal `decide (currentNode = root) = specBool` **well-posed**
(both sides range over the same `pkSeed pkRoot message sig`), closing *Blocker A*
(the floating-`pk`/`sigParsed` ill-posedness).  It still carries `hCmp` and does
not discharge the keccak correspondence (*Blocker B*).  Axiom-clean. -/
theorem accept_path_returns_verifyParsed_bool_linked
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (specBool : Bool)
    (_hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (_hSig : parseSignatureC13 c13 sig = some sigParsed)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
              = some specBool)
    (hCmp : decide
        (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
        = specBool) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed = some specBool ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord specBool)) finalState := by
  -- The linkage hypotheses pin the spec inputs to the bytes (Blocker A); the proof
  -- itself is the same as the unlinked stub.
  exact accept_path_returns_verifyParsed_bool
    pkSeed pkRoot message sig pk sigParsed specBool hlen hg3 hgL hSpec hCmp

/-- **`accept_path_returns_verifyParsed_bool_from_root`** — a sharper compose
adapter for the residual `hCmp`: if the left operand of the final model compare is
the word image of the spec's final root, and byte equality at the spec boundary is
represented by the corresponding word equality, then the existing accept-path
composition returns the `verifyParsed` boolean.

The right operand is no longer a hypothesis here: it is supplied by
`RootFrame.afterLayer_root_mkC13State`, which proves the final `"root"` binding is
`wordOfHash16 pkRoot`.  The only remaining substantive obligations are therefore:

* `hCurrent`: the post-layer `"currentNode"` binding equals `wordOfHash16 specRoot`;
* `hWordCmp`: the word-level equality test agrees with the spec byte equality.

This is the bounded form of `hCmp` that the FORS/hypertree correspondence should
eventually discharge.  It still does not touch `execC13` or the bridge axiom. -/
theorem accept_path_returns_verifyParsed_bool_from_root
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hCurrent :
        lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = wordOfHash16 specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  subst hPk
  have hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) :=
    verifyParsed_ok_branch C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed forsPk specRoot
      hShape hZero hFors hFold
  have hRoot :
      lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root"
        = wordOfHash16 pkRoot :=
    afterLayer_root_mkC13State pkSeed pkRoot message sig
  have hCmp : decide
      (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
        = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
      = rootMatchesPk c13 specRoot pkRoot := by
    rw [hCurrent, hRoot, hWordCmp]
  exact accept_path_returns_verifyParsed_bool
    pkSeed pkRoot message sig { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed
    (rootMatchesPk c13 specRoot pkRoot) hlen hg3 hgL hSpec hCmp

/-- A compact way to discharge the final `hWordCmp` premise: if the word encoding
is injective for the two byte roots in question, then the model's word equality
decision agrees with the spec's `ByteArray` equality test. -/
theorem wordCmp_of_wordOfHash16_iff
    (specRoot pkRoot : ByteArray)
    (hIff : (wordOfHash16 specRoot = wordOfHash16 pkRoot) ↔ specRoot = pkRoot)
    (hBeq : (specRoot == pkRoot) = decide (specRoot = pkRoot)) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot) = (specRoot == pkRoot) := by
  rw [hBeq]
  by_cases hWord : wordOfHash16 specRoot = wordOfHash16 pkRoot
  · have hBytes : specRoot = pkRoot := hIff.mp hWord
    simp [hBytes]
  · have hBytes : specRoot ≠ pkRoot := by
      intro hEq
      exact hWord (hIff.mpr hEq)
    simp [hWord, hBytes]

/-- `ByteArray`'s derived `BEq` agrees with propositional equality on canonical
`hash16OfWord` outputs.  This avoids assuming a global `LawfulBEq ByteArray`
instance, which is not available in this environment. -/
theorem hash16OfWord_beq_eq_decide (w1 w2 : Word) :
    (hash16OfWord w1 == hash16OfWord w2)
      = decide (hash16OfWord w1 = hash16OfWord w2) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp [hash16OfWord] at h ⊢
    change
      (((List.map (fun i => UInt8.ofNat (w1 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray) ==
        ((List.map (fun i => UInt8.ofNat (w2 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray)) = true at h
    rw [beq_iff_eq] at h
    simpa using h
  · intro h
    simp [hash16OfWord] at h ⊢
    change
      (((List.map (fun i => UInt8.ofNat (w1 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray) ==
        ((List.map (fun i => UInt8.ofNat (w2 / 256 ^ (31 - i) % 256))
            (List.range 16)).toArray)) = true
    rw [beq_iff_eq]
    simpa using h

/-- If both byte roots are canonical roundtrips through `wordOfHash16` and
`hash16OfWord`, their `ByteArray` equality test agrees with propositional
equality. -/
theorem byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip
    (specRoot pkRoot : ByteArray)
    (hSpec : hash16OfWord (wordOfHash16 specRoot) = specRoot)
    (hPk : hash16OfWord (wordOfHash16 pkRoot) = pkRoot) :
    (specRoot == pkRoot) = decide (specRoot = pkRoot) := by
  rw [← hSpec, ← hPk]
  exact hash16OfWord_beq_eq_decide (wordOfHash16 specRoot) (wordOfHash16 pkRoot)

/-- Canonical root roundtrips are enough to discharge the final word-comparison
premise: word equality is reflected by `hash16OfWord`, and the byte-side `BEq`
is reduced to canonical `hash16OfWord` outputs. -/
theorem wordCmp_of_wordOfHash16_roundtrip
    (specRoot pkRoot : ByteArray)
    (hSpec : hash16OfWord (wordOfHash16 specRoot) = specRoot)
    (hPk : hash16OfWord (wordOfHash16 pkRoot) = pkRoot) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot) = (specRoot == pkRoot) := by
  have hIff :
      (wordOfHash16 specRoot = wordOfHash16 pkRoot) ↔ specRoot = pkRoot := by
    constructor
    · intro hWord
      rw [← hSpec, ← hPk, hWord]
    · intro hBytes
      rw [hBytes]
  exact wordCmp_of_wordOfHash16_iff specRoot pkRoot hIff
    (byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip specRoot pkRoot hSpec hPk)

/-- `UInt8.ofNat` stores the low byte of its natural argument. -/
theorem uint8_toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := rfl

/-- Appending one low base-256 digit to a truncated quotient recovers one more
base-256 digit of `x`. -/
theorem base256_digit_append (x n : Nat) :
    ((x / 256) % 256 ^ n) * 256 + x % 256 = x % 256 ^ (n + 1) := by
  let M := 256 ^ n
  have hpow : 256 ^ (n + 1) = 256 * M := by
    simp [M, pow_succ]
    ring
  rw [hpow]
  calc
    ((x / 256) % M) * 256 + x % 256
        = 256 * ((x / 256) % M) + x % 256 := by ring
    _ = 256 * ((x % (256 * M)) / 256) + (x % (256 * M)) % 256 := by
        rw [Nat.mod_mul_right_div_self]
        have hmod : (x % (256 * M)) % 256 = x % 256 := by
          rw [Nat.mul_comm 256 M]
          exact Nat.mod_mul_left_mod x M 256
        rw [hmod]
    _ = x % (256 * M) := by
        rw [Nat.div_add_mod]

/-- Extract one byte digit from a base-256 decomposition with a bounded tail. -/
theorem base256_digit_decomp
    (a d t s : Nat) (hd : d < 256) (ht : t < 256 ^ s) :
    ((a * 256 ^ (s + 1) + d * 256 ^ s + t) / 256 ^ s) % 256 = d := by
  let m := 256 ^ s
  have hm : 0 < m := Nat.pow_pos (by norm_num : 0 < 256)
  have hpow : 256 ^ (s + 1) = 256 * m := by
    simp [m, pow_succ]
    ring
  have hshape :
      a * 256 ^ (s + 1) + d * 256 ^ s + t
        = (a * 256 + d) * m + t := by
    rw [hpow]
    simp [m]
    ring
  rw [hshape]
  change (((a * 256 + d) * m + t) / m) % 256 = d
  rw [Nat.mul_comm (a * 256 + d) m]
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt ht, Nat.add_zero]
  rw [Nat.add_comm (a * 256) d]
  rw [Nat.mul_comm a 256]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hd

/-- Pull an initial accumulator out of a big-endian fold over byte values. -/
theorem base256_uint8_fold_init (l : List UInt8) (init : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) init
      = init * 256 ^ l.length + l.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons b bs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (init * 256 + b.toNat), ih (0 * 256 + b.toNat)]
      ring

/-- A big-endian fold over bytes is bounded by the corresponding base-256
width. -/
theorem base256_uint8_fold_lt (l : List UInt8) :
    l.foldl (fun acc b => acc * 256 + b.toNat) 0 < 256 ^ l.length := by
  have h :
      ∀ (l : List UInt8) (init k : Nat), init < 256 ^ k →
        l.foldl (fun acc b => acc * 256 + b.toNat) init < 256 ^ (k + l.length) := by
    intro l
    induction l with
    | nil =>
        intro init k hinit
        simpa using hinit
    | cons b bs ih =>
        intro init k hinit
        simp only [List.foldl_cons, List.length_cons]
        have hnew : init * 256 + b.toNat < 256 ^ (k + 1) := by
          have hb : b.toNat < 256 := b.toNat_lt_size
          have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := by rw [pow_succ]
          omega
        have hrec := ih (init * 256 + b.toNat) (k + 1) hnew
        have hExp : k + 1 + bs.length = k + (bs.length + 1) := by omega
        rwa [hExp] at hrec
  simpa using h l 0 0 (by norm_num)

/-- The `i`th byte of a fixed base-256 fold can be selected by shifting away the
lower bytes and reducing modulo 256. -/
theorem base256_fold_digit_of_list
    (l : List UInt8) (i : Nat) (hi : i < l.length) :
    (l.foldl (fun acc b => acc * 256 + b.toNat) 0 /
        256 ^ (l.length - 1 - i)) % 256 = l[i].toNat := by
  let tail := l.drop (i + 1)
  have hsplit : l = l.take i ++ l[i] :: tail := by
    rw [← List.drop_eq_getElem_cons hi]
    exact (List.take_append_drop i l).symm
  have htailLen : tail.length = l.length - (i + 1) := by
    simp [tail]
  have hExp : l.length - 1 - i = tail.length := by
    rw [htailLen]
    omega
  have htailLt :
      tail.foldl (fun acc b => acc * 256 + b.toNat) 0 < 256 ^ tail.length :=
    base256_uint8_fold_lt tail
  have hfold :
      l.foldl (fun acc b => acc * 256 + b.toNat) 0 =
        (l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0 *
            256 ^ (tail.length + 1) +
          l[i].toNat * 256 ^ tail.length +
          tail.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    calc
      l.foldl (fun acc b => acc * 256 + b.toNat) 0
          = (l.take i ++ l[i] :: tail).foldl
              (fun acc b => acc * 256 + b.toNat) 0 := by
            exact congrArg (fun xs => xs.foldl (fun acc b => acc * 256 + b.toNat) 0) hsplit
      _ = (l[i] :: tail).foldl
              (fun acc b => acc * 256 + b.toNat)
              ((l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0) := by
            rw [List.foldl_append]
      _ = (l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0 *
              256 ^ (tail.length + 1) +
            (l[i] :: tail).foldl (fun acc b => acc * 256 + b.toNat) 0 := by
            rw [base256_uint8_fold_init (l[i] :: tail)]
            simp
      _ = (l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0 *
              256 ^ (tail.length + 1) +
            l[i].toNat * 256 ^ tail.length +
            tail.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
            simp only [List.foldl_cons, zero_mul, zero_add]
            rw [base256_uint8_fold_init tail l[i].toNat]
            ring
  rw [hfold, hExp]
  exact base256_digit_decomp
    ((l.take i).foldl (fun acc b => acc * 256 + b.toNat) 0)
    l[i].toNat
    (tail.foldl (fun acc b => acc * 256 + b.toNat) 0)
    tail.length
    l[i].toNat_lt_size htailLt

/-- `baToNatBE` is the big-endian fold of the backing byte list. -/
theorem baToNatBE_eq_data_toList (b : ByteArray) :
    baToNatBE b =
      b.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 := by
  unfold baToNatBE
  rw [SegmentS2R.ba_foldl_eq]
  conv_lhs => rw [← Array.toArray_toList (xs := b.data)]
  rw [List.foldl_toArray' (fun acc byte => acc * 256 + byte.toNat) 0 b.data.toList rfl]

/-- A byte array of size 16 folds to a 128-bit natural. -/
theorem baToNatBE_lt_of_size (b : ByteArray) (hsize : b.size = 16) :
    baToNatBE b < 2 ^ 128 := by
  rw [baToNatBE_eq_data_toList]
  have h := base256_uint8_fold_lt b.data.toList
  have hpow : (256 : Nat) ^ b.data.toList.length = 2 ^ 128 := by
    have hlen : b.data.toList.length = 16 := by
      simpa [ByteArray.size, Array.length_toList] using hsize
    rw [hlen]
    norm_num
  rwa [hpow] at h

/-- A 16-byte array is already canonical for the C13
`hash16OfWord`/`wordOfHash16` byte roundtrip. -/
theorem hash16OfWord_wordOfHash16_of_size
    (b : ByteArray) (hsize : b.size = 16) :
    hash16OfWord (wordOfHash16 b) = b := by
  apply ByteArray.ext
  apply Array.ext
  · simpa [hash16OfWord, ByteArray.size] using hsize.symm
  · intro i hiHash hiB
    apply UInt8.toNat_inj.mp
    have hi : i < 16 := by
      simpa [hash16OfWord, List.size_toArray] using hiHash
    have hbaLt : baToNatBE b < 2 ^ 128 := baToNatBE_lt_of_size b hsize
    have hpow128 : (2 : Nat) ^ 128 = 256 ^ 16 := by norm_num
    have hbaLt256 : baToNatBE b < 256 ^ 16 := by
      rwa [← hpow128]
    have hExp : 31 - i = 16 + (15 - i) := by omega
    have hDigit :
        (b.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 /
            256 ^ (15 - i)) % 256 = b.data[i].toNat := by
      have hListIdx : i < b.data.toList.length := by
        simpa [Array.length_toList] using hiB
      have hLen : b.data.toList.length = 16 := by
        simpa [ByteArray.size, Array.length_toList] using hsize
      have hbase := base256_fold_digit_of_list b.data.toList i hListIdx
      have hExpList : b.data.toList.length - 1 - i = 15 - i := by
        rw [hLen]
      have hGet : b.data.toList[i] = b.data[i] := by
        exact Array.getElem_toList (xs := b.data) hiB
      rw [hExpList] at hbase
      rw [hGet] at hbase
      exact hbase
    simp [hash16OfWord, wordOfHash16]
    change
      (baToNatBE b % 2 ^ 128 * 2 ^ 128 / 256 ^ (31 - i) % 256
        = b.data[i].toNat)
    rw [hpow128, Nat.mod_eq_of_lt hbaLt256, hExp]
    rw [Nat.pow_add]
    rw [Nat.mul_comm (baToNatBE b) (256 ^ 16)]
    rw [Nat.mul_div_mul_left _ _ (Nat.pow_pos (by norm_num : 0 < 256))]
    rw [baToNatBE_eq_data_toList]
    exact hDigit

/-- Folding `n` high-to-low base-256 digits of `w`, starting at byte offset `k`,
is the corresponding `n`-byte window of `w`. -/
theorem highDigitsFold_eq_mod (w k n : Nat) :
    (List.range n).foldl
      (fun acc i => acc * 256 + w / 256 ^ (k + n - 1 - i) % 256) 0
      = (w / 256 ^ k) % 256 ^ n := by
  induction n generalizing k with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      have hfun :
          (fun acc i => acc * 256 + w / 256 ^ (k + (n + 1) - 1 - i) % 256)
          = (fun acc i => acc * 256 + w / 256 ^ (k + 1 + n - 1 - i) % 256) := by
        funext acc i
        have : k + (n + 1) - 1 - i = k + 1 + n - 1 - i := by omega
        rw [this]
      rw [hfun, ih (k + 1)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hlast : k + 1 + n - 1 - n = k := by omega
      rw [hlast]
      have hdiv : w / 256 ^ (k + 1) = (w / 256 ^ k) / 256 := by
        rw [Nat.div_div_eq_div_mul]
        congr 1
      rw [hdiv]
      exact base256_digit_append (w / 256 ^ k) n

/-- Folding the bytes rendered by `bytesOfNatBE 16` recovers the low 128 bits. -/
theorem baToNatBE_bytesOfNatBE16 (w : Nat) :
    baToNatBE (bytesOfNatBE 16 w) = w % 256 ^ 16 := by
  unfold bytesOfNatBE
  rw [SegmentS2R.baToNatBE_toArray]
  rw [List.foldl_map]
  simpa [uint8_toNat_ofNat, Nat.mod_mod] using
    (highDigitsFold_eq_mod w 0 16)

/-- The C13 public-key-root byte spec compares against the same 128-bit
projection that `wordOfHash16` reads from the full `bytes32` public-root
argument. -/
theorem wordOfHash16_lowBytesProjection16 (pkRoot : ByteArray) :
    wordOfHash16 (lowBytesProjection 16 pkRoot) = wordOfHash16 pkRoot := by
  unfold wordOfHash16 lowBytesProjection
  rw [baToNatBE_bytesOfNatBE16]
  simp [bytesToNatBE, baToNatBE]

/-- C13-specific final comparison bridge: the model's word equality agrees with
the byte spec's projected public-root comparison. -/
theorem wordCmp_of_wordOfHash16_rootMatchesPk_c13
    (specRoot pkRoot : ByteArray)
    (hSpec : hash16OfWord (wordOfHash16 specRoot) = specRoot) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
      = rootMatchesPk c13 specRoot pkRoot := by
  rw [← wordOfHash16_lowBytesProjection16 pkRoot]
  unfold rootMatchesPk comparePkRootBytes
  simp [c13]
  exact wordCmp_of_wordOfHash16_roundtrip specRoot (lowBytesProjection 16 pkRoot)
    hSpec
    (hash16OfWord_wordOfHash16_of_size (lowBytesProjection 16 pkRoot) (by
      simp [lowBytesProjection, bytesOfNatBE, ByteArray.size]))

/-- A low byte selected from the high half after truncating to 16 bytes is the
same byte selected from the original word. -/
theorem highHalf_mod_digit (w r : Nat) (hr : r < 16) :
    (((w / 256 ^ 16) % 256 ^ 16) * 256 ^ 16) / 256 ^ (16 + r) % 256
      = w / 256 ^ (16 + r) % 256 := by
  set x := w / 256 ^ 16
  have hpowDen : 256 ^ (16 + r) = 256 ^ 16 * 256 ^ r := by
    rw [Nat.pow_add]
  have hright : w / 256 ^ (16 + r) = x / 256 ^ r := by
    rw [hpowDen, ← Nat.div_div_eq_div_mul]
  rw [hright, hpowDen]
  have hdivmul :
      (x % 256 ^ 16 * 256 ^ 16) / (256 ^ 16 * 256 ^ r)
        = (x % 256 ^ 16) / 256 ^ r := by
    rw [Nat.mul_comm (256 ^ 16) (256 ^ r)]
    exact Nat.mul_div_mul_right (x % 256 ^ 16) (256 ^ r)
      (Nat.pow_pos (by norm_num : 0 < 256))
  rw [hdivmul]
  have hpow16 : 256 ^ 16 = 256 ^ r * 256 ^ (16 - r) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow16, Nat.mod_mul_right_div_self]
  have hdvd : 256 ∣ 256 ^ (16 - r) := by
    refine ⟨256 ^ (15 - r), ?_⟩
    rw [show 16 - r = (15 - r) + 1 by omega, pow_succ]
    ring
  exact Nat.mod_mod_of_dvd (x / 256 ^ r) hdvd

/-- Canonical `hash16OfWord` outputs roundtrip through `wordOfHash16`. -/
theorem hash16OfWord_wordOfHash16_hash16OfWord (w : Word) :
    hash16OfWord (wordOfHash16 (hash16OfWord w)) = hash16OfWord w := by
  simp [hash16OfWord, wordOfHash16, SegmentS2R.baToNatBE_toArray]
  intro a ha
  rw [List.foldl_map]
  simp only [uint8_toNat_ofNat, Nat.mod_mod]
  have hfold :
      (List.foldl
          (fun acc i => acc * 256 + w / 256 ^ (31 - i) % 256) 0
          (List.range 16)) = (w / 256 ^ 16) % 256 ^ 16 := by
    convert highDigitsFold_eq_mod w 16 16 using 2
  rw [hfold]
  change
    UInt8.ofNat
      (((w / 256 ^ 16 % 256 ^ 16 % 256 ^ 16) * 256 ^ 16
          / 256 ^ (31 - a)) % 256)
      = UInt8.ofNat (w / 256 ^ (31 - a) % 256)
  rw [Nat.mod_mod]
  congr 1
  have hr : 15 - a < 16 := by omega
  have hExp : 31 - a = 16 + (15 - a) := by omega
  rw [hExp]
  exact highHalf_mod_digit w (15 - a) hr

/-- Reading the high 16 bytes of a word as a `ByteArray` and folding them back
big-endian recovers the word's high 128-bit window. -/
theorem baToNatBE_hash16OfWord (w : Word) :
    baToNatBE (hash16OfWord w) = (w / 256 ^ 16) % 256 ^ 16 := by
  simp [hash16OfWord, SegmentS2R.baToNatBE_toArray]
  rw [List.foldl_map]
  simp only [uint8_toNat_ofNat, Nat.mod_mod]
  convert highDigitsFold_eq_mod w 16 16 using 1

/-- A word already shaped as a high-half C13 hash roundtrips through
`hash16OfWord` and `wordOfHash16`. -/
theorem wordOfHash16_hash16OfWord_highHalf
    (h : Nat) (hh : h < 2 ^ 128) :
    wordOfHash16 (hash16OfWord (h * 2 ^ 128)) = h * 2 ^ 128 := by
  unfold wordOfHash16
  rw [baToNatBE_hash16OfWord]
  have hpow : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
  rw [hpow]
  have hdiv : h * 2 ^ 128 / 2 ^ 128 = h := by
    exact Nat.mul_div_left h (Nat.pow_pos (by norm_num : 0 < 2))
  rw [hdiv]
  rw [Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hh]

/-- The final word-comparison boundary is not unconditional: a canonical
16-byte root and a non-canonical byte root can have the same `wordOfHash16`
projection while remaining unequal as byte arrays. -/
theorem wordCmp_boundary_counterexample :
    ∃ specRoot pkRoot : ByteArray,
      CanonicalHash16 specRoot ∧
      pkRoot.size ≠ 16 ∧
      wordOfHash16 specRoot = wordOfHash16 pkRoot ∧
      specRoot ≠ pkRoot := by
  refine ⟨hash16OfWord 0, ByteArray.empty, hash16OfWord_canonical 0, ?_, ?_⟩
  · simp [ByteArray.size]
  · have hWordSpec : wordOfHash16 (hash16OfWord 0) = 0 := by
      exact wordOfHash16_hash16OfWord_highHalf 0 (by norm_num)
    have hWordPk : wordOfHash16 ByteArray.empty = 0 := by
      unfold wordOfHash16
      rw [baToNatBE_eq_data_toList]
      simp [ByteArray.empty]
    have hNe : hash16OfWord 0 ≠ ByteArray.empty := by
      intro hEq
      have hSize := congrArg ByteArray.size hEq
      simp [hash16OfWord, ByteArray.size] at hSize
    exact ⟨by rw [hWordSpec, hWordPk], hNe⟩

/-- A bounded 256-bit word masked by C13's `N_MASK` is already canonical for
the `hash16OfWord`/`wordOfHash16` conversion. -/
theorem wordOfHash16_hash16OfWord_maskN_of_lt
    (w : Word) (hw : w < 2 ^ 256) :
    wordOfHash16 (hash16OfWord (maskN w)) = maskN w := by
  let hi := w / 2 ^ 128
  let lo := w % 2 ^ 128
  have hpow : 2 ^ 256 = 2 ^ 128 * 2 ^ 128 := by norm_num
  have hhi : hi < 2 ^ 128 := by
    unfold hi
    exact Nat.div_lt_of_lt_mul (by
      show w < 2 ^ 128 * 2 ^ 128
      rwa [← hpow])
  have hlo : lo < 2 ^ 128 := by
    unfold lo
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num : 0 < 2))
  have hsplit : w = hi * 2 ^ 128 + lo := by
    unfold hi lo
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod w (2 ^ 128)).symm
  have hmask : maskN w = hi * 2 ^ 128 := by
    unfold maskN
    rw [hsplit]
    rw [show nMask = SphincsMinusVerifiers.ClimbKit.N_MASK from rfl]
    exact SegmentS2R.land_nmask hi lo hhi hlo
  rw [hmask]
  exact wordOfHash16_hash16OfWord_highHalf hi hhi

/-- The named C13 FORS public-key compression word is masked, hence canonical
for the `hash16OfWord`/`wordOfHash16` conversion. -/
theorem forsPkWordC13_roundtrip
    (pk : PublicKey) (digest : HMsg) (fors : ForsSig) :
    wordOfHash16 (hash16OfWord (C13Concrete.forsPkWordC13 pk digest fors))
      = C13Concrete.forsPkWordC13 pk digest fors := by
  let seed := wordOfHash16 pk.pkSeed
  let words := seed :: C13Concrete.adrsForsRootsC13 digest ::
    C13Concrete.forsAllRootsC13 pk digest fors
  have hlt : C13Concrete.keccakWords words < 2 ^ 256 := by
    simpa [Compiler.Constants.evmModulus] using
      SphincsMinusVerifiers.KeccakBridge.keccakWords_lt words
  simpa [C13Concrete.forsPkWordC13, words, seed] using
    wordOfHash16_hash16OfWord_maskN_of_lt (C13Concrete.keccakWords words) hlt

/-- C13 XMSS climb preserves the `hash16OfWord`/`wordOfHash16` canonical-word
shape.  Each nonzero step replaces the node by `maskN (keccakWords ...)`, and
`wordOfHash16_hash16OfWord_maskN_of_lt` closes that new node shape. -/
theorem xmssClimb_roundtrip_of_node_roundtrip
    (seed treeAdrs fuel h mIdx node : Nat) (auth : List ByteArray)
    (hNode : wordOfHash16 (hash16OfWord node) = node) :
    wordOfHash16
        (hash16OfWord
          (C13Concrete.xmssClimb seed treeAdrs fuel h mIdx node auth))
      = C13Concrete.xmssClimb seed treeAdrs fuel h mIdx node auth := by
  induction fuel generalizing h mIdx node with
  | zero =>
      simpa [C13Concrete.xmssClimb] using hNode
  | succ fuel ih =>
      rw [C13Concrete.xmssClimb]
      by_cases heven : mIdx % 2 == 0
      · simp only [heven]
        exact ih (h + 1) (mIdx / 2)
          (C13Concrete.maskN
            (C13Concrete.keccakWords
              [seed, treeAdrs ||| ((h + 1) <<< 32) ||| (mIdx / 2), node,
                wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)]))
          (by
            exact wordOfHash16_hash16OfWord_maskN_of_lt
              (C13Concrete.keccakWords
                [seed, treeAdrs ||| ((h + 1) <<< 32) ||| (mIdx / 2), node,
                  wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)])
              (by
                simpa [Compiler.Constants.evmModulus] using
                  SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
                    [seed, treeAdrs ||| ((h + 1) <<< 32) ||| (mIdx / 2), node,
                      wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)]))
      · simp only [heven]
        exact ih (h + 1) (mIdx / 2)
          (C13Concrete.maskN
            (C13Concrete.keccakWords
              [seed, treeAdrs ||| ((h + 1) <<< 32) ||| (mIdx / 2),
                wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node]))
          (by
            exact wordOfHash16_hash16OfWord_maskN_of_lt
              (C13Concrete.keccakWords
                [seed, treeAdrs ||| ((h + 1) <<< 32) ||| (mIdx / 2),
                  wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node])
              (by
                simpa [Compiler.Constants.evmModulus] using
                  SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
                    [seed, treeAdrs ||| ((h + 1) <<< 32) ||| (mIdx / 2),
                      wordOfHash16 ((auth[h]?).getD ⟨#[]⟩), node]))

/-- Successful C13 WOTS reconstruction gives a 16-byte starting XMSS node, so
the concrete C13 XMSS climb word roundtrips through
`hash16OfWord`/`wordOfHash16`. -/
theorem xmssClimb_roundtrip_of_wots_success
    (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node wotsPk : ByteArray) (wots : WotsSig) (auth : List ByteArray)
    (hWots : C13Concrete.wotsPkFromSigC13 c13 pk treeIdx leafIdx node wots
        = some wotsPk) :
    wordOfHash16
        (hash16OfWord
          (C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
            (wordOfHash16 wotsPk) auth))
      =
        C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
          (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
          (wordOfHash16 wotsPk) auth := by
  refine xmssClimb_roundtrip_of_node_roundtrip
    (wordOfHash16 pk.pkSeed) (C13Concrete.adrsXmssTree 0 treeIdx)
    11 0 leafIdx (wordOfHash16 wotsPk) auth ?_
  rw [hash16OfWord_wordOfHash16_of_size wotsPk
    (C13Concrete.wotsPkFromSigC13_size hWots)]

/-- Any byte string known to be a canonical C13 `hash16OfWord` output roundtrips
through `wordOfHash16`. -/
theorem hash16OfWord_wordOfHash16_of_canonical
    (b : ByteArray) (h : C13Concrete.CanonicalHash16 b) :
    hash16OfWord (wordOfHash16 b) = b := by
  rcases h with ⟨w, rfl⟩
  exact hash16OfWord_wordOfHash16_hash16OfWord w

/-- A successful C13 FORS reconstruction followed by a successful C13 hypertree
fold produces a root that roundtrips through `wordOfHash16`/`hash16OfWord`. -/
theorem specRoot_roundtrip_of_c13_fors_fold
    {pk : PublicKey} {digest : HMsg} {fors : ForsSig} {forsPk specRoot : ByteArray}
    {layers : List XmssLayerSig}
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk digest fors
        = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest forsPk layers
        = .ok specRoot) :
    hash16OfWord (wordOfHash16 specRoot) = specRoot :=
  hash16OfWord_wordOfHash16_of_canonical specRoot
    (C13Concrete.foldHypertree_c13_ok_root_canonical_of_fors hFors hFold)

/-- **Layer-step form of the final accept adapter.**  This replaces the raw
`hCurrent` hypothesis of `accept_path_returns_verifyParsed_bool_from_root` with
the two facts the hypertree proof is expected to produce:

* S4/FORS finalize binds `"forsPk"` to the word image of the spec FORS public key;
* one `stepLayer` iteration preserves the `"currentNode"` ↔ spec-node relation,
  so `CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step` lifts it
  across the two-layer C13 loop.

The per-layer correspondence is still a hypothesis here; this theorem only
performs the segment composition from that correspondence to the final
`verifyParsed` boolean. -/
theorem accept_path_returns_verifyParsed_bool_from_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hForsPkWord :
        lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
          = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  have hCurrent :
      lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
        = wordOfHash16 specRoot :=
    CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step
      (mkC13State pkSeed pkRoot message sig) specStep forsPk specRoot
      hForsPkWord hLayerStep hSpecFold
  exact accept_path_returns_verifyParsed_bool_from_root
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot hPk hShape hZero hFors hFold
    hlen hg3 hgL hCurrent hWordCmp

/-- Same as `accept_path_returns_verifyParsed_bool_from_layer_step`, but the S4
premise is the concrete masked FORS-compression word rather than the already-bound
`"forsPk"` lookup.  This is the handoff shape for the forthcoming S4/FORS root
correspondence proof. -/
theorem accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hForsCompress :
        CurrentNodeFrame.forsPkCompressWord
          (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  have hForsPkWord :
      lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
        = wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress
      (mkC13State pkSeed pkRoot message sig) forsPk hForsCompress
  exact accept_path_returns_verifyParsed_bool_from_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsPkWord hLayerStep hSpecFold hWordCmp

/-- Range-gated S4/FORS-root form of the final accept adapter.  It replaces the
raw `hForsCompress` premise with the concrete frozen-entry compression frame:
the seed cell is preserved across the real `i < 6` FORS loop, six root cells plus
the forced-root cell are supplied from the pre-copy frame, and a spec-side
compression equality identifies those seven roots with `forsPk`. -/
theorem accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (roots : List Nat)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hRootsLen : roots.length = 7)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega))
    (hForsPkCompress :
        C13Concrete.maskN
          (C13Concrete.keccakWords
            (C13Concrete.wordOfHash16 pkSeed ::
              C13Concrete.adrsForsRootsC13
                (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) ::
              roots))
          = C13Concrete.wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord
        (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk := by
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    have hT :
        lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
          = C13Concrete.idxTree0C13 digest := by
      show _ = C13Concrete.idxTree0C13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
      rw [hPk, hR]
      exact CurrentNodeFrame.afterFors_idxTree0_mkC13State pkSeed pkRoot message sig
    have hL :
        lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
          = C13Concrete.idxLeaf0C13 digest := by
      show _ = C13Concrete.idxLeaf0C13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
      rw [hPk, hR]
      exact CurrentNodeFrame.afterFors_idxLeaf0_mkC13State pkSeed pkRoot message sig
    have hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
      C13Concrete.idxTree0C13_lt pk sigParsed.R message
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_mkC13State_six_plus_last_range
      pkSeed pkRoot message sig digest roots hRootsLen hT hTlt hL hLeaf hmRlo hmRlast]
    exact hForsPkCompress
  exact accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsCompress hLayerStep hSpecFold hWordCmp

/-- Seed-cell form of the final accept adapter.  Compared with
`accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range`,
this takes the exact seed cell needed by FORS public-key compression directly,
instead of a quantified `forsLeafStep` preservation premise. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (roots : List Nat)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hRootsLen : roots.length = 7)
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val = roots[j]'(by omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val = roots[6]'(by omega))
    (hForsPkCompress :
        C13Concrete.maskN
          (C13Concrete.keccakWords
            (C13Concrete.wordOfHash16 pkSeed ::
              C13Concrete.adrsForsRootsC13
                (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) ::
              roots))
          = C13Concrete.wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord
        (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk := by
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    have hT :
        lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
          = C13Concrete.idxTree0C13 digest := by
      show _ = C13Concrete.idxTree0C13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
      rw [hPk, hR]
      exact CurrentNodeFrame.afterFors_idxTree0_mkC13State pkSeed pkRoot message sig
    have hL :
        lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
          = C13Concrete.idxLeaf0C13 digest := by
      show _ = C13Concrete.idxLeaf0C13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
      rw [hPk, hR]
      exact CurrentNodeFrame.afterFors_idxLeaf0_mkC13State pkSeed pkRoot message sig
    have hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
      C13Concrete.idxTree0C13_lt pk sigParsed.R message
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
      pkSeed pkRoot message sig digest roots hRootsLen hT hTlt hL hmSeed hmRlo hmRlast]
    exact hForsPkCompress
  exact accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsCompress hLayerStep hSpecFold hWordCmp

/-- Named-root-list form of
`accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range`.
The seven S4 root cells are stated directly against
`C13Concrete.forsAllRootsC13`, and the compression premise is the named
`C13Concrete.forsPkWordC13` word. -/
theorem accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkWord :
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkCompress :
      C13Concrete.maskN
        (C13Concrete.keccakWords
          (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRootsC13 digest ::
            C13Concrete.forsAllRootsC13 pk digest sigParsed.fors))
        = C13Concrete.wordOfHash16 forsPk := by
    subst hPk
    simpa [digest, C13Concrete.forsPkWordC13] using hForsPkWord
  exact accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
    hPk hR hShape hZero hFors hFold hlen hg3 hgL
    (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors)
    hLeaf
    (by
      intro j hj
      simpa [digest] using hmRlo j hj)
    (by
      simpa [digest] using hmRlast)
    hForsPkCompress hLayerStep hSpecFold hWordCmp

/-- Named-root-list plus direct seed-cell form of the final accept adapter.  This
is the named-root analogue of
`accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step`:
the root cells are stated against `C13Concrete.forsAllRootsC13`, while the seed
cell is supplied directly at `afterFors`. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkWord :
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkCompress :
      C13Concrete.maskN
        (C13Concrete.keccakWords
          (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRootsC13 digest ::
            C13Concrete.forsAllRootsC13 pk digest sigParsed.fors))
        = C13Concrete.wordOfHash16 forsPk := by
    subst hPk
    simpa [digest, C13Concrete.forsPkWordC13] using hForsPkWord
  exact accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
    hPk hR hShape hZero hFors hFold hlen hg3 hgL
    (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors)
    hmSeed
    (by
      intro j hj
      simpa [digest] using hmRlo j hj)
    (by
      simpa [digest] using hmRlast)
    hForsPkCompress hLayerStep hSpecFold hWordCmp

/-- Same named-root accept adapter as
`accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range`,
but the caller supplies only the canonicality/roundtrip fact for the named
masked FORS compression word.  The byte result equality is derived from `hFors`
and `C13Concrete.forsPkFromSigC13_some_eq_hash16_named`. -/
theorem accept_path_returns_verifyParsed_bool_from_named_fors_roots_roundtrip_and_layer_step_range
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
      ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
        = (s.world.memory 0).val)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkRoundtrip :
        wordOfHash16
          (hash16OfWord
            (C13Concrete.forsPkWordC13 pk
              (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
              sigParsed.fors))
          =
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkByte :
      forsPk =
        hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte, hForsPkRoundtrip]
  exact accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hR hShape hZero hFors hFold hlen hg3 hgL hLeaf hmRlo hmRlast
    hForsPkWord hLayerStep hSpecFold hWordCmp

/-- Direct seed-cell plus named-root roundtrip form of the final accept adapter.
This is currently the narrowest named C13 FORS handoff: the caller supplies the
`afterFors` seed cell, named root cells, and the masked-word roundtrip fact. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_roundtrip_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkRoundtrip :
        wordOfHash16
          (hash16OfWord
            (C13Concrete.forsPkWordC13 pk
              (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
              sigParsed.fors))
          =
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = rootMatchesPk c13 specRoot pkRoot) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkByte :
      forsPk =
        hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte, hForsPkRoundtrip]
  exact accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hR hShape hZero hFors hFold hlen hg3 hgL hmSeed hmRlo hmRlast
    hForsPkWord hLayerStep hSpecFold hWordCmp

/-! ## Named C13 accept-obligation bundle. -/

/-- Residual data/control obligations for the current narrow C13 accept handoff.

This packages the remaining post-parse model/spec correspondence surface after
`hFors`/`hFold` are known: the length and guard facts, the S4 seed/root frame,
the canonical FORS public-key roundtrip, the two-layer climb step/fold contract,
and the final word-comparison bridge.  It is intentionally only a bundle; every
field is still a real standalone obligation for later bridge work. -/
structure C13SeedNamedAcceptObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
            = wordNormalize 3688
  hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0
  hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2)
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot

/-- Bundle-consuming form of the current narrow C13 accept adapter.  This is the
shape intended for final integration: parse/spec facts remain explicit, while
the still-open model/spec correspondence facts travel as one named contract. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  exact accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_roundtrip_and_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hR hShape hZero hFors hFold hObs.hlen hObs.hg3 hObs.hgL hObs.hmSeed
    hObs.hmRlo hObs.hmRlast hObs.hForsPkRoundtrip hObs.hLayerStep
    hObs.hSpecFold hObs.hWordCmp

/-- Successful concrete C13 parsing pins the ABI `sig_length` local to the C13
expected length.  This is the byte-spec length gate restated at the model-entry
state. -/
theorem c13_sig_length_of_parseSignatureC13
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
      = wordNormalize 3688 := by
  have hsz : sig.size = c13.sigBytes :=
    C13Concrete.parseSignatureC13_size hParse
  change sig.size = wordNormalize 3688
  rw [hsz]
  rfl

theorem c13_s3Guard_of_parse_forcedZero
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true) :
    SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0 := by
  let digestWord := keccakWords
    [ wordOfHash16 pkSeed
    , wordOfHash16 pkRoot
    , wordOfHash16 (read16 sig 0)
    , baToNatBE message % wordMod
    , hMsgPad ]
  have hR : sigParsed.R = read16 sig 0 :=
    C13Concrete.parseSignatureC13_R hParse
  have hIdxZero :
      (hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message).forsIndex[6]?
        = some 0 := by
    have hz := C13Concrete.forcedZeroOk_c13_forsIndex_six
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) hZero
    rw [hPk, hR] at hz
    exact hz
  have hIdxFormula :
      (hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message).forsIndex[6]?
        = some ((digestWord >>> 114) % 2 ^ 19) := by
    simpa [digestWord] using
      C13Concrete.hMsgC13_forsIndex_six
        { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message
  have hd0 : (digestWord >>> 114) % 2 ^ 19 = 0 := by
    rw [hIdxFormula] at hIdxZero
    injection hIdxZero
  have hdigest :
      lookupValue (afterS2 (mkC13State pkSeed pkRoot message sig)).bindings "digest"
        = digestWord := by
    unfold afterS2 digestWord
    exact SegmentS2R.s2_digest_mkC13State_final pkSeed pkRoot message sig
  have hbound : digestWord < 2 ^ 256 := by
    unfold digestWord
    have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
      [ wordOfHash16 pkSeed
      , wordOfHash16 pkRoot
      , wordOfHash16 (read16 sig 0)
      , baToNatBE message % wordMod
      , hMsgPad ]
    rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
  rw [SegmentS3.s3Guard_eq_forsIndex6
    (afterS2 (mkC13State pkSeed pkRoot message sig)) digestWord hdigest hbound]
  exact hd0

theorem c13_s3Guard_ne_zero_of_parse_forcedZero_false
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = false) :
    SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) ≠ 0 := by
  let digestWord := keccakWords
    [ wordOfHash16 pkSeed
    , wordOfHash16 pkRoot
    , wordOfHash16 (read16 sig 0)
    , baToNatBE message % wordMod
    , hMsgPad ]
  have hR : sigParsed.R = read16 sig 0 :=
    C13Concrete.parseSignatureC13_R hParse
  have hIdxFormula :
      (hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message).forsIndex[6]?
        = some ((digestWord >>> 114) % 2 ^ 19) := by
    simpa [digestWord] using
      C13Concrete.hMsgC13_forsIndex_six
        { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message
  have hIdxNeZero : (digestWord >>> 114) % 2 ^ 19 ≠ 0 := by
    intro hd0
    have hIdxZero :
        (hMsgC13 c13 { pkSeed := pkSeed, pkRoot := pkRoot } (read16 sig 0) message).forsIndex[6]?
          = some 0 := by
      rw [hIdxFormula, hd0]
    have hZeroTrue : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true := by
      rw [hPk, hR]
      unfold forcedZeroOk
      simp [C13Concrete.c13PrimitivesConcrete, c13]
      simpa [c13] using hIdxZero
    rw [hZeroTrue] at hZero
    contradiction
  have hdigest :
      lookupValue (afterS2 (mkC13State pkSeed pkRoot message sig)).bindings "digest"
        = digestWord := by
    unfold afterS2 digestWord
    exact SegmentS2R.s2_digest_mkC13State_final pkSeed pkRoot message sig
  have hbound : digestWord < 2 ^ 256 := by
    unfold digestWord
    have := SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
      [ wordOfHash16 pkSeed
      , wordOfHash16 pkRoot
      , wordOfHash16 (read16 sig 0)
      , baToNatBE message % wordMod
      , hMsgPad ]
    rwa [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at this
  rw [SegmentS3.s3Guard_eq_forsIndex6
    (afterS2 (mkC13State pkSeed pkRoot message sig)) digestWord hdigest hbound]
  exact hIdxNeZero

/-- A one-layer C13 hypertree obligation that packages the control-flow guard
and the data relation together.  The genuine WOTS/XMSS correspondence should
prove this once per layer state: the model checksum guard passes, and the
post-layer `currentNode` tracks the spec step. -/
def LayerGuardedStep (specStep : Nat → ByteArray → ByteArray) : Prop :=
  ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      SegmentLayer3.layerGuard
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true ∧
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)

/-! ## Concrete C13 hypertree layer step

The accept-path bundles above intentionally quantify over an abstract
`specStep`.  The definitions and lemmas in this section instantiate that hook
with the concrete one-layer C13 WOTS/XMSS transition used by
`foldHypertree`.  They are still standalone: the actual model data-cell
correspondence is supplied by explicit hypotheses, and neither `execC13` nor the
byte-level bridge axiom is touched. -/

/-- The pre-shift hypertree index seen by layer `idx`, computed from the original
`H_msg` hypertree index. -/
def c13LayerTreeIdx (digest : HMsg) (idx : Nat) : Nat :=
  digest.hyperIndex / 2 ^ (c13.subtreeH * idx)

/-- The XMSS leaf index consumed by layer `idx`. -/
def c13LayerLeafIdx (digest : HMsg) (idx : Nat) : Nat :=
  c13LayerTreeIdx digest idx % 2 ^ c13.subtreeH

/-- The post-shift tree index used to address WOTS and XMSS at layer `idx`. -/
def c13LayerNextTree (digest : HMsg) (idx : Nat) : Nat :=
  c13LayerTreeIdx digest idx / 2 ^ c13.subtreeH

/-- Concrete byte-level C13 hypertree step for one layer.

On the accepting path this is the successful WOTS+C public-key reconstruction
followed by one XMSS root reconstruction.  The fallback branches make the
function total; accept-path lemmas use explicit hypotheses that rule them out. -/
def c13HypertreeSpecStep
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig) :
    Nat → ByteArray → ByteArray
  | idx, node =>
      match layers[idx]? with
      | none => node
      | some lsig =>
          let treeIdx := c13LayerNextTree digest idx
          let leafIdx := c13LayerLeafIdx digest idx
          if wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
              treeIdx leafIdx node lsig.wots then
            node
          else
            match C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
                treeIdx leafIdx node lsig.wots with
            | none => node
            | some wotsPk =>
                match C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
                    treeIdx leafIdx wotsPk lsig.authPath with
                | none => node
                | some root => root

/-- Layer-aware C13 hypertree step matching the executable layer loop's ADRS
construction.  This intentionally differs from `c13HypertreeSpecStep` for
nonzero layers because the contract includes the loop index in the WOTS and XMSS
addresses, while the current `Primitives` API has no layer field. -/
def c13HypertreeSpecStepAtLayer
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig) :
    Nat → ByteArray → ByteArray
  | idx, node =>
      match layers[idx]? with
      | none => node
      | some lsig =>
          let treeIdx := c13LayerNextTree digest idx
          let leafIdx := c13LayerLeafIdx digest idx
          if wotsGrindingFailsAtLayer C13Concrete.c13PrimitivesConcrete idx c13 pk
              treeIdx leafIdx node lsig.wots then
            node
          else
            match C13Concrete.wotsPkFromSigC13AtLayer idx c13 pk
                treeIdx leafIdx node lsig.wots with
            | none => node
            | some wotsPk =>
                match C13Concrete.xmssRootFromSigC13AtLayer idx c13 pk
                    treeIdx leafIdx wotsPk lsig.authPath with
                | none => node
                | some root => root

/-- The concrete C13 step unfolds to the successful WOTS/XMSS root when the
corresponding layer, grinding check, WOTS reconstruction, and XMSS reconstruction
facts are supplied. -/
theorem c13HypertreeSpecStep_eq_root_of_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (idx : Nat) (node wotsPk root : ByteArray) (lsig : XmssLayerSig)
    (hLayer : layers[idx]? = some lsig)
    (hGrinding :
      wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots = false)
    (hWots :
      C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots
          = some wotsPk)
    (hXmss :
      C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) wotsPk lsig.authPath
          = some root) :
    c13HypertreeSpecStep pk digest layers idx node = root := by
  simp [c13HypertreeSpecStep, hLayer, hGrinding, hWots, hXmss]

/-- The layer-aware C13 step unfolds to the successful WOTS/XMSS root when the
corresponding executable-layer facts are supplied. -/
theorem c13HypertreeSpecStepAtLayer_eq_root_of_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (idx : Nat) (node wotsPk root : ByteArray) (lsig : XmssLayerSig)
    (hLayer : layers[idx]? = some lsig)
    (hGrinding :
      wotsGrindingFailsAtLayer C13Concrete.c13PrimitivesConcrete idx c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots = false)
    (hWots :
      C13Concrete.wotsPkFromSigC13AtLayer idx c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots
          = some wotsPk)
    (hXmss :
      C13Concrete.xmssRootFromSigC13AtLayer idx c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) wotsPk lsig.authPath
          = some root) :
    c13HypertreeSpecStepAtLayer pk digest layers idx node = root := by
  simp [c13HypertreeSpecStepAtLayer, hLayer, hGrinding, hWots, hXmss]

/-- A reusable accept-path layer-step adapter: explicit guard and data-cell facts
for `SegmentLayer3.stepLayer` discharge `LayerGuardedStep` for the concrete C13
hypertree step.  The substantive WOTS/XMSS correspondence is isolated in
`hMerkleNode`, a direct post-step data-cell equality for `"merkleNode"`. -/
theorem layerGuardedStep_c13HypertreeSpecStep_of_merkleNode
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hMerkleNode : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        lookupValue
            (SegmentLayer3.stepLayer
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "merkleNode"
          = wordOfHash16 (c13HypertreeSpecStep pk digest layers idx node)) :
    LayerGuardedStep (c13HypertreeSpecStep pk digest layers) := by
  intro s node idx hRel
  refine ⟨hGuard s node idx hRel, ?_⟩
  exact CurrentNodeFrame.stepLayer_currentNodeRel_of_merkleNode
    s (c13HypertreeSpecStep pk digest layers) node idx
    (hMerkleNode s node idx hRel)

/-- Variant of `layerGuardedStep_c13HypertreeSpecStep_of_merkleNode` for callers
that can prove the final post-step `"currentNode"` equality directly.  This is
the natural shape when the concrete proof follows the executable assignment
`currentNode := merkleNode` instead of exposing the intermediate `"merkleNode"`
cell as the layer-loop contract. -/
theorem layerGuardedStep_c13HypertreeSpecStep_of_currentNode
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hCurrentNode : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        lookupValue
            (SegmentLayer3.stepLayer
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "currentNode"
          = wordOfHash16 (c13HypertreeSpecStep pk digest layers idx node)) :
    LayerGuardedStep (c13HypertreeSpecStep pk digest layers) := by
  intro s node idx hRel
  refine ⟨hGuard s node idx hRel, ?_⟩
  unfold CurrentNodeRel
  exact hCurrentNode s node idx hRel

/-- A single successful concrete layer fact is enough to rewrite the
post-`stepLayer` `"currentNode"` relation to the successful XMSS root. -/
theorem stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (s : RuntimeState) (idx : Nat) (node wotsPk root : ByteArray) (lsig : XmssLayerSig)
    (hLayer : layers[idx]? = some lsig)
    (hGrinding :
      wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots = false)
    (hWots :
      C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots
          = some wotsPk)
    (hXmss :
      C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) wotsPk lsig.authPath
          = some root)
    (hMerkleNode :
      lookupValue
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
          "merkleNode"
        = wordOfHash16 root) :
    CurrentNodeRel wordOfHash16
      (SegmentLayer3.stepLayer
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
      (c13HypertreeSpecStep pk digest layers idx node) := by
  rw [c13HypertreeSpecStep_eq_root_of_success
    pk digest layers idx node wotsPk root lsig hLayer hGrinding hWots hXmss]
  exact CurrentNodeFrame.stepLayer_currentNodeRel_of_merkleNode
    s (fun _ _ => root) node idx hMerkleNode

/-- Current-node form of
`stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success`: the caller proves the
post-step `"currentNode"` word equality directly. -/
theorem stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success_currentNode
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (s : RuntimeState) (idx : Nat) (node wotsPk root : ByteArray) (lsig : XmssLayerSig)
    (hLayer : layers[idx]? = some lsig)
    (hGrinding :
      wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots = false)
    (hWots :
      C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) node lsig.wots
          = some wotsPk)
    (hXmss :
      C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
        (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx) wotsPk lsig.authPath
          = some root)
    (hCurrentNode :
      lookupValue
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
          "currentNode"
        = wordOfHash16 root) :
    CurrentNodeRel wordOfHash16
      (SegmentLayer3.stepLayer
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
      (c13HypertreeSpecStep pk digest layers idx node) := by
  rw [c13HypertreeSpecStep_eq_root_of_success
    pk digest layers idx node wotsPk root lsig hLayer hGrinding hWots hXmss]
  unfold CurrentNodeRel
  exact hCurrentNode

/-- Concrete-success variant of `layerGuardedStep_c13HypertreeSpecStep_of_merkleNode`.
Callers provide the checksum guard fact and, for each related layer state, the
successful WOTS/XMSS spec facts plus the post-step `"merkleNode"` word equality.
This packages those facts into the `LayerGuardedStep` contract consumed by the
guarded layer-loop adapters. -/
theorem layerGuardedStep_c13HypertreeSpecStep_of_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
          layers[idx]? = some lsig ∧
          wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = false ∧
          C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = some wotsPk ∧
          C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            wotsPk lsig.authPath = some root ∧
          lookupValue
              (SegmentLayer3.stepLayer
                { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
              "merkleNode"
            = wordOfHash16 root) :
    LayerGuardedStep (c13HypertreeSpecStep pk digest layers) := by
  intro s node idx hRel
  refine ⟨hGuard s node idx hRel, ?_⟩
  rcases hSuccess s node idx hRel with
    ⟨lsig, wotsPk, root, hLayer, hGrinding, hWots, hXmss, hMerkleNode⟩
  exact stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success
    pk digest layers s idx node wotsPk root lsig hLayer hGrinding hWots hXmss
    hMerkleNode

/-- Concrete-success variant of
`layerGuardedStep_c13HypertreeSpecStep_of_currentNode`.  The success package ends
with the final post-step `"currentNode"` word equality rather than the
intermediate `"merkleNode"` cell. -/
theorem layerGuardedStep_c13HypertreeSpecStep_of_success_currentNode
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
          layers[idx]? = some lsig ∧
          wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = false ∧
          C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = some wotsPk ∧
          C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            wotsPk lsig.authPath = some root ∧
          lookupValue
              (SegmentLayer3.stepLayer
                { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
              "currentNode"
            = wordOfHash16 root) :
    LayerGuardedStep (c13HypertreeSpecStep pk digest layers) := by
  intro s node idx hRel
  refine ⟨hGuard s node idx hRel, ?_⟩
  rcases hSuccess s node idx hRel with
    ⟨lsig, wotsPk, root, hLayer, hGrinding, hWots, hXmss, hCurrentNode⟩
  exact stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success_currentNode
    pk digest layers s idx node wotsPk root lsig hLayer hGrinding hWots hXmss
    hCurrentNode

/-- Concrete-data-cell variant of
`layerGuardedStep_c13HypertreeSpecStep_of_success`.  Callers prove the executable
guard through the natural model fact: after the guard-free layer prefix,
`"digitSum"` is exactly the C13 grinding target `208`. -/
theorem layerGuardedStep_c13HypertreeSpecStep_of_digitSum_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hDigitSum : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        lookupValue
            (SegmentLayer3.afterDigit
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "digitSum"
          = 208)
    (hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
          layers[idx]? = some lsig ∧
          wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = false ∧
          C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = some wotsPk ∧
          C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            wotsPk lsig.authPath = some root ∧
          lookupValue
              (SegmentLayer3.stepLayer
                { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
              "merkleNode"
            = wordOfHash16 root) :
    LayerGuardedStep (c13HypertreeSpecStep pk digest layers) := by
  refine layerGuardedStep_c13HypertreeSpecStep_of_success pk digest layers ?_ hSuccess
  intro s node idx hRel
  exact SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq
    { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }
    (hDigitSum s node idx hRel)

/-- Frame-threaded XMSS climb projection for the structural layer split in
`SegmentLayer3`.  Once callers materialize the generic Merkle frame at the
`"h" = 0` state used by `afterMerkle`, the existing frame theorem gives the
normalized model `"merkleNode"` as the C13 `xmssClimb` word.  The final exact
post-`stepLayer` byte/word equality remains a separate obligation. -/
theorem afterMerkle_model_node_of_xmss_frame
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (auth : List ByteArray) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs merklePtr
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx a))
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hR : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs merklePtr
          { SegmentLayer3.beforeMerkle ls with
            bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
              (wordNormalize 0) }
          (mIdx, node)) :
    wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
      = C13Concrete.xmssClimb seed treeAdrs (wordNormalize 11) 0 mIdx node auth :=
  SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimbFrame_model_node
    "merkleNode" "mIdx" "treeAdrs" "merklePtr"
    pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt hstep
    { SegmentLayer3.beforeMerkle ls with
      bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h" (wordNormalize 0) }
    mIdx node 0 (wordNormalize 11) hD hR

/-- C13-height specialization of `afterMerkle_model_node_of_xmss_frame`, with
the range premise and conclusion stated at literal XMSS height `11`. -/
theorem afterMerkle_model_node_of_xmss_frame_c13
    (pkSeed pkRoot message sig : ByteArray)
    (seed treeAdrs merklePtr : Nat)
    (auth : List ByteArray) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs merklePtr
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx a))
    (hD : ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hR : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs merklePtr
          { SegmentLayer3.beforeMerkle ls with
            bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
              (wordNormalize 0) }
          (mIdx, node)) :
    wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  have h11 : wordNormalize 11 = 11 :=
    SegmentS2.wordNormalize_of_lt (by decide : 11 < 2 ^ 256)
  rw [← h11]
  exact afterMerkle_model_node_of_xmss_frame
    pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt ls mIdx node
    hstep
    (fun i _ hi => hD i (by
      rw [h11] at hi
      omega))
    hR

/-- Raw-relation XMSS climb projection for the structural layer split in
`SegmentLayer3`.  Unlike the frame-threaded theorem above, this exposes exact
post-`afterMerkle` `"merkleNode"` lookup equality, conditional on a raw
per-step climb relation and raw initial relation. -/
theorem afterMerkle_model_node_raw
    (seed treeAdrs : Nat)
    (auth : List ByteArray) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx a))
    (hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hR : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          { SegmentLayer3.beforeMerkle ls with
            bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
              (wordNormalize 0) }
          (mIdx, node)) :
    lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"
      = C13Concrete.xmssClimb seed treeAdrs (wordNormalize 11) 0 mIdx node auth :=
  SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimbRaw_model_node
    "merkleNode" "mIdx" "treeAdrs" "merklePtr"
    seed treeAdrs auth cdAt hstep
    { SegmentLayer3.beforeMerkle ls with
      bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h" (wordNormalize 0) }
    mIdx node 0 (wordNormalize 11) hD hR

/-- C13-height specialization of `afterMerkle_model_node_raw`, with the range
premise and conclusion stated at literal XMSS height `11`. -/
theorem afterMerkle_model_node_raw_c13
    (seed treeAdrs : Nat)
    (auth : List ByteArray) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx" s a →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx a))
    (hD : ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hR : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          { SegmentLayer3.beforeMerkle ls with
            bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
              (wordNormalize 0) }
          (mIdx, node)) :
    lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  have h11 : wordNormalize 11 = 11 :=
    SegmentS2.wordNormalize_of_lt (by decide : 11 < 2 ^ 256)
  rw [← h11]
  exact afterMerkle_model_node_raw
    seed treeAdrs auth cdAt ls mIdx node hstep
    (fun i _ hi => hD i (by
      rw [h11] at hi
      omega))
    hR

/-- Successful concrete C13 XMSS reconstruction exposes the exact `xmssClimb`
word whose high 16 bytes are returned as the byte root.  This is a small
spec-side adapter for the remaining layer `"merkleNode"` bridge; the separate
model-side obligation is still to relate the executable word cell to this climb
word, then discharge the `wordOfHash16`/`hash16OfWord` roundtrip for that word. -/
theorem xmssRootFromSigC13_some_eq_hash16OfWord_xmssClimb
    (pk : PublicKey) (treeIdx leafIdx : Nat)
    (wotsPk root : ByteArray) (auth : List ByteArray)
    (hXmss : C13Concrete.xmssRootFromSigC13 c13 pk treeIdx leafIdx wotsPk auth
        = some root) :
    root =
      hash16OfWord
        (C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
          (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
          (wordOfHash16 wotsPk) auth) := by
  unfold C13Concrete.xmssRootFromSigC13 at hXmss
  injection hXmss with hEq
  exact hEq.symm

/-- Exact post-step `"merkleNode"` adapter once the remaining model-side climb
facts are available.  The concrete XMSS success fact gives `root =
hash16OfWord (xmssClimb ...)`; callers still provide the exact model climb word
and the climb word's `wordOfHash16` roundtrip. -/
theorem stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb
    (pk : PublicKey) (treeIdx leafIdx : Nat)
    (wotsPk root : ByteArray) (auth : List ByteArray)
    (ls : RuntimeState)
    (hXmss : C13Concrete.xmssRootFromSigC13 c13 pk treeIdx leafIdx wotsPk auth
        = some root)
    (hModel :
      lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
        =
          C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
            (wordOfHash16 wotsPk) auth)
    (hRoundtrip :
      wordOfHash16
          (hash16OfWord
            (C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
              (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
              (wordOfHash16 wotsPk) auth))
        =
          C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
            (wordOfHash16 wotsPk) auth) :
    lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
      = wordOfHash16 root := by
  have hRoot :=
    xmssRootFromSigC13_some_eq_hash16OfWord_xmssClimb
      pk treeIdx leafIdx wotsPk root auth hXmss
  rw [hModel, hRoot]
  exact hRoundtrip.symm

/-- Exact post-step `"merkleNode"` adapter in the concrete WOTS-success shape.
The WOTS success fact supplies the climb word roundtrip, leaving only the exact
model-side climb-word equality as a caller obligation. -/
theorem stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
    (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node wotsPk root : ByteArray) (wots : WotsSig) (auth : List ByteArray)
    (ls : RuntimeState)
    (hWots : C13Concrete.wotsPkFromSigC13 c13 pk treeIdx leafIdx node wots
        = some wotsPk)
    (hXmss : C13Concrete.xmssRootFromSigC13 c13 pk treeIdx leafIdx wotsPk auth
        = some root)
    (hModel :
      lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
        =
          C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
            (wordOfHash16 wotsPk) auth) :
    lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
      = wordOfHash16 root :=
  stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb
    pk treeIdx leafIdx wotsPk root auth ls hXmss hModel
    (xmssClimb_roundtrip_of_wots_success
      pk treeIdx leafIdx node wotsPk wots auth hWots)

/-- Exact post-step `"merkleNode"` adapter from the normalized model climb word.
This separates the two remaining model-side obligations: prove the post-step
cell normalizes to the C13 climb word, and prove the raw post-step cell is
already normalized. -/
theorem stepLayer_merkleNode_eq_wordOfHash16_root_of_normalized_xmssClimb_wots_success
    (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node wotsPk root : ByteArray) (wots : WotsSig) (auth : List ByteArray)
    (ls : RuntimeState)
    (hWots : C13Concrete.wotsPkFromSigC13 c13 pk treeIdx leafIdx node wots
        = some wotsPk)
    (hXmss : C13Concrete.xmssRootFromSigC13 c13 pk treeIdx leafIdx wotsPk auth
        = some root)
    (hModel :
      wordNormalize (lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode")
        =
          C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
            (wordOfHash16 wotsPk) auth)
    (hCellNorm :
      wordNormalize (lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode")
        = lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode") :
    lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
      = wordOfHash16 root :=
  stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
    pk treeIdx leafIdx node wotsPk root wots auth ls hWots hXmss
    (by
      rw [← hCellNorm]
      exact hModel)

/-- Normalized post-step `"merkleNode"` adapter in the concrete WOTS-success
shape.  This matches the current model-side frame theorem, which proves the
normalized executable cell equals the C13 climb word; the separate raw-cell
normalization obligation is only needed when callers require exact lookup
equality. -/
theorem stepLayer_merkleNode_norm_eq_wordOfHash16_root_of_xmssClimb_wots_success
    (pk : PublicKey) (treeIdx leafIdx : Nat)
    (node wotsPk root : ByteArray) (wots : WotsSig) (auth : List ByteArray)
    (ls : RuntimeState)
    (hWots : C13Concrete.wotsPkFromSigC13 c13 pk treeIdx leafIdx node wots
        = some wotsPk)
    (hXmss : C13Concrete.xmssRootFromSigC13 c13 pk treeIdx leafIdx wotsPk auth
        = some root)
    (hModel :
      wordNormalize (lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode")
        =
          C13Concrete.xmssClimb (wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree 0 treeIdx) 11 0 leafIdx
            (wordOfHash16 wotsPk) auth) :
    wordNormalize (lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode")
      = wordOfHash16 root := by
  have hRoot :=
    xmssRootFromSigC13_some_eq_hash16OfWord_xmssClimb
      pk treeIdx leafIdx wotsPk root auth hXmss
  rw [hModel, hRoot]
  exact (xmssClimb_roundtrip_of_wots_success
    pk treeIdx leafIdx node wotsPk wots auth hWots).symm

/-- The pure `specFold` used by the loop invariant agrees with the concrete,
layer-aware C13 `foldHypertree` result when the concrete two-layer climb
succeeds. -/
theorem specFold_c13HypertreeSpecStepAtLayer_eq_of_foldHypertree_ok
    (pk : PublicKey) (digest : HMsg) (forsPk specRoot : ByteArray)
    (layers : List XmssLayerSig)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest forsPk layers
        = .ok specRoot) :
    ClimbLoop.specFold (c13HypertreeSpecStepAtLayer pk digest layers)
        forsPk 0 (wordNormalize 2) = specRoot := by
  have hTwo : wordNormalize 2 = 2 := by
    exact SegmentS2.wordNormalize_of_lt (by norm_num [Verity.Core.Uint256.modulus])
  rw [hTwo]
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot layers hFold
  have hStep0 :
      c13HypertreeSpecStepAtLayer pk digest layers 0 forsPk = d.root0 := by
    exact c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest layers 0 forsPk d.wotsPk0 d.root0 d.lsig0
      d.hLayer0
      (by simpa [c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hGrinding0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, c13LayerNextTree,
          c13LayerLeafIdx, c13LayerTreeIdx, c13] using d.hWots0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, c13LayerNextTree,
          c13LayerLeafIdx, c13LayerTreeIdx, c13] using d.hXmss0)
  have hStep1 :
      c13HypertreeSpecStepAtLayer pk digest layers 1 d.root0 = specRoot := by
    exact c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest layers 1 d.root0 d.wotsPk1 specRoot d.lsig1
      d.hLayer1
      (by simpa [c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hGrinding1)
      (by simpa [C13Concrete.c13PrimitivesConcrete, c13LayerNextTree,
          c13LayerLeafIdx, c13LayerTreeIdx, c13] using d.hWots1)
      (by simpa [C13Concrete.c13PrimitivesConcrete, c13LayerNextTree,
          c13LayerLeafIdx, c13LayerTreeIdx, c13] using d.hXmss1)
  simp [ClimbLoop.specFold, hStep0, hStep1]

theorem layerGuardsPass_of_guarded_step
    (pkSeed pkRoot message sig : ByteArray)
    (forsPk : ByteArray) (specStep : Nat → ByteArray → ByteArray)
    (hStart : CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk)
    (hLayerGuardStep : LayerGuardedStep specStep) :
    ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2) :=
  ClimbLoopGuarded.allGuardsPass_of_rel "layer" SegmentLayer3.stepLayer
    SegmentLayer3.layerGuard specStep (CurrentNodeRel wordOfHash16)
    hLayerGuardStep _ forsPk 0 (wordNormalize 2) hStart

theorem layerStep_of_guarded_step
    (specStep : Nat → ByteArray → ByteArray)
    (hLayerGuardStep : LayerGuardedStep specStep) :
    ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node) := by
  intro s node idx h
  exact (hLayerGuardStep s node idx h).2

/-- Concrete C13 layer success facts package directly into the guarded layer-loop
guard trace.  This is the loop-control projection of
`layerGuardedStep_c13HypertreeSpecStep_of_success`: callers supply the concrete
checksum guard and per-layer WOTS/XMSS/`"merkleNode"` success facts, while this
lemma produces the `allGuardsPass` evidence consumed by `SegmentLayer3.execLayerLoop`. -/
theorem layerGuardsPass_of_c13HypertreeSpecStep_success
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (forsPk : ByteArray)
    (hStart : CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
          layers[idx]? = some lsig ∧
          wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = false ∧
          C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = some wotsPk ∧
          C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            wotsPk lsig.authPath = some root ∧
          lookupValue
              (SegmentLayer3.stepLayer
                { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
              "merkleNode"
            = wordOfHash16 root) :
    ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2) :=
  layerGuardsPass_of_guarded_step pkSeed pkRoot message sig forsPk
    (c13HypertreeSpecStep pk digest layers) hStart
    (layerGuardedStep_c13HypertreeSpecStep_of_success
      pk digest layers hGuard hSuccess)

/-- Concrete C13 layer success facts package directly into the per-step
`currentNode` relation used by the accept-path layer fold.  This is the data
projection paired with `layerGuardsPass_of_c13HypertreeSpecStep_success`. -/
theorem layerStep_of_c13HypertreeSpecStep_success
    (pk : PublicKey) (digest : HMsg) (layers : List XmssLayerSig)
    (hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        SegmentLayer3.layerGuard
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true)
    (hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
        ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
          layers[idx]? = some lsig ∧
          wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = false ∧
          C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            node lsig.wots = some wotsPk ∧
          C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13 pk
            (c13LayerNextTree digest idx) (c13LayerLeafIdx digest idx)
            wotsPk lsig.authPath = some root ∧
          lookupValue
              (SegmentLayer3.stepLayer
                { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
              "merkleNode"
            = wordOfHash16 root) :
    ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (c13HypertreeSpecStep pk digest layers idx node) :=
  layerStep_of_guarded_step (c13HypertreeSpecStep pk digest layers)
    (layerGuardedStep_c13HypertreeSpecStep_of_success
      pk digest layers hGuard hSuccess)

/-- The initial C13 layer-loop relation follows from the named S4/FORS frame.

This packages the S4 compression adapters with the seed assignment: once the
`afterFors` seed cell, the six normal root cells, the forced-root cell, and the
canonical named-FORS roundtrip are known, `afterSeed`'s `"currentNode"` binding
already tracks the spec-side `forsPk`.  The following guarded-layer handoff can
therefore start from S4/FORS facts directly instead of carrying a separate
`hLayerStart` premise. -/
theorem layerStart_of_seed_named_fors_roots_roundtrip
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk : ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hR : sigParsed.R = C13Concrete.read16 sig 0)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hmSeed :
      ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
        = wordOfHash16 pkSeed)
    (hmRlo : ∀ j, (h : j < 6) →
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          (0x80 + 32 * j)).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[j]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hmRlast :
      ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
          (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
          0x140).val =
        (C13Concrete.forsAllRootsC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors)[6]'(by
            rw [C13Concrete.forsAllRootsC13_length]
            omega))
    (hForsPkRoundtrip :
        wordOfHash16
          (hash16OfWord
            (C13Concrete.forsPkWordC13 pk
              (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
              sigParsed.fors))
          =
        C13Concrete.forsPkWordC13 pk
          (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
          sigParsed.fors) :
    CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk := by
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPkByte :
      forsPk =
        hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte, hForsPkRoundtrip]
  have hForsPkCompress :
      C13Concrete.maskN
        (C13Concrete.keccakWords
          (C13Concrete.wordOfHash16 pkSeed :: C13Concrete.adrsForsRootsC13 digest ::
            C13Concrete.forsAllRootsC13 pk digest sigParsed.fors))
        = C13Concrete.wordOfHash16 forsPk := by
    subst hPk
    simpa [digest, C13Concrete.forsPkWordC13] using hForsPkWord
  have hT :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13 digest := by
    show _ = C13Concrete.idxTree0C13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
    rw [hPk, hR]
    exact CurrentNodeFrame.afterFors_idxTree0_mkC13State pkSeed pkRoot message sig
  have hLd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13 digest := by
    show _ = C13Concrete.idxLeaf0C13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
    rw [hPk, hR]
    exact CurrentNodeFrame.afterFors_idxLeaf0_mkC13State pkSeed pkRoot message sig
  have hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
    C13Concrete.idxTree0C13_lt pk sigParsed.R message
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord
        (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_seed_mkC13State_six_plus_last
      pkSeed pkRoot message sig digest (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
      (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors) hT hTlt hLd hmSeed]
    · exact hForsPkCompress
    · intro j hj
      simpa [digest] using hmRlo j hj
    · simpa [digest] using hmRlast
  have hForsPkFinal :
      lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
        = wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress
      (mkC13State pkSeed pkRoot message sig) forsPk hForsCompress
  unfold CurrentNodeRel
  rw [MemoryKit.lookupValue_bindValue_ne
    (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
    "layer" "currentNode" (wordNormalize 0) (by decide)]
  rw [CurrentNodeFrame.afterSeed_currentNode]
  exact hForsPkFinal

/-- The same residual C13 accept-obligation bundle as
`C13SeedNamedAcceptObligations`, but with the length guard omitted.  Use this
when a successful concrete C13 parse is already available; the corresponding
`sig_length = 3688` model fact is supplied by
`c13_sig_length_of_parseSignatureC13`. -/
structure C13SeedNamedAcceptDataObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0
  hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2)
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot

/-- The current parse-and-forced-zero based C13 accept-obligation bundle.  Both
the length guard and the S3 forced-zero guard are omitted: successful concrete
C13 parsing supplies the length fact, and
`c13_s3Guard_of_parse_forcedZero` supplies the S3 guard from the same parse fact
plus the spec-side `forcedZeroOk` hypothesis. -/
structure C13SeedNamedAcceptParsedObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      0 (wordNormalize 2)
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
      CurrentNodeRel wordOfHash16 s node →
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
        (specStep idx node)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot

/-- A tighter parsed handoff that replaces the separate layer-loop guard trace
and layer-step relation with one guarded per-layer correspondence plus the
already-derived start relation. -/
structure C13SeedNamedAcceptGuardedLayerObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerStart : CurrentNodeRel wordOfHash16
      { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
          bindings := bindValue
            (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings
            "layer" (wordNormalize 0) }
      forsPk
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot

/-- Parsed guarded-layer C13 obligations with the layer start relation derived
from the S4/FORS frame instead of supplied separately. -/
structure C13SeedNamedAcceptGuardedObligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 pk
            (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot

/-- Byte-shaped guarded C13 obligations with the final word comparison reduced
to canonical root roundtrips.  This is the same residual surface as
`C13SeedNamedAcceptGuardedObligations`, except callers no longer supply
`hWordCmp` directly. -/
structure C13SeedNamedAcceptGuardedRoundtripObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hSpecRootRoundtrip : hash16OfWord (wordOfHash16 specRoot) = specRoot
  hPkRootRoundtrip : hash16OfWord (wordOfHash16 pkRoot) = pkRoot

/-- Byte-shaped guarded C13 obligations after deriving the C13-produced
spec-root roundtrip from successful FORS reconstruction and hypertree folding.
The public key root remains a boundary premise because C13 imposes no byte-level
canonicality check on `pkRoot`. -/
structure C13SeedNamedAcceptGuardedPkRoundtripObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hForsPkRoundtrip :
      wordOfHash16
        (hash16OfWord
          (C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors))
        =
      C13Concrete.forsPkWordC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootRoundtrip : hash16OfWord (wordOfHash16 pkRoot) = pkRoot

/-- Byte-shaped guarded C13 obligations after deriving both C13-produced
roundtrips internally: the FORS public-key compression word is a masked Keccak
word, and the spec-root byte roundtrip follows from successful reconstruction.
The public key root remains a boundary premise because C13 imposes no byte-level
canonicality check on `pkRoot`. -/
structure C13SeedNamedAcceptGuardedPkRootObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootRoundtrip : hash16OfWord (wordOfHash16 pkRoot) = pkRoot

/-- Byte-shaped guarded C13 obligations with the public-key root boundary stated
as the SPHINCS+ byte width rather than the derived C13 byte-roundtrip equation. -/
structure C13SeedNamedAcceptGuardedPkRootSizeObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hmSeed :
    ((afterFors (mkC13State pkSeed pkRoot message sig)).world.memory 0).val
      = wordOfHash16 pkSeed
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations where the seed cell needed by FORS
public-key compression is derived from a range-gated one-step FORS leaf frame.
The remaining FORS root cells are still the substantive S4 correspondence
obligations. -/
structure C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val
  hmRlo : ∀ j, (h : j < 6) →
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x80 + 32 * j)).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hmRlast :
    ((SphincsMinusVerifiers.SegmentS4Finalize.forsFinalizePreCopyStep
        (afterFors (mkC13State pkSeed pkRoot message sig))).world.memory
        0x140).val =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[6]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations where the FORS root cells are derived
from the frozen calldata/auth-path frame and the post-inner-climb `"node"`
correspondence for the six ordinary FORS roots.  The forced-root cell is
recovered from concrete parsing plus the range-gated seed-cell frame. -/
structure C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 →
    ((SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
        { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }).world.memory 0).val
      = (s.world.memory 0).val
  hSite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
    ∃ base,
      s.selector = 0 ∧
      s.world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig ∧
      lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
      lookupValue s.bindings "forsBase" = base ∧
      base < 2 ^ 256 ∧
      lookupValue s.bindings "pathIdx" < 2 ^ 256
  hNode : ∀ j, (hj : j < 6) →
    wordNormalize
      (lookupValue
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
            { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
                  bindings :=
                    bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
                      "i" (wordNormalize 0) }
                0 j) with
              bindings :=
                bindValue
                  (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
                      bindings :=
                        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
                          "i" (wordNormalize 0) }
                    0 j).bindings "i" (wordNormalize j) })).bindings "node") =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations where the range-gated FORS seed frame is
also derived from the frozen calldata/auth-path site package.  Compared with
`C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations`, callers no longer
supply `hLeaf`: every concrete leaf step obtains the seed-cell frame from the
same site facts used for the ordinary-root carry. -/
structure C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray) : Prop where
  hLayerGuardStep : LayerGuardedStep specStep
  hSite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
    ∃ base,
      s.selector = 0 ∧
      s.world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig ∧
      lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
      lookupValue s.bindings "forsBase" = base ∧
      base < 2 ^ 256 ∧
      lookupValue s.bindings "pathIdx" < 2 ^ 256
  hNode : ∀ j, (hj : j < 6) →
    wordNormalize
      (lookupValue
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
            { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
                  bindings :=
                    bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
                      "i" (wordNormalize 0) }
                0 j) with
              bindings :=
                bindValue
                  (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
                      bindings :=
                        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
                          "i" (wordNormalize 0) }
                    0 j).bindings "i" (wordNormalize j) })).bindings "node") =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations at the current narrowest concrete C13
accept boundary.  The layer step is fixed to `c13HypertreeSpecStep`; callers
supply concrete model-side layer guard facts and successful WOTS/XMSS plus
post-step `"merkleNode"` facts, while the adapter derives both
`LayerGuardedStep` and the pure concrete layer `specFold`. -/
structure C13SeedNamedAcceptConcreteLayerSiteRootObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) : Prop where
  hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      SegmentLayer3.layerGuard
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true
  hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
        sigParsed.layers[idx]? = some lsig ∧
            wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          node lsig.wots = false ∧
            C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          node lsig.wots = some wotsPk ∧
            C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          wotsPk lsig.authPath = some root ∧
        lookupValue
            (SegmentLayer3.stepLayer
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "merkleNode"
          = wordOfHash16 root
  hSite : ∀ (s : RuntimeState) (t idx : Nat), t < 6 → idx < 19 →
    ∃ base,
      s.selector = 0 ∧
      s.world.calldata
        = headWords pkSeed pkRoot message sig.size ++ bytesToWords sig ∧
      lookupValue s.bindings "authPtr" = sigDataOffset + (128 + 304 * t) ∧
      lookupValue s.bindings "forsBase" = base ∧
      base < 2 ^ 256 ∧
      lookupValue s.bindings "pathIdx" < 2 ^ 256
  hNode : ∀ j, (hj : j < 6) →
    wordNormalize
      (lookupValue
        (SphincsMinusVerifiers.SegmentS4Fors.forsLeafInnerStep
          (SphincsMinusVerifiers.SegmentS4Fors.forsLeafSetupStep
            { (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
                  bindings :=
                    bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
                      "i" (wordNormalize 0) }
                0 j) with
              bindings :=
                bindValue
                  (ClimbLoop.foldLoop "i" SphincsMinusVerifiers.SegmentS4Fors.forsLeafStep
                    { (afterForsSetup (mkC13State pkSeed pkRoot message sig)) with
                      bindings :=
                        bindValue (afterForsSetup (mkC13State pkSeed pkRoot message sig)).bindings
                          "i" (wordNormalize 0) }
                    0 j).bindings "i" (wordNormalize j) })).bindings "node") =
      (C13Concrete.forsAllRootsC13 { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors)[j]'(by
          rw [C13Concrete.forsAllRootsC13_length]
          omega)
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations after the concrete FORS root-cell bridge
is discharged from `mkC13State`.  Compared with
`C13SeedNamedAcceptConcreteLayerSiteRootObligations`, callers no longer supply
FORS frozen-site facts or post-inner normal-root node correspondences; the root
cells are derived from parsing and the concrete C13 outer leaf states. -/
structure C13SeedNamedAcceptConcreteLayerObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) : Prop where
  hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      SegmentLayer3.layerGuard
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true
  hSuccess : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
        sigParsed.layers[idx]? = some lsig ∧
        wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          node lsig.wots = false ∧
        C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          node lsig.wots = some wotsPk ∧
        C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          wotsPk lsig.authPath = some root ∧
        lookupValue
            (SegmentLayer3.stepLayer
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "merkleNode"
          = wordOfHash16 root
  hPkRootSize : pkRoot.size = 16

/-- Byte-shaped guarded C13 obligations whose concrete layer data proof is
already in the final post-step `"currentNode"` cell.  This is the current-node
boundary needed by the eventual full bridge: callers no longer have to expose
the intermediate `"merkleNode"` cell when they can prove the executable
assignment result directly. -/
structure C13SeedNamedAcceptConcreteLayerCurrentNodeObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) : Prop where
  hGuard : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      SegmentLayer3.layerGuard
        { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) } = true
  hSuccessCurrent : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
    CurrentNodeRel wordOfHash16 s node →
      ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
        sigParsed.layers[idx]? = some lsig ∧
        wotsGrindingFails C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          node lsig.wots = false ∧
        C13Concrete.c13PrimitivesConcrete.wotsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          node lsig.wots = some wotsPk ∧
        C13Concrete.c13PrimitivesConcrete.xmssRootFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c13LayerNextTree
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          (c13LayerLeafIdx
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
          wotsPk lsig.authPath = some root ∧
        lookupValue
            (SegmentLayer3.stepLayer
              { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
            "currentNode"
          = wordOfHash16 root
  hPkRootSize : pkRoot.size = 16

/-- A bounded current-node success fact for one concrete C13 hypertree layer.  The
state `s` is the pre-loop-body accumulator; the executable loop binds `"layer"`
to `idx` before running `SegmentLayer3.stepLayer`. -/
def ConcreteLayerSuccessCurrent
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (node : ByteArray) (idx : Nat) : Prop :=
  ∃ (lsig : XmssLayerSig) (wotsPk root : ByteArray),
    sigParsed.layers[idx]? = some lsig ∧
      wotsGrindingFailsAtLayer C13Concrete.c13PrimitivesConcrete idx c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (c13LayerNextTree
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
      (c13LayerLeafIdx
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
      node lsig.wots = false ∧
      C13Concrete.c13PrimitivesConcrete.wotsPkFromSigAtLayer idx c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (c13LayerNextTree
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
      (c13LayerLeafIdx
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
      node lsig.wots = some wotsPk ∧
      C13Concrete.c13PrimitivesConcrete.xmssRootFromSigAtLayer idx c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (c13LayerNextTree
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
      (c13LayerLeafIdx
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) idx)
      wotsPk lsig.authPath = some root ∧
    lookupValue
        (SegmentLayer3.stepLayer
          { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) }).bindings
        "currentNode"
      = wordOfHash16 root

/-- Bounded concrete C13 current-node obligations.  Unlike
`C13SeedNamedAcceptConcreteLayerCurrentNodeObligations`, this only asks for the two
layer states that `forEach "layer" 2` actually executes, avoiding impossible
facts for `idx >= 2` on a two-layer parsed C13 signature. -/
structure C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk : ByteArray) : Prop where
  hGuard0 :
    SegmentLayer3.layerGuard
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig)) = true
  hSuccessCurrent0 :
    ConcreteLayerSuccessCurrent pkSeed pkRoot message sigParsed
      (CurrentNodeFrame.c13LayerStartState
        (mkC13State pkSeed pkRoot message sig))
      forsPk 0
  hGuard1 :
    SegmentLayer3.layerGuard
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig)) = true
  hSuccessCurrent1 :
    ConcreteLayerSuccessCurrent pkSeed pkRoot message sigParsed
      (CurrentNodeFrame.c13LayerAfterStep0
        (mkC13State pkSeed pkRoot message sig))
            (c13HypertreeSpecStepAtLayer { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.layers 0 forsPk)
      1
  hPkRootSize : pkRoot.size = 16

/-- Successful concrete C13 fold data plus the two executable layer
guard/current-node facts package into the bounded accept obligations.  This
removes the need for bridge callers to restate the pure WOTS/XMSS layer facts
already present in `foldHypertree ... = .ok specRoot`. -/
theorem concrete_layer_current_node_two_step_obligations_of_fold_ok_current_nodes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hGuard0 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        =
          wordOfHash16
            (c13HypertreeSpecStepAtLayer { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk))
    (hGuard1 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        = wordOfHash16 specRoot)
    (hPkRootSize : pkRoot.size = 16) :
    C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
      pkSeed pkRoot message sig sigParsed forsPk := by
  let st := mkC13State pkSeed pkRoot message sig
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot sigParsed.layers hFold
  have hStep0Eq :
      c13HypertreeSpecStepAtLayer pk digest sigParsed.layers 0 forsPk = d.root0 := by
    exact c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 0 forsPk d.wotsPk0 d.root0 d.lsig0
      d.hLayer0
      (by simpa [digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hGrinding0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, digest, c13LayerNextTree,
          c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hWots0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, digest, c13LayerNextTree,
          c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hXmss0)
  refine
    { hGuard0 := hGuard0
      hSuccessCurrent0 := ?_
      hGuard1 := hGuard1
      hSuccessCurrent1 := ?_
      hPkRootSize := hPkRootSize }
  · refine ⟨d.lsig0, d.wotsPk0, d.root0, d.hLayer0, ?_, ?_, ?_, ?_⟩
    · simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hGrinding0
    · simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hWots0
    · simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hXmss0
    · simpa [st, pk, digest, CurrentNodeFrame.c13LayerLoopState0,
        CurrentNodeFrame.c13LayerStartState, hStep0Eq] using hCurrent0
  · refine ⟨d.lsig1, d.wotsPk1, specRoot, d.hLayer1, ?_, ?_, ?_, ?_⟩
    · rw [hStep0Eq]
      simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hGrinding1
    · rw [hStep0Eq]
      simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hWots1
    · simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
        using d.hXmss1
    · simpa [st, pk, digest, CurrentNodeFrame.c13LayerLoopState1,
        CurrentNodeFrame.c13LayerAfterStep0] using hCurrent1

set_option maxHeartbeats 4000000 in
/-- Adapter from frozen-calldata/root-node obligations to the older accept
bundle with explicit FORS root-cell equalities. -/
theorem seed_named_leaf_obligations_of_leaf_root_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hbaseF :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "forsBase"
        = C13Concrete.adrsForsBase
            (C13Concrete.idxTree0C13 digest) (C13Concrete.idxLeaf0C13 digest) := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "forsBase"
        = C13Concrete.adrsForsBase
            (C13Concrete.idxTree0C13
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message))
            (C13Concrete.idxLeaf0C13
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message))
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_forsBase_mkC13State pkSeed pkRoot message sig
  have hTlt : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
    C13Concrete.idxTree0C13_lt pk sigParsed.R message
  have hRoots :=
    CurrentNodeFrame.rootCells_eq_forsAllRootsC13_of_fors_frozen_calldata_nodes_and_parse_range_seed
      pk digest message sig hParse hbaseF hTlt hObs.hSite hObs.hNode hObs.hLeaf
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hLeaf := hObs.hLeaf
      hmRlo := by
        intro j hj
        simpa [pk, digest] using hRoots.1 j hj
      hmRlast := by
        simpa [pk, digest] using hRoots.2
      hSpecFold := hObs.hSpecFold
      hPkRootSize := hObs.hPkRootSize }

/-- Adapter that derives the range-gated leaf-step seed frame from frozen
calldata/auth-path site facts before using the combined FORS root-cell handoff. -/
theorem seed_named_leaf_root_obligations_of_site_root_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep := by
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hLeaf := by
        intro s idx hidx
        have hi :
            lookupValue (bindValue s.bindings "i" (wordNormalize idx)) "i" = idx := by
          rw [MemoryKit.lookupValue_bindValue_self]
          rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
            Nat.mod_eq_of_lt (lt_trans hidx (by decide))]
        exact
          SphincsMinusVerifiers.SegmentS4ForsMerkleFrame.forsLeafStep_preserves_seed_slot_range_of_fors_frozen_calldata
            { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
            idx hidx hi pkSeed pkRoot message sig
            (fun s h hlt => hObs.hSite s idx h hidx hlt)
      hSite := hObs.hSite
      hNode := hObs.hNode
      hSpecFold := hObs.hSpecFold
      hPkRootSize := hObs.hPkRootSize }

/-- Direct adapter from frozen-calldata/root-node obligations to the guarded
accept bundle with concrete seed and root-cell facts.  This bypasses the older
intermediate range-gated `hLeaf`: the `afterFors` seed cell and forced root are
discharged from the actual C13 outer-loop prefix facts. -/
theorem seed_named_pk_root_size_obligations_of_site_root_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    C13SeedNamedAcceptGuardedPkRootSizeObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hRoots :=
    CurrentNodeFrame.rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
      pk message sig hParse
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := CurrentNodeFrame.afterFors_seed_slot_mkC13State pkSeed pkRoot message sig
      hmRlo := by
        intro j hj
        simpa [pk, digest] using hRoots.1 j hj
      hmRlast := by
        simpa [pk, digest] using hRoots.2
      hSpecFold := hObs.hSpecFold
      hPkRootSize := hObs.hPkRootSize }

/-- Parse-based bundle-consuming form of the current narrow C13 accept adapter.
Successful `parseSignatureC13` supplies the length guard; all remaining data
correspondence obligations stay explicit in
`C13SeedNamedAcceptDataObligations`. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_data_obligations_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptDataObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk (C13Concrete.parseSignatureC13_R hParse) hShape hZero hFors hFold ?_
  exact
    { hlen := c13_sig_length_of_parseSignatureC13 pkSeed pkRoot message sig sigParsed hParse
      hg3 := hObs.hg3
      hgL := hObs.hgL
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hLayerStep := hObs.hLayerStep
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

theorem accept_path_returns_verifyParsed_bool_from_seed_named_parsed_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptParsedObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_data_obligations_of_parse
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse hShape hZero hFors hFold ?_
  exact
    { hg3 := c13_s3Guard_of_parse_forcedZero
        pkSeed pkRoot message sig pk sigParsed hPk hParse hZero
      hgL := hObs.hgL
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hLayerStep := hObs.hLayerStep
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_layer_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedLayerObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_parsed_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse hShape hZero hFors hFold ?_
  exact
    { hgL := layerGuardsPass_of_guarded_step
        pkSeed pkRoot message sig forsPk specStep hObs.hLayerStart hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hLayerStep := layerStep_of_guarded_step specStep hObs.hLayerGuardStep
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState := by
  refine accept_path_returns_verifyParsed_bool_from_seed_named_guarded_layer_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse hShape hZero hFors hFold ?_
  exact
    { hLayerStart := layerStart_of_seed_named_fors_roots_roundtrip
        pkSeed pkRoot message sig pk sigParsed forsPk hPk
        (C13Concrete.parseSignatureC13_R hParse) hFors hObs.hmSeed
        hObs.hmRlo hObs.hmRlast hObs.hForsPkRoundtrip
      hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hSpecFold := hObs.hSpecFold
      hWordCmp := hObs.hWordCmp }

/-- Same as `accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations`,
but derives the C13 `signatureShapeOk` guard from successful concrete parsing.
This is the current narrowest parse-based accept handoff: the caller supplies
parse, forced-zero, FORS, fold, and the remaining model/spec correspondence
bundle, but no separate signature-shape fact. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedObligations
        pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (rootMatchesPk c13 specRoot pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pk.pkRoot))) finalState :=
  accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep
    hPk hParse (C13Concrete.parseSignatureC13_shape hParse) hZero hFors hFold hObs

/-- Byte-shaped form of the current C13 accept handoff.  The public key is the
one obtained from the two byte-level public-key arguments, so callers no longer
need to pass the record-equality side condition separately. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedObligations
        pkSeed pkRoot message sig
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  simpa using
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse
      pkSeed pkRoot message sig
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed forsPk specRoot specStep
      rfl hParse hZero hFors hFold hObs

/-- Byte-shaped guarded handoff with the final comparison discharged from
canonical root roundtrips. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedRoundtripObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hSpecFold := hObs.hSpecFold
      hWordCmp :=
        wordCmp_of_wordOfHash16_rootMatchesPk_c13 specRoot pkRoot
          hObs.hSpecRootRoundtrip }

/-- Byte-shaped guarded handoff with the C13-produced spec-root roundtrip
derived internally from `hFors` and `hFold`.  The only final comparison
roundtrip premise left in the bundle is the public-key root roundtrip. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRoundtripObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := hObs.hForsPkRoundtrip
      hSpecFold := hObs.hSpecFold
      hSpecRootRoundtrip :=
        specRoot_roundtrip_of_c13_fors_fold hFors hFold
      hPkRootRoundtrip := hObs.hPkRootRoundtrip }

/-- Byte-shaped guarded handoff after deriving the FORS public-key masked-word
roundtrip and the C13-produced spec-root byte roundtrip internally.  The only
roundtrip premise left in the bundle is for the public-key root. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hForsPkRoundtrip := forsPkWordC13_roundtrip
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors
      hSpecFold := hObs.hSpecFold
      hPkRootRoundtrip := hObs.hPkRootRoundtrip }

/-- Byte-shaped guarded handoff with the public-key-root byte roundtrip derived
from the ordinary 16-byte SPHINCS+ root width. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed := hObs.hmSeed
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hSpecFold := hObs.hSpecFold
      hPkRootRoundtrip := hash16OfWord_wordOfHash16_of_size pkRoot hObs.hPkRootSize }

/-- Byte-shaped guarded handoff with the seed-cell premise derived from a
range-gated FORS leaf-step preservation fact. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  refine
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold ?_
  exact
    { hLayerGuardStep := hObs.hLayerGuardStep
      hmSeed :=
        CurrentNodeFrame.afterFors_seed_slot_mkC13State_of_forsLeafStep_range_preserves
          pkSeed pkRoot message sig hObs.hLeaf
      hmRlo := hObs.hmRlo
      hmRlast := hObs.hmRlast
      hSpecFold := hObs.hSpecFold
      hPkRootSize := hObs.hPkRootSize }

/-- Byte-shaped guarded handoff with both the seed cell and all seven FORS root
cells derived from the range-gated seed frame, frozen calldata/auth-path sites,
and six post-inner-climb `"node"` correspondences. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_root_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  exact
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold
      (seed_named_leaf_obligations_of_leaf_root_obligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep hParse hObs)

/-- Byte-shaped guarded handoff with the range-gated seed frame and all seven
FORS root cells derived from a single frozen calldata/auth-path site package
plus the six post-inner-climb `"node"` correspondences. -/
theorem accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_site_root_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  exact
    accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
      pkSeed pkRoot message sig sigParsed forsPk specRoot specStep
      hParse hZero hFors hFold
      (seed_named_pk_root_size_obligations_of_site_root_obligations
        pkSeed pkRoot message sig sigParsed forsPk specRoot specStep hParse hObs)

/-- Byte-shaped accept handoff from bounded concrete C13 layer facts.  This is the
two-layer version of
`accept_path_returns_verifyParsed_bool_from_concrete_layer_current_node_obligations_of_bytes`:
it uses only the concrete `layer = 0` and `layer = 1` states executed by C13. -/
theorem accept_path_returns_verifyParsed_bool_from_concrete_layer_current_node_two_step_obligations_of_bytes
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
        pkSeed pkRoot message sig sigParsed forsPk) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (rootMatchesPk c13 specRoot pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (rootMatchesPk c13 specRoot pkRoot))) finalState := by
  let st := mkC13State pkSeed pkRoot message sig
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let specStep := c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
  have hTwo : wordNormalize 2 = 2 := by
    exact SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256)
  have hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer
      SegmentLayer3.layerGuard
      { (afterSeed st) with
          bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
      0 (wordNormalize 2) := by
    rw [hTwo]
    unfold ClimbLoopGuarded.allGuardsPass
    refine ⟨?_, ?_⟩
    · simpa [st, CurrentNodeFrame.c13LayerLoopState0,
        CurrentNodeFrame.c13LayerStartState] using hObs.hGuard0
    · refine ⟨?_, True.intro⟩
      simpa [st, CurrentNodeFrame.c13LayerLoopState1,
        CurrentNodeFrame.c13LayerAfterStep0, CurrentNodeFrame.c13LayerLoopState0,
        CurrentNodeFrame.c13LayerStartState, Nat.zero_add] using hObs.hGuard1
  have hRoots :=
    CurrentNodeFrame.rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
      pk message sig hParse
  have hForsPkByte :
      forsPk = hash16OfWord (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors = wordOfHash16 forsPk := by
    rw [hForsPkByte]
    exact (forsPkWordC13_roundtrip pk digest sigParsed.fors).symm
  have hTd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13 digest := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxTree0"
        = C13Concrete.idxTree0C13
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_idxTree0_mkC13State pkSeed pkRoot message sig
  have hLd :
      lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13 digest := by
    show lookupValue (afterFors (mkC13State pkSeed pkRoot message sig)).bindings "idxLeaf0"
        = C13Concrete.idxLeaf0C13
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
    rw [C13Concrete.parseSignatureC13_R hParse]
    exact CurrentNodeFrame.afterFors_idxLeaf0_mkC13State pkSeed pkRoot message sig
  have hTltd : C13Concrete.idxTree0C13 digest < 2 ^ 11 :=
    C13Concrete.idxTree0C13_lt pk sigParsed.R message
  have hForsCompress :
      CurrentNodeFrame.forsPkCompressWord (afterFors st) = wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last
      pkSeed pkRoot message sig digest (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
      (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors) hTd hTltd hLd]
    · simpa [pk, digest, C13Concrete.forsPkWordC13] using hForsPkWord
    · intro j hj
      simpa [pk, digest] using hRoots.1 j hj
    · simpa [pk, digest] using hRoots.2
  have hForsPkFinal :
      lookupValue (afterFinalize st).bindings "forsPk" = wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress st forsPk hForsCompress
  have hStep0 :
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer (CurrentNodeFrame.c13LayerLoopState0 st))
        (specStep 0 forsPk) := by
    rcases hObs.hSuccessCurrent0 with
      ⟨lsig, wotsPk, root, hLayer, hGrinding, hWots, hXmss, hCurrent⟩
    have hStepEq :
        c13HypertreeSpecStepAtLayer pk digest sigParsed.layers 0 forsPk = root := by
      exact c13HypertreeSpecStepAtLayer_eq_root_of_success
        pk digest sigParsed.layers 0 forsPk wotsPk root lsig hLayer
        (by simpa [pk, digest, c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13]
          using hGrinding)
        (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest, c13LayerNextTree,
            c13LayerLeafIdx, c13LayerTreeIdx, c13] using hWots)
        (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest, c13LayerNextTree,
            c13LayerLeafIdx, c13LayerTreeIdx, c13] using hXmss)
    change
      lookupValue (SegmentLayer3.stepLayer (CurrentNodeFrame.c13LayerLoopState0 st)).bindings
          "currentNode" = wordOfHash16 (specStep 0 forsPk)
    rw [show specStep 0 forsPk = root by simpa [specStep] using hStepEq]
    simpa [st, CurrentNodeFrame.c13LayerLoopState0,
      CurrentNodeFrame.c13LayerStartState] using hCurrent
  have hStep1 :
      CurrentNodeRel wordOfHash16
        (SegmentLayer3.stepLayer (CurrentNodeFrame.c13LayerLoopState1 st))
        (specStep 1 (specStep 0 forsPk)) := by
    rcases hObs.hSuccessCurrent1 with
      ⟨lsig, wotsPk, root, hLayer, hGrinding, hWots, hXmss, hCurrent⟩
    have hStepEq :
        c13HypertreeSpecStepAtLayer pk digest sigParsed.layers 1
          (specStep 0 forsPk) = root := by
      exact c13HypertreeSpecStepAtLayer_eq_root_of_success
        pk digest sigParsed.layers 1 (specStep 0 forsPk) wotsPk root lsig hLayer
        (by simpa [pk, digest, specStep, c13LayerNextTree, c13LayerLeafIdx,
            c13LayerTreeIdx, c13] using hGrinding)
        (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest, specStep,
            c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13] using hWots)
        (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
            c13LayerNextTree, c13LayerLeafIdx, c13LayerTreeIdx, c13] using hXmss)
    change
      lookupValue (SegmentLayer3.stepLayer (CurrentNodeFrame.c13LayerLoopState1 st)).bindings
          "currentNode" = wordOfHash16 (specStep 1 (specStep 0 forsPk))
    rw [show specStep 1 (specStep 0 forsPk) = root by simpa [specStep] using hStepEq]
    simpa [st, CurrentNodeFrame.c13LayerLoopState1,
      CurrentNodeFrame.c13LayerAfterStep0] using hCurrent
  have hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot := by
    simpa [pk, digest, specStep] using
      specFold_c13HypertreeSpecStepAtLayer_eq_of_foldHypertree_ok
        pk digest forsPk specRoot sigParsed.layers hFold
  have hCurrent :
      lookupValue (afterLayer st).bindings "currentNode" = wordOfHash16 specRoot :=
    CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_two_steps
      st specStep forsPk specRoot hForsPkFinal hStep0 hStep1 hSpecFold
  have hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
        = rootMatchesPk c13 specRoot pkRoot :=
    wordCmp_of_wordOfHash16_rootMatchesPk_c13 specRoot pkRoot
      (specRoot_roundtrip_of_c13_fors_fold hFors hFold)
  exact accept_path_returns_verifyParsed_bool_from_root
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot rfl
    (C13Concrete.parseSignatureC13_shape hParse) hZero hFors hFold
    (c13_sig_length_of_parseSignatureC13 pkSeed pkRoot message sig sigParsed hParse)
    (c13_s3Guard_of_parse_forcedZero
      pkSeed pkRoot message sig pk sigParsed rfl hParse hZero)
    (by simpa [st] using hgL)
    (by simpa [st] using hCurrent)
    hWordCmp

/-! ## Axiom audit. -/

#print axioms accept_path_returns_verifyParsed_bool
#print axioms accept_path_returns_verifyParsed_bool_linked
#print axioms verifyParsed_ok_branch
#print axioms accept_path_returns_verifyParsed_bool_from_root
#print axioms wordCmp_of_wordOfHash16_iff
#print axioms hash16OfWord_beq_eq_decide
#print axioms byteRoot_beq_eq_decide_of_wordOfHash16_roundtrip
#print axioms wordCmp_of_wordOfHash16_roundtrip
#print axioms wordCmp_boundary_counterexample
#print axioms uint8_toNat_ofNat
#print axioms base256_digit_append
#print axioms base256_digit_decomp
#print axioms base256_uint8_fold_init
#print axioms base256_uint8_fold_lt
#print axioms base256_fold_digit_of_list
#print axioms baToNatBE_eq_data_toList
#print axioms baToNatBE_lt_of_size
#print axioms hash16OfWord_wordOfHash16_of_size
#print axioms highDigitsFold_eq_mod
#print axioms highHalf_mod_digit
#print axioms hash16OfWord_wordOfHash16_hash16OfWord
#print axioms baToNatBE_hash16OfWord
#print axioms wordOfHash16_hash16OfWord_highHalf
#print axioms wordOfHash16_hash16OfWord_maskN_of_lt
#print axioms forsPkWordC13_roundtrip
#print axioms xmssClimb_roundtrip_of_node_roundtrip
#print axioms xmssClimb_roundtrip_of_wots_success
#print axioms hash16OfWord_wordOfHash16_of_canonical
#print axioms specRoot_roundtrip_of_c13_fors_fold
#print axioms accept_path_returns_verifyParsed_bool_from_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_fors_roots_and_layer_step_range
#print axioms accept_path_returns_verifyParsed_bool_from_seed_and_fors_roots_and_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_named_fors_roots_and_layer_step_range
#print axioms accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_and_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_named_fors_roots_roundtrip_and_layer_step_range
#print axioms accept_path_returns_verifyParsed_bool_from_seed_and_named_fors_roots_roundtrip_and_layer_step
#print axioms C13SeedNamedAcceptObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_obligations
#print axioms c13_sig_length_of_parseSignatureC13
#print axioms c13_s3Guard_of_parse_forcedZero
#print axioms c13_s3Guard_ne_zero_of_parse_forcedZero_false
#print axioms LayerGuardedStep
#print axioms c13HypertreeSpecStep_eq_root_of_success
#print axioms layerGuardedStep_c13HypertreeSpecStep_of_merkleNode
#print axioms layerGuardedStep_c13HypertreeSpecStep_of_currentNode
#print axioms stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success
#print axioms stepLayer_currentNodeRel_c13HypertreeSpecStep_of_success_currentNode
#print axioms layerGuardedStep_c13HypertreeSpecStep_of_success
#print axioms layerGuardedStep_c13HypertreeSpecStep_of_success_currentNode
#print axioms layerGuardedStep_c13HypertreeSpecStep_of_digitSum_success
#print axioms afterMerkle_model_node_of_xmss_frame
#print axioms afterMerkle_model_node_of_xmss_frame_c13
#print axioms afterMerkle_model_node_raw
#print axioms afterMerkle_model_node_raw_c13
#print axioms xmssRootFromSigC13_some_eq_hash16OfWord_xmssClimb
#print axioms stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb
#print axioms stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
#print axioms stepLayer_merkleNode_eq_wordOfHash16_root_of_normalized_xmssClimb_wots_success
#print axioms stepLayer_merkleNode_norm_eq_wordOfHash16_root_of_xmssClimb_wots_success
#print axioms specFold_c13HypertreeSpecStepAtLayer_eq_of_foldHypertree_ok
#print axioms layerGuardsPass_of_guarded_step
#print axioms layerStep_of_guarded_step
#print axioms layerGuardsPass_of_c13HypertreeSpecStep_success
#print axioms layerStep_of_c13HypertreeSpecStep_success
#print axioms layerStart_of_seed_named_fors_roots_roundtrip
#print axioms C13SeedNamedAcceptDataObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_data_obligations_of_parse
#print axioms C13SeedNamedAcceptParsedObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_parsed_obligations
#print axioms C13SeedNamedAcceptGuardedLayerObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_layer_obligations
#print axioms C13SeedNamedAcceptGuardedObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_parse
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedRoundtripObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_roundtrip_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRoundtripObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_roundtrip_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRootObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRootSizeObligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_obligations_of_bytes
#print axioms C13SeedNamedAcceptGuardedPkRootSizeLeafObligations
#print axioms C13SeedNamedAcceptGuardedPkRootSizeLeafRootObligations
#print axioms C13SeedNamedAcceptGuardedPkRootSizeSiteRootObligations
#print axioms C13SeedNamedAcceptConcreteLayerSiteRootObligations
#print axioms C13SeedNamedAcceptConcreteLayerObligations
#print axioms C13SeedNamedAcceptConcreteLayerCurrentNodeObligations
#print axioms ConcreteLayerSuccessCurrent
#print axioms C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
#print axioms concrete_layer_current_node_two_step_obligations_of_fold_ok_current_nodes
#print axioms seed_named_leaf_obligations_of_leaf_root_obligations
#print axioms seed_named_leaf_root_obligations_of_site_root_obligations
#print axioms seed_named_pk_root_size_obligations_of_site_root_obligations
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_obligations_of_bytes
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_leaf_root_obligations_of_bytes
#print axioms accept_path_returns_verifyParsed_bool_from_seed_named_guarded_pk_root_size_site_root_obligations_of_bytes
#print axioms accept_path_returns_verifyParsed_bool_from_concrete_layer_current_node_two_step_obligations_of_bytes

end SphincsMinusVerifiers.SegmentAcceptSpec
