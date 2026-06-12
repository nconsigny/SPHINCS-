/-
  Refinement hooks from the Verity models to the SPHINCS- verifier specs.

  Proof chain (see `SphincsMinusVerifiers/README.md`):

      Verity compiled model  refines  ByteLevel.verifyBytes  refines  verifySpec

  * The right link (`verifyBytes` refines `verifySpec`) is proved with no axioms
    in `SphincsMinusVerifierSpec/Spec.lean` (`verifyBytes_eq_verifySpec`) and
    lifted to the observable boundary here by `byteVerifier_refines_spec`.

  * The left link (compiled model refines `verifyBytes`) is the MODEL-EXEC-BRIDGE.
    Verity's executable source semantics (`Compiler/.../SourceSemantics.lean`)
    *does* model the raw `bytes`-calldata surface: `evalExpr` handles
    `.calldataload` / `.calldatasize` / `.param` / `.localVar`, and `execStmt` /
    `execStmtList` run statements over a `RuntimeState`. As of the keccak
    source-semantics work, the interpreter now also models the native `keccak256`
    opcode: `evalExpr` on `.keccak256 off size` returns the *computed* 32-byte
    digest of the word-aligned memory slice (`keccakMemorySlice`, backed by the
    in-tree pure `KeccakEngine`), no longer `none`. So the keccak-family bodies
    C13 no longer reverts at its first hash; its accept subdomain is
    now *reachable* through the real interpreter, and the residual gap there is
    proof size — the line-by-line equivalence of the full hypertree climb against
    `ByteLevel.verifyBytes` — not a framework limitation. The SHA-256 precompile
    (`staticcall` to `0x02`) remains unmodeled (`evalExpr_staticcall = none`): a
    faithful model is blocked by the word-keyed `RuntimeState` memory vs. the
    SLH-DSA body's overlapping sub-word `mstore`s (the `linear_memory_aliasing`
    obligation), so the SHA-2 body still reverts at its first precompile call and
    that accept subdomain stays out of reach pending a byte-addressed memory
    model. Until the full per-body accept equivalence is proved, each model's
    refinement of the byte spec is taken as a **named, documented axiom**, not a
    `sorry`. These axioms are the Lean-level statement of the
    `proofStatus := .assumed` local obligations already attached to each model in
    `Model.lean` (`assembly_refinement`, `linear_memory_aliasing`, the raw-Yul
    revert obligations). They sit alongside the repo's existing keccak
    collision-resistance axioms in the trust surface and are surfaced by
    `#print axioms`. Two unconditional slices of this bridge are already
    discharged (no bridge axiom): the malformed-length subdomain — see the
    `*_interp_agrees_verifyBytes_bad_length` theorems below, which run the real
    interpreter on the real body and prove two-sided agreement with the byte spec
    — and the length-guard pass-through on the good-length subdomain (the first
    accept-path step) — see `*VerifyBody_passes_length_guard` in `Model.lean`,
    which proves the real interpreter falls through the guard to the body when
    `sig_length` matches.

  The per-verifier `*_refines_byte_spec` and `*_refines_spec` results below are
  therefore unconditional theorems whose only assumptions are these explicitly
  named bridge axioms (plus `propext`).

  ## Scope: implementation-correctness, NOT unforgeability

  These proofs establish *implementation correctness*: each compiled verifier
  faithfully runs the SPHINCS- verification *algorithm* and reaches the algorithm's
  verdict (accept / reject / revert), down to the byte-level parsing and the
  +C grinding checks (`verifyParsed_accepts_sound` exhibits the reconstructed
  witness on the accept side).

  They do **not** prove anything about the cryptographic *security* of SPHINCS-.
  Nothing here shows the scheme is EUF-CMA secure, that signatures are
  unforgeable, or that the hash families are collision-resistant; those are
  cryptographic assumptions, not theorems of this development. The `Primitives`
  package is taken abstractly (hashing/parsing supplied as opaque operations), so
  a verifier that "accepts" here means exactly "the on-chain code accepts under the
  modeled algorithm", which is the correct conditional statement: *if* SPHINCS- is
  secure as a scheme, *then* this contract enforces it faithfully. Unforgeability
  is out of scope by design.
-/

import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.C13BridgePrep
import SphincsMinusVerifiers.C13ChainCells
import SphincsMinusVerifiers.C13WotsPkKeccak
import SphincsMinusVerifiers.KeccakBridge
import SphincsMinusVerifiers.SegmentLayer3AddressCells
import SphincsMinusVerifiers.SegmentLayer3MerkleFrame
import SphincsMinusVerifiers.SiblingCalldata

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

private theorem runtimeState_with_bindings_selector
    (st : RuntimeState) (bindings : List (String × Nat)) :
    ({ st with bindings := bindings } : RuntimeState).selector = st.selector := rfl

private theorem runtimeState_with_bindings_calldata
    (st : RuntimeState) (bindings : List (String × Nat)) :
    ({ st with bindings := bindings } : RuntimeState).world.calldata =
      st.world.calldata := rfl

private theorem loopState_selector
    (varName : String) (st : RuntimeState) (index : Nat) :
    (ClimbLoopGuarded.loopState varName st index).selector = st.selector := rfl

private theorem loopState_calldata
    (varName : String) (st : RuntimeState) (index : Nat) :
    (ClimbLoopGuarded.loopState varName st index).world.calldata =
      st.world.calldata := rfl

/--
The proved core: any observable verifier semantics that refines the byte-level
contract spec also refines the abstract algorithmic spec.

This is the lower-spec-refines-abstract-spec step of the layering, lifted to the
observable boundary. It holds for *any* `exec`, with no axiom, by composing the
hypothesis with `ByteLevel.verifyBytes_eq_verifySpec`. `#print axioms` shows it
depends only on `propext`.
-/
theorem byteVerifier_refines_spec
    {p : Primitives} {v : Variant}
    {exec : Bytes → Bytes → Bytes → Bytes → Option Bool}
    (hModel : ByteLevel.ImplementsByteVerifier p v exec)
    (pkSeed pkRoot message sig : Bytes) :
    exec pkSeed pkRoot message sig =
      verifySpec p v { pkSeed := pkSeed, pkRoot := pkRoot } message sig := by
  rw [hModel]
  exact ByteLevel.verifyBytes_eq_verifySpec p v pkSeed pkRoot message sig

/--
The same composition packaged at the `ImplementsVerifier` level: a byte-level
refinement of a model upgrades to an abstract-spec refinement of the same model.
Proved, axiom-free beyond `propext`.
-/
theorem byteVerifier_implements_spec
    {p : Primitives} {v : Variant}
    {exec : Bytes → Bytes → Bytes → Bytes → Option Bool}
    (hModel : ByteLevel.ImplementsByteVerifier p v exec) :
    ImplementsVerifier p v
      (fun pk message sig => exec pk.pkSeed pk.pkRoot message sig) := by
  intro pk message sig
  have h := byteVerifier_refines_spec hModel pk.pkSeed pk.pkRoot message sig
  simpa using h

/-! ### MODEL-EXEC-BRIDGE axioms

Each axiom asserts that one compiled Verity model refines its byte-level spec.
These are the assumed left link of the refinement chain; see the file header and
`SphincsMinusVerifiers/README.md`. They are deliberately fixed per verifier
(distinct primitive packages) and are the only model-specific assumptions the
theorems below rest on. The C13 bridge is narrowed later in this file
to its remaining concrete residuals before being re-exported at the byte-spec
boundary. -/

/-- Assumed: the compiled SHA2 SLH-DSA model refines the byte-level spec under
`slhDsaSha2_128_24_Primitives`. (MODEL-EXEC-BRIDGE.) -/
axiom slhDsaSha2_128_24_refines_byte_spec :
  ByteLevel.ImplementsByteVerifier
    slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 execSlhDsaSha2_128_24

/-- SHA2 SLH-DSA: the compiled model refines the abstract algorithmic spec. -/
theorem slhDsaSha2_128_24_refines_spec
    (pkSeed pkRoot message sig : Bytes) :
    execSlhDsaSha2_128_24 pkSeed pkRoot message sig =
      verifySpec slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
        { pkSeed := pkSeed, pkRoot := pkRoot } message sig :=
  byteVerifier_refines_spec slhDsaSha2_128_24_refines_byte_spec pkSeed pkRoot message sig

/-- SHA2 SLH-DSA packaged at the `ImplementsVerifier` boundary. -/
theorem slhDsaSha2_128_24_implements_spec :
    ImplementsVerifier slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
      (fun pk message sig => execSlhDsaSha2_128_24 pk.pkSeed pk.pkRoot message sig) :=
  byteVerifier_implements_spec slhDsaSha2_128_24_refines_byte_spec

/-! ### Bytes-level bad-length agreement (sound slice of MODEL-EXEC-BRIDGE)

These theorems connect the *real* interpreter run of each compiled `*VerifyBody`
to the byte-level spec `ByteLevel.verifyBytes` on the malformed-length subdomain,
introducing **no axiom**. They strengthen the interpreter-side revert lemmas in
`Model.lean` (which quantify over an abstract `RuntimeState`) into a two-sided
agreement at the `Bytes` boundary: for a state whose ABI-decoded `sig_length`
local equals the calldata signature length, a wrong length makes the compiled
body `revert` (`execStmtList ... = .revert`) *and* makes `verifyBytes` return
`none`. This is a genuine, machine-checked fragment of the `*_refines_byte_spec`
bridge equality, *proved* over a concrete `RuntimeState` rather than assumed; the
accept-path equality remains the carried bridge axiom. The hypotheses are stated
on `wordNormalize sig.size` (the 256-bit word the EVM length prefix decodes to);
for any realistic `sig.size < 2^256` this is exactly `sig.size ≠ <expected>`. -/

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- A concrete `RuntimeState` whose ABI-decoded `sig_length` local is the calldata
signature length. `world`/`selector` are immaterial to the length guard. -/
def badLenState (sigSize : Nat) : RuntimeState :=
  { world := Verity.defaultState
  , bindings := [("sig_length", wordNormalize sigSize)] }

open Compiler.Proofs.IRGeneration.SourceSemantics in
@[simp] theorem badLenState_sig_length (sigSize : Nat) :
    lookupValue (badLenState sigSize).bindings "sig_length" = wordNormalize sigSize := rfl

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13: the real compiled body run and the byte spec agree (both reject by
`revert`/`none`) on every wrong-length input. Proved, no bridge axiom. -/
theorem c13_interp_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : wordNormalize sig.size ≠ wordNormalize 3688) :
    execStmtList [] (badLenState sig.size) c13VerifyBody = .revert
      ∧ ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none := by
  refine ⟨?_, ?_⟩
  · apply c13VerifyBody_reverts_on_bad_length
    rw [badLenState_sig_length]; exact hne
  · apply ByteLevel.verifyBytes_bad_length
    intro h
    exact hne (congrArg wordNormalize h)

/-- C13: the internal concrete observable runner and byte spec agree on every malformed
signature length. This is the same bad-length bridge as
`c13_interp_agrees_verifyBytes_bad_length`, lifted all the way to `execC13Concrete`
over the frozen byte-facing entry state. -/
theorem execC13Concrete_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : sig.size ≠ 3688) :
    execC13Concrete pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig :=
  C13BridgePrep.runC13BodyObserved_revert_on_bad_length
    pkSeed pkRoot message sig hne

/-- C13 bridge reducer: once the good-length branch is covered for every input,
the malformed-length theorem above supplies the complement and yields the full
byte-verifier implementation statement.  This records the exact remaining
MODEL-EXEC-BRIDGE obligation without adding an axiom. -/
theorem c13_refines_byte_spec_of_good_length_cover
    (hGood :
      ∀ pkSeed pkRoot message sig,
        sig.size = 3688 →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  intro pkSeed pkRoot message sig
  by_cases hLen : sig.size = 3688
  · exact hGood pkSeed pkRoot message sig hLen
  · exact execC13Concrete_agrees_verifyBytes_bad_length pkSeed pkRoot message sig hLen

/-- C13 bridge reducer after discharging the forced-zero reject branch.  Once
the forced-zero-true branch is covered for every parsed good-length input, the
proved bad-length bridge and the proved forced-zero-false bridge supply the
complementary cases and yield the full byte-verifier implementation statement. -/
theorem c13_refines_byte_spec_of_forced_zero_true_cover
    (hTrue :
      ∀ pkSeed pkRoot message sig sigParsed,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_good_length_cover
  intro pkSeed pkRoot message sig hLen
  have hLenC13 : sig.size = c13.sigBytes := by
    simpa [c13] using hLen
  obtain ⟨sigParsed, hParse⟩ :=
    C13Concrete.parseSignatureC13_some_of_size (v := c13) (sig := sig) hLenC13
  cases hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) with
  | false =>
      exact
        C13BridgePrep.runC13BodyObserved_revert_on_forced_zero_false_of_parse
          pkSeed pkRoot message sig sigParsed hParse hZero
  | true =>
      exact hTrue pkSeed pkRoot message sig sigParsed hParse hZero

/-- C13 bridge reducer after discharging C13's total FORS reconstruction.  The
remaining cover obligation starts at parsed, forced-zero-true inputs with the
concrete C13 FORS public key fixed to its named compression output. -/
theorem c13_refines_byte_spec_of_fors_some_cover
    (hSome :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_forced_zero_true_cover
  intro pkSeed pkRoot message sig sigParsed hParse hZero
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let forsPk := C13Concrete.hash16OfWord
    (C13Concrete.forsPkWordC13 pk digest sigParsed.fors)
  have hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk digest
      sigParsed.fors = some forsPk := by
    simpa [pk, digest, forsPk, C13Concrete.c13PrimitivesConcrete] using
      C13Concrete.forsPkFromSigC13_eq_named c13 pk digest sigParsed.fors
  exact hSome pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors

/-- C13 bridge reducer after splitting the concrete C13 hypertree fold.  Parsed
C13 signatures rule out the `.rejected` branch, so the remaining proof surface is
only the successful `.ok root` branch and the executable-revert `.reverted`
branch. -/
theorem c13_refines_byte_spec_of_fold_result_cover
    (hOk :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig)
    (hReverted :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_fors_some_cover
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  cases hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest
      forsPk sigParsed.layers with
  | ok specRoot =>
      exact hOk pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero (by simpa [pk, digest] using hFors)
        (by simpa [pk, digest] using hFold)
  | reverted =>
      exact hReverted pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero (by simpa [pk, digest] using hFors)
        (by simpa [pk, digest] using hFold)
  | rejected =>
      have hNotRejected :
          foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest
            forsPk sigParsed.layers ≠ .rejected :=
        C13Concrete.foldHypertree_c13_ne_rejected_of_parse hParse pk digest forsPk
      exact False.elim (hNotRejected hFold)

/-- Export-boundary adapter for C13.  The public `execC13` runner is
definitionally `execC13Concrete`, so any completed concrete bridge proof can be
exposed at the former axiom's exact type. -/
theorem c13_refines_byte_spec_exported_of_concrete
    (hConcrete :
      ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13 := by
  simpa [execC13] using hConcrete

/-- The first C13 layer-loop guard state, in the exact shape consumed by the
revert bridge. -/
def c13FirstLayerGuardState
    (pkSeed pkRoot message sig : Bytes) : RuntimeState :=
  ClimbLoopGuarded.loopState "layer"
    { (SegmentCompose.afterSeed (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue
          (SegmentCompose.afterSeed
            (mkC13State pkSeed pkRoot message sig)).bindings
          "layer" (wordNormalize 0) } 0

/-- The second C13 layer-loop guard state, in the exact shape consumed by the
revert bridge. -/
def c13SecondLayerGuardState
    (pkSeed pkRoot message sig : Bytes) : RuntimeState :=
  ClimbLoopGuarded.loopState "layer"
    (SegmentLayer3.stepLayer
      (c13FirstLayerGuardState pkSeed pkRoot message sig)) 1

/-- The first guard state used by the revert bridge is the same concrete layer-0
state used by the accept-side current-node facts. -/
theorem c13FirstLayerGuardState_eq_c13LayerLoopState0
    (pkSeed pkRoot message sig : Bytes) :
    c13FirstLayerGuardState pkSeed pkRoot message sig =
      CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig) := rfl

/-- The second guard state used by the revert bridge is the same concrete layer-1
state used by the accept-side current-node facts. -/
theorem c13SecondLayerGuardState_eq_c13LayerLoopState1
    (pkSeed pkRoot message sig : Bytes) :
    c13SecondLayerGuardState pkSeed pkRoot message sig =
      CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig) := rfl

/-- The concrete C13 FORS-finalize prefix binds `"forsPk"` to the parsed
spec-side FORS public key word. -/
theorem c13AfterFinalize_forsPk_of_parse_fors
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk) :
    lookupValue
        (SegmentCompose.afterFinalize
          (mkC13State pkSeed pkRoot message sig)).bindings
        "forsPk" = C13Concrete.wordOfHash16 forsPk := by
  let st := mkC13State pkSeed pkRoot message sig
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hRoots :=
    CurrentNodeFrame.rootCells_eq_forsAllRootsC13_of_hMsg_parse_concrete
      pk message sig hParse
  have hForsPkByte :
      forsPk = C13Concrete.hash16OfWord
        (C13Concrete.forsPkWordC13 pk digest sigParsed.fors) := by
    exact C13Concrete.forsPkFromSigC13_some_eq_hash16_named (v := c13)
      (pk := pk) (digest := digest) (fors := sigParsed.fors) hFors
  have hForsPkWord :
      C13Concrete.forsPkWordC13 pk digest sigParsed.fors =
        C13Concrete.wordOfHash16 forsPk := by
    rw [hForsPkByte]
    exact (SegmentAcceptSpec.forsPkWordC13_roundtrip pk digest sigParsed.fors).symm
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
      CurrentNodeFrame.forsPkCompressWord (afterFors st) =
        C13Concrete.wordOfHash16 forsPk := by
    rw [CurrentNodeFrame.forsPkCompressWord_eq_of_afterFors_concrete_mkC13State_six_plus_last
      pkSeed pkRoot message sig digest (C13Concrete.forsAllRootsC13 pk digest sigParsed.fors)
      (C13Concrete.forsAllRootsC13_length pk digest sigParsed.fors) hTd hTltd hLd]
    · simpa [pk, digest, C13Concrete.forsPkWordC13] using hForsPkWord
    · intro j hj
      simpa [pk, digest] using hRoots.1 j hj
    · simpa [pk, digest] using hRoots.2
  exact CurrentNodeFrame.afterFinalize_forsPk_of_compress st forsPk hForsCompress

/-- The layer-0 guarded-loop state preserves the seed scratch word from
`afterSeed`. -/
theorem c13FirstLayerGuardState_seed_slot
    (pkSeed pkRoot message sig : Bytes) :
    ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  unfold c13FirstLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  rw [MemoryKit.withBindings_preserves_memory_val]
  exact CurrentNodeFrame.afterSeed_seed_slot_mkC13State pkSeed pkRoot message sig

/-- The layer-0 pre-digest prefix does not disturb the seed scratch word. -/
theorem c13FirstLayerBeforeDigest_seed_slot
    (pkSeed pkRoot message sig : Bytes) :
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [SegmentLayer3.beforeDigest_preserves_memory_zero]
  exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig

/-- If the first accepting C13 layer preserves the seed scratch word, then the
layer-1 pre-digest seed slot is already fixed.  This isolates the remaining
seed proof obligation at the exact `stepLayer` frame boundary. -/
theorem c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
    (pkSeed pkRoot message sig : Bytes)
    (hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed) :
    ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [SegmentLayer3.beforeDigest_preserves_memory_zero]
  unfold c13SecondLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  exact hStepSeed

/-- The first accepting C13 layer seed fact follows from the raw `stepLayer`
memory-frame obligation for scratch cell `0x00`. -/
theorem c13FirstStepLayer_seed_slot_of_memory_zero
    (pkSeed pkRoot message sig : Bytes)
    (hStepMem :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val) :
    ((SegmentLayer3.stepLayer
      (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [hStepMem]
  exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig

/-- The layer-0 guarded-loop binding updates do not disturb the seed-stage
`"currentNode"` binding. -/
theorem c13FirstLayerGuardState_currentNode
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" =
      lookupValue
        (SegmentCompose.afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings
        "forsPk" := by
  unfold c13FirstLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_currentNode
    (mkC13State pkSeed pkRoot message sig)

/-- The layer-0 guarded-loop binding updates do not disturb the seed-stage
`"idxTree"` binding. -/
theorem c13FirstLayerGuardState_idxTree
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
        "idxTree" =
      lookupValue
        (SegmentCompose.afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings
        "htIdx" := by
  unfold c13FirstLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "idxTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "idxTree" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_idxTree
    (mkC13State pkSeed pkRoot message sig)

/-- The layer-0 guarded-loop `"idxTree"` binding is the parsed C13 `H_msg`
hypertree index. -/
theorem c13FirstLayerGuardState_idxTree_hyperIndex
    (pkSeed pkRoot message sig : Bytes) {sigParsed : Signature}
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
        "idxTree"
      =
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex := by
  rw [c13FirstLayerGuardState_idxTree]
  rw [CurrentNodeFrame.afterFinalize_htIdx_mkC13State]
  rw [C13Concrete.parseSignatureC13_R hParse]
  rfl

/-- The layer-0 guarded-loop binding updates do not disturb the seed-stage
`"sigOff"` binding. -/
theorem c13FirstLayerGuardState_sigOff
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
        "sigOff" = wordNormalize 1952 := by
  unfold c13FirstLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_sigOff
    (mkC13State pkSeed pkRoot message sig)

/-- The layer-0 guarded-loop binding updates do not disturb the seed-stage
`"sigBase"` binding. -/
theorem c13FirstLayerGuardState_sigBase
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
        "sigBase" = sigDataOffset := by
  unfold c13FirstLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  exact CurrentNodeFrame.afterSeed_sigBase_mkC13State pkSeed pkRoot message sig

/-- The layer-1 guarded-loop binding updates and the first accepted layer do not
disturb the seed-stage `"sigBase"` binding. -/
theorem c13SecondLayerGuardState_sigBase
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "sigBase" = sigDataOffset := by
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  rw [SegmentLayer3.stepLayer_sigBase_eq]
  exact c13FirstLayerGuardState_sigBase pkSeed pkRoot message sig

/-- The layer-1 guarded-loop binding updates and the first accepted layer advance
the seed-stage `"sigOff"` to the second XMSS-layer signature offset. -/
theorem c13SecondLayerGuardState_sigOff
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "sigOff" = 2820 := by
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]
  have hSigOffRaw :
      lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
          "sigOff" = 1952 := by
    rw [c13FirstLayerGuardState_sigOff]
    exact SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)
  have hStep :=
    SegmentLayer3.stepLayer_sigOff_eq_of_sigOff
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      1952 hSigOffRaw
      (by decide : 1952 < 2 ^ 256)
      (by decide : 1952 + 688 < 2 ^ 256)
      (by decide : 1952 + 692 < 2 ^ 256)
      (by decide : 1952 + 868 < 2 ^ 256)
  simpa using hStep

/-- The layer-0 guarded-loop `"layer"` binding is zero. -/
theorem c13FirstLayerGuardState_layer
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
        "layer" = 0 := by
  unfold c13FirstLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_self]
  exact SegmentS2.wordNormalize_of_lt (by decide : 0 < 2 ^ 256)

/-- The layer-1 guarded-loop `"layer"` binding is one. -/
theorem c13SecondLayerGuardState_layer
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "layer" = 1 := by
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_self]
  exact SegmentS2.wordNormalize_of_lt (by decide : 1 < 2 ^ 256)

/-- The layer-0 guarded-loop state carries the frozen ABI selector. -/
theorem c13FirstLayerGuardState_selector
    (pkSeed pkRoot message sig : Bytes) :
    (c13FirstLayerGuardState pkSeed pkRoot message sig).selector = 0 := by
  unfold c13FirstLayerGuardState
  rw [loopState_selector, runtimeState_with_bindings_selector]
  exact CurrentNodeFrame.afterSeed_selector_mkC13State pkSeed pkRoot message sig

/-- The layer-0 guarded-loop state carries the frozen ABI calldata image. -/
theorem c13FirstLayerGuardState_calldata
    (pkSeed pkRoot message sig : Bytes) :
    (c13FirstLayerGuardState pkSeed pkRoot message sig).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold c13FirstLayerGuardState
  rw [loopState_calldata, runtimeState_with_bindings_calldata]
  exact CurrentNodeFrame.afterSeed_calldata_mkC13State pkSeed pkRoot message sig

/-- The layer-1 guarded-loop state carries the frozen ABI selector. -/
theorem c13SecondLayerGuardState_selector
    (pkSeed pkRoot message sig : Bytes) :
    (c13SecondLayerGuardState pkSeed pkRoot message sig).selector = 0 := by
  unfold c13SecondLayerGuardState
  rw [loopState_selector]
  have hFrame :=
    SegmentLayer3.stepLayer_preserves_selector_calldata
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
  rw [hFrame.1]
  exact c13FirstLayerGuardState_selector pkSeed pkRoot message sig

/-- The layer-1 guarded-loop state carries the frozen ABI calldata image. -/
theorem c13SecondLayerGuardState_calldata
    (pkSeed pkRoot message sig : Bytes) :
    (c13SecondLayerGuardState pkSeed pkRoot message sig).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold c13SecondLayerGuardState
  rw [loopState_calldata]
  have hFrame :=
    SegmentLayer3.stepLayer_preserves_selector_calldata
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
  rw [hFrame.2]
  exact c13FirstLayerGuardState_calldata pkSeed pkRoot message sig

/-- The layer-1 guarded-loop `"idxTree"` binding is the parsed C13 hypertree
index shifted by one XMSS subtree height. -/
theorem c13SecondLayerGuardState_idxTree_hyperIndex
    (pkSeed pkRoot message sig : Bytes) {sigParsed : Signature}
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "idxTree" = digest.hyperIndex / 2048 := by
  intro pk digest
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "idxTree" _ (by decide)]
  exact SegmentLayer3.stepLayer_idxTree_eq_of_idxTree
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    digest.hyperIndex
    (c13FirstLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_trans
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
      (by decide : 2 ^ 22 < 2 ^ 256))

/-- Layer-0 pre-digest `"idxLeaf"` is the low 11 bits of the parsed C13
hypertree index. -/
theorem c13FirstLayerBeforeDigest_idxLeaf_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "idxLeaf" = digest.hyperIndex % 2048 := by
  intro pk digest
  exact SegmentLayer3.beforeDigest_idxLeaf_eq_of_idxTree
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    digest.hyperIndex
    (c13FirstLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_trans
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
      (by decide : 2 ^ 22 < 2 ^ 256))

/-- Layer-0 pre-digest `"idxTree"` is the parsed C13 hypertree index shifted by
the C13 subtree height. -/
theorem c13FirstLayerBeforeDigest_idxTree_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "idxTree" = digest.hyperIndex / 2048 := by
  intro pk digest
  exact SegmentLayer3.beforeDigest_idxTree_eq_of_idxTree
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    digest.hyperIndex
    (c13FirstLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_trans
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
      (by decide : 2 ^ 22 < 2 ^ 256))

/-- Layer-0 pre-Merkle `"mIdx"` is the low 11 bits of the parsed C13
hypertree index. -/
theorem c13FirstLayerBeforeMerkle_mIdx_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeMerkle
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "mIdx" = digest.hyperIndex % 2048 := by
  intro pk digest
  exact SegmentLayer3.beforeMerkle_mIdx_eq_of_idxTree
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    digest.hyperIndex
    (c13FirstLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_trans
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
      (by decide : 2 ^ 22 < 2 ^ 256))

/-- Layer-1 pre-Merkle `"mIdx"` is the low 11 bits of the shifted C13
hypertree index. -/
theorem c13SecondLayerBeforeMerkle_mIdx_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeMerkle
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
        "mIdx" = (digest.hyperIndex / 2048) % 2048 := by
  intro pk digest
  exact SegmentLayer3.beforeMerkle_mIdx_eq_of_idxTree
    (c13SecondLayerGuardState pkSeed pkRoot message sig)
    (digest.hyperIndex / 2048)
    (c13SecondLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_of_le_of_lt
      (Nat.div_le_self _ _)
      (lt_trans
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
        (by decide : 2 ^ 22 < 2 ^ 256)))

/-- A C13 XMSS-tree address assembled from bounded layer/tree indices is already
an EVM word. -/
theorem c13_adrsXmssTree_lt_of_bounds
    (layer treeIdx : Nat)
    (hLayer : layer < 2 ^ 32)
    (hTree : treeIdx < 2 ^ 22) :
    C13Concrete.adrsXmssTree layer treeIdx < 2 ^ 256 := by
  have h224 : layer <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hLayer (by decide)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
  have h128 : treeIdx <<< 128 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      treeIdx * 2 ^ 128 < 2 ^ 22 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hTree (by decide)
      _ < 2 ^ 256 := by decide
  have h96 : 2 <<< 96 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    decide
  have hinner : (treeIdx <<< 128 ||| 2 <<< 96) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h96
  simpa [C13Concrete.adrsXmssTree, Nat.lor_assoc] using
    Nat.bitwise_lt_two_pow h224 hinner

/-- Layer-0 `beforeMerkle` is a concrete frozen C13 Merkle site. -/
theorem c13FirstLayerBeforeMerkle_layerFrozenSite
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    SegmentLayer3MerkleFrame.LayerFrozenSite 0 pkSeed pkRoot message sig
      (SegmentLayer3.beforeMerkle
        (c13FirstLayerGuardState pkSeed pkRoot message sig)) := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let treeAdrs : Nat := C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048)
  refine ⟨treeAdrs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (SegmentLayer3.beforeMerkle_preserves_selector_calldata
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).1.trans
        (c13FirstLayerGuardState_selector pkSeed pkRoot message sig)
  · exact
      (SegmentLayer3.beforeMerkle_preserves_selector_calldata
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).2.trans
        (c13FirstLayerGuardState_calldata pkSeed pkRoot message sig)
  · have hSigOffRaw :
        lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
            "sigOff" = 1952 := by
      rw [c13FirstLayerGuardState_sigOff]
      exact SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)
    have hPtr :=
      SegmentLayer3.beforeMerkle_merklePtr_eq_of_sigBase_sigOff
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        sigDataOffset 1952
        (c13FirstLayerGuardState_sigBase pkSeed pkRoot message sig)
        hSigOffRaw
        (by decide : sigDataOffset < 2 ^ 256)
        (by decide : 1952 < 2 ^ 256)
        (by decide : 1952 + 688 < 2 ^ 256)
        (by decide : 1952 + 692 < 2 ^ 256)
        (by decide : sigDataOffset + (1952 + 692) < 2 ^ 256)
    simpa using hPtr
  · dsimp [treeAdrs]
    exact SegmentLayer3.beforeMerkle_treeAdrs_eq_of_layer_idxTree
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      0 digest.hyperIndex
      (c13FirstLayerGuardState_layer pkSeed pkRoot message sig)
      (c13FirstLayerGuardState_idxTree_hyperIndex pkSeed pkRoot message sig hParse)
      (by decide : 0 < 2 ^ 32)
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
  · dsimp [treeAdrs]
    exact c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  · rw [c13FirstLayerBeforeMerkle_mIdx_hyperIndex pkSeed pkRoot message sig sigParsed hParse]
    exact lt_trans (Nat.mod_lt _ (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 256)

/-- Layer-0 `stepLayer` preserves seed cell `0x00` from `c13FirstLayerGuardState`,
derived directly from the parsed-signature `LayerFrozenSite` and the WOTS/copy
loop memory-zero frames.  This discharges the first conjunct of the cover's
`hRevertedLayerFacts` from `hParse` alone, eliminating the need for the caller
to thread it through. -/
theorem c13FirstStepLayer_memory_zero_eq_of_parse
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val := by
  have hSite :=
    c13FirstLayerBeforeMerkle_layerFrozenSite pkSeed pkRoot message sig sigParsed hParse
  have hStep :=
    SegmentLayer3MerkleFrame.stepLayer_preserves_memory_zero_of_layerFrozenSite_range
      (c13FirstLayerGuardState pkSeed pkRoot message sig) 0 pkSeed pkRoot message sig
      SegmentLayer3.wotsOuterForEach_preserves_memory_zero
      SegmentLayer3.copyForEach_preserves_memory_zero
      (by decide : 0 < 2) hSite
  rw [hStep]
  exact SegmentLayer3.afterDigit_preserves_memory_zero _

/-- Layer-1 `beforeMerkle` is a concrete frozen C13 Merkle site. -/
theorem c13SecondLayerBeforeMerkle_layerFrozenSite
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    SegmentLayer3MerkleFrame.LayerFrozenSite 1 pkSeed pkRoot message sig
      (SegmentLayer3.beforeMerkle
        (c13SecondLayerGuardState pkSeed pkRoot message sig)) := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let treeAdrs : Nat := C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048)
  refine ⟨treeAdrs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (SegmentLayer3.beforeMerkle_preserves_selector_calldata
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).1.trans
        (c13SecondLayerGuardState_selector pkSeed pkRoot message sig)
  · exact
      (SegmentLayer3.beforeMerkle_preserves_selector_calldata
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).2.trans
        (c13SecondLayerGuardState_calldata pkSeed pkRoot message sig)
  · have hPtr :=
      SegmentLayer3.beforeMerkle_merklePtr_eq_of_sigBase_sigOff
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        sigDataOffset 2820
        (c13SecondLayerGuardState_sigBase pkSeed pkRoot message sig)
        (c13SecondLayerGuardState_sigOff pkSeed pkRoot message sig)
        (by decide : sigDataOffset < 2 ^ 256)
        (by decide : 2820 < 2 ^ 256)
        (by decide : 2820 + 688 < 2 ^ 256)
        (by decide : 2820 + 692 < 2 ^ 256)
        (by decide : sigDataOffset + (2820 + 692) < 2 ^ 256)
    simpa using hPtr
  · dsimp [treeAdrs]
    exact SegmentLayer3.beforeMerkle_treeAdrs_eq_of_layer_idxTree
      (c13SecondLayerGuardState pkSeed pkRoot message sig)
      1 (digest.hyperIndex / 2048)
      (c13SecondLayerGuardState_layer pkSeed pkRoot message sig)
      (c13SecondLayerGuardState_idxTree_hyperIndex pkSeed pkRoot message sig hParse)
      (by decide : 1 < 2 ^ 32)
      (lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  · dsimp [treeAdrs]
    exact c13_adrsXmssTree_lt_of_bounds 1 ((digest.hyperIndex / 2048) / 2048)
      (by decide : 1 < 2 ^ 32)
      (lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)))
  · rw [c13SecondLayerBeforeMerkle_mIdx_hyperIndex pkSeed pkRoot message sig sigParsed hParse]
    exact lt_trans (Nat.mod_lt _ (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 256)

/-- Layer-0 pre-digest `"wotsAdrs"` is the C13 WOTS hash-base address assembled
from layer zero and the split parsed hypertree index. -/
theorem c13FirstLayerBeforeDigest_wotsAdrs_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "wotsAdrs" =
      C13Concrete.adrsWotsHashBase
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  exact SegmentLayer3.beforeDigest_wotsAdrs_eq_of_layer_idxTree
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    0 digest.hyperIndex
    (c13FirstLayerGuardState_layer pkSeed pkRoot message sig)
    (c13FirstLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (by decide : 0 < 2 ^ 32)
    (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)

/-- The layer-0 C13 WOTS hash-base address is already an EVM word. -/
theorem c13FirstLayer_wotsAdrs_hyperIndex_norm
    (pkSeed pkRoot message : Bytes) (sigParsed : Signature) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    wordNormalize
        (C13Concrete.adrsWotsHashBase
          0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
      =
        C13Concrete.adrsWotsHashBase
          0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  have h128 :
      (digest.hyperIndex / 2048) <<< 128 < 2 ^ 256 := by
    have hnext : digest.hyperIndex / 2048 < 2 ^ 11 := by
      simpa using C13Concrete.hMsgC13_hyperIndex_div_2048_lt pk sigParsed.R message
    rw [Nat.shiftLeft_eq]
    calc
      (digest.hyperIndex / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h64 :
      (digest.hyperIndex % 2048) <<< 64 < 2 ^ 256 := by
    have hleaf : digest.hyperIndex % 2048 < 2048 :=
      Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      (digest.hyperIndex % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have h0 : (0 : Nat) <<< 224 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have hinner :
      ((digest.hyperIndex / 2048) <<< 128 |||
          ((digest.hyperIndex % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h64
  have haddr :
      ((0 : Nat) <<< 224 |||
        ((digest.hyperIndex / 2048) <<< 128 |||
          ((digest.hyperIndex % 2048) <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h0 hinner
  simpa [C13Concrete.adrsWotsHashBase, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

/-- The layer-1 C13 WOTS hash-base address is already an EVM word. -/
theorem c13SecondLayer_wotsAdrs_hyperIndex_norm
    (pkSeed pkRoot message : Bytes) (sigParsed : Signature) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    wordNormalize
        (C13Concrete.adrsWotsHashBase
          1 ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048))
      =
        C13Concrete.adrsWotsHashBase
          1 ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  have h128 :
      (((digest.hyperIndex / 2048) / 2048) <<< 128) < 2 ^ 256 := by
    have hnext : (digest.hyperIndex / 2048) / 2048 < 2 ^ 22 :=
      lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
    rw [Nat.shiftLeft_eq]
    calc
      ((digest.hyperIndex / 2048) / 2048) * 2 ^ 128 < 2 ^ 22 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h64 :
      (((digest.hyperIndex / 2048) % 2048) <<< 64) < 2 ^ 256 := by
    have hleaf : (digest.hyperIndex / 2048) % 2048 < 2048 :=
      Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      ((digest.hyperIndex / 2048) % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have hLayer : (1 : Nat) <<< 224 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have hinner :
      (((digest.hyperIndex / 2048) / 2048) <<< 128 |||
          (((digest.hyperIndex / 2048) % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h64
  have haddr :
      ((1 : Nat) <<< 224 |||
        ((((digest.hyperIndex / 2048) / 2048) <<< 128) |||
          (((digest.hyperIndex / 2048) % 2048) <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow hLayer hinner
  simpa [C13Concrete.adrsWotsHashBase, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

/-- Layer-1 pre-digest `"wotsAdrs"` is the C13 WOTS hash-base address assembled
from layer one and the layer-1 split parsed hypertree index. -/
theorem c13SecondLayerBeforeDigest_wotsAdrs_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
        "wotsAdrs" =
      C13Concrete.adrsWotsHashBase
        1 ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  exact SegmentLayer3.beforeDigest_wotsAdrs_eq_of_layer_idxTree
    (c13SecondLayerGuardState pkSeed pkRoot message sig)
    1 (digest.hyperIndex / 2048)
    (c13SecondLayerGuardState_layer pkSeed pkRoot message sig)
    (c13SecondLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (by decide : 1 < 2 ^ 32)
    (lt_of_le_of_lt
      (Nat.div_le_self _ _)
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))

/-- Layer-0 pre-digest address scratch cell, once the executable `"wotsAdrs"`
binding has been identified and shown word-normalized. -/
theorem c13FirstLayerBeforeDigest_wotsAdrs_slot
    (pkSeed pkRoot message sig : Bytes) (wotsAdrs : Nat)
    (hWotsAdrs :
      lookupValue
          (SegmentLayer3.beforeDigest
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "wotsAdrs" = wotsAdrs)
    (hNorm : wordNormalize wotsAdrs = wotsAdrs) :
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      wotsAdrs := by
  rw [SegmentLayer3.beforeDigest_memory_0x20_eq_of_wotsAdrs _ wotsAdrs hWotsAdrs]
  exact hNorm

/-- Layer-0 pre-digest address scratch cell contains the C13 WOTS hash-base
address assembled from the parsed hypertree index. -/
theorem c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsHashBase
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  exact c13FirstLayerBeforeDigest_wotsAdrs_slot
    pkSeed pkRoot message sig
    (C13Concrete.adrsWotsHashBase
      0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
    (c13FirstLayerBeforeDigest_wotsAdrs_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13FirstLayer_wotsAdrs_hyperIndex_norm
      pkSeed pkRoot message sigParsed)

/-- Layer-1 pre-digest address scratch cell, once the executable `"wotsAdrs"`
binding has been identified and shown word-normalized. -/
theorem c13SecondLayerBeforeDigest_wotsAdrs_slot
    (pkSeed pkRoot message sig : Bytes) (wotsAdrs : Nat)
    (hWotsAdrs :
      lookupValue
          (SegmentLayer3.beforeDigest
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "wotsAdrs" = wotsAdrs)
    (hNorm : wordNormalize wotsAdrs = wotsAdrs) :
    ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      wotsAdrs := by
  rw [SegmentLayer3.beforeDigest_memory_0x20_eq_of_wotsAdrs _ wotsAdrs hWotsAdrs]
  exact hNorm

/-- Layer-1 pre-digest address scratch cell contains the C13 WOTS hash-base
address assembled from the parsed hypertree index. -/
theorem c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsHashBase
        1 ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  exact c13SecondLayerBeforeDigest_wotsAdrs_slot
    pkSeed pkRoot message sig
    (C13Concrete.adrsWotsHashBase
      1 ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048))
    (c13SecondLayerBeforeDigest_wotsAdrs_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13SecondLayer_wotsAdrs_hyperIndex_norm
      pkSeed pkRoot message sigParsed)

/-- Layer-0 pre-digest current-node scratch cell, once `afterFinalize` has
identified the FORS public-key accumulator word. -/
theorem c13FirstLayerBeforeDigest_currentNode_slot
    (pkSeed pkRoot message sig forsPk : Bytes)
    (hForsPk :
      lookupValue
          (SegmentCompose.afterFinalize
            (mkC13State pkSeed pkRoot message sig)).bindings
          "forsPk" = C13Concrete.wordOfHash16 forsPk) :
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x40).val =
      C13Concrete.wordOfHash16 forsPk := by
  exact SegmentLayer3.beforeDigest_memory_0x40_eq_wordOfHash16
    (c13FirstLayerGuardState pkSeed pkRoot message sig) forsPk
    (by
      rw [c13FirstLayerGuardState_currentNode]
      exact hForsPk)

/-- Layer-0 pre-digest current-node scratch cell contains the parsed C13 FORS
public key word. -/
theorem c13FirstLayerBeforeDigest_currentNode_slot_of_parse_fors
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk) :
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x40).val =
      C13Concrete.wordOfHash16 forsPk := by
  exact c13FirstLayerBeforeDigest_currentNode_slot
    pkSeed pkRoot message sig forsPk
    (c13AfterFinalize_forsPk_of_parse_fors
      pkSeed pkRoot message sig sigParsed forsPk hParse hFors)

/-- A layer-0 current-node step fact identifies the incoming layer-1 executable
`"currentNode"` binding for every C13 reverted-at-layer-1 data package. -/
theorem c13SecondLayerGuardState_currentNode_of_first_step_reverted_layer1
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "currentNode" =
        C13Concrete.wordOfHash16
          (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.layers 0 forsPk)) :
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers,
      lookupValue
          (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
          "currentNode" = C13Concrete.wordOfHash16 d.root0 := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hStep0Eq :
      SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
        0 forsPk = d.root0 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 0 forsPk d.wotsPk0 d.root0 d.lsig0
      d.hLayer0
      (by simpa [pk, digest, SegmentAcceptSpec.c13LayerNextTree,
          SegmentAcceptSpec.c13LayerLeafIdx, SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hGrinding0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hWots0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hXmss0)
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  rw [hStep0Eq] at hCurrent0
  simpa [pk, digest] using hCurrent0

/-- Layer-0 exact post-step `"merkleNode"` value for the C13 reverted-at-layer-1
branch, reduced to the current Merkle-frame obligations: the normalized model
cell is the C13 `xmssClimb` word and the raw cell is already normalized. -/
theorem c13FirstStep_merkleNode_eq_root0_of_reverted_layer1
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers)
    (hModel :
      wordNormalize
          (lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "merkleNode")
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
            11 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hCellNorm :
      wordNormalize
          (lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "merkleNode")
        =
          lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "merkleNode") :
    lookupValue
        (SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "merkleNode" = C13Concrete.wordOfHash16 d.root0 := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  exact
    SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_normalized_xmssClimb_wots_success
      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk d.wotsPk0 d.root0 d.lsig0.wots d.lsig0.authPath
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.xmssRootFromSigC13AtLayer_zero] using d.hXmss0)
      (by simpa [pk, digest] using hModel)
      hCellNorm

/-- Layer-0 exact post-step `"merkleNode"` value for the C13 reverted-at-layer-1
branch, reduced to the single raw Merkle-frame fact.  This is the sharper
version of `c13FirstStep_merkleNode_eq_root0_of_reverted_layer1`: once the
executable Merkle climb is identified with the concrete C13 `xmssClimb` word,
the WOTS-success roundtrip discharges the root conversion directly, with no
separate normalized-cell premises. -/
theorem c13FirstStep_merkleNode_eq_root0_of_reverted_layer1_of_raw_xmssClimb
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers)
    (hRaw :
      lookupValue
          (SegmentLayer3.stepLayer
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
            11 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    lookupValue
        (SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "merkleNode" = C13Concrete.wordOfHash16 d.root0 := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  exact
    SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk d.wotsPk0 d.root0 d.lsig0.wots d.lsig0.authPath
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.xmssRootFromSigC13AtLayer_zero] using d.hXmss0)
      (by simpa [pk, digest] using hRaw)

/-- Layer-1 pre-digest current-node scratch cell, once the incoming executable
`"currentNode"` binding has been identified as a C13 hash word. -/
theorem c13SecondLayerBeforeDigest_currentNode_slot
    (pkSeed pkRoot message sig root0 : Bytes)
    (hCurrent :
      lookupValue
          (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
          "currentNode" = C13Concrete.wordOfHash16 root0) :
    ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x40).val =
      C13Concrete.wordOfHash16 root0 := by
  exact SegmentLayer3.beforeDigest_memory_0x40_eq_wordOfHash16
    (c13SecondLayerGuardState pkSeed pkRoot message sig) root0 hCurrent

/-- Layer-0 pre-digest count scratch cell, once the executable `"count"` binding
has been identified and shown word-normalized. -/
theorem c13FirstLayerBeforeDigest_count_slot
    (pkSeed pkRoot message sig : Bytes) (count : Nat)
    (hCount :
      lookupValue
          (SegmentLayer3.beforeDigest
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "count" = count)
    (hNorm : wordNormalize count = count) :
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x60).val =
      count := by
  rw [SegmentLayer3.beforeDigest_memory_0x60_eq_of_count _ count hCount]
  exact hNorm

/-- Layer-1 pre-digest count scratch cell, once the executable `"count"` binding
has been identified and shown word-normalized. -/
theorem c13SecondLayerBeforeDigest_count_slot
    (pkSeed pkRoot message sig : Bytes) (count : Nat)
    (hCount :
      lookupValue
          (SegmentLayer3.beforeDigest
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "count" = count)
    (hNorm : wordNormalize count = count) :
    ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x60).val =
      count := by
  rw [SegmentLayer3.beforeDigest_memory_0x60_eq_of_count _ count hCount]
  exact hNorm

/-- Layer-0 pre-digest `"count"` is the parsed C13 layer-0 WOTS count. -/
theorem c13FirstLayerBeforeDigest_count_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "count" = lsig.wots.count := by
  have hSigOffRaw :
      lookupValue (c13FirstLayerGuardState pkSeed pkRoot message sig).bindings
          "sigOff" = 1952 := by
    rw [c13FirstLayerGuardState_sigOff]
    exact SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)
  have hRaw :=
    SegmentLayer3.beforeDigest_count_eq_of_sigBase_sigOff_calldata
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      sigDataOffset 1952
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (c13FirstLayerGuardState_sigBase pkSeed pkRoot message sig)
      hSigOffRaw
      (c13FirstLayerGuardState_selector pkSeed pkRoot message sig)
      (c13FirstLayerGuardState_calldata pkSeed pkRoot message sig)
      (by decide : sigDataOffset < 2 ^ 256)
      (by decide : 1952 < 2 ^ 256)
      (by decide : 1952 + 688 < 2 ^ 256)
      (by decide :
        sigDataOffset + (1952 + 688) < 2 ^ 256)
  rw [SphincsMinusVerifiers.SiblingCalldata.shr224_calldata_eq_readBE4
      pkSeed pkRoot message sig (1952 + 688)] at hRaw
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 0 < 2) hLayer0
  rw [hCountSpec]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig (1952 + 688)]
  exact hRaw

/-- Layer-1 pre-digest `"count"` is the parsed C13 layer-1 WOTS count. -/
theorem c13SecondLayerBeforeDigest_count_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig) :
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
        "count" = lsig.wots.count := by
  have hRaw :=
    SegmentLayer3.beforeDigest_count_eq_of_sigBase_sigOff_calldata
      (c13SecondLayerGuardState pkSeed pkRoot message sig)
      sigDataOffset 2820
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (c13SecondLayerGuardState_sigBase pkSeed pkRoot message sig)
      (c13SecondLayerGuardState_sigOff pkSeed pkRoot message sig)
      (c13SecondLayerGuardState_selector pkSeed pkRoot message sig)
      (c13SecondLayerGuardState_calldata pkSeed pkRoot message sig)
      (by decide : sigDataOffset < 2 ^ 256)
      (by decide : 2820 < 2 ^ 256)
      (by decide : 2820 + 688 < 2 ^ 256)
      (by decide :
        sigDataOffset + (2820 + 688) < 2 ^ 256)
  rw [SphincsMinusVerifiers.SiblingCalldata.shr224_calldata_eq_readBE4
      pkSeed pkRoot message sig (2820 + 688)] at hRaw
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 1 < 2) hLayer1
  rw [hCountSpec]
  rw [show 1952 + 868 * 1 + 688 = 2820 + 688 by decide]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig (2820 + 688)]
  exact hRaw

/-- Layer-0 parsed C13 WOTS count is already an EVM word. -/
theorem c13FirstLayer_wotsCount_norm
    (sig : Bytes) (sigParsed : Signature) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    wordNormalize lsig.wots.count = lsig.wots.count := by
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 0 < 2) hLayer0
  rw [hCountSpec]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig (1952 + 688)]
  exact SegmentS2.wordNormalize_of_lt
    (lt_trans
      (SphincsMinusVerifiers.SiblingCalldata.readBE_lt sig (1952 + 688) 4)
      (by decide : 256 ^ 4 < 2 ^ 256))

/-- Layer-1 parsed C13 WOTS count is already an EVM word. -/
theorem c13SecondLayer_wotsCount_norm
    (sig : Bytes) (sigParsed : Signature) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig) :
    wordNormalize lsig.wots.count = lsig.wots.count := by
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 1 < 2) hLayer1
  rw [hCountSpec]
  rw [show 1952 + 868 * 1 + 688 = 3508 by decide]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig 3508]
  exact SegmentS2.wordNormalize_of_lt
    (lt_trans
      (SphincsMinusVerifiers.SiblingCalldata.readBE_lt sig 3508 4)
      (by decide : 256 ^ 4 < 2 ^ 256))

/-- Layer-0 pre-digest count scratch cell contains the parsed C13 layer-0 WOTS
count. -/
theorem c13FirstLayerBeforeDigest_count_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    ((SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x60).val =
      lsig.wots.count := by
  exact c13FirstLayerBeforeDigest_count_slot
    pkSeed pkRoot message sig lsig.wots.count
    (c13FirstLayerBeforeDigest_count_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer0)
    (c13FirstLayer_wotsCount_norm sig sigParsed lsig hParse hLayer0)

/-- Layer-1 pre-digest count scratch cell contains the parsed C13 layer-1 WOTS
count. -/
theorem c13SecondLayerBeforeDigest_count_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig) :
    ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x60).val =
      lsig.wots.count := by
  exact c13SecondLayerBeforeDigest_count_slot
    pkSeed pkRoot message sig lsig.wots.count
    (c13SecondLayerBeforeDigest_count_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer1)
    (c13SecondLayer_wotsCount_norm sig sigParsed lsig hParse hLayer1)

/-- C13 WOTS calldata correspondence.  Under the frozen ABI calldata frame and
pointer/index evaluations, the masked `calldataload` at `wotsPtr + (i << 4)`
evaluates to `wordOfHash16` of the parsed C13 WOTS chain entry for the selected
layer and chain index. -/
theorem c13_wots_calldataload_eq
    (st : RuntimeState)
    (wotsPtrE iE : Compiler.CompilationModel.Expr)
    (pkSeed pkRoot message sig : Bytes)
    (layer k ap hval : Nat)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
            = MkC13State.headWords pkSeed pkRoot message sig.size
                ++ MkC13State.bytesToWords sig)
    (hap : evalExpr [] st wotsPtrE = some ap)
    (hi : evalExpr [] st iE = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256) (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4 =
      MkC13State.sigDataOffset + (1952 + 868 * layer + 16 * k)) :
    evalExpr [] st
        (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
      = some (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (MkC13State.headWords pkSeed pkRoot message sig.size
            ++ MkC13State.bytesToWords sig)
          (MkC13State.sigDataOffset + (1952 + 868 * layer + 16 * k))) := by
  have hoffset := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_siblingOffset
    st wotsPtrE iE ap hval hap hi haplt hhlt hshift hsum
  show (evalExpr [] st (.add wotsPtrE (.shl (.literal 4) iE))).bind
        (fun ro => some (Compiler.Proofs.YulGeneration.calldataloadWord
          st.selector st.world.calldata ro)) = _
  rw [hoffset]
  show some _ = _
  rw [hsel, hcd, hoff]

/-- C13 WOTS calldata correspondence.  Under the frozen ABI calldata frame and
pointer/index evaluations, the masked `calldataload` at `wotsPtr + (i << 4)`
evaluates to `wordOfHash16` of the parsed C13 WOTS chain entry for the selected
layer and chain index. -/
theorem c13_masked_wots_read_eq_wordOfHash16
    (st : RuntimeState)
    (wotsPtrE iE : Compiler.CompilationModel.Expr)
    (pkSeed pkRoot message sig : Bytes)
    (layer k ap hval : Nat)
    (hlayer : layer < 2) (hk : k < 43)
    (lsig : XmssLayerSig)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
            = MkC13State.headWords pkSeed pkRoot message sig.size
                ++ MkC13State.bytesToWords sig)
    (hap : evalExpr [] st wotsPtrE = some ap)
    (hi : evalExpr [] st iE = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256) (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4 =
      MkC13State.sigDataOffset + (1952 + 868 * layer + 16 * k))
    (hauth :
      (lsig.wots.chains[k]?).getD ⟨#[]⟩ =
        C13Concrete.read16 sig (1952 + 868 * layer + 16 * k)) :
    evalExpr [] st
        (.bitAnd (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some (C13Concrete.wordOfHash16
          ((lsig.wots.chains[k]?).getD ⟨#[]⟩)) := by
  have hcdl : evalExpr [] st
      (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
        = some (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (MkC13State.headWords pkSeed pkRoot message sig.size
              ++ MkC13State.bytesToWords sig)
            (MkC13State.sigDataOffset + (1952 + 868 * layer + 16 * k))) :=
    c13_wots_calldataload_eq st wotsPtrE iE pkSeed pkRoot message sig
      layer k ap hval hsel hcd hap hi haplt hhlt hshift hsum hoff
  have hoff4 :
      4 ≤ MkC13State.sigDataOffset + (1952 + 868 * layer + 16 * k) := by
    show 4 ≤ 164 + (1952 + 868 * layer + 16 * k)
    omega
  have hbound :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.calldataloadWord_lt_of_ge4 0
      (MkC13State.headWords pkSeed pkRoot message sig.size
        ++ MkC13State.bytesToWords sig)
      (MkC13State.sigDataOffset + (1952 + 868 * layer + 16 * k)) hoff4
  have hmasked := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedCalldata st
    (.add wotsPtrE (.shl (.literal 4) iE)) _ hcdl hbound
  have hgen := SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
    pkSeed pkRoot message sig (1952 + 868 * layer + 16 * k)
  show evalExpr [] st
      (.bitAnd (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
        (.literal C13Concrete.nMask)) = _
  rw [hmasked, hauth]
  exact congrArg some hgen

/-- Remaining concrete data needed for the C13 `.ok` fold branch at the current
node boundary. -/
def C13FoldOkCurrentNodeWordcmpData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    =
      C13Concrete.wordOfHash16
        (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.layers 0 forsPk) ∧
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState1
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    = C13Concrete.wordOfHash16 specRoot ∧
  decide (C13Concrete.wordOfHash16 specRoot = C13Concrete.wordOfHash16 pkRoot)
    = rootMatchesPk c13 specRoot pkRoot

/-- Successful C13 fold data with the byte-shaped public-key root width exposed
instead of the final word-comparison equation.  The comparison follows from
`pkRoot.size = 16` plus the C13-produced `specRoot` roundtrip. -/
def C13FoldOkCurrentNodePkRootSizeData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    =
      C13Concrete.wordOfHash16
        (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.layers 0 forsPk) ∧
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState1
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    = C13Concrete.wordOfHash16 specRoot ∧
  pkRoot.size = 16

/-- Package the current concrete two-step layer facts into the `.ok` branch data
shape consumed by the C13 byte-refinement reducer. -/
theorem c13FoldOkCurrentNodePkRootSizeData_of_current_node_facts
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
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
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
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
        = C13Concrete.wordOfHash16 specRoot)
    (hPkRootSize : pkRoot.size = 16) :
    C13FoldOkCurrentNodePkRootSizeData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, hPkRootSize⟩

/-- Package the current concrete two-step layer facts into the `.ok` branch data
shape whose final comparison uses the C13 public-key root projection.  The
comparison follows from the C13-produced `specRoot` roundtrip; the four
executable layer facts (two guards, two post-step `"currentNode"` words) are
explicit hypotheses — the spec-side fold data alone cannot discharge them. -/
theorem c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
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
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
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
        = C13Concrete.wordOfHash16 specRoot) :
    C13FoldOkCurrentNodeWordcmpData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  ⟨hGuard0, hCurrent0, hGuard1, hCurrent1,
    SegmentAcceptSpec.wordCmp_of_wordOfHash16_rootMatchesPk_c13 specRoot pkRoot
      (SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold hFors hFold)⟩

theorem c13_wotsDigest_lt
    (seed : C13Concrete.Word) (layer idxTree idxLeaf count node : Nat) :
    C13Concrete.wotsDigest seed layer idxTree idxLeaf count node < 2 ^ 256 := by
  simpa [C13Concrete.wotsDigest, Compiler.Constants.evmModulus] using
    SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
      [seed, C13Concrete.adrsWotsHashBase layer idxTree idxLeaf, node, count]

/-- The final C13 layer tail assigns `"currentNode"` and `"sigOff"` but does not
rebind `"merkleNode"`, so the post-step Merkle cell is exactly the post-climb
cell at `afterMerkle`. -/
theorem c13_stepLayer_merkleNode_eq_afterMerkle_merkleNode
    (ls : RuntimeState) :
    lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode" =
      lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode" := by
  have hTail := SegmentLayer3.finalLayerTail_preserves_merkleNode
    (SegmentLayer3.afterMerkle ls)
  rw [SegmentLayer3.finalLayerTail_continues_from_afterMerkle ls] at hTail
  exact hTail

/-- Exact raw `"merkleNode"` adapter from the Merkle-loop cutpoint to the full
C13 layer step.  The final layer tail does not rebind `"merkleNode"`, so any
exact `afterMerkle` climb equality is already the post-`stepLayer` equality. -/
theorem c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle
    (ls : RuntimeState) (seed treeAdrs mIdx node : Nat) (auth : List Bytes)
    (hAfter :
      lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode" =
        C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth) :
    lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode" =
      C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  rw [c13_stepLayer_merkleNode_eq_afterMerkle_merkleNode]
  exact hAfter

/-- Reverted-at-layer-1 `currentNode` closure from the smaller raw
`afterMerkle` climb equality.  The final layer tail does not rebind
`"merkleNode"`, and `stepLayer_currentNode_eq_merkleNode` identifies the
post-step `"currentNode"` with that Merkle result; the C13 spec-side
WOTS/XMSS success data then converts the raw climb word to `wordOfHash16 root0`.
-/
theorem c13SecondLayerGuardState_currentNode_of_reverted_layer1_afterMerkle_raw_xmssClimb
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (hAfter :
      ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers,
        lookupValue
            (SegmentLayer3.afterMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "merkleNode" =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
            11 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers,
      lookupValue
          (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
          "currentNode" = C13Concrete.wordOfHash16 d.root0 := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hRawStep :
      lookupValue
          (SegmentLayer3.stepLayer
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode" =
        C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          11 0 (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath := by
    exact c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)
      d.lsig0.authPath
      (by simpa [pk, digest] using hAfter d)
  have hMerkleRoot :
      lookupValue
          (SegmentLayer3.stepLayer
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode" = C13Concrete.wordOfHash16 d.root0 := by
    exact c13FirstStep_merkleNode_eq_root0_of_reverted_layer1_of_raw_xmssClimb
      pkSeed pkRoot message sig sigParsed forsPk d
      (by simpa [pk, digest] using hRawStep)
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
  exact hMerkleRoot

/-- Layer-indexed C13 XMSS reconstruction exposes the exact `xmssClimb` word
whose high 16 bytes are returned as the byte root. -/
theorem c13_xmssRootFromSigAtLayer_some_eq_hash16OfWord_xmssClimb
    (pk : PublicKey) (layer treeIdx leafIdx : Nat)
    (wotsPk root : ByteArray) (auth : List ByteArray)
    (hXmss : C13Concrete.xmssRootFromSigC13AtLayer layer c13 pk treeIdx leafIdx
        wotsPk auth = some root) :
    root =
      C13Concrete.hash16OfWord
        (C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pk.pkSeed)
          (C13Concrete.adrsXmssTree layer treeIdx) 11 0 leafIdx
          (C13Concrete.wordOfHash16 wotsPk) auth) := by
  unfold C13Concrete.xmssRootFromSigC13AtLayer at hXmss
  injection hXmss with hEq
  exact hEq.symm

/-- Successful layer-indexed C13 WOTS reconstruction gives a 16-byte starting
XMSS node, so the concrete XMSS climb word roundtrips through
`hash16OfWord`/`wordOfHash16`. -/
theorem c13_xmssClimbAtLayer_roundtrip_of_wots_success
    (pk : PublicKey) (layer treeIdx leafIdx : Nat)
    (node wotsPk : ByteArray) (wots : WotsSig) (auth : List ByteArray)
    (hWots : C13Concrete.wotsPkFromSigC13AtLayer layer c13 pk treeIdx leafIdx
        node wots = some wotsPk) :
    C13Concrete.wordOfHash16
        (C13Concrete.hash16OfWord
          (C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree layer treeIdx) 11 0 leafIdx
            (C13Concrete.wordOfHash16 wotsPk) auth))
      =
        C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pk.pkSeed)
          (C13Concrete.adrsXmssTree layer treeIdx) 11 0 leafIdx
          (C13Concrete.wordOfHash16 wotsPk) auth := by
  refine SegmentAcceptSpec.xmssClimb_roundtrip_of_node_roundtrip
    (C13Concrete.wordOfHash16 pk.pkSeed) (C13Concrete.adrsXmssTree layer treeIdx)
    11 0 leafIdx (C13Concrete.wordOfHash16 wotsPk) auth ?_
  rw [SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_size wotsPk
    (C13Concrete.wotsPkFromSigC13AtLayer_size hWots)]

/-- Exact post-step `"merkleNode"` adapter for a concrete C13 hypertree layer.
Callers provide the raw executable climb word at that layer; WOTS/XMSS success
turns it into the returned byte root's `wordOfHash16`. -/
theorem c13_stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimbAtLayer_wots_success
    (pk : PublicKey) (layer treeIdx leafIdx : Nat)
    (node wotsPk root : ByteArray) (wots : WotsSig) (auth : List ByteArray)
    (ls : RuntimeState)
    (hWots : C13Concrete.wotsPkFromSigC13AtLayer layer c13 pk treeIdx leafIdx
        node wots = some wotsPk)
    (hXmss : C13Concrete.xmssRootFromSigC13AtLayer layer c13 pk treeIdx leafIdx
        wotsPk auth = some root)
    (hModel :
      lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pk.pkSeed)
            (C13Concrete.adrsXmssTree layer treeIdx) 11 0 leafIdx
            (C13Concrete.wordOfHash16 wotsPk) auth) :
    lookupValue (SegmentLayer3.stepLayer ls).bindings "merkleNode"
      = C13Concrete.wordOfHash16 root := by
  have hRoot :=
    c13_xmssRootFromSigAtLayer_some_eq_hash16OfWord_xmssClimb
      pk layer treeIdx leafIdx wotsPk root auth hXmss
  rw [hModel, hRoot]
  exact (c13_xmssClimbAtLayer_roundtrip_of_wots_success
    pk layer treeIdx leafIdx node wotsPk wots auth hWots).symm

/-- Smaller executable facts that imply the four C13 `.ok` branch
guard/current-node facts: each guard is reduced to the post-prefix checksum
cell, and each final `"currentNode"` equality is reduced to the intermediate
post-step `"merkleNode"` cell. -/
def C13FoldOkDigitMerkleData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  lookupValue
      (SegmentLayer3.afterDigit
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "digitSum" = 208 ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "merkleNode"
    =
      C13Concrete.wordOfHash16
        (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.layers 0 forsPk) ∧
  lookupValue
      (SegmentLayer3.afterDigit
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "digitSum" = 208 ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "merkleNode"
    = C13Concrete.wordOfHash16 specRoot

/-- Residual model-side facts for the C13 `.ok` branch after the checksum
guards have been reduced to the parsed successful fold.  The two `"merkleNode"`
facts are the exact XMSS/model correspondence targets; the scratch-cell fact is
the seed-preservation bridge needed to materialize the layer-1 WOTS digest. -/
def C13FoldOkModelMerkleData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  ((SegmentLayer3.stepLayer
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
    ((CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)).world.memory 0x00).val ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "merkleNode"
    =
      C13Concrete.wordOfHash16
        (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.layers 0 forsPk) ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "merkleNode"
    = C13Concrete.wordOfHash16 specRoot

/-- The layer-0 C13 `.ok` branch preserves seed scratch cell `0x00`.  This is
the memory-frame part of `C13FoldOkModelMerkleData`; it follows from the
concrete frozen Merkle site plus the WOTS/copy loop frames. -/
theorem c13FirstLayerStep_preserves_memory_zero_of_parse
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((SegmentLayer3.stepLayer
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
      ((CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig)).world.memory 0x00).val := by
  have hStep :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((SegmentLayer3.afterDigit
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val := by
    exact
      SegmentLayer3MerkleFrame.stepLayer_preserves_memory_zero_of_layerFrozenSite_range
        (c13FirstLayerGuardState pkSeed pkRoot message sig) 0
        pkSeed pkRoot message sig
        SegmentLayer3.wotsOuterForEach_preserves_memory_zero
        SegmentLayer3.copyForEach_preserves_memory_zero
        (by decide : 0 < 2)
        (c13FirstLayerBeforeMerkle_layerFrozenSite
          pkSeed pkRoot message sig sigParsed hParse)
  have hMem :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val := by
    rw [hStep]
    exact SegmentLayer3.afterDigit_preserves_memory_zero
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
  simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using hMem

/-- Raw XMSS/model premises that imply the C13 `.ok` branch
`C13FoldOkModelMerkleData`.  The seed preservation conjunct is proved here from
the concrete layer frame; the two remaining conjuncts are reduced to exact raw
post-step `"merkleNode"` climb facts for layer 0 and layer 1. -/
theorem c13FoldOkModelMerkleData_of_raw_xmssClimb
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hRaw0 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hRaw1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        = C13Concrete.wordOfHash16 specRoot) :
    C13FoldOkModelMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot sigParsed.layers
      (by simpa [pk, digest] using hFold)
  have hStep0Eq :
      SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
        0 forsPk = d.root0 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 0 forsPk d.wotsPk0 d.root0 d.lsig0
      d.hLayer0
      (by simpa [pk, digest, SegmentAcceptSpec.c13LayerNextTree,
          SegmentAcceptSpec.c13LayerLeafIdx, SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hGrinding0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hWots0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hXmss0)
  have hMerkle0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
              0 forsPk) := by
    rw [hStep0Eq]
    exact
      SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
        pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        forsPk d.wotsPk0 d.root0 d.lsig0.wots d.lsig0.authPath
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (by
          simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
            C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)
        (by
          simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
            C13Concrete.xmssRootFromSigC13AtLayer_zero] using d.hXmss0)
        (by simpa [pk, digest] using hRaw0 d)
  have hMerkle1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        = C13Concrete.wordOfHash16 specRoot := hRaw1
  refine ⟨?_, ?_, ?_⟩
  · exact c13FirstLayerStep_preserves_memory_zero_of_parse
      pkSeed pkRoot message sig sigParsed hParse
  · simpa [pk, digest] using hMerkle0
  · exact hMerkle1

/-- Raw XMSS/model premises for both C13 `.ok` layers imply
`C13FoldOkModelMerkleData`.  Compared with
`c13FoldOkModelMerkleData_of_raw_xmssClimb`, the layer-1 post-step root cell is
reduced to the same exact raw climb-word shape as layer 0. -/
theorem c13FoldOkModelMerkleData_of_raw_xmssClimbs
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hRaw0 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hRaw1 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 1
                (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
              11 0
              (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath) :
    C13FoldOkModelMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot sigParsed.layers
      (by simpa [pk, digest] using hFold)
  refine
    c13FoldOkModelMerkleData_of_raw_xmssClimb
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold hRaw0 ?_
  exact
    c13_stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimbAtLayer_wots_success
      pk 1 ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
      d.root0 d.wotsPk1 specRoot d.lsig1.wots d.lsig1.authPath
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13] using d.hWots1)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13] using d.hXmss1)
      (by simpa [pk, digest] using hRaw1 d)

/-- Successful C13 `.ok` fold data discharges the model-side Merkle package
from exact raw climb cells at the `afterMerkle` cutpoint for both executable
layers.  This is the current smallest executable residual before proving the
raw climb relation itself: the final layer tail is already eliminated by
`c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle`. -/
theorem c13FoldOkModelMerkleData_of_afterMerkle_raw_xmssClimbs
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hAfter0 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hAfter1 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 1
                (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
              11 0
              (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath) :
    C13FoldOkModelMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  refine
    c13FoldOkModelMerkleData_of_raw_xmssClimbs
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold ?_ ?_
  · intro d
    exact
      c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath
        (hAfter0 d)
  · intro d
    exact
      c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 1
          (((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath
        (hAfter1 d)

/-- Successful C13 fold data discharges both executable checksum cells in
`C13FoldOkDigitMerkleData`.  The remaining premises are only the model/XMSS
post-step `"merkleNode"` equalities and the first-step seed scratch preservation
needed to build the second layer's pre-digest scratch frame. -/
theorem c13FoldOkDigitMerkleData_of_model_merkle_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (_hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hModel : C13FoldOkModelMerkleData
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot sigParsed.layers
      (by simpa [pk, digest] using hFold)
  rcases hModel with ⟨hStepMem0, hMerkle0, hMerkle1⟩
  have hStep0Eq :
      SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
        0 forsPk = d.root0 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 0 forsPk d.wotsPk0 d.root0 d.lsig0
      d.hLayer0
      (by simpa [pk, digest, SegmentAcceptSpec.c13LayerNextTree,
          SegmentAcceptSpec.c13LayerLeafIdx, SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hGrinding0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hWots0)
      (by simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
          SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
          SegmentAcceptSpec.c13LayerTreeIdx, c13]
        using d.hXmss0)
  have hCurrent0Root :
      lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 d.root0 := by
    have hMerkle0Root :
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "merkleNode" =
          C13Concrete.wordOfHash16 d.root0 := by
      simpa [pk, digest, hStep0Eq]
        using hMerkle0
    unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
    rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
    rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
    simpa [pk, digest] using hMerkle0Root
  have hSeed1 :
      ((SegmentLayer3.beforeDigest
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed :=
    c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig
      (c13FirstStepLayer_seed_slot_of_memory_zero
        pkSeed pkRoot message sig
        (by simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using hStepMem0))
  have hD0 :
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048)
            (digest.hyperIndex % 2048)
            d.lsig0.wots.count
            (C13Concrete.wordOfHash16 forsPk) := by
    exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wordOfHash16 pkSeed) 0
      (digest.hyperIndex / 2048)
      (digest.hyperIndex % 2048)
      d.lsig0.wots.count
      (C13Concrete.wordOfHash16 forsPk)
      (c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig)
      (c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse)
      (c13FirstLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig forsPk
        (c13AfterFinalize_forsPk_of_parse_fors
          pkSeed pkRoot message sig sigParsed forsPk hParse hFors))
      (c13FirstLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig0 hParse d.hLayer0)
  have hD1 :
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            d.lsig1.wots.count
            (C13Concrete.wordOfHash16 d.root0) := by
    exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
      (c13SecondLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wordOfHash16 pkSeed) 1
      ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
      d.lsig1.wots.count
      (C13Concrete.wordOfHash16 d.root0)
      hSeed1
      (c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse)
      (c13SecondLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig d.root0 hCurrent0Root)
      (c13SecondLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig1 hParse d.hLayer1)
  have hDigit0Wots :
      lookupValue
          (SegmentLayer3.afterDigit
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 0
              (digest.hyperIndex / 2048)
              (digest.hyperIndex % 2048)
              d.lsig0.wots.count
              (C13Concrete.wordOfHash16 forsPk)) := by
    exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wotsDigest
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk))
      hD0
      (c13_wotsDigest_lt
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk))
  have hDigit1Wots :
      lookupValue
          (SegmentLayer3.afterDigit
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 1
              ((digest.hyperIndex / 2048) / 2048)
              ((digest.hyperIndex / 2048) % 2048)
              d.lsig1.wots.count
              (C13Concrete.wordOfHash16 d.root0)) := by
    exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
      (c13SecondLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wotsDigest
        (C13Concrete.wordOfHash16 pkSeed) 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count
        (C13Concrete.wordOfHash16 d.root0))
      hD1
      (c13_wotsDigest_lt
        (C13Concrete.wordOfHash16 pkSeed) 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count
        (C13Concrete.wordOfHash16 d.root0))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c13FirstLayerGuardState_eq_c13LayerLoopState0] at hDigit0Wots
    rw [hDigit0Wots]
    exact C13Concrete.wotsDigitSum_eq_of_wotsGrindingFailsC13AtLayer_false
      (layer := 0) (pk := pk)
      (treeIdx := digest.hyperIndex / 2048)
      (leafIdx := digest.hyperIndex % 2048)
      (node := forsPk) (wots := d.lsig0.wots)
      d.hGrinding0
  · exact hMerkle0
  · rw [c13SecondLayerGuardState_eq_c13LayerLoopState1] at hDigit1Wots
    rw [hDigit1Wots]
    exact C13Concrete.wotsDigitSum_eq_of_wotsGrindingFailsC13AtLayer_false
      (layer := 1) (pk := pk)
      (treeIdx := (digest.hyperIndex / 2048) / 2048)
      (leafIdx := (digest.hyperIndex / 2048) % 2048)
      (node := d.root0) (wots := d.lsig1.wots)
      d.hGrinding1
  · exact hMerkle1

/-- The two C13 `.ok` guards and two post-step `"currentNode"` facts follow
from the smaller checksum/`"merkleNode"` facts, with the final comparison still
discharged by the C13-produced `specRoot` roundtrip rather than `pkRoot.size`. -/
theorem c13FoldOkCurrentNodeWordcmpData_of_digit_merkle_facts
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hFacts : C13FoldOkDigitMerkleData
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkCurrentNodeWordcmpData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  rcases hFacts with ⟨hDigit0, hMerkle0, hDigit1, hMerkle1⟩
  -- Use the (now deriving) constructor; supply the four facts via the lightweight
  -- digit+merkle proofs we already have (this path is used when we have the
  -- afterMerkle/raw step witnesses but want to avoid full observed derivation).
  apply
    c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
  · exact
      SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig)) hDigit0
  · rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
    exact hMerkle0
  · exact
      SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig)) hDigit1
  · rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
    exact hMerkle1

/-- Successful C13 `.ok` fold data discharges `C13FoldOkDigitMerkleData` once
the remaining model facts have been reduced to the raw layer-0 XMSS climb cell
and the raw layer-1 post-step root cell. -/
theorem c13FoldOkDigitMerkleData_of_raw_xmssClimb
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hRaw0 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hRaw1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        = C13Concrete.wordOfHash16 specRoot) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkDigitMerkleData_of_model_merkle_data
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
    (c13FoldOkModelMerkleData_of_raw_xmssClimb
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold hRaw0 hRaw1)

/-- Successful C13 `.ok` fold data discharges `C13FoldOkDigitMerkleData` from
raw XMSS/model climb cells for both layers, with no caller premise stating the
layer-1 post-step cell is already `wordOfHash16 specRoot`. -/
theorem c13FoldOkDigitMerkleData_of_raw_xmssClimbs
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hRaw0 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hRaw1 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 1
                (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
              11 0
              (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkDigitMerkleData_of_model_merkle_data
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
    (c13FoldOkModelMerkleData_of_raw_xmssClimbs
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold hRaw0 hRaw1)

/-- Successful C13 `.ok` fold data discharges `C13FoldOkDigitMerkleData` from
exact raw climb cells at the `afterMerkle` cutpoint for both executable layers.
This wires the reduced `afterMerkle` residuals into the checksum/current-node
ok-branch reducer. -/
theorem c13FoldOkDigitMerkleData_of_afterMerkle_raw_xmssClimbs
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hAfter0 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)
    (hAfter1 :
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers specRoot,
        lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode"
          =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 1
                (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
              11 0
              (((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkDigitMerkleData_of_model_merkle_data
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
    (c13FoldOkModelMerkleData_of_afterMerkle_raw_xmssClimbs
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold hAfter0 hAfter1)

/-- Named residual for the successful C13 `.ok` branch after the layer tail has
been eliminated: the only remaining Merkle facts are the exact raw
`afterMerkle` climb cells for the two executable layers.  This packages the
formerly duplicated goals at the smallest current boundary: proving it requires
the raw Merkle climb-state correspondence for each layer, while all checksum,
root-roundtrip, and final-tail plumbing is discharged by the surrounding
bridges. -/
def C13FoldOkAfterMerkleRawXmssClimbData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
      lookupValue
          (SegmentLayer3.afterMerkle
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) ∧
  (∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
      lookupValue
          (SegmentLayer3.afterMerkle
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            11 0 ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath)

/-- Normalized version of the current C13 `.ok` Merkle residual.  This is the
shape produced by the frame-threaded climb theorem (`wordNormalize` of the
`afterMerkle` cell equals the spec `xmssClimb`), plus the exact cell-normalization
facts needed to recover the raw binding equality consumed by the older bridge. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
      wordNormalize
          (lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode")
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) ∧
  wordNormalize
      (lookupValue
        (SegmentLayer3.afterMerkle
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))).bindings
        "merkleNode")
    =
      lookupValue
        (SegmentLayer3.afterMerkle
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))).bindings
        "merkleNode" ∧
  (∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
      wordNormalize
          (lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode")
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            11 0 ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath) ∧
  wordNormalize
      (lookupValue
        (SegmentLayer3.afterMerkle
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig))).bindings
        "merkleNode")
    =
      lookupValue
      (SegmentLayer3.afterMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "merkleNode"

/-- The true model/spec part of
`C13FoldOkAfterMerkleNormalizedXmssClimbData`: for each successful concrete C13
fold witness, the normalized executable `afterMerkle` cell is the corresponding
spec `xmssClimb` word.  This is the part supplied by the frame-threaded climb
theorem (`SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame_c13`) once the
Merkle frame, auth-path calldata range, and initial climb frame are in hand. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbModelData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
      wordNormalize
          (lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode")
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) ∧
  (∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
      wordNormalize
          (lookupValue
            (SegmentLayer3.afterMerkle
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "merkleNode")
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            11 0 ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk1) d.lsig1.authPath)

/-- Generic statement that an `afterMerkle` state's raw `"merkleNode"` binding is
already a normalized EVM word.  This is intentionally independent of C13 fold
data: it is the reusable cell-normalization side condition needed to turn a
normalized model equality into an exact raw binding equality. -/
def AfterMerkleMerkleNodeCellNormalized (ls : RuntimeState) : Prop :=
  wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
    =
      lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"

/-- Cell-normalization residual for the two concrete executable C13 `.ok`
layers.  This is separated from the true XMSS/model equality so future callers
can prove it once from source-semantics facts about the Merkle loop's raw output
cell, rather than duplicating it for every successful fold witness. -/
def C13FoldOkAfterMerkleCellNormalizedData
    (pkSeed pkRoot message sig : Bytes) : Prop :=
  AfterMerkleMerkleNodeCellNormalized
    (CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)) ∧
  AfterMerkleMerkleNodeCellNormalized
    (CurrentNodeFrame.c13LayerLoopState1
      (mkC13State pkSeed pkRoot message sig))

/-- Source-semantics ingredients that prove one `afterMerkle` `"merkleNode"`
cell is already normalized: the normalized model projection and the exact raw
projection expose the same concrete climb word. -/
def AfterMerkleMerkleNodeCellNormalizedSourceData (ls : RuntimeState) : Prop :=
  ∃ (seed treeAdrs mIdx node : Nat) (auth : List Bytes),
    wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth ∧
    lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth

/-- C13 layer-0/layer-1 source-semantics normalization premises. -/
def C13FoldOkAfterMerkleCellNormalizedSourceData
    (pkSeed pkRoot message sig : Bytes) : Prop :=
  AfterMerkleMerkleNodeCellNormalizedSourceData
    (CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)) ∧
  AfterMerkleMerkleNodeCellNormalizedSourceData
    (CurrentNodeFrame.c13LayerLoopState1
      (mkC13State pkSeed pkRoot message sig))

/-- If the raw `afterMerkle` cell is known to be an exact climb word and the
frame-threaded theorem gives the normalized cell as the same climb word, then
that particular raw cell is normalized.  This is a small generic adapter for
source-semantics facts that expose both raw and normalized views of the Merkle
climb. -/
theorem afterMerkle_merkleNode_cell_normalized_of_raw_and_normalized_xmssClimb
    (ls : RuntimeState) (seed treeAdrs mIdx node : Nat) (auth : List Bytes)
    (hModel :
      wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
        = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth)
    (hRaw :
      lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"
        = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth) :
    AfterMerkleMerkleNodeCellNormalized ls := by
  unfold AfterMerkleMerkleNodeCellNormalized
  exact hModel.trans hRaw.symm

/-- Source-semantics model/raw projections discharge the reusable normalized-cell
condition. -/
theorem afterMerkle_merkleNode_cell_normalized_of_source_data
    (ls : RuntimeState)
    (hSource : AfterMerkleMerkleNodeCellNormalizedSourceData ls) :
    AfterMerkleMerkleNodeCellNormalized ls := by
  rcases hSource with ⟨seed, treeAdrs, mIdx, node, auth, hModel, hRaw⟩
  exact afterMerkle_merkleNode_cell_normalized_of_raw_and_normalized_xmssClimb
    ls seed treeAdrs mIdx node auth hModel hRaw

/-- The C13 cell-normalization residual is reduced to the two source-semantics
model/raw projections at the concrete layer states. -/
theorem c13FoldOkAfterMerkleCellNormalizedData_of_source_data
    (pkSeed pkRoot message sig : Bytes)
    (hSource : C13FoldOkAfterMerkleCellNormalizedSourceData
        pkSeed pkRoot message sig) :
    C13FoldOkAfterMerkleCellNormalizedData
      pkSeed pkRoot message sig := by
  rcases hSource with ⟨hSource0, hSource1⟩
  exact ⟨
    afterMerkle_merkleNode_cell_normalized_of_source_data
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig)) hSource0,
    afterMerkle_merkleNode_cell_normalized_of_source_data
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig)) hSource1⟩

/-- The `beforeMerkle` prefix initializes the Merkle climb node from the freshly
computed WOTS public-key word and the later `"mIdx"`/`"merklePtr"` bindings do
not disturb it. -/
theorem beforeMerkle_merkleNode_eq_wotsPk (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeMerkle ls).bindings "merkleNode" =
      lookupValue (SegmentLayer3.beforeMerkle ls).bindings "wotsPk" := by
  unfold SegmentLayer3.beforeMerkle
  rw [show SegmentLayer3.suffixBeforeMerkle =
      SegmentLayer3.suffixBeforeMIdx ++
        [ .letVar "mIdx" (.localVar "idxLeaf")
        , .letVar "merklePtr" (.add
            (.localVar "sigBase") (.localVar "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentLayer3.beforeMIdx_eq ls)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "merkleNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "merkleNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  unfold SegmentLayer3.beforeMIdx SegmentLayer3.suffixBeforeMIdx
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentLayer3.beforeAuthOff_eq ls)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  simp only [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]

/-- The suffix between the executable WOTS public-key binding and the Merkle
cutpoint initializes only auth/tree/Merkle bookkeeping variables, so it leaves
the already-computed `"wotsPk"` binding unchanged. -/
theorem beforeMerkle_wotsPk_eq_beforeAuthOff_wotsPk (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeMerkle ls).bindings "wotsPk" =
      lookupValue (SegmentLayer3.beforeAuthOff ls).bindings "wotsPk" := by
  unfold SegmentLayer3.beforeMerkle
  rw [show SegmentLayer3.suffixBeforeMerkle =
        SegmentLayer3.suffixBeforeAuthOff ++
          SegmentLayer3.suffixBeforeMerkle.drop SegmentLayer3.suffixBeforeAuthOff.length by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentLayer3.beforeAuthOff_eq ls)]
  simp only [SegmentLayer3.suffixBeforeAuthOff, SegmentLayer3.suffixBeforeMerkle,
    List.length_cons, List.length_nil, List.drop]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "treeAdrs" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "wotsPk" _ (by decide)]

/-- Calldata image used by the C13 XMSS auth-path climb at `merklePtr`. -/
def c13XmssAuthCdAt
    (pkSeed pkRoot message sig : Bytes) (merklePtr : Nat) : Nat → Nat :=
  fun j =>
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (SphincsMinusVerifiers.MkC13State.headWords pkSeed pkRoot message sig.size
        ++ SphincsMinusVerifiers.MkC13State.bytesToWords sig)
      (merklePtr + 16 * j)

theorem c13_adrsWotsPk_norm_layer0
    (pkSeed pkRoot message : Bytes) (sigParsed : Signature) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    wordNormalize
        (C13Concrete.adrsWotsPk 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
      =
        C13Concrete.adrsWotsPk 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) := by
  intro pk digest
  have h128 :
      (digest.hyperIndex / 2048) <<< 128 < 2 ^ 256 := by
    have hnext : digest.hyperIndex / 2048 < 2 ^ 11 := by
      simpa using C13Concrete.hMsgC13_hyperIndex_div_2048_lt pk sigParsed.R message
    rw [Nat.shiftLeft_eq]
    calc
      (digest.hyperIndex / 2048) * 2 ^ 128 < 2 ^ 11 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h96 : (1 : Nat) <<< 96 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have h64 :
      (digest.hyperIndex % 2048) <<< 64 < 2 ^ 256 := by
    have hleaf : digest.hyperIndex % 2048 < 2048 :=
      Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      (digest.hyperIndex % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have h0 : (0 : Nat) <<< 224 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have hinner :
      (((digest.hyperIndex / 2048) <<< 128 ||| ((1 : Nat) <<< 96)) |||
          ((digest.hyperIndex % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow h128 h96) h64
  have haddr :
      ((0 : Nat) <<< 224 |||
        (((digest.hyperIndex / 2048) <<< 128 ||| ((1 : Nat) <<< 96)) |||
          ((digest.hyperIndex % 2048) <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h0 hinner
  simpa [C13Concrete.adrsWotsPk, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

theorem c13_adrsWotsPk_norm_layer1
    (pkSeed pkRoot message : Bytes) (sigParsed : Signature) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    wordNormalize
        (C13Concrete.adrsWotsPk 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048))
      =
        C13Concrete.adrsWotsPk 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  have h128 :
      (((digest.hyperIndex / 2048) / 2048) <<< 128) < 2 ^ 256 := by
    have hnext : (digest.hyperIndex / 2048) / 2048 < 2 ^ 22 :=
      lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
    rw [Nat.shiftLeft_eq]
    calc
      ((digest.hyperIndex / 2048) / 2048) * 2 ^ 128 < 2 ^ 22 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h96 : (1 : Nat) <<< 96 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have h64 :
      (((digest.hyperIndex / 2048) % 2048) <<< 64) < 2 ^ 256 := by
    have hleaf : (digest.hyperIndex / 2048) % 2048 < 2048 :=
      Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      ((digest.hyperIndex / 2048) % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have hLayer : (1 : Nat) <<< 224 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have hinner :
      ((((digest.hyperIndex / 2048) / 2048) <<< 128 ||| ((1 : Nat) <<< 96)) |||
          (((digest.hyperIndex / 2048) % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow h128 h96) h64
  have haddr :
      ((1 : Nat) <<< 224 |||
        ((((digest.hyperIndex / 2048) / 2048) <<< 128 ||| ((1 : Nat) <<< 96)) |||
          (((digest.hyperIndex / 2048) % 2048) <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow hLayer hinner
  simpa [C13Concrete.adrsWotsPk, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

/-- The per-step frame-advance fact needed by the frame-threaded C13 XMSS climb. -/
def C13AfterMerkleXmssFrameStepPremiseAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
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
        seed treeAdrs auth idx a)

/-- The initial `beforeMerkle` frame fact for one C13 XMSS climb. -/
def C13AfterMerkleXmssInitialFramePremiseAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (ls : RuntimeState) (mIdx node : Nat) : Prop :=
  SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
    "merkleNode" "mIdx" "treeAdrs" "merklePtr"
    pkSeed pkRoot message sig seed treeAdrs merklePtr
    { SegmentLayer3.beforeMerkle ls with
      bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
        (wordNormalize 0) }
    (mIdx, node)

/-- The remaining frame facts needed to instantiate the named frame-threaded
`afterMerkle` theorem for one concrete C13 XMSS climb.  The parsed auth-path
calldata range is supplied separately by `xmss_climb_data_range`; this package is
therefore exactly the per-step frame advance and the initial frame at `h = 0`. -/
def C13AfterMerkleXmssFramePremisesAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat) : Prop :=
  C13AfterMerkleXmssFrameStepPremiseAt
    pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt ∧
  C13AfterMerkleXmssInitialFramePremiseAt
    pkSeed pkRoot message sig seed treeAdrs merklePtr ls mIdx node

/-- The raw per-step advance fact needed by the exact-cell C13 XMSS climb. -/
def C13AfterMerkleXmssRawStepPremiseAt
    (seed treeAdrs : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx" s a →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx"
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        seed treeAdrs auth idx a)

/-- The initial raw `beforeMerkle` relation for one C13 XMSS climb. -/
def C13AfterMerkleXmssInitialRawPremiseAt
    (ls : RuntimeState) (mIdx node : Nat) : Prop :=
  SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
    "merkleNode" "mIdx"
    { SegmentLayer3.beforeMerkle ls with
      bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
        (wordNormalize 0) }
    (mIdx, node)

/-- Raw-relation analogue of `C13AfterMerkleXmssFramePremisesAt`.  This is the
smallest exact-cell premise needed for one C13 XMSS climb: a raw per-step
advance for `stepMerkle` plus the initial raw relation at `beforeMerkle` with
`"h" = 0`. -/
def C13AfterMerkleXmssRawPremisesAt
    (seed treeAdrs : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat) : Prop :=
  C13AfterMerkleXmssRawStepPremiseAt seed treeAdrs auth cdAt ∧
  C13AfterMerkleXmssInitialRawPremiseAt ls mIdx node

/-- One-layer normalized `afterMerkle` projection from the named frame premises. -/
theorem c13AfterMerkleNormalizedXmssClimb_of_frame_premises_at
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hData :
      ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hFrame : C13AfterMerkleXmssFramePremisesAt
        pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt ls mIdx node) :
    wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  rcases hFrame with ⟨hstep, hR⟩
  exact
    SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame_c13
      pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt ls mIdx node
      hstep hData hR

/-- One-layer exact raw `afterMerkle` projection from the named raw premises. -/
theorem c13AfterMerkleRawXmssClimb_of_raw_premises_at
    (seed treeAdrs : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hData :
      ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hRaw : C13AfterMerkleXmssRawPremisesAt
        seed treeAdrs auth cdAt ls mIdx node) :
    lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  rcases hRaw with ⟨hstep, hR⟩
  exact
    SegmentAcceptSpec.afterMerkle_model_node_raw_c13
      seed treeAdrs auth cdAt ls mIdx node hstep hData hR

/-- One-layer source-semantics normalization package from matching normalized
and raw Merkle-climb projections to the same concrete `xmssClimb` word. -/
theorem c13AfterMerkleCellNormalizedSourceData_of_frame_and_raw_premises_at
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (ls : RuntimeState) (mIdx node : Nat)
    (hData :
      ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt i)
    (hFrame : C13AfterMerkleXmssFramePremisesAt
        pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt ls mIdx node)
    (hRaw : C13AfterMerkleXmssRawPremisesAt
        seed treeAdrs auth cdAt ls mIdx node) :
    AfterMerkleMerkleNodeCellNormalizedSourceData ls := by
  refine ⟨seed, treeAdrs, mIdx, node, auth, ?_, ?_⟩
  · exact c13AfterMerkleNormalizedXmssClimb_of_frame_premises_at
      pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt ls mIdx node
      hData hFrame
  · exact c13AfterMerkleRawXmssClimb_of_raw_premises_at
      seed treeAdrs auth cdAt ls mIdx node hData hRaw

/-- Layer-0 frame residual for one successful C13 `.ok` fold witness. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFramePremisesAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692)))
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)

/-- Layer-1 frame residual for one successful C13 `.ok` fold witness. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFramePremisesAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692)))
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk1)

/-- Layer-0 raw-relation residual for one successful C13 `.ok` fold witness. -/
def C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssRawPremisesAt
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692)))
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)

/-- Layer-1 raw-relation residual for one successful C13 `.ok` fold witness. -/
def C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssRawPremisesAt
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692)))
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk1)

/-- Layer-0 normalized step residual: one `stepMerkle` frame advance for the
C13 `.ok` XMSS climb. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFrameStepPremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692)))

/-- Layer-0 normalized initial residual: the exact `beforeMerkle` frame at
`"h" = 0`. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssInitialFramePremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)

/-- Layer-1 normalized step residual: one `stepMerkle` frame advance for the
C13 `.ok` XMSS climb. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFrameStepPremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692)))

/-- Layer-1 normalized initial residual: the exact `beforeMerkle` frame at
`"h" = 0`. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssInitialFramePremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk1)

/-- Layer-0 raw step residual: one exact-cell `stepMerkle` advance. -/
def C13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssRawStepPremiseAt
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692)))

/-- Layer-0 raw initial residual: the exact `beforeMerkle` raw relation at
`"h" = 0`. -/
def C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssInitialRawPremiseAt
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)

/-- Layer-1 raw step residual: one exact-cell `stepMerkle` advance. -/
def C13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssRawStepPremiseAt
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692)))

/-- Layer-1 raw initial residual: the exact `beforeMerkle` raw relation at
`"h" = 0`. -/
def C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssInitialRawPremiseAt
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk1)

/-- Smallest exact-node prerequisite for the layer-0 raw initial Merkle climb:
the executable WOTS public-key word already equals the spec WOTS public key for
each successful `.ok` fold witness.  The structural `beforeMerkle` node binding,
the low-11-bit `"mIdx"` initialization, and word normalization are proved
separately. -/
def C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    lookupValue
        (SegmentLayer3.beforeMerkle
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk" =
      C13Concrete.wordOfHash16 d.wotsPk0

/-- Layer-1 analogue of
`C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0`. -/
def C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    lookupValue
        (SegmentLayer3.beforeMerkle
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk" =
      C13Concrete.wordOfHash16 d.wotsPk1

/-- Smaller layer-0 WOTS-start executable fact at the point immediately after
the WOTS public-key word is bound, before the auth/tree/Merkle initialization
suffix. -/
def C13FoldOkBeforeAuthOffWotsPkDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk" =
      C13Concrete.wordOfHash16 d.wotsPk0

/-- Smaller layer-1 analogue of `C13FoldOkBeforeAuthOffWotsPkDataLayer0`. -/
def C13FoldOkBeforeAuthOffWotsPkDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk" =
      C13Concrete.wordOfHash16 d.wotsPk1

/-- Layer-0 executable WOTS-start word before the auth-offset suffix, stated in
the spec kernel's raw `wotsPkWord` form.  This is the remaining executable
keccak/memory image behind `C13FoldOkBeforeAuthOffWotsPkDataLayer0`. -/
def C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk" =
      C13Concrete.wotsPkWord
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots

/-- Layer-1 analogue of `C13FoldOkBeforeAuthOffWotsPkWordDataLayer0`. -/
def C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk" =
      C13Concrete.wotsPkWord
        (C13Concrete.wordOfHash16 pkSeed) 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
        (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots

/-- Reverted-layer analogue of the layer-0 WOTS-start executable fact at the
`beforeAuthOff` cutpoint, stated in the raw `wotsPkWord` form.  This deliberately
does not mention an `.ok` fold witness or final root. -/
def C13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "wotsPk" =
      C13Concrete.wotsPkWord
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots

/-! ### Reverted layer-0 prebind-Keccak residual -/

/-- Reverted layer-0 value-only final-WOTS-PK masked-Keccak equation at the
`beforeWotsPk` cutpoint. -/
def C13FoldRevertedBeforeAuthOffWotsPkPrebindKeccakDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
    evalExpr []
        (SegmentLayer3.beforeWotsPk
          (c13FirstLayerGuardState pkSeed pkRoot message sig))
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)

/-- Reverted layer-0 concrete final-WOTS-PK Keccak preimage cells at the
`beforeWotsPk` cutpoint. -/
def C13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
    let st :=
      SegmentLayer3.beforeWotsPk
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
    (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) ∧
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- Strictly smaller reverted layer-0 `beforeWotsPk` residual after the seed
cell is discharged by the verified memory-zero frame. -/
def C13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
    let st :=
      SegmentLayer3.beforeWotsPk
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) ∧
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- Exact residual for only the reverted layer-0 WOTS-PK address cell at the
`beforeWotsPk` cutpoint. -/
def C13FoldRevertedBeforeAuthOffWotsPkAddressCellDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ _d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
    let st :=
      SegmentLayer3.beforeWotsPk
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)

/-- Exact residual for only the reverted layer-0 copied chain-end cells at the
`beforeWotsPk` cutpoint. -/
def C13FoldRevertedBeforeAuthOffWotsPkChainCellsDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
    let st :=
      SegmentLayer3.beforeWotsPk
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- The split address-cell and chain-cell residuals recombine into the previous
address/chain residual. -/
theorem c13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0_of_split
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hAddr : C13FoldRevertedBeforeAuthOffWotsPkAddressCellDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk)
    (hChain : C13FoldRevertedBeforeAuthOffWotsPkChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk := by
  intro d
  exact ⟨hAddr d, hChain d⟩

/-- The historical `SegmentLayer3.suffixBeforeWotsPk` and the lightweight
`SegmentLayer3AddressCells.suffixBeforeWotsPkFrom` are the *same* statement
list (the bodies are textual mirrors). -/
theorem c13_suffixBeforeWotsPk_eq :
    SegmentLayer3.suffixBeforeWotsPk
      = SegmentLayer3AddressCells.suffixBeforeWotsPkFrom := rfl

/-- The historical `beforeWotsPk` cutpoint IS the lightweight `beforeWotsPkFrom`
cutpoint: both run the same suffix from `afterDigit ls`. -/
theorem c13_beforeWotsPk_eq_beforeWotsPkFrom (ls : RuntimeState) :
    SegmentLayer3.beforeWotsPk ls
      = SegmentLayer3AddressCells.beforeWotsPkFrom (SegmentLayer3.afterDigit ls) := by
  have h1 := SegmentLayer3.beforeWotsPk_eq ls
  rw [c13_suffixBeforeWotsPk_eq] at h1
  have h2 := SegmentLayer3AddressCells.beforeWotsPkFrom_eq (SegmentLayer3.afterDigit ls)
  rw [h1] at h2
  injection h2

/-- C13 exact seed-cell bridge from the historical `SegmentLayer3.beforeWotsPk`
cutpoint to the lightweight post-digit prefix cutpoint.  This is intentionally a
single-cell bridge, not a whole-state equality.

Now discharged: `SegmentLayer3.beforeWotsPk` is *equal* to the lightweight
`beforeWotsPkFrom (afterDigit ls)` cutpoint (`c13_beforeWotsPk_eq_beforeWotsPkFrom`
below — the two suffix statement lists are syntactically the same), so the
single-cell framing is a rewrite. -/
theorem c13_beforeWotsPk_memory_zero_eq_lightweight
    (ls : RuntimeState) :
    ((SegmentLayer3.beforeWotsPk ls).world.memory 0x00).val =
      ((SegmentLayer3AddressCells.beforeWotsPkFrom
        (SegmentLayer3.afterDigit ls)).world.memory 0x00).val := by
  rw [c13_beforeWotsPk_eq_beforeWotsPkFrom]

/-- The reverted layer-0 `beforeWotsPk` seed cell follows from the verified
WOTS/copy memory-zero frames and the first-layer guarded-state seed slot. -/
theorem c13FoldRevertedBeforeAuthOffWotsPk_seed_cell
    (pkSeed pkRoot message sig : Bytes) :
    ((SegmentLayer3.beforeWotsPk
      (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed := by
  rw [c13_beforeWotsPk_memory_zero_eq_lightweight]
  rw [SegmentLayer3AddressCells.beforeWotsPkFrom_preserves_memory_zero]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig

/-- Reverted layer-0 `beforeWotsPk` preimage cells reduced to the already
separate seed cell plus the address cell and copied chain-end cells. -/
theorem c13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0_of_seed_address_chain_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hSeed :
      ((SegmentLayer3.beforeWotsPk
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          C13Concrete.wordOfHash16 pkSeed)
    (hRest : C13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk := by
  intro d
  rcases hRest d with ⟨hAddr, hChains⟩
  exact ⟨hSeed, hAddr, hChains⟩

/-- Reverted layer-0 final WOTS-PK masked-Keccak equation discharged from the
concrete `beforeWotsPk` preimage cells. -/
theorem c13FoldRevertedBeforeAuthOffWotsPkPrebindKeccakDataLayer0_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hCells : C13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeAuthOffWotsPkPrebindKeccakDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk := by
  intro d
  rcases hCells d with ⟨hm0, hm1, hmC⟩
  exact InitialNodeKeccak.wots_pk_node_eq_spec
    (SegmentLayer3.beforeWotsPk
      (c13FirstLayerGuardState pkSeed pkRoot message sig))
    (C13Concrete.wordOfHash16 pkSeed) 0
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
    (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots hm0 hm1 hmC

/-- Reverted layer-0 raw WOTS-PK word obligation reduced to the smaller
`beforeWotsPk` masked-Keccak value equation. -/
theorem c13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0_of_prebind_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hPrebind : C13FoldRevertedBeforeAuthOffWotsPkPrebindKeccakDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk := by
  intro d
  rw [SegmentLayer3.beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak]
  change (evalExpr []
        (SegmentLayer3.beforeWotsPk
          (c13FirstLayerGuardState pkSeed pkRoot message sig))
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))).getD 0 = _
  rw [hPrebind d]
  rfl

/-- Reverted layer-0 raw WOTS-PK word residual discharged directly from the
concrete `beforeWotsPk` preimage cells. -/
theorem c13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hCells : C13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk :=
  c13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0_of_prebind_keccak
    pkSeed pkRoot message sig sigParsed forsPk
    (c13FoldRevertedBeforeAuthOffWotsPkPrebindKeccakDataLayer0_of_preimage_cells
      pkSeed pkRoot message sig sigParsed forsPk hCells)

/-- Layer-0 final-keccak cutpoint behind
`C13FoldOkBeforeAuthOffWotsPkWordDataLayer0`.  This separates the executable
`"wotsPk"` binding from the evaluation of the final 45-word masked Keccak. -/
def C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeAuthOff
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
    lookupValue st.bindings "wotsPk" =
        (evalExpr [] st
          (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
            (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))).getD 0 ∧
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)

/-- Layer-1 analogue of
`C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0`. -/
def C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeAuthOff
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
    lookupValue st.bindings "wotsPk" =
        (evalExpr [] st
          (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
            (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))).getD 0 ∧
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)

/-! ### Layer-0 prebind-Keccak residual (smaller boundary)

`C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0` bundles two obligations: a
binding equation `lookup "wotsPk" = (evalExpr <expr>).getD 0` and a value
equation for the final masked Keccak.  The binding equation is unconditionally
discharged by the source-semantics infrastructure
(`SegmentLayer3.beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak`), so the
strictly smaller residual is the value-only Keccak equation, taken at the
finer `beforeWotsPk` cutpoint (i.e. immediately after the copy-loop and before
the final `.letVar "wotsPk"`).

This shape packages the C13 `beforeWotsPk` boundary used by the WOTS-PK bridge. -/
def C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    evalExpr []
        (SegmentLayer3.beforeWotsPk
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig)))
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)

/-- Layer-0 concrete final-WOTS-PK Keccak preimage cells at the `beforeWotsPk`
cutpoint.  This is the memory-shaped residual consumed by
`SegmentLayer3.beforeWotsPk_keccak_eq_wotsPkWord_of_cells`: seed at `0x00`,
WOTS-PK address at `0x20`, and 43 copied WOTS chain-end words starting at
`0x40`. -/
def C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
    (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) ∧
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- Layer-0 concrete WOTS-PK address and chain-end cells at the `beforeWotsPk`
cutpoint.  The seed cell is discharged separately by the memory-zero frame. -/
def C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) ∧
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- Layer-0 WOTS-PK address cell at the `beforeWotsPk` cutpoint. -/
def C13FoldOkBeforeAuthOffWotsPkAddressCellDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ _d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)

/-- Layer-0 copied WOTS chain-end cells at the `beforeWotsPk` cutpoint. -/
def C13FoldOkBeforeAuthOffWotsPkChainCellsDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- The layer-0 address-cell and chain-cell obligations recombine into the
address/chain package. -/
theorem c13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer0_of_split
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hAddr : C13FoldOkBeforeAuthOffWotsPkAddressCellDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hChain : C13FoldOkBeforeAuthOffWotsPkChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hAddr d, hChain d⟩

/-- Layer-0 `beforeWotsPk` seed cell follows from the verified memory-zero
frame. -/
theorem c13FoldOkBeforeAuthOffWotsPk_seed_cell_layer0
    (pkSeed pkRoot message sig : Bytes) :
    ((SegmentLayer3.beforeWotsPk
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed := by
  rw [← c13FirstLayerGuardState_eq_c13LayerLoopState0 pkSeed pkRoot message sig]
  rw [c13_beforeWotsPk_memory_zero_eq_lightweight]
  rw [SegmentLayer3AddressCells.beforeWotsPkFrom_preserves_memory_zero]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig

/-- Layer-0 preimage cells are reduced to the proved seed cell and the remaining
address/chain cells. -/
theorem c13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0_of_address_chain_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rcases hCells d with ⟨hAddr, hChains⟩
  exact ⟨c13FoldOkBeforeAuthOffWotsPk_seed_cell_layer0
    pkSeed pkRoot message sig, hAddr, hChains⟩

/-- Layer-0 final WOTS-PK masked-Keccak residual discharged from the concrete
`beforeWotsPk` preimage-cell facts. -/
theorem c13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer0_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rcases hCells d with ⟨hm0, hm1, hmC⟩
  exact InitialNodeKeccak.wots_pk_node_eq_spec
    (SegmentLayer3.beforeWotsPk
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig)))
    (C13Concrete.wordOfHash16 pkSeed) 0
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
    (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots hm0 hm1 hmC

/-- Layer-0 raw WOTS-PK word obligation reduced to the strictly smaller
`beforeWotsPk` masked-Keccak value equation.  The previously paired binding
equation conjunct of `C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0` is
discharged unconditionally via
`SegmentLayer3.beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak`. -/
theorem c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_prebind_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hPrebind : C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rw [SegmentLayer3.beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak]
  change (evalExpr []
        (SegmentLayer3.beforeWotsPk
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig)))
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))).getD 0 = _
  rw [hPrebind d]
  rfl

/-! ### Layer-1 prebind-Keccak residual (smaller boundary)

Layer-1 analogue of `C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer0`.
The binding-equation conjunct of `C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1`
is discharged unconditionally via the same source-semantics infrastructure
(`SegmentLayer3.beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak` applied at
`CurrentNodeFrame.c13LayerLoopState1`); the strictly smaller residual is the
value-only Keccak equation at the layer-1 `beforeWotsPk` cutpoint with the
layer-1 WOTS preimage (start node `d.root0` and layer-1 `(treeIdx, leafIdx)`
splits of the hypertree index). -/
def C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    evalExpr []
        (SegmentLayer3.beforeWotsPk
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig)))
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)

/-- Layer-1 concrete final-WOTS-PK Keccak preimage cells at the `beforeWotsPk`
cutpoint.  Layer-1 uses the threaded layer-0 root as the WOTS start node and the
layer-1 split of the hypertree index. -/
def C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
    (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048) ∧
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- Layer-1 concrete WOTS-PK address and chain-end cells at the `beforeWotsPk`
cutpoint.  The seed cell is discharged separately by the parsed first-step
memory-zero frame. -/
def C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048) ∧
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- Layer-1 WOTS-PK address cell at the `beforeWotsPk` cutpoint. -/
def C13FoldOkBeforeAuthOffWotsPkAddressCellDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ _d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
    (st.world.memory 0x20).val =
      C13Concrete.adrsWotsPk 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)

/-- Layer-1 copied WOTS chain-end cells at the `beforeWotsPk` cutpoint. -/
def C13FoldOkBeforeAuthOffWotsPkChainCellsDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
    ∀ j, (h : j < 43) →
      (st.world.memory (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)

/-- The layer-1 address-cell and chain-cell obligations recombine into the
address/chain package. -/
theorem c13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer1_of_split
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hAddr : C13FoldOkBeforeAuthOffWotsPkAddressCellDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hChain : C13FoldOkBeforeAuthOffWotsPkChainCellsDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hAddr d, hChain d⟩

/-- Layer-1 `beforeWotsPk` seed cell follows from the layer-0 step memory frame
and the layer-1 guarded-state construction. -/
theorem c13FoldOkBeforeAuthOffWotsPk_seed_cell_layer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((SegmentLayer3.beforeWotsPk
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed := by
  rw [← c13SecondLayerGuardState_eq_c13LayerLoopState1 pkSeed pkRoot message sig]
  rw [c13_beforeWotsPk_memory_zero_eq_lightweight]
  rw [SegmentLayer3AddressCells.beforeWotsPkFrom_preserves_memory_zero]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  unfold c13SecondLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  exact c13FirstStepLayer_seed_slot_of_memory_zero pkSeed pkRoot message sig
    (c13FirstStepLayer_memory_zero_eq_of_parse pkSeed pkRoot message sig sigParsed hParse)

/-- Layer-1 preimage cells are reduced to the proved seed cell and the remaining
address/chain cells. -/
theorem c13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1_of_address_chain_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hCells : C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rcases hCells d with ⟨hAddr, hChains⟩
  exact ⟨c13FoldOkBeforeAuthOffWotsPk_seed_cell_layer1
    pkSeed pkRoot message sig sigParsed hParse, hAddr, hChains⟩

/-- Layer-1 final WOTS-PK masked-Keccak residual discharged from the concrete
`beforeWotsPk` preimage-cell facts. -/
theorem c13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer1_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rcases hCells d with ⟨hm0, hm1, hmC⟩
  exact InitialNodeKeccak.wots_pk_node_eq_spec
    (SegmentLayer3.beforeWotsPk
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig)))
    (C13Concrete.wordOfHash16 pkSeed) 1
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
    (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots hm0 hm1 hmC

/-- Layer-1 raw WOTS-PK word obligation reduced to the strictly smaller
`beforeWotsPk` masked-Keccak value equation.  Layer-1 analogue of
`c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_prebind_keccak`. -/
theorem c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_prebind_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hPrebind : C13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rw [SegmentLayer3.beforeAuthOff_lookup_wotsPk_eq_beforeWotsPk_keccak]
  change (evalExpr []
        (SegmentLayer3.beforeWotsPk
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig)))
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))).getD 0 = _
  rw [hPrebind d]
  rfl

/-- Layer-0 raw WOTS-PK word residual discharged directly from the concrete
`beforeWotsPk` preimage cells. -/
theorem c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_prebind_keccak
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer0_of_preimage_cells
      pkSeed pkRoot message sig sigParsed forsPk specRoot hCells)

/-- Layer-1 raw WOTS-PK word residual discharged directly from the concrete
`beforeWotsPk` preimage cells. -/
theorem c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_prebind_keccak
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkPrebindKeccakDataLayer1_of_preimage_cells
      pkSeed pkRoot message sig sigParsed forsPk specRoot hCells)

/-- Layer-0 final-keccak residual after the executable `"wotsPk"` binding has
been discharged from `suffixBeforeAuthOff`; only the concrete masked Keccak
value remains. -/
def C13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeAuthOff
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)

/-- Layer-1 analogue of
`C13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer0`. -/
def C13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    let st :=
      SegmentLayer3.beforeAuthOff
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5A0))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      =
        some (C13Concrete.wotsPkWord
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)

/-- Layer-0 value-only final-keccak residual projected out of the existing
full final-keccak cutpoint. -/
theorem c13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer0_of_final_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFinal : C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact (hFinal d).2

/-- Layer-1 value-only final-keccak residual projected out of the existing
full final-keccak cutpoint. -/
theorem c13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer1_of_final_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFinal : C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkFinalKeccakEvalDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact (hFinal d).2

/-- Layer-0 raw WOTS word residual reduced to the final masked-Keccak cutpoint. -/
theorem c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_final_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFinal : C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rcases hFinal d with ⟨hBind, hEval⟩
  rw [hBind, hEval]
  rfl

/-- Layer-1 raw WOTS word residual reduced to the final masked-Keccak cutpoint. -/
theorem c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_final_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFinal : C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rcases hFinal d with ⟨hBind, hEval⟩
  rw [hBind, hEval]
  rfl

/-- A successful C13 WOTS reconstruction identifies the raw `wotsPkWord` with
the returned byte key's `wordOfHash16`. -/
theorem c13_wotsPkWord_eq_wordOfHash16_of_wots_success
    (pk : PublicKey) (layer treeIdx leafIdx : Nat)
    (node wotsPk : Bytes) (wots : WotsSig)
    (hWots : C13Concrete.wotsPkFromSigC13AtLayer layer c13 pk
        treeIdx leafIdx node wots = some wotsPk) :
    C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pk.pkSeed)
        layer treeIdx leafIdx (C13Concrete.wordOfHash16 node) wots =
      C13Concrete.wordOfHash16 wotsPk := by
  have hRet :
      C13Concrete.hash16OfWord
          (C13Concrete.wotsPkWord (C13Concrete.wordOfHash16 pk.pkSeed)
            layer treeIdx leafIdx (C13Concrete.wordOfHash16 node) wots) =
        wotsPk := by
    simpa [C13Concrete.wotsPkFromSigC13AtLayer] using Option.some.inj hWots
  rw [← hRet]
  unfold C13Concrete.wotsPkWord
  exact (SegmentAcceptSpec.wordOfHash16_hash16OfWord_maskN_of_lt
    (C13Concrete.keccakWords
      (C13Concrete.wordOfHash16 pk.pkSeed ::
        C13Concrete.adrsWotsPk layer treeIdx leafIdx ::
        (List.range 43).map (fun i =>
          let d :=
            C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pk.pkSeed)
              layer treeIdx leafIdx wots.count (C13Concrete.wordOfHash16 node)
          let wotsAdrs := C13Concrete.adrsWotsHashBase layer treeIdx leafIdx
          let digit := (d >>> (3 * i)) % 8
          let steps := 7 - digit
          let val := C13Concrete.wordOfHash16 ((wots.chains[i]?).getD ⟨#[]⟩)
          let chainBase := wotsAdrs ||| (i <<< 32)
          C13Concrete.chainHash (C13Concrete.wordOfHash16 pk.pkSeed)
            chainBase digit steps 0 val)))
    (by
      simpa [Compiler.Constants.evmModulus] using
        SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
          (C13Concrete.wordOfHash16 pk.pkSeed ::
            C13Concrete.adrsWotsPk layer treeIdx leafIdx ::
            (List.range 43).map (fun i =>
              let d :=
                C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pk.pkSeed)
                  layer treeIdx leafIdx wots.count (C13Concrete.wordOfHash16 node)
              let wotsAdrs := C13Concrete.adrsWotsHashBase layer treeIdx leafIdx
              let digit := (d >>> (3 * i)) % 8
              let steps := 7 - digit
              let val := C13Concrete.wordOfHash16 ((wots.chains[i]?).getD ⟨#[]⟩)
              let chainBase := wotsAdrs ||| (i <<< 32)
              C13Concrete.chainHash (C13Concrete.wordOfHash16 pk.pkSeed)
                chainBase digit steps 0 val)))).symm

/-- Reverted-layer before-auth WOTS-PK fact from the raw executable
`wotsPkWord` binding.  The concrete reverted witness supplies only the
byte/word conversion via `d.hWots0`; the executable binding equation stays as
the remaining cutpoint premise. -/
theorem c13_reverted_beforeAuthOff_wotsPk0_of_wotsPkWord
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hWotsPkWord : C13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.beforeAuthOff
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "wotsPk" = C13Concrete.wordOfHash16 d.wotsPk0 := by
  intro pk digest d
  calc
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "wotsPk"
        = C13Concrete.wotsPkWord
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots := by
              simpa [pk, digest] using hWotsPkWord d
    _ = C13Concrete.wordOfHash16 d.wotsPk0 := by
      exact c13_wotsPkWord_eq_wordOfHash16_of_wots_success
        pk 0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        forsPk d.wotsPk0 d.lsig0.wots
        (by
          simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
            SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
            SegmentAcceptSpec.c13LayerTreeIdx, c13,
            C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)

/-- Layer-0 WOTS before-auth residual reduced to the raw executable
`wotsPkWord` binding.  The C13 success witness supplies only the byte/word
conversion from `wotsPkWord` to `wordOfHash16 d.wotsPk0`. -/
theorem c13FoldOkBeforeAuthOffWotsPkDataLayer0_of_wotsPkWord
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWotsPkWord : C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  calc
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk"
        = C13Concrete.wotsPkWord
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots := by
              simpa [pk, digest] using hWotsPkWord d
    _ = C13Concrete.wordOfHash16 d.wotsPk0 := by
      exact c13_wotsPkWord_eq_wordOfHash16_of_wots_success
        pk 0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        forsPk d.wotsPk0 d.lsig0.wots
        (by
          simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
            SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
            SegmentAcceptSpec.c13LayerTreeIdx, c13,
            C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)

/-- Layer-1 WOTS before-auth residual reduced to the raw executable
`wotsPkWord` binding. -/
theorem c13FoldOkBeforeAuthOffWotsPkDataLayer1_of_wotsPkWord
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWotsPkWord : C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  calc
    lookupValue
        (SegmentLayer3.beforeAuthOff
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig))).bindings
        "wotsPk"
        = C13Concrete.wotsPkWord
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots := by
              simpa [pk, digest] using hWotsPkWord d
    _ = C13Concrete.wordOfHash16 d.wotsPk1 := by
      exact c13_wotsPkWord_eq_wordOfHash16_of_wots_success
        pk 1 ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
        d.root0 d.wotsPk1 d.lsig1.wots
        (by
          simpa [C13Concrete.c13PrimitivesConcrete, pk, digest,
            SegmentAcceptSpec.c13LayerNextTree, SegmentAcceptSpec.c13LayerLeafIdx,
            SegmentAcceptSpec.c13LayerTreeIdx, c13] using d.hWots1)

/-- Layer-0 before-auth WOTS-PK residual discharged directly from concrete
`beforeWotsPk` preimage cells. -/
theorem c13FoldOkBeforeAuthOffWotsPkDataLayer0_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkBeforeAuthOffWotsPkDataLayer0_of_wotsPkWord
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_preimage_cells
      pkSeed pkRoot message sig sigParsed forsPk specRoot hCells)

/-- Layer-1 before-auth WOTS-PK residual discharged directly from concrete
`beforeWotsPk` preimage cells. -/
theorem c13FoldOkBeforeAuthOffWotsPkDataLayer1_of_preimage_cells
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hCells : C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkBeforeAuthOffWotsPkDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkBeforeAuthOffWotsPkDataLayer1_of_wotsPkWord
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_preimage_cells
      pkSeed pkRoot message sig sigParsed forsPk specRoot hCells)

/-- Layer-0 WOTS start-node fact reduced to the strictly earlier executable
cutpoint where `"wotsPk"` has just been bound. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_beforeAuthOff
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWotsPk : C13FoldOkBeforeAuthOffWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rw [beforeMerkle_wotsPk_eq_beforeAuthOff_wotsPk]
  exact hWotsPk d

/-- Layer-1 WOTS start-node fact reduced to the strictly earlier executable
cutpoint where `"wotsPk"` has just been bound. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_beforeAuthOff
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWotsPk : C13FoldOkBeforeAuthOffWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  rw [beforeMerkle_wotsPk_eq_beforeAuthOff_wotsPk]
  exact hWotsPk d

/-- Layer-0 after-Merkle initial WOTS start-node fact reduced all the way down
to the executable final masked-Keccak cutpoint, threading the existing
`final_keccak ⇒ wotsPkWord ⇒ beforeAuthOff ⇒ afterMerkle` reducer chain.  The
caller now only has to discharge the executable evaluation of the final 45-word
masked Keccak load at `beforeAuthOff`. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_final_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFinal : C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_beforeAuthOff
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkDataLayer0_of_wotsPkWord
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_final_keccak
        pkSeed pkRoot message sig sigParsed forsPk specRoot hFinal))

/-- Layer-1 analogue of
`c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_final_keccak`. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_final_keccak
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFinal : C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_beforeAuthOff
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkDataLayer1_of_wotsPkWord
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_final_keccak
        pkSeed pkRoot message sig sigParsed forsPk specRoot hFinal))

/-- Layer-0 after-Merkle initial WOTS start-node fact reduced to the strictly
weaker `C13FoldOkBeforeAuthOffWotsPkWordDataLayer0` cutpoint.  Unlike
`_of_final_keccak`, the caller no longer has to discharge the binding-eval
structural conjunct nor the executable masked-Keccak evaluation: the single
direct binding equation
`lookup "wotsPk" = C13Concrete.wotsPkWord …` is enough.  The `wotsPkWord =
wordOfHash16 d.wotsPk0` reduction comes from `d.hWots0` via
`c13_wotsPkWord_eq_wordOfHash16_of_wots_success` (no executable side). -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_wotsPkWord
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWotsPkWord : C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_beforeAuthOff
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkDataLayer0_of_wotsPkWord
      pkSeed pkRoot message sig sigParsed forsPk specRoot hWotsPkWord)

/-- Layer-1 analogue of
`c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_wotsPkWord`. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_wotsPkWord
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWotsPkWord : C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_beforeAuthOff
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkBeforeAuthOffWotsPkDataLayer1_of_wotsPkWord
      pkSeed pkRoot message sig sigParsed forsPk specRoot hWotsPkWord)

/-- Explicit per-step witness package for one frame-threaded XMSS climb.  It is
the C13-local surface needed to invoke the generic `MerkleClimbFrame_hstep`
builder without expanding that proof at every layer-specific residual. -/
def C13AfterMerkleXmssFrameStepWitnessPremiseAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
    ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
      ((a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
          ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40)) ∧
      vpar = a.1 / 2 ∧
      wordNormalize vnode = a.2 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vadr vsib2 seed treeAdrs idx a.1 auth ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
            "sibling" vsib) "parentIdx" vpar }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "merkleNode") = some vnode ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "sibling") = some vsib2

/-- Raw exact-node analogue of
`C13AfterMerkleXmssFrameStepWitnessPremiseAt`. -/
def C13AfterMerkleXmssRawStepWitnessPremiseAt
    (seed treeAdrs : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx" s a →
    ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
      ((a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
          ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40)) ∧
      vpar = a.1 / 2 ∧
      wordNormalize vnode = a.2 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vadr vsib2 seed treeAdrs idx a.1 auth ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
            "sibling" vsib) "parentIdx" vpar }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "merkleNode") = some vnode ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "sibling") = some vsib2

/-- Smaller per-call eval package behind
`C13AfterMerkleXmssFrameStepWitnessPremiseAt`: the hard executable facts are
the bounded masked sibling load (`h1`), the ADRS expression eval (`h3`), and
the normalized ADRS word.  The generic parent-index/selector/child-slot
bookkeeping is reconstructed by
`c13AfterMerkleXmssFrameStepWitnessCall_of_eval`. -/
def C13AfterMerkleXmssFrameStepEvalFacts
    (s : RuntimeState) (a : Nat × Nat) (idx treeAdrs : Nat)
    (cdAt : Nat → Nat) : Prop :=
  ∃ vsib vadr,
    idx < 11 ∧
    a.1 < 2 ^ 256 ∧
    lookupValue s.bindings "treeAdrs" = treeAdrs ∧
    treeAdrs < 2 ^ 256 ∧
    evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
      (.bitAnd (.calldataload (.add (.localVar "merklePtr")
        (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
        = some vsib ∧
    vsib = SphincsMinusVerifierSpec.C13Concrete.maskN (cdAt idx) ∧
    evalExpr []
      { s with bindings :=
        bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
          "sibling" vsib) "parentIdx" (a.1 / 2) }
      (.bitOr (.localVar "treeAdrs")
        (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
          (.localVar "parentIdx"))) = some vadr ∧
    wordNormalize vadr = treeAdrs ||| ((idx + 1) <<< 32) ||| a.1 / 2

/-- Smaller site-specific residue for
`C13AfterMerkleXmssFrameStepEvalFacts`.  The frame supplies the `"treeAdrs"`
binding, and the normalized ADRS word is reconstructed from the ADRS expression
eval plus ordinary operand bounds. -/
def C13AfterMerkleXmssFrameStepCoreEvalFacts
    (s : RuntimeState) (a : Nat × Nat) (idx treeAdrs : Nat)
    (cdAt : Nat → Nat) : Prop :=
  ∃ vsib vadr,
    idx < 11 ∧
    a.1 < 2 ^ 256 ∧
    treeAdrs < 2 ^ 256 ∧
    evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
      (.bitAnd (.calldataload (.add (.localVar "merklePtr")
        (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
        = some vsib ∧
    vsib = SphincsMinusVerifierSpec.C13Concrete.maskN (cdAt idx) ∧
    evalExpr []
      { s with bindings :=
        bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
          "sibling" vsib) "parentIdx" (a.1 / 2) }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr

/-- Concrete C13 layer-frame constructor for the smaller core eval package.  The
remaining non-executable inputs are exactly the loop height bound and the current
`"mIdx"`/tree-address word bounds; the masked sibling read and ADRS expression
eval are discharged from the frozen calldata/frame facts. -/
theorem c13AfterMerkleXmssFrameStepCoreEvalFacts_of_c13_layer_frame
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs : Nat) (layer idx : Nat)
    (s : RuntimeState) (a : Nat × Nat)
    (hLayer : layer < 2)
    (hidx : idx < 11)
    (hmIdxLt : a.1 < 2 ^ 256)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (hFrame :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692)) s a) :
    C13AfterMerkleXmssFrameStepCoreEvalFacts s a idx treeAdrs
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * layer + 692))) := by
  let stH : RuntimeState :=
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let ap : Nat := sigDataOffset + (1952 + 868 * layer + 692)
  let sOff : Nat := 1952 + 868 * layer + 692 + 16 * idx
  let vsib : Nat :=
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (c13XmssAuthCdAt pkSeed pkRoot message sig ap idx)
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hselH : stH.selector = 0 := by
    dsimp [stH]
    exact hFrame.2.2.2.2.1
  have hcdH : stH.world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
    dsimp [stH]
    exact hFrame.2.2.2.2.2.1
  have hapH : evalExpr [] stH (.localVar "merklePtr") = some ap := by
    show some (lookupValue stH.bindings "merklePtr") = some ap
    dsimp [stH, ap]
    rw [MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "merklePtr" (wordNormalize idx) (by decide)]
    exact congrArg some hFrame.2.2.1
  have hhH : evalExpr [] stH (.localVar "h") = some idx := by
    show some (lookupValue stH.bindings "h") = some idx
    dsimp [stH]
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have haplt : ap < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have hshift : idx <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    omega
  have hsum : ap + idx <<< 4 < 2 ^ 256 := by
    dsimp [ap]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset, Nat.shiftLeft_eq]
    omega
  have hoff : ap + idx <<< 4 = sigDataOffset + sOff := by
    dsimp [ap, sOff]
    rw [Nat.shiftLeft_eq]
    omega
  have hoff4 : 4 ≤ sigDataOffset + sOff := by
    dsimp [sOff]
    rw [SphincsMinusVerifiers.MkC13State.sigDataOffset]
    omega
  have h1 : evalExpr [] stH
      (.bitAnd (.calldataload (.add (.localVar "merklePtr")
        (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some vsib := by
    dsimp [vsib]
    have hread :=
      SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_sibling_read_frozen
        stH "merklePtr" pkSeed pkRoot message sig ap idx sOff
        hselH hcdH hapH hhH haplt hidx256 hshift hsum hoff hoff4
    simpa [c13XmssAuthCdAt, ap, sOff, Nat.shiftLeft_eq, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using hread
  rcases SegmentLayer3MerkleFrame.layer_address_assembly_eval_exists
      s idx vsib treeAdrs a.1 hFrame.2.1 hTreeLt hmIdxLt hidx with
    ⟨vadr, h3⟩
  refine ⟨vsib, vadr, hidx, hmIdxLt, hTreeLt, ?_, ?_, ?_⟩
  · simpa [stH] using h1
  · dsimp [vsib]
  · simpa [Nat.shiftRight_eq_div_pow] using h3

/-- Reconstruct the full C13 per-call eval package from the smaller
site-specific residue and the static `MerkleClimbFrame`. -/
theorem c13AfterMerkleXmssFrameStepEvalFacts_of_core
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (cdAt : Nat → Nat)
    (hFrame :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs merklePtr s a)
    (hCore : C13AfterMerkleXmssFrameStepCoreEvalFacts s a idx treeAdrs cdAt) :
    C13AfterMerkleXmssFrameStepEvalFacts s a idx treeAdrs cdAt := by
  rcases hCore with
    ⟨vsib, vadr, hidx, hmIdxLt, hTreeLt, h1, hload, h3⟩
  let stA : RuntimeState :=
    { s with bindings :=
      bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
        "sibling" vsib) "parentIdx" (a.1 / 2) }
  let sh : Nat := (idx + 1) <<< 32
  have hidx256 : idx < 2 ^ 256 := lt_trans hidx (by decide)
  have hwordlt : idx + 1 < 2 ^ 256 := by omega
  have hshlt : sh < 2 ^ 256 := by
    dsimp [sh]
    rw [Nat.shiftLeft_eq]
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right (2 ^ 32) (Nat.succ_le_of_lt hidx))
      (by decide : 11 * 2 ^ 32 < 2 ^ 256)
  have hparentLt : a.1 / 2 < 2 ^ 256 := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self a.1 2) hmIdxLt
  have hbaseEval : evalExpr [] stA (.localVar "treeAdrs") = some treeAdrs := by
    show some (lookupValue stA.bindings "treeAdrs") = some treeAdrs
    dsimp [stA]
    rw [MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "treeAdrs" (a.1 / 2) (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "treeAdrs" vsib (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne
      s.bindings "h" "treeAdrs" (wordNormalize idx) (by decide)]
    exact congrArg some hFrame.2.1
  have hhEval : evalExpr [] stA (.localVar "h") = some idx := by
    show some (lookupValue stA.bindings "h") = some idx
    dsimp [stA]
    rw [MemoryKit.lookupValue_bindValue_ne
      (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib)
      "parentIdx" "h" (a.1 / 2) (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne
      (bindValue s.bindings "h" (wordNormalize idx))
      "sibling" "h" vsib (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have hparentEval : evalExpr [] stA (.localVar "parentIdx") = some (a.1 / 2) := by
    show some (lookupValue stA.bindings "parentIdx") = some (a.1 / 2)
    dsimp [stA]
    rw [MemoryKit.lookupValue_bindValue_self]
  have hlit1 : evalExpr [] stA (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hplus : evalExpr [] stA (.add (.localVar "h") (.literal 1))
      = some (idx + 1) := by
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      stA (.localVar "h") (.literal 1) idx 1 hhEval hlit1 hidx256 (by decide) hwordlt
  have hlit32 : evalExpr [] stA (.literal 32) = some 32 := by
    show some (wordNormalize 32) = some 32
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hsh : evalExpr [] stA
      (.shl (.literal 32) (.add (.localVar "h") (.literal 1))) = some sh := by
    dsimp [sh]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      stA (.literal 32) (.add (.localVar "h") (.literal 1)) 32 (idx + 1)
      hlit32 hplus (by decide) hwordlt hshlt
  have hadr : wordNormalize vadr = treeAdrs ||| ((idx + 1) <<< 32) ||| a.1 / 2 := by
    have hadr' := SphincsMinusVerifiers.ClimbMemFrameMerkle.address_assembly_eq
      stA (.localVar "treeAdrs")
      (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
      (.localVar "parentIdx") vadr treeAdrs sh (a.1 / 2)
      h3 hbaseEval hsh hparentEval hTreeLt hshlt hparentLt
    simpa [stA, sh] using hadr'
  exact ⟨vsib, vadr, hidx, hmIdxLt, hFrame.2.1, hTreeLt, h1, hload, h3, hadr⟩

/-- Per-call constructor for the frame step witness from the smaller executable
eval package.  This closes all generic binding, parity, and reread fields; what
remains outside this theorem is exactly the site-specific executable eval data
named by `C13AfterMerkleXmssFrameStepEvalFacts`. -/
theorem c13AfterMerkleXmssFrameStepWitnessCall_of_eval
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (hData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx)
    (hFrame :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs merklePtr s a)
    (hEval : C13AfterMerkleXmssFrameStepEvalFacts s a idx treeAdrs cdAt) :
    ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
      ((a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
          ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40)) ∧
      vpar = a.1 / 2 ∧
      wordNormalize vnode = a.2 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vadr vsib2 seed treeAdrs idx a.1 auth ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
            "sibling" vsib) "parentIdx" vpar }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "merkleNode") = some vnode ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "sibling") = some vsib2 := by
  rcases hEval with
    ⟨vsib, vadr, hidx, hmIdxLt, _hTree, _hTreeLt, h1, hload, h3, hadr⟩
  let stH : RuntimeState := { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := a.1 / 2
  let st1 : RuntimeState := { stH with bindings := bindValue stH.bindings "sibling" vsib }
  let st2 : RuntimeState := { st1 with bindings := bindValue st1.bindings "parentIdx" vpar }
  let sval : Nat := (a.1 &&& 1) <<< 5
  let st3 : RuntimeState :=
    { st2 with world := { st2.world with memory := MemoryKit.memUpdate st2.world.memory 0x20 vadr } }
  let st4 : RuntimeState := { st3 with bindings := bindValue st3.bindings "s" sval }
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let vnode : Nat := lookupValue st4.bindings "merkleNode"
  let st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  let vsib2 : Nat := lookupValue st5.bindings "sibling"
  have hmIdxH : lookupValue stH.bindings "mIdx" = a.1 := by
    dsimp [stH]
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.idx hFrame.1
  have hmIdx1 : lookupValue st1.bindings "mIdx" = a.1 := by
    dsimp [st1]
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "mIdx" _ (by decide)]
    exact hmIdxH
  have h2 : evalExpr [] st1 (.shr (.literal 1) (.localVar "mIdx")) = some vpar := by
    dsimp [vpar]
    rw [← SphincsMinusVerifiers.ClimbMemFrameMerkle.parentIdx_shiftRight a.1]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "mIdx" st1 a.1 hmIdx1 hmIdxLt
  have hmIdx2 : lookupValue st2.bindings "mIdx" = a.1 := by
    dsimp [st2]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "mIdx" _ (by decide)]
    exact hmIdx1
  have hmIdx3 : lookupValue st3.bindings "mIdx" = a.1 := by
    dsimp [st3]
    exact hmIdx2
  have h4 : evalExpr [] st3
      (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval := by
    dsimp [sval]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "mIdx" st3 a.1 hmIdx3 hmIdxLt
  have hsvalt : sval < 2 ^ 256 := by
    dsimp [sval]
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 : lookupValue st4.bindings "s" = sval := by
    dsimp [st4]
    rw [MemoryKit.lookupValue_bindValue_self]
  have h5off : evalExpr [] st4 (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    dsimp [o5]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st4 0x40 sval hs4 (by decide) hsvalt
  have h5val : evalExpr [] st4 (.localVar "merkleNode") = some vnode := by
    rfl
  have hs5 : lookupValue st5.bindings "s" = sval := by
    dsimp [st5]
    exact hs4
  have h6off : evalExpr [] st5 (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    dsimp [o6]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      st5 0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr [] st5 (.localVar "sibling") = some vsib2 := by
    rfl
  have hnode : wordNormalize vnode = a.2 := by
    dsimp [vnode, st4, st3, st2, st1, stH]
    rw [MemoryKit.lookupValue_bindValue_ne _ "s" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRel.node hFrame.1
  have hseed : (stH.world.memory 0x00).val = seed := by
    dsimp [stH]
    exact hFrame.2.2.2.1
  have hstepData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        stH vadr vsib2 seed treeAdrs idx a.1 auth := by
    refine SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations.intro
      hseed hadr ?_
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleClimbData_to_sib
      auth cdAt idx stH vsib vpar vadr sval o5 vnode vsib2 h6val hload hData
  have hpar : a.1 % 2 = 0 ∨ a.1 % 2 = 1 := by
    have hlt : a.1 % 2 < 2 := Nat.mod_lt a.1 (by decide)
    omega
  have hparOff : (a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even a.1 hzero
      exact ⟨hzero, by simpa [o5, sval] using ho.1, by simpa [o6, sval] using ho.2⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd a.1 hone
      exact ⟨hone, by simpa [o5, sval] using ho.1, by simpa [o6, sval] using ho.2⟩
  refine ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
    hparOff, rfl, hnode, hstepData, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [stH] using h1
  · simpa [st1] using h2
  · simpa [stH, st1, st2, vpar] using h3
  · simpa [stH, st1, st2, st3] using h4
  · simpa [stH, st1, st2, st3, st4] using h5off
  · simpa [stH, st1, st2, st3, st4, vnode] using h5val
  · simpa [stH, st1, st2, st3, st4, st5, o5, vnode] using h6off
  · simpa [stH, st1, st2, st3, st4, st5, o5, vnode, vsib2] using h6val

/-- If an abstract natural already is its EVM word normalization, then it is a
256-bit word. -/
theorem wordNormalize_eq_self_lt {n : Nat} (h : wordNormalize n = n) :
    n < 2 ^ 256 := by
  rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl] at h
  rw [← h]
  exact Nat.mod_lt n (by decide : 0 < 2 ^ 256)

/-- A value below the C13 XMSS leaf range is already an EVM word. -/
theorem wordNormalize_mod_2048 (n : Nat) :
    wordNormalize (n % 2048) = n % 2048 :=
  SegmentS2.wordNormalize_of_lt
    (lt_trans (Nat.mod_lt n (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 256))

/-- Layer-0 `beforeMerkle` `"mIdx"` is word-normalized because the concrete site
binds it to the low 11 bits of the C13 hypertree index. -/
theorem c13FirstLayerBeforeMerkle_mIdx_norm_of_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    wordNormalize
        (lookupValue
          (SegmentLayer3.beforeMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "mIdx") =
      lookupValue
        (SegmentLayer3.beforeMerkle
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "mIdx" := by
  rw [c13FirstLayerBeforeMerkle_mIdx_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse]
  exact wordNormalize_mod_2048 _

/-- Layer-1 analogue of `c13FirstLayerBeforeMerkle_mIdx_norm_of_hyperIndex`. -/
theorem c13SecondLayerBeforeMerkle_mIdx_norm_of_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    wordNormalize
        (lookupValue
          (SegmentLayer3.beforeMerkle
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "mIdx") =
      lookupValue
        (SegmentLayer3.beforeMerkle
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
        "mIdx" := by
  rw [c13SecondLayerBeforeMerkle_mIdx_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse]
  exact wordNormalize_mod_2048 _

/-- The actual layer-0 initial XMSS frame starts with a normalized `"mIdx"`,
projected through the frame relation from the concrete before-Merkle site. -/
theorem c13AfterMerkleXmssInitialFramePremiseAt_layer0_mIdx_norm
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (node : Nat) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    C13AfterMerkleXmssInitialFramePremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048) node →
    wordNormalize (digest.hyperIndex % 2048) = digest.hyperIndex % 2048 := by
  intro pk digest hFrame
  have hidx :=
    (SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame.toRel hFrame).idx
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)] at hidx
  have hsite :=
    c13FirstLayerBeforeMerkle_mIdx_norm_of_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse
  simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0, hidx] using hsite

/-- The actual layer-1 initial XMSS frame starts with a normalized `"mIdx"`,
again projected from the concrete before-Merkle low-11-bit binding. -/
theorem c13AfterMerkleXmssInitialFramePremiseAt_layer1_mIdx_norm
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (node : Nat) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    C13AfterMerkleXmssInitialFramePremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048) node →
    wordNormalize ((digest.hyperIndex / 2048) % 2048) =
      (digest.hyperIndex / 2048) % 2048 := by
  intro pk digest hFrame
  have hidx :=
    (SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame.toRel hFrame).idx
  rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)] at hidx
  have hsite :=
    c13SecondLayerBeforeMerkle_mIdx_norm_of_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse
  simpa [c13SecondLayerGuardState_eq_c13LayerLoopState1, hidx] using hsite

/-- The C13 Merkle-climb parent index preserves the current `"mIdx"` word
normalization invariant. -/
theorem wordNormalize_div_two_of_eq_self {n : Nat}
    (h : wordNormalize n = n) :
    wordNormalize (n / 2) = n / 2 :=
  SegmentS2.wordNormalize_of_lt
    (lt_of_le_of_lt (Nat.div_le_self n 2) (wordNormalize_eq_self_lt h))

/-- The first component of one XMSS Merkle spec step is exactly the parent index. -/
theorem merkleSpecStep_fst
    (seed treeAdrs : Nat) (auth : List Bytes) (idx : Nat) (a : Nat × Nat) :
    (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
      seed treeAdrs auth idx a).1 = a.1 / 2 := by
  cases a
  rfl

/-- The remaining runtime word-normalization invariant needed by the concrete C13
XMSS frame-step witness.  The constructor below turns this into the arithmetic
`a.1 < 2^256` bound exactly where the evaluator needs it.  The universal
frame-step surface does not by itself constrain the loop height `idx`; the
`[0, 11)` fact is kept as a separate height premise at the constructor boundary
below. -/
def C13AfterMerkleXmssFrameStepRuntimeBoundsAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
    wordNormalize a.1 = a.1

/-- The separate loop-height component formerly bundled into
`C13AfterMerkleXmssFrameStepRuntimeBoundsAt`.  It cannot be projected from
`MerkleClimbData`, which is only a sibling-correspondence predicate at the given
index. -/
def C13AfterMerkleXmssFrameStepHeightBoundsAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
    idx < 11

/-- Concrete C13 layer frame witness reduced to the remaining loop bounds.  The
frozen calldata read, masked sibling identity, and ADRS expression eval are
closed by `c13AfterMerkleXmssFrameStepCoreEvalFacts_of_c13_layer_frame`; callers
must supply the 11-level XMSS height bound separately from the current `"mIdx"`
word bound. -/
theorem c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_bounds
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs : Nat) (layer : Nat) (auth : List Bytes)
    (hLayer : layer < 2)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (hHeight :
      C13AfterMerkleXmssFrameStepHeightBoundsAt
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692)) auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))))
    (hBounds :
      C13AfterMerkleXmssFrameStepRuntimeBoundsAt
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692)) auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692)))) :
    C13AfterMerkleXmssFrameStepWitnessPremiseAt
      pkSeed pkRoot message sig seed treeAdrs
      (sigDataOffset + (1952 + 868 * layer + 692)) auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * layer + 692))) := by
  intro s a idx hData hFrame
  have hidx := hHeight s a idx hData hFrame
  have hmIdxLt := wordNormalize_eq_self_lt (hBounds s a idx hData hFrame)
  have hCore :
      C13AfterMerkleXmssFrameStepCoreEvalFacts s a idx treeAdrs
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) :=
    c13AfterMerkleXmssFrameStepCoreEvalFacts_of_c13_layer_frame
      pkSeed pkRoot message sig seed treeAdrs layer idx s a
      hLayer hidx hmIdxLt hTreeLt hFrame
  have hEval :
      C13AfterMerkleXmssFrameStepEvalFacts s a idx treeAdrs
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) :=
    c13AfterMerkleXmssFrameStepEvalFacts_of_core
      pkSeed pkRoot message sig seed treeAdrs
      (sigDataOffset + (1952 + 868 * layer + 692))
      s a idx
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * layer + 692)))
      hFrame hCore
  exact c13AfterMerkleXmssFrameStepWitnessCall_of_eval
    pkSeed pkRoot message sig seed treeAdrs
    (sigDataOffset + (1952 + 868 * layer + 692))
    auth
    (c13XmssAuthCdAt pkSeed pkRoot message sig
      (sigDataOffset + (1952 + 868 * layer + 692)))
    s a idx hData hFrame hEval

/-- Site-bounded C13 layer step witness.  Unlike the broad
`C13AfterMerkleXmssFrameStepWitnessPremiseAt` residual, this is the shape consumed by
the actual C13 XMSS loop: the fold site supplies `idx < 11`, while the strengthened
loop invariant supplies the current `"mIdx"` word-normalization fact. -/
theorem c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_site_bounds
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs : Nat) (layer : Nat) (auth : List Bytes)
    (hLayer : layer < 2)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (hidx : idx < 11)
    (hmIdxNorm : wordNormalize a.1 = a.1)
    (hData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) idx)
    (hFrame :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692)) s a) :
    ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
      ((a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
          ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40)) ∧
      vpar = a.1 / 2 ∧
      wordNormalize vnode = a.2 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vadr vsib2 seed treeAdrs idx a.1 auth ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
            "sibling" vsib) "parentIdx" vpar }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "merkleNode") = some vnode ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "sibling") = some vsib2 := by
  have hCore :
      C13AfterMerkleXmssFrameStepCoreEvalFacts s a idx treeAdrs
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) :=
    c13AfterMerkleXmssFrameStepCoreEvalFacts_of_c13_layer_frame
      pkSeed pkRoot message sig seed treeAdrs layer idx s a
      hLayer hidx (wordNormalize_eq_self_lt hmIdxNorm) hTreeLt hFrame
  have hEval :
      C13AfterMerkleXmssFrameStepEvalFacts s a idx treeAdrs
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) :=
    c13AfterMerkleXmssFrameStepEvalFacts_of_core
      pkSeed pkRoot message sig seed treeAdrs
      (sigDataOffset + (1952 + 868 * layer + 692))
      s a idx
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * layer + 692)))
      hFrame hCore
  exact c13AfterMerkleXmssFrameStepWitnessCall_of_eval
    pkSeed pkRoot message sig seed treeAdrs
    (sigDataOffset + (1952 + 868 * layer + 692))
    auth
    (c13XmssAuthCdAt pkSeed pkRoot message sig
      (sigDataOffset + (1952 + 868 * layer + 692)))
    s a idx hData hFrame hEval

/-- The site-bounded C13 layer step preserves both the frame and the strengthened
runtime invariant.  This is the substantive runtime reduction at the real C13 loop
site: the next `"mIdx"` is `a.1 / 2`, so word-normalization is preserved without a
separate universal `C13AfterMerkleXmssFrameStepRuntimeBoundsAt` assumption. -/
theorem c13AfterMerkleXmssFrameStepBoundedInvariant_of_c13_layer_site_bounds
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs : Nat) (layer : Nat) (auth : List Bytes)
    (hLayer : layer < 2)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (hSite :
      idx < 11 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) idx)
    (hInv :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692)) s a ∧
      wordNormalize a.1 = a.1) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692))
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
          seed treeAdrs auth idx a) ∧
      wordNormalize
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
          seed treeAdrs auth idx a).1 =
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
          seed treeAdrs auth idx a).1 := by
  rcases hSite with ⟨hidx, hData⟩
  rcases hInv with ⟨hFrame, hmIdxNorm⟩
  rcases a with ⟨mIdx, node⟩
  have hWitness :=
    c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_site_bounds
      pkSeed pkRoot message sig seed treeAdrs layer auth hLayer hTreeLt
      s (mIdx, node) idx hidx hmIdxNorm hData hFrame
  constructor
  · rcases hWitness with
      ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
        hparOff, hvpar, hnode, hStepData,
        h1, h2, h3, h4, h5off, h5val, h6off, h6val⟩
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_hstep
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs
      (sigDataOffset + (1952 + 868 * layer + 692))
      s mIdx node idx auth
      vsib vpar vadr sval o5 vnode o6 vsib2 hFrame
      hparOff hvpar hnode hStepData
      h1 h2 h3 h4 h5off h5val h6off h6val
  · rw [merkleSpecStep_fst]
    exact wordNormalize_div_two_of_eq_self hmIdxNorm

/-- Local bounded-step model lift: the `wordNormalize`-of-`afterMerkle` to
`xmssClimb` equality at one C13 layer site, threaded through the bounded
universal step preserved by
`c13AfterMerkleXmssFrameStepBoundedInvariant_of_c13_layer_site_bounds`.
Unlike `SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame_c13`, this lift
carries the `wordNormalize a.1 = a.1` invariant in the loop-invariant predicate,
so no broad universal step witness (and hence no
`C13AfterMerkleXmssFrameStepRuntimeBoundsAt`) is required from the caller. -/
theorem c13AfterMerkleNormalizedXmssClimb_of_layer_site_bounded
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs : Nat) (layer : Nat) (auth : List Bytes)
    (hLayer : layer < 2)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (ls : RuntimeState) (mIdx node : Nat)
    (hData : ∀ i, i < 11 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) i)
    (hR : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            pkSeed pkRoot message sig seed treeAdrs
            (sigDataOffset + (1952 + 868 * layer + 692))
            { SegmentLayer3.beforeMerkle ls with
              bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
                (wordNormalize 0) }
            (mIdx, node))
    (hMIdxNorm : wordNormalize mIdx = mIdx) :
    wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode")
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  let R : RuntimeState → Nat × Nat → Prop := fun s a =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs
      (sigDataOffset + (1952 + 868 * layer + 692)) s a ∧
    wordNormalize a.1 = a.1
  let D : Nat → Prop := fun idx =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * layer + 692))) idx ∧ idx < 11
  have hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
      D idx → R s a →
      R (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep seed treeAdrs auth
          idx a) := by
    intro s a idx hD hR'
    exact c13AfterMerkleXmssFrameStepBoundedInvariant_of_c13_layer_site_bounds
      pkSeed pkRoot message sig seed treeAdrs layer auth hLayer hTreeLt
      s a idx ⟨hD.2, hD.1⟩ hR'
  have hRange : ∀ i, 0 ≤ i → i < 0 + 11 → D i := fun i _ hi =>
    ⟨hData i (by omega), by omega⟩
  have hR0 : R { SegmentLayer3.beforeMerkle ls with
                  bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
                    (wordNormalize 0) }
                 (mIdx, node) := ⟨hR, hMIdxNorm⟩
  have hresult :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_invariant_cond "h"
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "treeAdrs" "merklePtr")
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep seed treeAdrs auth)
      R D hstep
      { SegmentLayer3.beforeMerkle ls with
        bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
          (wordNormalize 0) }
      (mIdx, node) 0 11 hRange hR0
  rcases hresult with ⟨hframeFinal, _⟩
  have h11 : wordNormalize 11 = 11 :=
    SegmentS2.wordNormalize_of_lt (by decide : 11 < 2 ^ 256)
  rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimb_eq_specFold]
  show wordNormalize (lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode") = _
  unfold SegmentLayer3.afterMerkle
  rw [h11]
  exact hframeFinal.toRel.node

/-- Local bounded-step exact model lift: the raw `afterMerkle` node equals the
spec `xmssClimb` at one C13 layer site.  This strengthens
`c13AfterMerkleNormalizedXmssClimb_of_layer_site_bounded` by threading the exact
`MerkleClimbRawRel` alongside the frame invariant, avoiding the broad universal
raw-step premise used by `c13AfterMerkleRawXmssClimb_of_raw_premises_at`. -/
theorem c13AfterMerkleRawXmssClimb_of_layer_site_bounded
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs : Nat) (layer : Nat) (auth : List Bytes)
    (hLayer : layer < 2)
    (hTreeLt : treeAdrs < 2 ^ 256)
    (ls : RuntimeState) (mIdx node : Nat)
    (hData : ∀ i, i < 11 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * layer + 692))) i)
    (hFrame : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            pkSeed pkRoot message sig seed treeAdrs
            (sigDataOffset + (1952 + 868 * layer + 692))
            { SegmentLayer3.beforeMerkle ls with
              bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
                (wordNormalize 0) }
            (mIdx, node))
    (hRaw : SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
            "merkleNode" "mIdx"
            { SegmentLayer3.beforeMerkle ls with
              bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
                (wordNormalize 0) }
            (mIdx, node))
    (hMIdxNorm : wordNormalize mIdx = mIdx) :
    lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode"
      = C13Concrete.xmssClimb seed treeAdrs 11 0 mIdx node auth := by
  let R : RuntimeState → Nat × Nat → Prop := fun s a =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs
      (sigDataOffset + (1952 + 868 * layer + 692)) s a ∧
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx" s a ∧
    wordNormalize a.1 = a.1
  let D : Nat → Prop := fun idx =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * layer + 692))) idx ∧ idx < 11
  have hstep : ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
      D idx → R s a →
      R (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep seed treeAdrs auth
          idx a) := by
    intro s a idx hD hR'
    rcases hR' with ⟨hFrame', hRaw', hmIdxNorm⟩
    rcases a with ⟨mIdx', node'⟩
    have hWitness :=
      c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_site_bounds
        pkSeed pkRoot message sig seed treeAdrs layer auth hLayer hTreeLt
        s (mIdx', node') idx hD.2 hmIdxNorm hD.1 hFrame'
    rcases hWitness with
      ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
        hparOff, hvpar, hnode, hStepData,
        h1, h2, h3, h4, h5off, h5val, h6off, h6val⟩
    have hFrameNext :
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          pkSeed pkRoot message sig seed treeAdrs
          (sigDataOffset + (1952 + 868 * layer + 692))
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx (mIdx', node')) :=
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_hstep
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig seed treeAdrs
        (sigDataOffset + (1952 + 868 * layer + 692))
        s mIdx' node' idx auth
        vsib vpar vadr sval o5 vnode o6 vsib2 hFrame'
        hparOff hvpar hnode hStepData
        h1 h2 h3 h4 h5off h5val h6off h6val
    have hPair :
        (lookupValue
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "treeAdrs" "merklePtr"
              { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
            "mIdx",
          lookupValue
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "treeAdrs" "merklePtr"
              { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
            "merkleNode")
          =
          SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx (mIdx', node') := by
      exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_eq_merkleSpecStep
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vsib vpar vadr sval o5 vnode o6 vsib2
        seed treeAdrs idx mIdx' node' auth
        (by decide) (by decide) hparOff hvpar hStepData.1 hStepData.2.1
        hnode hStepData.2.2 h1 h2 h3 h4 h5off h5val h6off h6val
    have hRawNext :
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "treeAdrs" "merklePtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            seed treeAdrs auth idx (mIdx', node')) :=
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel_of_pair
        "merkleNode" "mIdx"
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "treeAdrs" "merklePtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
        seed treeAdrs idx mIdx' node' auth hPair
    refine ⟨hFrameNext, hRawNext, ?_⟩
    rw [merkleSpecStep_fst]
    exact wordNormalize_div_two_of_eq_self hmIdxNorm
  have hRange : ∀ i, 0 ≤ i → i < 0 + 11 → D i := fun i _ hi =>
    ⟨hData i (by omega), by omega⟩
  have hR0 : R { SegmentLayer3.beforeMerkle ls with
                  bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
                    (wordNormalize 0) }
                 (mIdx, node) := ⟨hFrame, hRaw, hMIdxNorm⟩
  have hresult :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_invariant_cond "h"
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "treeAdrs" "merklePtr")
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep seed treeAdrs auth)
      R D hstep
      { SegmentLayer3.beforeMerkle ls with
        bindings := bindValue (SegmentLayer3.beforeMerkle ls).bindings "h"
          (wordNormalize 0) }
      (mIdx, node) 0 11 hRange hR0
  rcases hresult with ⟨_, hrawFinal, _⟩
  have h11 : wordNormalize 11 = 11 :=
    SegmentS2.wordNormalize_of_lt (by decide : 11 < 2 ^ 256)
  rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimb_eq_specFold]
  show lookupValue (SegmentLayer3.afterMerkle ls).bindings "merkleNode" = _
  unfold SegmentLayer3.afterMerkle
  rw [h11]
  exact hrawFinal.node

/-- Reverted layer-1 branch: the raw layer-0 `afterMerkle` XMSS equality follows
from the executable WOTS-PK start-node binding at `beforeAuthOff`.  The Merkle
loop itself is discharged by the bounded exact frame/raw invariant, so the
remaining caller surface is the WOTS public-key reconstruction cutpoint. -/
theorem c13_reverted_afterMerkle_raw_xmss_of_wotsPkWord
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature) (forsPk : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPkWord : C13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk) :
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode" =
        C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
          11 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hData :
      ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
    simpa [pk, c13XmssAuthCdAt] using
      SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
        pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
        (sigDataOffset + (1952 + 868 * 0 + 692))
        hParse (by decide : 0 < 2) d.hLayer0 rfl
  have hTreeLt :
      C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) < 2 ^ 256 :=
    c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  have hWotsPk :
      lookupValue
          (SegmentLayer3.beforeMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "wotsPk" = C13Concrete.wordOfHash16 d.wotsPk0 := by
    rw [beforeMerkle_wotsPk_eq_beforeAuthOff_wotsPk]
    exact c13_reverted_beforeAuthOff_wotsPk0_of_wotsPkWord
      pkSeed pkRoot message sig sigParsed forsPk hWotsPkWord d
  have hRaw :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx"
        { SegmentLayer3.beforeMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig) with
          bindings := bindValue
            (SegmentLayer3.beforeMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "h" (wordNormalize 0) }
        (digest.hyperIndex % 2048, C13Concrete.wordOfHash16 d.wotsPk0) := by
    refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel.intro ?_ ?_ ?_
    · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
      simpa [pk, digest] using
        c13FirstLayerBeforeMerkle_mIdx_hyperIndex
          pkSeed pkRoot message sig sigParsed hParse
    · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
      rw [beforeMerkle_merkleNode_eq_wotsPk]
      exact hWotsPk
    · exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_wordOfHash16 d.wotsPk0
  have hFrame :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
        "merkleNode" "mIdx" "treeAdrs" "merklePtr"
        pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        (sigDataOffset + (1952 + 868 * 0 + 692))
        { SegmentLayer3.beforeMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig) with
          bindings := bindValue
            (SegmentLayer3.beforeMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "h" (wordNormalize 0) }
        (digest.hyperIndex % 2048, C13Concrete.wordOfHash16 d.wotsPk0) := by
    have hSite :=
      c13FirstLayerBeforeMerkle_layerFrozenSite
        pkSeed pkRoot message sig sigParsed hParse
    rcases hSite with ⟨treeAdrs, hSel, hCd, hPtr, _hTree, _hTreeLt, _hmIdxLt⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact hRaw.toRel
    · change lookupValue
          (bindValue
            (SegmentLayer3.beforeMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "h" (wordNormalize 0)) "treeAdrs" =
          C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048)
      rw [MemoryKit.lookupValue_bindValue_ne _ "h" "treeAdrs" _ (by decide)]
      simpa [pk, digest] using
        SegmentLayer3.beforeMerkle_treeAdrs_eq_of_layer_idxTree
          (c13FirstLayerGuardState pkSeed pkRoot message sig)
          0 digest.hyperIndex
          (c13FirstLayerGuardState_layer pkSeed pkRoot message sig)
          (c13FirstLayerGuardState_idxTree_hyperIndex
            pkSeed pkRoot message sig hParse)
          (by decide : 0 < 2 ^ 32)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
    · change lookupValue
          (bindValue
            (SegmentLayer3.beforeMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "h" (wordNormalize 0)) "merklePtr" =
          sigDataOffset + (1952 + 868 * 0 + 692)
      rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merklePtr" _ (by decide)]
      exact hPtr
    · change ((SegmentLayer3.beforeMerkle
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          C13Concrete.wordOfHash16 pkSeed
      have hMem :
          ((SegmentLayer3.beforeMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
            ((SegmentLayer3.afterDigit
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val := by
        exact SegmentLayer3.beforeMerkle_preserves_memory_zero_of_loop_frames
          (c13FirstLayerGuardState pkSeed pkRoot message sig)
          SegmentLayer3.wotsOuterForEach_preserves_memory_zero
          SegmentLayer3.copyForEach_preserves_memory_zero
      have hDigit :
          ((SegmentLayer3.afterDigit
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
            C13Concrete.wordOfHash16 pkSeed := by
        rw [SegmentLayer3.afterDigit_preserves_memory_zero]
        exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig
      exact hMem.trans hDigit
    · exact hSel
    · exact hCd
  simpa [pk, digest] using
    c13AfterMerkleRawXmssClimb_of_layer_site_bounded
      pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      0 d.lsig0.authPath (by decide : 0 < 2) hTreeLt
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)
      hData hFrame hRaw (wordNormalize_mod_2048 digest.hyperIndex)

/-- Reverted layer-1 branch: the current raw after-Merkle XMSS residual follows
from the strictly smaller layer-0 WOTS final-Keccak preimage-cell package at
`beforeWotsPk`. -/
theorem c13_reverted_afterMerkle_raw_xmss_of_preimage_cells
    (pkSeed pkRoot message sig sigParsed forsPk)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (_hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (_hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (_hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted)
    (hCells : C13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk) :
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode" =
        C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
          11 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath :=
  c13_reverted_afterMerkle_raw_xmss_of_wotsPkWord
    pkSeed pkRoot message sig sigParsed forsPk hParse
    (c13FoldRevertedBeforeAuthOffWotsPkWordDataLayer0_of_preimage_cells
      pkSeed pkRoot message sig sigParsed forsPk hCells)

/-- Reverted layer-1 branch reduced to the layer-0 `beforeWotsPk` address and
chain-cell residual.  The seed cell is discharged by the verified memory-zero
frame theorem. -/
theorem c13_reverted_afterMerkle_raw_xmss_of_address_chain_cells
    (pkSeed pkRoot message sig sigParsed forsPk)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted)
    (hCells : C13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk) :
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode" =
        C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
          11 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath :=
  c13_reverted_afterMerkle_raw_xmss_of_preimage_cells
    pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
    (c13FoldRevertedBeforeAuthOffWotsPkPreimageCellsDataLayer0_of_seed_address_chain_cells
      pkSeed pkRoot message sig sigParsed forsPk
      (c13FoldRevertedBeforeAuthOffWotsPk_seed_cell pkSeed pkRoot message sig)
      hCells)

/-- Concrete layer-0 C13 frame-step witness: the static layer and XMSS-tree
address word bounds are discharged from the C13 hypertree-index bound.  The only
remaining inputs are the dynamic loop height and current `"mIdx"` word bounds. -/
theorem c13AfterMerkleXmssFrameStepWitnessPremiseAt_layer0_of_runtime_bounds
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (auth : List Bytes)
    (hHeight :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      C13AfterMerkleXmssFrameStepHeightBoundsAt
        pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        (sigDataOffset + (1952 + 868 * 0 + 692)) auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hBounds :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      C13AfterMerkleXmssFrameStepRuntimeBoundsAt
        pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        (sigDataOffset + (1952 + 868 * 0 + 692)) auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 0 + 692)))) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    C13AfterMerkleXmssFrameStepWitnessPremiseAt
      pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692)) auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692))) := by
  intro pk digest
  refine c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_bounds
    pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
    (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048)) 0 auth
    (by decide : 0 < 2) ?_ ?_ ?_
  · exact c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  · simpa [pk, digest] using hHeight
  · simpa [pk, digest] using hBounds

/-- Concrete layer-1 analogue of
`c13AfterMerkleXmssFrameStepWitnessPremiseAt_layer0_of_runtime_bounds`. -/
theorem c13AfterMerkleXmssFrameStepWitnessPremiseAt_layer1_of_runtime_bounds
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (auth : List Bytes)
    (hHeight :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      C13AfterMerkleXmssFrameStepHeightBoundsAt
        pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
        (sigDataOffset + (1952 + 868 * 1 + 692)) auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hBounds :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      C13AfterMerkleXmssFrameStepRuntimeBoundsAt
        pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
        (sigDataOffset + (1952 + 868 * 1 + 692)) auth
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 1 + 692)))) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    C13AfterMerkleXmssFrameStepWitnessPremiseAt
      pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692)) auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692))) := by
  intro pk digest
  refine c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_bounds
    pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
    (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048)) 1 auth
    (by decide : 1 < 2) ?_ ?_ ?_
  · exact c13_adrsXmssTree_lt_of_bounds 1 ((digest.hyperIndex / 2048) / 2048)
      (by decide : 1 < 2 ^ 32)
      (lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)))
  · simpa [pk, digest] using hHeight
  · simpa [pk, digest] using hBounds

/-- Universal step-witness premise carrying the dynamic loop bounds as per-call
hypotheses.  Unlike `C13AfterMerkleXmssFrameStepWitnessPremiseAt`, this packages
`idx < 11` and `wordNormalize a.1 = a.1` as explicit per-call inputs rather than
demanding a separate universal `C13AfterMerkleXmssFrameStepRuntimeBoundsAt`
discharge from the caller.  The layer-specific proofs below build this
unconditionally at each C13 climb site. -/
def C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat) : Prop :=
  ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData auth cdAt idx →
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame
      "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      pkSeed pkRoot message sig seed treeAdrs merklePtr s a →
    idx < 11 →
    wordNormalize a.1 = a.1 →
    ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
      ((a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
          ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40)) ∧
      vpar = a.1 / 2 ∧
      wordNormalize vnode = a.2 ∧
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vadr vsib2 seed treeAdrs idx a.1 auth ∧
      evalExpr [] { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "merklePtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
          = some vsib ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar ∧
      evalExpr []
        { s with bindings :=
          bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
            "sibling" vsib) "parentIdx" vpar }
        (.bitOr (.localVar "treeAdrs")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate s.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "merkleNode") = some vnode ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6 ∧
      evalExpr []
        { s with
          world := { s.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate s.world.memory 0x20 vadr) o5 vnode },
          bindings :=
            bindValue (bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx))
              "sibling" vsib) "parentIdx" vpar) "s" sval }
        (.localVar "sibling") = some vsib2

/-- Layer-0 bounded step witness, proved unconditionally from the layer-site
arithmetic: the only static input is the XMSS tree-address word bound, which
follows from the C13 hypertree-index bound.  This eliminates the broad
`C13AfterMerkleXmssFrameStepRuntimeBoundsAt` premise at the layer-0 caller. -/
theorem c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer0
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (auth : List Bytes) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt
      pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692)) auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692))) := by
  intro pk digest s a idx hData hFrame hidx hmIdxNorm
  have hTreeLt :
      C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) < 2 ^ 256 :=
    c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  have hWitness :=
    c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_site_bounds
      pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      0 auth (by decide : 0 < 2) hTreeLt
      s a idx hidx hmIdxNorm hData hFrame
  show ∃ vsib vpar vadr sval o5 vnode o6 vsib2, _
  exact hWitness

/-- Layer-1 analogue of
`c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer0`. -/
theorem c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer1
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (auth : List Bytes) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt
      pkSeed pkRoot message sig (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692)) auth
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692))) := by
  intro pk digest s a idx hData hFrame hidx hmIdxNorm
  have hTreeLt :
      C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048) < 2 ^ 256 :=
    c13_adrsXmssTree_lt_of_bounds 1 ((digest.hyperIndex / 2048) / 2048)
      (by decide : 1 < 2 ^ 32)
      (lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)))
  have hWitness :=
    c13AfterMerkleXmssFrameStepWitnessPremiseAt_of_c13_layer_site_bounds
      pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      1 auth (by decide : 1 < 2) hTreeLt
      s a idx hidx hmIdxNorm hData hFrame
  show ∃ vsib vpar vadr sval o5 vnode o6 vsib2, _
  exact hWitness

/-- Frame step residual reduced to the generic per-step witness package. -/
theorem c13AfterMerkleXmssFrameStepPremiseAt_of_witness
    (pkSeed pkRoot message sig : Bytes)
    (seed treeAdrs merklePtr : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (hWitness : C13AfterMerkleXmssFrameStepWitnessPremiseAt
        pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt) :
    C13AfterMerkleXmssFrameStepPremiseAt
      pkSeed pkRoot message sig seed treeAdrs merklePtr auth cdAt := by
  intro s a idx hData hFrame
  rcases hWitness s a idx hData hFrame with
    ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
      hparOff, hvpar, hnode, hStepData, h1, h2, h3, h4, h5off, h5val, h6off, h6val⟩
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbFrame_hstep
    "merkleNode" "mIdx" "treeAdrs" "merklePtr"
    pkSeed pkRoot message sig seed treeAdrs merklePtr s a.1 a.2 idx auth
    vsib vpar vadr sval o5 vnode o6 vsib2 hFrame
    hparOff hvpar hnode hStepData h1 h2 h3 h4 h5off h5val h6off h6val

/-- Raw step residual reduced to the exact-node per-step witness package. -/
theorem c13AfterMerkleXmssRawStepPremiseAt_of_witness
    (seed treeAdrs : Nat)
    (auth : List Bytes) (cdAt : Nat → Nat)
    (hWitness : C13AfterMerkleXmssRawStepWitnessPremiseAt
        seed treeAdrs auth cdAt) :
    C13AfterMerkleXmssRawStepPremiseAt seed treeAdrs auth cdAt := by
  intro s a idx hData hRaw
  rcases hWitness s a idx hData hRaw with
    ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
      hparOff, hvpar, hnode, hStepData, h1, h2, h3, h4, h5off, h5val, h6off, h6val⟩
  refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel_of_pair
    "merkleNode" "mIdx"
    (SphincsMinusVerifiers.ClimbKit.stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr"
      { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
    seed treeAdrs idx a.1 a.2 auth ?_
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_eq_merkleSpecStep
    "merkleNode" "mIdx" "treeAdrs" "merklePtr"
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
    vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs idx a.1 a.2 auth
    (by decide) (by decide) hparOff hvpar hStepData.1 hStepData.2.1 hnode hStepData.2.2
    h1 h2 h3 h4 h5off h5val h6off h6val

/-- Layer-0 normalized step residual reduced to its per-step witness package. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer0_of_witness
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          (sigDataOffset + (1952 + 868 * 0 + 692))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692)))) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact c13AfterMerkleXmssFrameStepPremiseAt_of_witness
    pkSeed pkRoot message sig
    (C13Concrete.wordOfHash16 pkSeed)
    (C13Concrete.adrsXmssTree 0
      ((C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
    (sigDataOffset + (1952 + 868 * 0 + 692))
    d.lsig0.authPath
    (c13XmssAuthCdAt pkSeed pkRoot message sig
      (sigDataOffset + (1952 + 868 * 0 + 692)))
    (hWitness d)

/-- Layer-1 normalized step residual reduced to its per-step witness package. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer1_of_witness
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          (sigDataOffset + (1952 + 868 * 1 + 692))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692)))) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact c13AfterMerkleXmssFrameStepPremiseAt_of_witness
    pkSeed pkRoot message sig
    (C13Concrete.wordOfHash16 pkSeed)
    (C13Concrete.adrsXmssTree 1
      (((C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
    (sigDataOffset + (1952 + 868 * 1 + 692))
    d.lsig1.authPath
    (c13XmssAuthCdAt pkSeed pkRoot message sig
      (sigDataOffset + (1952 + 868 * 1 + 692)))
    (hWitness d)

/-- Layer-0 C13 `.ok` bounded per-step witness residual.  Mirrors
`C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer0` but threads the
bounded universal-witness premise; the dynamic per-call `idx < 11` and
`wordNormalize a.1 = a.1` inputs replace the broad
`C13AfterMerkleXmssFrameStepRuntimeBoundsAt` discharge the caller would
otherwise need. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692)))

/-- Layer-1 analogue of
`C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0`. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692)))

/-- The layer-0 `.ok` bounded step witness is unconditionally derivable from the
layer-site arithmetic: no broad `C13AfterMerkleXmssFrameStepRuntimeBoundsAt`,
`C13AfterMerkleXmssFrameStepHeightBoundsAt`, or `hParse` premises are required.
This is the actual layer-0 callee that replaces the broad runtime/height bounds
package at the `.ok` boundary. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0_holds
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer0
    pkSeed pkRoot message sig sigParsed d.lsig0.authPath

/-- Layer-1 analogue of
`c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0_holds`. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer1_holds
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer1
    pkSeed pkRoot message sig sigParsed d.lsig1.authPath

/-- Layer-0 raw step residual reduced to its exact-node per-step witness package. -/
theorem c13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer0_of_witness
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692)))) :
    C13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact c13AfterMerkleXmssRawStepPremiseAt_of_witness
    (C13Concrete.wordOfHash16 pkSeed)
    (C13Concrete.adrsXmssTree 0
      ((C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
    d.lsig0.authPath
    (c13XmssAuthCdAt pkSeed pkRoot message sig
      (sigDataOffset + (1952 + 868 * 0 + 692)))
    (hWitness d)

/-- Layer-1 raw step residual reduced to its exact-node per-step witness package. -/
theorem c13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer1_of_witness
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692)))) :
    C13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact c13AfterMerkleXmssRawStepPremiseAt_of_witness
    (C13Concrete.wordOfHash16 pkSeed)
    (C13Concrete.adrsXmssTree 1
      (((C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048))
    d.lsig1.authPath
    (c13XmssAuthCdAt pkSeed pkRoot message sig
      (sigDataOffset + (1952 + 868 * 1 + 692)))
    (hWitness d)

/-- Layer-0 raw initial residual reduced to the exact WOTS-start-node fact plus
the preexisting `beforeMerkle` `"mIdx"` site lemma. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel.intro ?_ ?_ ?_
  · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    exact c13FirstLayerBeforeMerkle_mIdx_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse
  · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    rw [beforeMerkle_merkleNode_eq_wotsPk]
    exact hWotsPk d
  · exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_wordOfHash16 d.wotsPk0

/-- Layer-1 raw initial residual reduced to the exact WOTS-start-node fact plus
the preexisting `beforeMerkle` `"mIdx"` site lemma. -/
theorem c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel.intro ?_ ?_ ?_
  · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    exact c13SecondLayerBeforeMerkle_mIdx_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse
  · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    rw [beforeMerkle_merkleNode_eq_wotsPk]
    exact hWotsPk d
  · exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_wordOfHash16 d.wotsPk1

/-- Layer-0 `beforeMerkle` still carries the public seed word in scratch cell
`0x00`; the WOTS and copy loops do not disturb that cell. -/
theorem c13FirstLayerBeforeMerkle_seed_slot_of_parse
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (_hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((SegmentLayer3.beforeMerkle
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  have hMem :
      ((SegmentLayer3.beforeMerkle
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((SegmentLayer3.afterDigit
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val := by
    exact SegmentLayer3.beforeMerkle_preserves_memory_zero_of_loop_frames
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      SegmentLayer3.wotsOuterForEach_preserves_memory_zero
      SegmentLayer3.copyForEach_preserves_memory_zero
  have hDigit :
      ((SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed := by
    rw [SegmentLayer3.afterDigit_preserves_memory_zero]
    exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig
  simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using hMem.trans hDigit

/-- Layer-1 `beforeMerkle` still carries the public seed word in scratch cell
`0x00`.  The seed is preserved by the first layer step and by the layer-1
WOTS/copy prefixes before the Merkle climb. -/
theorem c13SecondLayerBeforeMerkle_seed_slot_of_parse
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((SegmentLayer3.beforeMerkle
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  have hStepMem0 :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val := by
    simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using
      c13FirstLayerStep_preserves_memory_zero_of_parse
        pkSeed pkRoot message sig sigParsed hParse
  have hBeforeDigest :
      ((SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed :=
    c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig
      (c13FirstStepLayer_seed_slot_of_memory_zero
        pkSeed pkRoot message sig hStepMem0)
  have hMem :
      ((SegmentLayer3.beforeMerkle
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((SegmentLayer3.afterDigit
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val := by
    exact SegmentLayer3.beforeMerkle_preserves_memory_zero_of_loop_frames
      (c13SecondLayerGuardState pkSeed pkRoot message sig)
      SegmentLayer3.wotsOuterForEach_preserves_memory_zero
      SegmentLayer3.copyForEach_preserves_memory_zero
  have hDigit :
      ((SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed := by
    rw [SegmentLayer3.afterDigit_preserves_memory_zero]
    exact hBeforeDigest
  simpa [c13SecondLayerGuardState_eq_c13LayerLoopState1] using hMem.trans hDigit

/-- The layer-0 normalized initial frame follows from the exact raw initial
relation plus the already-proved frozen-site facts. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_raw
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hRaw : C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hSite :=
    c13FirstLayerBeforeMerkle_layerFrozenSite pkSeed pkRoot message sig sigParsed hParse
  rcases hSite with ⟨treeAdrs, hSel, hCd, hPtr, hTree, _hTreeLt, _hmIdxLt⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact (hRaw d).toRel
  · change lookupValue
        (bindValue
          (SegmentLayer3.beforeMerkle
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "h" (wordNormalize 0)) "treeAdrs" =
        C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048)
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "treeAdrs" _ (by decide)]
    have hTreeConcrete :
        lookupValue
            (SegmentLayer3.beforeMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "treeAdrs" =
          C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) := by
      simpa [pk, digest] using
        SegmentLayer3.beforeMerkle_treeAdrs_eq_of_layer_idxTree
          (c13FirstLayerGuardState pkSeed pkRoot message sig)
          0 digest.hyperIndex
          (c13FirstLayerGuardState_layer pkSeed pkRoot message sig)
          (c13FirstLayerGuardState_idxTree_hyperIndex
            pkSeed pkRoot message sig hParse)
          (by decide : 0 < 2 ^ 32)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
    simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using hTreeConcrete
  · change lookupValue
        (bindValue
          (SegmentLayer3.beforeMerkle
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "h" (wordNormalize 0)) "merklePtr" =
        sigDataOffset + (1952 + 868 * 0 + 692)
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merklePtr" _ (by decide)]
    simpa [pk, digest, c13FirstLayerGuardState_eq_c13LayerLoopState0] using hPtr
  · change ((SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed
    exact c13FirstLayerBeforeMerkle_seed_slot_of_parse
      pkSeed pkRoot message sig sigParsed hParse
  · change (SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).selector = 0
    simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using hSel
  · change (SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).world.calldata =
        headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
    simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using hCd

/-- The layer-1 normalized initial frame follows from the exact raw initial
relation plus the frozen-site facts.  The layer-1 seed slot remains an explicit
data premise, because proving it inline expands the layer-0 step preservation
proof too aggressively for this local adapter. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_raw
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hSeed :
      ((SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hRaw : C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hSite :=
    c13SecondLayerBeforeMerkle_layerFrozenSite pkSeed pkRoot message sig sigParsed hParse
  rcases hSite with ⟨treeAdrs, hSel, hCd, hPtr, hTree, _hTreeLt, _hmIdxLt⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact (hRaw d).toRel
  · change lookupValue
        (bindValue
          (SegmentLayer3.beforeMerkle
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "h" (wordNormalize 0)) "treeAdrs" =
        C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048)
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "treeAdrs" _ (by decide)]
    have hTreeConcrete :
        lookupValue
            (SegmentLayer3.beforeMerkle
              (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
            "treeAdrs" =
          C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048) := by
      simpa [pk, digest] using
        SegmentLayer3.beforeMerkle_treeAdrs_eq_of_layer_idxTree
          (c13SecondLayerGuardState pkSeed pkRoot message sig)
          1 (digest.hyperIndex / 2048)
          (c13SecondLayerGuardState_layer pkSeed pkRoot message sig)
          (c13SecondLayerGuardState_idxTree_hyperIndex
            pkSeed pkRoot message sig hParse)
          (by decide : 1 < 2 ^ 32)
          (lt_of_le_of_lt
            (Nat.div_le_self _ _)
            (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
    simpa [c13SecondLayerGuardState_eq_c13LayerLoopState1] using hTreeConcrete
  · change lookupValue
        (bindValue
          (SegmentLayer3.beforeMerkle
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "h" (wordNormalize 0)) "merklePtr" =
        sigDataOffset + (1952 + 868 * 1 + 692)
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merklePtr" _ (by decide)]
    simpa [pk, digest, c13SecondLayerGuardState_eq_c13LayerLoopState1] using hPtr
  · change ((SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed
    exact hSeed
  · change (SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).selector = 0
    simpa [c13SecondLayerGuardState_eq_c13LayerLoopState1] using hSel
  · change (SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).world.calldata =
        headWords pkSeed pkRoot message sig.size ++ bytesToWords sig
    simpa [c13SecondLayerGuardState_eq_c13LayerLoopState1] using hCd

/-- Layer-0 normalized initial residual reduced directly to the WOTS public-key
start-node fact. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_raw
    pkSeed pkRoot message sig sigParsed forsPk specRoot hParse
    (c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-1 normalized initial residual reduced directly to the WOTS public-key
start-node fact plus the layer-1 seed-slot fact. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hSeed :
      ((SegmentLayer3.beforeMerkle
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_raw
    pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hSeed
    (c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-1 normalized initial residual reduced directly to the WOTS public-key
start-node fact; the seed-slot premise is discharged locally from the parse
trace. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk_parse
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk
    pkSeed pkRoot message sig sigParsed forsPk specRoot hParse
    (c13SecondLayerBeforeMerkle_seed_slot_of_parse
      pkSeed pkRoot message sig sigParsed hParse)
    hWotsPk

/-- The layer-0 normalized residual is reduced to the exact per-step advance and
initial `beforeMerkle` frame facts. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0_of_step_and_initial
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hStep : C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hInit : C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hStep d, hInit d⟩

/-- The layer-1 normalized residual is reduced to the exact per-step advance and
initial `beforeMerkle` frame facts. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1_of_step_and_initial
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hStep : C13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hInit : C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hStep d, hInit d⟩

/-- The layer-0 raw residual is reduced to the exact per-step advance and
initial `beforeMerkle` raw facts. -/
theorem c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0_of_step_and_initial
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hStep : C13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hInit : C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hStep d, hInit d⟩

/-- The layer-1 raw residual is reduced to the exact per-step advance and
initial `beforeMerkle` raw facts. -/
theorem c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1_of_step_and_initial
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hStep : C13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hInit : C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hStep d, hInit d⟩

/-- Layer-0 normalized frame data from the exact per-step witness package and
the executable WOTS start-node fact. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0_of_witness_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hStepWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          (sigDataOffset + (1952 + 868 * 0 + 692))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0_of_step_and_initial
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer0_of_witness
      pkSeed pkRoot message sig sigParsed forsPk specRoot hStepWitness)
    (c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-1 normalized frame data from the exact per-step witness package and
the executable WOTS start-node fact. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1_of_witness_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hStepWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          (sigDataOffset + (1952 + 868 * 1 + 692))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1_of_step_and_initial
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleNormalizedXmssClimbFrameStepDataLayer1_of_witness
      pkSeed pkRoot message sig sigParsed forsPk specRoot hStepWitness)
    (c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk_parse
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-0 C13 `.ok` bounded frame residual: the bounded per-step witness
package threaded with the initial `beforeMerkle` frame.  Unlike
`C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0`, this carries the
bounded universal step (dynamic per-call `idx < 11` and `wordNormalize a.1 = a.1`
inputs), eliminating the broad `C13AfterMerkleXmssFrameStepRuntimeBoundsAt`
discharge from the caller. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692))) ∧
    C13AfterMerkleXmssInitialFramePremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0)

/-- Layer-1 analogue of
`C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0`. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692))) ∧
    C13AfterMerkleXmssInitialFramePremiseAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk1)

/-- Layer-0 bounded normalized residual reduced to the bounded per-step witness
and the initial `beforeMerkle` frame.  Bounded analogue of
`c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0_of_step_and_initial`. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_step_and_initial
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hStep : C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hInit : C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hStep d, hInit d⟩

/-- Layer-1 analogue of
`c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_step_and_initial`. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1_of_step_and_initial
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hStep : C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hInit : C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hStep d, hInit d⟩

/-- Layer-0 bounded normalized frame data directly from the executable WOTS
start-node fact: the broad step witness premise is internalised through the
proved bounded step holds.  No `C13AfterMerkleXmssFrameStepWitnessPremiseAt`
input is required at the caller boundary. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_step_and_initial
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0_holds
      pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-1 analogue of
`c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_wotsPk`. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1_of_step_and_initial
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer1_holds
      pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk_parse
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-0 raw frame data from the exact per-step witness package and the
executable WOTS start-node fact. -/
theorem c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0_of_witness_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hStepWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0_of_step_and_initial
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer0_of_witness
      pkSeed pkRoot message sig sigParsed forsPk specRoot hStepWitness)
    (c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- Layer-1 raw frame data from the exact per-step witness package and the
executable WOTS start-node fact. -/
theorem c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1_of_witness_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hStepWitness :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hWotsPk : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1_of_step_and_initial
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleRawXmssClimbFrameStepDataLayer1_of_witness
      pkSeed pkRoot message sig sigParsed forsPk specRoot hStepWitness)
    (c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk)

/-- C13 `.ok` model residual reduced to the smallest frame-threaded premises:
for each successful fold witness and each executable layer, provide the
per-step frame advance and initial `beforeMerkle` frame. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbFrameData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      pk digest forsPk sigParsed.layers specRoot,
    C13AfterMerkleXmssFramePremisesAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
      (sigDataOffset + (1952 + 868 * 0 + 692))
      d.lsig0.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 0 + 692)))
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk0) ∧
    C13AfterMerkleXmssFramePremisesAt pkSeed pkRoot message sig
      (C13Concrete.wordOfHash16 pkSeed)
      (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
      (sigDataOffset + (1952 + 868 * 1 + 692))
      d.lsig1.authPath
      (c13XmssAuthCdAt pkSeed pkRoot message sig
        (sigDataOffset + (1952 + 868 * 1 + 692)))
      (CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.wotsPk1)

/-- Both-layer bounded normalized frame-data package: the two bounded-witness
per-step residuals threaded with their initial `beforeMerkle` frames.  Carries
exactly the surface produced from the proved bounded step holds plus the
WOTS start-node facts, without the broad
`C13AfterMerkleXmssFrameStepWitnessPremiseAt` step input the existing
`C13FoldOkAfterMerkleNormalizedXmssClimbFrameData` requires. -/
def C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot ∧
  C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot

/-- Higher analog of
`c13FoldOkAfterMerkleNormalizedXmssClimbFrameData_of_layers`: combines the two
bounded layer residuals into the both-layer bounded frame-data package without
any broad step-witness premise. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData_of_layers
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hLayer0 : C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hLayer1 : C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  ⟨hLayer0, hLayer1⟩

/-- The bounded both-layer normalized frame-data package follows from just
`hParse` plus the layer-0/layer-1 WOTS start-node facts.  The broad step witness
inputs `hFrameStep0`/`hFrameStep1` that
`c13FoldOkAfterMerkleNormalizedXmssClimbData_of_step_witnesses_and_wotsPk`
demands are eliminated; the bounded step is supplied internally by the proved
`_holds` reducers. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk0 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hWotsPk1 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData_of_layers
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    (c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0)
    (c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk1)

/-- The separated layer-0/layer-1 frame residuals reconstitute the existing
combined normalized frame-data package. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbFrameData_of_layers
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hLayer0 : C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hLayer1 : C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbFrameData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  intro d
  exact ⟨hLayer0 d, hLayer1 d⟩

/-- The named frame-threaded `afterMerkle` theorem discharges the true normalized
model residual once the two C13 layer frame packages are supplied.  Auth-path
calldata ranges are discharged from the parsed signature and each successful
fold witness's layer membership facts. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbModelData_of_frame_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFrame : C13FoldOkAfterMerkleNormalizedXmssClimbFrameData
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbModelData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  constructor
  · intro d
    rcases hFrame d with ⟨hFrame0, _⟩
    rcases hFrame0 with ⟨hstep0, hR0⟩
    have hD0 :
        ∀ i, i < 11 →
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
      simpa [pk, c13XmssAuthCdAt] using
        SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
          pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
          (sigDataOffset + (1952 + 868 * 0 + 692))
          hParse (by decide : 0 < 2) d.hLayer0 rfl
    simpa [pk, digest] using
      SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame_c13
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        (sigDataOffset + (1952 + 868 * 0 + 692))
        d.lsig0.authPath
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 0 + 692)))
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk0)
        hstep0 hD0 hR0
  · intro d
    rcases hFrame d with ⟨_, hFrame1⟩
    rcases hFrame1 with ⟨hstep1, hR1⟩
    have hD1 :
        ∀ i, i < 11 →
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))) i := by
      simpa [pk, c13XmssAuthCdAt] using
        SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
          pkSeed pkRoot message sig c13 sigParsed d.lsig1 1
          (sigDataOffset + (1952 + 868 * 1 + 692))
          hParse (by decide : 1 < 2) d.hLayer1 rfl
    simpa [pk, digest] using
      SegmentAcceptSpec.afterMerkle_model_node_of_xmss_frame_c13
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
        (sigDataOffset + (1952 + 868 * 1 + 692))
        d.lsig1.authPath
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 1 + 692)))
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
        ((digest.hyperIndex / 2048) % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk1)
        hstep1 hD1 hR1

/-- Matching normalized-frame and raw-relation Merkle projections discharge the
C13 cell-normalization source package.  The remaining premises are explicitly
split by layer: normalized `MerkleClimbFrame` advance/initial-frame facts and
raw `MerkleClimbRawRel` advance/initial-relation facts for layer 0 and layer 1. -/
theorem c13FoldOkAfterMerkleCellNormalizedSourceData_of_frame_and_raw_layers
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hFrame0 : C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hFrame1 : C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRaw0 : C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRaw1 : C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleCellNormalizedSourceData
      pkSeed pkRoot message sig := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot sigParsed.layers
      (by simpa [pk, digest] using hFold)
  constructor
  · have hD0 :
        ∀ i, i < 11 →
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
      simpa [pk, c13XmssAuthCdAt] using
        SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
          pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
          (sigDataOffset + (1952 + 868 * 0 + 692))
          hParse (by decide : 0 < 2) d.hLayer0 rfl
    exact
      c13AfterMerkleCellNormalizedSourceData_of_frame_and_raw_premises_at
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        (sigDataOffset + (1952 + 868 * 0 + 692))
        d.lsig0.authPath
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 0 + 692)))
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk0)
        hD0
        (by simpa [pk, digest] using hFrame0 d)
        (by simpa [pk, digest] using hRaw0 d)
  · have hD1 :
        ∀ i, i < 11 →
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))) i := by
      simpa [pk, c13XmssAuthCdAt] using
        SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
          pkSeed pkRoot message sig c13 sigParsed d.lsig1 1
          (sigDataOffset + (1952 + 868 * 1 + 692))
          hParse (by decide : 1 < 2) d.hLayer1 rfl
    exact
      c13AfterMerkleCellNormalizedSourceData_of_frame_and_raw_premises_at
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
        (sigDataOffset + (1952 + 868 * 1 + 692))
        d.lsig1.authPath
        (c13XmssAuthCdAt pkSeed pkRoot message sig
          (sigDataOffset + (1952 + 868 * 1 + 692)))
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
        ((digest.hyperIndex / 2048) % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk1)
        hD1
        (by simpa [pk, digest] using hFrame1 d)
        (by simpa [pk, digest] using hRaw1 d)

/-- The split residuals reconstitute the previous normalized C13 `.ok`
after-Merkle package. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbData_of_model_and_cell_normalized
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hModel : C13FoldOkAfterMerkleNormalizedXmssClimbModelData
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hCell : C13FoldOkAfterMerkleCellNormalizedData
        pkSeed pkRoot message sig) :
    C13FoldOkAfterMerkleNormalizedXmssClimbData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  rcases hModel with ⟨hModel0, hModel1⟩
  rcases hCell with ⟨hCell0, hCell1⟩
  exact ⟨hModel0, hCell0, hModel1, hCell1⟩

/-- C13 `.ok` after-Merkle package from the exact residual surface left after
the per-step reducers: four executable step witness packages and the two WOTS
start-node facts. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbData_of_step_witnesses_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hFrameStep0 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          (sigDataOffset + (1952 + 868 * 0 + 692))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hFrameStep1 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          (sigDataOffset + (1952 + 868 * 1 + 692))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hRawStep0 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hRawStep1 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hWotsPk0 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hWotsPk1 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  have hFrame0 :
      C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer0_of_witness_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFrameStep0 hWotsPk0
  have hFrame1 :
      C13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbFrameDataLayer1_of_witness_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFrameStep1 hWotsPk1
  have hRaw0 :
      C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer0_of_witness_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hRawStep0 hWotsPk0
  have hRaw1 :
      C13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleRawXmssClimbFrameDataLayer1_of_witness_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hRawStep1 hWotsPk1
  have hFrame :
      C13FoldOkAfterMerkleNormalizedXmssClimbFrameData
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbFrameData_of_layers
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFrame0 hFrame1
  have hModel :
      C13FoldOkAfterMerkleNormalizedXmssClimbModelData
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbModelData_of_frame_data
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hFrame
  have hCellSource :
      C13FoldOkAfterMerkleCellNormalizedSourceData
        pkSeed pkRoot message sig :=
    c13FoldOkAfterMerkleCellNormalizedSourceData_of_frame_and_raw_layers
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hFold
      hFrame0 hFrame1 hRaw0 hRaw1
  exact
    c13FoldOkAfterMerkleNormalizedXmssClimbData_of_model_and_cell_normalized
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hModel
      (c13FoldOkAfterMerkleCellNormalizedData_of_source_data
        pkSeed pkRoot message sig hCellSource)

/-- C13 `.ok` normalized model data from just the executable WOTS start-node
facts and parsing.  No broad `hFrameStep0`/`hFrameStep1` step-witness premise
is required: the bounded local model lift
`c13AfterMerkleNormalizedXmssClimb_of_layer_site_bounded` produces each layer's
`wordNormalize`-of-`afterMerkle`-equals-`xmssClimb` equality from the bounded
step invariant threaded through `foldLoop_invariant_cond`. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbModelData_of_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hWotsPk0 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hWotsPk1 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbModelData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hInit0 :
      C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hInit1 :
      C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk_parse
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk1
  refine ⟨?_, ?_⟩
  · intro d
    have hD0 :
        ∀ i, i < 11 →
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
      simpa [pk, c13XmssAuthCdAt] using
        SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
          pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
          (sigDataOffset + (1952 + 868 * 0 + 692))
          hParse (by decide : 0 < 2) d.hLayer0 rfl
    have hTreeLt0 :
        C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) < 2 ^ 256 :=
      c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
        (by decide : 0 < 2 ^ 32)
        (lt_of_le_of_lt (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
    have hMIdxNorm0 : wordNormalize (digest.hyperIndex % 2048) = digest.hyperIndex % 2048 :=
      wordNormalize_mod_2048 digest.hyperIndex
    simpa [pk, digest] using
      c13AfterMerkleNormalizedXmssClimb_of_layer_site_bounded
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        0 d.lsig0.authPath
        (by decide : 0 < 2) hTreeLt0
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk0)
        hD0
        (by simpa [pk, digest] using hInit0 d)
        hMIdxNorm0
  · intro d
    have hD1 :
        ∀ i, i < 11 →
          SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))) i := by
      simpa [pk, c13XmssAuthCdAt] using
        SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
          pkSeed pkRoot message sig c13 sigParsed d.lsig1 1
          (sigDataOffset + (1952 + 868 * 1 + 692))
          hParse (by decide : 1 < 2) d.hLayer1 rfl
    have hTreeLt1 :
        C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048) < 2 ^ 256 :=
      c13_adrsXmssTree_lt_of_bounds 1 ((digest.hyperIndex / 2048) / 2048)
        (by decide : 1 < 2 ^ 32)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (lt_of_le_of_lt
            (Nat.div_le_self _ _)
            (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)))
    have hMIdxNorm1 :
        wordNormalize ((digest.hyperIndex / 2048) % 2048) =
          (digest.hyperIndex / 2048) % 2048 :=
      wordNormalize_mod_2048 (digest.hyperIndex / 2048)
    simpa [pk, digest] using
      c13AfterMerkleNormalizedXmssClimb_of_layer_site_bounded
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
        1 d.lsig1.authPath
        (by decide : 1 < 2) hTreeLt1
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))
        ((digest.hyperIndex / 2048) % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk1)
        hD1
        (by simpa [pk, digest] using hInit1 d)
        hMIdxNorm1

/-- C13 `.ok` after-Merkle package from the bounded model side (internally
discharged) plus the broad exact-raw step witnesses and the WOTS start-node
facts.  Bounded analog of
`c13FoldOkAfterMerkleNormalizedXmssClimbData_of_step_witnesses_and_wotsPk`:
the layer-0/layer-1 normalized step witness premises `hFrameStep0`/`hFrameStep1`
are eliminated.  Only the raw-relation step witnesses and the WOTS start-node
facts remain as caller surface. -/
theorem c13FoldOkAfterMerkleNormalizedXmssClimbData_of_raw_step_witnesses_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hWotsPk0 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hWotsPk1 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleNormalizedXmssClimbData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  have hModel :
      C13FoldOkAfterMerkleNormalizedXmssClimbModelData
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbModelData_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hWotsPk0 hWotsPk1
  have hFrameInit0 :
      C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hFrameInit1 :
      C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer1_of_wotsPk_parse
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk1
  have hRawInit0 :
      C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hRawInit1 :
      C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer1_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk1
  -- Build cell-normalized source data directly from the bounded model equality
  -- and the raw equality, without going through the universal frame step.
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let d :=
    C13Concrete.foldHypertree_c13_ok_two_layer_data
      pk digest forsPk specRoot sigParsed.layers
      (by simpa [pk, digest] using hFold)
  have hCellSource :
      C13FoldOkAfterMerkleCellNormalizedSourceData
        pkSeed pkRoot message sig := by
    refine ⟨?_, ?_⟩
    · have hD0 :
          ∀ i, i < 11 →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              d.lsig0.authPath
              (c13XmssAuthCdAt pkSeed pkRoot message sig
                (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
        simpa [pk, c13XmssAuthCdAt] using
          SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
            pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
            (sigDataOffset + (1952 + 868 * 0 + 692))
            hParse (by decide : 0 < 2) d.hLayer0 rfl
      refine ⟨C13Concrete.wordOfHash16 pkSeed,
              C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048),
              digest.hyperIndex % 2048,
              C13Concrete.wordOfHash16 d.wotsPk0,
              d.lsig0.authPath, ?_, ?_⟩
      · exact hModel.1 d
      · have hTreeLt0 :
            C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) < 2 ^ 256 :=
          c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
            (by decide : 0 < 2 ^ 32)
            (lt_of_le_of_lt (Nat.div_le_self _ _)
              (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
        have hMIdxNorm0 :
            wordNormalize (digest.hyperIndex % 2048) =
              digest.hyperIndex % 2048 :=
          wordNormalize_mod_2048 digest.hyperIndex
        simpa [pk, digest] using
          c13AfterMerkleRawXmssClimb_of_layer_site_bounded
            pkSeed pkRoot message sig
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            0 d.lsig0.authPath (by decide : 0 < 2) hTreeLt0
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))
            (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0)
            hD0
            (by simpa [pk, digest] using hFrameInit0 d)
            (by simpa [pk, digest] using hRawInit0 d)
            hMIdxNorm0
    · have hD1 :
          ∀ i, i < 11 →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              d.lsig1.authPath
              (c13XmssAuthCdAt pkSeed pkRoot message sig
                (sigDataOffset + (1952 + 868 * 1 + 692))) i := by
        simpa [pk, c13XmssAuthCdAt] using
          SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
            pkSeed pkRoot message sig c13 sigParsed d.lsig1 1
            (sigDataOffset + (1952 + 868 * 1 + 692))
            hParse (by decide : 1 < 2) d.hLayer1 rfl
      refine ⟨C13Concrete.wordOfHash16 pkSeed,
              C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048),
              (digest.hyperIndex / 2048) % 2048,
              C13Concrete.wordOfHash16 d.wotsPk1,
              d.lsig1.authPath, ?_, ?_⟩
      · exact hModel.2 d
      · have hTreeLt1 :
            C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048) < 2 ^ 256 :=
          c13_adrsXmssTree_lt_of_bounds 1 ((digest.hyperIndex / 2048) / 2048)
            (by decide : 1 < 2 ^ 32)
            (lt_of_le_of_lt
              (Nat.div_le_self _ _)
              (lt_of_le_of_lt
                (Nat.div_le_self _ _)
                (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)))
        have hMIdxNorm1 :
            wordNormalize ((digest.hyperIndex / 2048) % 2048) =
              (digest.hyperIndex / 2048) % 2048 :=
          wordNormalize_mod_2048 (digest.hyperIndex / 2048)
        simpa [pk, digest] using
          c13AfterMerkleRawXmssClimb_of_layer_site_bounded
            pkSeed pkRoot message sig
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            1 d.lsig1.authPath (by decide : 1 < 2) hTreeLt1
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))
            ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk1)
            hD1
            (by simpa [pk, digest] using hFrameInit1 d)
            (by simpa [pk, digest] using hRawInit1 d)
            hMIdxNorm1
  exact
    c13FoldOkAfterMerkleNormalizedXmssClimbData_of_model_and_cell_normalized
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hModel
      (c13FoldOkAfterMerkleCellNormalizedData_of_source_data
        pkSeed pkRoot message sig hCellSource)

/-- A normalized after-Merkle climb package implies the exact raw package by
rewriting each raw cell through its supplied `wordNormalize` identity. -/
theorem c13FoldOkAfterMerkleRawXmssClimbData_of_normalized
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hNorm : C13FoldOkAfterMerkleNormalizedXmssClimbData
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkAfterMerkleRawXmssClimbData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  rcases hNorm with ⟨hModel0, hCell0, hModel1, hCell1⟩
  constructor
  · intro d
    rw [← hCell0]
    exact hModel0 d
  · intro d
    rw [← hCell1]
    exact hModel1 d

/-- Packaged `.ok` bridge from the normalized frame-threaded after-Merkle
residual. -/
theorem c13FoldOkDigitMerkleData_of_afterMerkle_normalized_xmssClimb_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hNorm : C13FoldOkAfterMerkleNormalizedXmssClimbData
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  rcases c13FoldOkAfterMerkleRawXmssClimbData_of_normalized
      pkSeed pkRoot message sig sigParsed forsPk specRoot hNorm with
    ⟨hAfter0, hAfter1⟩
  exact
    c13FoldOkDigitMerkleData_of_afterMerkle_raw_xmssClimbs
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold hAfter0 hAfter1

/-- `.ok` digit/Merkle data from the exact after-Merkle residual surface: four
step witness packages and the two WOTS start-node facts. -/
theorem c13FoldOkDigitMerkleData_of_afterMerkle_step_witnesses_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hFrameStep0 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          (sigDataOffset + (1952 + 868 * 0 + 692))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hFrameStep1 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssFrameStepWitnessPremiseAt pkSeed pkRoot message sig
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          (sigDataOffset + (1952 + 868 * 1 + 692))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hRawStep0 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hRawStep1 :
      let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
      let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
      ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
          pk digest forsPk sigParsed.layers specRoot,
        C13AfterMerkleXmssRawStepWitnessPremiseAt
          (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
          d.lsig1.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hWotsPk0 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hWotsPk1 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkDigitMerkleData_of_afterMerkle_normalized_xmssClimb_data
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
    (c13FoldOkAfterMerkleNormalizedXmssClimbData_of_step_witnesses_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold
      hFrameStep0 hFrameStep1 hRawStep0 hRawStep1 hWotsPk0 hWotsPk1)

/-- Bounded analog of
`c13FoldOkDigitMerkleData_of_afterMerkle_step_witnesses_and_wotsPk`.  The broad
`hFrameStep0`/`hFrameStep1` step-witness premises are eliminated: the normalized
after-Merkle climb data is built internally by
`c13FoldOkAfterMerkleNormalizedXmssClimbData_of_raw_step_witnesses_and_wotsPk`,
which threads the bounded step preservation through the climb loop.  The
exact-raw step witnesses and WOTS start-node facts remain as caller surface. -/
theorem c13FoldOkDigitMerkleData_of_afterMerkle_raw_step_witnesses_and_wotsPk
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hWotsPk0 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hWotsPk1 : C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  c13FoldOkDigitMerkleData_of_afterMerkle_normalized_xmssClimb_data
    pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
    (c13FoldOkAfterMerkleNormalizedXmssClimbData_of_raw_step_witnesses_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hFold hWotsPk0 hWotsPk1)

/-- Packaged form of
`c13FoldOkDigitMerkleData_of_afterMerkle_raw_xmssClimbs`.  Callers now discharge
one named residual, `C13FoldOkAfterMerkleRawXmssClimbData`, rather than carrying
the two full exact binding equalities inline. -/
theorem c13FoldOkDigitMerkleData_of_afterMerkle_raw_xmssClimb_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hAfter : C13FoldOkAfterMerkleRawXmssClimbData
        pkSeed pkRoot message sig sigParsed forsPk specRoot) :
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  rcases hAfter with ⟨hAfter0, hAfter1⟩
  exact
    c13FoldOkDigitMerkleData_of_afterMerkle_raw_xmssClimbs
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold
      (by
        intro d
        exact hAfter0 d)
      (by
        intro d
        exact hAfter1 d)

/-- Convert the bounded accept-side two-step current-node observation package
into the exact successful C13 fold data consumed by the word-comparison bridge
boundary.  The package's legacy `pkRoot.size = 16` field is intentionally unused:
the final comparison is discharged from the C13 `specRoot` roundtrip instead. -/
theorem c13FoldOkCurrentNodeWordcmpData_of_two_step_obligations
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldOkCurrentNodeWordcmpData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let specStep := SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
  rcases hObs.hSuccessCurrent0 with
    ⟨lsig0, wotsPk0, root0, hLayer0, hGrinding0, hWots0, hXmss0, hCurrent0⟩
  rcases hObs.hSuccessCurrent1 with
    ⟨lsig1, wotsPk1, root1, hLayer1, hGrinding1, hWots1, hXmss1, hCurrent1⟩
  have hStep0Eq : specStep 0 forsPk = root0 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 0 forsPk wotsPk0 root0 lsig0 hLayer0
      (by simpa [pk, digest, specStep] using hGrinding0)
      (by simpa [pk, digest, specStep] using hWots0)
      (by simpa [pk, digest, specStep] using hXmss0)
  have hStep1Eq : specStep 1 (specStep 0 forsPk) = root1 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 1 (specStep 0 forsPk) wotsPk1 root1 lsig1 hLayer1
      (by simpa [pk, digest, specStep] using hGrinding1)
      (by simpa [pk, digest, specStep] using hWots1)
      (by simpa [pk, digest, specStep] using hXmss1)
  have hTwo : wordNormalize 2 = 2 :=
    SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256)
  have hSpecFold :
      ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot := by
    simpa [pk, digest, specStep] using
      SegmentAcceptSpec.specFold_c13HypertreeSpecStepAtLayer_eq_of_foldHypertree_ok
        pk digest forsPk specRoot sigParsed.layers hFold
  have hStep1Root0 : specStep 1 root0 = root1 := by
    simpa [hStep0Eq] using hStep1Eq
  have hRoot1 : root1 = specRoot := by
    simpa [ClimbLoop.specFold, hTwo, hStep0Eq, hStep1Root0] using hSpecFold
  apply
    c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
  · exact hObs.hGuard0
  · change
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode" = C13Concrete.wordOfHash16 (specStep 0 forsPk)
    rw [hStep0Eq]
    simpa [pk, digest, specStep, CurrentNodeFrame.c13LayerLoopState0,
      CurrentNodeFrame.c13LayerStartState] using hCurrent0
  · exact hObs.hGuard1
  · rw [← hRoot1]
    simpa [pk, digest, specStep, CurrentNodeFrame.c13LayerLoopState1,
      CurrentNodeFrame.c13LayerAfterStep0, hStep0Eq] using hCurrent1

/-- Remaining concrete guard data needed for the C13 `.reverted` fold branch. -/
def C13FoldRevertedGuardData
    (pkSeed pkRoot message sig : Bytes) : Prop :=
  SegmentLayer3.layerGuard
      (c13FirstLayerGuardState pkSeed pkRoot message sig) = false ∨
  (SegmentLayer3.layerGuard
      (c13FirstLayerGuardState pkSeed pkRoot message sig) = true ∧
    SegmentLayer3.layerGuard
      (c13SecondLayerGuardState pkSeed pkRoot message sig) = false)

/-- Reverted-branch executable checksum data.  These are the concrete layer facts
needed to turn the spec-side C13 grinding failure exposed by
`foldHypertree ... = .reverted` into the executable layer guard failure. -/
def C13FoldRevertedDigitSumData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer0Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterDigit
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 0
              (digest.hyperIndex / 2048)
              (digest.hyperIndex % 2048)
              d.lsig0.wots.count
              (C13Concrete.wordOfHash16 forsPk))) ∧
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterDigit
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 0
              (digest.hyperIndex / 2048)
              (digest.hyperIndex % 2048)
              d.lsig0.wots.count
              (C13Concrete.wordOfHash16 forsPk)) ∧
      lookupValue
          (SegmentLayer3.afterDigit
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 1
              ((digest.hyperIndex / 2048) / 2048)
              ((digest.hyperIndex / 2048) % 2048)
              d.lsig1.wots.count
              (C13Concrete.wordOfHash16 d.root0)))

/-- Reverted-branch pre-checksum digest data.  This is the remaining
straight-line obligation before the executable 43-step checksum fold can be
reduced to `C13Concrete.wotsDigitSum`. -/
def C13FoldRevertedBeforeDigitData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer0Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048)
            (digest.hyperIndex % 2048)
            d.lsig0.wots.count
            (C13Concrete.wordOfHash16 forsPk)) ∧
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048)
            (digest.hyperIndex % 2048)
            d.lsig0.wots.count
            (C13Concrete.wordOfHash16 forsPk) ∧
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            d.lsig1.wots.count
            (C13Concrete.wordOfHash16 d.root0))

/-- Reverted-branch WOTS digest scratch data.  These are the four words consumed
by `keccak256(0x00, 0x80)` immediately before the executable prefix binds
`"d"`: seed, WOTS hash address, current node, and WOTS count. -/
def C13FoldRevertedDigestScratchData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer0Data
      pk digest forsPk sigParsed.layers,
      let st := SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
      (st.world.memory 0x20).val =
        C13Concrete.adrsWotsHashBase 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048) ∧
      (st.world.memory 0x40).val = C13Concrete.wordOfHash16 forsPk ∧
      (st.world.memory 0x60).val = d.lsig0.wots.count) ∧
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
      let st0 := SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
      let st1 := SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
      (st0.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
      (st0.world.memory 0x20).val =
        C13Concrete.adrsWotsHashBase 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048) ∧
      (st0.world.memory 0x40).val = C13Concrete.wordOfHash16 forsPk ∧
      (st0.world.memory 0x60).val = d.lsig0.wots.count ∧
      (st1.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
      (st1.world.memory 0x20).val =
        C13Concrete.adrsWotsHashBase 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) ∧
      (st1.world.memory 0x40).val = C13Concrete.wordOfHash16 d.root0 ∧
      (st1.world.memory 0x60).val = d.lsig1.wots.count)

/-- Package the proved C13 pre-digest scratch-cell facts into the full reverted
digest-scratch data shape, leaving only the genuinely semantic layer-threading
facts as hypotheses.  This concentrates the remaining universal proof work:
FORS compression must identify layer 0's current node, and layer 1 still needs
seed/current-node threading from the first accepted layer. -/
theorem c13FoldRevertedDigestScratchData_of_layer_facts
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFirstStepMem :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "currentNode" =
        C13Concrete.wordOfHash16
          (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.layers 0 forsPk)) :
    C13FoldRevertedDigestScratchData
      pkSeed pkRoot message sig sigParsed forsPk := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPk :=
    c13AfterFinalize_forsPk_of_parse_fors
      pkSeed pkRoot message sig sigParsed forsPk hParse hFors
  have hSecondCurrent :=
    c13SecondLayerGuardState_currentNode_of_first_step_reverted_layer1
      pkSeed pkRoot message sig sigParsed forsPk hCurrent0
  have hSecondSeed :=
    c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig
      (c13FirstStepLayer_seed_slot_of_memory_zero
        pkSeed pkRoot message sig hFirstStepMem)
  refine ⟨?_, ?_⟩
  · intro d
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig
    · exact c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse
    · exact c13FirstLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig forsPk hForsPk
    · exact c13FirstLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig0 hParse d.hLayer0
  · intro d
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig
    · exact c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse
    · exact c13FirstLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig forsPk hForsPk
    · exact c13FirstLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig0 hParse d.hLayer0
    · exact hSecondSeed
    · exact c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse
    · exact c13SecondLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig d.root0 (hSecondCurrent d)
    · exact c13SecondLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig1 hParse d.hLayer1

/-- Variant of `c13FoldRevertedDigestScratchData_of_layer_facts` that replaces
the broad first-step `"currentNode"` correspondence with the smaller raw
layer-0 `afterMerkle` XMSS-climb equality needed only for the reverted-at-layer-1
case.  The layer-0 reverted scratch branch remains proved from the parse/FORS
facts alone. -/
theorem c13FoldRevertedDigestScratchData_of_layer1_afterMerkle_raw_xmssClimb
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFirstStepMem :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val)
    (hAfter :
      ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers,
        lookupValue
            (SegmentLayer3.afterMerkle
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "merkleNode" =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
            11 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    C13FoldRevertedDigestScratchData
      pkSeed pkRoot message sig sigParsed forsPk := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hForsPk :=
    c13AfterFinalize_forsPk_of_parse_fors
      pkSeed pkRoot message sig sigParsed forsPk hParse hFors
  have hSecondCurrent :=
    c13SecondLayerGuardState_currentNode_of_reverted_layer1_afterMerkle_raw_xmssClimb
      pkSeed pkRoot message sig sigParsed forsPk hAfter
  have hSecondSeed :=
    c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig
      (c13FirstStepLayer_seed_slot_of_memory_zero
        pkSeed pkRoot message sig hFirstStepMem)
  refine ⟨?_, ?_⟩
  · intro d
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig
    · exact c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse
    · exact c13FirstLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig forsPk hForsPk
    · exact c13FirstLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig0 hParse d.hLayer0
  · intro d
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig
    · exact c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse
    · exact c13FirstLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig forsPk hForsPk
    · exact c13FirstLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig0 hParse d.hLayer0
    · exact hSecondSeed
    · exact c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed hParse
    · exact c13SecondLayerBeforeDigest_currentNode_slot
        pkSeed pkRoot message sig d.root0 (hSecondCurrent d)
    · exact c13SecondLayerBeforeDigest_count_slot_hyperIndex
        pkSeed pkRoot message sig sigParsed d.lsig1 hParse d.hLayer1

/-- The generic Layer-3 pre-digest theorem turns concrete scratch-cell data into
the `"d" = C13Concrete.wotsDigest ...` facts required by the checksum reducer. -/
theorem c13FoldRevertedBeforeDigitData_of_digest_scratch_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hScratch : C13FoldRevertedDigestScratchData
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  refine ⟨?_, ?_⟩
  · intro d
    rcases hScratch.1 d with ⟨hSeed, hAdrs, hNode, hCount⟩
    exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wordOfHash16 pkSeed) 0
      (digest.hyperIndex / 2048)
      (digest.hyperIndex % 2048)
      d.lsig0.wots.count
      (C13Concrete.wordOfHash16 forsPk)
      hSeed hAdrs hNode hCount
  · intro d
    rcases hScratch.2 d with
      ⟨hSeed0, hAdrs0, hNode0, hCount0, hSeed1, hAdrs1, hNode1, hCount1⟩
    constructor
    · exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk)
        hSeed0 hAdrs0 hNode0 hCount0
    · exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wordOfHash16 pkSeed) 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count
        (C13Concrete.wordOfHash16 d.root0)
        hSeed1 hAdrs1 hNode1 hCount1

/-- The executable checksum fold computes exactly the spec-side WOTS+C digit
sum once the straight-line prefix has bound `"d"` to the layer digest. -/
theorem c13FoldRevertedDigitSumData_of_before_digit_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hBefore : C13FoldRevertedBeforeDigitData
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedDigitSumData pkSeed pkRoot message sig sigParsed forsPk := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  refine ⟨?_, ?_⟩
  · intro d
    exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wotsDigest
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk))
      (by simpa [pk, digest] using hBefore.1 d)
      (c13_wotsDigest_lt
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk))
  · intro d
    constructor
    · exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wotsDigest
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048)
          d.lsig0.wots.count
          (C13Concrete.wordOfHash16 forsPk))
        (by simpa [pk, digest] using (hBefore.2 d).1)
        (c13_wotsDigest_lt
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048)
          d.lsig0.wots.count
          (C13Concrete.wordOfHash16 forsPk))
    · exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wotsDigest
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          d.lsig1.wots.count
          (C13Concrete.wordOfHash16 d.root0))
        (by simpa [pk, digest] using (hBefore.2 d).2)
        (c13_wotsDigest_lt
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          d.lsig1.wots.count
          (C13Concrete.wordOfHash16 d.root0))

/-- A C13 spec-side `.reverted` fold plus executable checksum correspondence is
enough to produce the raw guard-failure data consumed by the existing revert
bridges. -/
theorem c13FoldRevertedGuardData_of_digit_sum_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted)
    (hDigit : C13FoldRevertedDigitSumData
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedGuardData pkSeed pkRoot message sig := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  cases C13Concrete.foldHypertree_c13_reverted_two_layer_data
      pk digest forsPk sigParsed.layers (by simpa [pk, digest] using hFold) with
  | layer0 d =>
      have hNe :
          C13Concrete.wotsDigitSum
              (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed) 0
                (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk)) ≠ 208 :=
        C13Concrete.wotsDigitSum_ne_of_wotsGrindingFailsC13AtLayer_true
          (layer := 0) (pk := pk)
          (treeIdx := digest.hyperIndex / 2048)
          (leafIdx := digest.hyperIndex % 2048)
          (node := forsPk) (wots := d.lsig0.wots)
          d.hGrinding0
      have hExecNe :
          lookupValue
              (SegmentLayer3.afterDigit
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "digitSum" ≠ 208 := by
        rw [hDigit.1 d]
        simpa [pk, digest] using hNe
      exact Or.inl
        (SegmentLayer3.layerGuard_of_afterDigit_digitSum_ne
          (c13FirstLayerGuardState pkSeed pkRoot message sig) hExecNe)
  | layer1 d =>
      have hSum0 :
          C13Concrete.wotsDigitSum
              (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed) 0
                (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk)) = 208 := by
        exact C13Concrete.wotsDigitSum_eq_of_wotsGrindingFailsC13AtLayer_false
          (layer := 0) (pk := pk)
          (treeIdx := digest.hyperIndex / 2048)
          (leafIdx := digest.hyperIndex % 2048)
          (node := forsPk) (wots := d.lsig0.wots)
          d.hGrinding0
      have hExecEq0 :
          lookupValue
              (SegmentLayer3.afterDigit
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "digitSum" = 208 := by
        rw [(hDigit.2 d).1]
        simpa [pk, digest] using hSum0
      have hGuard0 :
          SegmentLayer3.layerGuard
            (c13FirstLayerGuardState pkSeed pkRoot message sig) = true :=
        SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq
          (c13FirstLayerGuardState pkSeed pkRoot message sig) hExecEq0
      have hNe1 :
          C13Concrete.wotsDigitSum
              (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed) 1
                ((digest.hyperIndex / 2048) / 2048)
                ((digest.hyperIndex / 2048) % 2048)
                d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0)) ≠ 208 :=
        C13Concrete.wotsDigitSum_ne_of_wotsGrindingFailsC13AtLayer_true
          (layer := 1) (pk := pk)
          (treeIdx := (digest.hyperIndex / 2048) / 2048)
          (leafIdx := (digest.hyperIndex / 2048) % 2048)
          (node := d.root0) (wots := d.lsig1.wots)
          d.hGrinding1
      have hExecNe1 :
          lookupValue
              (SegmentLayer3.afterDigit
                (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
              "digitSum" ≠ 208 := by
        rw [(hDigit.2 d).2]
        simpa [pk, digest] using hNe1
      exact Or.inr ⟨hGuard0,
        SegmentLayer3.layerGuard_of_afterDigit_digitSum_ne
          (c13SecondLayerGuardState pkSeed pkRoot message sig) hExecNe1⟩

/-- C13 bridge reducer at the current concrete data boundary.  The proved
bad-length, forced-zero-false, FORS-totality, and no-`.rejected` facts are
discharged internally.  The remaining assumptions are exactly the concrete data
facts needed by the existing `.ok` and `.reverted` body bridges. -/
theorem c13_refines_byte_spec_of_current_node_and_reverted_guard_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedGuardData pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_fold_result_cover
  · intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
    rcases hOkData pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold with
      ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, hWordCmp⟩
    exact
      C13BridgePrep.runC13BodyObserved_accept_from_fold_ok_current_nodes_wordcmp
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold hGuard0 hCurrent0 hGuard1 hCurrent1 hWordCmp
  · intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
    have hg3 :
        SegmentS3.s3Guard
          (SegmentCompose.afterS2 (mkC13State pkSeed pkRoot message sig)) = 0 :=
      SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero
        pkSeed pkRoot message sig
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed rfl hParse hZero
    cases hRevertedData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold with
    | inl hFirst =>
        exact
          C13BridgePrep.runC13BodyObserved_revert_on_layer_first_guard_of_fold_reverted
            pkSeed pkRoot message sig sigParsed forsPk
            hParse hg3 (by simpa [c13FirstLayerGuardState] using hFirst)
            hZero hFors hFold
    | inr hSecond =>
        rcases hSecond with ⟨hGuard0, hGuard1⟩
        exact
          C13BridgePrep.runC13BodyObserved_revert_on_layer_second_guard_of_fold_reverted
            pkSeed pkRoot message sig sigParsed forsPk
            hParse hg3
            (by simpa [c13FirstLayerGuardState] using hGuard0)
            (by simpa [c13SecondLayerGuardState, c13FirstLayerGuardState] using hGuard1)
            hZero hFors hFold

/-- C13 bridge reducer with the accept branch left at the exact executable
word-comparison boundary, while the reverted branch is reduced from raw guard
facts to digit-sum correspondence facts.  This is the public-key-shape-free
counterpart of
`c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover`.
-/
theorem c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digit_sum_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigitSumData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_and_reverted_guard_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedGuardData_of_digit_sum_data
      pkSeed pkRoot message sig sigParsed forsPk hFold
      (hRevertedDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer with the final comparison reduced to the byte-shape fact
`pkRoot.size = 16`.  This is the strongest currently useful no-axiom reducer:
all C13 branch splitting is internal, and the remaining `.ok` branch data is
guard/current-node correspondence plus the public-key-root width. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_guard_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedGuardData pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_and_reverted_guard_cover ?_ hRevertedData
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  rcases hOkData pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold with
    ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, hPkRootSize⟩
  refine ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, ?_⟩
  exact
    SegmentAcceptSpec.wordCmp_of_wordOfHash16_rootMatchesPk_c13 specRoot pkRoot
      (SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold hFors hFold)

/-- C13 bridge reducer with the reverted branch reduced from raw guard-failure
facts to executable checksum correspondence facts. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigitSumData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_guard_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedGuardData_of_digit_sum_data
      pkSeed pkRoot message sig sigParsed forsPk hFold
      (hRevertedDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer after the executable checksum loop has been discharged:
callers now provide only the straight-line `"d"` digest bindings before the
43-iteration checksum fold. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_before_digit_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedBeforeDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedDigitSumData_of_before_digit_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer at the corrected final-comparison boundary after the
executable checksum loop has been discharged: callers provide only the
straight-line `"d"` digest bindings before the 43-iteration checksum fold. -/
theorem c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_before_digit_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedBeforeDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digit_sum_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedDigitSumData_of_before_digit_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer after the executable checksum and pre-digest binding have
been discharged: callers provide only the four WOTS digest scratch words for
each reverting layer. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digest_scratch_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedScratchData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_before_digit_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedBeforeDigitData_of_digest_scratch_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedScratchData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer at the corrected final-comparison boundary after the
executable checksum and pre-digest binding have been discharged: callers provide
only the four WOTS digest scratch words for each reverting layer. -/
theorem c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedScratchData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_before_digit_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedBeforeDigitData_of_digest_scratch_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedScratchData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer at the concrete two-layer current-node boundary, with the
final comparison discharged by the C13 word-roundtrip rather than by any
public-key-root byte-size premise.  The accept branch asks only for the two
guards and post-step `"currentNode"` facts that the concrete C13 loop actually
executes. -/
theorem c13_refines_byte_spec_of_current_node_facts_and_reverted_digest_scratch_cover
    (hOkFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        SegmentLayer3.layerGuard
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig)) = true ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "currentNode"
          =
            C13Concrete.wordOfHash16
              (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.layers 0 forsPk) ∧
        SegmentLayer3.layerGuard
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig)) = true ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "currentNode"
          = C13Concrete.wordOfHash16 specRoot)
    (hRevertedScratchData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
      ?_ hRevertedScratchData
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  rcases hOkFacts pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold with
    ⟨hGuard0, hCurrent0, hGuard1, hCurrent1⟩
  exact
    c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
      hGuard0 hCurrent0 hGuard1 hCurrent1

/-- C13 bridge reducer with both branches at concrete layer facts.  The accept
branch uses the two guards and two post-step `"currentNode"` facts.  The reverted
branch only asks for the first layer's seed-cell preservation and current-node
identification; `c13FoldRevertedDigestScratchData_of_layer_facts` packages those
into the WOTS digest scratch data required by the lower reducer. -/
theorem c13_refines_byte_spec_of_current_node_facts_and_reverted_layer_facts_cover
    (hOkFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        SegmentLayer3.layerGuard
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig)) = true ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "currentNode"
          =
            C13Concrete.wordOfHash16
              (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.layers 0 forsPk) ∧
        SegmentLayer3.layerGuard
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig)) = true ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "currentNode"
          = C13Concrete.wordOfHash16 specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_facts_and_reverted_digest_scratch_cover
      hOkFacts ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  rcases hRevertedLayerFacts pkSeed pkRoot message sig sigParsed forsPk
      hParse hZero hFors hFold with
    ⟨hFirstStepMem, hCurrent0⟩
  exact
    c13FoldRevertedDigestScratchData_of_layer_facts
      pkSeed pkRoot message sig sigParsed forsPk hParse hFors
      hFirstStepMem hCurrent0

/-- C13 bridge reducer with the reverted branch reduced to the raw layer-0
`afterMerkle` XMSS-climb equality needed by the layer-1 reverted case.  This is
strictly below the older first-step `"currentNode"` premise; the packaging lemma
derives the layer-1 scratch-cell current node from the raw merkle-node frame. -/
theorem c13_refines_byte_spec_of_current_node_facts_and_reverted_afterMerkle_raw_xmss_cover
    (hOkFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        SegmentLayer3.layerGuard
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig)) = true ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig))).bindings
            "currentNode"
          =
            C13Concrete.wordOfHash16
              (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.layers 0 forsPk) ∧
        SegmentLayer3.layerGuard
          (CurrentNodeFrame.c13LayerLoopState1
            (mkC13State pkSeed pkRoot message sig)) = true ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig))).bindings
            "currentNode"
          = C13Concrete.wordOfHash16 specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            forsPk sigParsed.layers,
          lookupValue
              (SegmentLayer3.afterMerkle
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "merkleNode" =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_facts_and_reverted_digest_scratch_cover
      hOkFacts ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse _hZero hFors hFold
  rcases hRevertedLayerFacts pkSeed pkRoot message sig sigParsed forsPk
      hParse _hZero hFors hFold with
    ⟨hFirstStepMem, hAfter⟩
  exact
    c13FoldRevertedDigestScratchData_of_layer1_afterMerkle_raw_xmssClimb
      pkSeed pkRoot message sig sigParsed forsPk hParse hFors
      hFirstStepMem hAfter

/-- C13 bridge reducer with the `.ok` branch reduced below the primitive
guard/current-node facts.  Callers provide post-prefix checksum cells for the
two guards and post-step `"merkleNode"` cells for the two `"currentNode"` facts;
the final comparison remains at the C13 word-roundtrip boundary and no
`pkRoot.size` premise is required. -/
theorem c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_layer_facts_cover
    (hOkFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkDigitMerkleData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
      ?_ ?_
  · intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
    exact
      c13FoldOkCurrentNodeWordcmpData_of_digit_merkle_facts
        pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
        (hOkFacts pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold)
  · intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
    rcases hRevertedLayerFacts pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold with
      ⟨hFirstStepMem, hCurrent0⟩
    exact
      c13FoldRevertedDigestScratchData_of_layer_facts
        pkSeed pkRoot message sig sigParsed forsPk hParse hFors
        hFirstStepMem hCurrent0

/-- C13 bridge reducer with the `.ok` branch at digit/Merkle facts and the
reverted branch reduced to the raw layer-0 `afterMerkle` XMSS equality.  This is
the direct after-Merkle analogue of
`c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_layer_facts_cover`. -/
theorem c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_afterMerkle_raw_xmss_cover
    (hOkFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkDigitMerkleData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            forsPk sigParsed.layers,
          lookupValue
              (SegmentLayer3.afterMerkle
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "merkleNode" =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
      ?_ ?_
  · intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
    exact
      c13FoldOkCurrentNodeWordcmpData_of_digit_merkle_facts
        pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
        (hOkFacts pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold)
  · intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
    rcases hRevertedLayerFacts pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold with
      ⟨hFirstStepMem, hAfter⟩
    exact
      c13FoldRevertedDigestScratchData_of_layer1_afterMerkle_raw_xmssClimb
        pkSeed pkRoot message sig sigParsed forsPk hParse hFors
        hFirstStepMem hAfter

/-- Bounded variant of
`c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_layer_facts_cover`.  The
caller no longer threads `C13FoldOkDigitMerkleData` through `hOkFacts`; instead
the accept branch consumes the exact-raw step witnesses and WOTS start-node
facts directly, and the normalized after-Merkle climb data is discharged
internally by
`c13FoldOkDigitMerkleData_of_afterMerkle_raw_step_witnesses_and_wotsPk` (no
broad `hFrameStep0`/`hFrameStep1` step witness premise). -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover
    (_hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (_hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkWotsPk0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkWotsPk1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_layer_facts_cover
      ?_ hRevertedLayerFacts
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  exact
    c13FoldOkDigitMerkleData_of_afterMerkle_raw_step_witnesses_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold
      (hOkWotsPk0 pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)
        (hOkWotsPk1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold)

/-- After-Merkle reverted variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover`.
The caller-side reverted branch no longer states the first-step
`"currentNode"` equality; it only supplies the raw layer-0 `afterMerkle`
XMSS-climb equality, while the first-step memory-zero fact is discharged from
`hParse`. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_afterMerkle_raw_xmss_cover
    (_hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (_hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkWotsPk0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkWotsPk1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedAfterMerkle :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            forsPk sigParsed.layers,
          lookupValue
              (SegmentLayer3.afterMerkle
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "merkleNode" =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_afterMerkle_raw_xmss_cover
      ?_ ?_
  · intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
    exact
      c13FoldOkDigitMerkleData_of_afterMerkle_raw_step_witnesses_and_wotsPk
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold
        (hOkWotsPk0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold)
        (hOkWotsPk1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold)
  · intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
    exact
      ⟨c13FirstStepLayer_memory_zero_eq_of_parse
          pkSeed pkRoot message sig sigParsed hParse,
       hRevertedAfterMerkle pkSeed pkRoot message sig sigParsed forsPk
          hParse hZero hFors hFold⟩

/-- Reduced variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover`.
The caller now provides the layer-0/layer-1 WOTS start-node facts at the
strictly earlier `beforeAuthOff` final-keccak cutpoint, which is closer to the
executable runtime; the chain to the after-Merkle initial WOTS PK shape needed
downstream is discharged internally by
`c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer{0,1}_of_final_keccak`. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_final_keccak_and_reverted_layer_facts_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkFinalKeccak0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkFinalKeccak1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover
    hOkRawStep0 hOkRawStep1
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_final_keccak
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkFinalKeccak0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_final_keccak
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkFinalKeccak1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    hRevertedLayerFacts

/-- After-Merkle reverted variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_final_keccak_and_reverted_layer_facts_cover`.
The accept branch is unchanged; the reverted branch is forwarded to the
raw-XMSS after-Merkle reducer. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_final_keccak_and_reverted_afterMerkle_raw_xmss_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkFinalKeccak0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkFinalKeccak1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkFinalKeccakDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedAfterMerkle :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            forsPk sigParsed.layers,
          lookupValue
              (SegmentLayer3.afterMerkle
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "merkleNode" =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_afterMerkle_raw_xmss_cover
    hOkRawStep0 hOkRawStep1
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_final_keccak
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkFinalKeccak0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_final_keccak
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkFinalKeccak1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    hRevertedAfterMerkle

/-- Reduced variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_final_keccak_and_reverted_layer_facts_cover`.
The caller now provides the layer-0/layer-1 WOTS start-node facts as the
single-equation `C13FoldOkBeforeAuthOffWotsPkWordDataLayer{0,1}` shape — just
`lookup "wotsPk" = C13Concrete.wotsPkWord …` — instead of the two-conjunct
`FinalKeccak` cutpoint.  The structural binding-eval equation that previously
had to be discharged alongside the executable masked-Keccak evaluation is
internalised: only the direct `wotsPkWord` equation is required at the boundary.
The reducer chain to the after-Merkle initial WOTS PK shape is dispatched via
`c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer{0,1}_of_wotsPkWord`. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_wotsPkWord_and_reverted_layer_facts_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkWotsPkWord0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkWotsPkWord1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover
    hOkRawStep0 hOkRawStep1
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_wotsPkWord
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkWotsPkWord0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_wotsPkWord
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkWotsPkWord1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    hRevertedLayerFacts

/-- After-Merkle reverted variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_wotsPkWord_and_reverted_layer_facts_cover`.
Only the reverted branch changes; the accept-side `wotsPkWord` adapters are
identical to the older layer-facts reducer. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_wotsPkWord_and_reverted_afterMerkle_raw_xmss_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkWotsPkWord0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkWordDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkWotsPkWord1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkWordDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedAfterMerkle :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            forsPk sigParsed.layers,
          lookupValue
              (SegmentLayer3.afterMerkle
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "merkleNode" =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_afterMerkle_raw_xmss_cover
    hOkRawStep0 hOkRawStep1
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_wotsPkWord
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkWotsPkWord0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_wotsPkWord
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkWotsPkWord1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    hRevertedAfterMerkle

/-- Strictly reduced variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_wotsPkWord_and_reverted_layer_facts_cover`.
The caller now provides the layer-0/layer-1 WOTS start-node facts in their
shortest spec-shape:
`lookup "wotsPk" = C13Concrete.wordOfHash16 d.wotsPk0` (six-argument
`C13Concrete.wotsPkWord …` reconstruction is no longer part of the caller
surface).  The `wotsPkWord = wordOfHash16 d.wotsPk0` reduction the previous
variant relied on is internalised: the cover dispatches via the existing
single-step `c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer{0,1}_of_beforeAuthOff`
reducer (which threads `beforeMerkle_wotsPk_eq_beforeAuthOff_wotsPk`). -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_layer_facts_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkBeforeAuthOffWotsPk0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkBeforeAuthOffWotsPk1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedLayerFacts :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ((SegmentLayer3.stepLayer
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
          ((c13FirstLayerGuardState pkSeed pkRoot message sig).world.memory 0x00).val ∧
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover
    hOkRawStep0 hOkRawStep1
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_beforeAuthOff
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkBeforeAuthOffWotsPk0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_beforeAuthOff
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkBeforeAuthOffWotsPk1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    hRevertedLayerFacts

/-- After-Merkle reverted variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_layer_facts_cover`.
This keeps the accept branch at the `beforeAuthOff` WOTS-PK facts while replacing
the older reverted first-step `"currentNode"` surface with the raw layer-0
`afterMerkle` XMSS equality. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_afterMerkle_raw_xmss_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkBeforeAuthOffWotsPk0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkBeforeAuthOffWotsPk1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedAfterMerkle :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            forsPk sigParsed.layers,
          lookupValue
              (SegmentLayer3.afterMerkle
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "merkleNode" =
            C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
              (C13Concrete.adrsXmssTree 0
                ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
              11 0
              ((C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
              (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_afterMerkle_raw_xmss_cover
    hOkRawStep0 hOkRawStep1
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_beforeAuthOff
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkBeforeAuthOffWotsPk0 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    (fun pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold =>
      c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_beforeAuthOff
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (hOkBeforeAuthOffWotsPk1 pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))
    hRevertedAfterMerkle

/-- Strictly reduced variant of
`c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_layer_facts_cover`.
The caller-side `hRevertedLayerFacts` has had its memory-zero conjunct
internalised via `c13FirstStepLayer_memory_zero_eq_of_parse` (proved unconditionally
from `hParse`).  Only the substantive `"currentNode"` correctness claim
remains on the reverted-branch caller surface. -/
theorem c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_currentNode_facts_cover
    (hOkRawStep0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            d.lsig0.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 0 + 692))))
    (hOkRawStep1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
        let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
        ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
            pk digest forsPk sigParsed.layers specRoot,
          C13AfterMerkleXmssRawStepWitnessPremiseAt
            (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 1 ((digest.hyperIndex / 2048) / 2048))
            d.lsig1.authPath
            (c13XmssAuthCdAt pkSeed pkRoot message sig
              (sigDataOffset + (1952 + 868 * 1 + 692))))
    (hOkBeforeAuthOffWotsPk0 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkDataLayer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hOkBeforeAuthOffWotsPk1 :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkBeforeAuthOffWotsPkDataLayer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedCurrentNode :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        lookupValue
            (SegmentLayer3.stepLayer
              (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
            "currentNode" =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk)) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete :=
  c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_layer_facts_cover
    hOkRawStep0 hOkRawStep1 hOkBeforeAuthOffWotsPk0 hOkBeforeAuthOffWotsPk1
    (fun pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold =>
      ⟨c13FirstStepLayer_memory_zero_eq_of_parse pkSeed pkRoot message sig sigParsed hParse,
       hRevertedCurrentNode pkSeed pkRoot message sig sigParsed forsPk
         hParse hZero hFors hFold⟩)

/-- C13 bridge reducer with the accept branch using the bounded two-step
current-node observation package and the reverted branch reduced to WOTS digest
scratch cells.  This keeps the final comparison at the C13 wordcmp boundary and
does not require the legacy public-key-root size premise from the observation
package. -/
theorem c13_refines_byte_spec_of_two_step_current_node_and_reverted_digest_scratch_cover
    (hOkObs :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
          pkSeed pkRoot message sig sigParsed forsPk)
    (hRevertedScratchData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
      ?_ hRevertedScratchData
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  exact
    c13FoldOkCurrentNodeWordcmpData_of_two_step_obligations
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
      (hOkObs pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)

/-- C13 bridge reducer with split accept-side guard/current-node facts and the
reverted branch reduced to WOTS digest scratch cells.  This uses the
word-comparison current-node boundary, so it does not require the legacy
universal `pkRoot.size = 16` premise from the older two-step observation
package. -/
theorem c13_refines_byte_spec_of_accept_guard_current_node_and_reverted_digest_scratch_cover

    (hGuard0 :

      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,

        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →

        forcedZeroOk c13

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →

        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          sigParsed.fors = some forsPk →

        foldHypertree C13Concrete.c13PrimitivesConcrete c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          forsPk sigParsed.layers = .ok specRoot →

        SegmentLayer3.layerGuard

          (CurrentNodeFrame.c13LayerLoopState0

            (mkC13State pkSeed pkRoot message sig)) = true)

    (hCurrent0 :

      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,

        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →

        forcedZeroOk c13

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →

        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          sigParsed.fors = some forsPk →

        foldHypertree C13Concrete.c13PrimitivesConcrete c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          forsPk sigParsed.layers = .ok specRoot →

        lookupValue

            (SegmentLayer3.stepLayer

              (CurrentNodeFrame.c13LayerLoopState0

                (mkC13State pkSeed pkRoot message sig))).bindings

            "currentNode"

          =

            C13Concrete.wordOfHash16

              (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer

                { pkSeed := pkSeed, pkRoot := pkRoot }

                (C13Concrete.c13PrimitivesConcrete.hMsg c13

                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

                sigParsed.layers 0 forsPk))

    (hGuard1 :

      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,

        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →

        forcedZeroOk c13

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →

        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          sigParsed.fors = some forsPk →

        foldHypertree C13Concrete.c13PrimitivesConcrete c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          forsPk sigParsed.layers = .ok specRoot →

        SegmentLayer3.layerGuard

          (CurrentNodeFrame.c13LayerLoopState1

            (mkC13State pkSeed pkRoot message sig)) = true)

    (hCurrent1 :

      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,

        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →

        forcedZeroOk c13

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →

        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          sigParsed.fors = some forsPk →

        foldHypertree C13Concrete.c13PrimitivesConcrete c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          forsPk sigParsed.layers = .ok specRoot →

        lookupValue

            (SegmentLayer3.stepLayer

              (CurrentNodeFrame.c13LayerLoopState1

                (mkC13State pkSeed pkRoot message sig))).bindings

            "currentNode"

          = C13Concrete.wordOfHash16 specRoot)

    (hRevertedScratchData :

      ∀ pkSeed pkRoot message sig sigParsed forsPk,

        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →

        forcedZeroOk c13

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →

        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          sigParsed.fors = some forsPk →

        foldHypertree C13Concrete.c13PrimitivesConcrete c13

          { pkSeed := pkSeed, pkRoot := pkRoot }

          (C13Concrete.c13PrimitivesConcrete.hMsg c13

            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)

          forsPk sigParsed.layers = .reverted →

        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :

    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by

  refine
    c13_refines_byte_spec_of_current_node_facts_and_reverted_digest_scratch_cover
      ?_ hRevertedScratchData

  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold

  exact
    ⟨hGuard0 pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold,
     hCurrent0 pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold,
     hGuard1 pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold,
     hCurrent1 pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold⟩



/-- C13 exact address-slot bridge from the historical `SegmentLayer3.beforeWotsPk`
cutpoint to the lightweight post-digit prefix cutpoint.  This is intentionally a
single-cell bridge, not a whole-state equality.

Now discharged via `c13_beforeWotsPk_eq_beforeWotsPkFrom`: the two states are
equal, so the cell framing is a rewrite. -/
theorem c13_beforeWotsPk_memory_0x20_eq_lightweight
    (ls : RuntimeState) :
    ((SegmentLayer3.beforeWotsPk ls).world.memory 0x20).val =
      ((SegmentLayer3AddressCells.beforeWotsPkFrom
        (SegmentLayer3.afterDigit ls)).world.memory 0x20).val := by
  rw [c13_beforeWotsPk_eq_beforeWotsPkFrom]

/-- Lightweight C13 WOTS-outer entry state used by the single-cell historical
bridges. -/
def c13BeforeWotsPkLightState (ls : RuntimeState) : RuntimeState :=
  { SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
      (SegmentLayer3.afterDigit ls) with
    bindings :=
      bindValue
        (SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
          (SegmentLayer3.afterDigit ls)).bindings
        "i" (wordNormalize 0) }

/-- `beforeWotsPkFrom` factors through the post-WOTS/address-store cutpoint and
the final copy loop (`beforeWotsPkAfterWotsCopyFrom`); proven by exec-list
rewriting only — no loop iteration is ever unfolded. -/
theorem c13_beforeWotsPkFrom_eq_afterWotsCopy (ad : RuntimeState) :
    SegmentLayer3AddressCells.beforeWotsPkFrom ad
      = SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom ad := by
  unfold SegmentLayer3AddressCells.beforeWotsPkFrom
    SegmentLayer3AddressCells.suffixBeforeWotsPkFrom
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (SegmentLayer3AddressCells.beforeWotsPkCopyFrom_eq ad)]
  rw [SegmentLayer3AddressCells.beforeWotsPkCopyFrom_eq_afterWots ad]
  rw [show ([Compiler.CompilationModel.Stmt.forEach "i"
          (Compiler.CompilationModel.Expr.literal 43)
          SegmentLayer3CopyCells.copyBody] : List Compiler.CompilationModel.Stmt)
        = SegmentLayer3AddressCells.suffixWotsPkCopyFrom from rfl]
  rw [SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom_eq ad]

/-- The WOTS-PK address-store interlude (the `pkAdrs` letVar plus `mstore 0x20`)
preserves every memory cell other than `0x20`. -/
theorem c13_addressStore_preserves_cell (ad : RuntimeState) (c : Nat)
    (hc : c ≠ 0x20) :
    ((SegmentLayer3AddressCells.beforeWotsPkCopyAfterWotsFrom ad).world.memory c).val =
      ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsFrom ad).world.memory c).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val c
    SegmentLayer3AddressCells.suffixWotsPkAddressStoreFrom _ _ ?_
    (SegmentLayer3AddressCells.beforeWotsPkCopyAfterWotsFrom_eq ad)
  intro s s'' stmt hmem hexec
  simp [SegmentLayer3AddressCells.suffixWotsPkAddressStoreFrom] at hmem
  rcases hmem with rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' c "pkAdrs" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' c _ _ ?_ hexec
    intro ro rv hoff _
    cases hoff
    have h20 : wordNormalize 0x20 = 0x20 := by
      rw [wordNormalize_eq_mod]; exact Nat.mod_eq_of_lt (by decide)
    rw [h20]
    omega

/-- The C13 WOTS-PK copy fold leaves chain-destination cells beyond the copy
range (`43 ≤ j`) untouched. -/
theorem c13_copyLoop_preserves_out_slot :
    ∀ (s : RuntimeState) (idx remaining j : Nat),
      43 ≤ j → idx + remaining ≤ 43 →
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep s idx remaining).world.memory
          (0x40 + 32 * j)).val
        = (s.world.memory (0x40 + 32 * j)).val
  | s, idx, 0, j, _, _ => by
      rw [ClimbLoop.foldLoop_zero]
  | s, idx, remaining + 1, j, hj, hbound => by
      have hidx : idx < 43 := by omega
      let s1 : RuntimeState :=
        SegmentLayer3CopyCells.copyStep
          { s with bindings := bindValue s.bindings "i" (wordNormalize idx) }
      rw [ClimbLoop.foldLoop_succ]
      change ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep s1 (idx + 1)
          remaining).world.memory (0x40 + 32 * j)).val
        = (s.world.memory (0x40 + 32 * j)).val
      rw [c13_copyLoop_preserves_out_slot s1 (idx + 1) remaining j hj (by omega)]
      exact SegmentLayer3CopyCells.copyStep_preserves_copy_slot s idx j hidx (by omega)

/-- Chain-destination cells of the full lightweight WOTS-PK cutpoint are the
pre-copy source cells, for in-range `j`.  The copy fold is introduced only via
`rw [← he]`, so the fold start state is never restated (its spelling stays the
one produced by `execStmt_forEach_of_step`). -/
theorem c13_awcf_copied_slot (ls : RuntimeState) (j : Nat) (hj : j < 43) :
    ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom
        (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val =
      ((SegmentLayer3AddressCells.beforeWotsPkCopyAfterWotsFrom
        (SegmentLayer3.afterDigit ls)).world.memory (0x80 + 32 * j)).val := by
  have h := SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom_eq
    (SegmentLayer3.afterDigit ls)
  unfold SegmentLayer3AddressCells.suffixWotsPkCopyFrom at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ []
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.copyBody _ _
      SegmentLayer3CopyCells.copyStep rfl
      SegmentLayer3CopyCells.copyStepLemma)] at h
  have hb : wordNormalize 43 = 43 := by
    rw [wordNormalize_eq_mod]; exact Nat.mod_eq_of_lt (by decide)
  rw [hb] at h
  have hnil : ∀ (s : RuntimeState), execStmtList [] s [] = StmtResult.continue s :=
    fun _ => rfl
  rw [hnil] at h
  have he := StmtResult.continue.inj h
  rw [← he]
  exact SegmentLayer3CopyCells.copyFold43_copied_slot _ j hj

/-- Out-of-range chain cells pass through the copy fold untouched. -/
theorem c13_awcf_out_slot (ls : RuntimeState) (j : Nat) (hj : 43 ≤ j) :
    ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom
        (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val =
      ((SegmentLayer3AddressCells.beforeWotsPkCopyAfterWotsFrom
        (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val := by
  have h := SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom_eq
    (SegmentLayer3.afterDigit ls)
  unfold SegmentLayer3AddressCells.suffixWotsPkCopyFrom at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ []
    (ClimbLoop.execStmt_forEach_of_step "i" (.literal 43)
      SegmentLayer3CopyCells.copyBody _ _
      SegmentLayer3CopyCells.copyStep rfl
      SegmentLayer3CopyCells.copyStepLemma)] at h
  have hb : wordNormalize 43 = 43 := by
    rw [wordNormalize_eq_mod]; exact Nat.mod_eq_of_lt (by decide)
  rw [hb] at h
  have hnil : ∀ (s : RuntimeState), execStmtList [] s [] = StmtResult.continue s :=
    fun _ => rfl
  rw [hnil] at h
  have he := StmtResult.continue.inj h
  rw [← he]
  exact c13_copyLoop_preserves_out_slot _ 0 43 j hj (by omega)

/-- The lightweight WOTS outer fold over `c13BeforeWotsPkLightState` IS the
named post-WOTS cutpoint (same start-state spelling, so `rfl`). -/
theorem c13_wotsFold_eq_lightweight (ls : RuntimeState) :
    ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
        (c13BeforeWotsPkLightState ls) 0 43
      = SegmentLayer3AddressCells.beforeWotsPkAfterWotsFrom
          (SegmentLayer3.afterDigit ls) := rfl

/-- C13 exact chain-cell bridge from the historical `SegmentLayer3.beforeWotsPk`
cutpoint to the lightweight WOTS-outer/copy-fold state.  This exposes only the
destination preimage cell requested by downstream WOTS-PK proofs.

Now discharged: routed through the lightweight `beforeWotsPkAfterWotsCopyFrom`
cutpoint (equal to `beforeWotsPk ls` via `c13_beforeWotsPk_eq_beforeWotsPkFrom` and
`c13_beforeWotsPkFrom_eq_afterWotsCopy`), whose chain cells are identified with the
copy-fold image by `c13_awcf_copied_slot` / `c13_awcf_out_slot`; both sides then meet
at the post-WOTS source cells through the address-store frame
`c13_addressStore_preserves_cell`.  Assembled with `congrArg`/`trans` only — no
rewriting under the interpreter folds — so elaboration stays in the ~400 MB regime. -/
theorem c13_beforeWotsPk_memory_chain_eq_lightweight
    (ls : RuntimeState) (j : Nat) :
    ((SegmentLayer3.beforeWotsPk ls).world.memory (0x40 + 32 * j)).val =
      ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
          (c13BeforeWotsPkLightState ls) 0 43)
        0 43).world.memory (0x40 + 32 * j)).val := by
  have h12 : SegmentLayer3.beforeWotsPk ls
      = SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom
          (SegmentLayer3.afterDigit ls) :=
    (c13_beforeWotsPk_eq_beforeWotsPkFrom ls).trans
      (c13_beforeWotsPkFrom_eq_afterWotsCopy (SegmentLayer3.afterDigit ls))
  have hA : ((SegmentLayer3.beforeWotsPk ls).world.memory (0x40 + 32 * j)).val
      = ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsCopyFrom
          (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val :=
    congrArg (fun s => ((s.world.memory (0x40 + 32 * j))).val) h12
  by_cases hj : j < 43
  · have hsrc : ((SegmentLayer3AddressCells.beforeWotsPkCopyAfterWotsFrom
          (SegmentLayer3.afterDigit ls)).world.memory (0x80 + 32 * j)).val
        = ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsFrom
            (SegmentLayer3.afterDigit ls)).world.memory (0x80 + 32 * j)).val :=
      c13_addressStore_preserves_cell (SegmentLayer3.afterDigit ls)
        (0x80 + 32 * j) (by omega)
    have hB : ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
          (c13BeforeWotsPkLightState ls) 0 43)
        0 43).world.memory (0x40 + 32 * j)).val
        = ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsFrom
            (SegmentLayer3.afterDigit ls)).world.memory (0x80 + 32 * j)).val :=
      (congrArg (fun s => ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          s 0 43).world.memory (0x40 + 32 * j)).val) (c13_wotsFold_eq_lightweight ls)).trans
        (SegmentLayer3CopyCells.copyFold43_copied_slot _ j hj)
    exact (hA.trans ((c13_awcf_copied_slot ls j hj).trans hsrc)).trans hB.symm
  · have hj' : 43 ≤ j := by omega
    have hcell : ((SegmentLayer3AddressCells.beforeWotsPkCopyAfterWotsFrom
          (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val
        = ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsFrom
            (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val :=
      c13_addressStore_preserves_cell (SegmentLayer3.afterDigit ls)
        (0x40 + 32 * j) (by omega)
    have hB : ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
        (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
          (c13BeforeWotsPkLightState ls) 0 43)
        0 43).world.memory (0x40 + 32 * j)).val
        = ((SegmentLayer3AddressCells.beforeWotsPkAfterWotsFrom
            (SegmentLayer3.afterDigit ls)).world.memory (0x40 + 32 * j)).val :=
      (congrArg (fun s => ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          s 0 43).world.memory (0x40 + 32 * j)).val) (c13_wotsFold_eq_lightweight ls)).trans
        (c13_copyLoop_preserves_out_slot _ 0 43 j hj' (by omega))
    exact (hA.trans ((c13_awcf_out_slot ls j hj').trans hcell)).trans hB.symm

/-- The exact lightweight facts needed to close a C13 WOTS-outer/copy-chain
cell residual.  This deliberately exposes only seed, digest, WOTS address,
WOTS pointer, and the calldata load relation for the lightweight loop state. -/
structure C13WotsOuterExactInputs
    (pkSeed pkRoot message sig : Bytes) (st : RuntimeState)
    (layer treeIdx leafIdx count node wotsPtr calldataBase : Nat) : Prop where
  hSeed : ∀ j, j < 43 →
    ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed
  hD : ∀ j, j < 43 →
    lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        layer treeIdx leafIdx count node
  hAdrs : ∀ j, j < 43 →
    lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
        "wotsAdrs" =
      C13Concrete.adrsWotsHashBase layer treeIdx leafIdx
  hWPtr : ∀ j, j < 43 →
    lookupValue (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).bindings
        "wotsPtr" = wotsPtr
  hCdLoad : ∀ j, j < 43 → ∀ (s : RuntimeState),
      lookupValue s.bindings "wotsPtr" = wotsPtr →
      lookupValue s.bindings "i" = j →
      s.world = (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 j).world →
      evalExpr [] s
          (.calldataload
            (.add (.localVar "wotsPtr")
              (.shl (.literal 4) (.localVar "i")))) =
        some (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
          (sigDataOffset + (calldataBase + 16 * j)))

/-- C13 accept-side layer-0 WOTS-PK address cell at the `beforeWotsPk`
cutpoint, discharged from the executable WOTS-PK address store. -/
theorem c13_ok_beforeAuthOff_wotsPk_address_cell_residual_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkAddressCellDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot
    := by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse _hZero _hFors _hFold
  intro _d
  rw [← c13FirstLayerGuardState_eq_c13LayerLoopState0 pkSeed pkRoot message sig]
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  change
    ((SegmentLayer3.beforeWotsPk
      (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
  rw [c13_beforeWotsPk_memory_0x20_eq_lightweight]
  exact SegmentLayer3AddressCells.beforeWotsPkFrom_memory_0x20_eq_of_bindings
    (SegmentLayer3.afterDigit (c13FirstLayerGuardState pkSeed pkRoot message sig))
    0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
    (by
      rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
        (c13FirstLayerGuardState pkSeed pkRoot message sig) "layer"
        (by decide) (by decide)]
      rw [SegmentLayer3.beforeDigitLoop_preserves_layer]
      exact c13FirstLayerGuardState_layer pkSeed pkRoot message sig)
    (by
      rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
        (c13FirstLayerGuardState pkSeed pkRoot message sig) "idxTree"
        (by decide) (by decide)]
      exact SegmentLayer3.beforeDigitLoop_idxTree_eq_of_idxTree
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        digest.hyperIndex
        (c13FirstLayerGuardState_idxTree_hyperIndex
          pkSeed pkRoot message sig hParse)
        (lt_trans
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
          (by decide : 2 ^ 22 < 2 ^ 256)))
    (by
      exact SegmentLayer3.afterDigit_idxLeaf_eq_of_idxTree
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        digest.hyperIndex
        (c13FirstLayerGuardState_idxTree_hyperIndex
          pkSeed pkRoot message sig hParse)
        (lt_trans
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
          (by decide : 2 ^ 22 < 2 ^ 256)))
    (by decide : 0 < 2 ^ 32)
    (by
      exact lt_of_le_of_lt (Nat.div_le_self _ _)
        (lt_trans (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
          (by decide : 2 ^ 22 < 2 ^ 32)))
    (lt_trans (Nat.mod_lt _ (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 32))

/-- Residual exact C13 accept-side layer-0 WOTS-outer facts at the lightweight
cutpoint.  The downstream chain cells are derived from these facts, not
axiomatized directly.

ASSEMBLY OBLIGATION (accepted axiom — see README "Residual assembly axioms").
Asserts that the five-field `C13WotsOuterExactInputs` package (seed cell, digest
`"d"`, `"wotsAdrs"`, `"wotsPtr"`, calldata load) holds at the *concrete* layer-0
WOTS-outer entry state `c13BeforeWotsPkLightState (c13LayerLoopState0 (mkC13State …))`.
This is a minimal honest assembly obligation: it pins the generic inputs record to a
concrete state built on `SegmentLayer3.afterDigit`, so its proof inherently needs
SegmentLayer3 reasoning. The GENERIC consumers of this record are already verified
under cap in `C13WotsPkKeccak.lean` (`c13Layer0_copyFold43_wotsChainsEnd_cells_of_inputs`,
`c13Layer0_copyFold43_wotsPk_keccak_of_inputs`); only this concrete-state instantiation
remains. Cannot be discharged on the current host: `Proofs.lean`/`SegmentLayer3.lean`
each peak ~48 GB as single modules (OOM above the 10 GB cap). Discharge needs a
>~64 GB pass; tracked in project memory. -/
axiom c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
        pk digest forsPk sigParsed.layers specRoot,
      let st :=
        c13BeforeWotsPkLightState
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))
      let wotsPtr := lookupValue st.bindings "wotsPtr"
      C13WotsOuterExactInputs pkSeed pkRoot message sig st
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk) wotsPtr 1952

/-- The layer-0 C13 calldata/loop closure from exact lightweight WOTS-outer
inputs to copied chain-end cells: discharged by the verified
`c13Layer0_copyFold43_wotsChainsEnd_cells_of_entry` (C13WotsPkKeccak), with the
entry record built from the inputs record at prefix `0` via `foldLoop_zero`
and the calldata loads passed through verbatim. -/
theorem c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_of_inputs_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
        pk digest forsPk sigParsed.layers specRoot,
      let st :=
        c13BeforeWotsPkLightState
          (CurrentNodeFrame.c13LayerLoopState0
            (mkC13State pkSeed pkRoot message sig))
      let wotsPtr := lookupValue st.bindings "wotsPtr"
      C13WotsOuterExactInputs pkSeed pkRoot message sig st
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk) wotsPtr 1952 →
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep st 0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega):= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse _hZero _hFors _hFold pk digest d st wotsPtr hInputs j hj
  have hHyLt :
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).hyperIndex
        < 2 ^ 22 :=
    C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message
  have hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk) < 2 ^ 256 :=
    c13_wotsDigest_lt (C13Concrete.wordOfHash16 pkSeed)
      0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk)
  have hAdrsLt :
      C13Concrete.adrsWotsHashBase 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) < 2 ^ 256 := by
    have hT : (digest.hyperIndex / 2048) <<< 128 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        (digest.hyperIndex / 2048) * 2 ^ 128 ≤ 2 ^ 22 * 2 ^ 128 :=
          Nat.mul_le_mul_right _
            (le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hHyLt))
        _ < 2 ^ 256 := by decide
    have hL : (digest.hyperIndex % 2048) <<< 64 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        (digest.hyperIndex % 2048) * 2 ^ 64 ≤ 2047 * 2 ^ 64 :=
          Nat.mul_le_mul_right _
            (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2048)))
        _ < 2 ^ 256 := by decide
    have h224 : (0 : Nat) <<< 224 < 2 ^ 256 := by decide
    exact Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow h224 hT) hL
  have e : C13WotsOuterEntry pkSeed st
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk))
      (C13Concrete.adrsWotsHashBase 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
      wotsPtr :=
    { seed0 := by
        have h := hInputs.hSeed 0 (by decide)
        rwa [ClimbLoop.foldLoop_zero] at h
      d0 := by
        have h := hInputs.hD 0 (by decide)
        rwa [ClimbLoop.foldLoop_zero] at h
      adrs0 := by
        have h := hInputs.hAdrs 0 (by decide)
        rwa [ClimbLoop.foldLoop_zero] at h
      wptr0 := rfl }
  exact c13Layer0_copyFold43_wotsChainsEnd_cells_of_entry
    pkSeed pkRoot message sig sigParsed st
    (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
    (C13Concrete.wordOfHash16 forsPk) wotsPtr
    d.lsig0 hParse d.hLayer0 hDigestLt hAdrsLt e
    (fun j' hj' s h1 h2 h3 => hInputs.hCdLoad j' hj' s h1 h2 h3)
    j hj

/-- C13 accept-side layer-0 copied WOTS chain-end cells at the lightweight
WOTS-outer/copy-fold cutpoint: composition of the exact-inputs obligation and
its verified `_of_inputs` closure. -/
theorem c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
        pk digest forsPk sigParsed.layers specRoot,
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (CurrentNodeFrame.c13LayerLoopState0
                (mkC13State pkSeed pkRoot message sig)))
            0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega):= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold pk digest d j hj
  have hInputs :=
    c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold d
  exact
    c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_of_inputs_layer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold d hInputs
      j hj

/-- C13 accept-side layer-0 copied WOTS chain-end cells at the historical
`beforeWotsPk` cutpoint, reduced to the lightweight copy-fold residual. -/
theorem c13_ok_beforeAuthOff_wotsPk_chain_cells_residual_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  intro d
  change
    ∀ j, (h : j < 43) →
      ((SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)
  intro j hj
  rw [c13_beforeWotsPk_memory_chain_eq_lightweight]
  exact
    c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold d j hj

/-- C13 accept-side layer-1 WOTS-PK address cell at the `beforeWotsPk`
cutpoint, discharged from the executable WOTS-PK address store. -/
theorem c13_ok_beforeAuthOff_wotsPk_address_cell_residual_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkAddressCellDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse _hZero _hFors _hFold
  intro _d
  rw [← c13SecondLayerGuardState_eq_c13LayerLoopState1 pkSeed pkRoot message sig]
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  change
    ((SegmentLayer3.beforeWotsPk
      (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsPk 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
  rw [c13_beforeWotsPk_memory_0x20_eq_lightweight]
  exact SegmentLayer3AddressCells.beforeWotsPkFrom_memory_0x20_eq_of_bindings
    (SegmentLayer3.afterDigit (c13SecondLayerGuardState pkSeed pkRoot message sig))
    1 ((digest.hyperIndex / 2048) / 2048)
      ((digest.hyperIndex / 2048) % 2048)
    (by
      rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
        (c13SecondLayerGuardState pkSeed pkRoot message sig) "layer"
        (by decide) (by decide)]
      rw [SegmentLayer3.beforeDigitLoop_preserves_layer]
      exact c13SecondLayerGuardState_layer pkSeed pkRoot message sig)
    (by
      rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
        (c13SecondLayerGuardState pkSeed pkRoot message sig) "idxTree"
        (by decide) (by decide)]
      exact SegmentLayer3.beforeDigitLoop_idxTree_eq_of_idxTree
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        (digest.hyperIndex / 2048)
        (c13SecondLayerGuardState_idxTree_hyperIndex
          pkSeed pkRoot message sig hParse)
        (lt_of_le_of_lt (Nat.div_le_self _ _)
          (lt_trans
            (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
            (by decide : 2 ^ 22 < 2 ^ 256))))
    (by
      exact SegmentLayer3.afterDigit_idxLeaf_eq_of_idxTree
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        (digest.hyperIndex / 2048)
        (c13SecondLayerGuardState_idxTree_hyperIndex
          pkSeed pkRoot message sig hParse)
        (lt_of_le_of_lt (Nat.div_le_self _ _)
          (lt_trans
            (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
            (by decide : 2 ^ 22 < 2 ^ 256))))
    (by decide : 1 < 2 ^ 32)
    (by
      exact lt_of_le_of_lt (Nat.div_le_self _ _)
        (lt_of_le_of_lt (Nat.div_le_self _ _)
          (lt_trans (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
            (by decide : 2 ^ 22 < 2 ^ 32))))
    (lt_trans (Nat.mod_lt _ (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 32))

/-- Residual C13 accept-side layer-1 copied WOTS chain-end cells at the
lightweight WOTS-outer/copy-fold cutpoint.

ASSEMBLY OBLIGATION (accepted axiom — see README "Residual assembly axioms").
Asserts the 43 copied chain-end memory cells (`0x40 + 32*j`) equal
`InitialNodeKeccak.wotsChainsEnd … d.root0 …` at the *concrete* layer-1 entry state
`beforeWotsPkWotsPtrFrom (SegmentLayer3.afterDigit (c13LayerLoopState1 (mkC13State …)))`.
Minimal honest assembly obligation: the generic copy-fold/chain-cells closure is already
verified under cap in `C13WotsPkKeccak.lean`
(`c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs` / `_of_entry`); what remains is only
pinning it to this concrete `afterDigit`-derived state, which needs SegmentLayer3 reasoning.
Cannot be discharged on the current host (Proofs.lean/SegmentLayer3.lean peak ~48 GB,
OOM above the 10 GB cap); needs a >~64 GB pass. -/
axiom c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
        pk digest forsPk sigParsed.layers specRoot,
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig)))
            0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega)

/-- C13 accept-side layer-1 copied WOTS chain-end cells at the historical
`beforeWotsPk` cutpoint, reduced to the lightweight copy-fold residual. -/
theorem c13_ok_beforeAuthOff_wotsPk_chain_cells_residual_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkChainCellsDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  intro d
  change
    ∀ j, (h : j < 43) →
      ((SegmentLayer3.beforeWotsPk
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).world.memory
        (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 1
          (((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
          (((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
          (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)
  intro j hj
  rw [c13_beforeWotsPk_memory_chain_eq_lightweight]
  exact
    c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold d j hj

/-- C13 accept-side layer-0 address/chain cells, composed from separate exact
address-cell and chain-cell residuals. -/
theorem c13_ok_beforeAuthOff_wotsPk_address_chain_cells_residual_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer0_of_split
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13_ok_beforeAuthOff_wotsPk_address_cell_residual_layer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)
      (c13_ok_beforeAuthOff_wotsPk_chain_cells_residual_layer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)

/-- C13 accept-side layer-1 address/chain cells, composed from separate exact
address-cell and chain-cell residuals. -/
theorem c13_ok_beforeAuthOff_wotsPk_address_chain_cells_residual_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkBeforeAuthOffWotsPkAddressChainCellsDataLayer1_of_split
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13_ok_beforeAuthOff_wotsPk_address_cell_residual_layer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)
      (c13_ok_beforeAuthOff_wotsPk_chain_cells_residual_layer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)

/-- C13 accept-side layer-0 final-WOTS-PK preimage cells, reduced to the
remaining address/chain-cell residual plus the proved seed cell. -/
theorem c13_ok_beforeAuthOff_wotsPk_preimage_cells_residual_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer0_of_address_chain_cells
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13_ok_beforeAuthOff_wotsPk_address_chain_cells_residual_layer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)

/-- C13 accept-side layer-1 final-WOTS-PK preimage cells, reduced to the
remaining address/chain-cell residual plus the proved seed cell. -/
theorem c13_ok_beforeAuthOff_wotsPk_preimage_cells_residual_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkBeforeAuthOffWotsPkPreimageCellsDataLayer1_of_address_chain_cells
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse
      (c13_ok_beforeAuthOff_wotsPk_address_chain_cells_residual_layer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)

/-- C13 accept-side layer-0 WOTS-PK start node at the after-Merkle cutpoint,
reduced to concrete WOTS-PK preimage cells at `beforeWotsPk`. -/
theorem c13_ok_afterMerkle_initial_wotsPk_residual_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_beforeAuthOff
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13FoldOkBeforeAuthOffWotsPkDataLayer0_of_preimage_cells
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (c13_ok_beforeAuthOff_wotsPk_preimage_cells_residual_layer0
          pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))

/-- C13 accept-side layer-1 WOTS-PK start node at the after-Merkle cutpoint,
reduced to concrete WOTS-PK preimage cells at `beforeWotsPk`. -/
theorem c13_ok_afterMerkle_initial_wotsPk_residual_layer1 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_beforeAuthOff
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      (c13FoldOkBeforeAuthOffWotsPkDataLayer1_of_preimage_cells
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        (c13_ok_beforeAuthOff_wotsPk_preimage_cells_residual_layer1
          pkSeed pkRoot message sig sigParsed forsPk specRoot
          hParse hZero hFors hFold))

/-- Residual C13 accept-side digit/checksum and Merkle facts, now composed from
separate raw step-witness and initial-WOTS-PK obligations.  The final
current-node word-comparison package is composed locally from this surface by
`c13FoldOkCurrentNodeWordcmpData_of_digit_merkle_facts`. -/
theorem c13_ok_digit_merkle_facts_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkDigitMerkleData
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkDigitMerkleData_of_afterMerkle_raw_step_witnesses_and_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold
      (c13_ok_afterMerkle_initial_wotsPk_residual_layer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold)
      (c13_ok_afterMerkle_initial_wotsPk_residual_layer1
        pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold)

/-- C13 accept-side current-node fact at the final word-comparison boundary,
proved by composing the smaller digit/Merkle package. -/
theorem c13_ok_current_node_wordcmp_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot →
    C13FoldOkCurrentNodeWordcmpData
      pkSeed pkRoot message sig sigParsed forsPk specRoot:= by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold
  exact
    c13FoldOkCurrentNodeWordcmpData_of_digit_merkle_facts
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
      (c13_ok_digit_merkle_facts_residual
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold)

/-- C13 reverted-at-layer-1 layer-0 WOTS-PK address cell at the `beforeWotsPk`
cutpoint, discharged from the executable WOTS-PK address store. -/
theorem c13_reverted_layer0_beforeAuthOff_wotsPk_address_cell_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted →
    C13FoldRevertedBeforeAuthOffWotsPkAddressCellDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk:= by
  intro pkSeed pkRoot message sig sigParsed forsPk hParse _hZero _hFors _hFold
  intro _d
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  change
    ((SegmentLayer3.beforeWotsPk
      (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsPk 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
  rw [c13_beforeWotsPk_memory_0x20_eq_lightweight]
  exact SegmentLayer3AddressCells.beforeWotsPkFrom_memory_0x20_eq_of_bindings
    (SegmentLayer3.afterDigit (c13FirstLayerGuardState pkSeed pkRoot message sig))
    0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
    (by
      rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
        (c13FirstLayerGuardState pkSeed pkRoot message sig) "layer"
        (by decide) (by decide)]
      rw [SegmentLayer3.beforeDigitLoop_preserves_layer]
      exact c13FirstLayerGuardState_layer pkSeed pkRoot message sig)
    (by
      rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
        (c13FirstLayerGuardState pkSeed pkRoot message sig) "idxTree"
        (by decide) (by decide)]
      exact SegmentLayer3.beforeDigitLoop_idxTree_eq_of_idxTree
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        digest.hyperIndex
        (c13FirstLayerGuardState_idxTree_hyperIndex
          pkSeed pkRoot message sig hParse)
        (lt_trans
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
          (by decide : 2 ^ 22 < 2 ^ 256)))
    (by
      exact SegmentLayer3.afterDigit_idxLeaf_eq_of_idxTree
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        digest.hyperIndex
        (c13FirstLayerGuardState_idxTree_hyperIndex
          pkSeed pkRoot message sig hParse)
        (lt_trans
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
          (by decide : 2 ^ 22 < 2 ^ 256)))
    (by decide : 0 < 2 ^ 32)
    (by
      exact lt_of_le_of_lt (Nat.div_le_self _ _)
        (lt_trans (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
          (by decide : 2 ^ 22 < 2 ^ 32)))
    (lt_trans (Nat.mod_lt _ (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 32))

/-- Residual C13 reverted-at-layer-1 layer-0 copied WOTS chain-end cells at the
lightweight WOTS-outer/copy-fold cutpoint.

ASSEMBLY OBLIGATION (accepted axiom — see README "Residual assembly axioms").
The reverted-path twin of the layer-0 chain-cells closure: asserts the 43 copied
chain-end cells equal `wotsChainsEnd …` at the concrete reverted-layer-0 entry state.
Minimal honest assembly obligation: the generic reverted closure is already verified
under cap in `C13WotsPkKeccak.lean`
(`c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs`,
`c13RevertedLayer0_copyFold43_wotsPk_keccak_of_inputs`); only the concrete-state
instantiation (built on `SegmentLayer3.afterDigit`) remains. Cannot be discharged on
the current host (~48 GB OOM above the 10 GB cap); needs a >~64 GB pass. -/
axiom c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        pk digest forsPk sigParsed.layers,
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (c13FirstLayerGuardState pkSeed pkRoot message sig))
            0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega)

/-- C13 reverted-at-layer-1 layer-0 copied WOTS chain-end cells at the
historical `beforeWotsPk` cutpoint, reduced to the lightweight copy-fold
residual. -/
theorem c13_reverted_layer0_beforeAuthOff_wotsPk_chain_cells_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted →
    C13FoldRevertedBeforeAuthOffWotsPkChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk:= by
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  intro d
  change
    ∀ j, (h : j < 43) →
      ((SegmentLayer3.beforeWotsPk
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory
        (0x40 + 32 * j)).val =
        (InitialNodeKeccak.wotsChainsEnd
          (C13Concrete.wordOfHash16 pkSeed) 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
            rw [InitialNodeKeccak.wotsChainsEnd_length]
            omega)
  intro j hj
  rw [c13_beforeWotsPk_memory_chain_eq_lightweight]
  exact
    c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual
      pkSeed pkRoot message sig sigParsed forsPk
      hParse hZero hFors hFold d j hj

/-- Residual C13 reverted-at-layer-1 layer-0 WOTS-PK address and chain cells
at the `beforeWotsPk` cutpoint, now composed from separate exact address-cell
and copied-chain-cell obligations. -/
theorem c13_reverted_layer0_beforeAuthOff_wotsPk_address_chain_cells_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted →
    C13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0
      pkSeed pkRoot message sig sigParsed forsPk:= by
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedBeforeAuthOffWotsPkAddressChainCellsDataLayer0_of_split
      pkSeed pkRoot message sig sigParsed forsPk
      (c13_reverted_layer0_beforeAuthOff_wotsPk_address_cell_residual
        pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold)
      (c13_reverted_layer0_beforeAuthOff_wotsPk_chain_cells_residual
        pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold)

/-- C13 reverted-branch raw XMSS climb fact after the first layer's Merkle
segment, reduced to the smaller layer-0 WOTS-PK address and chain cells. -/
theorem c13_reverted_afterMerkle_raw_xmss_residual :
  ∀ pkSeed pkRoot message sig sigParsed forsPk,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted →
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterMerkle
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "merkleNode" =
        C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
          (C13Concrete.adrsXmssTree 0
            ((C13Concrete.c13PrimitivesConcrete.hMsg c13
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048))
          11 0
          ((C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
          (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath:= by
  intro pkSeed pkRoot message sig sigParsed forsPk
    hParse hZero hFors hFold
  exact
    c13_reverted_afterMerkle_raw_xmss_of_address_chain_cells
      pkSeed pkRoot message sig sigParsed forsPk
      hParse hZero hFors hFold
      (c13_reverted_layer0_beforeAuthOff_wotsPk_address_chain_cells_residual
        pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 exported byte-spec bridge, reduced to the accept-side current-node
word-comparison residual and the reverted after-Merkle residual rather than
assumed directly at the byte-verifier boundary. -/
theorem c13_refines_byte_spec :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13 :=
  SphincsMinusVerifiers.c13_refines_byte_spec_exported_of_concrete
    (c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
      c13_ok_current_node_wordcmp_residual
      (fun pkSeed pkRoot message sig sigParsed forsPk hParse _hZero hFors _hFold =>
        c13FoldRevertedDigestScratchData_of_layer1_afterMerkle_raw_xmssClimb
          pkSeed pkRoot message sig sigParsed forsPk hParse hFors
          (c13FirstStepLayer_memory_zero_eq_of_parse
            pkSeed pkRoot message sig sigParsed hParse)
          (c13_reverted_afterMerkle_raw_xmss_residual
            pkSeed pkRoot message sig sigParsed forsPk
            hParse _hZero hFors _hFold)))

/-- C13: the compiled model refines the abstract algorithmic spec. -/
theorem c13_refines_spec
    (pkSeed pkRoot message sig : Bytes) :
    execC13 pkSeed pkRoot message sig =
      verifySpec c13Primitives c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sig :=
  byteVerifier_refines_spec c13_refines_byte_spec pkSeed pkRoot message sig

/-- C13 packaged at the `ImplementsVerifier` boundary. -/
theorem c13_implements_spec :
    ImplementsVerifier c13Primitives c13
      (fun pk message sig => execC13 pk.pkSeed pk.pkRoot message sig) :=
  byteVerifier_implements_spec c13_refines_byte_spec

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- SHA-2 SLH-DSA: the real compiled body run and the byte spec agree on every
wrong-length input. Proved, no bridge axiom. -/
theorem slhDsaSha2_128_24_interp_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : wordNormalize sig.size ≠ wordNormalize 3856) :
    execStmtList [] (badLenState sig.size) slhDsaSha2VerifyBody = .revert
      ∧ ByteLevel.verifyBytes slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
          pkSeed pkRoot message sig = none := by
  refine ⟨?_, ?_⟩
  · apply slhDsaSha2VerifyBody_reverts_on_bad_length
    rw [badLenState_sig_length]; exact hne
  · apply ByteLevel.verifyBytes_bad_length
    intro h
    exact hne (congrArg wordNormalize h)

/-! ### Surfaced accept-direction soundness

`verifyBytes_accepts_sound` (proved axiom-free beyond `propext` in `Spec.lean`)
lifted across each MODEL-EXEC-BRIDGE axiom to the observable `exec*` boundary: an
accepting compiled run exhibits a canonical public key, a parsed signature, and a
hypertree climb terminating in a root that matches `pkRoot`. -/

/-- Generic lifter: any observable verifier refining its byte spec inherits the
byte-level accept-direction soundness. -/
theorem exec_accepts_sound
    {p : Primitives} {v : Variant}
    {exec : Bytes → Bytes → Bytes → Bytes → Option Bool}
    (hModel : ByteLevel.ImplementsByteVerifier p v exec)
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : exec pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey v pkSeed pkRoot = some pk ∧
      p.parseSignature v sig = some parsedSig ∧
      signatureShapeOk v parsedSig = true ∧
      forcedZeroOk v (p.hMsg v pk parsedSig.R message) = true ∧
      p.forsPkFromSig v pk (p.hMsg v pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree p v pk (p.hMsg v pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      rootMatchesPk v root pk.pkRoot = true := by
  have hBytes : ByteLevel.verifyBytes p v pkSeed pkRoot message sig = some true := by
    rw [← hModel]; exact hAcc
  exact ByteLevel.verifyBytes_accepts_sound p v pkSeed pkRoot message sig hBytes

/-- C13: accepting compiled run ⇒ well-formed reconstructed witness. -/
theorem execC13_accepts_sound
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : execC13 pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey c13 pkSeed pkRoot = some pk ∧
      c13Primitives.parseSignature c13 sig = some parsedSig ∧
      signatureShapeOk c13 parsedSig = true ∧
      forcedZeroOk c13 (c13Primitives.hMsg c13 pk parsedSig.R message) = true ∧
      c13Primitives.forsPkFromSig c13 pk (c13Primitives.hMsg c13 pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree c13Primitives c13 pk (c13Primitives.hMsg c13 pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      rootMatchesPk c13 root pk.pkRoot = true :=
  exec_accepts_sound c13_refines_byte_spec pkSeed pkRoot message sig hAcc

/-- SHA2 SLH-DSA: accepting compiled run ⇒ well-formed reconstructed witness. -/
theorem execSlhDsaSha2_128_24_accepts_sound
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : execSlhDsaSha2_128_24 pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey slhDsaSha2_128_24 pkSeed pkRoot = some pk ∧
      slhDsaSha2_128_24_Primitives.parseSignature slhDsaSha2_128_24 sig = some parsedSig ∧
      signatureShapeOk slhDsaSha2_128_24 parsedSig = true ∧
      forcedZeroOk slhDsaSha2_128_24 (slhDsaSha2_128_24_Primitives.hMsg slhDsaSha2_128_24 pk parsedSig.R message) = true ∧
      slhDsaSha2_128_24_Primitives.forsPkFromSig slhDsaSha2_128_24 pk (slhDsaSha2_128_24_Primitives.hMsg slhDsaSha2_128_24 pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 pk (slhDsaSha2_128_24_Primitives.hMsg slhDsaSha2_128_24 pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      rootMatchesPk slhDsaSha2_128_24 root pk.pkRoot = true :=
  exec_accepts_sound slhDsaSha2_128_24_refines_byte_spec pkSeed pkRoot message sig hAcc

/--
Compilation-model presence checks.  These are small regression anchors: if the
models are renamed or removed, the refinement file stops compiling before any
semantic proof attempt starts.
-/
example : c13Model.name = "SphincsC13Asm_VerityModel" := rfl
example : slhDsaSha2_128_24_Model.name = "SLH_DSA_SHA2_128_24_VerityModel" := rfl

#print axioms c13_refines_byte_spec_of_good_length_cover
#print axioms c13_refines_byte_spec_of_forced_zero_true_cover
#print axioms c13_refines_byte_spec_of_fors_some_cover
#print axioms c13_refines_byte_spec_of_fold_result_cover
#print axioms c13FirstLayerGuardState_eq_c13LayerLoopState0
#print axioms c13SecondLayerGuardState_eq_c13LayerLoopState1
#print axioms c13FirstLayerGuardState_seed_slot
#print axioms c13FirstLayerBeforeDigest_seed_slot
#print axioms c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
#print axioms c13FirstStepLayer_seed_slot_of_memory_zero
#print axioms c13FirstLayerGuardState_currentNode
#print axioms c13AfterFinalize_forsPk_of_parse_fors
#print axioms c13FirstLayerGuardState_idxTree
#print axioms c13FirstLayerGuardState_idxTree_hyperIndex
#print axioms c13FirstLayerGuardState_sigOff
#print axioms c13FirstLayerGuardState_sigBase
#print axioms c13SecondLayerGuardState_sigBase
#print axioms c13SecondLayerGuardState_sigOff
#print axioms c13FirstLayerGuardState_layer
#print axioms c13SecondLayerGuardState_layer
#print axioms c13FirstLayerGuardState_selector
#print axioms c13FirstLayerGuardState_calldata
#print axioms c13SecondLayerGuardState_selector
#print axioms c13SecondLayerGuardState_calldata
#print axioms c13SecondLayerGuardState_idxTree_hyperIndex
#print axioms c13FirstLayerBeforeDigest_idxLeaf_hyperIndex
#print axioms c13FirstLayerBeforeDigest_idxTree_hyperIndex
#print axioms c13FirstLayerBeforeMerkle_mIdx_hyperIndex
#print axioms c13SecondLayerBeforeMerkle_mIdx_hyperIndex
#print axioms c13_adrsXmssTree_lt_of_bounds
#print axioms c13FirstLayerBeforeMerkle_layerFrozenSite
#print axioms c13SecondLayerBeforeMerkle_layerFrozenSite
#print axioms c13FirstLayerBeforeDigest_wotsAdrs_hyperIndex
#print axioms c13FirstLayer_wotsAdrs_hyperIndex_norm
#print axioms c13SecondLayer_wotsAdrs_hyperIndex_norm
#print axioms c13SecondLayerBeforeDigest_wotsAdrs_hyperIndex
#print axioms c13FirstLayerBeforeDigest_wotsAdrs_slot
#print axioms c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
#print axioms c13SecondLayerBeforeDigest_wotsAdrs_slot
#print axioms c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
#print axioms c13FirstLayerBeforeDigest_currentNode_slot
#print axioms c13FirstLayerBeforeDigest_currentNode_slot_of_parse_fors
#print axioms c13SecondLayerGuardState_currentNode_of_first_step_reverted_layer1
#print axioms c13SecondLayerBeforeDigest_currentNode_slot
#print axioms c13FirstLayerBeforeDigest_count_slot
#print axioms c13SecondLayerBeforeDigest_count_slot
#print axioms c13FirstLayerBeforeDigest_count_hyperIndex
#print axioms c13SecondLayerBeforeDigest_count_hyperIndex
#print axioms c13FirstLayer_wotsCount_norm
#print axioms c13SecondLayer_wotsCount_norm
#print axioms c13FirstLayerBeforeDigest_count_slot_hyperIndex
#print axioms c13SecondLayerBeforeDigest_count_slot_hyperIndex
#print axioms c13SecondLayerGuardState_currentNode_of_reverted_layer1_afterMerkle_raw_xmssClimb
#print axioms c13FoldOkCurrentNodePkRootSizeData_of_current_node_facts
#print axioms c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
#print axioms c13FoldOkCurrentNodeWordcmpData_of_two_step_obligations
#print axioms c13_refines_byte_spec_of_current_node_and_reverted_guard_cover
#print axioms c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digit_sum_cover
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_guard_cover
#print axioms c13FoldRevertedBeforeDigitData_of_digest_scratch_data
#print axioms c13FoldRevertedDigitSumData_of_before_digit_data
#print axioms c13FoldRevertedGuardData_of_digit_sum_data
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_before_digit_cover
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digest_scratch_cover
#print axioms c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_before_digit_cover
#print axioms c13FoldRevertedDigestScratchData_of_layer_facts
#print axioms c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
#print axioms c13_refines_byte_spec_of_current_node_facts_and_reverted_digest_scratch_cover
#print axioms c13_refines_byte_spec_of_current_node_facts_and_reverted_layer_facts_cover
#print axioms c13_refines_byte_spec_of_current_node_facts_and_reverted_afterMerkle_raw_xmss_cover
#print axioms c13_refines_byte_spec_of_ok_digit_merkle_and_reverted_afterMerkle_raw_xmss_cover
#print axioms c13_refines_byte_spec_of_two_step_current_node_and_reverted_digest_scratch_cover
#print axioms c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer0
#print axioms c13AfterMerkleXmssFrameStepBoundedWitnessPremiseAt_layer1
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer0_holds
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameStepDataLayer1_holds
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer0_of_wotsPk
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameDataLayer1_of_wotsPk
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbBoundedFrameData_of_wotsPk
#print axioms c13AfterMerkleNormalizedXmssClimb_of_layer_site_bounded
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbModelData_of_wotsPk
#print axioms c13FoldOkAfterMerkleNormalizedXmssClimbData_of_raw_step_witnesses_and_wotsPk
#print axioms c13FoldOkDigitMerkleData_of_afterMerkle_raw_step_witnesses_and_wotsPk
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_layer_facts_cover
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_reverted_afterMerkle_raw_xmss_cover
#print axioms c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_final_keccak
#print axioms c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_final_keccak
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_final_keccak_and_reverted_layer_facts_cover
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_final_keccak_and_reverted_afterMerkle_raw_xmss_cover
#print axioms c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0_of_wotsPkWord
#print axioms c13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer1_of_wotsPkWord
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_wotsPkWord_and_reverted_layer_facts_cover
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_wotsPkWord_and_reverted_afterMerkle_raw_xmss_cover
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_layer_facts_cover
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_afterMerkle_raw_xmss_cover
#print axioms c13FirstStepLayer_memory_zero_eq_of_parse
#print axioms c13FoldRevertedDigestScratchData_of_layer1_afterMerkle_raw_xmssClimb
#print axioms c13_refines_byte_spec_of_ok_raw_step_witnesses_and_beforeAuthOffWotsPk_and_reverted_currentNode_facts_cover
#print axioms c13FoldOkBeforeAuthOffWotsPkWordDataLayer0_of_prebind_keccak
#print axioms c13FoldOkBeforeAuthOffWotsPkWordDataLayer1_of_prebind_keccak

end SphincsMinusVerifiers
#print axioms SphincsMinusVerifiers.c13_refines_byte_spec_of_accept_guard_current_node_and_reverted_digest_scratch_cover
#print axioms SphincsMinusVerifiers.c13_refines_byte_spec
#print axioms SphincsMinusVerifiers.c13_refines_spec
