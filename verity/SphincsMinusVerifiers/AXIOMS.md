# Axiom Inventory

Status date: 2026-06-11

This directory models only the two live verifiers: the C13 keccak verifier
(`src/SPHINCs-C13Asm.sol`) and the SLH-DSA-SHA2-128-24 verifier
(`src/SLH-DSA-SHA2-128-24verifier.sol`). C7 and C9 remain live Solidity
contracts but are not modeled here. The Lean models are hand-transcribed from
the Solidity assembly; they are not compiled into production contracts, not
deployed, and not replayed in Foundry.

The complete trust surface of the top-level theorems, as reported by the
`#print axioms` guards at the bottom of `Proofs.lean`, is listed below.
There are no other axioms in this development.

## C13 (keccak)

`c13_refines_byte_spec`, `c13_refines_spec`, and `c13_implements_spec` are
proved theorems (not axioms). The model-to-byte-spec bridge that older
revisions took as an axiom has been discharged. `c13Primitives` is a concrete
definition (`def c13Primitives := C13Concrete.c13PrimitivesConcrete` in
`ProofCore.lean`), whose hashing is the same pure `KeccakEngine.keccak256`
the Verity interpreter uses, so no opaque primitive axiom remains on the C13
side.

Their `#print axioms` output is Lean's core axioms (`propext`,
`Classical.choice`, `Quot.sound`) plus exactly three residual assembly
axioms, all declared in `Proofs.lean`:

1. `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0`
2. `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1`
3. `c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual`

Each is a model-to-spec proof obligation at the lightweight WOTS
public-key recomputation cutpoint inside the hypertree climb: it pins an
already-verified generic chain lemma (see `C13WotsPkKeccak.lean` and
`C13ChainCells.lean`) to the concrete interpreter state at the
`beforeAuthOff` cut. They are proof debt inside the Lean development, not
claims about source-to-model transcription fidelity. Discharging them is
tracked in issue #7; work-in-progress proofs toward that live on the
`wip/axiom-discharge` branch.

## SLH-DSA-SHA2-128-24

The SHA-2 verifier body calls the SHA-256 precompile (`staticcall` to
`0x02`), which the interpreter does not model, so its accept path cannot yet
be replayed by the interpreter. Two axioms remain:

1. `slhDsaSha2_128_24_refines_byte_spec` (`Proofs.lean`): the
   MODEL-EXEC-BRIDGE axiom stating the SHA-2 Verity model refines
   `ByteLevel.verifyBytes` for the `slhDsaSha2_128_24` variant. Two slices
   are proved unconditionally and do not rest on this axiom: the
   malformed-length subdomain (`*_interp_agrees_verifyBytes_bad_length`) and
   the length-guard pass-through (`*VerifyBody_passes_length_guard` in
   `Model.lean`).
2. `slhDsaSha2_128_24_Primitives` (`ProofCore.lean`): the primitive package
   (SHA-256 based hashing) is taken as an opaque constant.

## Out of scope (assumptions, not Lean axioms)

Cryptographic security is not part of the trust surface above because it is
not formalized at all: nothing here states or assumes EUF-CMA security or
hash collision resistance as a Lean axiom. The theorems establish
implementation correctness only: the modeled verifier computes exactly the
SPHINCS- / SLH-DSA verification algorithm's verdict. Whether that algorithm
is secure is a cryptographic assumption outside this development, as is the
fidelity of the hand transcription from Solidity assembly to the Verity
model.
