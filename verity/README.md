# Formal Verification (Verity / Lean 4)

This directory contains a small Verity workbench that hand-models two of the
production verifiers in `src/` and proves that each model refines a
functional spec. The workbench is not a build artefact for the production
contracts and is not exercised by Foundry.

## Scope

The Verity models cover only:

- `src/SPHINCs-C13Asm.sol` (keccak; the main production verifier).
- `src/SLH-DSA-SHA2-128-24verifier.sol` (FIPS 205 external SLH-DSA, empty
  context, SHA-256 precompile).

The other live production verifiers, `src/SPHINCs-C7Asm.sol` and
`src/SPHINCs-C9Asm.sol`, are **not** modeled and **not** verified here. They
should be treated as unverified code.

The C12 Verity model has been removed: C12 lives in `legacy/` and is no
longer a production verifier. The old `SphincsC6/`, `SphincsC6Full/`,
`SphincsC6V/`, and `SphincsKernel/` work, the `verity/artifacts/` Yul
artefacts, and `test/MerkleKernelVerityTest.t.sol` have been removed from
this tree.

## What the models are, and what they are not

The models in `SphincsMinusVerifiers/Model.lean` are hand-transcribed from
the Solidity inline assembly. They mirror the handwritten assembly
structure (stacks, memory, and Yul revert fragments) and use Verity's
ABI-aware `Bytes` parameter locals (`sig.length`, `sig.offset`).

- The models are **not** compiled into the production contracts.
- The models are **not** deployed.
- The models are **not** replayed in the Foundry test suite. There is no
  EVM-side regression test that takes the Lean model and runs it against
  the on-chain verifier.
- The proof target is model-to-byte-spec correspondence inside Lean.
  Correspondence between the model and the deployed code rests on the
  transcription itself being reviewed against the assembly.

The C13 model includes the public-key canonicality guard from the
Solidity: `pkSeed` and `pkRoot` must each equal themselves masked by
`N_MASK`, otherwise the verifier reverts with `Invalid public key`. The
SHA-2 model has the same public-key guard.

## File map

- `SphincsMinusVerifierSpec/Spec.lean`: the byte-level contract spec
  (`ByteLevel.verifyBytes`) and the abstract algorithmic spec
  (`verifyParsed`, `verifySpec`). The byte spec refines the algorithmic
  spec unconditionally: `verifyBytes_eq_verifySpec` and
  `byteVerifier_refines_spec` are proved with no assumptions beyond
  `propext`.
- `SphincsMinusVerifierSpec/C13Concrete.lean` and `C13Mirror.lean` (plus
  the matching `Axioms` files): the hand-coded `Primitives` instances and
  concrete FORS / hypertree arithmetic that the algorithmic spec is
  checked against.
- `SphincsMinusVerifiers/Model.lean`: the hand-transcribed Verity models
  for the C13 keccak verifier and the SLH-DSA-SHA2-128-24 verifier.
- `SphincsMinusVerifiers/Proofs.lean`: the per-verifier refinement
  surface, with `c13_refines_spec` and
  `slhDsaSha2_128_24_refines_spec` as the top-level theorems.
- `SphincsMinusVerifiers/AXIOMS.md`: the full trust surface (every
  named bridge axiom, opaque primitive, and residual assembly axiom).

## Proof state

- `c13_refines_spec` is currently proved in Lean and rests on Lean's
  logic plus three named residual assembly axioms, all enumerated in
  `SphincsMinusVerifiers/AXIOMS.md`. The keccak hashing in the C13
  model is concrete (the interpreter's own pure Keccak), so no opaque
  primitive axiom remains on the C13 side. A follow-up PR is
  discharging the residual assembly axioms; once it lands,
  `c13_refines_spec` will rest on Lean's logic alone.
- `slhDsaSha2_128_24_refines_spec` is proved in Lean but additionally
  keeps a named bridge axiom for byte-addressed memory modeling (the
  SHA-256 precompile path uses overlapping sub-word `mstore`s that the
  current word-keyed interpreter does not represent) and an opaque
  SHA-256 primitives constant.

This README is worded so the scope above stays true in both proof states:
as of today, and after the residual assembly obligations are discharged.
The exhaustive list of named assumptions is in
`SphincsMinusVerifiers/AXIOMS.md`.

## Build

```bash
cd verity
./scripts/build.sh
```

Always use `verity/scripts/build.sh`, not a bare `lake build`. The
proof modules here are large (a single Lean worker on `Proofs.lean` can
peak at several GB), and a bare `lake build` schedules one worker per
core, which OOMs on machines with 16 to 32 GB of RAM. The script caps
the Lean task pool at 2 workers via `LEAN_NUM_THREADS`; `lakefile.lean`
sets `maxHeartbeats 1000000` so a runaway `whnf` aborts as an error
instead of OOMing the machine. Several proof files were authored on
large cloud machines and exceed 12 GB per worker if a defeq diverges.

Do **not** run `lake build` or `lean` directly on hosts with less than
64 GB of RAM. Use the script; do not bypass it.
