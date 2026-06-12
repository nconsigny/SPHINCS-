# Verity Audit

Status date: 2026-06-11

## Scope

The modeled verifier set is limited to C13 keccak and SLH-DSA-SHA2-128-24. C7 and C9 are live Solidity contracts but are not modeled in Verity.

## Current Trust Surface

- The C13 model is hand-transcribed from `src/SPHINCs-C13Asm.sol`.
- The SHA2 model is hand-transcribed from `src/SLH-DSA-SHA2-128-24verifier.sol`.
- The models are not contract outputs and are not replayed by Foundry.
- Source-to-model fidelity remains outside Lean unless a future importer is added.

## Guard Audit

C13 and SHA2 both reject non-canonical public keys with `Invalid public key`. The C13 model now threads the length guard into the public-key guard tail before entering the algorithmic body.

## Removed Scope

Legacy verifier models and the old kernel workbench are no longer part of this tree.
