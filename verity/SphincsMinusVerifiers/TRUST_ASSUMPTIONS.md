# Trust Assumptions

Status date: 2026-06-11

## In Scope

- Model-to-byte-spec correspondence for the C13 keccak verifier.
- Model-to-byte-spec correspondence for the SLH-DSA-SHA2-128-24 verifier, subject to its SHA-256 precompile and packed-memory blockers.
- Public-key canonicality guards for both modeled verifiers.

## Out Of Scope

- C7 and C9 Verity models.
- Legacy verifier models.
- Older kernel or generated artifact workflows.
- Mechanical Solidity-to-Verity import fidelity. The current models are hand-transcribed.
- Foundry replay of Lean models. Foundry tests exercise Solidity, not the Lean model tree.

## Soundness Note

A Lean refinement theorem proves a property of the Verity model against the Lean spec. It does not by itself prove that the model is byte-for-byte imported from Solidity assembly.
