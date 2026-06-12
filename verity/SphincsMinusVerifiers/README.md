# SPHINCS- Verity Models

This folder is the Verity workbench for two modeled production verifiers:

- `SphincsC13Asm_VerityModel` models `src/SPHINCs-C13Asm.sol`.
- `SLH_DSA_SHA2_128_24_VerityModel` models `src/SLH-DSA-SHA2-128-24verifier.sol`.

Live Solidity also includes `SPHINCs-C7Asm.sol` and `SPHINCs-C9Asm.sol`; those are not modeled in this tree. Legacy verifier models and older kernel experiments have been removed from this workbench.

The models are hand-transcribed from handwritten Solidity assembly. They are not compiled into the production contracts, and Foundry tests do not replay the Lean models. The proof target is model-to-byte-spec correspondence inside Lean. Source-to-model fidelity remains a review and differential-testing assumption.

The C13 model includes the public-key canonicality guard from Solidity: `pkSeed` and `pkRoot` must equal themselves masked by `N_MASK`, otherwise the verifier reverts with `Invalid public key`. The SHA2 model has the same public-key guard.

`Proofs.lean` contains the C13 and SHA2 refinement surface. SHA2 remains blocked on precise SHA-256 precompile and packed memory semantics.

## Residual assembly axioms

The C13 proof chain carries three named residual assembly axioms in `Proofs.lean`, each pinning an already-verified generic WOTS chain lemma to a concrete interpreter state at the lightweight cutpoint. They are enumerated, with the rest of the trust surface, in `AXIOMS.md`. Discharging them is tracked in issue #7.
