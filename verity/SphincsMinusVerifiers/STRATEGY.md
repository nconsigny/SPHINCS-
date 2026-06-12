# Strategy

The active strategy is to keep the Verity model tree aligned with the live production verifier set while modeling only the two verifier families currently in scope:

- C13 keccak, modeled from `src/SPHINCs-C13Asm.sol`.
- SLH-DSA-SHA2-128-24, modeled from `src/SLH-DSA-SHA2-128-24verifier.sol`.

C7 and C9 are live Solidity contracts but are not modeled here. Legacy verifier and kernel work have been removed.

The Lean work should continue to distinguish three boundaries:

1. Solidity assembly to hand-transcribed Verity model. This is reviewed manually and is not closed by Lean.
2. Verity model to `ByteLevel.verifyBytes`. This is the model-to-byte-spec proof obligation.
3. `ByteLevel.verifyBytes` to the algorithmic verifier spec. This is the abstract-spec layer.

Future proof work should prioritize the C13 public-key guard, the C13 accept path, and the SHA2 precompile and packed-memory blockers.
