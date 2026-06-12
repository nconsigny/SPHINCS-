# C13 Interface Contract

This file records the segment map for the modeled C13 verifier. It is derived from `c13VerifyBody` in `Model.lean` and the live Solidity assembly in `src/SPHINCs-C13Asm.sol`.

## Preflight

The C13 body starts with:

1. Signature length guard for `3688` bytes.
2. Public-key canonicality guard for `pkSeed` and `pkRoot` using `N_MASK`.

Only after both guards pass does execution enter `c13VerifyBodyTail`.

## Body Shape

The body then performs Hmsg keccak, FORS+C reconstruction, FORS root compression, the two-layer WOTS+C and XMSS climb, final root comparison, and boolean return.

## Scope

This contract applies only to the C13 Verity model. SHA2 has a separate model shape because it uses SHA-256 precompile calls and packed memory offsets.
