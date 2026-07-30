// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "account-abstraction/core/BaseAccount.sol";
import "account-abstraction/core/Helpers.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

/// @title SphincsAccount - Hybrid ECDSA + SPHINCS+ account using a SHARED verifier
/// @notice Keys stored in storage (not immutable) to support future key rotation.
///         The shared verifier is deployed once and used by all accounts.
contract SphincsAccount is BaseAccount {
    using ECDSA for bytes32;

    IEntryPoint private immutable _entryPoint;
    address public immutable verifier;       // Shared verifier (same for all users)
    address public owner;                    // ECDSA signer (rotatable)
    bytes32 public pkSeed;                   // SPHINCS+ public seed (rotatable)
    bytes32 public pkRoot;                   // SPHINCS+ Merkle root (rotatable)

    /// @dev n=16 key shape: the 16-byte pkSeed / pkRoot occupy the TOP half of
    ///      each word, low 128 bits zero — the same mask every verifier and the
    ///      signer applies.
    bytes32 private constant N_MASK =
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000;

    error NotSelfOrEntryPoint();
    error NotEntryPoint();
    error NonCanonicalKey();

    constructor(
        IEntryPoint ep,
        address _owner,
        address _verifier,
        bytes32 _pkSeed,
        bytes32 _pkRoot
    ) {
        _requireCanonicalKey(_pkSeed, _pkRoot);
        _entryPoint = ep;
        verifier = _verifier;
        owner = _owner;
        pkSeed = _pkSeed;
        pkRoot = _pkRoot;
    }

    /// @dev Reject a non-canonical key at the point it would be COMMITTED, not
    ///      just when it is used. Every verifier reverts on a non-top-aligned
    ///      pkSeed/pkRoot, so storing one permanently bricks the account:
    ///      recovery would have to run `rotateKeys` through `execute` →
    ///      EntryPoint → `_validateSignature`, and that path can never pass
    ///      again once the stored key is unusable. Validating here also keeps
    ///      `SphincsAccountFactory`'s CREATE2 salt canonical, so one logical key
    ///      maps to exactly one account address.
    function _requireCanonicalKey(bytes32 _pkSeed, bytes32 _pkRoot) private pure {
        require(
            (_pkSeed & N_MASK) == _pkSeed && (_pkRoot & N_MASK) == _pkRoot,
            NonCanonicalKey()
        );
    }

    function entryPoint() public view override returns (IEntryPoint) {
        return _entryPoint;
    }

    /// @notice Only the EntryPoint can drive `execute` / `executeBatch`.
    /// @dev    Direct owner-EOA calls are intentionally forbidden so that the
    ///         hybrid ECDSA + SPHINCS+ check in `_validateSignature` cannot be
    ///         bypassed. Without this, a leaked/broken ECDSA key alone would
    ///         authorize execution and reach `rotateKeys`/`rotateOwner` via
    ///         the `address(this)` self-call branch.
    function _requireForExecute() internal view override {
        require(msg.sender == address(entryPoint()), NotEntryPoint());
    }

    /// @notice Rotate SPHINCS+ keys. Can only be called by the account itself
    ///         (via execute) or by the EntryPoint during a UserOp.
    function rotateKeys(bytes32 newPkSeed, bytes32 newPkRoot) external {
        // Authorization first, so an unauthorized caller always gets
        // NotSelfOrEntryPoint regardless of the key shape it passed.
        require(msg.sender == address(this) || msg.sender == address(entryPoint()), NotSelfOrEntryPoint());
        _requireCanonicalKey(newPkSeed, newPkRoot);
        pkSeed = newPkSeed;
        pkRoot = newPkRoot;
    }

    /// @notice Rotate ECDSA owner.
    function rotateOwner(address newOwner) external {
        require(msg.sender == address(this) || msg.sender == address(entryPoint()), NotSelfOrEntryPoint());
        require(newOwner != address(0));
        owner = newOwner;
    }

    /// @notice Validate hybrid signature: abi.encode(ecdsaSig, sphincsSig)
    /// @dev ERC-4337 requires `_validateSignature` to be TOTAL: any signature
    ///      failure must RETURN `SIG_VALIDATION_FAILED`, never revert (a revert
    ///      becomes EntryPoint `AA23` and reverts the whole bundle). Two former
    ///      revert paths are made total here (review C13-acc-g1):
    ///        (1) `abi.decode` of a malformed `userOp.signature` — wrapped in
    ///            try/catch via `decodeHybridSignature`;
    ///        (2) ECDSA recovery on a bad-length / high-`s` / bad-`v` signature —
    ///            switched from the reverting `recover` to `tryRecover`.
    function _validateSignature(
        PackedUserOperation calldata userOp,
        bytes32 userOpHash
    ) internal view override returns (uint256 validationData) {
        // (1) Total decode: a malformed 2-tuple must fail validation, not revert.
        try this.decodeHybridSignature(userOp.signature)
            returns (bytes memory ecdsaSig, bytes memory sphincsSig)
        {
            // (2) Verify ECDSA via tryRecover (no revert on bad length/v/high-s).
            (address recovered, ECDSA.RecoverError err, ) =
                ECDSA.tryRecover(userOpHash, ecdsaSig);
            if (err != ECDSA.RecoverError.NoError || recovered != owner) {
                return SIG_VALIDATION_FAILED;
            }

            // (3) Verify SPHINCS+ via shared verifier.
            (bool success, bytes memory result) = verifier.staticcall(
                abi.encodeWithSignature(
                    "verify(bytes32,bytes32,bytes32,bytes)",
                    pkSeed, pkRoot, userOpHash, sphincsSig
                )
            );
            if (!success || result.length < 32) {
                return SIG_VALIDATION_FAILED;
            }
            if (!abi.decode(result, (bool))) {
                return SIG_VALIDATION_FAILED;
            }
            return SIG_VALIDATION_SUCCESS;
        } catch {
            return SIG_VALIDATION_FAILED;
        }
    }

    /// @notice External helper so `abi.decode((bytes,bytes))` of the hybrid
    ///         signature blob can be wrapped in try/catch (a malformed blob then
    ///         yields `SIG_VALIDATION_FAILED` instead of a revert). Pure; callable
    ///         only as `this.decodeHybridSignature(...)` from `_validateSignature`.
    function decodeHybridSignature(bytes calldata sigBlob)
        external pure returns (bytes memory ecdsaSig, bytes memory sphincsSig)
    {
        (ecdsaSig, sphincsSig) = abi.decode(sigBlob, (bytes, bytes));
    }

    receive() external payable {}
}
