// SPDX-License-Identifier: MIT
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

    error NotSelfOrEntryPoint();
    error NotEntryPoint();

    constructor(
        IEntryPoint ep,
        address _owner,
        address _verifier,
        bytes32 _pkSeed,
        bytes32 _pkRoot
    ) {
        _entryPoint = ep;
        verifier = _verifier;
        owner = _owner;
        pkSeed = _pkSeed;
        pkRoot = _pkRoot;
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
        require(msg.sender == address(this) || msg.sender == address(entryPoint()), NotSelfOrEntryPoint());
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
    function _validateSignature(
        PackedUserOperation calldata userOp,
        bytes32 userOpHash
    ) internal view override returns (uint256 validationData) {
        (bytes memory ecdsaSig, bytes memory sphincsSig) = abi.decode(
            userOp.signature,
            (bytes, bytes)
        );

        // 1. Verify ECDSA
        address recovered = userOpHash.recover(ecdsaSig);
        if (recovered != owner) {
            return SIG_VALIDATION_FAILED;
        }

        // 2. Verify SPHINCS+ via shared verifier
        (bool success, bytes memory result) = verifier.staticcall(
            abi.encodeWithSignature(
                "verify(bytes32,bytes32,bytes32,bytes)",
                pkSeed, pkRoot, userOpHash, sphincsSig
            )
        );
        if (!success || result.length < 32) {
            return SIG_VALIDATION_FAILED;
        }
        bool valid = abi.decode(result, (bool));
        if (!valid) {
            return SIG_VALIDATION_FAILED;
        }

        return SIG_VALIDATION_SUCCESS;
    }

    receive() external payable {}
}
