// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "account-abstraction/interfaces/IEntryPoint.sol";
import "./SphincsAccount.sol";

/// @title SphincsAccountFactory - Factory using a SHARED verifier for all accounts
/// @notice Deploys only the account contract (not a per-user verifier).
///         The shared SphincsC6Shared verifier is deployed once and its address
///         is set in the factory constructor.
contract SphincsAccountFactory {
    IEntryPoint public immutable entryPoint;
    address public immutable sharedVerifier;  // SphincsC6Shared — deployed once

    event AccountCreated(address indexed account, address indexed owner);

    constructor(IEntryPoint _entryPoint, address _sharedVerifier) {
        entryPoint = _entryPoint;
        sharedVerifier = _sharedVerifier;
    }

    error ZeroOwner();
    error NonCanonicalKey();
    error ZeroRoot();

    /// @dev Low half of a 32-byte word; n=16 keys are top-aligned, so it must be zero.
    bytes32 private constant N_MASK_LOW = bytes32(uint256(type(uint128).max));

    /// @dev The same rules `SphincsAccount`'s constructor enforces. Checking them in
    ///      `getAddress` too means the factory never predicts an address it can never
    ///      deploy (funds sent there would be stranded).
    ///      (review factory-undeployable-prediction-nonidempotent)
    function _check(address ecdsaOwner, bytes32 pkSeed, bytes32 pkRoot) private pure {
        require(ecdsaOwner != address(0), ZeroOwner());
        require(pkRoot != 0, ZeroRoot());
        require(((pkSeed | pkRoot) & N_MASK_LOW) == 0, NonCanonicalKey());
    }

    /// @notice Create a new hybrid account, or return it if it already exists.
    /// @dev Idempotent like the reference `SimpleAccountFactory`: a second call (or a
    ///      call that lost a race, since anyone can deploy any tuple) returns the
    ///      existing account instead of reverting, so EntryPoint `getSenderAddress`
    ///      with this initCode keeps working after deployment. The returned account may
    ///      have rotated its keys or owner since it was created.
    /// @param ecdsaOwner The ECDSA signer address
    /// @param pkSeed SPHINCS+ public seed
    /// @param pkRoot SPHINCS+ Merkle root
    function createAccount(
        address ecdsaOwner,
        bytes32 pkSeed,
        bytes32 pkRoot
    ) external returns (SphincsAccount account) {
        address addr = getAddress(ecdsaOwner, pkSeed, pkRoot);
        if (addr.code.length > 0) return SphincsAccount(payable(addr));

        bytes32 salt = keccak256(abi.encodePacked(ecdsaOwner, pkSeed, pkRoot));
        account = new SphincsAccount{salt: salt}(
            entryPoint, ecdsaOwner, sharedVerifier, pkSeed, pkRoot
        );

        emit AccountCreated(address(account), ecdsaOwner);
    }

    /// @notice Counterfactual address of `createAccount(ecdsaOwner, pkSeed, pkRoot)`.
    ///         Reverts for a tuple the account constructor would reject.
    function getAddress(
        address ecdsaOwner,
        bytes32 pkSeed,
        bytes32 pkRoot
    ) public view returns (address) {
        _check(ecdsaOwner, pkSeed, pkRoot);
        bytes32 salt = keccak256(abi.encodePacked(ecdsaOwner, pkSeed, pkRoot));
        bytes32 hash = keccak256(abi.encodePacked(
            type(SphincsAccount).creationCode,
            abi.encode(entryPoint, ecdsaOwner, sharedVerifier, pkSeed, pkRoot)
        ));
        return address(uint160(uint256(keccak256(abi.encodePacked(
            bytes1(0xff), address(this), salt, hash
        )))));
    }
}
