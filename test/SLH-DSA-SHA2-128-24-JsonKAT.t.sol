// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SLH-DSA-SHA2-128-24verifier.sol";

/// @notice JSON-fixture Known-Answer Test for the FIPS 205 EXTERNAL
///         SLH-DSA-SHA2-128-24 verifier (empty context, M wrapped as 0x00 0x00 || M).
///         Loads the pinned DETERMINISTIC (counter-mode) vector from
///         `signers/slhvk-sha2-128-24/kat-counter0.json` via vm.readFile +
///         vm.parseJson and asserts a freshly-deployed verifier accepts it.
///         The vector was produced by the Vulkan GPU signer (bit-exact vs the
///         sphincsplus-128-24 CPU reference); reproduce with the fixture's
///         `reproduce` field. This is the machine-readable companion to the
///         inline SLH-DSA-SHA2-128-24-KAT.t.sol: it guards the verifier against
///         silent signer/FIPS co-drift AND keeps the JSON fixture itself honest.
///         Requires fs read access to the fixture (see `fs_permissions` in
///         foundry.toml).
contract SLH_DSA_SHA2_128_24_JsonKAT_Test is Test {
    SLH_DSA_SHA2_128_24_Verifier verifier;
    string constant FIXTURE = "signers/slhvk-sha2-128-24/kat-counter0.json";

    function setUp() public {
        verifier = new SLH_DSA_SHA2_128_24_Verifier();
    }

    function _load()
        internal
        view
        returns (bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig)
    {
        string memory json = vm.readFile(FIXTURE);
        pkSeed  = vm.parseJsonBytes32(json, ".public_key.pkSeed");
        pkRoot  = vm.parseJsonBytes32(json, ".public_key.pkRoot");
        message = vm.parseJsonBytes32(json, ".inputs.message_M");
        sig     = vm.parseJsonBytes(json, ".signature");
    }

    /// The pinned JSON vector must verify, and its self-described length /
    /// expectation must be internally consistent (catches a tampered fixture).
    function testJsonKatVerifies() public view {
        (bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig) = _load();
        string memory json = vm.readFile(FIXTURE);
        uint256 sigLen = vm.parseJsonUint(json, ".signature_len");
        bool expected  = vm.parseJsonBool(json, ".verify_expected");

        assertEq(sig.length, sigLen, "fixture signature_len mismatch");
        assertEq(sig.length, 3856, "SLH-DSA-SHA2-128-24 sig must be 3856 B");
        assertEq(verifier.verify(pkSeed, pkRoot, message, sig), expected, "JSON KAT must verify");
    }

    /// A one-bit flip in the message must be rejected (guards an accept-all bug).
    function testJsonKatRejectsWrongMessage() public view {
        (bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig) = _load();
        bytes32 wrong = bytes32(uint256(message) ^ 1);
        assertFalse(verifier.verify(pkSeed, pkRoot, wrong, sig), "wrong message must not verify");
    }
}
