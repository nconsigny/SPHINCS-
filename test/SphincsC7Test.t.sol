// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C7Asm.sol";

contract SphincsC7Test is Test {
    SphincsC7Asm verifier;

    function setUp() public {
        verifier = new SphincsC7Asm();
    }

    /// @dev End-to-end: a real C7 signature from the Python signer (now on the
    ///      FIPS 205 uncompressed ADRS + FORS leaf-binding) must verify under
    ///      the migrated verifier. Proves signer↔verifier byte-agreement.
    function testC7VerifyFFI() public {
        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c7";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";

        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));
        assertEq(sig.length, 3704, "C7 sig must be 3704 bytes");

        bool valid = verifier.verify(pkSeed, pkRoot, message, sig);
        assertTrue(valid, "C7 signature should be valid");

        uint256 gasBefore = gasleft();
        verifier.verify(pkSeed, pkRoot, message, sig);
        uint256 gasUsed = gasBefore - gasleft();
        emit log_named_uint("C7 verify gas", gasUsed);
    }
}
