// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "./helpers/SoundnessGates.sol";
import "../src/keccak/SPHINCs-C9Asm.sol";

contract SphincsC9Test is SoundnessGates {
    SphincsC9Asm verifier;

    function setUp() public {
        verifier = new SphincsC9Asm();
    }

    function testC9VerifyFFI() public {
        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c9";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";

        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));

        bool valid = verifier.verify(pkSeed, pkRoot, message, sig);
        assertTrue(valid, "C9 signature should be valid");

        // Both soundness gates return false rather than reverting. Forced-zero field
        // and(shr(120, dVal), 0xFFF); layer-0 count at HT_START 2112 + 43*16 = 2800.
        _checkSoundnessGatesReturnFalse(address(verifier), pkSeed, pkRoot, message, sig, 120, 0xFFF, 2800);

        uint256 gasBefore = gasleft();
        verifier.verify(pkSeed, pkRoot, message, sig);
        uint256 gasUsed = gasBefore - gasleft();
        emit log_named_uint("C9 verify gas", gasUsed);
    }
}
