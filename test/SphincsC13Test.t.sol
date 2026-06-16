// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C13Asm.sol";

contract SphincsC13Test is Test {
    SphincsC13Asm verifier;

    function setUp() public {
        verifier = new SphincsC13Asm();
    }

    /// @dev Heavy: the Python signer for C13 takes minutes (R-grind ≈ 2^19,
    ///      6 FORS trees of 2^19 leaves, 2 WOTS+C count grinds). The Rust CLI
    ///      under signer-wasm/target/release/signer-c13 is far faster and is
    ///      the recommended path; this test stays on Python for parity with
    ///      the C7/C11 test pattern.
    function testC13VerifyFFI() public {
        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c13";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";

        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));
        assertEq(sig.length, 3688, "C13 sig must be 3688 bytes");

        bool valid = verifier.verify(pkSeed, pkRoot, message, sig);
        assertTrue(valid, "C13 signature should be valid");

        uint256 gasBefore = gasleft();
        verifier.verify(pkSeed, pkRoot, message, sig);
        uint256 gasUsed = gasBefore - gasleft();
        emit log_named_uint("C13 verify gas", gasUsed);
    }

    /// @notice Same as above but uses the Rust CLI (much faster).
    ///         Skipped if the binary is not built. Build with:
    ///         (cd signer-wasm && cargo build --release --bin signer-c13)
    function testC13VerifyFFI_Rust() public {
        // Probe for the Rust CLI; skip if missing.
        string[] memory probe = new string[](3);
        probe[0] = "sh";
        probe[1] = "-c";
        probe[2] = "test -x signer-wasm/target/release/signer-c13 && echo yes || echo no";
        bytes memory probeOut = vm.ffi(probe);
        if (keccak256(probeOut) != keccak256(bytes("yes"))) {
            emit log("Skipping Rust-CLI test: signer-wasm/target/release/signer-c13 not built");
            return;
        }

        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](3);
        inputs[0] = "signer-wasm/target/release/signer-c13";
        inputs[1] = "c13";
        inputs[2] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";

        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));
        assertEq(sig.length, 3688, "C13 sig must be 3688 bytes");

        bool valid = verifier.verify(pkSeed, pkRoot, message, sig);
        assertTrue(valid, "C13 signature (from Rust CLI) should be valid");

        uint256 gasBefore = gasleft();
        verifier.verify(pkSeed, pkRoot, message, sig);
        uint256 gasUsed = gasBefore - gasleft();
        emit log_named_uint("C13 verify gas (rust sig)", gasUsed);
    }
}
