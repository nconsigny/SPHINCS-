// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C10Asm.sol";

/// @dev End-to-end FFI test for C10 promoted out of legacy/ onto the FIPS 205 §4.2
///      uncompressed 32-byte ADRS + keccak256. Vectors from `script/signer.py
///      c10-fips`; the JARDIN-layout original is still covered separately by
///      legacy/test/SphincsC10Test.t.sol driven by `signer.py c10`, and the two must
///      NOT be fed each other's vectors.
contract SphincsC10Test is Test {
    SphincsC10Asm verifier;

    bytes32 constant MSG = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

    function setUp() public {
        verifier = new SphincsC10Asm();
    }

    function _sign(string memory variant)
        internal
        returns (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig)
    {
        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = variant;
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        (pkSeed, pkRoot, sig) = abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }

    function testC10VerifyFFI() public {
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = _sign("c10-fips");
        assertEq(sig.length, 4008, "C10 sig must be 4008 bytes");

        assertTrue(verifier.verify(pkSeed, pkRoot, MSG, sig), "C10 signature should be valid");

        uint256 gasBefore = gasleft();
        verifier.verify(pkSeed, pkRoot, MSG, sig);
        emit log_named_uint("C10 verify gas", gasBefore - gasleft());
    }

    function testC10RejectsWrongMessage() public {
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = _sign("c10-fips");
        // A different message re-derives htIdx and the FORS indices, so this dies on
        // the forced-zero or target-sum check (bare revert) or fails the root compare.
        (bool ok, bytes memory ret) = address(verifier).staticcall(
            abi.encodeCall(SphincsC10Asm.verify, (pkSeed, pkRoot, bytes32(uint256(1)), sig))
        );
        assertTrue(!ok || !abi.decode(ret, (bool)), "wrong message must not verify");
    }

    /// @dev The layouts really are distinct: a JARDIN-layout C10 signature (same
    ///      params, same 4008-byte length, so it clears the length check) must not
    ///      verify under the FIPS-layout verifier. This is the regression guard for
    ///      the mistake that orphaned legacy/test/SphincsC11Test.t.sol.
    function testC10RejectsJardinLayoutSignature() public {
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = _sign("c10");
        assertEq(sig.length, 4008, "legacy C10 sig is also 4008 bytes");

        (bool ok, bytes memory ret) = address(verifier).staticcall(
            abi.encodeCall(SphincsC10Asm.verify, (pkSeed, pkRoot, MSG, sig))
        );
        assertTrue(!ok || !abi.decode(ret, (bool)), "JARDIN-layout sig must not verify here");
    }

    function testC10RejectsNonCanonicalKey() public {
        bytes memory zeroSig = new bytes(4008);
        vm.expectRevert(bytes("Invalid public key"));
        verifier.verify(bytes32(uint256(1)), bytes32(uint256(2) << 128), MSG, zeroSig);
    }

    function testC10RejectsWrongLength() public {
        bytes memory shortSig = new bytes(3976); // C11's length
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128), MSG, shortSig);
    }
}
