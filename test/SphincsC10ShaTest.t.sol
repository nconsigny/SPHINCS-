// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SPHINCs-C10-SHA.sol";

/// @dev End-to-end FFI test for the SHA-256 / 22-byte-ADRSc "minimal twin" of C10.
///      Vectors from `script/signer.py c10-sha` (hash=sha2, adrs_mode=adrsc,
///      parse=msb). Proves signer↔verifier byte agreement on the SHA-2 layout —
///      the layout FIPS 205 §11.2 requires once you pick SHA-2, and the one
///      EthereumPhone/PQ1's SPHINCsC10Asm does not use (it swaps only the hash and
///      keeps the JARDIN 32-byte ADRS).
contract SphincsC10ShaTest is Test {
    SphincsC10ShaAsm verifier;

    bytes32 constant MSG = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SphincsC10ShaAsm();
        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c10-sha";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        (cachedSeed, cachedRoot, cachedSig) = abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }

    function _verifySilent(bytes32 seed, bytes32 r, bytes32 m, bytes memory s)
        internal view returns (bool ok)
    {
        (bool call_ok, bytes memory res) = address(verifier).staticcall(
            abi.encodeWithSelector(verifier.verify.selector, seed, r, m, s)
        );
        if (!call_ok || res.length < 32) return false;
        ok = abi.decode(res, (bool));
    }

    function testC10ShaVerifyValid() public view {
        assertEq(cachedSig.length, 4008, "C10-SHA sig must be 4008 bytes");
        assertTrue(verifier.verify(cachedSeed, cachedRoot, MSG, cachedSig), "should be valid");
    }

    function testC10ShaVerifyGas() public {
        uint256 g = gasleft();
        verifier.verify(cachedSeed, cachedRoot, MSG, cachedSig);
        emit log_named_uint("C10-SHA verify gas", g - gasleft());
    }

    function testC10ShaRejectsWrongMessage() public view {
        assertFalse(_verifySilent(cachedSeed, cachedRoot, bytes32(uint256(1)), cachedSig));
    }

    function testC10ShaRejectsWrongRoot() public view {
        assertFalse(_verifySilent(cachedSeed, bytes32(uint256(2) << 128), MSG, cachedSig));
    }

    /// @dev The keccak FIPS-uncompressed C10 and this SHA/ADRSc C10 share parameters
    ///      and signature length, so only the coupled hash+address change separates
    ///      them. A keccak-layout signature must not verify here.
    function testC10ShaRejectsKeccakLayoutSignature() public {
        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c10-fips";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        (bytes32 s, bytes32 r, bytes memory sig) = abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
        assertEq(sig.length, 4008, "same length, so the length check cannot be what rejects it");
        assertFalse(_verifySilent(s, r, MSG, sig), "keccak-layout sig must not verify here");
    }
}
