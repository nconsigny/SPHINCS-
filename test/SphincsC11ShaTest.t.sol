// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SPHINCs-C11-SHA.sol";

/// @dev End-to-end FFI test for the SHA-256 / 22-byte-ADRSc "minimal twin" of C11.
///      Vectors from script/signer.py c11-sha (hash=sha2, adrs_mode=adrsc, parse=msb).
///      Proves signer↔verifier byte agreement on the SHA-2 instantiation.
contract SphincsC11ShaTest is Test {
    SphincsC11ShaAsm verifier;

    bytes32 constant MSG = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SphincsC11ShaAsm();
        string[] memory inputs = new string[](3);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c11-sha";
        // signer.py takes (variant, message_hex)
        string[] memory full = new string[](4);
        full[0] = inputs[0];
        full[1] = inputs[1];
        full[2] = inputs[2];
        full[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        bytes memory result = vm.ffi(full);
        (cachedSeed, cachedRoot, cachedSig) = abi.decode(result, (bytes32, bytes32, bytes));
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

    function testC11ShaVerifyValid() public view {
        assertEq(cachedSig.length, 3976, "C11-SHA sig must be 3976 bytes");
        assertTrue(_verifySilent(cachedSeed, cachedRoot, MSG, cachedSig), "C11-SHA signature should be valid");
    }

    function testC11ShaVerifyGas() public {
        uint256 g = gasleft();
        verifier.verify(cachedSeed, cachedRoot, MSG, cachedSig);
        emit log_named_uint("C11-SHA verify gas", g - gasleft());
    }

    function testC11ShaRejectsWrongMessage() public view {
        bytes32 wrong = bytes32(uint256(MSG) ^ 1);
        assertFalse(_verifySilent(cachedSeed, cachedRoot, wrong, cachedSig), "wrong message must not verify");
    }

    function testC11ShaRejectsWrongRoot() public view {
        bytes32 wrongRoot = bytes32(uint256(cachedRoot) ^ (1 << 200));
        assertFalse(_verifySilent(cachedSeed, wrongRoot, MSG, cachedSig), "wrong root must not verify");
    }
}
