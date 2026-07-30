// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SPHINCs-C13-SHA.sol";

/// @dev End-to-end FFI test for the SHA-256 / 22-byte-ADRSc "minimal twin" of C13.
///      Vectors from script/signer.py c13-sha (hash=sha2, adrs_mode=adrsc, parse=msb).
///      NOTE: signing C13 is slow (~minutes: a=19 ⇒ 2^19 FORS leaves × 7 trees in Python).
contract SphincsC13ShaTest is Test {
    SphincsC13ShaAsm verifier;

    bytes32 constant MSG = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SphincsC13ShaAsm();
        string[] memory full = new string[](4);
        full[0] = "python3";
        full[1] = "script/signer.py";
        full[2] = "c13-sha";
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

    function testC13ShaVerifyValid() public view {
        assertEq(cachedSig.length, 3688, "C13-SHA sig must be 3688 bytes");
        assertTrue(_verifySilent(cachedSeed, cachedRoot, MSG, cachedSig), "C13-SHA signature should be valid");
    }

    function testC13ShaVerifyGas() public {
        uint256 g = gasleft();
        verifier.verify(cachedSeed, cachedRoot, MSG, cachedSig);
        emit log_named_uint("C13-SHA verify gas", g - gasleft());
    }

    function testC13ShaRejectsWrongMessage() public view {
        bytes32 wrong = bytes32(uint256(MSG) ^ 1);
        assertFalse(_verifySilent(cachedSeed, cachedRoot, wrong, cachedSig), "wrong message must not verify");
    }

    function testC13ShaRejectsWrongRoot() public view {
        bytes32 wrongRoot = bytes32(uint256(cachedRoot) ^ (1 << 200));
        assertFalse(_verifySilent(cachedSeed, wrongRoot, MSG, cachedSig), "wrong root must not verify");
    }
}
