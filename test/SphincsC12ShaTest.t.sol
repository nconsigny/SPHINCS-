// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SPHINCs-C12-SHA.sol";

/// @dev End-to-end FFI test for C12-SHA: full FIPS 205 SLH-DSA-SHA2 at C12 params
///      (n=16 h=20 d=5 a=7 k=20 w=8). MGF1 H_msg + 0x00 0x00 envelope, MSB-first
///      base_2b. Vectors from script/slh_dsa_sha2_c12_signer.py. Signs fast (small
///      trees: h'=4, a=7).
contract SphincsC12ShaTest is Test {
    SPHINCs_C12ShaAsm verifier;

    bytes32 constant MSG = 0xdeadbeef00000000000000000000000000000000000000000000000000000000;
    bytes32 constant SK  = 0x1111111111111111111111111111111111111111111111111111111111111111;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SPHINCs_C12ShaAsm();
        string[] memory full = new string[](4);
        full[0] = "python3";
        full[1] = "script/slh_dsa_sha2_c12_signer.py";
        full[2] = vm.toString(SK);
        full[3] = vm.toString(MSG);
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

    function testC12ShaVerifyValid() public view {
        assertEq(cachedSig.length, 6496, "C12-SHA sig must be 6496 bytes");
        assertTrue(_verifySilent(cachedSeed, cachedRoot, MSG, cachedSig), "C12-SHA signature should be valid");
    }

    function testC12ShaVerifyGas() public {
        uint256 g = gasleft();
        verifier.verify(cachedSeed, cachedRoot, MSG, cachedSig);
        emit log_named_uint("C12-SHA verify gas", g - gasleft());
    }

    function testC12ShaRejectsWrongMessage() public view {
        bytes32 wrong = bytes32(uint256(MSG) ^ 1);
        assertFalse(_verifySilent(cachedSeed, cachedRoot, wrong, cachedSig), "wrong message must not verify");
    }

    function testC12ShaRejectsWrongRoot() public view {
        bytes32 wrongRoot = bytes32(uint256(cachedRoot) ^ (1 << 200));
        assertFalse(_verifySilent(cachedSeed, wrongRoot, MSG, cachedSig), "wrong root must not verify");
    }
}
