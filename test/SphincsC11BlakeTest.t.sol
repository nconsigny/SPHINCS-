// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/blake/SPHINCs-C11-BLAKE.sol";

/// @dev End-to-end test of the BLAKE2b C11 verifier against script/signer.py c11-blake.
contract SphincsC11BlakeTest is Test {
    SphincsC11BlakeAsm verifier;

    bytes32 constant MSG = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SphincsC11BlakeAsm();

        string[] memory full = new string[](4);
        full[0] = "python3";
        full[1] = "script/signer.py";
        full[2] = "c11-blake";
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

    function testC11BlakeVerifyValid() public view {
        assertEq(cachedSig.length, 3976, "sig length");
        assertTrue(_verifySilent(cachedSeed, cachedRoot, MSG, cachedSig), "valid sig must verify");
    }

    function testC11BlakeVerifyGas() public {
        uint256 g = gasleft();
        bool ok = _verifySilent(cachedSeed, cachedRoot, MSG, cachedSig);
        uint256 used = g - gasleft();
        assertTrue(ok);
        emit log_named_uint("C11-BLAKE verify gas", used);
    }

    function testC11BlakeRejectsWrongMessage() public view {
        assertFalse(_verifySilent(cachedSeed, cachedRoot, bytes32(uint256(MSG) ^ 1), cachedSig), "wrong msg must reject");
    }

    function testC11BlakeRejectsWrongRoot() public view {
        assertFalse(_verifySilent(cachedSeed, bytes32(uint256(cachedRoot) ^ 1), MSG, cachedSig), "wrong root must reject");
    }
}
