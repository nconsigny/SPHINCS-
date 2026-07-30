// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/blake/SPHINCs-C12-BLAKE.sol";

/// @dev End-to-end test of the BLAKE2b plain-SPHINCS+ C12 verifier against its
///      signer script/spx_blake_signer.py. Mirrors SphincsC12Test.
contract SphincsC12BlakeTest is Test {
    SPHINCs_C12BlakeAsm verifier;

    bytes32 constant MSG = 0xdeadbeef00000000000000000000000000000000000000000000000000000000;
    bytes32 constant SK  = 0x1111111111111111111111111111111111111111111111111111111111111111;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SPHINCs_C12BlakeAsm();

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/spx_blake_signer.py";
        inputs[2] = vm.toString(SK);
        inputs[3] = vm.toString(MSG);
        bytes memory result = vm.ffi(inputs);
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

    function testC12BlakeVerifyValid() public view {
        assertEq(cachedSig.length, 6512, "sig length");
        assertTrue(_verifySilent(cachedSeed, cachedRoot, MSG, cachedSig), "valid sig must verify");
    }

    function testC12BlakeVerifyGas() public {
        uint256 g = gasleft();
        bool ok = _verifySilent(cachedSeed, cachedRoot, MSG, cachedSig);
        uint256 used = g - gasleft();
        assertTrue(ok);
        emit log_named_uint("C12-BLAKE verify gas", used);
    }

    function testC12BlakeRejectsWrongMessage() public view {
        assertFalse(_verifySilent(cachedSeed, cachedRoot, bytes32(uint256(MSG) ^ 1), cachedSig));
    }

    function testC12BlakeRejectsWrongRoot() public view {
        assertFalse(_verifySilent(cachedSeed, bytes32(uint256(cachedRoot) ^ 1), MSG, cachedSig));
    }
}
