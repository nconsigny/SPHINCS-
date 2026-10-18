// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/blake/SPHINCs-C13-BLAKE.sol";

/// @dev End-to-end test of the BLAKE2b C13 verifier against its Python signer
///      (script/signer.py c13-blake). Mirrors SphincsC13ShaTest.
contract SphincsC13BlakeTest is Test {
    SphincsC13BlakeAsm verifier;

    bytes32 constant MSG = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes cachedSig;

    function setUp() public {
        verifier = new SphincsC13BlakeAsm();

        string[] memory full = new string[](4);
        full[0] = "python3";
        full[1] = "script/signer.py";
        full[2] = "c13-blake";
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

    function testC13BlakeVerifyValid() public view {
        assertEq(cachedSig.length, 3688, "sig length");
        assertTrue(_verifySilent(cachedSeed, cachedRoot, MSG, cachedSig), "valid sig must verify");
    }

    function testC13BlakeVerifyGas() public {
        uint256 g = gasleft();
        bool ok = _verifySilent(cachedSeed, cachedRoot, MSG, cachedSig);
        uint256 used = g - gasleft();
        assertTrue(ok);
        emit log_named_uint("C13-BLAKE verify gas", used);
    }

    function testC13BlakeRejectsWrongMessage() public view {
        assertFalse(_verifySilent(cachedSeed, cachedRoot, bytes32(uint256(MSG) ^ 1), cachedSig), "wrong msg must reject");
    }

    /// @dev Flip a bit in the canonical (top) half of the root. A low-bit flip would make the
    ///      key non-canonical and stop at the "Invalid public key" guard instead.
    function testC13BlakeRejectsWrongRoot() public view {
        assertFalse(_verifySilent(cachedSeed, bytes32(uint256(cachedRoot) ^ (1 << 200)), MSG, cachedSig), "wrong root must reject");
    }

    function _flip(bytes memory s, uint256 pos) internal pure returns (bytes memory t) {
        t = bytes.concat(s);
        t[pos] = bytes1(uint8(t[pos]) ^ 0x01);
    }

    /// @dev Corruptions in the TOP hypertree layer leave H_msg and every earlier digest
    ///      unchanged, so they pass the forced-zero and target-sum gates and are caught only
    ///      by the final root comparison. (HT_START 1952; layer = 43*16 + 4 + 11*16 = 868.)
    function testC13BlakeRejectsCorruptedTopLayer() public view {
        assertFalse(_verifySilent(cachedSeed, cachedRoot, MSG, _flip(cachedSig, 3672)), "corrupted last auth node must reject");
        assertFalse(_verifySilent(cachedSeed, cachedRoot, MSG, _flip(cachedSig, 2820)), "corrupted top-layer WOTS chain must reject");
    }

    function testC13BlakeRevertsOnNonCanonicalKey() public {
        vm.expectRevert(bytes("Invalid public key"));
        verifier.verify(cachedSeed, bytes32(uint256(cachedRoot) | 1), MSG, cachedSig);
        vm.expectRevert(bytes("Invalid public key"));
        verifier.verify(bytes32(uint256(cachedSeed) | 1), cachedRoot, MSG, cachedSig);
    }
}
