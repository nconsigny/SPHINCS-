// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SLH-DSA-SHA2-128-24verifier.sol";
import {SLH_DSA_SHA2_128_24_KAT_Test} from "./SLH-DSA-SHA2-128-24-KAT.t.sol";

/// Adversarial probe: does the 16-byte over-read at the end of the XMSS auth
/// path (verifier line 269) let trailing calldata influence the verdict?
contract AdvVerifyPaddingProbe is Test {
    SLH_DSA_SHA2_128_24_Verifier verifier;

    bytes32 constant MSG  = 0xdeadbeef00000000000000000000000000000000000000000000000000000000;
    bytes32 constant SEED = 0x750e7b30f37700dd14b20a5c647bb93600000000000000000000000000000000;
    bytes32 constant ROOT = 0x3456300211d2a77c26a60804b918738f00000000000000000000000000000000;

    bytes katSig;  // pinned KAT signature, fetched once in setUp from the KAT test contract

    function setUp() public {
        verifier = new SLH_DSA_SHA2_128_24_Verifier();
        katSig = new SLH_DSA_SHA2_128_24_KAT_Test().sigVector();
    }

    function _sig() internal view returns (bytes memory) {
        return katSig;
    }

    function _call(bytes memory raw) internal view returns (bool ok, bool result) {
        bytes memory res;
        (ok, res) = address(verifier).staticcall(raw);
        result = ok && res.length >= 32 && abi.decode(res, (bool));
    }

    function testPaddingBytesAreDeadInput() public view {
        bytes memory sig = _sig();
        assertEq(sig.length, 3856);
        bytes memory raw = abi.encodeWithSelector(verifier.verify.selector, SEED, ROOT, MSG, sig);
        // layout: 4 selector + 32*3 static + 32 offset + 32 length + 3856 data + 16 pad
        assertEq(raw.length, 4 + 32 * 4 + 32 + 3856 + 16, "expected ABI envelope size");

        (bool ok, bool r) = _call(raw);
        assertTrue(ok && r, "baseline KAT must verify");

        // Mutate ALL 16 trailing ABI padding bytes (calldata positions sig_end..sig_end+16)
        for (uint256 i = raw.length - 16; i < raw.length; i++) raw[i] = 0xFF;
        (ok, r) = _call(raw);
        assertTrue(ok && r, "padding bytes must be dead input (masked by N_MASK)");

        // Append 64 extra junk bytes after the envelope too
        bytes memory rawExt = bytes.concat(raw, hex"deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        (ok, r) = _call(rawExt);
        assertTrue(ok && r, "extra trailing calldata must be dead input");

        // Control: flip the LAST in-bounds sig byte (index 3855) -> must flip verdict
        bytes memory raw2 = abi.encodeWithSelector(verifier.verify.selector, SEED, ROOT, MSG, sig);
        uint256 lastSigBytePos = 4 + 32 * 4 + 32 + 3855;
        raw2[lastSigBytePos] = bytes1(uint8(raw2[lastSigBytePos]) ^ 0x01);
        (ok, r) = _call(raw2);
        assertTrue(ok && !r, "flipping last in-bounds sig byte must invalidate");

        // Control: flip first byte of the final XMSS sibling (sig offset 3840)
        bytes memory raw3 = abi.encodeWithSelector(verifier.verify.selector, SEED, ROOT, MSG, sig);
        uint256 sibPos = 4 + 32 * 4 + 32 + 3840;
        raw3[sibPos] = bytes1(uint8(raw3[sibPos]) ^ 0x01);
        (ok, r) = _call(raw3);
        assertTrue(ok && !r, "flipping in-bounds sibling byte must invalidate");
    }

    function testTruncatedPaddingStillVerifies() public view {
        // Drop the 16 ABI padding bytes entirely: calldataload zero-fills past
        // calldatasize, and the masked top-16 bytes are still in-bounds sig data.
        bytes memory sig = _sig();
        bytes memory raw = abi.encodeWithSelector(verifier.verify.selector, SEED, ROOT, MSG, sig);
        bytes memory trunc = new bytes(raw.length - 16);
        for (uint256 i = 0; i < trunc.length; i++) trunc[i] = raw[i];
        (bool ok, bytes memory res) = address(verifier).staticcall(trunc);
        // Whether solc's decoder accepts the truncated envelope is version-dependent;
        // if it does accept it, the verdict must still be true.
        if (ok && res.length >= 32) {
            assertTrue(abi.decode(res, (bool)), "truncated padding must still verify if decoded");
        }
    }
}
