// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C13Asm.sol";
import "../src/SphincsFrameAccount.sol";

/// @notice Integration test: SphincsFrameAccount + C13 verifier.
///         APPROVE opcode (0xaa) is EIP-8141; the contract's assembly block
///         is currently a placeholder, so verifyAndApprove returns normally
///         on standard EVM after the verifier staticcall succeeds — which is
///         what we test here.
contract SphincsFrameAccountC13Test is Test {
    SphincsC13Asm verifier;
    address frameOwner;

    function setUp() public {
        verifier = new SphincsC13Asm();
        frameOwner = address(0xBEEF);
    }

    function testFrameVerifyAndApproveAcceptsRealC13SignatureFFI() public {
        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c13";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));

        SphincsFrameAccount frame = new SphincsFrameAccount(pkSeed, pkRoot, address(verifier), frameOwner);

        assertEq(frame.verifier(), address(verifier), "verifier wired");
        assertEq(frame.pkSeed(), pkSeed, "pkSeed stored");
        assertEq(frame.pkRoot(), pkRoot, "pkRoot stored");
        assertEq(frame.owner(), frameOwner, "owner stored");

        // verifyAndApprove must not revert on a valid C13 sig.
        frame.verifyAndApprove(message, sig, 1);
    }

    function testFrameVerifyAndApproveRevertsOnBadSignature() public {
        // Canonical (top-128-aligned) keys so we exercise the actual bad-SIGNATURE
        // path, not the non-canonical-key input guard.
        bytes32 pkSeed = bytes32(uint256(1) << 128);
        bytes32 pkRoot = bytes32(uint256(2) << 128);
        SphincsFrameAccount frame = new SphincsFrameAccount(pkSeed, pkRoot, address(verifier), frameOwner);

        // 3688 zero bytes: correct length, but the FORS+C forced-zero / WOTS+C
        // target-sum / root checks all fail. The verifier now RETURNS false for
        // these (review C13-evm-f2), so the frame's descriptive require fires.
        bytes memory zeroSig = new bytes(3688);
        bytes32 message = bytes32(uint256(0xdead));
        vm.expectRevert(bytes("invalid SPHINCS+ signature"));
        frame.verifyAndApprove(message, zeroSig, 1);
    }

    function testFrameRevertsOnNonCanonicalKey() public {
        // Non-canonical pkSeed (low 128 bits set) now trips the verifier's
        // "Invalid public key" guard, surfaced by the frame as "verify call failed".
        bytes32 pkSeed = bytes32(uint256(1));
        bytes32 pkRoot = bytes32(uint256(2) << 128);
        SphincsFrameAccount frame = new SphincsFrameAccount(pkSeed, pkRoot, address(verifier), frameOwner);
        bytes memory zeroSig = new bytes(3688);
        vm.expectRevert(bytes("verify call failed"));
        frame.verifyAndApprove(bytes32(uint256(0xdead)), zeroSig, 1);
    }
}
