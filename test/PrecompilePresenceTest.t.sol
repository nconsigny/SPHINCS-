// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SPHINCs-C10-SHA.sol";
import "../src/sha/SPHINCs-C11-SHA.sol";
import "../src/sha/SPHINCs-C12-SHA.sol";
import "../src/sha/SPHINCs-C13-SHA.sol";
import "../src/blake/SPHINCs-C11-BLAKE.sol";
import "../src/blake/SPHINCs-C12-BLAKE.sol";
import "../src/blake/SPHINCs-C13-BLAKE.sol";

/// @notice Regression test for review finding c12sha-precompile-presence. On an EVM where
///         0x02 (SHA-256) or 0x09 (BLAKE2F) is not a precompile, a STATICCALL to it hits an
///         empty account: it "succeeds", returns no data and leaves the output buffer
///         untouched. The verifiers must notice (returndatasize check) and revert, rather
///         than keep hashing with stale buffers. `vm.mockCall` with empty return data models
///         exactly that empty-account behaviour.
contract PrecompilePresenceTest is Test {
    bytes32 constant SEED = bytes32(uint256(0x1234) << 128);
    bytes32 constant ROOT = bytes32(uint256(0x5678) << 128);
    bytes32 constant MSG = keccak256("presence");

    function _call(address v, uint256 sigLen) internal view returns (bool ok, bytes memory ret) {
        (ok, ret) = v.staticcall(
            abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", SEED, ROOT, MSG, new bytes(sigLen))
        );
    }

    /// @dev Precompile present: a garbage (all-zero) signature is simply rejected with `false`.
    ///      Precompile absent: the verifier reverts with no data before using any output.
    function _check(address v, uint256 sigLen, address precompile) internal {
        (bool ok, bytes memory ret) = _call(v, sigLen);
        assertTrue(ok, "control: present precompile, garbage sig must not revert");
        assertEq(ret.length, 32);
        assertEq(uint256(bytes32(ret)), 0, "control: garbage sig must return false");

        vm.mockCall(precompile, bytes(""), bytes(""));
        (ok, ret) = _call(v, sigLen);
        assertFalse(ok, "absent precompile must make verify revert");
        assertEq(ret.length, 0);
        vm.clearMockedCalls();
    }

    function testC10ShaRevertsWithoutSha256Precompile() public {
        _check(address(new SphincsC10ShaAsm()), 4008, address(0x02));
    }

    function testC11ShaRevertsWithoutSha256Precompile() public {
        _check(address(new SphincsC11ShaAsm()), 3976, address(0x02));
    }

    function testC12ShaRevertsWithoutSha256Precompile() public {
        _check(address(new SPHINCs_C12ShaAsm()), 6576, address(0x02));
    }

    function testC13ShaRevertsWithoutSha256Precompile() public {
        _check(address(new SphincsC13ShaAsm()), 3688, address(0x02));
    }

    // ── In-place SHA kernel: a 0x02 that answers H_msg but no F/H/T ──
    // The SHA twins write every F/H/T output straight into the next call's input slot, so
    // a call that comes back without writing passes its input through unchanged. A
    // prefix-matched mock (every F/H/T input starts with PK.seed ‖ toByte(0,48); none of
    // the H_msg inputs do) models a 0x02 that answers H_msg but nothing after it: the
    // first-call presence check passes, and only the presence check on the last call
    // stands between the pass-through signatures below and an accept (with that check
    // removed, each of these tests verifies true). Each signature is plain garbage under
    // real hashes, which the control call confirms.

    function _fhtPrefix() internal pure returns (bytes memory) {
        return abi.encodePacked(bytes16(SEED), new bytes(48));
    }

    function _put16(bytes memory s, uint256 off, bytes16 v) internal pure {
        for (uint256 b; b < 16; ++b) s[off + b] = v[b];
    }

    function _checkPassThrough(address v, bytes32 root, bytes memory sig) internal {
        bytes memory data = abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", SEED, root, MSG, sig);
        (bool ok, bytes memory ret) = v.staticcall(data);
        assertTrue(ok, "control: real hashes, pass-through sig must not revert");
        assertEq(uint256(bytes32(ret)), 0, "control: real hashes, pass-through sig must return false");

        vm.mockCall(address(0x02), _fhtPrefix(), bytes(""));
        (ok, ret) = v.staticcall(data);
        assertFalse(ok, "F/H/T unanswered after a real H_msg: the last-call presence check must revert");
        assertEq(ret.length, 0);
        vm.clearMockedCalls();
    }

    /// @dev WOTS+C/FORS+C twins (d = 2, l = 43). R is ground (offline) so the real H_msg
    ///      passes the forced-zero gate. With F/H/T unanswered the WOTS digest word d is
    ///      stale: its top 6 bytes are bytes 6..11 of auth[1] (the tail of the count word
    ///      stored at 0x66), the rest is H_msg's 0xFF domain word. root16 carries a digit
    ///      pattern there that makes the 43 digits sum to the target. The top layer's last
    ///      chain value and every top-layer auth node are root16, so whichever slot the
    ///      unanswered Merkle climb ends on, 0x56 holds pkRoot.
    function _wotsCPassThroughSig(uint256 sigLen, uint256 htStart, uint256 subtreeH, bytes16 root16, uint128 r)
        internal
        pure
        returns (bytes memory sig)
    {
        sig = new bytes(sigLen);
        _put16(sig, 0, bytes16(r));
        uint256 layerLen = 43 * 16 + 4 + 16 * subtreeH;   // chains ‖ count ‖ auth
        _put16(sig, htStart + 692 + 16, root16);           // layer-0 auth[1]
        uint256 top = htStart + layerLen;
        _put16(sig, top + 42 * 16, root16);                // top-layer chain 42
        for (uint256 j; j < subtreeH; ++j) _put16(sig, top + 692 + 16 * j, root16);
        assertEq(top + 692 + 16 * subtreeH, sigLen);
    }

    function _assertForcedZeroPasses(bytes32 root, uint128 r, uint256 shift, uint256 mask) internal pure {
        uint256 dWord = uint256(sha256(abi.encodePacked(SEED, root, bytes16(r), bytes16(0), MSG, type(uint256).max)));
        assertEq((dWord >> shift) & mask, 0, "R must pass the forced-zero gate under the real H_msg");
    }

    function testC10ShaRejectsPassThroughForgeryWhenOnlyHmsgAnswers() public {
        bytes16 root16 = 0x5678abcdef01249249249249a5a5c3c3;   // digits 1 x16 -> 16 + 27*7 = 205
        _assertForcedZeroPasses(bytes32(root16), 0x2c4c, 113, 0x7FF);
        _checkPassThrough(
            address(new SphincsC10ShaAsm()), bytes32(root16), _wotsCPassThroughSig(4008, 2336, 9, root16, 0x2c4c)
        );
    }

    function testC11ShaRejectsPassThroughForgeryWhenOnlyHmsgAnswers() public {
        bytes16 root16 = 0x5678abcdef01249249249240a5a5c3c3;   // digits 1 x14, 0 x2 -> 14 + 189 = 203
        _assertForcedZeroPasses(bytes32(root16), 0x803, 113, 0x7FF);
        _checkPassThrough(
            address(new SphincsC11ShaAsm()), bytes32(root16), _wotsCPassThroughSig(3976, 2336, 8, root16, 0x803)
        );
    }

    function testC13ShaRejectsPassThroughForgeryWhenOnlyHmsgAnswers() public {
        bytes16 root16 = 0x5678abcdef01249249249292a5a5c3c3;   // digits 1 x13, 2 x3 -> 19 + 189 = 208
        _assertForcedZeroPasses(bytes32(root16), 0x4a11, 123, 0x7FFFF);
        _checkPassThrough(
            address(new SphincsC13ShaAsm()), bytes32(root16), _wotsCPassThroughSig(3688, 1952, 11, root16, 0x4a11)
        );
    }

    /// @dev C12-SHA has no gates: the top layer's last chain value (chain 45) and its 4 auth
    ///      nodes = pkRoot are enough.
    function testC12ShaRejectsPassThroughForgeryWhenOnlyHmsgAnswers() public {
        bytes memory sig = new bytes(6576);
        uint256 top = 2576 + 4 * 800;   // R(16) + FORS(20 * 128) + 4 layers x (46 * 16 + 4 * 16)
        _put16(sig, top + 45 * 16, bytes16(ROOT));
        for (uint256 j; j < 4; ++j) _put16(sig, top + 736 + 16 * j, bytes16(ROOT));
        _checkPassThrough(address(new SPHINCs_C12ShaAsm()), ROOT, sig);
    }

    // ── BLAKE2F (0x09) ──
    // With a code-less 0x09 the kernel's H_msg is an IV-derived constant, so C11/C13-BLAKE
    // may already return false at the forced-zero gate; the guarantee is that nothing is
    // ever accepted, and that the final comparison is never reached without the
    // returndatasize guard.

    function _assertNotAccepted(address v, bytes32 root, bytes memory sig) internal view {
        (bool ok, bytes memory ret) = v.staticcall(
            abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", SEED, root, MSG, sig)
        );
        assertTrue(!ok || ret.length < 32 || uint256(bytes32(ret)) == 0, "accepted with an absent BLAKE2F precompile");
    }

    function _checkBlake(address v, uint256 sigLen) internal {
        (bool ok, bytes memory ret) = _call(v, sigLen);
        assertTrue(ok, "control: present precompile, garbage sig must not revert");
        assertEq(uint256(bytes32(ret)), 0, "control: garbage sig must return false");
        vm.mockCall(address(0x09), bytes(""), bytes(""));
        _assertNotAccepted(v, ROOT, new bytes(sigLen));
        vm.clearMockedCalls();
    }

    function testC11BlakeNeverAcceptsWithoutBlake2f() public {
        _checkBlake(address(new SphincsC11BlakeAsm()), 3976);
    }

    function testC13BlakeNeverAcceptsWithoutBlake2f() public {
        _checkBlake(address(new SphincsC13BlakeAsm()), 3688);
    }

    /// @dev C12-BLAKE has no forced-zero gate, so an absent precompile reaches the climbs.
    ///      The F/H fast path writes each digest into the next input slot; when nothing is
    ///      written, inputs pass straight through and an all-zero signature carrying the
    ///      victim's pkRoot as one top-layer auth node would end on pkRoot (with the guard
    ///      removed, the h = 2 placement below verifies true). The guard must revert before
    ///      the final comparison.
    function testC12BlakeRejectsPassThroughForgeryWithoutBlake2f() public {
        address v = address(new SPHINCs_C12BlakeAsm());
        _checkBlake(v, 6592);
        // top layer (4): HT_START 2592 + 4 * 800, auth nodes at +736, 4 x 16 B
        for (uint256 h; h < 4; ++h) {
            bytes memory sig = new bytes(6592);
            uint256 off = 2592 + 4 * 800 + 736 + 16 * h;
            for (uint256 b; b < 16; ++b) sig[off + b] = ROOT[b];
            vm.mockCall(address(0x09), bytes(""), bytes(""));
            (bool ok,) = v.staticcall(
                abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", SEED, ROOT, MSG, sig)
            );
            assertFalse(ok, "absent BLAKE2F precompile must make C12-BLAKE revert");
            vm.clearMockedCalls();
        }
    }
}
