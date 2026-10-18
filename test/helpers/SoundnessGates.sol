// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

/// @notice Shared checks for the two WOTS+C / FORS+C soundness gates of the keccak C-series
///         verifiers (C7, C9, C10, C11, C13). A well-formed but invalid signature must make
///         `verify` RETURN an ABI-encoded `false`, not revert, so a caller using
///         `try ... returns (bool)` or a typed `bool ok = v.verify(...)` sees a rejection.
///         C7/C9/C10/C11 used to `revert(0, 0)` on both gates (review L-01 /
///         keccak-c7-c9-c10-c11-empty-revert-on-soundness-gates).
abstract contract SoundnessGates is Test {
    bytes32 private constant N_MASK = bytes32(~uint256(type(uint128).max));

    function _assertReturnsFalse(address v, bytes32 seed, bytes32 root, bytes32 m, bytes memory sig, string memory what)
        internal
        view
    {
        (bool ok, bytes memory ret) =
            v.staticcall(abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", seed, root, m, sig));
        assertTrue(ok, string.concat(what, ": reverted instead of returning false"));
        assertEq(ret.length, 32, string.concat(what, ": return data is not one ABI word"));
        assertEq(uint256(bytes32(ret)), 0, string.concat(what, ": did not return false"));
    }

    /// @dev H_msg of the keccak C-series: keccak(seed ‖ root ‖ R ‖ msg ‖ 0xFF..FF), R = top
    ///      16 bytes of sig[0:32]. Returns the first message whose digest has a non-zero
    ///      forced-zero field (bits [shift, shift + log2(mask+1))), i.e. one that is
    ///      rejected by the FORS+C forced-zero gate before any other check.
    function _forcedZeroViolatingMessage(bytes32 seed, bytes32 root, bytes memory sig, uint256 shift, uint256 mask)
        internal
        pure
        returns (bytes32 m)
    {
        bytes32 r;
        assembly {
            r := mload(add(sig, 0x20))
        }
        r &= N_MASK;
        for (uint256 i;; ++i) {
            m = keccak256(abi.encode("forced-zero gate", i));
            uint256 d = uint256(keccak256(abi.encodePacked(seed, root, r, m, type(uint256).max)));
            if ((d >> shift) & mask != 0) return m;
        }
    }

    /// @param shift,mask  the verifier's forced-zero field (`and(shr(shift, dVal), mask)`).
    /// @param countOff    byte offset of the layer-0 WOTS+C count (4 bytes, big-endian).
    function _checkSoundnessGatesReturnFalse(
        address v,
        bytes32 seed,
        bytes32 root,
        bytes32 m,
        bytes memory sig,
        uint256 shift,
        uint256 mask,
        uint256 countOff
    ) internal view {
        // Forced-zero gate: a message whose H_msg violates the forced-zero bits.
        _assertReturnsFalse(v, seed, root, _forcedZeroViolatingMessage(seed, root, sig, shift, mask), sig, "forced-zero");

        // Target-sum gate: H_msg (and so the forced-zero field) is unchanged, but the layer-0
        // WOTS+C digest now hashes a different count, so its digit sum misses the target
        // (or, rarely, the chains end on a wrong root). Either way the answer is false.
        bytes memory bad = bytes.concat(sig);
        bad[countOff + 3] = bytes1(uint8(bad[countOff + 3]) ^ 0x01);
        _assertReturnsFalse(v, seed, root, m, bad, "target-sum");
    }
}
