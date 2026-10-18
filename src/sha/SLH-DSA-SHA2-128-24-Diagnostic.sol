// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @dev Diagnostic: runs Hmsg → FORS and returns tree-0 climb checkpoints
///      so we can bisect where Solidity diverges from Python.
///
///      Returns 7 bytes32 (224 bytes):  leaf, c0, c5, c11, c17, c22, r0
///      where c_j is tree-0's intermediate node after H call j (0-based, so c0 is
///      the height-1 node and c22 the height-23 node) and r0 is the final tree-0
///      FORS root (after all 24 H calls, j = 23).
///
///      H_msg mirrors SLH-DSA-SHA2-128-24verifier.sol exactly: FIPS 205 EXTERNAL
///      mode with empty context, M' = 0x00 ‖ 0x00 ‖ M (review SLH-X-f1). Without
///      the envelope the trace follows a FORS tree the verifier never computes
///      (review slh-diag-stale-hmsg-envelope).
contract SLH_DSA_SHA2_128_24_Diagnostic {

    function forsTree0Trace(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (
            bytes32 leaf, bytes32 c0, bytes32 c5, bytes32 c11, bytes32 c17, bytes32 c22, bytes32 r0)
    {
        leaf; c0; c5; c11; c17; c22; r0;
        require(sig.length == 3856, "bad sig len");

        // writes 0x40+/0x80+/0x600+ without
        // updating the FMP, but exits via `return` so memory state isn't
        // returned.
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000
            let seed := pkSeed
            let root := pkRoot
            let sigBase := sig.offset

            // Hmsg, inner = SHA-256(R ‖ seed ‖ root ‖ 0x00 ‖ 0x00 ‖ M), 82 bytes
            mstore(0x00, calldataload(sigBase))
            mstore(0x10, seed)
            mstore(0x20, root)
            mstore(0x30, 0)            // empty-context envelope 0x00 0x00 at 0x30..0x32
            mstore(0x32, message)      // M at 0x32..0x52
            if iszero(staticcall(gas(), 0x02, 0x00, 0x52, 0x20, 0x20)) { revert(0, 0) }
            mstore(0x40, 0)
            if iszero(staticcall(gas(), 0x02, 0x00, 0x44, 0x100, 0x20)) { revert(0, 0) }
            let dWord := mload(0x100)
            let leafIdx := and(shr(88, dWord), 0x3FFFFF)

            mstore(0x00, seed)
            mstore(0x20, 0)

            let forsBase := or(shl(176, 3), shl(144, leafIdx))

            // Tree 0 only — FIPS 205 BE 24-bit read of digest[0..3]
            //   md[0] = digest[0]<<16 | digest[1]<<8 | digest[2]
            //         = (dWord >> 232) & 0xFFFFFF
            let mdT := and(shr(232, dWord), 0xFFFFFF)

            let sk := and(calldataload(add(sigBase, 16)), N_MASK)
            mstore(0x40, or(forsBase, shl(80, mdT)))
            mstore(0x56, sk)
            if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
            let node := and(mload(0x80), N_MASK)

            // Stash leaf into return buffer at 0x600
            mstore(0x600, node)

            let authPtr := add(sigBase, 32)
            let pathIdx := mdT

            for { let j := 0 } lt(j, 24) { j := add(j, 1) } {
                let sibling := and(calldataload(add(authPtr, shl(4, j))), N_MASK)
                let parentIdx := shr(1, pathIdx)
                let globalY := parentIdx   // t=0 so shift doesn't matter
                mstore(0x40, or(forsBase, or(shl(112, add(j, 1)), shl(80, globalY))))
                switch and(pathIdx, 1)
                case 0 { mstore(0x56, node)    mstore(0x66, sibling) }
                default { mstore(0x56, sibling) mstore(0x66, node) }
                if iszero(staticcall(gas(), 0x02, 0x00, 0x76, 0x80, 0x20)) { revert(0, 0) }
                node := and(mload(0x80), N_MASK)
                pathIdx := parentIdx

                if eq(j, 0) { mstore(0x620, node) }   // c0
                if eq(j, 5) { mstore(0x640, node) }   // c5
                if eq(j, 11) { mstore(0x660, node) }  // c11
                if eq(j, 17) { mstore(0x680, node) }  // c17
                if eq(j, 22) { mstore(0x6A0, node) }  // c22
            }
            mstore(0x6C0, node)   // final r0

            return(0x600, 0xE0)   // 7 × bytes32 = 224 bytes
        }
    }
}
