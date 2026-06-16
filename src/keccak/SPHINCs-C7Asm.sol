// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @title SphincsC7Asm — Stateless SPHINCS+ C7 verifier (shared, Yul-optimized)
/// @notice C7: W+C_F+C h=24 d=2 a=16 k=8 w=8 l=43 target_sum=151 sig=3704
///         Same FORS+C as C6 but with w=8 WOTS chains: fewer hash steps per chain (7 vs 15),
///         more chains (43 vs 32), trading +352 bytes sig for ~20% less compute.
/// @dev    Uses the FIPS 205 §4.2 uncompressed 32-byte ADRS (as C13). FORS is keyed by the
///         per-message hypertree leaf via the exact FIPS field split — tree=idxTree0,
///         kp=idxLeaf0, tree_index folds in the FORS tree number ((forsTree<<(A-height))|node).
///         Domain-separated H_msg (160 bytes).
///         ADRS: layer(4) ‖ tree(12) ‖ type(4) ‖ word1 ‖ word2 ‖ word3.
contract SphincsC7Asm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        assembly ("memory-safe") {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 3704)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            let seed := pkSeed
            let root := pkRoot
            mstore(0x00, seed)

            // H_msg (domain-separated, 160 bytes)
            let R := and(calldataload(sig.offset), N_MASK)
            mstore(0x20, root)
            mstore(0x40, R)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            let digest := keccak256(0x00, 0xA0)

            let htIdx := and(shr(128, digest), 0xFFFFFF)

            // FORS+C (K=8, A=16) — FIPS 205 FORS field split (per-message leaf keying):
            //   tree=idxTree0 (htIdx>>SUBTREE_H), kp=idxLeaf0 (htIdx&(2^SUBTREE_H-1)),
            //   tree_index=(forsTree<<(A-height))|node, tree_height=height.
            let dVal := digest
            if and(shr(112, dVal), 0xFFFF) { revert(0, 0) }

            let sigBase := sig.offset
            // SUBTREE_H = 12 (h/d = 24/2): split htIdx into bottom subtree + leaf.
            let idxLeaf0 := and(htIdx, 0xFFF)
            let idxTree0 := shr(12, htIdx)
            // forsBase: tree=idxTree0 (shl 128), type=3 (shl 96), kp=idxLeaf0 (shl 64).
            let forsBase := or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            for { let i := 0 } lt(i, 7) { i := add(i, 1) } {
                let treeIdx := and(shr(shl(4, i), dVal), 0xFFFF)
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): word3 = (i << A) | treeIdx, A=16
                let leafAdrs := or(forsBase, or(shl(16, i), treeIdx))
                mstore(0x20, leafAdrs)
                mstore(0x40, secretVal)
                let node := and(keccak256(0x00, 0x60), N_MASK)

                let pathIdx := treeIdx
                let authPtr := add(sigBase, add(144, shl(8, i)))

                for { let h := 0 } lt(h, 16) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx, A-1=15
                    mstore(0x20, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(15, h), i), parentIdx))))
                    // Branchless Merkle swap (Solady pattern)
                    let s := shl(5, and(pathIdx, 1))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), sibling)
                    node := and(keccak256(0x00, 0x80), N_MASK)
                    pathIdx := parentIdx
                }
                mstore(add(0x80, shl(5, i)), node)
            }

            {
                let lastSecret := and(calldataload(add(sigBase, 128)), N_MASK)
                // Forced-zero tree (forsTree=7) as leaf node 0: word3 = (7 << A)
                mstore(0x20, or(forsBase, shl(16, 7)))
                mstore(0x40, lastSecret)
                mstore(0x160, and(keccak256(0x00, 0x60), N_MASK))
            }

            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
            }
            let forsPk := and(keccak256(0x00, 0x140), N_MASK)

            // ============================================================
            // Hypertree (D=2) — w=8, l=43, target_sum=151
            // ============================================================
            let currentNode := forsPk
            let idxTree := htIdx
            let sigOff := 1936  // HT_START (same as C6: FORS part identical)

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0xFFF)
                idxTree := shr(12, idxTree)

                let wotsAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(64, idxLeaf)))

                // Count at sigOff + l*N = sigOff + 43*16 = sigOff + 688
                let countOff := add(sigOff, 688)
                let count := shr(224, calldataload(add(sigBase, countOff)))

                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := keccak256(0x00, 0x80)

                // Validate digit sum = 151 (43 base-8 digits, 3 bits each)
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(mul(ii, 3), d), 0x7))  // 3-bit digits, mask=0x7
                }
                if iszero(eq(digitSum, 151)) { revert(0, 0) }

                // Complete 43 chains (w=8: max 7 steps per chain)
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(mul(i, 3), d), 0x7)
                    let steps := sub(7, digit)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    // FIPS WOTS_HASH: chain_address=word2 (shl 32), hash_address=word3 (shl 0)
                    let chainBase := or(wotsAdrs, shl(32, i))

                    for { let step := 0 } lt(step, steps) { step := add(step, 1) } {
                        mstore(0x20, or(chainBase, add(digit, step)))
                        mstore(0x40, val)
                        val := and(keccak256(0x00, 0x60), N_MASK)
                    }
                    mstore(add(0x80, shl(5, i)), val)
                }

                // PK compression: keccak256(seed || pkAdrs || 43 endpoints)
                // = 32 + 32 + 43*32 = 1440 = 0x5A0
                let pkAdrs := or(shl(224, layer), or(shl(128, idxTree), or(shl(96, 1), shl(64, idxLeaf))))
                mstore(0x20, pkAdrs)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
                }
                let wotsPk := and(keccak256(0x00, 0x5A0), N_MASK)

                // Merkle auth path (12 levels)
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)

                for { let h := 0 } lt(h, 12) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(merklePtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    // type=2, word2=height=h+1, word3=tree_index=parentIdx
                    mstore(0x20, or(treeAdrs, or(shl(32, add(h, 1)), parentIdx)))
                    // Branchless Merkle swap (Solady pattern)
                    let s := shl(5, and(mIdx, 1))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), sibling)
                    merkleNode := and(keccak256(0x00, 0x80), N_MASK)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 192)  // 12*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
