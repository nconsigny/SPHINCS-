// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC11Asm — Stateless SPHINCS+ C11 verifier (shared, Yul-optimized)
/// @dev C11: h=16 d=2 a=11 k=13 w=8 l=43 target_sum=203 sig=3976
///      Domain-separated H_msg (160 bytes). Branchless Merkle swap, hoisted chain address.
contract SphincsC11Asm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        assembly ("memory-safe") {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 3976)) {
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

            // htIdx = (digest >> 143) & (2^16-1)
            let htIdx := and(shr(143, digest), 0xFFFF)

            // FORS+C (K=13, A=11)
            //
            // FORS addressing — exact FIPS 205 FORS field split (matches C12,
            // SPHINCs-C12Asm.sol:80) in the JARDIN layout —
            //   tree address      = idxTree0 = htIdx >> SUBTREE_H (bottom subtree)
            //   kp                 = idxLeaf0 = htIdx & (2^SUBTREE_H-1) (bottom leaf)
            //   ha/tree_index      = (forsTree << (A-height)) | node  (k FORS trees
            //                        indexed as one forest, FIPS 205 Alg. 17)
            //   cp/tree_height     = height
            // so each of the 2^h hypertree leaves selects a distinct FORS
            // instance. The signer mirrors this and derives the leaf secrets
            // from the same leaf.
            let dVal := digest
            // Forced-zero: last index (i=12) at bits 132..142
            if and(shr(132, dVal), 0x7FF) { revert(0, 0) }

            let sigBase := sig.offset
            // SUBTREE_H = 8 (h/d = 16/2): split htIdx into bottom subtree + leaf.
            let idxLeaf0 := and(htIdx, 0xFF)
            let idxTree0 := shr(8, htIdx)
            // forsBase: tree=idxTree0 (shl 160), type=3 (shl 128), kp=idxLeaf0 (shl 96).
            // Per-site we OR in cp=height (shl 32) and ha=tree_index (shl 0).
            let forsBase := or(shl(160, idxTree0), or(shl(128, 3), shl(96, idxLeaf0)))
            // K-1=12 normal trees
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 11), dVal), 0x7FF) // 11-bit indices
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): ha = (i << A) | treeIdx, A=11
                let leafAdrs := or(forsBase, or(shl(11, i), treeIdx))
                mstore(0x20, leafAdrs)
                mstore(0x40, secretVal)
                let node := and(keccak256(0x00, 0x60), N_MASK)

                let pathIdx := treeIdx
                // AUTH_START=224, auth per tree = 11*16 = 176
                let authPtr := add(sigBase, add(224, mul(i, 176)))

                // Walk A=11 auth path levels
                for { let h := 0 } lt(h, 11) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // cp=height=h+1; ha = (i << (A-1-h)) | parentIdx, A-1=10
                    mstore(0x20, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(10, h), i), parentIdx))))
                    // Branchless Merkle swap
                    let s := shl(5, and(pathIdx, 1))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), sibling)
                    node := and(keccak256(0x00, 0x80), N_MASK)
                    pathIdx := parentIdx
                }
                mstore(add(0x80, shl(5, i)), node)
            }

            // Last tree (forced-zero)
            {
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 12)))), N_MASK) // 16+12*16=208
                // Forced-zero tree (forsTree=12) as leaf node 0: ha = (12 << A)
                mstore(0x20, or(forsBase, shl(11, 12)))
                mstore(0x40, lastSecret)
                // 0x80 + 12*0x20 = 0x80 + 0x180 = 0x200
                mstore(0x200, and(keccak256(0x00, 0x60), N_MASK))
            }

            // Compress 13 roots: keccak256(seed || rootsAdrs || 13 roots)
            // FORS_ROOTS: tree=idxTree0 (shl 160), type=4 (shl 128), kp=idxLeaf0 (shl 96).
            // = 32 + 32 + 13*32 = 480 = 0x1E0
            mstore(0x20, or(shl(160, idxTree0), or(shl(128, 4), shl(96, idxLeaf0))))
            for { let i := 0 } lt(i, 13) { i := add(i, 1) } {
                mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
            }
            let forsPk := and(keccak256(0x00, 0x1E0), N_MASK)

            // Hypertree (D=2, subtree_h=8, w=8, l=43, target_sum=203)
            let currentNode := forsPk
            let idxTree := htIdx
            let sigOff := 2336 // HT_START

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0xFF) // 2^8 - 1
                idxTree := shr(8, idxTree)

                let wotsAdrs := or(shl(224, layer), or(shl(160, idxTree), shl(96, idxLeaf)))
                // countOff = sigOff + l*N = sigOff + 688
                let countOff := add(sigOff, 688)
                let count := shr(224, calldataload(add(sigBase, countOff)))

                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := keccak256(0x00, 0x80)

                // Validate digit sum = 203 (43 base-8 digits, 3 bits each)
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(mul(ii, 3), d), 0x7))
                }
                if iszero(eq(digitSum, 203)) { revert(0, 0) }

                // 43 WOTS chains (w=8: max 7 steps per chain)
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(mul(i, 3), d), 0x7)
                    let steps := sub(7, digit)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := and(
                        or(wotsAdrs, shl(64, i)),
                        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFF
                    )

                    for { let step := 0 } lt(step, steps) { step := add(step, 1) } {
                        mstore(0x20, or(chainBase, shl(32, add(digit, step))))
                        mstore(0x40, val)
                        val := and(keccak256(0x00, 0x60), N_MASK)
                    }
                    mstore(add(0x80, shl(5, i)), val)
                }

                // PK compression: 32+32+43*32 = 1440 = 0x5A0
                let pkAdrs := or(shl(224, layer), or(shl(160, idxTree), or(shl(128, 1), shl(96, idxLeaf))))
                mstore(0x20, pkAdrs)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
                }
                let wotsPk := and(keccak256(0x00, 0x5A0), N_MASK)

                // Merkle auth path (8 levels)
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(160, idxTree), shl(128, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)

                for { let h := 0 } lt(h, 8) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(merklePtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    mstore(0x20, or(
                        and(treeAdrs, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0000000000000000),
                        or(shl(32, add(h, 1)), parentIdx)
                    ))
                    let s := shl(5, and(mIdx, 1))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), sibling)
                    merkleNode := and(keccak256(0x00, 0x80), N_MASK)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 128) // 8*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
