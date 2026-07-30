// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC9Asm — Stateless SPHINCS+ C9 verifier (shared, Yul-optimized)
/// @dev C9: h=20 d=2 a=12 k=11 w=8 l=43 target_sum=208 sig=3816
///      Uses the FIPS 205 §4.2 uncompressed 32-byte ADRS (as C13). FORS keyed by the
///      per-message hypertree leaf via the exact FIPS field split — tree=idxTree0, kp=idxLeaf0,
///      tree_index folds in the FORS tree number ((forsTree<<(A-height))|node).
///      Domain-separated H_msg (160 bytes).
///      ADRS: layer(4) ‖ tree(12) ‖ type(4) ‖ word1 ‖ word2 ‖ word3.
contract SphincsC9Asm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        // NOTE: this block intentionally uses Solidity's free-memory-pointer slot
        // (0x40) and the zero slot (0x60) as scratch and writes high memory without
        // updating the FMP. That is only sound because every exit below is an
        // unconditional in-assembly `return`/`revert`, so Solidity never regains
        // control with a clobbered FMP. It is therefore NOT `memory-safe` in the
        // Yul sense — do not add the ("memory-safe") annotation and do not introduce
        // a normal (fall-through) exit from this block. (matches C13, review C13-evm-f1)
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 3816)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            // Reject non-canonical public keys (low 128 bits must be zero), mirroring
            // the C13 verifier and the SHA-2 / BLAKE2b twins. Without this a
            // non-top-aligned pkRoot can never equal the always-N_MASK'd `currentNode`,
            // silently bricking the account, and pkSeed would diverge from the signer,
            // which always masks. Fail loudly instead.
            if or(iszero(eq(pkSeed, and(pkSeed, N_MASK))), iszero(eq(pkRoot, and(pkRoot, N_MASK)))) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid public key")
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

            // htIdx = (digest >> 132) & (2^20-1)
            let htIdx := and(shr(132, digest), 0xFFFFF)

            // FORS+C (K=11, A=12) — FIPS 205 FORS field split (per-message leaf keying):
            //   tree=idxTree0 (htIdx>>SUBTREE_H), kp=idxLeaf0 (htIdx&(2^SUBTREE_H-1)),
            //   tree_index=(forsTree<<(A-height))|node, tree_height=height.
            let dVal := digest
            // Forced-zero: last index (i=10) at bits 120..131
            if and(shr(120, dVal), 0xFFF) { revert(0, 0) }

            let sigBase := sig.offset
            // SUBTREE_H = 10 (h/d = 20/2): split htIdx into bottom subtree + leaf.
            let idxLeaf0 := and(htIdx, 0x3FF)
            let idxTree0 := shr(10, htIdx)
            // forsBase: tree=idxTree0 (shl 128), type=3 (shl 96), kp=idxLeaf0 (shl 64).
            let forsBase := or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            // K-1=10 normal trees
            for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 12), dVal), 0xFFF) // 12-bit indices
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): word3 = (i << A) | treeIdx, A=12
                let leafAdrs := or(forsBase, or(shl(12, i), treeIdx))
                mstore(0x20, leafAdrs)
                mstore(0x40, secretVal)
                let node := and(keccak256(0x00, 0x60), N_MASK)

                let pathIdx := treeIdx
                // AUTH_START=192, auth per tree = 12*16 = 192
                let authPtr := add(sigBase, add(192, mul(i, 192)))

                // Walk A=12 auth path levels
                for { let h := 0 } lt(h, 12) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx, A-1=11
                    mstore(0x20, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(11, h), i), parentIdx))))
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
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 10)))), N_MASK) // 16+10*16=176
                // Forced-zero tree (forsTree=10) as leaf node 0: word3 = (10 << A)
                mstore(0x20, or(forsBase, shl(12, 10)))
                mstore(0x40, lastSecret)
                // 0x80 + 10*0x20 = 0x80 + 0x140 = 0x1C0
                mstore(0x1C0, and(keccak256(0x00, 0x60), N_MASK))
            }

            // Compress 11 roots: keccak256(seed || rootsAdrs || 11 roots)
            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            // = 32 + 32 + 11*32 = 416 = 0x1A0
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
            for { let i := 0 } lt(i, 11) { i := add(i, 1) } {
                mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
            }
            let forsPk := and(keccak256(0x00, 0x1A0), N_MASK)

            // Hypertree (D=2, subtree_h=10, w=8, l=43, target_sum=208)
            let currentNode := forsPk
            let idxTree := htIdx
            let sigOff := 2112 // HT_START

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x3FF) // 2^10 - 1
                idxTree := shr(10, idxTree)

                let wotsAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(64, idxLeaf)))
                // countOff = sigOff + l*N = sigOff + 688
                let countOff := add(sigOff, 688)
                let count := shr(224, calldataload(add(sigBase, countOff)))

                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := keccak256(0x00, 0x80)

                // Validate digit sum = 208 (43 base-8 digits, 3 bits each)
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(mul(ii, 3), d), 0x7))
                }
                if iszero(eq(digitSum, 208)) { revert(0, 0) }

                // 43 WOTS chains (w=8: max 7 steps per chain)
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

                // PK compression: 32+32+43*32 = 1440 = 0x5A0
                let pkAdrs := or(shl(224, layer), or(shl(128, idxTree), or(shl(96, 1), shl(64, idxLeaf))))
                mstore(0x20, pkAdrs)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
                }
                let wotsPk := and(keccak256(0x00, 0x5A0), N_MASK)

                // Merkle auth path (10 levels)
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)

                for { let h := 0 } lt(h, 10) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(merklePtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    // type=2, word2=height=h+1, word3=tree_index=parentIdx
                    mstore(0x20, or(treeAdrs, or(shl(32, add(h, 1)), parentIdx)))
                    let s := shl(5, and(mIdx, 1))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), sibling)
                    merkleNode := and(keccak256(0x00, 0x80), N_MASK)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 160) // 10*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
