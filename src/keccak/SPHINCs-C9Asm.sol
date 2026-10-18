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
            // A forced-zero violation is a well-formed-but-invalid signature: return
            // `false` (the bool contract) rather than an empty revert, as C13 and the
            // SHA/BLAKE twins do. (review C13-V-f2 / L-01)
            if and(shr(120, dVal), 0xFFF) { mstore(0x00, 0) return(0x00, 0x20) }

            let sigBase := sig.offset
            // SUBTREE_H = 10 (h/d = 20/2): split htIdx into bottom subtree + leaf.
            let idxLeaf0 := and(htIdx, 0x3FF)
            let idxTree0 := shr(10, htIdx)
            // forsBase: tree=idxTree0 (shl 128), type=3 (shl 96), kp=idxLeaf0 (shl 64).
            let forsBase := or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            // K-1=10 normal trees. Their auth paths are contiguous (AUTH_START=192,
            // A*N = 12*16 = 192 bytes per tree), so one calldata pointer walks them all,
            // and dVal is consumed A=12 bits per tree.
            let authPtr := add(sigBase, 192)
            for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
                // tIdx = word3 at height 0 = (i << A) | treeIdx, A=12. The tree_index at
                // height t is tIdx >> t (= (i << (A-t)) | (treeIdx >> t)), and for t < A
                // its low bit is the path parity bit, so one shift per level suffices.
                let tIdx := or(shl(12, i), and(dVal, 0xFFF)) // 12-bit indices
                dVal := shr(12, dVal)
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): word2 = 0, word3 = tIdx
                mstore(0x20, or(forsBase, tIdx))
                mstore(0x40, secretVal)
                let node := and(keccak256(0x00, 0x60), N_MASK)

                // Walk A=12 auth path levels: word2 = tree_height climbs by one (1 << 32)
                // per level, word3 = tIdx >> height.
                let heightAdrs := forsBase
                let authEnd := add(authPtr, 192)
                for { } lt(authPtr, authEnd) { authPtr := add(authPtr, 16) } {
                    let s := shl(5, and(tIdx, 1))
                    tIdx := shr(1, tIdx)
                    heightAdrs := add(heightAdrs, 0x100000000)
                    mstore(0x20, or(heightAdrs, tIdx))
                    // Branchless Merkle swap (Solady pattern)
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), and(calldataload(authPtr), N_MASK))
                    node := and(keccak256(0x00, 0x80), N_MASK)
                }
                mstore(add(0x80, shl(5, i)), node)
            }

            // Last tree (forced-zero)
            {
                let lastSecret := and(calldataload(add(sigBase, 176)), N_MASK) // 16+10*16
                // Forced-zero tree (forsTree=10) as leaf node 0: word3 = (10 << A)
                mstore(0x20, or(forsBase, shl(12, 10)))
                mstore(0x40, lastSecret)
                // 0x80 + 10*0x20 = 0x1C0
                mstore(0x1C0, and(keccak256(0x00, 0x60), N_MASK))
            }

            // Compress 11 roots: keccak256(seed || rootsAdrs || 11 roots)
            // FORS_ROOTS: tree=idxTree0 (shl 128), type=4 (shl 96), kp=idxLeaf0 (shl 64).
            // = 32 + 32 + 11*32 = 416 = 0x1A0
            // The roots already sit at 0x80..: write seed and ADRS into the dead scratch
            // words 0x40/0x60 directly in front of them and hash from 0x40 (same bytes
            // as seed@0x00 ‖ adrs@0x20 ‖ roots@0x40, without a copy-down loop).
            mstore(0x40, seed)
            mstore(0x60, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
            let forsPk := and(keccak256(0x40, 0x1A0), N_MASK)

            // ============================================================
            // Hypertree (D=2, subtree_h=10, w=8, l=43, target_sum=208)
            // ============================================================
            let currentNode := forsPk
            let idxTree := htIdx
            // HT_START = AUTH_START + (K-1)*A*N = 2112, kept as an absolute calldata pointer
            let sigPtr := add(sigBase, 2112)

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x3FF) // 2^10 - 1
                idxTree := shr(10, idxTree)

                let wotsAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(64, idxLeaf)))
                // countPtr = sigPtr + l*N = sigPtr + 688
                let countPtr := add(sigPtr, 688)
                let count := shr(224, calldataload(countPtr))

                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := keccak256(0x00, 0x80)

                // Validate digit sum = 208 (43 base-8 digits, 3 bits each, LSB-first).
                // Branch-free SWAR sum (constants assume L=43, LOG_W=3): the digits are
                // bits [0,129) of d. Fold digit pairs into 22 6-bit lanes (<= 14), lane
                // pairs into 11 12-bit lanes (<= 28), then multiply by sum(2^(12k), k=0..10)
                // to collect every lane in bits 120..131. Each partial sum is <= 43*7 = 301
                // < 4096, so no carry crosses a lane and the result is exact for any d.
                let digitSum := and(d, 0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
                digitSum := add(and(digitSum, 0x1C71C71C71C71C71C71C71C71C71C71C7), and(shr(3, digitSum), 0x1C71C71C71C71C71C71C71C71C71C71C7))
                digitSum := add(and(digitSum, 0x3F03F03F03F03F03F03F03F03F03F03F), and(shr(6, digitSum), 0x3F03F03F03F03F03F03F03F03F03F03F))
                digitSum := and(shr(120, mul(digitSum, 0x1001001001001001001001001001001)), 0xFFF)
                // A digit-sum mismatch is a well-formed-but-invalid signature: return
                // `false`, uniform with the forced-zero path. (review C13-V-f2 / L-01)
                if iszero(eq(digitSum, 208)) { mstore(0x00, 0) return(0x00, 0x20) }

                // 43 WOTS chains (w=8: max 7 steps per chain). Chain i runs hash_address
                // digit_i..6, so the step loop counts on the ADRS word itself
                // (word3 = hash_address is the low 32 bits); per chain, wotsAdrs advances
                // chain_address (word2, shl 32) by one and d drops its low 3-bit digit.
                // Endpoints go to 0x80 + 32*i.
                let outPtr := 0x80
                for { } lt(sigPtr, countPtr) { sigPtr := add(sigPtr, 16) } {
                    // The chain value lives in memory at 0x40 (its slot in the F input
                    // seed ‖ adrs ‖ value), so a step is just store ADRS, hash, mask, store.
                    mstore(0x40, and(calldataload(sigPtr), N_MASK))
                    // FIPS WOTS_HASH: chain_address=word2 (shl 32), hash_address=word3 (shl 0)
                    let adrsEnd := or(wotsAdrs, 7)
                    for { let adrs := or(wotsAdrs, and(d, 0x7)) } lt(adrs, adrsEnd) { adrs := add(adrs, 1) } {
                        mstore(0x20, adrs)
                        mstore(0x40, and(keccak256(0x00, 0x60), N_MASK))
                    }
                    mstore(outPtr, mload(0x40))
                    outPtr := add(outPtr, 0x20)
                    d := shr(3, d)
                    wotsAdrs := add(wotsAdrs, 0x100000000) // chain_address += 1
                }

                // PK compression: 32+32+43*32 = 1440 = 0x5A0, hashed in place from 0x40
                // like the FORS roots (the endpoints already sit at 0x80..).
                let pkAdrs := or(shl(224, layer), or(shl(128, idxTree), or(shl(96, 1), shl(64, idxLeaf))))
                mstore(0x40, seed)
                mstore(0x60, pkAdrs)
                let merkleNode := and(keccak256(0x40, 0x5A0), N_MASK)

                // Merkle auth path (10 levels) at countPtr + 4:
                // type=2, word2=tree_height, word3=tree_index = idxLeaf >> height.
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let mIdx := idxLeaf
                let merklePtr := add(countPtr, 4)
                sigPtr := add(merklePtr, 160) // 10*16: next layer's WOTS sig
                for { } lt(merklePtr, sigPtr) { merklePtr := add(merklePtr, 16) } {
                    let s := shl(5, and(mIdx, 1))
                    mIdx := shr(1, mIdx)
                    treeAdrs := add(treeAdrs, 0x100000000) // word2 = tree_height
                    mstore(0x20, or(treeAdrs, mIdx))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), and(calldataload(merklePtr), N_MASK))
                    merkleNode := and(keccak256(0x00, 0x80), N_MASK)
                }

                currentNode := merkleNode
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
