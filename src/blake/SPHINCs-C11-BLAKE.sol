// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC11BlakeAsm — BLAKE2b "minimal twin" of the C11 verifier
/// @notice C11: W+C_F+C h=16 d=2 a=11 k=13 w=8 l=43 target_sum=203 sig=3976.
/// @dev    BLAKE2b twin of src/keccak/SPHINCs-C11Asm.sol — IDENTICAL construction
///         (FIPS 205 §4.2 uncompressed 32-byte ADRS, WOTS+C/FORS+C, one-shot H_msg,
///         forced-zero FORS tree, same signature byte layout) with only the hash
///         primitive swapped: keccak256(seed‖adrs‖payload) -> BLAKE2b(...). BLAKE2b
///         is built on the 0x09 (BLAKE2F) compression precompile by the blake2b()
///         Yul kernel (see src/blake/SPHINCs-C13-BLAKE.sol for the kernel notes).
///         F/H/T use nn=16; H_msg and the WOTS+C digest use nn=32. NOT FIPS
///         (research "BLAKE flavour"). `view` (the precompile is a staticcall).
///         Adds the canonical public-key guard the keccak C11 lacks (review C13-V-f1).
///         Vectors: script/signer.py c11-blake (hash=blake2, adrs_mode=fips).
contract SphincsC11BlakeAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        // Bare `assembly` (NOT memory-safe): the main block uses 0x40/0x60 as scratch
        // and writes high memory; sound only because every exit is an in-assembly
        // return/revert. The blake2b() kernel uses scratch at 0x800+ (clear of the
        // SPHINCS+ working set, which tops out ~0x5E0) and reads preimages from 0x00.
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 3976)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }
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

            // H_msg (domain-separated, 160 bytes) — nn=32.
            let R := and(calldataload(sig.offset), N_MASK)
            mstore(0x20, root)
            mstore(0x40, R)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            let digest := blake2b(0x00, 0xA0, 32)

            // htIdx = (digest >> 143) & (2^16-1).  143 = K*A = 13*11.
            let htIdx := and(shr(143, digest), 0xFFFF)

            let dVal := digest
            // Forced-zero: last FORS index (i=K-1=12) at bits [132,143). 132=(K-1)*A.
            if and(shr(132, dVal), 0x7FF) { mstore(0x00, 0) return(0x00, 0x20) }

            let sigBase := sig.offset

            // SUBTREE_H = 8 (h/d = 16/2).
            let idxLeaf0 := and(htIdx, 0xFF)
            let idxTree0 := shr(8, htIdx)
            // forsBase: tree=idxTree0 (shl 128), type=3 (shl 96), kp=idxLeaf0 (shl 64).
            let forsBase := or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            // K-1=12 normal trees
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 11), dVal), 0x7FF) // 11=A-bit indices
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): word3 = (i << A) | treeIdx, A=11
                let leafAdrs := or(forsBase, or(shl(11, i), treeIdx))
                mstore(0x20, leafAdrs)
                mstore(0x40, secretVal)
                let node := blake2b(0x00, 0x60, 16)

                let pathIdx := treeIdx
                // AUTH_START = 16 + K*N = 224, auth per tree = A*N = 11*16 = 176
                let authPtr := add(sigBase, add(224, mul(i, 176)))

                for { let h := 0 } lt(h, 11) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx, A-1=10
                    mstore(0x20, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(10, h), i), parentIdx))))
                    let s := shl(5, and(pathIdx, 1))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), sibling)
                    node := blake2b(0x00, 0x80, 16)
                    pathIdx := parentIdx
                }
                mstore(add(0x80, shl(5, i)), node)
            }

            // Last tree (forced-zero)
            {
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 12)))), N_MASK) // 16+12*16=208
                mstore(0x20, or(forsBase, shl(11, 12))) // word3 = 12 << A
                mstore(0x40, lastSecret)
                mstore(0x200, blake2b(0x00, 0x60, 16)) // 0x80 + 12*0x20
            }

            // Compress 13 roots: = 32 + 32 + 13*32 = 480 = 0x1E0
            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
            for { let i := 0 } lt(i, 13) { i := add(i, 1) } {
                mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
            }
            let forsPk := blake2b(0x00, 0x1E0, 16)

            // ============================================================
            // Hypertree (D=2, subtree_h=8, w=8, l=43, target_sum=203)
            // ============================================================
            let currentNode := forsPk
            let idxTree := htIdx
            let sigOff := 2336 // HT_START = AUTH_START + (K-1)*A*N = 224 + 12*176

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0xFF) // 2^8 - 1
                idxTree := shr(8, idxTree)

                let wotsAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(64, idxLeaf)))
                let countOff := add(sigOff, 688) // l*N = 43*16
                let count := shr(224, calldataload(add(sigBase, countOff)))

                // WOTS-message digest — nn=32.
                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := blake2b(0x00, 0x80, 32)

                // Validate WOTS+C digit sum == 203 (43 base-8 digits).
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(mul(ii, 3), d), 0x7))
                }
                if iszero(eq(digitSum, 203)) { mstore(0x00, 0) return(0x00, 0x20) }

                // 43 WOTS chains (w=8: max 7 steps per chain)
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(mul(i, 3), d), 0x7)
                    let steps := sub(7, digit)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsAdrs, shl(32, i))
                    for { let step := 0 } lt(step, steps) { step := add(step, 1) } {
                        mstore(0x20, or(chainBase, add(digit, step)))
                        mstore(0x40, val)
                        val := blake2b(0x00, 0x60, 16)
                    }
                    mstore(add(0x80, shl(5, i)), val)
                }

                // WOTS_PK compression: type=1, word1=idxLeaf. = 32+32+43*32 = 1440 = 0x5A0
                let pkAdrs := or(shl(224, layer), or(shl(128, idxTree), or(shl(96, 1), shl(64, idxLeaf))))
                mstore(0x20, pkAdrs)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
                }
                let wotsPk := blake2b(0x00, 0x5A0, 16)

                // TREE Merkle auth path (8 levels): type=2, word2=height, word3=tree_index
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)

                for { let h := 0 } lt(h, 8) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(merklePtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    mstore(0x20, or(treeAdrs, or(shl(32, add(h, 1)), parentIdx)))
                    let s := shl(5, and(mIdx, 1))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), sibling)
                    merkleNode := blake2b(0x00, 0x80, 16)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 128) // 8*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)

            // ── BLAKE2b kernel (validated in test/Blake2bKernelTest.t.sol) ──
            function blake2b(inPtr, inLen, nnLocal) -> result {
                let S := 0x800
                mstore(S, shl(224, 12)) // rounds = 12 (big-endian)
                let h0 := bswap64(xor(xor(0x6a09e667f3bcc908, 0x01010000), nnLocal))
                mstore(add(S, 4), or(or(shl(192, h0), shl(128, bswap64(0xbb67ae8584caa73b))),
                                     or(shl(64, bswap64(0x3c6ef372fe94f82b)), bswap64(0xa54ff53a5f1d36f1))))
                mstore(add(S, 36), or(or(shl(192, bswap64(0x510e527fade682d1)), shl(128, bswap64(0x9b05688c2b3e6c1f))),
                                      or(shl(64, bswap64(0x1f83d9abfb41bd6b)), bswap64(0x5be0cd19137e2179))))
                let remaining := inLen
                let blockOff := 0
                let processed := 0
                for {} 1 {} {
                    let thisLen := 128
                    let isLast := 0
                    if lt(remaining, 128) { thisLen := remaining isLast := 1 }
                    if eq(remaining, 128) { isLast := 1 }
                    processed := add(processed, thisLen)
                    mstore(add(S, 68), 0) mstore(add(S, 100), 0)
                    mstore(add(S, 132), 0) mstore(add(S, 164), 0)
                    let src := add(inPtr, blockOff)
                    let dst := add(S, 68)
                    let full := and(thisLen, not(31))
                    let o := 0
                    for {} lt(o, full) { o := add(o, 32) } { mstore(add(dst, o), mload(add(src, o))) }
                    let rest := and(thisLen, 31)
                    if rest {
                        let mask := not(shr(mul(rest, 8), not(0)))
                        mstore(add(dst, o), and(mload(add(src, o)), mask))
                    }
                    mstore(add(S, 196), shl(192, bswap64(processed))) // t_0 (LE), t_1=0
                    mstore8(add(S, 212), isLast)
                    if iszero(staticcall(gas(), 0x09, S, 213, add(S, 4), 64)) { revert(0, 0) }
                    remaining := sub(remaining, thisLen)
                    blockOff := add(blockOff, 128)
                    if iszero(remaining) { break }
                }
                switch nnLocal
                case 16 { result := and(mload(add(S, 4)), 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000) }
                default { result := mload(add(S, 4)) }
            }

            function bswap64(x) -> y {
                for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                    y := or(shl(8, y), and(x, 0xff))
                    x := shr(8, x)
                }
            }
        }
    }
}
