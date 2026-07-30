// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC13BlakeAsm — BLAKE2b "minimal twin" of the C13 verifier
/// @notice C13: W+C_F+C h=22 d=2 a=19 k=7 w=8 l=43 target_sum=208 sig=3688.
/// @dev    BLAKE2b twin of src/keccak/SPHINCs-C13Asm.sol. IDENTICAL construction —
///         same FIPS 205 §4.2 uncompressed 32-byte ADRS, same WOTS+C/FORS+C
///         counter-grinding, same signature byte layout, same one-shot H_msg, same
///         forced-zero FORS tree — only the hash primitive changes:
///         keccak256(seed‖adrs‖payload)  ->  BLAKE2b(seed‖adrs‖payload).
///
///         BLAKE2b is built on the EVM BLAKE2F compression precompile (0x09,
///         EIP-152), which is NOT a hash — it is BLAKE2b's compression function F.
///         The `blake2b()` Yul kernel below wraps it with the BLAKE2b construction:
///         IV + parameter-block init (h[0] ^= 0x01010000 ^ nn), 128-byte block loop
///         with the byte counter `t` and final-block flag `f`, and the LE<->BE lane
///         bridging the precompile requires (it reads h/m/t as little-endian 64-bit
///         words; the EVM and the SPHINCS+ memory are big-endian). The message block
///         needs no swap (BLAKE2b reads it as 16 LE words = the raw byte order); only
///         the state init and the counter are swapped, and the 64-byte LE output
///         feeds straight back as the next block's state.
///
///         Output lengths: tweakable hashes F/H/T use nn=16 (truncated, top-aligned
///         via N_MASK); H_msg and the WOTS+C message digest use nn=32 (need >=129
///         bits to slice). The differing nn lives in the BLAKE2b parameter block, so
///         it also domain-separates the 16-byte tweakable hashes from the 32-byte
///         H_msg. NOT FIPS (BLAKE2b has no FIPS 205 instantiation, and WOTS+C/FORS+C
///         has no FIPS analog): a research "BLAKE flavour" of C13. Verifier is `view`
///         (the precompile is a staticcall), unlike the `pure` keccak twin.
///         Vectors: script/signer.py c13-blake (hash=blake2, adrs_mode=fips).
contract SphincsC13BlakeAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        // The main block uses Solidity's FMP (0x40) / zero (0x60) slots as scratch
        // and writes high memory without updating the FMP; sound only because every
        // exit is an unconditional in-assembly return/revert. The blake2b() kernel
        // uses scratch at 0x800+ (clear of the SPHINCS+ working set, which tops out
        // around 0x620) and reads each hash preimage from 0x00. Bare `assembly`
        // (NOT memory-safe); do not add the annotation or a fall-through exit.
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 3688)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            // Reject non-canonical public keys (low 128 bits must be zero), mirroring
            // the C13 keccak twin / the SHA family. Without this a non-top-aligned
            // pkRoot can never equal the always-N_MASK'd currentNode (silently
            // bricking the account); pkSeed would diverge from the always-masking
            // signer. Fail loudly. (review C13-V-f1)
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

            // H_msg (domain-separated, 160 bytes) — nn=32 (full digest to slice).
            let R := and(calldataload(sig.offset), N_MASK)
            mstore(0x20, root)
            mstore(0x40, R)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            let digest := blake2b(0x00, 0xA0, 32)

            // htIdx = (digest >> 133) & (2^22-1).  133 = K*A = 7*19 ; 0x3FFFFF = 2^H-1.
            let htIdx := and(shr(133, digest), 0x3FFFFF)

            let dVal := digest
            // Forced-zero: last FORS index (i=K-1=6) at bits [114,133). 114=(K-1)*A;
            // 0x7FFFF = 2^A-1. Well-formed-but-invalid -> return false (uniform bool
            // contract, not empty revert). (review C13-V-f2)
            if and(shr(114, dVal), 0x7FFFF) { mstore(0x00, 0) return(0x00, 0x20) }

            let sigBase := sig.offset

            // SUBTREE_H = 11. 0x7FF = 2^11-1 ; shift 11 = SUBTREE_H.
            let idxLeaf0 := and(htIdx, 0x7FF)
            let idxTree0 := shr(11, htIdx)
            // forsBase: tree=idxTree0 (shl 128), type=3 (shl 96), kp=idxLeaf0 (shl 64).
            let forsBase := or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            // K-1=6 normal trees
            for { let i := 0 } lt(i, 6) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 19), dVal), 0x7FFFF) // 19=A-bit indices, shift i*A
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): word3 = (i << A) | treeIdx, A=19
                let leafAdrs := or(forsBase, or(shl(19, i), treeIdx))
                mstore(0x20, leafAdrs)
                mstore(0x40, secretVal)
                let node := blake2b(0x00, 0x60, 16)

                let pathIdx := treeIdx
                // AUTH_START = 16 + K*N = 128, auth per tree = A*N = 19*16 = 304
                let authPtr := add(sigBase, add(128, mul(i, 304)))

                // Walk A=19 auth path levels
                for { let h := 0 } lt(h, 19) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx. 18 = A-1.
                    mstore(0x20, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(18, h), i), parentIdx))))
                    // Branchless Merkle swap (Solady)
                    let s := shl(5, and(pathIdx, 1))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), sibling)
                    node := blake2b(0x00, 0x80, 16)
                    pathIdx := parentIdx
                }
                mstore(add(0x80, shl(5, i)), node)
            }

            // Last tree (forced-zero): secret is the revealed root, hashed under FORS_TREE leaf ADRS
            {
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 6)))), N_MASK) // 16+(K-1)*16=112
                // Forced-zero tree (forsTree=K-1=6) as leaf node 0: word3 = (6 << A). 19=A.
                mstore(0x20, or(forsBase, shl(19, 6)))
                mstore(0x40, lastSecret)
                // 0x80 + 6*0x20 = 0x140
                mstore(0x140, blake2b(0x00, 0x60, 16))
            }

            // Compress K=7 roots: BLAKE2b(seed || FORS_ROOTS-ADRS || 7 roots)
            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            // = 32 + 32 + 7*32 = 288 = 0x120
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
            for { let i := 0 } lt(i, 7) { i := add(i, 1) } {
                mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
            }
            let forsPk := blake2b(0x00, 0x120, 16)

            // ============================================================
            // Hypertree (D=2, subtree_h=11, w=8, l=43, target_sum=208)
            // ============================================================
            let currentNode := forsPk
            let idxTree := htIdx
            let sigOff := 1952 // HT_START = AUTH_START + (K-1)*A*N = 128 + 1824

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x7FF) // 2^11 - 1
                idxTree := shr(11, idxTree)

                // WOTS_HASH base ADRS: layer, tree=idxTree, word1=idxLeaf (kp)
                let wotsAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(64, idxLeaf)))
                // countOff = sigOff + l*N = sigOff + 688
                let countOff := add(sigOff, 688)
                let count := shr(224, calldataload(add(sigBase, countOff)))

                // WOTS-message digest — nn=32 (full digest for the 43*3=129-bit slice).
                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := blake2b(0x00, 0x80, 32)

                // Validate WOTS+C digit sum == 208 (43 base-8 digits). 3=LOG_W ; 0x7=W-1.
                // Mismatch -> return false (uniform with forced-zero path).
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(mul(ii, 3), d), 0x7))
                }
                if iszero(eq(digitSum, 208)) { mstore(0x00, 0) return(0x00, 0x20) }

                // 43 WOTS chains (w=8: max 7 steps per chain)
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(mul(i, 3), d), 0x7)
                    let steps := sub(7, digit)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    // FIPS WOTS_HASH: word2=chain_address=i, word3=hash_address=digit+step
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

                // TREE Merkle auth path (11 levels): type=2, word2=height, word3=tree_index
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)

                for { let h := 0 } lt(h, 11) { h := add(h, 1) } {
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
                sigOff := add(authOff, 176) // 11*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)

            // ── BLAKE2b kernel (validated in test/Blake2bKernelTest.t.sol) ──
            // BLAKE2b(inPtr[0..inLen]) truncated to nn bytes via the 0x09 precompile.
            // Returns the digest top-aligned (nn=16 -> 16 bytes high, low zero; nn=32
            // -> full word). Scratch at S=0x800, clear of the SPHINCS+ working set.
            function blake2b(inPtr, inLen, nnLocal) -> result {
                let S := 0x800
                mstore(S, shl(224, 12)) // rounds = 12 (big-endian)
                // init state h: 8 little-endian 64-bit words. h0 = IV0 ^ 0x01010000 ^ nn.
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
                    // m field (128 bytes): zero then copy thisLen raw bytes (no swap)
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
                    mstore8(add(S, 212), isLast)                      // final-block flag
                    // compress; output overwrites the h field in place
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
