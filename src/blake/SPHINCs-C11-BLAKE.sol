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
///         Yul kernel (see src/blake/SPHINCs-C13-BLAKE.sol for the kernel notes);
///         the single-block F/H hashes bypass it through fixed precompile input
///         buffers at 0x800/0x900 (same fast path as C13-BLAKE).
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
        // return/revert. Memory map: T_k/T_l and kernel preimages at 0x00..0x5A0
        // (read by the kernel from 0x00); fixed F/H precompile buffers at 0x800/0x900;
        // blake2b() kernel scratch at 0xA00.
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

            // ── Fixed single-block BLAKE2F input buffers (see SPHINCs-C13-BLAKE.sol) ──
            // F: m = seed@0x844 ‖ adrs@0x864 ‖ val@0x884 ‖ zero@0x8A4; t_0=96,  f=1.
            // H: m = seed@0x944 ‖ adrs@0x964 ‖ L@0x984  ‖ R@0x9A4;    t_0=128, f=1.
            // 16-byte outputs go into the top half of the payload slot read next; all
            // other stores there are full N_MASK'd words, so the low halves stay zero.
            mstore(0x800, shl(224, 12)) // rounds = 12 (big-endian)
            mstore(0x804, 0x18c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5) // IV0^0x01010010 ‖ IV1..3 (LE)
            mstore(0x824, 0xd182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b) // IV4..7 (LE)
            mstore(0x844, seed)
            mstore(0x8A4, 0) // F zero-pad word (fresh memory; explicit for clarity)
            mstore(0x8C4, 0x6000000000000000000000000000000001000000000000000000000000000000) // t_0=96 LE, f=1
            mstore(0x900, shl(224, 12))
            mstore(0x904, 0x18c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5)
            mstore(0x924, 0xd182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b)
            mstore(0x944, seed)
            mstore(0x9C4, 0x8000000000000000000000000000000001000000000000000000000000000000) // t_0=128 LE, f=1
            let ok := 1 // AND of every fast-path STATICCALL's success

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
            // K-1=12 normal trees. Roots land in the T_k preimage slots 0x40 + 32*i.
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 11), dVal), 0x7FF) // 11=A-bit indices
                // Leaf hash F (height 0): word3 = (i << A) | treeIdx, A=11
                mstore(0x864, or(forsBase, or(shl(11, i), treeIdx)))
                mstore(0x884, and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK))
                // leaf digest -> its level-0 L/R slot in the H buffer
                ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, add(0x984, shl(5, and(treeIdx, 1))), 16))

                let pathIdx := treeIdx
                // AUTH_START = 16 + K*N = 224, auth per tree = A*N = 11*16 = 176
                let authPtr := add(sigBase, add(224, mul(i, 176)))

                for { let h := 0 } lt(h, 11) { h := add(h, 1) } {
                    let parentIdx := shr(1, pathIdx)
                    // sibling into the slot opposite the current node (branchless swap)
                    mstore(xor(0x9A4, shl(5, and(pathIdx, 1))), and(calldataload(add(authPtr, shl(4, h))), N_MASK))
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx, A-1=10
                    mstore(0x964, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(10, h), i), parentIdx))))
                    // parent digest -> the next level's node slot (0x984 at the root)
                    ok := and(ok, staticcall(gas(), 0x09, 0x900, 213, add(0x984, shl(5, and(parentIdx, 1))), 16))
                    pathIdx := parentIdx
                }
                mstore(add(0x40, shl(5, i)), mload(0x984))
            }

            // Last tree (forced-zero)
            {
                mstore(0x864, or(forsBase, shl(11, 12))) // word3 = 12 << A
                mstore(0x884, and(calldataload(add(sigBase, add(16, shl(4, 12)))), N_MASK)) // 16+12*16=208
                // digest straight into T_k slot 0x40 + 12*0x20 = 0x1C0 (fresh memory, low half zero)
                ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, 0x1C0, 16))
            }

            // Compress 13 roots: = 32 + 32 + 13*32 = 480 = 0x1E0
            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
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

                // 43 WOTS chains (w=8: max 7 steps per chain), run in place in the F val
                // slot; each top lands in the T_l preimage slot 0x40 + 32*i.
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(0x884, and(calldataload(add(wotsPtr, shl(4, i))), N_MASK))
                    // word2=chain_address=i; word3=hash_address runs digit..6 (the ADRS is the
                    // loop counter, which keeps via-IR from rematerialising it per step).
                    let chainBase := or(wotsAdrs, shl(32, i))
                    for { let a := or(chainBase, and(shr(mul(i, 3), d), 0x7)) let e := or(chainBase, 7) } lt(a, e) { a := add(a, 1) } {
                        mstore(0x864, a)
                        ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, 0x884, 16))
                    }
                    mstore(add(0x40, shl(5, i)), mload(0x884))
                }

                // WOTS_PK compression: type=1, word1=idxLeaf. = 32+32+43*32 = 1440 = 0x5A0
                let pkAdrs := or(shl(224, layer), or(shl(128, idxTree), or(shl(96, 1), shl(64, idxLeaf))))
                mstore(0x20, pkAdrs)
                let wotsPk := blake2b(0x00, 0x5A0, 16)

                // TREE Merkle auth path (8 levels): type=2, word2=height, word3=tree_index
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)
                mstore(add(0x984, shl(5, and(mIdx, 1))), wotsPk)

                for { let h := 0 } lt(h, 8) { h := add(h, 1) } {
                    let parentIdx := shr(1, mIdx)
                    mstore(xor(0x9A4, shl(5, and(mIdx, 1))), and(calldataload(add(merklePtr, shl(4, h))), N_MASK))
                    mstore(0x964, or(treeAdrs, or(shl(32, add(h, 1)), parentIdx)))
                    ok := and(ok, staticcall(gas(), 0x09, 0x900, 213, add(0x984, shl(5, and(parentIdx, 1))), 16))
                    mIdx := parentIdx
                }

                currentNode := mload(0x984)
                sigOff := add(authOff, 128) // 8*16
            }

            // Every fast-path STATICCALL succeeded, and 0x09 is really BLAKE2F: a code-less
            // 0x09 "succeeds" with no output, and since outputs land in input slots the
            // climbs would then pass attacker-chosen auth nodes through. Required, not
            // defensive. The precompile always returns 64 bytes (the last call is one).
            if iszero(and(ok, eq(returndatasize(), 64))) { revert(0, 0) }
            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)

            // ── BLAKE2b kernel (validated in test/Blake2bKernelTest.t.sol) ──
            // Scratch at 0xA00 (clear of the fixed F/H buffers). H_msg, WOTS+C digest
            // and T_k/T_l only; F and H take the single-block fast path above.
            function blake2b(inPtr, inLen, nnLocal) -> result {
                let S := 0xA00
                mstore(S, shl(224, 12)) // rounds = 12 (big-endian)
                // init state h: IV as 8 little-endian 64-bit words, byte-swapped at authoring
                // time (no runtime bswap). h0 = IV0 ^ 0x01010000 ^ nn (kk=0); nn < 256 only
                // touches IV0's low byte = its first LE byte, hence the shl(248, nn).
                mstore(add(S, 4), xor(0x08c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5, shl(248, nnLocal)))
                mstore(add(S, 36), 0xd182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b)
                let processed := 0
                for {} 1 {} {
                    let thisLen := sub(inLen, processed)
                    let isLast := 1
                    if gt(thisLen, 128) { thisLen := 128 isLast := 0 }
                    // m field (128 bytes): thisLen raw bytes (no swap), zero-padded on the last block
                    mcopy(add(S, 68), add(inPtr, processed), thisLen)
                    if isLast { calldatacopy(add(add(S, 68), thisLen), calldatasize(), sub(128, thisLen)) }
                    processed := add(processed, thisLen)
                    // t_0 = processed as LE u64, t_1 = 0, f = isLast (byte S+212 = bit 120).
                    // 2-byte LE swap is exact because every inLen here is < 2^16 (max 0x600).
                    mstore(add(S, 196), or(or(shl(248, and(processed, 0xff)), shl(240, shr(8, processed))), shl(120, isLast)))
                    // compress; output (new state) overwrites the h field in place
                    if iszero(staticcall(gas(), 0x09, S, 213, add(S, 4), 64)) { revert(0, 0) }
                    if isLast { break }
                }
                result := mload(add(S, 4))
                if eq(nnLocal, 16) { result := and(result, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000) }
            }
        }
    }
}
