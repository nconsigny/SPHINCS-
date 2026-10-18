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
///         the state init and the counter are LE-encoded (the IV as pre-swapped
///         constants, the < 2^16 counter as a 2-byte swap — no runtime bswap loop),
///         and the 64-byte LE output feeds straight back as the next block's state.
///
///         Single-block fast path: F (seed‖adrs‖val, 96 B) and H (seed‖adrs‖L‖R,
///         128 B) are one BLAKE2b block each and are ~90% of all hashes, so they skip
///         the kernel. Each has a permanent 213-byte precompile input buffer (F at
///         0x800, H at 0x900) whose rounds, nn=16 IV, seed and constant t/f word are
///         written once at entry; the hot loops write only the ADRS and payload and
///         route the 16-byte digest (= the first 16 LE output bytes) straight into the
///         slot that consumes it next (the F val slot for WOTS chains, the H L/R slot
///         of the next level for Merkle climbs). The kernel (scratch 0xA00) is left
///         with H_msg, the WOTS+C digest and the multi-block T_k/T_l.
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
        // exit is an unconditional in-assembly return/revert. Memory map: T_k/T_l and
        // kernel preimages at 0x00..0x5A0 (read by the kernel from 0x00); fixed F/H
        // precompile buffers at 0x800/0x900; kernel scratch at 0xA00. Bare `assembly`
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

            // ── Fixed single-block BLAKE2F input buffers (213 B each), set up once ──
            // rounds(4) ‖ h(64, LE IV with nn=16) ‖ m(128) ‖ t(16, LE) ‖ f(1).
            // F: m = seed@0x844 ‖ adrs@0x864 ‖ val@0x884 ‖ zero@0x8A4; t_0=96,  f=1.
            // H: m = seed@0x944 ‖ adrs@0x964 ‖ L@0x984  ‖ R@0x9A4;    t_0=128, f=1.
            // Outputs are 16 bytes written into the top half of a payload slot; every
            // other store into those slots is a full N_MASK'd word, so the low halves
            // stay zero. The h field is never an output target, so the IV stays valid.
            // L/R are 0x20 apart with bit 5 clear in 0x984, so xor(0x984, 0x20) = 0x9A4
            // keeps the Solady branchless swap.
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
            // AND-accumulated success of every fast-path STATICCALL, checked before the
            // final comparison (together with the precompile-presence check).
            let ok := 1

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
            // K-1=6 normal trees. Roots land in the T_k preimage slots 0x40 + 32*i.
            for { let i := 0 } lt(i, 6) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 19), dVal), 0x7FFFF) // 19=A-bit indices, shift i*A
                // Leaf hash F (height 0): word3 = (i << A) | treeIdx, A=19
                mstore(0x864, or(forsBase, or(shl(19, i), treeIdx)))
                mstore(0x884, and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK))
                // leaf digest -> its level-0 L/R slot in the H buffer
                ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, add(0x984, shl(5, and(treeIdx, 1))), 16))

                let pathIdx := treeIdx
                // AUTH_START = 16 + K*N = 128, auth per tree = A*N = 19*16 = 304
                let authPtr := add(sigBase, add(128, mul(i, 304)))

                // Walk A=19 auth path levels
                for { let h := 0 } lt(h, 19) { h := add(h, 1) } {
                    let parentIdx := shr(1, pathIdx)
                    // sibling into the slot opposite the current node (branchless swap)
                    mstore(xor(0x9A4, shl(5, and(pathIdx, 1))), and(calldataload(add(authPtr, shl(4, h))), N_MASK))
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx. 18 = A-1.
                    mstore(0x964, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(18, h), i), parentIdx))))
                    // parent digest -> the next level's node slot (0x984 at the root)
                    ok := and(ok, staticcall(gas(), 0x09, 0x900, 213, add(0x984, shl(5, and(parentIdx, 1))), 16))
                    pathIdx := parentIdx
                }
                mstore(add(0x40, shl(5, i)), mload(0x984))
            }

            // Last tree (forced-zero): secret is the revealed root, hashed under FORS_TREE leaf ADRS
            {
                // Forced-zero tree (forsTree=K-1=6) as leaf node 0: word3 = (6 << A). 19=A.
                mstore(0x864, or(forsBase, shl(19, 6)))
                mstore(0x884, and(calldataload(add(sigBase, add(16, shl(4, 6)))), N_MASK)) // 16+(K-1)*16=112
                // digest straight into T_k slot 0x40 + 6*0x20 = 0x100 (fresh memory, low half zero)
                ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, 0x100, 16))
            }

            // Compress K=7 roots: BLAKE2b(seed || FORS_ROOTS-ADRS || 7 roots)
            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            // = 32 + 32 + 7*32 = 288 = 0x120
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
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

                // 43 WOTS chains (w=8: max 7 steps per chain). Each chain runs in place
                // in the F val slot; its top lands in the T_l preimage slot 0x40 + 32*i.
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(0x884, and(calldataload(add(wotsPtr, shl(4, i))), N_MASK))
                    // FIPS WOTS_HASH: word2=chain_address=i, word3=hash_address=digit+step.
                    // The ADRS itself is the loop counter: hash_address runs digit..6, i.e.
                    // 7-digit steps (digit <= 7, so no carry out of word3). Written this way
                    // because via-IR's stack compressor otherwise rematerialises chainBase /
                    // digit / steps from d inside the step loop.
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

                // TREE Merkle auth path (11 levels): type=2, word2=height, word3=tree_index
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)
                mstore(add(0x984, shl(5, and(mIdx, 1))), wotsPk)

                for { let h := 0 } lt(h, 11) { h := add(h, 1) } {
                    let parentIdx := shr(1, mIdx)
                    mstore(xor(0x9A4, shl(5, and(mIdx, 1))), and(calldataload(add(merklePtr, shl(4, h))), N_MASK))
                    mstore(0x964, or(treeAdrs, or(shl(32, add(h, 1)), parentIdx)))
                    ok := and(ok, staticcall(gas(), 0x09, 0x900, 213, add(0x984, shl(5, and(parentIdx, 1))), 16))
                    mIdx := parentIdx
                }

                currentNode := mload(0x984)
                sigOff := add(authOff, 176) // 11*16
            }

            // Every fast-path STATICCALL must have succeeded, and 0x09 must really be the
            // BLAKE2F precompile: a call to a code-less 0x09 also "succeeds" but returns
            // nothing and writes no output, which would leave inputs in place as outputs
            // (the climbs would pass attacker-chosen auth nodes through). Required, not
            // defensive. The real precompile always returns 64 bytes (the last call above
            // is one).
            if iszero(and(ok, eq(returndatasize(), 64))) { revert(0, 0) }
            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)

            // ── BLAKE2b kernel (validated in test/Blake2bKernelTest.t.sol) ──
            // BLAKE2b(inPtr[0..inLen]) truncated to nn bytes via the 0x09 precompile.
            // Returns the digest top-aligned (nn=16 -> 16 bytes high, low zero; nn=32
            // -> full word). Scratch at S=0xA00, clear of the SPHINCS+ working set and
            // of the fixed F/H buffers at 0x800/0x900. Used for H_msg, the WOTS+C
            // digest and T_k/T_l only; F and H take the single-block fast path above.
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
