// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @title SphincsC13Asm — Stateless SPHINCS+ C13 verifier (shared, Yul-optimized)
/// @notice C13: W+C_F+C h=22 d=2 a=19 k=7 w=8 l=43 target_sum=208 sig=3688
/// @dev    Address layout: **FIPS 205 §4.2 uncompressed 32-byte ADRS**
///         (the SHAKE-instantiation form), with keccak256 substituted for
///         SHAKE-256 to stay native on EVM. C13 was the first verifier in this
///         repo on the FIPS ADRS layout; C7/C9 have since migrated to it, so every
///         live src/ keccak verifier now shares this layout. The JARDIN 8-byte-tree
///         / 4-word variants (C11, C12, SLH-DSA-keccak) are retired to legacy/.
///         See README "ADRS layout discipline".
///
///         ADRS layout (32 bytes, big-endian, FIPS 205 §4.2 Algorithm 1):
///           bytes  0.. 4   layer address          (uint32)
///           bytes  4..16   tree address           (96 bits, big-endian)
///           bytes 16..20   type                   (uint32)
///           bytes 20..24   word1 (type-dependent)
///           bytes 24..28   word2 (type-dependent)
///           bytes 28..32   word3 (type-dependent)
///
///         Type → (word1, word2, word3):
///           0 WOTS_HASH   (key_pair_address, chain_address, hash_address)
///           1 WOTS_PK     (key_pair_address, 0,             0)
///           2 TREE        (0,                tree_height,   tree_index)
///           3 FORS_TREE   (key_pair_address, tree_height,   tree_index)
///           4 FORS_ROOTS  (key_pair_address, 0,             0)
///
///         Tweakable hash: keccak256(seed32 ‖ adrs32 ‖ payload). Domain-separated
///         H_msg (160 bytes). Branchless Merkle swap (Solady), hoisted chain
///         address base.
contract SphincsC13Asm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        // NOTE: this block intentionally uses Solidity's free-memory-pointer slot
        // (0x40) and the zero slot (0x60) as scratch and writes high memory without
        // updating the FMP. That is only sound because every exit below is an
        // unconditional in-assembly `return`/`revert`, so Solidity never regains
        // control with a clobbered FMP. It is therefore NOT `memory-safe` in the
        // Yul sense — do not add the ("memory-safe") annotation and do not introduce
        // a normal (fall-through) exit from this block. (review C13-evm-f1)
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
            // the SLH-DSA-SHA2 verifier. Without this a non-top-aligned pkRoot can
            // never equal the always-N_MASK'd `currentNode` (line ~"valid := eq"),
            // silently bricking the account; pkSeed would also diverge from the
            // signer which always masks. Fail loudly instead. (review C13-V-f1)
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

            // htIdx = (digest >> 133) & (2^22-1)
            // PARAM IDENTITIES (must hold or signer/verifier desync silently —
            // review C13-V-f4): 133 = K*A = 7*19 ; 0x3FFFFF = 2^H-1 = 2^22-1.
            let htIdx := and(shr(133, digest), 0x3FFFFF)

            // FORS+C (K=7, A=19)
            //
            // FORS addressing — exact FIPS 205 FORS field split: the FORS
            // instance is keyed by the per-message hypertree leaf via the
            // canonical address fields —
            //   tree address      = idxTree0 = htIdx >> SUBTREE_H (bottom subtree)
            //   word1/kp           = idxLeaf0 = htIdx & (2^SUBTREE_H-1) (bottom leaf)
            //   word3/tree_index   = (forsTree << (A-height)) | node  (k FORS trees
            //                        indexed as one forest, FIPS 205 Alg. 17)
            //   word2/tree_height  = height
            // so each of the 2^h hypertree leaves selects a distinct FORS
            // instance. Matches C12 / SLH-DSA-SHA2 field semantics; the signer
            // mirrors this and derives the leaf secrets from the same leaf.
            let dVal := digest
            // Forced-zero: last FORS index (i=K-1=6) occupies bits [114,133)
            // (19-bit field). PARAM IDENTITIES (review C13-V-f4): 114 = (K-1)*A =
            // 6*19 ; 0x7FFFF = 2^A-1 = 2^19-1.
            // A well-formed-but-invalid signature is rejected by returning `false`
            // (the bool contract), NOT by an empty revert — so all soundness
            // rejections are uniform across callers. (review C13-V-f2 / C13-evm-f2)
            if and(shr(114, dVal), 0x7FFFF) { mstore(0x00, 0) return(0x00, 0x20) }

            let sigBase := sig.offset

            // SUBTREE_H = 11 (h/d = 22/2): split htIdx into bottom subtree + leaf.
            // PARAM IDENTITIES (review C13-V-f4): 0x7FF = 2^SUBTREE_H-1 = 2^11-1 ;
            // shift 11 = SUBTREE_H.
            let idxLeaf0 := and(htIdx, 0x7FF)
            let idxTree0 := shr(11, htIdx)
            // forsBase: tree=idxTree0 (shl 128), type=3 (shl 96), kp=idxLeaf0 (shl 64).
            // Per-site we OR in word2=height (shl 32) and word3=tree_index (shl 0).
            let forsBase := or(shl(128, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            // K-1=6 normal trees
            for { let i := 0 } lt(i, 6) { i := add(i, 1) } {
                let treeIdx := and(shr(mul(i, 19), dVal), 0x7FFFF) // 19=A-bit indices, shift i*A
                let secretVal := and(calldataload(add(sigBase, add(16, shl(4, i)))), N_MASK)
                // Leaf hash (height 0): word3 = (i << A) | treeIdx, A=19 (folds the k
                // FORS trees into one tree_index space; review C13-V-f4)
                let leafAdrs := or(forsBase, or(shl(19, i), treeIdx))
                mstore(0x20, leafAdrs)
                mstore(0x40, secretVal)
                let node := and(keccak256(0x00, 0x60), N_MASK)

                let pathIdx := treeIdx
                // AUTH_START = 16 + K*N = 128, auth per tree = A*N = 19*16 = 304
                let authPtr := add(sigBase, add(128, mul(i, 304)))

                // Walk A=19 auth path levels
                for { let h := 0 } lt(h, 19) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2=height=h+1; word3 = (i << (A-1-h)) | parentIdx.
                    // PARAM IDENTITY (review C13-V-f4): 18 = A-1; sub(18,h) stays
                    // >= 0 for h in [0,18] (the A=19 auth levels).
                    mstore(0x20, or(forsBase, or(shl(32, add(h, 1)), or(shl(sub(18, h), i), parentIdx))))
                    // Branchless Merkle swap (Solady)
                    let s := shl(5, and(pathIdx, 1))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), sibling)
                    node := and(keccak256(0x00, 0x80), N_MASK)
                    pathIdx := parentIdx
                }
                mstore(add(0x80, shl(5, i)), node)
            }

            // Last tree (forced-zero): secret is the revealed root, hashed under FORS_TREE leaf ADRS
            {
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 6)))), N_MASK) // 16+(K-1)*16=112
                // Forced-zero tree (forsTree=K-1=6) as leaf node 0: word3 = (6 << A).
                // PARAM IDENTITY (review C13-V-f4): 19 = A, 6 = K-1.
                mstore(0x20, or(forsBase, shl(19, 6)))
                mstore(0x40, lastSecret)
                // 0x80 + 6*0x20 = 0x80 + 0xC0 = 0x140
                mstore(0x140, and(keccak256(0x00, 0x60), N_MASK))
            }

            // Compress K=7 roots: keccak256(seed || FORS_ROOTS-ADRS || 7 roots)
            // FORS_ROOTS: tree=idxTree0, type=4 (shl 96), kp=idxLeaf0 (shl 64).
            // = 32 + 32 + 7*32 = 288 = 0x120
            mstore(0x20, or(shl(128, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))
            for { let i := 0 } lt(i, 7) { i := add(i, 1) } {
                mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
            }
            let forsPk := and(keccak256(0x00, 0x120), N_MASK)

            // ============================================================
            // Hypertree (D=2, subtree_h=11, w=8, l=43, target_sum=208)
            //
            // FIPS ADRS bit positions:
            //   layer        at shl(224, …)  bytes 0..4
            //   tree         at shl(128, …)  bytes 4..16 (96-bit address; top 4 B always 0)
            //   type         at shl( 96, …)  bytes 16..20
            //   word1 (kp)   at shl( 64, …)  bytes 20..24
            //   word2 (...)  at shl( 32, …)  bytes 24..28
            //   word3 (...)  at shl(  0, …)  bytes 28..32
            // ============================================================
            let currentNode := forsPk
            let idxTree := htIdx
            let sigOff := 1952 // HT_START = AUTH_START + (K-1)*A*N = 128 + 1824

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x7FF) // 2^11 - 1
                idxTree := shr(11, idxTree)

                // WOTS_HASH base ADRS for this WOTS keypair (type=0 implicit):
                //   layer, tree=idxTree, word1=idxLeaf (key_pair_address)
                let wotsAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(64, idxLeaf)))
                // countOff = sigOff + l*N = sigOff + 688
                let countOff := add(sigOff, 688)
                let count := shr(224, calldataload(add(sigBase, countOff)))

                // WOTS-message digest: hashAdrs is the WOTS_HASH base with word2/word3 = 0
                mstore(0x20, wotsAdrs)
                mstore(0x40, currentNode)
                mstore(0x60, count)
                let d := keccak256(0x00, 0x80)

                // Validate WOTS+C digit sum == TARGET_SUM (43 base-8 digits, 3 bits
                // each). PARAM IDENTITIES (review C13-V-f4): loop bound 43 = L ;
                // digit shift 3 = LOG_W ; mask 0x7 = W-1 = 2^LOG_W-1 ; 208 = TARGET_SUM.
                // A digit-sum mismatch is a well-formed-but-invalid signature ->
                // return `false` (uniform with the forced-zero path; review
                // C13-V-f2 / C13-evm-f2), not an empty revert.
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
                    // wotsAdrs already has word2=word3=0; OR in chain_address here.
                    let chainBase := or(wotsAdrs, shl(32, i))

                    for { let step := 0 } lt(step, steps) { step := add(step, 1) } {
                        mstore(0x20, or(chainBase, add(digit, step)))
                        mstore(0x40, val)
                        val := and(keccak256(0x00, 0x60), N_MASK)
                    }
                    mstore(add(0x80, shl(5, i)), val)
                }

                // WOTS_PK compression: type=1, word1=idxLeaf
                // = 32+32+43*32 = 1440 = 0x5A0
                let pkAdrs := or(shl(224, layer), or(shl(128, idxTree), or(shl(96, 1), shl(64, idxLeaf))))
                mstore(0x20, pkAdrs)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
                }
                let wotsPk := and(keccak256(0x00, 0x5A0), N_MASK)

                // TREE Merkle auth path (11 levels)
                //   type=2, word1=0 always, word2=tree_height, word3=tree_index
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(224, layer), or(shl(128, idxTree), shl(96, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)

                for { let h := 0 } lt(h, 11) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(merklePtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    // treeAdrs has word1=0, word2=0, word3=0; OR in height and index.
                    mstore(0x20, or(treeAdrs, or(shl(32, add(h, 1)), parentIdx)))
                    let s := shl(5, and(mIdx, 1))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), sibling)
                    merkleNode := and(keccak256(0x00, 0x80), N_MASK)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 176) // 11*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
