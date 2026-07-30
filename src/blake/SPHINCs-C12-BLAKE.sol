// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SPHINCs_C12BlakeAsm — BLAKE2b twin of the plain-SPHINCS+ C12 verifier
/// @notice C12: plain SPHINCS+ n=16 h=20 d=5 h'=4 a=7 k=20 w=8 l=45. Sig 6,512 B.
/// @dev    BLAKE2b twin of src/keccak/SPHINCs-C12Asm.sol — IDENTICAL plain-SPHINCS+
///         construction (standard WOTS+ checksum, d=5 hypertree, standard FORS, FIPS
///         205 §4.2 uncompressed 32-byte ADRS, same signature byte layout) with only
///         the hash primitive swapped: keccak256(seed‖adrs‖payload) -> BLAKE2b(...),
///         built on the 0x09 (BLAKE2F) compression precompile by the blake2b() Yul
///         kernel (see SPHINCs-C13-BLAKE.sol for kernel notes). F/H/T use nn=16;
///         H_msg uses nn=32 (the WOTS digits come straight from the node, so there
///         is no separate WOTS-message hash). H_msg domain = 0xFF..FC (as keccak C12).
///         NOT FIPS (BLAKE2b has no FIPS 205 instantiation). `view` (precompile is a
///         staticcall). Adds the canonical public-key guard the keccak C12 lacks
///         and uses bare `assembly` (drops the keccak C12's unsound memory-safe tag).
///         Vectors: script/spx_blake_signer.py.
contract SPHINCs_C12BlakeAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 6512)) {
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
            let sigBase := sig.offset

            // ── Hmsg: BLAKE2b(seed ‖ root ‖ R ‖ msg ‖ dom=0xFF..FC) — nn=32 ──
            mstore(0x00, seed)
            mstore(0x20, root)
            mstore(0x40, calldataload(sigBase)) // R (32 B, full word; low 16 are zero)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC)
            let dVal := blake2b(0x00, 0xA0, 32)

            // LSB-first digest parsing (md[t]=7 bits at 7t; treeIdx 16b at 140; leafIdx 4b at 156)
            let treeIdx := and(shr(140, dVal), 0xFFFF)
            let leafIdx := and(shr(156, dVal), 0xF)

            mstore(0x00, seed)

            // ───────────────────────── FORS (k=20, a=7) ─────────────────────────
            // FORS_TREE base: type=3, tree=treeIdx, kp=leafIdx
            let forsBase := or(or(shl(128, treeIdx), shl(96, 3)), shl(64, leafIdx))
            let forsOff := 32 // R is 32 bytes

            for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                let mdT := and(shr(mul(7, t), dVal), 0x7F)
                let treeOff := add(forsOff, mul(t, 128)) // 128 = sk(16) + auth(7*16)
                let sk := and(calldataload(add(sigBase, treeOff)), N_MASK)
                // Leaf (height 0): word3 = (t << A) | mdT, A=7
                mstore(0x20, or(forsBase, or(shl(7, t), mdT)))
                mstore(0x40, sk)
                let node := blake2b(0x00, 0x60, 16)

                let authPtr := add(sigBase, add(treeOff, 16))
                let pathIdx := mdT
                for { let j := 0 } lt(j, 7) { j := add(j, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, j))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // height = j+1 (word2); global y = (t << (A-1-j)) | parent (word3)
                    let globalY := or(shl(sub(6, j), t), parentIdx)
                    mstore(0x20, or(forsBase, or(shl(32, add(j, 1)), globalY)))
                    let s := shl(5, and(pathIdx, 1))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), sibling)
                    node := blake2b(0x00, 0x80, 16)
                    pathIdx := parentIdx
                }
                mstore(add(0x80, shl(5, t)), node)
            }

            // FORS_ROOTS compress (T_k over 20 roots): type=4. = 32+32+20*32 = 704 = 0x2C0
            {
                let adrsRoots := or(or(shl(128, treeIdx), shl(96, 4)), shl(64, leafIdx))
                mstore(0x20, adrsRoots)
                for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                    mstore(add(0x40, shl(5, t)), mload(add(0x80, shl(5, t))))
                }
            }
            let currentNode := blake2b(0x00, 0x2C0, 16) // fors_pk

            // ───────────────────── Hypertree (d=5 layers, h'=4) ─────────────────────
            let curTree := treeIdx
            let curLeaf := leafIdx
            let sigOff := 2592 // R(32) + FORS(2560)

            for { let layer := 0 } lt(layer, 5) { layer := add(layer, 1) } {
                // WOTS_HASH base: type=0, layer, tree=curTree, kp=curLeaf
                let wotsBase := or(or(shl(224, layer), shl(128, curTree)), shl(64, curLeaf))
                let wotsPtr := add(sigBase, sigOff)
                let csum := 0

                // 42 message-digit chains. digit i = (node >> (128 + 3i)) & 7 (LSB-first).
                for { let i := 0 } lt(i, 42) { i := add(i, 1) } {
                    let digit := and(shr(add(128, mul(3, i)), currentNode), 7)
                    csum := add(csum, sub(7, digit))
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsBase, shl(32, i)) // chain_address = word2
                    let steps := sub(7, digit)
                    for { let s := 0 } lt(s, steps) { s := add(s, 1) } {
                        mstore(0x20, or(chainBase, add(digit, s))) // hash_step = word3
                        mstore(0x40, val)
                        val := blake2b(0x00, 0x60, 16)
                    }
                    mstore(add(0x80, shl(5, i)), val)
                }

                // 3 checksum chains (i = 42,43,44). csum<<7 then MSB-first 3-bit digits.
                let csumShifted := shl(7, csum)
                for { let j := 0 } lt(j, 3) { j := add(j, 1) } {
                    let digit := and(shr(sub(13, mul(3, j)), csumShifted), 7)
                    let i := add(42, j)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsBase, shl(32, i))
                    let steps := sub(7, digit)
                    for { let s := 0 } lt(s, steps) { s := add(s, 1) } {
                        mstore(0x20, or(chainBase, add(digit, s)))
                        mstore(0x40, val)
                        val := blake2b(0x00, 0x60, 16)
                    }
                    mstore(add(0x80, shl(5, i)), val)
                }

                // WOTS_PK compression (T_l over 45 chain tops): type=1. = 32+32+45*32 = 1504 = 0x5E0
                {
                    let pkAdrs := or(or(shl(224, layer), shl(128, curTree)),
                                      or(shl(96, 1), shl(64, curLeaf)))
                    mstore(0x20, pkAdrs)
                    for { let i := 0 } lt(i, 45) { i := add(i, 1) } {
                        mstore(add(0x40, shl(5, i)), mload(add(0x80, shl(5, i))))
                    }
                }
                let wotsPk := blake2b(0x00, 0x5E0, 16)

                // XMSS auth climb (h' = 4): XMSS_TREE type=2, layer, tree=curTree.
                let authOff := add(sigOff, 720) // 45 * 16
                let authPtr := add(sigBase, authOff)
                let xmssBase := or(or(shl(224, layer), shl(128, curTree)), shl(96, 2))
                let merkleNode := wotsPk
                let mIdx := curLeaf
                for { let h := 0 } lt(h, 4) { h := add(h, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, h))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    // height = h+1 (word2), tree_index = parentIdx (word3)
                    mstore(0x20, or(xmssBase, or(shl(32, add(h, 1)), parentIdx)))
                    let s := shl(5, and(mIdx, 1))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), sibling)
                    merkleNode := blake2b(0x00, 0x80, 16)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 64) // + 4 * 16
                curLeaf := and(curTree, 0xF)
                curTree := shr(4, curTree)
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
