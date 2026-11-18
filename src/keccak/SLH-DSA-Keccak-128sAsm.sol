// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>
// SPDX-FileCopyrightText: 2026 Sagar Rana

pragma solidity ^0.8.28;

/// @title SLH-DSA-Keccak-128sAsm — plain SPHINCS+ at the NIST 128s parameters, FIPS 205 uncompressed ADRS
/// @dev C12's construction (`SPHINCs-C12Asm.sol`) re-parameterized to FIPS 205's SLH-DSA-128s set: plain
///      SPHINCS+ with the standard WOTS+ checksum and standard FORS, no counter grinding. A standard-parameter
///      baseline (2^64 signatures per key) next to the SPHINCs- sets, not a SPHINCs- variant.
///
///      Parameters: n=16, h=63, d=7, h'=9, a=12, k=14, w=16, l1=32, l2=3, l=35.
///      7,872 B signature.
///
///      Hash framing, key derivation, digest parsing and memory layout are C12's, unchanged:
///        F     : keccak(seed32 ‖ adrs32 ‖ M32)                      96 B
///        H     : keccak(seed32 ‖ adrs32 ‖ L32 ‖ R32)               128 B
///        T_l   : keccak(seed32 ‖ adrs32 ‖ v0..v34  (35 × 32B))    1,184 B
///        T_k   : keccak(seed32 ‖ adrs32 ‖ r0..r13  (14 × 32B))      512 B
///        Hmsg  : keccak(seed32 ‖ root32 ‖ R32 ‖ msg32 ‖ dom32)      160 B
///                where dom = 0xFF..FA (C12 uses 0xFF..FC, SLH-DSA-Keccak-128-24 0xFF..FB)
///      All outputs keccak256 truncated to 16 B. Same family as C12, so NOT FIPS 205 compliant: the
///      SHA-3 hash is keccak256 (not SHAKE256) and the framing is word-padded.
///
///      LSB-first digest parsing: md[t] = 12 bits at bit 12t (t = 0..13), treeIdx = 54 bits at
///      bit 168, leafIdx = 9 bits at bit 222. WOTS+ message digits are LSB-first base-16 digits of
///      the 128-bit node; the 3 checksum digits are MSB-first (SLH-DSA base_w), csum << 4.
///
///      ADRS (32 bytes): layer(4) ‖ tree(12) ‖ type(4) ‖ word1(4) ‖ word2(4) ‖ word3(4)
///        type 0 WOTS_HASH    word1=kp  word2=chain_address  word3=hash_step
///        type 1 WOTS_PK      word1=kp  word2=0              word3=0
///        type 2 XMSS_TREE    word1=0   word2=height         word3=tree_index
///        type 3 FORS_TREE    word1=kp  word2=height         word3=tree_index
///        type 4 FORS_ROOTS   word1=kp  word2=0              word3=0
///
///      Signature layout (7,872 bytes, constant):
///        R(32) ‖ FORS(k=14 × (sk 16B + auth 12×16B)) = 2,912
///              ‖ Hypertree(d=7 layers × (WOTS 35×16B + XMSS auth 9×16B)) = 4,928
///
///      Signer: script/slh_dsa_keccak_128s_signer.py (wraps script/jardin_spx_signer.py like
///      spx_fips_signer.py does for C12).
contract SLH_DSA_Keccak_128sAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        // NOTE: as in C12, this block uses Solidity's free-memory-pointer slot (0x40) and the zero
        // slot (0x60) as scratch and writes high memory without updating the FMP. That is only sound
        // because every exit below is an unconditional in-assembly `return`/`revert`, so Solidity never
        // regains control with a clobbered FMP. It is therefore NOT `memory-safe` in the Yul sense —
        // do not add the ("memory-safe") annotation and do not introduce a fall-through exit.
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 7872)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            // Reject non-canonical public keys (low 128 bits must be zero), as C12 and C13 do.
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

            // ── Hmsg: keccak(seed ‖ root ‖ R ‖ msg ‖ dom=0xFF..FA) = 160 B ──
            mstore(0x00, seed)
            mstore(0x20, root)
            mstore(0x40, calldataload(sigBase))       // R (32 B, full word)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA)
            let dVal := keccak256(0x00, 0xA0)

            // LSB-first digest parsing:
            //   md[t] for t in 0..13 : 12 bits at bit 12t
            //   treeIdx              : 54 bits at bit 168
            //   leafIdx              :  9 bits at bit 222
            let treeIdx := and(shr(168, dVal), 0x3FFFFFFFFFFFFF)
            let leafIdx := and(shr(222, dVal), 0x1FF)

            // Put seed back at 0x00 for all subsequent hash calls.
            mstore(0x00, seed)

            // ───────────────────────── FORS ─────────────────────────
            // FORS ADRS base: type=3, layer=0, tree=treeIdx, kp=leafIdx
            let forsBase := or(or(shl(128, treeIdx), shl(96, 3)), shl(64, leafIdx))
            // The 14 FORS trees sit back to back after R (32 B), 208 B each (sk 16 ‖ auth 12×16),
            // so one calldata pointer walks them all, and dVal is consumed A=12 bits per tree.
            let forsPtr := add(sigBase, 32)

            for { let t := 0 } lt(t, 14) { t := add(t, 1) } {
                // tIdx = word3 at height 0 = (t << A) | md[t]; the tree_index at height h is
                // tIdx >> h, and for h < A its low bit is the path parity bit.
                let tIdx := or(shl(12, t), and(dVal, 0xFFF))
                dVal := shr(12, dVal)

                // Leaf ADRS: height=0 (word2), word3 = tIdx
                mstore(0x20, or(forsBase, tIdx))
                mstore(0x40, and(calldataload(forsPtr), N_MASK))   // sk
                let node := and(keccak256(0x00, 0x60), N_MASK)
                forsPtr := add(forsPtr, 16)

                // Walk the A=12 auth levels: word2 = height climbs by one (1 << 32) per level.
                let heightAdrs := forsBase
                let authEnd := add(forsPtr, 192)   // 12 × 16
                for { } lt(forsPtr, authEnd) { forsPtr := add(forsPtr, 16) } {
                    let s := shl(5, and(tIdx, 1))
                    tIdx := shr(1, tIdx)
                    heightAdrs := add(heightAdrs, 0x100000000)
                    mstore(0x20, or(heightAdrs, tIdx))
                    mstore(xor(0x40, s), node)
                    mstore(xor(0x60, s), and(calldataload(forsPtr), N_MASK))
                    node := and(keccak256(0x00, 0x80), N_MASK)
                }
                // Stash root at 0x80 + t*0x20
                mstore(add(0x80, shl(5, t)), node)
            }

            // ── Compress 14 FORS roots: T_k(seed, FORS_ROOTS adrs, roots) ──
            // total = seed(32) + adrs(32) + 14*32 = 512 = 0x200, hashed in place from 0x40.
            mstore(0x40, seed)
            mstore(0x60, or(or(shl(128, treeIdx), shl(96, 4)), shl(64, leafIdx)))
            let currentNode := and(keccak256(0x40, 0x200), N_MASK)   // fors_pk

            // ───────────────────── Hypertree (d=7 layers) ─────────────────────
            let curTree := treeIdx
            let curLeaf := leafIdx
            // R(32) + FORS(2912), kept as an absolute calldata pointer
            let sigPtr  := add(sigBase, 2944)

            for { let layer := 0 } lt(layer, 7) { layer := add(layer, 1) } {
                // WOTS+ digits from currentNode (128-bit value in high 16B of word).
                //   msg_digit[i] (i=0..31) = (node >> (128 + 4i)) & 15   — LSB-first
                //   csum = Σ (15 - digit[i])
                //   csum_digit[j] (j=0..2) = (csum_shifted >> (12 - 4j)) & 15  (MSB-first, SLH-DSA)
                let wotsAdrs := or(or(shl(224, layer), shl(128, curTree)), shl(64, curLeaf))
                let outPtr := 0x80

                let msgDigits := shr(128, currentNode)   // digit i = (msgDigits >> 4i) & 15

                // csum = 32*15 - Σ digit[i], with a branch-free SWAR digit sum: fold nibble pairs
                // into 16 8-bit lanes (<= 30), byte pairs into 8 16-bit lanes (<= 60), then multiply
                // by sum(2^(16k), k=0..7) to collect every lane in bits 112..127 (<= 480 < 2^16,
                // so no carry crosses a lane and the result is exact).
                let csum := add(and(msgDigits, 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F), and(shr(4, msgDigits), 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F))
                csum := add(and(csum, 0x00FF00FF00FF00FF00FF00FF00FF00FF), and(shr(8, csum), 0x00FF00FF00FF00FF00FF00FF00FF00FF))
                csum := sub(480, and(shr(112, mul(csum, 0x00010001000100010001000100010001)), 0xFFFF))

                // ── 32 message-digit chains ──
                // Chain i runs hash_address digit_i..14, counting on the ADRS word itself.
                for { let msgEnd := add(sigPtr, 512) } lt(sigPtr, msgEnd) { sigPtr := add(sigPtr, 16) } {
                    let digit := and(msgDigits, 15)
                    msgDigits := shr(4, msgDigits)

                    mstore(0x40, and(calldataload(sigPtr), N_MASK))
                    let aEnd := or(wotsAdrs, 15)
                    for { let a := or(wotsAdrs, digit) } lt(a, aEnd) { a := add(a, 1) } {
                        mstore(0x20, a)
                        mstore(0x40, and(keccak256(0x00, 0x60), N_MASK))
                    }
                    mstore(outPtr, mload(0x40))
                    outPtr := add(outPtr, 0x20)
                    wotsAdrs := add(wotsAdrs, 0x100000000)   // chain_address += 1
                }

                // ── 3 checksum chains (i = 32, 33, 34) ──
                // csum_digit[j] = (csumShifted >> (12 - 4j)) & 15: read bits 12..15, then shift
                // csumShifted left by 4 for the next digit.
                let csumShifted := shl(4, csum)
                for { let csumEnd := add(sigPtr, 48) } lt(sigPtr, csumEnd) { sigPtr := add(sigPtr, 16) } {
                    let digit := and(shr(12, csumShifted), 15)
                    csumShifted := and(shl(4, csumShifted), 0xFFFF)
                    mstore(0x40, and(calldataload(sigPtr), N_MASK))
                    let aEnd := or(wotsAdrs, 15)
                    for { let a := or(wotsAdrs, digit) } lt(a, aEnd) { a := add(a, 1) } {
                        mstore(0x20, a)
                        mstore(0x40, and(keccak256(0x00, 0x60), N_MASK))
                    }
                    mstore(outPtr, mload(0x40))
                    outPtr := add(outPtr, 0x20)
                    wotsAdrs := add(wotsAdrs, 0x100000000)
                }

                // ── WOTS_PK compression via T_l (35 chain outputs) ──
                // total = seed(32) + adrs(32) + 35*32 = 1184 = 0x4A0, hashed in place from 0x40.
                mstore(0x40, seed)
                mstore(0x60, or(or(shl(224, layer), shl(128, curTree)), or(shl(96, 1), shl(64, curLeaf))))
                let merkleNode := and(keccak256(0x40, 0x4A0), N_MASK)   // wots_pk

                // ── XMSS auth climb (h' = 9), auth path right after the 35 WOTS values ──
                let xmssAdrs := or(or(shl(224, layer), shl(128, curTree)), shl(96, 2))
                let mIdx := curLeaf
                for { let authEnd := add(sigPtr, 144) } lt(sigPtr, authEnd) { sigPtr := add(sigPtr, 16) } {
                    let s := shl(5, and(mIdx, 1))
                    mIdx := shr(1, mIdx)
                    xmssAdrs := add(xmssAdrs, 0x100000000)
                    mstore(0x20, or(xmssAdrs, mIdx))
                    mstore(xor(0x40, s), merkleNode)
                    mstore(xor(0x60, s), and(calldataload(sigPtr), N_MASK))
                    merkleNode := and(keccak256(0x00, 0x80), N_MASK)
                }
                // sigPtr now points at the next layer's WOTS signature.

                currentNode := merkleNode

                // Advance: leaf = tree & 0x1FF, tree = tree >> 9.
                curLeaf := and(curTree, 0x1FF)
                curTree := shr(9, curTree)
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
