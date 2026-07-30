// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC10ShaAsm — SHA-256 "minimal twin" of the C10 verifier
/// @notice C10: W+C_F+C h=18 d=2 a=11 k=13 w=8 l=43 target_sum=205 sig=4008.
/// @dev    SHA-256 + 22-byte compressed ADRSc twin of src/keccak/SPHINCs-C10Asm.sol
///         (the keccak FIPS-uncompressed C10). The construction is IDENTICAL —
///         same WOTS+C / FORS+C counter-grinding, same signature byte layout,
///         same one-shot H_msg, same forced-zero FORS tree — only two things
///         change, as a coupled unit:
///           1. hash:   keccak256 opcode → SHA-256 precompile (0x02), every F/H/T
///              framed as SHA-256(PK.seed‖toByte(0,48)‖ADRSc‖payload)[0..15];
///           2. address: FIPS uncompressed 32-byte ADRS → FIPS §11.2 compressed
///              22-byte ADRSc; and digest/digit parsing is MSB-first (FIPS base_2b
///              order) instead of the keccak family's LSB-first.
///
///         Changing the hash WITHOUT changing the address is not a FIPS-shaped
///         SHA-2 instantiation: §11.1 (SHAKE) uses the full 32-byte ADRS, §11.2
///         (SHA-2) uses ADRSc plus the toByte(0,64-n) pad that makes PK.seed fill
///         exactly one SHA-256 block. EthereumPhone/PQ1's SPHINCsC10Asm swaps only
///         the hash and keeps the legacy JARDIN 32-byte ADRS with no pad, so it is
///         a self-consistent scheme but not the FIPS SHA-2 layout; this file is.
///
///         Still NOT FIPS SLH-DSA: WOTS+C/FORS+C counter-grinding has no FIPS
///         analog, and H_msg is one-shot (no MGF1, no context envelope). It is a
///         research "SHA flavour" of C10. Vectors come from
///         script/signer.py c10-sha (cfg: hash=sha2, adrs_mode=adrsc, parse=msb).
///
///         Differs from C11-SHA only in h (18 vs 16): SUBTREE_H 9 vs 8, htIdx at
///         bit 95 vs 97 (256 - K*A - H), target_sum 205 vs 203, and one extra
///         auth-path node per hypertree layer (sig 4008 vs 3976).
///
///         ADRSc (22 B, top-aligned in the 0x40 word; FIPS 205 §11.2), bit offsets:
///           layer(1) bit248 ‖ tree(8) bit184 ‖ type(1) bit176 ‖
///           word1(4) bit144 ‖ word2(4) bit112 ‖ word3(4) bit80
///         Type→(word1,word2,word3): 0 WOTS_HASH (kp,chain,hash) · 1 WOTS_PK (kp,0,0)
///           · 2 TREE (0,height,index) · 3 FORS_TREE (kp,height,index) · 4 FORS_ROOTS (kp,0,0)
///
///         Memory prefix for every F/H/T (mirrors SLH-DSA-SHA2 kernel):
///           0x00..0x10 PK.seed ‖ 0x10..0x40 zeros (48 B) ‖ 0x40..0x56 ADRSc ‖ 0x56.. payload
///         16-byte-aligned, so Merkle children use explicit L-first/R-second order.
contract SphincsC10ShaAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 4008)) {
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

            // ── H_msg: one-shot SHA-256(seed ‖ root ‖ R ‖ msg ‖ domain) = 160 B ──
            let R := and(calldataload(sigBase), N_MASK)
            mstore(0x00, seed)
            mstore(0x20, root)
            mstore(0x40, R)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            if iszero(staticcall(gas(), 0x02, 0x00, 0xA0, 0xA0, 0x20)) { revert(0, 0) }
            let dWord := mload(0xA0)

            // MSB-first digest parsing (FIPS base_2b order). Fields, from the MSB:
            //   FORS idx i (11 bit): (dWord >> (245 - 11i)) & 0x7FF     [245 = 256 - A]
            //   htIdx     (18 bit): (dWord >> 95) & 0x3FFFF             [95 = 256 - K*A - H]
            //   forced-zero is FORS idx K-1=12: (dWord >> 113) & 0x7FF  [113 = 256 - K*A]
            if and(shr(113, dWord), 0x7FF) { mstore(0x00, 0) return(0x00, 0x20) }
            let htIdx := and(shr(95, dWord), 0x3FFFF)
            let idxLeaf0 := and(htIdx, 0x1FF)   // SUBTREE_H = 9
            let idxTree0 := shr(9, htIdx)

            // F/H/T prefix: seed at 0x00 (top 16 = value), 48 zero bytes 0x10..0x40.
            mstore(0x00, seed)
            mstore(0x20, 0)

            // forsBase: type=3 @176, tree=idxTree0 @184, kp=idxLeaf0 @144.
            let forsBase := or(shl(184, idxTree0), or(shl(176, 3), shl(144, idxLeaf0)))

            // ──────────────────────── FORS+C (K=13, A=11) ────────────────────────
            for { let t := 0 } lt(t, 12) { t := add(t, 1) } {
                let mdT := and(shr(sub(245, mul(11, t)), dWord), 0x7FF)
                let sk := and(calldataload(add(sigBase, add(16, shl(4, t)))), N_MASK)
                // Leaf F: word3 = (t << A) | mdT (height 0)
                mstore(0x40, or(forsBase, shl(80, or(shl(11, t), mdT))))
                mstore(0x56, sk)
                if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                let node := and(mload(0x80), N_MASK)

                let pathIdx := mdT
                // AUTH_START = 16 + K*N = 224; per-tree auth = A*N = 176
                let authPtr := add(sigBase, add(224, mul(t, 176)))
                for { let hh := 0 } lt(hh, 11) { hh := add(hh, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, hh))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2 = height = hh+1; word3 = (t << (A-1-hh)) | parentIdx
                    mstore(0x40, or(forsBase, or(shl(112, add(hh, 1)), shl(80, or(shl(sub(10, hh), t), parentIdx)))))
                    switch and(pathIdx, 1)
                    case 0 { mstore(0x56, node)    mstore(0x66, sibling) }
                    default { mstore(0x56, sibling) mstore(0x66, node) }
                    if iszero(staticcall(gas(), 0x02, 0x00, 0x76, 0x80, 0x20)) { revert(0, 0) }
                    node := and(mload(0x80), N_MASK)
                    pathIdx := parentIdx
                }
                mstore(add(0x100, shl(5, t)), node)
            }

            // Forced-zero tree (t=K-1=12): revealed root hashed under FORS_TREE leaf ADRS
            {
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 12)))), N_MASK) // 16+12*16=208
                mstore(0x40, or(forsBase, shl(80, shl(11, 12))))   // word3 = 12 << A
                mstore(0x56, lastSecret)
                if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                mstore(0x280, and(mload(0x80), N_MASK))   // 0x100 + 12*0x20
            }

            // T_k: compress K=13 roots. input = 16+48+22+13*16 = 294 = 0x126
            mstore(0x40, or(shl(184, idxTree0), or(shl(176, 4), shl(144, idxLeaf0))))
            for { let t := 0 } lt(t, 13) { t := add(t, 1) } {
                mstore(add(0x56, shl(4, t)), mload(add(0x100, shl(5, t))))
            }
            if iszero(staticcall(gas(), 0x02, 0x00, 0x126, 0x80, 0x20)) { revert(0, 0) }
            let currentNode := and(mload(0x80), N_MASK)

            // ──────────────────── Hypertree (D=2, subtree_h=9) ────────────────────
            let idxTree := htIdx
            let sigOff := 2336   // HT_START = 224 + (K-1)*A*N = 224 + 12*176

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x1FF)
                idxTree := shr(9, idxTree)
                // wotsBase: type=0, layer @248, tree=idxTree @184, kp=idxLeaf @144
                let wotsBase := or(shl(248, layer), or(shl(184, idxTree), shl(144, idxLeaf)))

                let countOff := add(sigOff, 688)   // l*N = 43*16
                let count := shr(224, calldataload(add(sigBase, countOff)))

                // WOTS-message digest d = SHA-256(seed‖zeros‖wotsBase‖currentNode‖count[4])
                mstore(0x40, wotsBase)
                mstore(0x56, currentNode)
                mstore(0x66, shl(224, count))   // count in top 4 bytes at 0x66..0x6A
                if iszero(staticcall(gas(), 0x02, 0x00, 0x6A, 0x80, 0x20)) { revert(0, 0) }
                let d := mload(0x80)

                // WOTS+C digit sum == 205 (43 base-8 digits, MSB-first: digit i @ (253-3i))
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(sub(253, mul(3, ii)), d), 0x7))
                }
                if iszero(eq(digitSum, 205)) { mstore(0x00, 0) return(0x00, 0x20) }

                // Complete 43 chains
                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(sub(253, mul(3, i)), d), 0x7)
                    let steps := sub(7, digit)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsBase, shl(112, i))   // word2 = chain_address = i
                    for { let step := 0 } lt(step, steps) { step := add(step, 1) } {
                        mstore(0x40, or(chainBase, shl(80, add(digit, step))))   // word3 = hash step
                        mstore(0x56, val)
                        if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                        val := and(mload(0x80), N_MASK)
                    }
                    mstore(add(0x100, shl(5, i)), val)
                }

                // T_l: WOTS_pk = compress 43 chain tops. input = 16+48+22+43*16 = 774 = 0x306
                mstore(0x40, or(shl(248, layer), or(shl(184, idxTree), or(shl(176, 1), shl(144, idxLeaf)))))
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x56, shl(4, i)), mload(add(0x100, shl(5, i))))
                }
                if iszero(staticcall(gas(), 0x02, 0x00, 0x306, 0x320, 0x20)) { revert(0, 0) }
                let wotsPk := and(mload(0x320), N_MASK)

                // Merkle climb (subtree_h = 9). TREE: type=2, layer @248, tree @184
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(248, layer), or(shl(184, idxTree), shl(176, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)
                for { let hh := 0 } lt(hh, 9) { hh := add(hh, 1) } {
                    let sibling := and(calldataload(add(merklePtr, shl(4, hh))), N_MASK)
                    let parentIdx := shr(1, mIdx)
                    mstore(0x40, or(treeAdrs, or(shl(112, add(hh, 1)), shl(80, parentIdx))))
                    switch and(mIdx, 1)
                    case 0 { mstore(0x56, merkleNode) mstore(0x66, sibling)    }
                    default { mstore(0x56, sibling)    mstore(0x66, merkleNode) }
                    if iszero(staticcall(gas(), 0x02, 0x00, 0x76, 0x80, 0x20)) { revert(0, 0) }
                    merkleNode := and(mload(0x80), N_MASK)
                    mIdx := parentIdx
                }

                currentNode := merkleNode
                sigOff := add(authOff, 144)   // subtree_h*N = 9*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
