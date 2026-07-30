// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC13ShaAsm — SHA-256 "minimal twin" of the C13 verifier
/// @notice C13: W+C_F+C h=22 d=2 a=19 k=7 w=8 l=43 target_sum=208 sig=3688.
/// @dev    SHA-256 + 22-byte compressed ADRSc twin of src/SPHINCs-C13Asm.sol
///         (the keccak FIPS-uncompressed C13). IDENTICAL construction — same
///         WOTS+C / FORS+C counter-grinding, same signature byte layout, same
///         one-shot H_msg, same forced-zero FORS tree — only the hash primitive
///         (keccak256 → SHA-256 precompile 0x02, framed as
///         SHA-256(PK.seed‖toByte(0,48)‖ADRSc‖payload)[0..15]), the address
///         (FIPS uncompressed 32 B → FIPS §11.2 compressed 22-byte ADRSc), and
///         the parse order (MSB-first / FIPS base_2b instead of LSB-first) change.
///
///         NOT FIPS SLH-DSA: WOTS+C/FORS+C has no FIPS analog; one-shot H_msg,
///         no context envelope. Research "SHA flavour" of C13. Vectors:
///         script/signer.py c13-sha (hash=sha2, adrs_mode=adrsc, parse=msb).
///         See src/sha/SPHINCs-C11-SHA.sol for the shared ADRSc / memory notes.
contract SphincsC13ShaAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 3688)) {
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

            // MSB-first digest parsing (K=7, A=19, H=22; K*A=133):
            //   FORS idx i (19 bit): (dWord >> (237 - 19i)) & 0x7FFFF   [237 = 256 - A]
            //   htIdx     (22 bit): (dWord >> 101) & 0x3FFFFF           [101 = 256 - K*A - H]
            //   forced-zero idx K-1=6: (dWord >> 123) & 0x7FFFF         [123 = 256 - K*A]
            if and(shr(123, dWord), 0x7FFFF) { mstore(0x00, 0) return(0x00, 0x20) }
            let htIdx := and(shr(101, dWord), 0x3FFFFF)
            let idxLeaf0 := and(htIdx, 0x7FF)   // SUBTREE_H = 11
            let idxTree0 := shr(11, htIdx)

            mstore(0x00, seed)
            mstore(0x20, 0)

            let forsBase := or(shl(184, idxTree0), or(shl(176, 3), shl(144, idxLeaf0)))

            // ──────────────────────── FORS+C (K=7, A=19) ────────────────────────
            for { let t := 0 } lt(t, 6) { t := add(t, 1) } {
                let mdT := and(shr(sub(237, mul(19, t)), dWord), 0x7FFFF)
                let sk := and(calldataload(add(sigBase, add(16, shl(4, t)))), N_MASK)
                mstore(0x40, or(forsBase, shl(80, or(shl(19, t), mdT))))
                mstore(0x56, sk)
                if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                let node := and(mload(0x80), N_MASK)

                let pathIdx := mdT
                // AUTH_START = 16 + K*N = 128; per-tree auth = A*N = 304
                let authPtr := add(sigBase, add(128, mul(t, 304)))
                for { let hh := 0 } lt(hh, 19) { hh := add(hh, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, hh))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2 = height = hh+1; word3 = (t << (A-1-hh)) | parentIdx
                    mstore(0x40, or(forsBase, or(shl(112, add(hh, 1)), shl(80, or(shl(sub(18, hh), t), parentIdx)))))
                    switch and(pathIdx, 1)
                    case 0 { mstore(0x56, node)    mstore(0x66, sibling) }
                    default { mstore(0x56, sibling) mstore(0x66, node) }
                    if iszero(staticcall(gas(), 0x02, 0x00, 0x76, 0x80, 0x20)) { revert(0, 0) }
                    node := and(mload(0x80), N_MASK)
                    pathIdx := parentIdx
                }
                mstore(add(0x100, shl(5, t)), node)
            }

            // Forced-zero tree (t=K-1=6)
            {
                let lastSecret := and(calldataload(add(sigBase, add(16, shl(4, 6)))), N_MASK) // 16+6*16=112
                mstore(0x40, or(forsBase, shl(80, shl(19, 6))))   // word3 = 6 << A
                mstore(0x56, lastSecret)
                if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                mstore(0x1C0, and(mload(0x80), N_MASK))   // 0x100 + 6*0x20
            }

            // T_k: compress K=7 roots. input = 16+48+22+7*16 = 198 = 0xC6
            mstore(0x40, or(shl(184, idxTree0), or(shl(176, 4), shl(144, idxLeaf0))))
            for { let t := 0 } lt(t, 7) { t := add(t, 1) } {
                mstore(add(0x56, shl(4, t)), mload(add(0x100, shl(5, t))))
            }
            if iszero(staticcall(gas(), 0x02, 0x00, 0xC6, 0x80, 0x20)) { revert(0, 0) }
            let currentNode := and(mload(0x80), N_MASK)

            // ──────────────────── Hypertree (D=2, subtree_h=11) ────────────────────
            let idxTree := htIdx
            let sigOff := 1952   // HT_START = 128 + (K-1)*A*N = 128 + 6*304

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x7FF)
                idxTree := shr(11, idxTree)
                let wotsBase := or(shl(248, layer), or(shl(184, idxTree), shl(144, idxLeaf)))

                let countOff := add(sigOff, 688)   // l*N = 43*16
                let count := shr(224, calldataload(add(sigBase, countOff)))

                mstore(0x40, wotsBase)
                mstore(0x56, currentNode)
                mstore(0x66, shl(224, count))
                if iszero(staticcall(gas(), 0x02, 0x00, 0x6A, 0x80, 0x20)) { revert(0, 0) }
                let d := mload(0x80)

                // WOTS+C digit sum == 208 (43 base-8 digits, MSB-first: digit i @ (253-3i))
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(sub(253, mul(3, ii)), d), 0x7))
                }
                if iszero(eq(digitSum, 208)) { mstore(0x00, 0) return(0x00, 0x20) }

                let wotsPtr := add(sigBase, sigOff)
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(sub(253, mul(3, i)), d), 0x7)
                    let steps := sub(7, digit)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsBase, shl(112, i))
                    for { let step := 0 } lt(step, steps) { step := add(step, 1) } {
                        mstore(0x40, or(chainBase, shl(80, add(digit, step))))
                        mstore(0x56, val)
                        if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                        val := and(mload(0x80), N_MASK)
                    }
                    mstore(add(0x100, shl(5, i)), val)
                }

                // T_l: input = 16+48+22+43*16 = 774 = 0x306
                mstore(0x40, or(shl(248, layer), or(shl(184, idxTree), or(shl(176, 1), shl(144, idxLeaf)))))
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    mstore(add(0x56, shl(4, i)), mload(add(0x100, shl(5, i))))
                }
                if iszero(staticcall(gas(), 0x02, 0x00, 0x306, 0x320, 0x20)) { revert(0, 0) }
                let wotsPk := and(mload(0x320), N_MASK)

                // Merkle climb (subtree_h = 11)
                let authOff := add(countOff, 4)
                let treeAdrs := or(shl(248, layer), or(shl(184, idxTree), shl(176, 2)))
                let merkleNode := wotsPk
                let mIdx := idxLeaf
                let merklePtr := add(sigBase, authOff)
                for { let hh := 0 } lt(hh, 11) { hh := add(hh, 1) } {
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
                sigOff := add(authOff, 176)   // subtree_h*N = 11*16
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
