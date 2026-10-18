// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsC10ShaAsm — SHA-256 twin of the C10 verifier
/// @notice C10: W+C_F+C h=18 d=2 a=11 k=13 w=8 l=43 target_sum=205 sig=4008.
/// @dev    SHA-256 + 22-byte compressed ADRSc twin of src/keccak/SPHINCs-C10Asm.sol.
///         The construction is identical — same WOTS+C / FORS+C counter-grinding,
///         same signature byte layout, same one-shot H_msg, same forced-zero FORS
///         tree. Hash and address change together, because FIPS 205 pairs each hash
///         family with its own address form (§11.1 SHAKE with the uncompressed
///         32-byte ADRS, §11.2 SHA-2 with ADRSc):
///           1. hash:   keccak256 opcode → SHA-256 precompile (0x02), every F/H/T
///              framed as SHA-256(PK.seed‖toByte(0,48)‖ADRSc‖payload)[0..15]. The
///              pad makes PK.seed fill exactly one SHA-256 block, so that block's
///              compression is constant for a given key.
///           2. address: FIPS uncompressed 32-byte ADRS → FIPS §11.2 compressed
///              22-byte ADRSc; and digest/digit parsing is MSB-first (FIPS base_2b
///              order) instead of the keccak family's LSB-first.
///
///         Not FIPS SLH-DSA: WOTS+C/FORS+C counter-grinding has no FIPS analog, and
///         H_msg is one-shot (no MGF1, no context envelope). Vectors come from
///         script/signer.py c10-sha (cfg: hash=sha2, adrs_mode=adrsc, parse=msb).
///
///         Differs from C11-SHA only in h (18 vs 16): SUBTREE_H 9 vs 8, htIdx at
///         bit 95 vs 97 (256 - K*A - H), target_sum 205 vs 203, and one extra
///         auth-path node per hypertree layer (sig 4008 vs 3976).
///
///         ADRSc (22 B, FIPS 205 §11.2) is kept RIGHT-aligned in a word, bit offsets:
///           layer(1) bit168 ‖ tree(8) bit104 ‖ type(1) bit96 ‖
///           word1(4) bit64 ‖ word2(4) bit32 ‖ word3(4) bit0
///         and written with mstore(0x36, adrs): the top 10 bytes (always zero, adrs <
///         2^176) land in the zero pad 0x36..0x40, the ADRSc in 0x40..0x56, and the
///         payload slot at 0x56 is never touched.
///         Type→(word1,word2,word3): 0 WOTS_HASH (kp,chain,hash) · 1 WOTS_PK (kp,0,0)
///           · 2 TREE (0,height,index) · 3 FORS_TREE (kp,height,index) · 4 FORS_ROOTS (kp,0,0)
///
///         Memory prefix for every F/H (mirrors SLH-DSA-SHA2 kernel):
///           0x00..0x10 PK.seed ‖ 0x10..0x40 zeros (48 B) ‖ 0x40..0x56 ADRSc ‖ 0x56.. payload
///         T_k / T_l use a second copy of the prefix at 0x100 (payload from 0x156), so
///         FORS roots and WOTS chain tops are written straight into their preimage slot.
///         Each SHA-256 output is written directly into the payload slot the next call
///         reads: 0x56 for F chains; 0x56 + 16·(next index bit) on a Merkle/FORS climb,
///         with the sibling calldatacopy'd into the other half (xor(out, 0x30)).
///         The precompile reads its input before writing its output, so the overlap is
///         safe. Because outputs are written in place, a call that came back without
///         writing would leave its input to be read as its output (the identity): the
///         calls are pop()ed, and the call-failure note at the final compare explains
///         why no such call can reach the compare (returndatasize checks on the first
///         and the last call; out-of-gas halts the frame).
contract SphincsC10ShaAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000
            // N_MASK is applied only where a word's low 16 bytes could matter: R (H_msg
            // hashes the full 0x40 word) and the final root compare. Every other n-byte
            // value is either calldatacopy'd as exactly 16 bytes (sk, sibling, chain value)
            // or written as a 32-byte word (a precompile output, a root / chain top moved
            // into its T slot) whose low half is overwritten by the next write or lies past
            // the SHA-256 input length, so it never reaches a preimage.

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

            let sigBase := sig.offset

            // ── H_msg: one-shot SHA-256(seed ‖ root ‖ R ‖ msg ‖ domain) = 160 B ──
            mstore(0x00, pkSeed)
            mstore(0x20, pkRoot)
            mstore(0x40, and(calldataload(sigBase), N_MASK))
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            pop(staticcall(gas(), 0x02, 0x00, 0xA0, 0xA0, 0x20))
            // Precompile presence: on a chain where 0x02 is not a precompile the call to the
            // empty account "succeeds" with no return data and leaves the output slot as it
            // was. With in-place outputs every F/H/T would then be the identity, so this is
            // checked here, before any output is read (a precompile is there for the whole
            // call or not at all; this also catches a call-depth failure, which is likewise
            // the same for every call of this frame), and again on the last call before the
            // root compare. (review c12sha-precompile-presence)
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            let dWord := mload(0xA0)

            // MSB-first digest parsing (FIPS base_2b order). Fields, from the MSB:
            //   FORS idx i (11 bit): (dWord >> (245 - 11i)) & 0x7FF     [245 = 256 - A]
            //   htIdx     (18 bit): (dWord >> 95) & 0x3FFFF             [95 = 256 - K*A - H]
            //   forced-zero is FORS idx K-1=12: (dWord >> 113) & 0x7FF  [113 = 256 - K*A]
            if and(shr(113, dWord), 0x7FF) { mstore(0x00, 0) return(0x00, 0x20) }
            let htIdx := and(shr(95, dWord), 0x3FFFF)
            let idxLeaf0 := and(htIdx, 0x1FF)   // SUBTREE_H = 9
            let idxTree0 := shr(9, htIdx)

            // F/H prefix at 0x00 and T prefix at 0x100: seed (top 16 B) + 48 zero bytes.
            mstore(0x00, pkSeed)
            mstore(0x20, 0)
            mstore(0x100, pkSeed)
            mstore(0x120, 0)

            // forsBase: type=3 @96, tree=idxTree0 @104, kp=idxLeaf0 @64.
            let forsBase := or(shl(104, idxTree0), or(shl(96, 3), shl(64, idxLeaf0)))
            // T_k ADRSc (FORS_ROOTS, type=4) — nothing else writes 0x136..0x156 before T_k.
            mstore(0x136, or(shl(104, idxTree0), or(shl(96, 4), shl(64, idxLeaf0))))

            // ──────────────────────── FORS+C (K=13, A=11) ────────────────────────
            // g = (t << A) | mdT is the FIPS tree_index at height 0; shifting it right
            // once per level gives the parent tree_index, and its low bit is the
            // L/R position of the node being hashed next.
            let dd := dWord
            let authPtr := add(sigBase, 224)   // AUTH_START = 16 + K*N; per-tree auth = A*N = 176
            for { let t := 0 } lt(t, 12) { t := add(t, 1) } {
                let g := or(shl(11, t), shr(245, dd))
                dd := shl(11, dd)
                // Leaf F: word3 = (t << A) | mdT (height 0); sk = sig[16 + 16t]
                mstore(0x36, or(forsBase, g))
                calldatacopy(0x56, add(sigBase, add(16, shl(4, t))), 0x10)
                let out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x66, out, 0x20))
                let lvl := forsBase
                for { let end := add(authPtr, 176) } lt(authPtr, end) { authPtr := add(authPtr, 0x10) } {
                    calldatacopy(xor(out, 0x30), authPtr, 0x10)   // sibling into the other half
                    g := shr(1, g)
                    lvl := add(lvl, 0x100000000)                   // word2 = height + 1
                    mstore(0x36, or(lvl, g))                       // word3 = parent tree_index
                    out := add(0x56, shl(4, and(g, 1)))
                    pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                }
                mstore(add(0x156, shl(4, t)), mload(out))         // root t → T_k slot t
            }

            // Forced-zero tree (t=K-1=12): revealed root hashed under FORS_TREE leaf ADRS,
            // output straight into T_k slot 12 (0x156 + 12*16).
            mstore(0x36, or(forsBase, shl(11, 12)))   // word3 = 12 << A
            calldatacopy(0x56, add(sigBase, 208), 0x10)   // 16 + 12*16
            pop(staticcall(gas(), 0x02, 0x00, 0x66, 0x216, 0x20))

            // T_k: compress K=13 roots. input = 16+48+22+13*16 = 294 = 0x126.
            // Output → 0x56, the payload slot of the layer-0 WOTS-message digest.
            pop(staticcall(gas(), 0x02, 0x100, 0x126, 0x56, 0x20))

            // ──────────────────── Hypertree (D=2, subtree_h=9) ────────────────────
            let idxTree := htIdx
            let wotsPtr := add(sigBase, 2336)   // HT_START = 224 + (K-1)*A*N = 224 + 12*176

            for { let layer := 0 } lt(layer, 2) { layer := add(layer, 1) } {
                let idxLeaf := and(idxTree, 0x1FF)
                idxTree := shr(9, idxTree)
                let layerTree := or(shl(168, layer), shl(104, idxTree))
                // wotsBase: type=0, layer @168, tree=idxTree @104, kp=idxLeaf @64
                let wotsBase := or(layerTree, shl(64, idxLeaf))
                let countPtr := add(wotsPtr, 688)   // l*N = 43*16

                // WOTS-message digest d = SHA-256(seed‖zeros‖wotsBase‖currentNode‖count[4]).
                // currentNode is already at 0x56; only the top 4 bytes of the 0x66 word
                // (the count) fall inside the 0x6A-byte input.
                mstore(0x36, wotsBase)
                mstore(0x66, calldataload(countPtr))
                pop(staticcall(gas(), 0x02, 0x00, 0x6A, 0x80, 0x20))
                let d := mload(0x80)

                // WOTS+C digit sum == 205 (43 base-8 digits, MSB-first: digit i @ (253-3i))
                let digitSum := 0
                for { let ii := 0 } lt(ii, 43) { ii := add(ii, 1) } {
                    digitSum := add(digitSum, and(shr(sub(253, mul(3, ii)), d), 0x7))
                }
                if iszero(eq(digitSum, 205)) { mstore(0x00, 0) return(0x00, 0x20) }

                // Complete 43 chains. chainBase carries word2 = chain i (word3 = 0); the
                // hash step (word3, < 256) is its last byte 0x55, set with mstore8 and run
                // from the digit (MSB-first cursor on d) up to 6. Each F output lands
                // back in 0x56, the next step's input.
                let chainBase := wotsBase
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    calldatacopy(0x56, add(wotsPtr, shl(4, i)), 0x10)
                    mstore(0x36, chainBase)
                    for { let hs := shr(253, d) } lt(hs, 7) { hs := add(hs, 1) } {
                        mstore8(0x55, hs)
                        pop(staticcall(gas(), 0x02, 0x00, 0x66, 0x56, 0x20))
                    }
                    d := shl(3, d)
                    mstore(add(0x156, shl(4, i)), mload(0x56))   // chain top → T_l slot i
                    chainBase := add(chainBase, 0x100000000)    // word2 = chain + 1
                }

                // T_l: WOTS_pk = compress 43 chain tops. input = 16+48+22+43*16 = 774 = 0x306.
                // Output → the Merkle slot of leaf idxLeaf (0x56 if even, 0x66 if odd).
                mstore(0x136, or(wotsBase, shl(96, 1)))
                let mIdx := idxLeaf
                let out := add(0x56, shl(4, and(mIdx, 1)))
                pop(staticcall(gas(), 0x02, 0x100, 0x306, out, 0x20))

                // Merkle climb (subtree_h = 9). TREE: type=2, layer @168, tree @104
                let lvl := or(layerTree, shl(96, 2))
                let p := add(countPtr, 4)
                for { let end := add(p, 144) } lt(p, end) { p := add(p, 0x10) } {
                    calldatacopy(xor(out, 0x30), p, 0x10)
                    mIdx := shr(1, mIdx)
                    lvl := add(lvl, 0x100000000)
                    mstore(0x36, or(lvl, mIdx))
                    out := add(0x56, shl(4, and(mIdx, 1)))
                    pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                }
                // mIdx is 0 after subtree_h shifts, so the subtree root sits at 0x56:
                // the next layer's WOTS-digest payload, or the final root.
                wotsPtr := p   // subtree_h*N = 9*16 after the auth path
            }

            // Call-failure model. The SHA-256 calls are pop()ed, not guarded one by one,
            // and a call that came back without writing would leave its input in place as
            // its "output". Every way a 0x02 call can come back without 32 bytes ends the
            // frame before this compare:
            //  - 0x02 absent (empty account: success, no data) or the call-depth limit hit
            //    (failure, no data, no gas burnt): the same for every call of this frame, so
            //    the returndatasize check after the first call reverts before any output is
            //    read, and this check covers the call that produced the compared root.
            //  - out of gas: the call gets all but 1/64 of the gas left (EIP-150) and burns
            //    it, so a failing call of cost P leaves this frame at most P/63 gas; P is at
            //    most 360 (the 774-B T_l), so at most 5 gas: too little to reach another
            //    call or this check, and the frame halts.
            // On a chain where 0x02 can fail without burning the forwarded gas, restore the
            // per-call `if iszero(staticcall(..)) { revert(0, 0) }` guards.
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            valid := eq(and(mload(0x56), N_MASK), pkRoot)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
