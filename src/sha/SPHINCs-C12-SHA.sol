// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SPHINCs_C12ShaAsm — full FIPS 205 SLH-DSA-SHA2 at the C12 parameter set
/// @notice C12: plain SPHINCS+ n=16 h=20 d=5 h'=4 a=7 k=20 w=8 l=46. Sig 6,576 B.
/// @dev    The SHA-2 twin of the keccak C12 (src/SPHINCs-C12Asm.sol). Because C12
///         is plain SPHINCS+, it takes the FULL FIPS 205 SHA-2 instantiation
///         (unlike the WOTS+C/FORS+C compact twins which only borrow the hash):
///           • SHA-256 precompile (0x02), F/H/T = SHA-256(seed‖toByte(0,48)‖ADRSc‖M)[0..15]
///           • 22-byte compressed ADRSc (FIPS §11.2)
///           • MGF1-SHA-256 H_msg with the 0x00‖0x00 empty-context envelope
///             (external SLH-DSA.Verify), identical to src/SLH-DSA-SHA2-128-24verifier.sol
///           • MSB-first base_2b digit/index parsing (FIPS 205 Algorithm 4)
///           • standard WOTS+ checksum (l1=43 message + l2=3 checksum digits)
///         It is a true SLH-DSA *algorithm* at research params (NOT one of the 12
///         NIST sets, so it matches no published KAT). Vectors:
///         script/slh_dsa_sha2_c12_signer.py.
///
///         R is n=16 bytes on the wire (FIPS), so the signature is 6,576 B — 16 B
///         shorter than the keccak C12 (which used a 32-byte randomizer).
///         ADRSc is kept RIGHT-aligned in a word and written with mstore(0x36, adrs)
///         (see src/sha/SPHINCs-C11-SHA.sol for the shared in-place kernel): bit
///         offsets layer 168, tree 104, type 96, word1 64, word2 32, word3 0. Every
///         SHA-256 output lands directly in the payload slot the next call reads;
///         T_l / T_k use a second prefix at 0x100 (payload from 0x156). A call that
///         came back without writing would therefore leave its input to be read as
///         its output: the calls are pop()ed, and the call-failure note at the final
///         compare explains why no such call can reach the compare.
contract SPHINCs_C12ShaAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 6576)) {
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

            let ptr := sig.offset

            // ── H_msg: MGF1-SHA-256 with 0x00‖0x00 envelope (FIPS external) ──
            // inner = SHA-256(R ‖ seed ‖ root ‖ 0x00 0x00 ‖ message)  (82 B)
            mstore(0x00, calldataload(ptr))       // R(16) ‖ junk
            mstore(0x10, pkSeed)                  // seed(16)
            mstore(0x20, pkRoot)                  // root(16)
            mstore(0x30, 0)                       // 0x30,0x31 = 0x00 0x00 envelope
            mstore(0x32, message)                 // message(32)
            pop(staticcall(gas(), 0x02, 0x00, 0x52, 0x20, 0x20))
            // Precompile presence: on a chain where 0x02 is not a precompile the call to the
            // empty account "succeeds" with no return data and leaves the output slot as it
            // was. With in-place outputs every F/H/T would then be the identity, so this is
            // checked here, before any output is read (a precompile is there for the whole
            // call or not at all; this also catches a call-depth failure, which is likewise
            // the same for every call of this frame), and again on the last call before the
            // root compare. (review c12sha-precompile-presence)
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            // outer = SHA-256(R ‖ seed ‖ inner ‖ I2OSP(0,4))  (68 B) → digest
            mstore(0x40, 0)
            pop(staticcall(gas(), 0x02, 0x00, 0x44, 0x100, 0x20))
            let dWord := mload(0x100)

            // MSB-first parse (K=20 A=7; fors_bytes=18, then idx_tree(16b), idx_leaf(4b)):
            //   md[t] = (dWord >> (249 - 7t)) & 0x7F          [249 = 256 - A]
            //   idx_tree = (dWord >> 96) & 0xFFFF             [bytes 18..19]
            //   idx_leaf = (dWord >> 88) & 0xF                [byte 20 low nibble]
            let idxTree := and(shr(96, dWord), 0xFFFF)
            let idxLeaf := and(shr(88, dWord), 0xF)

            // F/H prefix at 0x00 and T prefix at 0x100: seed (top 16 B) + 48 zero bytes.
            mstore(0x00, pkSeed)
            mstore(0x20, 0)
            mstore(0x100, pkSeed)
            mstore(0x120, 0)

            // forsBase: type=3, tree=idxTree, kp=idxLeaf.
            let forsBase := or(shl(104, idxTree), or(shl(96, 3), shl(64, idxLeaf)))

            // ──────────────────────── FORS (K=20, A=7) ────────────────────────
            // FORS tree t: sk + auth at 16 + t*128 (sk 16, auth 7*16=112).
            // g = (t << A) | md[t] is the FIPS tree_index at height 0; shifting it right
            // once per level gives the parent tree_index, and its low bit is the L/R
            // position of the node being hashed next.
            let dd := dWord
            ptr := add(ptr, 16)
            for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                let g := or(shl(7, t), shr(249, dd))
                dd := shl(7, dd)
                mstore(0x36, or(forsBase, g))
                calldatacopy(0x56, ptr, 0x10)
                let out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x66, out, 0x20))
                // Climb (unrolled), heights h = 1..7 (word2 = h); auth[h-1] sits at
                // ptr + 16h. The top level writes root t straight into T_k slot t.
                calldatacopy(xor(out, 0x30), add(ptr, 0x10), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x100000000, g)))
                out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x20), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x200000000, g)))
                out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x30), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x300000000, g)))
                out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x40), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x400000000, g)))
                out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x50), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x500000000, g)))
                out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x60), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x600000000, g)))
                out := add(0x56, shl(4, and(g, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x70), 0x10)
                g := shr(1, g)
                mstore(0x36, or(forsBase, or(0x700000000, g)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, add(0x156, shl(4, t)), 0x20))
                ptr := add(ptr, 0x80)
            }

            // FORS_ROOTS compress (T_l over K=20 roots). input = 16+48+22+20*16 = 406 = 0x196
            mstore(0x136, or(shl(104, idxTree), or(shl(96, 4), shl(64, idxLeaf))))
            pop(staticcall(gas(), 0x02, 0x100, 0x196, 0x80, 0x20))
            let currentNode := and(mload(0x80), N_MASK)

            // ──────────────────── Hypertree (d=5, h'=4) ────────────────────
            let curTree := idxTree
            let curLeaf := idxLeaf
            // ptr = sigBase + 2576 = R(16) + FORS(2560)

            for { let layer := 0 } lt(layer, 5) { layer := add(layer, 1) } {
                // WOTS+ digits from currentNode (MSB-first base_2b, w=8):
                //   msg digit i (i=0..42) = top 3 bits of the cursor, then shl 3
                //   digit 42 contains the final two message bits plus one zero pad bit
                //   (currentNode is N_MASKed, so that pad bit is 0)
                //   csum = Σ (7 - digit) = 301 - Σ digit (9 bits) → 3 base-8 digits,
                //   MSB-first (= (csum<<7 >> (13 - 3j)) & 7 for j=0..2)
                let layerTree := or(shl(168, layer), shl(104, curTree))
                // chainBase: WOTS_HASH (type 0), kp=curLeaf, word2 = chain i, word3 = 0
                let chainBase := or(layerTree, shl(64, curLeaf))
                let bits := currentNode
                let dsum := 0
                let topPtr := 0x156
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := shr(253, bits)
                    bits := shl(3, bits)
                    dsum := add(dsum, digit)
                    calldatacopy(0x56, ptr, 0x10)
                    // word3 = hash step (< 256, so its last byte 0x55, set with mstore8)
                    // runs from the digit up to 6; each F output lands back in 0x56, the
                    // next step's input.
                    mstore(0x36, chainBase)
                    for { let hs := digit } lt(hs, 7) { hs := add(hs, 1) } {
                        mstore8(0x55, hs)
                        pop(staticcall(gas(), 0x02, 0x00, 0x66, 0x56, 0x20))
                    }
                    mstore(topPtr, mload(0x56))                // chain top → T_l slot i
                    topPtr := add(topPtr, 0x10)
                    ptr := add(ptr, 0x10)
                    chainBase := add(chainBase, 0x100000000)  // word2 = chain + 1
                }
                bits := shl(247, sub(301, dsum))   // csum (9 bits) at the top of the cursor
                for { let j := 0 } lt(j, 3) { j := add(j, 1) } {
                    let digit := shr(253, bits)
                    bits := shl(3, bits)
                    calldatacopy(0x56, ptr, 0x10)
                    mstore(0x36, chainBase)
                    for { let hs := digit } lt(hs, 7) { hs := add(hs, 1) } {
                        mstore8(0x55, hs)
                        pop(staticcall(gas(), 0x02, 0x00, 0x66, 0x56, 0x20))
                    }
                    mstore(topPtr, mload(0x56))
                    topPtr := add(topPtr, 0x10)
                    ptr := add(ptr, 0x10)
                    chainBase := add(chainBase, 0x100000000)
                }

                // WOTS_PK compress (T_l over 46 tops). input = 16+48+22+46*16 = 822 = 0x336.
                // Output → the XMSS slot of leaf curLeaf (0x56 if even, 0x66 if odd).
                mstore(0x136, or(layerTree, or(shl(96, 1), shl(64, curLeaf))))
                let mIdx := curLeaf
                let out := add(0x56, shl(4, and(mIdx, 1)))
                pop(staticcall(gas(), 0x02, 0x100, 0x336, out, 0x20))

                // XMSS climb (h' = 4, unrolled). TREE: type=2, layer, tree=curTree,
                // word2 = height 1..4. mIdx is 0 after the last shift, so the XMSS root
                // lands at 0x56 (the next layer's WOTS input / the final root).
                let treeAdrs := or(layerTree, shl(96, 2))
                calldatacopy(xor(out, 0x30), ptr, 0x10)
                mIdx := shr(1, mIdx)
                mstore(0x36, or(treeAdrs, or(0x100000000, mIdx)))
                out := add(0x56, shl(4, and(mIdx, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x10), 0x10)
                mIdx := shr(1, mIdx)
                mstore(0x36, or(treeAdrs, or(0x200000000, mIdx)))
                out := add(0x56, shl(4, and(mIdx, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x20), 0x10)
                mIdx := shr(1, mIdx)
                mstore(0x36, or(treeAdrs, or(0x300000000, mIdx)))
                out := add(0x56, shl(4, and(mIdx, 1)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, out, 0x20))
                calldatacopy(xor(out, 0x30), add(ptr, 0x30), 0x10)
                mIdx := shr(1, mIdx)
                mstore(0x36, or(treeAdrs, or(0x400000000, mIdx)))
                pop(staticcall(gas(), 0x02, 0x00, 0x76, 0x56, 0x20))
                ptr := add(ptr, 0x40)
                currentNode := and(mload(0x56), N_MASK)
                curLeaf := and(curTree, 0xF)
                curTree := shr(4, curTree)
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
            //    most 372 (the 822-B WOTS_PK T_l), so at most 5 gas: too little to reach
            //    another call or this check, and the frame halts.
            // On a chain where 0x02 can fail without burning the forwarded gas, restore the
            // per-call `if iszero(staticcall(..)) { revert(0, 0) }` guards.
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            valid := eq(currentNode, pkRoot)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
