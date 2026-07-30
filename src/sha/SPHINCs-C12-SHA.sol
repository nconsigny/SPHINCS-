// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SPHINCs_C12ShaAsm — full FIPS 205 SLH-DSA-SHA2 at the C12 parameter set
/// @notice C12: plain SPHINCS+ n=16 h=20 d=5 h'=4 a=7 k=20 w=8 l=45. Sig 6,496 B.
/// @dev    The SHA-2 twin of the keccak C12 (src/SPHINCs-C12Asm.sol). Because C12
///         is plain SPHINCS+, it takes the FULL FIPS 205 SHA-2 instantiation
///         (unlike the WOTS+C/FORS+C compact twins which only borrow the hash):
///           • SHA-256 precompile (0x02), F/H/T = SHA-256(seed‖toByte(0,48)‖ADRSc‖M)[0..15]
///           • 22-byte compressed ADRSc (FIPS §11.2)
///           • MGF1-SHA-256 H_msg with the 0x00‖0x00 empty-context envelope
///             (external SLH-DSA.Verify), identical to src/SLH-DSA-SHA2-128-24verifier.sol
///           • MSB-first base_2b digit/index parsing (FIPS 205 Algorithm 4)
///           • standard WOTS+ checksum (l1=42 message + l2=3 checksum digits)
///         It is a true SLH-DSA *algorithm* at research params (NOT one of the 12
///         NIST sets, so it matches no published KAT). Vectors:
///         script/slh_dsa_sha2_c12_signer.py.
///
///         R is n=16 bytes on the wire (FIPS), so the signature is 6,496 B — 16 B
///         shorter than the keccak C12 (which used a 32-byte randomizer).
///         ADRSc bit offsets (see src/sha/SPHINCs-C11-SHA.sol): layer 248, tree 184,
///         type 176, word1 144, word2 112, word3 80.
contract SPHINCs_C12ShaAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external view returns (bool valid)
    {
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 6496)) {
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

            // ── H_msg: MGF1-SHA-256 with 0x00‖0x00 envelope (FIPS external) ──
            // inner = SHA-256(R ‖ seed ‖ root ‖ 0x00 0x00 ‖ message)  (82 B)
            mstore(0x00, calldataload(sigBase))   // R(16) ‖ junk
            mstore(0x10, seed)                    // seed(16)
            mstore(0x20, root)                    // root(16)
            mstore(0x30, 0)                       // 0x30,0x31 = 0x00 0x00 envelope
            mstore(0x32, message)                 // message(32)
            if iszero(staticcall(gas(), 0x02, 0x00, 0x52, 0x20, 0x20)) { revert(0, 0) }
            // outer = SHA-256(R ‖ seed ‖ inner ‖ I2OSP(0,4))  (68 B) → digest
            mstore(0x40, 0)
            if iszero(staticcall(gas(), 0x02, 0x00, 0x44, 0x100, 0x20)) { revert(0, 0) }
            let dWord := mload(0x100)

            // MSB-first parse (K=20 A=7; fors_bytes=18, then idx_tree(16b), idx_leaf(4b)):
            //   md[t] = (dWord >> (249 - 7t)) & 0x7F          [249 = 256 - A]
            //   idx_tree = (dWord >> 96) & 0xFFFF             [bytes 18..19]
            //   idx_leaf = (dWord >> 88) & 0xF                [byte 20 low nibble]
            let idxTree := and(shr(96, dWord), 0xFFFF)
            let idxLeaf := and(shr(88, dWord), 0xF)

            // F/H/T prefix: seed @0x00 (top 16 = value), 48 zero bytes 0x10..0x40.
            mstore(0x00, seed)
            mstore(0x20, 0)

            // forsBase: type=3, tree=idxTree, kp=idxLeaf.
            let forsBase := or(shl(184, idxTree), or(shl(176, 3), shl(144, idxLeaf)))

            // ──────────────────────── FORS (K=20, A=7) ────────────────────────
            for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                let mdT := and(shr(sub(249, mul(7, t)), dWord), 0x7F)
                // FORS tree t: sk + auth at 16 + t*128 (sk 16, auth 7*16=112)
                let treeOff := add(16, mul(t, 128))
                let sk := and(calldataload(add(sigBase, treeOff)), N_MASK)
                mstore(0x40, or(forsBase, shl(80, or(shl(7, t), mdT))))   // word3 = (t<<A)|mdT
                mstore(0x56, sk)
                if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                let node := and(mload(0x80), N_MASK)

                let pathIdx := mdT
                let authPtr := add(sigBase, add(treeOff, 16))
                for { let hh := 0 } lt(hh, 7) { hh := add(hh, 1) } {
                    let sibling := and(calldataload(add(authPtr, shl(4, hh))), N_MASK)
                    let parentIdx := shr(1, pathIdx)
                    // word2 = height = hh+1; word3 = (t << (A-1-hh)) | parentIdx
                    mstore(0x40, or(forsBase, or(shl(112, add(hh, 1)), shl(80, or(shl(sub(6, hh), t), parentIdx)))))
                    switch and(pathIdx, 1)
                    case 0 { mstore(0x56, node)    mstore(0x66, sibling) }
                    default { mstore(0x56, sibling) mstore(0x66, node) }
                    if iszero(staticcall(gas(), 0x02, 0x00, 0x76, 0x80, 0x20)) { revert(0, 0) }
                    node := and(mload(0x80), N_MASK)
                    pathIdx := parentIdx
                }
                mstore(add(0x100, shl(5, t)), node)
            }

            // FORS_ROOTS compress (T_l over K=20 roots). input = 16+48+22+20*16 = 406 = 0x196
            mstore(0x40, or(shl(184, idxTree), or(shl(176, 4), shl(144, idxLeaf))))
            for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                mstore(add(0x56, shl(4, t)), mload(add(0x100, shl(5, t))))
            }
            if iszero(staticcall(gas(), 0x02, 0x00, 0x196, 0x80, 0x20)) { revert(0, 0) }
            let currentNode := and(mload(0x80), N_MASK)

            // ──────────────────── Hypertree (d=5, h'=4) ────────────────────
            let curTree := idxTree
            let curLeaf := idxLeaf
            let sigOff := 2576   // R(16) + FORS(2560)

            for { let layer := 0 } lt(layer, 5) { layer := add(layer, 1) } {
                // WOTS+ digits from currentNode (MSB-first base_2b, w=8):
                //   msg digit i (i=0..41) = (currentNode >> (253 - 3i)) & 7
                //   csum = Σ (7 - digit); csum_digit j (j=0..2) = (csum<<7 >> (13 - 3j)) & 7
                let wotsBase := or(shl(248, layer), or(shl(184, curTree), shl(144, curLeaf)))
                let wotsPtr := add(sigBase, sigOff)

                let csum := 0
                for { let i := 0 } lt(i, 42) { i := add(i, 1) } {
                    let digit := and(shr(sub(253, mul(3, i)), currentNode), 7)
                    csum := add(csum, sub(7, digit))
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsBase, shl(112, i))   // word2 = chain = i
                    let steps := sub(7, digit)
                    for { let s := 0 } lt(s, steps) { s := add(s, 1) } {
                        mstore(0x40, or(chainBase, shl(80, add(digit, s))))   // word3 = hash step
                        mstore(0x56, val)
                        if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                        val := and(mload(0x80), N_MASK)
                    }
                    mstore(add(0x100, shl(5, i)), val)
                }
                let csumShifted := shl(7, csum)
                for { let j := 0 } lt(j, 3) { j := add(j, 1) } {
                    let digit := and(shr(sub(13, mul(3, j)), csumShifted), 7)
                    let i := add(42, j)
                    let val := and(calldataload(add(wotsPtr, shl(4, i))), N_MASK)
                    let chainBase := or(wotsBase, shl(112, i))
                    let steps := sub(7, digit)
                    for { let s := 0 } lt(s, steps) { s := add(s, 1) } {
                        mstore(0x40, or(chainBase, shl(80, add(digit, s))))
                        mstore(0x56, val)
                        if iszero(staticcall(gas(), 0x02, 0x00, 0x66, 0x80, 0x20)) { revert(0, 0) }
                        val := and(mload(0x80), N_MASK)
                    }
                    mstore(add(0x100, shl(5, i)), val)
                }

                // WOTS_PK compress (T_l over 45 tops). input = 16+48+22+45*16 = 806 = 0x326
                mstore(0x40, or(shl(248, layer), or(shl(184, curTree), or(shl(176, 1), shl(144, curLeaf)))))
                for { let i := 0 } lt(i, 45) { i := add(i, 1) } {
                    mstore(add(0x56, shl(4, i)), mload(add(0x100, shl(5, i))))
                }
                if iszero(staticcall(gas(), 0x02, 0x00, 0x326, 0x340, 0x20)) { revert(0, 0) }
                let wotsPk := and(mload(0x340), N_MASK)

                // XMSS climb (h' = 4). TREE: type=2, layer, tree=curTree.
                let authOff := add(sigOff, 720)   // 45*16
                let treeAdrs := or(shl(248, layer), or(shl(184, curTree), shl(176, 2)))
                let merkleNode := wotsPk
                let mIdx := curLeaf
                let merklePtr := add(sigBase, authOff)
                for { let hh := 0 } lt(hh, 4) { hh := add(hh, 1) } {
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
                sigOff := add(authOff, 64)   // h'*16 = 4*16
                curLeaf := and(curTree, 0xF)
                curTree := shr(4, curTree)
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
