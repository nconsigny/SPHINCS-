// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SPHINCs_C12BlakeAsm — BLAKE2b twin of the plain-SPHINCS+ C12 verifier
/// @notice C12: plain SPHINCS+ n=16 h=20 d=5 h'=4 a=7 k=20 w=8 l=46. Sig 6,592 B.
/// @dev    BLAKE2b twin of src/keccak/SPHINCs-C12Asm.sol — IDENTICAL plain-SPHINCS+
///         construction (standard WOTS+ checksum, d=5 hypertree, standard FORS, FIPS
///         205 §4.2 uncompressed 32-byte ADRS, same signature byte layout) with only
///         the hash primitive swapped: keccak256(seed‖adrs‖payload) -> BLAKE2b(...),
///         built on the 0x09 (BLAKE2F) compression precompile by the blake2b() Yul
///         kernel (see SPHINCs-C13-BLAKE.sol for kernel notes); the single-block F/H
///         hashes bypass it through fixed precompile input buffers at 0x800/0x900
///         (same fast path as C13-BLAKE). F/H/T use nn=16;
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
        // Bare `assembly` (NOT memory-safe): sound only because every exit is an
        // in-assembly return/revert. Memory map: T_k/T_l and kernel preimages at
        // 0x00..0x600 (read by the kernel from 0x00); fixed F/H precompile buffers
        // at 0x800/0x900; blake2b() kernel scratch at 0xA00.
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 6592)) {
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

            // 0x00 still holds seed (T_k / T_l preimage prefix).

            // ───────────────────────── FORS (k=20, a=7) ─────────────────────────
            // FORS_TREE base: type=3, tree=treeIdx, kp=leafIdx
            let forsBase := or(or(shl(128, treeIdx), shl(96, 3)), shl(64, leafIdx))
            let forsOff := 32 // R is 32 bytes

            // Roots land in the T_k preimage slots 0x40 + 32*t.
            for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                let mdT := and(shr(mul(7, t), dVal), 0x7F)
                let treeOff := add(forsOff, mul(t, 128)) // 128 = sk(16) + auth(7*16)
                // Leaf F (height 0): word3 = (t << A) | mdT, A=7
                mstore(0x864, or(forsBase, or(shl(7, t), mdT)))
                mstore(0x884, and(calldataload(add(sigBase, treeOff)), N_MASK))
                // leaf digest -> its level-0 L/R slot in the H buffer
                ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, add(0x984, shl(5, and(mdT, 1))), 16))

                let authPtr := add(sigBase, add(treeOff, 16))
                let pathIdx := mdT
                for { let j := 0 } lt(j, 7) { j := add(j, 1) } {
                    let parentIdx := shr(1, pathIdx)
                    // sibling into the slot opposite the current node (branchless swap)
                    mstore(xor(0x9A4, shl(5, and(pathIdx, 1))), and(calldataload(add(authPtr, shl(4, j))), N_MASK))
                    // height = j+1 (word2); global y = (t << (A-1-j)) | parent (word3)
                    let globalY := or(shl(sub(6, j), t), parentIdx)
                    mstore(0x964, or(forsBase, or(shl(32, add(j, 1)), globalY)))
                    // parent digest -> the next level's node slot (0x984 at the root)
                    ok := and(ok, staticcall(gas(), 0x09, 0x900, 213, add(0x984, shl(5, and(parentIdx, 1))), 16))
                    pathIdx := parentIdx
                }
                mstore(add(0x40, shl(5, t)), mload(0x984))
            }

            // FORS_ROOTS compress (T_k over 20 roots): type=4. = 32+32+20*32 = 704 = 0x2C0
            mstore(0x20, or(or(shl(128, treeIdx), shl(96, 4)), shl(64, leafIdx)))
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

                // 43 message-digit chains. Digit 42 carries the final two bits + one zero pad bit.
                // digit i = (node >> (128 + 3i)) & 7 (LSB-first). Each chain runs in place
                // in the F val slot; its top lands in the T_l preimage slot 0x40 + 32*i.
                for { let i := 0 } lt(i, 43) { i := add(i, 1) } {
                    let digit := and(shr(add(128, mul(3, i)), currentNode), 7)
                    csum := add(csum, sub(7, digit))
                    mstore(0x884, and(calldataload(add(wotsPtr, shl(4, i))), N_MASK))
                    let chainBase := or(wotsBase, shl(32, i)) // chain_address = word2
                    // hash_step = word3 runs digit..6: the ADRS is the loop counter (keeps
                    // via-IR from rematerialising chainBase/digit per step; digit <= 7).
                    for { let a := or(chainBase, digit) let e := or(chainBase, 7) } lt(a, e) { a := add(a, 1) } {
                        mstore(0x864, a)
                        ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, 0x884, 16))
                    }
                    mstore(add(0x40, shl(5, i)), mload(0x884))
                }

                // 3 checksum chains (i = 43,44,45). csum<<7 then MSB-first 3-bit digits.
                let csumShifted := shl(7, csum)
                for { let j := 0 } lt(j, 3) { j := add(j, 1) } {
                    let digit := and(shr(sub(13, mul(3, j)), csumShifted), 7)
                    let i := add(43, j)
                    mstore(0x884, and(calldataload(add(wotsPtr, shl(4, i))), N_MASK))
                    let chainBase := or(wotsBase, shl(32, i))
                    for { let a := or(chainBase, digit) let e := or(chainBase, 7) } lt(a, e) { a := add(a, 1) } {
                        mstore(0x864, a)
                        ok := and(ok, staticcall(gas(), 0x09, 0x800, 213, 0x884, 16))
                    }
                    mstore(add(0x40, shl(5, i)), mload(0x884))
                }

                // WOTS_PK compression (T_l over 46 chain tops): type=1. = 32+32+46*32 = 1536 = 0x600
                mstore(0x20, or(or(shl(224, layer), shl(128, curTree)), or(shl(96, 1), shl(64, curLeaf))))
                let wotsPk := blake2b(0x00, 0x600, 16)

                // XMSS auth climb (h' = 4): XMSS_TREE type=2, layer, tree=curTree.
                let authOff := add(sigOff, 736) // 46 * 16
                let authPtr := add(sigBase, authOff)
                let xmssBase := or(or(shl(224, layer), shl(128, curTree)), shl(96, 2))
                let mIdx := curLeaf
                mstore(add(0x984, shl(5, and(mIdx, 1))), wotsPk)
                for { let h := 0 } lt(h, 4) { h := add(h, 1) } {
                    let parentIdx := shr(1, mIdx)
                    mstore(xor(0x9A4, shl(5, and(mIdx, 1))), and(calldataload(add(authPtr, shl(4, h))), N_MASK))
                    // height = h+1 (word2), tree_index = parentIdx (word3)
                    mstore(0x964, or(xmssBase, or(shl(32, add(h, 1)), parentIdx)))
                    ok := and(ok, staticcall(gas(), 0x09, 0x900, 213, add(0x984, shl(5, and(parentIdx, 1))), 16))
                    mIdx := parentIdx
                }

                currentNode := mload(0x984)
                sigOff := add(authOff, 64) // + 4 * 16
                curLeaf := and(curTree, 0xF)
                curTree := shr(4, curTree)
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
            // Scratch at 0xA00 (clear of the fixed F/H buffers). H_msg and T_k/T_l
            // only; F and H take the single-block fast path above.
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
