// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SPHINCs-C12Asm — plain SPHINCS+ (SPX) verifier, FIPS 205 uncompressed ADRS
/// @dev The C12 variant of the SPHINCs- family.  Unlike the WOTS+C / FORS+C
///      C-series (C7/C9/C11/C13), C12 is plain SPHINCS+ with standard WOTS+
///      checksum and standard FORS — a hypertree of depth d=5, per-layer XMSS
///      height h'=4.
///
///      Parameters: n=16, h=20, d=5, h'=4, a=7, k=20, w=8, l=46.
///      6,592 B signature.
///
///      Migrated from the JARDIN 32-byte ADRS to the FIPS 205 §4.2
///      uncompressed 32-byte ADRS + keccak256 (the canonical keccak-family
///      layout shared with C7/C9/C13). The signature byte layout and hash
///      structure are unchanged from the legacy verifier; only the ADRS word
///      positions move: JARDIN's 8-byte tree → FIPS's 12-byte tree, and the
///      WOTS chain/hash addresses from JARDIN ci(shl64)+cp(shl32) to FIPS
///      word2(shl32)+word3(shl0). The legacy JARDIN-layout C12 stays in
///      legacy/src/ as JardinSpxVerifier for the nconsigny/JARDIN repo.
///
///      Hash primitives (all keccak256 truncated to 16B):
///        F     : keccak(seed32 ‖ adrs32 ‖ M32)                      96 B
///        H     : keccak(seed32 ‖ adrs32 ‖ L32 ‖ R32)               128 B
///        T_l   : keccak(seed32 ‖ adrs32 ‖ v0..v45  (46 × 32B))    1,536 B
///        T_k   : keccak(seed32 ‖ adrs32 ‖ r0..r19  (20 × 32B))      704 B
///        Hmsg  : keccak(seed32 ‖ root32 ‖ R32 ‖ msg32 ‖ dom32)      160 B
///                where dom = 0xFF..FC (distinct from C11/T0/plain-FORS)
///
///      ADRS (32 bytes): layer(4) ‖ tree(12) ‖ type(4) ‖ word1(4) ‖ word2(4) ‖ word3(4)
///
///      C12 FIPS field mapping (FIPS 205 Table 1):
///        type 0 WOTS_HASH    word1=kp  word2=chain_address  word3=hash_step
///        type 1 WOTS_PK      word1=kp  word2=0              word3=0
///        type 2 XMSS_TREE    word1=0   word2=height         word3=tree_index
///        type 3 FORS_TREE    word1=kp  word2=height         word3=tree_index
///        type 4 FORS_ROOTS   word1=kp  word2=0              word3=0
///
///      Signature layout (6,592 bytes, constant):
///        R(32) ‖ FORS(k=20 × (sk 16B + auth 7×16B)) = 2,560
///              ‖ Hypertree(d=5 layers × (WOTS 46×16B + XMSS auth 4×16B)) = 4,000
contract SPHINCs_C12Asm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        // NOTE: this block intentionally uses Solidity's free-memory-pointer slot
        // (0x40) and the zero slot (0x60) as scratch and writes high memory without
        // updating the FMP. That is only sound because every exit below is an
        // unconditional in-assembly `return`/`revert`, so Solidity never regains
        // control with a clobbered FMP. It is therefore NOT `memory-safe` in the
        // Yul sense — do not add the ("memory-safe") annotation and do not introduce
        // a normal (fall-through) exit from this block. (matches C13, review C13-evm-f1)
        assembly {
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            if iszero(eq(sig.length, 6592)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            // Reject non-canonical public keys (low 128 bits must be zero), mirroring
            // the C13 verifier and the SHA-2 / BLAKE2b twins. Without this a
            // non-top-aligned pkRoot can never equal the always-N_MASK'd `currentNode`,
            // silently bricking the account, and pkSeed would diverge from the signer,
            // which always masks. Fail loudly instead.
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

            // ── Hmsg: keccak(seed ‖ root ‖ R ‖ msg ‖ dom=0xFF..FC) = 160 B ──
            mstore(0x00, seed)
            mstore(0x20, root)
            mstore(0x40, calldataload(sigBase))       // R (32 B, full word)
            mstore(0x60, message)
            mstore(0x80, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC)
            let dVal := keccak256(0x00, 0xA0)

            // LSB-first digest parsing (independent of ADRS layout):
            //   md[t] for t in 0..19 : 7 bits at bit t*7
            //   treeIdx              : 16 bits at bit 140
            //   leafIdx              :  4 bits at bit 156
            let treeIdx := and(shr(140, dVal), 0xFFFF)
            let leafIdx := and(shr(156, dVal), 0xF)

            // Put seed back at 0x00 for all subsequent hash calls.
            mstore(0x00, seed)

            // ───────────────────────── FORS ─────────────────────────
            // FORS ADRS base: type=3, layer=0, tree=treeIdx, kp=leafIdx
            //   = shl(128, treeIdx) | shl(96, 3) | shl(64, leafIdx)
            let forsBase := or(or(shl(128, treeIdx), shl(96, 3)), shl(64, leafIdx))
            // The 20 FORS trees sit back to back after R (32 B), 128 B each
            // (sk 16 ‖ auth 7×16), so one calldata pointer walks them all, and dVal is
            // consumed A=7 bits per tree (treeIdx/leafIdx above are already extracted).
            let forsPtr := add(sigBase, 32)

            for { let t := 0 } lt(t, 20) { t := add(t, 1) } {
                // tIdx = word3 at height 0 = (t << A) | md[t]  (global y across 20 trees,
                // A=7). The tree_index at height h is tIdx >> h (= (t << (A-h)) | (md[t] >> h)),
                // and for h < A its low bit is the path parity bit, so one shift per level.
                let tIdx := or(shl(7, t), and(dVal, 0x7F))
                dVal := shr(7, dVal)

                // Leaf ADRS: height=0 (word2), word3 = tIdx
                mstore(0x20, or(forsBase, tIdx))
                mstore(0x40, and(calldataload(forsPtr), N_MASK))   // sk
                let node := and(keccak256(0x00, 0x60), N_MASK)
                forsPtr := add(forsPtr, 16)

                // Walk the A=7 auth levels: word2 = height climbs by one (1 << 32) per
                // level, word3 = tIdx >> height.
                let heightAdrs := forsBase
                let authEnd := add(forsPtr, 112)   // 7 × 16
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

            // ── Compress 20 FORS roots: T_k(seed, FORS_ROOTS adrs, roots) ──
            // total = seed(32) + adrs(32) + 20*32 = 704 = 0x2C0
            // Hash in place: the 20 roots already sit at 0x80+32t, so put seed and
            // ADRS in the dead scratch words 0x40/0x60 and hash from 0x40 (same bytes
            // as seed@0x00 ‖ adrs@0x20 ‖ roots@0x40, without a copy-down loop).
            mstore(0x40, seed)
            mstore(0x60, or(or(shl(128, treeIdx), shl(96, 4)), shl(64, leafIdx)))
            let currentNode := and(keccak256(0x40, 0x2C0), N_MASK)   // fors_pk

            // ───────────────────── Hypertree (d=5 layers) ─────────────────────
            let curTree := treeIdx
            let curLeaf := leafIdx
            // R(32) + FORS(2560), kept as an absolute calldata pointer
            let sigPtr  := add(sigBase, 2592)

            for { let layer := 0 } lt(layer, 5) { layer := add(layer, 1) } {
                // WOTS+ digits from currentNode (128-bit value in high 16B of word).
                //   msg_digit[i] (i=0..42) = (node >> (128 + 3i)) & 7   — LSB-first
                //   digit 42 contains the final two message bits plus one zero pad bit
                //   csum = Σ (7 - digit[i])
                //   csum_digit[j] (j=0..2) = (csum_shifted >> (13 - 3j)) & 7  (MSB-first, SLH-DSA)

                // WOTS ADRS base for this layer: type=0, layer, tree=curTree, kp=curLeaf.
                // Both chain loops below walk by pointer: sigPtr steps 16 B per chain,
                // wotsAdrs steps chain_address (word2) by 1 << 32, outPtr steps 32 B; the
                // checksum loop continues where the message loop stopped (chain 43).
                let wotsAdrs := or(or(shl(224, layer), shl(128, curTree)), shl(64, curLeaf))
                let outPtr := 0x80

                let msgDigits := shr(128, currentNode)   // digit i = (msgDigits >> 3i) & 7

                // csum = Σ (7 - digit[i]) = 43*7 - Σ digit[i], with a branch-free SWAR digit
                // sum (constants assume 43 digits, LOG_W=3): the digits are bits [0,129) of
                // msgDigits (< 2^128). Fold digit pairs into 22 6-bit lanes (<= 14), lane
                // pairs into 11 12-bit lanes (<= 28), then multiply by sum(2^(12k), k=0..10)
                // to collect every lane in bits 120..131. Each partial sum is <= 43*7 = 301
                // < 4096, so no carry crosses a lane and the result is exact.
                let csum := add(and(msgDigits, 0x1C71C71C71C71C71C71C71C71C71C71C7), and(shr(3, msgDigits), 0x1C71C71C71C71C71C71C71C71C71C71C7))
                csum := add(and(csum, 0x3F03F03F03F03F03F03F03F03F03F03F), and(shr(6, csum), 0x3F03F03F03F03F03F03F03F03F03F03F))
                csum := sub(301, and(shr(120, mul(csum, 0x1001001001001001001001001001001)), 0xFFF))

                // ── 43 message-digit chains ──
                // Chain i runs hash_address digit_i..6, so the step loop counts on the ADRS
                // word itself (word3 = hash_address is the low 32 bits, zero in wotsAdrs).
                // The chain value lives in memory at 0x40 (its slot in the F input
                // seed ‖ adrs ‖ value), so a step is just store ADRS, hash, mask, store.
                for { let msgEnd := add(sigPtr, 688) } lt(sigPtr, msgEnd) { sigPtr := add(sigPtr, 16) } {
                    let digit := and(msgDigits, 7)
                    msgDigits := shr(3, msgDigits)

                    mstore(0x40, and(calldataload(sigPtr), N_MASK))
                    // FIPS WOTS_HASH: chain_address=word2 (shl 32), hash_address=word3 (shl 0)
                    let aEnd := or(wotsAdrs, 7)
                    for { let a := or(wotsAdrs, digit) } lt(a, aEnd) { a := add(a, 1) } {
                        mstore(0x20, a)
                        mstore(0x40, and(keccak256(0x00, 0x60), N_MASK))
                    }
                    mstore(outPtr, mload(0x40))
                    outPtr := add(outPtr, 0x20)
                    wotsAdrs := add(wotsAdrs, 0x100000000)   // chain_address += 1
                }

                // ── 3 checksum chains (i = 43, 44, 45) ──
                // csum_digit[j] = (csumShifted >> (13 - 3j)) & 7: read bits 13..15, then
                // shift csumShifted left by 3 for the next digit.
                let csumShifted := shl(7, csum)
                for { let csumEnd := add(sigPtr, 48) } lt(sigPtr, csumEnd) { sigPtr := add(sigPtr, 16) } {
                    let digit := and(shr(13, csumShifted), 7)
                    csumShifted := shl(3, csumShifted)
                    mstore(0x40, and(calldataload(sigPtr), N_MASK))
                    let aEnd := or(wotsAdrs, 7)
                    for { let a := or(wotsAdrs, digit) } lt(a, aEnd) { a := add(a, 1) } {
                        mstore(0x20, a)
                        mstore(0x40, and(keccak256(0x00, 0x60), N_MASK))
                    }
                    mstore(outPtr, mload(0x40))
                    outPtr := add(outPtr, 0x20)
                    wotsAdrs := add(wotsAdrs, 0x100000000)
                }

                // ── WOTS_PK compression via T_l (46 chain outputs) ──
                // total = seed(32) + adrs(32) + 46*32 = 1536 = 0x600, hashed in place from
                // 0x40 like the FORS roots (the endpoints already sit at 0x80..).
                mstore(0x40, seed)
                mstore(0x60, or(or(shl(224, layer), shl(128, curTree)), or(shl(96, 1), shl(64, curLeaf))))
                let merkleNode := and(keccak256(0x40, 0x600), N_MASK)   // wots_pk

                // ── XMSS auth climb (h' = 4), auth path right after the 46 WOTS values ──
                // XMSS_TREE ADRS: type=2, layer, tree=curTree, kp=0; word2 = height
                // (+1 per level at shl 32), word3 = tree_index = curLeaf >> height.
                let xmssAdrs := or(or(shl(224, layer), shl(128, curTree)), shl(96, 2))
                let mIdx := curLeaf
                for { let authEnd := add(sigPtr, 64) } lt(sigPtr, authEnd) { sigPtr := add(sigPtr, 16) } {
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

                // Advance: leaf = tree & 0xF, tree = tree >> 4.
                curLeaf := and(curTree, 0xF)
                curTree := shr(4, curTree)
            }

            valid := eq(currentNode, root)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
