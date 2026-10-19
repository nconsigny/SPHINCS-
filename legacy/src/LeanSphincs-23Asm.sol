// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title LeanSphincs23Asm — Stateless leanSphincs-23 verifier over keccak256 (shared, Yul)
/// @notice leanSphincs-23: one XMSS layer h=25 (d=1), FORS k=13 a=12 (no tree roots: the two
///         top nodes of each tree), WOTS+C v=64 chains of 4 positions (w=2 bits), target sum
///         T=128, n=16, sig=4148 B. Spec: legacy/docs/leanSphincs-23-keccak.md ("spec §N" below).
///         Retired to legacy/: superseded by leanSphincs-S (src/keccak/LeanSphincs-SAsm.sol).
///         Port of the upstream leanSphincs crate (Tom Wambsgans, crates/sphincs, BLAKE2s);
///         the only change is keccak256 in place of BLAKE2s.
/// @dev    Tweakable hash (spec §2):
///           Th(P, tw, M) = keccak256(P ‖ address(tw) ‖ M)[0:16]   — the HIGH 128 bits
///         `P ‖ address` is exactly one EVM word, so the hash input is that word with the
///         payload right after it. The message digest alone keeps all 32 output bytes.
///
///         Address (spec §3). This is leanSphincs' own 16-byte tweak, NOT a SPHINCS+ /
///         FIPS 205 ADRS (the repo's FIPS-ADRS rule covers the C-series / SPX family only):
///           bytes 0..4   lo              u32 little endian
///           bytes 4..7   hi              low 3 bytes, little endian (hi < 2^24)
///           byte  7      t | step << 5   (t < 32, step < 8)
///           bytes 8..16  zero
///         The verifier stores `P ‖ address` 8 bytes early (HASH WINDOW in the body): the
///         stored prefix word is `0^8 ‖ P ‖ address bytes 0..7`, so in it (bit 0 = least
///         significant):
///           bits 32..63   lo, byte k of lo at bits 56-8k .. 63-8k
///           bits  8..31   hi, byte k of hi at bits 24-8k .. 31-8k
///           bits  0.. 7   t | step << 5
///         Upstream test vector: address(t=10, step=5, hi=0x123456, lo=0x89abcdef) =
///         ef cd ab 89 56 34 12 aa 00 … 00, i.e. the low 64 bits 0xefcdab89_563412_aa.
///
///         Tweak types used by verification (t, hi, lo):
///            1 CHAIN     (chain i, leaf e; step = target position - 1)
///            2 LEAF      (0, e)                 3 NODE    (level, node index)
///            4 ENC       (0, e)                 9 FTS_LEAF, 10 FTS_NODE (pos(κ,ℓ,j), idx)
///           11 FTS_KEY   (0, idx)              12 MSG     (0, 0)
///         with e = idx (the one-time key signs at the digest's leaf) and
///         pos(κ,ℓ,j) = κ + 32ℓ + 512j (spec §4; disjoint bit fields, pos < 2^21).
///
///         Signature layout (spec §11, 4148 B). Fields after the 4-byte counter are not
///         16-aligned; calldataload / calldatacopy do not care. A 32-byte read of a 16-byte
///         field also picks up the next 16 bytes, which never reach a hash input (see
///         MASKING in the body):
///              0                  ρ (randomizer)
///             16 + 208κ           FORS secret sk_κ          κ = 0..12
///             32 + 208κ + 16ℓ     FORS path p_κ[ℓ]          ℓ = 0..11
///           2720                  counter c, u32 LE (4 B)
///           2724 + 16i            WOTS value σ_i            i = 0..63
///           3748 + 16ℓ            XMSS auth path[ℓ]         ℓ = 0..24
///
///         Work: keccak256 calls on every input that reaches the root comparison (constant —
///         the WOTS+C target sum fixes the number of chain steps at 64·3 - T):
///           message digest                  1
///           FORS leaves                    13
///           FORS nodes  (13 trees · 11)   143
///           FORS key                        1
///           WOTS+C encoding                 1
///           WOTS chain steps (192 - 128)   64
///           WOTS leaf                       1
///           XMSS path nodes                25
///           total                         249
///         The keccak256 count is constant; the gas is not: the chain dispatch (section 4)
///         costs more for some step counts than for others, and nothing else depends on the
///         signature. Typical signatures differ by a few hundred gas; the extremes over all
///         admissible codewords are about 1,000 apart (see VERIFY_GAS_MAX in
///         legacy/test/LeanSphincs23Test.t.sol). Every input is public, so this leaks nothing.
///
///         Loop structure: the 11 FORS levels and the 25 XMSS levels are unrolled, so every
///         shift, mask, address constant and calldata offset in them is a literal; the 13
///         FORS trees are a loop; the 64 WOTS chains are a loop unrolled by 4 (one
///         codeword byte per iteration).
///
///         Memory map (bytes). Small hashes read keccak256(0x08, 0x20 + payload length):
///           0x000  0^8 ‖ P ‖ address[0..8]   prefix word; the window starts at 0x008
///           0x020  0^8                       address[8..16], zeroed once
///           0x028  payload                   m ‖ ρ (48 B) for the digest; sk_κ, a node
///                                            pair L ‖ R, M ‖ LE32(c) or a chain value
///         The wide hashes (FTS_KEY, LEAF) read keccak256(0x68, 0x20 + payload length):
///           0x060  0^8 ‖ P ‖ address[0..8]
///           0x080  0^8                       zeroed once
///           0x088  13 packed FORS top words (416 B) for FTS_KEY, then reused for the
///                  64 WOTS chain ends (1024 B, to 0x487) for LEAF
///         The highest byte written is 0x497 (end_63's stray low half).
contract LeanSphincs23Asm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        // NOTE: this block intentionally uses Solidity's free-memory-pointer slot
        // (0x40) and the zero slot (0x60) as scratch and writes high memory (up to
        // 0x497) without updating the FMP. That is only sound because every exit
        // below is an unconditional in-assembly `return`/`revert`, so Solidity never
        // regains control with a clobbered FMP. It is therefore NOT `memory-safe` in
        // the Yul sense — do not add the ("memory-safe") annotation and do not
        // introduce a normal (fall-through) exit from this block. (Same reasoning as
        // SphincsC13Asm, review C13-evm-f1.)
        assembly {
            // HASH WINDOW. A hash input `P ‖ address ‖ payload` does not start at a word
            // boundary: it starts 8 bytes into its prefix word. The word stored at 0x00 is
            //   0^8 ‖ P ‖ address bytes 0..7          (word bytes 0..7, 8..23, 24..31)
            // so the address's nonzero half (lo, hi, t|step) is the LOW 64 bits of the
            // stored word and every field constant is a short PUSH (in the high half they
            // would be wide constants, which the optimizer splits into PUSH+SHL pairs).
            // The address's zero half (bytes 8..15) is memory 0x20..0x27, which is zeroed
            // once and never written again, and the payload starts at 0x28. The wide
            // hashes (FTS_KEY, LEAF) use the same shape 0x60 higher: prefix word at 0x60,
            // zero bytes 0x80..0x87, payload from 0x88.

            // MASKING. A 16-byte value arrives in a 32-byte word whose low half is not zero:
            // a calldataload carries the next field's bytes, a keccak256 word the 16 output
            // bytes Th drops. No such value is masked on its way into a hash; instead each
            // store is placed so that its low half never reaches a hash input:
            //   ρ         stored at 0x48; the digest reads 0x08..0x57 and no hash ever
            //             reads 0x58..0x67
            //   sk_κ      stored at 0x28; the leaf hash reads 0x28..0x37
            //   FORS and XMSS nodes, their siblings, and the WOTS leaf: L/R PLACEMENT
            //   FORS tops the same placement into the packed top words (section 2)
            //   FORS key  stored at 0x28; the counter calldatacopy overwrites 0x38..0x3B and
            //             the ENC hash reads 0x08..0x3B
            //   ENC hash  only its high 16 bytes (d) are read
            //   σ_i and every chain-step output: a CHAIN hash reads 0x28..0x37 only; the
            //             32-byte store of end_i at 0x88 + 16i puts its low half on
            //             end_{i+1}'s slot, which the next (ascending) store overwrites, and
            //             end_63's spills to 0x488..0x497, past the LEAF payload [0x88, 0x488)
            // N_MASK is applied once, to the XMSS root before the comparison with pkRoot.
            // The unmasked low halves are nonzero (calldata, hash output), so breaking one of
            // these invariants (a longer hash read, reordered stores) corrupts a hash input
            // on every signature and fails the known-answer tests.
            //
            // L/R PLACEMENT. A Merkle pair `L ‖ R` is the 32 payload bytes 0x28..0x47. The
            // current node, a 32-byte keccak word, is stored at p = 0x28 + 16·bit (the L
            // slot when the side bit is 0, the R slot when it is 1), then the sibling's 16
            // calldata bytes are calldatacopy'd into the other slot, xor(p, 0x10).
            // calldatacopy writes exactly 16 bytes, so with the node written first its
            // stray low half is harmless: it lands on the R slot, which the sibling then
            // overwrites, or on 0x48..0x57, past the 0x40-byte hash input. This is
            // Solady's MerkleProofLib swap (node at s, sibling at xor(s, 0x20)) adapted to
            // 16-byte children: no mask, no swap arithmetic, no branch.
            //
            // SIDE TABLES. The slots of a whole climb are precomputed from its index (u_κ
            // for a FORS tree, idx for the XMSS fold) into one word S: byte ℓ of S, counting
            // from the low end, is 0x28 + 16·(bit ℓ of the index), so level ℓ's p is
            // byte(31 - ℓ, S). A chunk of c ≤ 7 index bits is spread to one bit per byte by
            // a multiply: chunk·Σ_{ℓ<c} 2^(7ℓ) puts bit ℓ at bit 7ℓ + ℓ = 8ℓ, and the c
            // shifted copies (7 bits apart, at most 7 bits wide) never overlap, so the
            // product has no carries; the mask Σ_{ℓ<c} 2^(8ℓ) keeps exactly those bits.
            // Then shl(4, ·) | 0x2828…28 turns each byte into 0x28 or 0x38.
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            // ---------------------------------------------------------------
            // Input checks (spec §12)
            // ---------------------------------------------------------------

            // PARAM IDENTITY: 4148 = 16 + k(1+a)·16 + 4 + v·16 + h·16
            //                      = 16 + 13·13·16 + 4 + 64·16 + 25·16.
            if iszero(eq(sig.length, 4148)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            // The key words are high-aligned: pkSeed = P ‖ 0^16, pkRoot = root ‖ 0^16.
            // A nonzero low half would make pkRoot unreachable (the root is N_MASK'd)
            // and would corrupt the address bytes of every prefix word built from
            // pkSeed. Fail loudly instead of returning false forever.
            if or(shl(128, pkSeed), shl(128, pkRoot)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid public key")
                revert(0x00, 0x64)
            }

            let sigBase := sig.offset
            // P at word bytes 8..23 (see HASH WINDOW): OR an address's low 8 bytes into
            // the low 64 bits to get a prefix word.
            let P := shr(64, pkSeed)
            // The address's zero half, for both windows (see HASH WINDOW).
            mstore(0x20, 0) // 0x20..0x3F; 0x28.. is payload, written before every read
            mstore(0x80, 0) // 0x80..0x9F; 0x88.. is payload, written before every read

            // ---------------------------------------------------------------
            // 1. Message digest (spec §5) — 1 keccak
            //    D = ThFull(P, address(MSG=12, step 0, hi=0, lo=0), m ‖ ρ),
            //    32 + 32 + 16 = 80 input bytes, untruncated.
            // ---------------------------------------------------------------
            mstore(0x00, or(P, 12))
            mstore(0x28, message)
            mstore(0x48, calldataload(sigBase)) // ρ = sig[0:16]; unmasked, see MASKING
            let D := keccak256(0x08, 0x50)
            // Leaf index: idx = word_3 & (2^25 - 1), word_3 = u64 LE of D[24:32], so idx
            // = D[24] | D[25] << 8 | D[26] << 16 | (D[27] & 1) << 24. Every FORS, ENC,
            // CHAIN and LEAF address has lo = idx: lo bytes 0..3 = D[24], D[25], D[26],
            // D[27] & 1. In the raw hash word those bytes already sit at bits 56..63,
            // 48..55, 40..47 and 32..39, exactly where the lo field goes (see HASH
            // WINDOW), so the field is a mask of D, with no byte swap. PARAM IDENTITY: the
            // mask keeps h = 25 bits, 3 bytes + 1 bit.
            let idxLo := and(D, 0xFFFFFF0100000000)
            // word_w = u64 LE of D[8w : 8w+8]. Byte-reversing D (swap adjacent bytes,
            // then 2-, 4-, 8- and 16-byte groups) turns it into the little-endian 256-bit
            // number word_0 + 2^64·word_1 + 2^128·word_2 + 2^192·word_3, so
            // word_w = (dRev >> 64w) mod 2^64.
            let dRev := D
            {
                let m := 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF
                dRev := or(and(shr(8, dRev), m), shl(8, and(dRev, m)))
                m := 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF
                dRev := or(and(shr(16, dRev), m), shl(16, and(dRev, m)))
                m := 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF
                dRev := or(and(shr(32, dRev), m), shl(32, and(dRev, m)))
                m := 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF
                dRev := or(and(shr(64, dRev), m), shl(64, and(dRev, m)))
                dRev := or(shr(128, dRev), shl(128, dRev))
            }
            // The XMSS fold's SIDE TABLE (section 5), built here while dRev is at hand:
            // byte ℓ of SX (from the low end) is 0x28 + 16·(bit ℓ of idx), idx = word_3 &
            // (2^25 - 1) spread in 7-bit chunks (bits 0..6, 7..13, 14..20, 21..24).
            // PARAM IDENTITIES: 0x1FFFFFF = 2^h - 1; 25 table bytes = h; 0x40810204081 =
            // Σ_{ℓ<7} 2^(7ℓ), 0x1010101010101 = Σ_{ℓ<7} 2^(8ℓ).
            let SX
            {
                let idx := and(shr(192, dRev), 0x1FFFFFF)
                SX := or(0x28282828282828282828282828282828282828282828282828, shl(4, or(
                    or(
                        and(mul(and(idx, 0x7F), 0x40810204081), 0x1010101010101),
                        shl(56, and(mul(and(shr(7, idx), 0x7F), 0x40810204081), 0x1010101010101))
                    ),
                    or(
                        shl(112, and(mul(and(shr(14, idx), 0x7F), 0x40810204081), 0x1010101010101)),
                        shl(168, and(mul(shr(21, idx), 0x40810204081), 0x1010101010101))
                    )
                )))
            }

            // ---------------------------------------------------------------
            // 2. FORS recovery (spec §7) — 13 · (1 leaf + 11 nodes) = 156 keccak
            //    Per tree κ: opened leaf u_κ, secret sk_κ, path p_κ[0..11].
            //      node = Th(P, FTS_LEAF(pos(κ,0,u), idx), sk)
            //      ℓ = 0..10: node = Th(P, FTS_NODE(pos(κ,ℓ+1,u>>(ℓ+1)), idx), L ‖ R),
            //                 (L, R) = bit ℓ of u ? (p[ℓ], node) : (node, p[ℓ])
            //      tops (top_{κ,0}, top_{κ,1}) ordered by bit 11 of u with p[11].
            //    A FORS tree has no root hash: its two level-11 nodes go into the key.
            //
            //    FORS HI FIELD. hi = pos(κ,ℓ,j) = κ | ℓ<<5 | j<<9 (disjoint bit fields), so
            //    its 3 little-endian bytes are byte 0 = κ | (ℓ&7)<<5, byte 1 = ℓ>>3 |
            //    (j&0x7F)<<1, byte 2 = j>>7. In the prefix word: κ at bits 24..28, the
            //    level at bits 29..31 and 16, j&0x7F at bits 17..23, j>>7 at bits 8..12.
            //    κ is a per-tree value and the level a literal in each unrolled level. For
            //    j = u>>up, W = u·(2^17 + 2^1) holds two disjoint copies of u (bits 17..28
            //    and 1..12): after shr(up, W) the first copy has j at bit 17 and the
            //    second has j>>7 at bit 8, so and(shr(up, W), J_LO) is the j part. For
            //    up ≥ 5, j>>7 = 0 while the first copy's low bits of u (the ones j drops)
            //    reach down to bit 17 - up ≤ 12, so the mask keeps bits 17..23 only (J_HI).
            // ---------------------------------------------------------------
            let J_LO := 0xFE1F00 // bits 17..23 and 8..12 (up ≤ 4)
            let J_HI := 0xFE0000 // bits 17..23           (up ≥ 5)
            // P and lo = idx are shared by every FORS address; the type (t = 9 FTS_LEAF,
            // t = 10 FTS_NODE) goes into each hash's literal part.
            let forsAdrs := or(P, idxLo)
            // u_κ = (word_{⌊κ/5⌋} >> 12·(κ mod 5)) & 0xFFF: five 12-bit indices per 64-bit
            // word (bits 0..59), κ = 10..12 in word 2. Dropping each word's 4 unused top
            // bits packs the 13 indices back to back, U = Σ u_κ·2^(12κ), so tree κ takes
            // the low 12 bits and shifts U down. PARAM IDENTITIES: 0xFFFFFFFFFFFFFFF =
            // 2^60 - 1 = five a-bit indices, 0xFFFFFFFFF = 2^36 - 1 = three, 0xFFF = 2^a - 1.
            let U := or(
                or(and(dRev, 0xFFFFFFFFFFFFFFF), shl(60, and(shr(64, dRev), 0xFFFFFFFFFFFFFFF))),
                shl(120, and(shr(128, dRev), 0xFFFFFFFFF))
            )
            for { let kappa := 0 } lt(kappa, 13) { kappa := add(kappa, 1) } {
                let u := and(U, 0xFFF)
                U := shr(12, U)
                // treePtr = sig + 208κ, so sk_κ is at treePtr + 16 (sig offset 16 + 208κ)
                // and p_κ[ℓ] at treePtr + 32 + 16ℓ (sig offset 32 + 208κ + 16ℓ).
                // PARAM IDENTITY: 208 = (1 + a)·n = 13·16, one tree's opening.
                let treePtr := add(sigBase, mul(208, kappa))
                // κ (< 32, byte 0 of hi) at bits 24..28.
                let treeAdrs := or(forsAdrs, shl(24, kappa))
                let W := mul(u, 0x20002) // 2^17 + 2^1, see FORS HI FIELD
                // SIDE TABLE: byte ℓ of S (from the low end) is 0x28 + 16·(bit ℓ of u),
                // spread in two 6-bit chunks. PARAM IDENTITIES: 12 table bytes = a;
                // 0x810204081 = Σ_{ℓ<6} 2^(7ℓ), 0x10101010101 = Σ_{ℓ<6} 2^(8ℓ).
                let S := or(0x282828282828282828282828, shl(4, or(
                    and(mul(and(u, 0x3F), 0x810204081), 0x10101010101),
                    shl(48, and(mul(shr(6, u), 0x810204081), 0x10101010101))
                )))

                // Leaf: hi = pos(κ, 0, u) = κ + 512u.
                mstore(0x00, or(treeAdrs, or(9, and(W, J_LO))))
                mstore(0x28, calldataload(add(treePtr, 16))) // sk_κ; unmasked, see MASKING
                let node := keccak256(0x08, 0x30) // unmasked, see L/R PLACEMENT

                // Levels 1..11 (a - 1 = 11 node hashes), unrolled: L/R PLACEMENT with p
                // from S, p_κ[ℓ] at treePtr + 32 + 16ℓ; t = 10 and the level in the literal.
                let p
                // ℓ = 0: side = bit 0 of u, hi = pos(κ, 1, u >> 1), sibling p_κ[0]
                p := byte(31, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 1)), and(shr(1, W), J_LO))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 32), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 1: side = bit 1 of u, hi = pos(κ, 2, u >> 2), sibling p_κ[1]
                p := byte(30, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 2)), and(shr(2, W), J_LO))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 48), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 2: side = bit 2 of u, hi = pos(κ, 3, u >> 3), sibling p_κ[2]
                p := byte(29, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 3)), and(shr(3, W), J_LO))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 64), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 3: side = bit 3 of u, hi = pos(κ, 4, u >> 4), sibling p_κ[3]
                p := byte(28, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 4)), and(shr(4, W), J_LO))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 80), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 4: side = bit 4 of u, hi = pos(κ, 5, u >> 5), sibling p_κ[4]
                p := byte(27, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 5)), and(shr(5, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 96), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 5: side = bit 5 of u, hi = pos(κ, 6, u >> 6), sibling p_κ[5]
                p := byte(26, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 6)), and(shr(6, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 112), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 6: side = bit 6 of u, hi = pos(κ, 7, u >> 7), sibling p_κ[6]
                p := byte(25, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(29, 7)), and(shr(7, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 128), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 7: side = bit 7 of u, hi = pos(κ, 8, u >> 8), sibling p_κ[7]
                p := byte(24, S)
                mstore(0x00, or(treeAdrs, or(or(10, shl(16, 1)), and(shr(8, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 144), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 8: side = bit 8 of u, hi = pos(κ, 9, u >> 9), sibling p_κ[8]
                p := byte(23, S)
                mstore(0x00, or(treeAdrs, or(or(10, or(shl(29, 1), shl(16, 1))), and(shr(9, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 160), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 9: side = bit 9 of u, hi = pos(κ, 10, u >> 10), sibling p_κ[9]
                p := byte(22, S)
                mstore(0x00, or(treeAdrs, or(or(10, or(shl(29, 2), shl(16, 1))), and(shr(10, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 176), 0x10)
                node := keccak256(0x08, 0x40)
                // ℓ = 10: side = bit 10 of u, hi = pos(κ, 11, u >> 11), sibling p_κ[10]
                p := byte(21, S)
                mstore(0x00, or(treeAdrs, or(or(10, or(shl(29, 3), shl(16, 1))), and(shr(11, W), J_HI))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 192), 0x10)
                node := keccak256(0x08, 0x40)

                // Tops: the level-11 node and its sibling p_κ[11] (sig offset
                // 32 + 208κ + 16·11 = 208 + 208κ), ordered by bit 11 of u, form the packed
                // word top_{κ,0} ‖ top_{κ,1} at 0x88 + 32κ, by the same placement: p =
                // 0x88 + 32κ + 16·bit = 0x60 + 32κ + byte 11 of S, and 0x88 + 32κ has bit 4
                // clear, so xor(p, 0x10) is the other half of that word. A stray node low
                // half lands on tree κ+1's top_0 slot, which that tree writes next, or for
                // κ = 12 on 0x228..0x237, past the FTS_KEY input.
                p := add(add(0x60, shl(5, kappa)), byte(20, S))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 208), 0x10)
            }

            // FORS key = Th(P, FTS_KEY(hi=0, lo=idx), top_{0,0} ‖ top_{0,1} ‖ … ‖ top_{12,1})
            // — 1 keccak. Prefix word at 0x60, the 13 packed top words from 0x88:
            // 32 + 13·32 = 448 = 0x1C0 bytes from 0x68. The key goes straight to the ENC
            // payload slot, unmasked (see MASKING).
            mstore(0x60, or(P, or(idxLo, 11)))
            mstore(0x28, keccak256(0x68, 0x1C0))

            // ---------------------------------------------------------------
            // 3. WOTS+C encoding (spec §6) — 1 keccak
            //    d = Th(P, ENC(hi=0, lo=e=idx), M ‖ LE32(c)), M = FORS key: 32 + 20 bytes.
            //    The counter's 4 signature bytes are LE32(c) already and go back into the
            //    payload in the same order, so c is never decoded: calldatacopy moves the
            //    4 bytes at sig offset 2720 to payload bytes 16..19 (0x38..0x3B), over the
            //    FORS key word's dropped half.
            // ---------------------------------------------------------------
            calldatacopy(0x38, add(sigBase, 2720), 4)
            mstore(0x00, or(P, or(idxLo, 4)))
            // X = d as u128 little endian, x_i = (X >> 2i) & 3, i = 0..63: for i = 4k + r,
            // bits 2r..2r+1 of byte k of d. d is the high 16 bytes of the raw hash word h,
            // so byte k of d is byte(k, h) and X is never formed; the low 16 bytes of h
            // (the dropped half of the hash) are never read: unmasked, see MASKING.
            let h := keccak256(0x08, 0x34)

            // Admissible iff Σ x_i = T. A well-formed signature that fails is rejected by
            // returning `false` (the bool contract), not by reverting — uniform with the
            // root mismatch below.
            // The sum is a SWAR reduction over the 64 two-bit fields of d = h >> 128 (byte
            // order does not change which 2-bit fields there are, so d is not byte-reversed):
            //   pairs of x_i into 32 nibbles, each ≤ 6;
            //   pairs of nibbles into 16 bytes, each ≤ 12;
            //   multiplying by 0x0101…01 (16 ones) puts the sum of all 16 bytes in byte 15
            //   (bits 120..127). Every partial byte sum is ≤ 16·12 = 192 < 256, so no byte
            //   carries into the next and byte 15 is exact.
            // PARAM IDENTITIES: 128-bit masks = v·w = 64·2 bits of d; 3 = 2^w - 1; the
            // compared 128 is T (equal to v·w by coincidence — not the same quantity).
            {
                let d := shr(128, h)
                let t := add(
                    and(d, 0x33333333333333333333333333333333),
                    and(shr(2, d), 0x33333333333333333333333333333333)
                )
                t := and(add(t, shr(4, t)), 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F)
                let sum := and(shr(120, mul(t, 0x01010101010101010101010101010101)), 0xFF)
                if iszero(eq(sum, 128)) {
                    mstore(0x00, 0)
                    return(0x00, 0x20)
                }
            }

            // ---------------------------------------------------------------
            // 4. WOTS chains (spec §6) — Σ (3 - x_i) = 192 - T = 64 keccak
            //    end_i = chain σ_i from position x_i to 3; the step onto position `to`
            //    is Th(P, CHAIN(step = to-1, hi = i, lo = e), x).
            //    Chain i still needs n_i = 3 - x_i steps. n_i is the 2-bit complement of
            //    x_i, so the n of chains 4k..4k+3 are the 2-bit fields of
            //    nb = byte(k, h) xor 0xFF (bits 2r..2r+1 for chain 4k + r; nb is one byte,
            //    so shr(6, nb) needs no mask). Each chain switches on n into straight-line
            //    code, cases in falling frequency: under Σ x_i = T the x_i lean high
            //    (P[x = 3, 2, 1, 0] ≈ 0.42, 0.28, 0.18, 0.12). Within a chain only address
            //    byte 7 (t | step << 5, memory 0x1F) changes from step to step, so the
            //    later steps rewrite that byte with mstore8.
            //    Unrolled by 4: one codeword byte per iteration, chains in ascending
            //    order. end_i goes to 0x88 + 16i; each 32-byte store's low half (the rest
            //    of the hash word, or σ_{i+1} when x_i = 3) lands on end_{i+1}'s slot,
            //    which the next store overwrites; the last one spills 16 bytes to
            //    0x488..0x497, past the LEAF payload.
            // ---------------------------------------------------------------
            let chainAdrs := or(P, or(idxLo, 1)) // t = CHAIN, step field 0
            let wots := add(sigBase, 2724) // σ_i at sig offset 2724 + 16i
            for { let off := 0 } lt(off, 1024) { off := add(off, 64) } { // off = 64k = 16·4k
                let nb := xor(byte(shr(6, off), h), 0xFF)
                let ptr := add(wots, off) // σ_{4k}
                let slot := add(0x88, off) // end_{4k}
                // hi = i = 4k + r < 64 is one byte, at bits 24..31: shl(24, 4k) = shl(20, off).
                let a := or(chainAdrs, shl(20, off))
                { // chain 4k + 0
                    let val := calldataload(ptr) // σ_i; unmasked, see MASKING
                    switch and(nb, 3)
                    case 0 {} // x = 3: end = σ
                    case 1 {
                        mstore(0x00, or(a, 0x40)) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    case 2 {
                        mstore(0x00, or(a, 0x20)) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    default {
                        mstore(0x00, a) // onto 1
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x21) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    mstore(slot, val)
                }
                { // chain 4k + 1
                    let val := calldataload(add(ptr, 16)) // σ_i; unmasked, see MASKING
                    switch and(shr(2, nb), 3)
                    case 0 {} // x = 3: end = σ
                    case 1 {
                        mstore(0x00, or(or(a, shl(24, 1)), 0x40)) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    case 2 {
                        mstore(0x00, or(or(a, shl(24, 1)), 0x20)) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    default {
                        mstore(0x00, or(a, shl(24, 1))) // onto 1
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x21) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    mstore(add(slot, 16), val)
                }
                { // chain 4k + 2
                    let val := calldataload(add(ptr, 32)) // σ_i; unmasked, see MASKING
                    switch and(shr(4, nb), 3)
                    case 0 {} // x = 3: end = σ
                    case 1 {
                        mstore(0x00, or(or(a, shl(24, 2)), 0x40)) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    case 2 {
                        mstore(0x00, or(or(a, shl(24, 2)), 0x20)) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    default {
                        mstore(0x00, or(a, shl(24, 2))) // onto 1
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x21) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    mstore(add(slot, 32), val)
                }
                { // chain 4k + 3
                    let val := calldataload(add(ptr, 48)) // σ_i; unmasked, see MASKING
                    switch shr(6, nb)
                    case 0 {} // x = 3: end = σ
                    case 1 {
                        mstore(0x00, or(or(a, shl(24, 3)), 0x40)) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    case 2 {
                        mstore(0x00, or(or(a, shl(24, 3)), 0x20)) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    default {
                        mstore(0x00, or(a, shl(24, 3))) // onto 1
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x21) // onto 2
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                        mstore8(0x1F, 0x41) // onto 3
                        mstore(0x28, val)
                        val := keccak256(0x08, 0x30)
                    }
                    mstore(add(slot, 48), val)
                }
            }

            // WOTS leaf = Th(P, LEAF(hi=0, lo=e), end_0 ‖ … ‖ end_63) — 1 keccak.
            // Prefix word at 0x60, 1024-byte payload at 0x88: 32 + 1024 = 0x420 bytes
            // from 0x68.
            mstore(0x60, or(P, or(idxLo, 2)))
            let cur := keccak256(0x68, 0x420) // unmasked, see L/R PLACEMENT

            // ---------------------------------------------------------------
            // 5. XMSS fold (spec §8) — 25 keccak
            //    ℓ = 0..24: cur = Th(P, NODE(hi = ℓ+1, lo = idx >> (ℓ+1)), L ‖ R),
            //               (L, R) = bit ℓ of idx ? (path[ℓ], cur) : (cur, path[ℓ]).
            //    Unrolled, with L/R PLACEMENT and path[ℓ] at sig offset 3748 + 16ℓ (the
            //    last one, 4132..4147, ends exactly at the end of the signature).
            //    side   p = byte(31 - ℓ, SX), the SIDE TABLE built in section 1
            //    lo     LE32(idx >> up), up = ℓ+1, from idxLo = LE32(idx) in the lo field
            //           (bits 32..63, byte k at bits 56-8k..63-8k) with literal shifts and
            //           masks. For up = 8q + r: dropping q whole bytes is a left shift by
            //           8q (byte k+q moves up to byte k), and shifting by the remaining r
            //           bits gives byte k = (b_k >> r) | (b_{k+1} << 8-r):
            //             and(idxLo << (8q - r), (0xFF >> r) in every byte)
            //           | and(idxLo << (8q + 16 - r), (0xFF << 8-r) in every byte)
            //           (a negative shift is a right shift). The 8-byte repeating masks
            //           also clear everything outside bits 32..63: no shifted copy has a
            //           bit below 32 that the mask keeps. r = 0 needs one term; up = 25
            //           has lo = 0.
            //    t = NODE (3) and hi = ℓ+1 (one byte, at bits 24..31) are in the literal.
            //    Here the pair goes in before the prefix word, in the FORS levels after it:
            //    the two touch disjoint bytes (0x28..0x57 and 0x00..0x1F), so the order
            //    only changes the via-IR stack schedule, and each section keeps its cheaper
            //    one (measured: the other order costs +3 gas here and +323 in FORS).
            // ---------------------------------------------------------------
            let p
            let lo
            // ℓ = 0: hi = 1, lo = LE32(idx >> 1), side = bit 0 of idx, sibling path[0]
            p := byte(31, SX)
            lo := or(and(shr(1, idxLo), 0x7F7F7F7F7F7F7F7F), and(shl(15, idxLo), 0x8080808080808080))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3748), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 1)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 1: hi = 2, lo = LE32(idx >> 2), side = bit 1 of idx, sibling path[1]
            p := byte(30, SX)
            lo := or(and(shr(2, idxLo), 0x3F3F3F3F3F3F3F3F), and(shl(14, idxLo), 0xC0C0C0C0C0C0C0C0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3764), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 2)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 2: hi = 3, lo = LE32(idx >> 3), side = bit 2 of idx, sibling path[2]
            p := byte(29, SX)
            lo := or(and(shr(3, idxLo), 0x1F1F1F1F1F1F1F1F), and(shl(13, idxLo), 0xE0E0E0E0E0E0E0E0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3780), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 3)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 3: hi = 4, lo = LE32(idx >> 4), side = bit 3 of idx, sibling path[3]
            p := byte(28, SX)
            lo := or(and(shr(4, idxLo), 0x0F0F0F0F0F0F0F0F), and(shl(12, idxLo), 0xF0F0F0F0F0F0F0F0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3796), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 4)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 4: hi = 5, lo = LE32(idx >> 5), side = bit 4 of idx, sibling path[4]
            p := byte(27, SX)
            lo := or(and(shr(5, idxLo), 0x0707070707070707), and(shl(11, idxLo), 0xF8F8F8F8F8F8F8F8))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3812), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 5)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 5: hi = 6, lo = LE32(idx >> 6), side = bit 5 of idx, sibling path[5]
            p := byte(26, SX)
            lo := or(and(shr(6, idxLo), 0x0303030303030303), and(shl(10, idxLo), 0xFCFCFCFCFCFCFCFC))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3828), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 6)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 6: hi = 7, lo = LE32(idx >> 7), side = bit 6 of idx, sibling path[6]
            p := byte(25, SX)
            lo := or(and(shr(7, idxLo), 0x0101010101010101), and(shl(9, idxLo), 0xFEFEFEFEFEFEFEFE))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3844), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 7)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 7: hi = 8, lo = LE32(idx >> 8), side = bit 7 of idx, sibling path[7]
            p := byte(24, SX)
            lo := and(shl(8, idxLo), 0xFFFFFFFFFFFFFFFF)
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3860), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 8)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 8: hi = 9, lo = LE32(idx >> 9), side = bit 8 of idx, sibling path[8]
            p := byte(23, SX)
            lo := or(and(shl(7, idxLo), 0x7F7F7F7F7F7F7F7F), and(shl(23, idxLo), 0x8080808080808080))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3876), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 9)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 9: hi = 10, lo = LE32(idx >> 10), side = bit 9 of idx, sibling path[9]
            p := byte(22, SX)
            lo := or(and(shl(6, idxLo), 0x3F3F3F3F3F3F3F3F), and(shl(22, idxLo), 0xC0C0C0C0C0C0C0C0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3892), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 10)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 10: hi = 11, lo = LE32(idx >> 11), side = bit 10 of idx, sibling path[10]
            p := byte(21, SX)
            lo := or(and(shl(5, idxLo), 0x1F1F1F1F1F1F1F1F), and(shl(21, idxLo), 0xE0E0E0E0E0E0E0E0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3908), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 11)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 11: hi = 12, lo = LE32(idx >> 12), side = bit 11 of idx, sibling path[11]
            p := byte(20, SX)
            lo := or(and(shl(4, idxLo), 0x0F0F0F0F0F0F0F0F), and(shl(20, idxLo), 0xF0F0F0F0F0F0F0F0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3924), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 12)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 12: hi = 13, lo = LE32(idx >> 13), side = bit 12 of idx, sibling path[12]
            p := byte(19, SX)
            lo := or(and(shl(3, idxLo), 0x0707070707070707), and(shl(19, idxLo), 0xF8F8F8F8F8F8F8F8))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3940), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 13)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 13: hi = 14, lo = LE32(idx >> 14), side = bit 13 of idx, sibling path[13]
            p := byte(18, SX)
            lo := or(and(shl(2, idxLo), 0x0303030303030303), and(shl(18, idxLo), 0xFCFCFCFCFCFCFCFC))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3956), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 14)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 14: hi = 15, lo = LE32(idx >> 15), side = bit 14 of idx, sibling path[14]
            p := byte(17, SX)
            lo := or(and(shl(1, idxLo), 0x0101010101010101), and(shl(17, idxLo), 0xFEFEFEFEFEFEFEFE))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3972), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 15)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 15: hi = 16, lo = LE32(idx >> 16), side = bit 15 of idx, sibling path[15]
            p := byte(16, SX)
            lo := and(shl(16, idxLo), 0xFFFFFFFFFFFFFFFF)
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 3988), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 16)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 16: hi = 17, lo = LE32(idx >> 17), side = bit 16 of idx, sibling path[16]
            p := byte(15, SX)
            lo := or(and(shl(15, idxLo), 0x7F7F7F7F7F7F7F7F), and(shl(31, idxLo), 0x8080808080808080))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4004), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 17)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 17: hi = 18, lo = LE32(idx >> 18), side = bit 17 of idx, sibling path[17]
            p := byte(14, SX)
            lo := or(and(shl(14, idxLo), 0x3F3F3F3F3F3F3F3F), and(shl(30, idxLo), 0xC0C0C0C0C0C0C0C0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4020), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 18)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 18: hi = 19, lo = LE32(idx >> 19), side = bit 18 of idx, sibling path[18]
            p := byte(13, SX)
            lo := or(and(shl(13, idxLo), 0x1F1F1F1F1F1F1F1F), and(shl(29, idxLo), 0xE0E0E0E0E0E0E0E0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4036), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 19)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 19: hi = 20, lo = LE32(idx >> 20), side = bit 19 of idx, sibling path[19]
            p := byte(12, SX)
            lo := or(and(shl(12, idxLo), 0x0F0F0F0F0F0F0F0F), and(shl(28, idxLo), 0xF0F0F0F0F0F0F0F0))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4052), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 20)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 20: hi = 21, lo = LE32(idx >> 21), side = bit 20 of idx, sibling path[20]
            p := byte(11, SX)
            lo := or(and(shl(11, idxLo), 0x0707070707070707), and(shl(27, idxLo), 0xF8F8F8F8F8F8F8F8))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4068), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 21)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 21: hi = 22, lo = LE32(idx >> 22), side = bit 21 of idx, sibling path[21]
            p := byte(10, SX)
            lo := or(and(shl(10, idxLo), 0x0303030303030303), and(shl(26, idxLo), 0xFCFCFCFCFCFCFCFC))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4084), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 22)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 22: hi = 23, lo = LE32(idx >> 23), side = bit 22 of idx, sibling path[22]
            p := byte(9, SX)
            lo := or(and(shl(9, idxLo), 0x0101010101010101), and(shl(25, idxLo), 0xFEFEFEFEFEFEFEFE))
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4100), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 23)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 23: hi = 24, lo = LE32(idx >> 24), side = bit 23 of idx, sibling path[23]
            p := byte(8, SX)
            lo := and(shl(24, idxLo), 0xFFFFFFFFFFFFFFFF)
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4116), 0x10)
            mstore(0x00, or(P, or(lo, or(3, shl(24, 24)))))
            cur := keccak256(0x08, 0x40)
            // ℓ = 24: hi = 25, lo = LE32(idx >> 25), side = bit 24 of idx, sibling path[24]
            p := byte(7, SX)
            mstore(p, cur)
            calldatacopy(xor(p, 0x10), add(sigBase, 4132), 0x10)
            mstore(0x00, or(P, or(3, shl(24, 25)))) // lo = idx >> 25 = 0
            cur := keccak256(0x08, 0x40)

            valid := eq(and(cur, N_MASK), pkRoot)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
