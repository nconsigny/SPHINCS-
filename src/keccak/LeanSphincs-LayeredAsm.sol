// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title LeanSphincsLayeredAsm — Stateless leanSPHINCS verifier, layered key for 2^30 signatures,
///        over keccak256 (shared, Yul)
/// @notice leanSPHINCS at the parameters of EthLib's specification: a hypertree of three layers of
///         heights 10 (top), 8 and 8 (bottom), h = 26; FORS k = 24 trees of height a = 10 with no
///         root hash (its key is the 48 level-9 nodes); WOTS+C with v = 64 chains of 4 positions
///         (2-bit digits), target sum T = 128, no checksum chains; n = 16; Keccak-256 everywhere.
///         Public key 32 bytes (root ‖ P), signature 7,740 bytes, verification 492 Keccak-f[1600]
///         permutations. This is the "layered 10+8+8, FORS 24x10" set of sphincs.art at lifetime
///         2^30 (the model proves 127-bit security up to 1,182,000,000 signatures).
///
///         Normative spec: EthLib's Lean module EthLib/Cryptography/Sphincs/ (ethereum/EthLib
///         PR #152, head aa99d5f), which follows leanSPHINCS.tex and its Lean model
///         formal/sphincs/FORS/Scheme.lean at TomWambsgans/sphincs.art commit 1538d0a. Lean names
///         below (Verify.lean `verify`, Fors.lean `treeRecover`, ...) are that module's. Summary:
///         docs/leanSphincs-layered-keccak.md. Python mirror: script/leansphincs_layered_signer.py,
///         which reproduces every EthLib vector and the Lean known answer byte for byte.
///         Structure derived from LeanSphincsAsm.sol (the one-tree h = 26 set): the hash window,
///         MASKING, L/R PLACEMENT and the chain dispatch are that verifier's; the address layout
///         (a layer byte and a tree word), the type codes, the FORS position, the digest's bit
///         layout and the three WOTS+C layers are this spec's.
///
/// @dev    Interface: verify(pkSeed, pkRoot, message, sig) with the key words high-aligned,
///         pkSeed = P ‖ 0^16 and pkRoot = root ‖ 0^16, i.e. EthLib's 32-byte public key root ‖ P
///         split in two (encodePublicKey). `message` is EthLib's 32-byte message m.
///
///         Tweakable hash (TweakableHash.lean):
///           Th(P, A, M) = keccak256(P ‖ A ‖ M)[0:16]     — the HIGH 128 bits of the word
///         The message digest alone keeps all 32 output bytes (thFull).
///
///         Address (Address.lean encodeAddress), 16 bytes, every field little endian:
///           bytes 0..4    lo
///           bytes 4..7    hi (< 2^24)
///           byte  7       type | step << 5   (type < 32, step < 8)
///           byte  8       layer, counted from the bottom (0 bottom, 1 middle, 2 top)
///           bytes 9..13   tree, u32
///           bytes 13..16  zero
///         Call types used by verification (type, hi, lo; layer and tree are zero outside the
///         hypertree):
///            1 CHAIN      step = mu, hi = chain i, lo = key leaf     (step from position mu)
///            2 LEAF       hi = 0, lo = key leaf
///            3 NODE       hi = level (1..height), lo = node index on that level
///            4 ENCODING   hi = 0, lo = key leaf
///           12 MSG        hi = call c (0, 1), lo = 0
///           15 FORS_LEAF  hi = κ + 64·l,              lo = idx
///           17 FORS_NODE  hi = κ + 64·(λ + 16·j),     lo = idx         (level λ, node index j)
///         (0 PRF, 5 PARAM, 7 RND and 14 FORS_PRF are the signer's.) A layer's one-time key is
///         OtsKey.ofIndex: bottom (layer 0, tree idx >> 8, leaf idx mod 2^8), middle (layer 1,
///         tree idx >> 16, leaf (idx >> 8) mod 2^8), top (layer 2, tree 0, leaf idx >> 16).
///
///         Signature layout (Serialization.lean encodeSignature, 7,740 B):
///              0                  ρ, the randomizer
///             16 + 176κ           FORS secret of tree κ                  κ = 0..23
///             32 + 176κ + 16ℓ     FORS path node ℓ of tree κ             ℓ = 0..9
///           4240 / 5396 / 6552    bottom / middle / top layer, each:
///             +0                  counter c, u32 LE (4 B)
///             +4 + 16i            chain value σ_i                        i = 0..63
///             +1028 + 16ℓ         tree path node ℓ                       ℓ < 8 / 8 / 10
///         Fields after the first counter are not 16-aligned; calldataload / calldatacopy do not
///         care. A 32-byte read of a 16-byte field also picks up the next 16 bytes, which never
///         reach a hash input (MASKING below); every read stays inside the signature except the
///         siblings, which are calldatacopy'd, exactly 16 bytes.
///
///         Work (Verify.lean "Cost"): keccak256 calls on every input that reaches the root
///         comparison, and the Keccak-f permutations they cost (⌊L/136⌋ + 1 for L input bytes):
///                                              calls   input bytes   permutations
///           message digest (2 calls)             2         80              2
///           FORS leaves                         24         48             24
///           FORS nodes (24 trees · 9 levels)   216         64            216
///           bottom encoding (FORS key)           1        804              6
///           middle, top encodings (a root)       2         52              2
///           chain steps (3 layers · (192-128)) 192         48            192
///           one-time leaves (64 chain ends)      3       1056             24
///           tree nodes (8 + 8 + 10)             26         64             26
///           total                              466                       492
///         The count is constant: the target sum fixes 64 chain steps per layer. An inadmissible
///         counter returns false at once (after 243 calls for the bottom layer). The gas is not
///         quite constant: the chain dispatch costs more for some step counts than for others.
///         Every input is public, so this leaks nothing.
///
///         Memory map (bytes). Small hashes read keccak256(0x08, 0x20 + payload length):
///           0x000  0^8 ‖ P ‖ address[0..8]   prefix word; the window starts at 0x008
///           0x020  address[8..16]            layer ‖ tree ‖ 0^3: zero for MSG and FORS, the
///                                            layer's for its encoding, chains and tree nodes
///           0x028  payload                   m ‖ ρ (48 B) for the digest; a FORS secret, a node
///                                            pair L ‖ R, a chain value, or root ‖ LE32(c) for the
///                                            middle and top encodings (52-byte input)
///         The wide hashes (bottom ENCODING, the three LEAFs) read keccak256(0x68, 0x20 + length):
///           0x060  0^8 ‖ P ‖ address[0..8]
///           0x080  address[8..16]            the bottom layer's before the FORS loop (the
///                                            loop never writes below 0x88), then each layer's
///                                            right after its encoding hash
///           0x088  the FORS key, 48 nodes (768 B, to 0x387), then the bottom counter (4 B,
///                  0x388..0x38B), for the bottom ENCODING; reused for the 64 chain ends
///                  (1024 B, to 0x487) of each layer for its LEAF
///         The highest byte written is 0x497 (end_63's stray low half).
contract LeanSphincsLayeredAsm {

    function verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes calldata sig)
        external pure returns (bool valid)
    {
        // NOTE: this block intentionally uses Solidity's free-memory-pointer slot (0x40) and the
        // zero slot (0x60) as scratch and writes high memory (up to 0x497) without updating the
        // FMP. That is only sound because every exit below is an unconditional in-assembly
        // `return`/`revert`, so Solidity never regains control with a clobbered FMP. It is
        // therefore NOT `memory-safe` in the Yul sense — do not add the ("memory-safe")
        // annotation and do not introduce a normal (fall-through) exit from this block. (Same
        // reasoning as SphincsC13Asm, review C13-evm-f1, and LeanSphincsAsm.)
        assembly {
            // HASH WINDOW. A hash input `P ‖ address ‖ payload` starts 8 bytes into its prefix
            // word: the word stored at 0x00 is
            //   0^8 ‖ P ‖ address bytes 0..7          (word bytes 0..7, 8..23, 24..31)
            // so the fields that change from call to call (lo, hi, type | step) are the LOW 64
            // bits of the stored word:
            //   bits 56..63, 48..55, 40..47, 32..39   lo bytes 0, 1, 2, 3
            //   bits 24..31, 16..23,  8..15           hi bytes 0, 1, 2
            //   bits  0.. 7                           type | step << 5
            // The address's second half (layer ‖ tree ‖ 0^3) is memory 0x20..0x27, which no
            // 32-byte store below touches: it is written only by the `mstore(0x20, treeWord)` of
            // each layer (zero before), whose bytes 8..31 are zero and land on payload bytes that
            // are rewritten before every read. The payload starts at 0x28. The wide hashes use the
            // same shape 0x60 higher: prefix word at 0x60, address bytes 8..15 at 0x80..0x87,
            // payload from 0x88. The small window never reads past 0x57 (its longest input is the
            // digest's 0x50 bytes from 0x08) and the wide one never reads below 0x68.

            // MASKING. A 16-byte value arrives in a 32-byte word whose low half is not zero: a
            // calldataload carries the next field's bytes, a keccak256 word the 16 output bytes Th
            // drops. No such value is masked on its way into a hash; each store is placed so that
            // its low half never reaches a hash input:
            //   ρ          stored at 0x48, once for both digest calls; each reads 0x08..0x57
            //   digests    D_0 and D_1 are never stored; only their bits named below are used
            //   FORS sk    stored at 0x28; the leaf hash reads 0x28..0x37
            //   nodes      FORS and tree nodes, their siblings, the one-time leaves: L/R PLACEMENT
            //   FORS key   the same placement into the packed words at 0x88 + 32κ; tree κ < 23's
            //              stray low half lands on tree κ+1's first slot, which tree κ+1 writes
            //              next, and tree 23's (bit 9 of its leaf set) on 0x388..0x397
            //   counters   bottom: calldatacopy'd to 0x388..0x38B after the FORS loop, over the
            //              start of tree 23's stray half; its encoding reads 0x68..0x38B.
            //              middle, top: the previous layer's root (a raw keccak word) is stored at
            //              0x28 and the counter calldatacopy'd to 0x38..0x3B over the root's low
            //              half; the encoding reads 0x08..0x3B
            //   encodings  only the high 16 bytes (d) are read
            //   σ_i and every chain-step output: a CHAIN hash reads 0x28..0x37 only; the 32-byte
            //              store of end_i at 0x88 + 16i puts its low half on end_{i+1}'s slot,
            //              which the next (ascending) store overwrites, and end_63's spills to
            //              0x488..0x497, past the LEAF payload [0x88, 0x488). The 64 stores rewrite
            //              all of [0x88, 0x488), so nothing of the FORS key, the counter or the
            //              previous layer's chain ends survives into a LEAF payload
            // N_MASK is applied once, to the top root before the comparison with pkRoot. The
            // unmasked low halves are nonzero (calldata, hash output), so breaking one of these
            // invariants (a longer hash read, reordered stores) corrupts a hash input on every
            // signature and fails the known-answer tests.
            //
            // L/R PLACEMENT. A Merkle pair `L ‖ R` is the 32 payload bytes 0x28..0x47. The current
            // node, a 32-byte keccak word, is stored at p = 0x28 + 16·bit (the L slot when the
            // side bit is 0, the R slot when it is 1), then the sibling's 16 calldata bytes are
            // calldatacopy'd into the other slot, xor(p, 0x10). calldatacopy writes exactly 16
            // bytes, so with the node written first its stray low half is harmless: it lands on
            // the R slot, which the sibling then overwrites, or on 0x48..0x57, past the 0x40-byte
            // hash input. (Solady's MerkleProofLib swap, adapted to 16-byte children.) This is
            // Merkle.climb: the side bit is the low bit of the current node's index.
            let N_MASK := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000

            // A layer's one-time signature and tree path (Verify.lean `layerRoot`), given its
            // encoding hash `h` (already computed into the raw word), the key's leaf, the layer's
            // tree height and the calldata offset of the layer's signature. The caller has
            // stored the layer's address bytes 8..15 (layer ‖ tree ‖ 0^3) at 0x20 and 0x80.
            // Returns the root as a raw keccak word (the high 16 bytes are the root), or ends the
            // call with `false` when the counter's encoding is not a codeword.
            function layerRoot(h, P, leaf, height, layerPtr) -> cur {
                // codeword? (Encoding.lean): x_i = 2-bit digit i of d = h[0:16] read as a
                // little-endian u128, i.e. bits 2r..2r+1 of byte k of d for i = 4k + r; d is
                // the high 16 bytes of h, so byte k of d is byte(k, h). Admissible iff Σ x_i = T.
                // The sum is a SWAR reduction over the 64 two-bit fields of d = h >> 128 (byte
                // order does not change which 2-bit fields there are, so d is not reversed):
                //   pairs of x_i into 32 nibbles, each ≤ 6; pairs of nibbles into 16 bytes, each
                //   ≤ 12; multiplying by 0x0101…01 (16 ones) puts the sum of all 16 bytes in byte
                //   15 (bits 120..127). Every partial byte sum is ≤ 16·12 = 192 < 256, so no byte
                //   carries into the next and byte 15 is exact.
                // A well-formed signature that fails is rejected by returning `false` (the bool
                // contract), not by reverting, uniform with the root mismatch.
                // PARAM IDENTITIES: 128-bit masks = v·2 = 64·2 bits of d; 128 is T (TARGET_SUM).
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

                // lo = LE32(leaf) in the prefix word: byte 0 at bits 56..63, byte 1 at 48..55
                // (leaf < 2^10, so bytes 2 and 3 are zero).
                let leafLo := or(shl(56, and(leaf, 0xFF)), shl(48, shr(8, leaf)))

                // Chains (Ots.lean `otsLeaf`): end_i = chain σ_i from position x_i to 3; the step
                // from position mu is Th(P, A_chain(K, i, mu), value), type 1 with step = mu.
                // Chain i needs n_i = 3 - x_i steps, the 2-bit complement of x_i, so the n of
                // chains 4k..4k+3 are the 2-bit fields of nb = byte(k, h) xor 0xFF (bits 2r..2r+1
                // for chain 4k + r; nb is one byte, so shr(6, nb) needs no mask). Each chain
                // switches on n into straight-line code. Within a chain only address byte 7
                // (type | step << 5, memory 0x1F) changes from step to step, so the later steps
                // rewrite that byte with mstore8: 0x01, 0x21, 0x41 are type 1 at steps 0, 1, 2.
                // Unrolled by 4: one codeword byte per iteration, chains in ascending order.
                // end_i goes to 0x88 + 16i (see MASKING).
                let chainAdrs := or(P, or(leafLo, 1)) // type CHAIN, step 0
                let wots := add(layerPtr, 4) // σ_i at layer offset 4 + 16i
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
                            mstore(0x00, or(a, 0x40)) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        case 2 {
                            mstore(0x00, or(a, 0x20)) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        default {
                            mstore(0x00, a) // step 0 → 1
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x21) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
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
                            mstore(0x00, or(or(a, shl(24, 1)), 0x40)) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        case 2 {
                            mstore(0x00, or(or(a, shl(24, 1)), 0x20)) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        default {
                            mstore(0x00, or(a, shl(24, 1))) // step 0 → 1
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x21) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
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
                            mstore(0x00, or(or(a, shl(24, 2)), 0x40)) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        case 2 {
                            mstore(0x00, or(or(a, shl(24, 2)), 0x20)) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        default {
                            mstore(0x00, or(a, shl(24, 2))) // step 0 → 1
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x21) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
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
                            mstore(0x00, or(or(a, shl(24, 3)), 0x40)) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        case 2 {
                            mstore(0x00, or(or(a, shl(24, 3)), 0x20)) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        default {
                            mstore(0x00, or(a, shl(24, 3))) // step 0 → 1
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x21) // step 1 → 2
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                            mstore8(0x1F, 0x41) // step 2 → 3
                            mstore(0x28, val)
                            val := keccak256(0x08, 0x30)
                        }
                        mstore(add(slot, 48), val)
                    }
                }

                // One-time leaf (otsLeafHash) = Th(P, A_leaf(K), end_0 ‖ … ‖ end_63): prefix
                // word at 0x60 (type 2, hi 0, lo = leaf), the layer's address bytes 8..15 at
                // 0x80 (stored by the caller), 1024-byte payload at 0x88: 32 + 1024 = 0x420
                // bytes from 0x68.
                mstore(0x60, or(P, or(leafLo, 2)))
                cur := keccak256(0x68, 0x420) // unmasked, see L/R PLACEMENT

                // Tree.fold = Merkle.climb from (level 0, j = leaf): for ℓ = 0 .. height - 1,
                //   cur = Th(P, A_node(layer, tree, ℓ + 1, leaf >> (ℓ + 1)), L ‖ R),
                //   (L, R) = bit ℓ of leaf ? (path[ℓ], cur) : (cur, path[ℓ]),
                // path[ℓ] at layer offset 1028 + 16ℓ. Type NODE (3), hi = ℓ + 1 (one byte, bits
                // 24..31), lo = LE32(leaf >> (ℓ + 1)) (< 2^9: bytes 0 and 1, bits 56..63 and
                // 48..55). The pair goes in before the prefix word; the two touch disjoint bytes
                // (0x28..0x57 and 0x00..0x1F).
                let pathPtr := add(layerPtr, 1028)
                let nodeAdrs := or(P, 3)
                for { let l := 0 } lt(l, height) { l := add(l, 1) } {
                    let p := add(0x28, shl(4, and(shr(l, leaf), 1)))
                    mstore(p, cur)
                    calldatacopy(xor(p, 0x10), add(pathPtr, shl(4, l)), 0x10)
                    let j := shr(add(l, 1), leaf)
                    mstore(0x00, or(nodeAdrs, or(
                        or(shl(56, and(j, 0xFF)), shl(48, shr(8, j))),
                        shl(24, add(l, 1))
                    )))
                    cur := keccak256(0x08, 0x40)
                }
            }

            // ---------------------------------------------------------------
            // Input checks
            // ---------------------------------------------------------------

            // PARAM IDENTITY: 7740 = 16 + k(1+a)·16 + 2·(4 + 64·16 + 8·16) + (4 + 64·16 + 10·16)
            //                      = 16 + 4224 + 1156 + 1156 + 1188 (Constants.lean SIG_SIZE).
            if iszero(eq(sig.length, 7740)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid sig length")
                revert(0x00, 0x64)
            }

            // The key words are high-aligned: pkSeed = P ‖ 0^16, pkRoot = root ‖ 0^16. A nonzero
            // low half would make pkRoot unreachable (the root is N_MASK'd) and would corrupt the
            // address bytes of every prefix word built from pkSeed. Fail loudly instead of
            // returning false forever.
            if or(shl(128, pkSeed), shl(128, pkRoot)) {
                mstore(0x00, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(0x04, 0x20)
                mstore(0x24, 18)
                mstore(0x44, "Invalid public key")
                revert(0x00, 0x64)
            }

            let sigBase := sig.offset
            // P at word bytes 8..23 (see HASH WINDOW): OR an address's low 8 bytes into the low
            // 64 bits to get a prefix word.
            let P := shr(64, pkSeed)
            // Address bytes 8..15 of the small window: zero (layer 0, tree 0) for the digest and
            // FORS calls. Also zeroes 0x28..0x3F, payload written before every read.
            mstore(0x20, 0)

            // ---------------------------------------------------------------
            // 1. Message digest (Digest.lean `messageDigest`) — 2 keccak
            //    D_c = H(P ‖ A_msg(c) ‖ m ‖ ρ), c = 0, 1: type MSG (12), hi = c, every other
            //    field zero; 32 + 32 + 16 = 80 input bytes each, all 32 output bytes kept.
            //    The two inputs differ only in hi, whose byte 0 is at bits 24..31 of the prefix
            //    word, so m ‖ ρ is stored once and only the prefix word is rewritten.
            // ---------------------------------------------------------------
            mstore(0x00, or(P, 12))
            mstore(0x28, message)
            mstore(0x48, calldataload(sigBase)) // ρ = sig[0:16]; unmasked, see MASKING
            let D0 := keccak256(0x08, 0x50)
            mstore(0x00, or(P, or(12, shl(24, 1)))) // hi = 1
            let D1 := keccak256(0x08, 0x50)

            // D = D_0 ‖ D_1 read as one 512-bit little-endian number (digestIndex, digestLeaves):
            //   idx      = bits 0..25                       (D_0 bytes 0..3, the last one & 3)
            //   leaf_κ   = bits 26 + 10κ .. 35 + 10κ        κ = 0..23; leaf_23 is bits 256..265,
            //                                              D_1 byte 0 and the low 2 bits of byte 1
            //
            // lo = LE32(idx) for every FORS call. idx's little-endian bytes are D_0 bytes 0, 1,
            // 2 and 3 & 3, which sit at bits 248..255, 240..247, 232..239 and 224..231 of the
            // raw hash word; shifted down by 192 they are at bits 56..63, 48..55, 40..47 and
            // 32..39, exactly the lo field (see HASH WINDOW). PARAM IDENTITY: the mask keeps
            // h = 26 bits, 3 bytes + 2 bits (0x03 on D_0 byte 3).
            let idxLo := and(shr(192, D0), 0xFFFFFF0300000000)

            // The 24 FORS leaves. Y = D_0 byte-reversed is the little-endian number of D_0
            // (byte k at bits 8k..8k+7): swap adjacent bytes, then 2-, 4-, 8- and 16-byte
            // groups. Then U = (Y >> 26) | leaf_23 << 230 holds leaf_κ at bits 10κ..10κ+9 for
            // every κ (Y >> 26 has 230 bits: leaves 0..22), and tree κ takes the low 10 bits
            // and shifts U down. PARAM IDENTITIES: 26 = h; 230 = 256 - h = 23 a; 0x3FF = 2^a - 1.
            let U
            {
                let y := D0
                let m := 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF
                y := or(and(shr(8, y), m), shl(8, and(y, m)))
                m := 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF
                y := or(and(shr(16, y), m), shl(16, and(y, m)))
                m := 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF
                y := or(and(shr(32, y), m), shl(32, and(y, m)))
                m := 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF
                y := or(and(shr(64, y), m), shl(64, and(y, m)))
                y := or(shr(128, y), shl(128, y))
                U := or(shr(26, y), shl(230, or(byte(0, D1), shl(8, and(byte(1, D1), 3)))))
            }

            // The bottom layer's address bytes 8..15 for the wide window, stored before the FORS
            // loop, which writes the FORS key from 0x88 up and never below: layer 0 at 0x80, then
            // tree = idx >> 8 as u32 LE at 0x81..0x84, i.e. idx's LE bytes 1, 2, 3 (& 3) and 0,
            // which are D_0 bytes 1, 2, 3 already at word bytes 1, 2, 3. The rest of the word is
            // zero and lands on 0x88..0x9F, which the FORS loop rewrites (tree 0's two nodes).
            mstore(0x80, and(D0, shl(224, 0xFFFF03)))

            // ---------------------------------------------------------------
            // 2. FORS recovery (Fors.lean `forsRecover`, `treeRecover`) — 24 · (1 leaf + 9
            //    nodes) = 240 keccak. Per tree κ, opened leaf u = leaf_κ, secret sk, path p[0..9]:
            //      node = Th(P, A_fleaf(idx, κ, u), sk)
            //      λ = 1..9: node = Th(P, A_fnode(idx, κ, λ, u >> λ), L ‖ R),
            //                (L, R) = bit λ-1 of u ? (p[λ-1], node) : (node, p[λ-1])
            //      FORS key pair κ = (level-9 node, p[9]) ordered by bit 9 of u.
            //    No tree has a root hash and no hash folds the FORS key: its 48 nodes go
            //    straight into the bottom encoding (section 3).
            //
            //    FORS HI FIELD (forsHi, forsNodePosition). A leaf has hi = κ + 64u, a node at
            //    level λ, index j has hi = κ + 64(λ + 16j) = κ | λ << 6 | j << 10 (κ < 64,
            //    λ < 16, j < 2^10: disjoint bit fields, hi < 2^20). Its little-endian bytes are
            //      byte 0 = κ | (λ & 3) << 6            prefix bits 24..29 κ, 30..31 λ & 3
            //      byte 1 = λ >> 2 | (j & 0x3F) << 2     prefix bits 16..17 λ >> 2, 18..23 j & 0x3F
            //      byte 2 = j >> 6                       prefix bits 8..10 (j ≤ 511)
            //    κ is per tree and λ a literal in each unrolled level (LEVEL below). For
            //    j = u >> λ, W = u·(2^18 + 2^2) holds two disjoint copies of u, at bits 18..27
            //    and 2..11. After shr(λ, W), the first copy has u bit λ+t at bit 18+t, so its
            //    bits 18..23 are j & 0x3F; the second has u bit λ+6+t at bit 8+t, so its bits
            //    8..(11-λ) are j >> 6, which has 4 - λ bits (λ ≤ 3) or none. The mask keeps
            //    bits 18..23 and those 4 - λ bits (J below): 0xFC0700, 0xFC0300, 0xFC0100,
            //    then 0xFC0000. Nothing else lands in a kept bit: the first copy starts at bit
            //    18 - λ ≥ 9 > 11 - λ, the second ends at bit 11 - λ < 18, and u < 2^10 leaves
            //    the first copy's bits above 27 - λ zero. A leaf's u part is (u & 3) << 30 |
            //    (u >> 2) << 16 (byte 0 bits 6..7, byte 1), from u directly.
            // ---------------------------------------------------------------
            let forsAdrs := or(P, idxLo) // P and lo = idx; layer and tree are zero
            for { let kappa := 0 } lt(kappa, 24) { kappa := add(kappa, 1) } {
                let u := and(U, 0x3FF)
                U := shr(10, U)
                // treePtr = sig + 176κ: sk at treePtr + 16, p[ℓ] at treePtr + 32 + 16ℓ.
                // PARAM IDENTITY: 176 = (1 + a)·n = 11·16, one tree's opening.
                let treePtr := add(sigBase, mul(176, kappa))
                let treeAdrs := or(forsAdrs, shl(24, kappa)) // κ < 64 at bits 24..29
                let W := mul(u, 0x40004) // 2^18 + 2^2, see FORS HI FIELD

                // Leaf: type 15, hi = κ + 64u.
                mstore(0x00, or(treeAdrs, or(15, or(shl(30, and(u, 3)), shl(14, and(u, 0x3FC))))))
                mstore(0x28, calldataload(add(treePtr, 16))) // sk; unmasked, see MASKING
                let node := keccak256(0x08, 0x30) // unmasked, see L/R PLACEMENT

                // Levels λ = 1..9 (a - 1 = 9 node hashes), unrolled: L/R PLACEMENT with the side
                // bit λ-1 of u and the sibling p[λ-1] at treePtr + 16 + 16λ. LEVEL λ = type 17
                // (0x11) | (λ & 3) << 30 | (λ >> 2) << 16.
                let p
                // λ = 1: side = bit 0 of u, sibling p[0]
                p := add(0x28, shl(4, and(u, 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, shl(30, 1)), and(shr(1, W), 0xFC0700))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 32), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 2: side = bit 1 of u, sibling p[1]
                p := add(0x28, shl(4, and(shr(1, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, shl(30, 2)), and(shr(2, W), 0xFC0300))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 48), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 3: side = bit 2 of u, sibling p[2]
                p := add(0x28, shl(4, and(shr(2, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, shl(30, 3)), and(shr(3, W), 0xFC0100))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 64), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 4: side = bit 3 of u, sibling p[3]
                p := add(0x28, shl(4, and(shr(3, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, shl(16, 1)), and(shr(4, W), 0xFC0000))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 80), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 5: side = bit 4 of u, sibling p[4]
                p := add(0x28, shl(4, and(shr(4, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, or(shl(30, 1), shl(16, 1))), and(shr(5, W), 0xFC0000))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 96), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 6: side = bit 5 of u, sibling p[5]
                p := add(0x28, shl(4, and(shr(5, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, or(shl(30, 2), shl(16, 1))), and(shr(6, W), 0xFC0000))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 112), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 7: side = bit 6 of u, sibling p[6]
                p := add(0x28, shl(4, and(shr(6, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, or(shl(30, 3), shl(16, 1))), and(shr(7, W), 0xFC0000))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 128), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 8: side = bit 7 of u, sibling p[7]
                p := add(0x28, shl(4, and(shr(7, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, shl(16, 2)), and(shr(8, W), 0xFC0000))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 144), 0x10)
                node := keccak256(0x08, 0x40)
                // λ = 9: side = bit 8 of u, sibling p[8]
                p := add(0x28, shl(4, and(shr(8, u), 1)))
                mstore(0x00, or(treeAdrs, or(or(0x11, or(shl(30, 1), shl(16, 2))), and(shr(9, W), 0xFC0000))))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 160), 0x10)
                node := keccak256(0x08, 0x40)

                // The FORS key pair of tree κ (Merkle.ordered by bit 9 of u): the level-9 node and
                // its sibling p[9] (sig offset 32 + 176κ + 16·9 = 176 + 176κ) form the packed word
                // t_κ[0] ‖ t_κ[1] at 0x88 + 32κ, by the same placement: p = 0x88 + 32κ + 16·bit;
                // 0x88 + 32κ has bit 4 clear, so xor(p, 0x10) is the other half of that word. A
                // stray node low half lands on tree κ+1's first slot, which that tree writes next,
                // or for κ = 23 on 0x388..0x397, which the bottom counter (section 3) partly
                // overwrites and the bottom encoding reads no further than 0x38B (see MASKING).
                p := add(add(0x88, shl(5, kappa)), shl(4, and(shr(9, u), 1)))
                mstore(p, node)
                calldatacopy(xor(p, 0x10), add(treePtr, 176), 0x10)
            }

            // ---------------------------------------------------------------
            // 3. The three layers (Verify.lean `verify`, steps 3 to 5), from the bottom up. Each
            //    layer's key is OtsKey.ofIndex(layer, idx): its address bytes 8..15 (layer ‖
            //    tree ‖ 0^3) go to 0x20 (small window) and 0x80 (wide window), its leaf to lo.
            //    The encoding input is P ‖ A_enc(K) ‖ msg ‖ LE32(c): type ENCODING (4), hi = 0,
            //    lo = leaf. The counter's 4 signature bytes are LE32(c) already and are copied,
            //    never decoded.
            // ---------------------------------------------------------------

            // Bottom: K = (layer 0, tree idx >> 8, leaf idx mod 2^8 = D_0 byte 0); msg = the FORS
            // key, already at 0x88..0x387 in the wide window, whose bytes 8..15 at 0x80 hold this
            // layer's (stored before the FORS loop). Input 32 + 768 + 4 = 804 = 0x324 bytes from
            // 0x68: the counter (sig offset 4240) goes to 0x388..0x38B, right after the FORS key,
            // and must follow the FORS loop (tree 23's key store can write 0x388..0x397).
            calldatacopy(0x388, add(sigBase, 4240), 4)
            let leaf := byte(0, D0)
            mstore(0x60, or(P, or(shl(56, leaf), 4)))
            let h := keccak256(0x68, 0x324)
            let treeWord := and(D0, shl(224, 0xFFFF03)) // as stored at 0x80 above
            mstore(0x20, treeWord)
            mstore(0x80, treeWord) // rewrites only 0x88..0x9F of the FORS key, already hashed
            let root := layerRoot(h, P, leaf, 8, add(sigBase, 4240))

            // Middle: K = (layer 1, tree idx >> 16, leaf (idx >> 8) mod 2^8 = D_0 byte 1); msg =
            // the bottom root, 52-byte input in the small window. The tree word is layer 1 at
            // byte 0, then idx >> 16 as u32 LE: D_0 bytes 2 and 3 (& 3), moved up one byte.
            leaf := byte(1, D0)
            treeWord := or(shl(248, 1), and(shl(8, D0), shl(232, 0xFF03)))
            mstore(0x20, treeWord)
            mstore(0x28, root) // the root's low half is overwritten by the counter, see MASKING
            calldatacopy(0x38, add(sigBase, 5396), 4)
            mstore(0x00, or(P, or(shl(56, leaf), 4)))
            h := keccak256(0x08, 0x34)
            mstore(0x80, treeWord)
            root := layerRoot(h, P, leaf, 8, add(sigBase, 5396))

            // Top: K = (layer 2, tree 0, leaf idx >> 16 = D_0 byte 2 | (byte 3 & 3) << 8, ten
            // bits, LE32 at lo bytes 0 and 1); msg = the middle root.
            leaf := or(byte(2, D0), shl(8, and(byte(3, D0), 3)))
            treeWord := shl(248, 2)
            mstore(0x20, treeWord)
            mstore(0x28, root)
            calldatacopy(0x38, add(sigBase, 6552), 4)
            mstore(0x00, or(P, or(or(shl(56, byte(2, D0)), shl(48, and(byte(3, D0), 3))), 4)))
            h := keccak256(0x08, 0x34)
            mstore(0x80, treeWord)
            root := layerRoot(h, P, leaf, 10, add(sigBase, 6552))

            // Step 6: the top root is the key's.
            valid := eq(and(root, N_MASK), pkRoot)
            mstore(0x00, valid)
            return(0x00, 0x20)
        }
    }
}
