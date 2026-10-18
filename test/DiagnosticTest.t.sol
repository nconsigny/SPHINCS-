// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/sha/SLH-DSA-SHA2-128-24-Diagnostic.sol";
import "../src/sha/SLH-DSA-SHA2-128-24verifier.sol";
import {SLH_DSA_SHA2_128_24_KAT_Test} from "./SLH-DSA-SHA2-128-24-KAT.t.sol";

/// @notice The Diagnostic must trace the FORS tree the live verifier actually computes.
///         Regression test for review finding slh-diag-stale-hmsg-envelope: after SLH-X-f1
///         moved the verifier to FIPS 205 external H_msg (M' = 0x00 ‖ 0x00 ‖ M) the
///         Diagnostic kept the old internal H_msg, so on every current signature it derived
///         a different leafIdx / md[0] and traced a tree the verifier never builds. Its
///         c5/c11/c17/c22 outputs were also really the nodes after H calls j = 1..4.
///
///         Uses the pinned KAT (deterministic, no FFI signer) and an independent high-level
///         reference (plain sha256 + abi.encodePacked ADRSc). The reference runs the whole
///         SLH-DSA verify and must rebuild pkRoot, which ties it to the verifier's path.
contract DiagnosticTest is Test {
    bytes32 constant MSG = 0xdeadbeef00000000000000000000000000000000000000000000000000000000;
    bytes32 constant SEED = 0x750e7b30f37700dd14b20a5c647bb93600000000000000000000000000000000;
    bytes32 constant ROOT = 0x3456300211d2a77c26a60804b918738f00000000000000000000000000000000;

    struct Trace {
        uint256 leafIdx;
        bytes32 leaf; // tree-0 FORS leaf
        bytes32[24] nodes; // nodes[j] = tree-0 node after H call j
        bytes32 rebuiltRoot; // full SLH-DSA verify result (XMSS root)
    }

    function _adrs(uint8 typ, uint32 kp, uint32 w2, uint32 w3) internal pure returns (bytes memory) {
        // ADRSc: layer(1) ‖ tree(8) ‖ type(1) ‖ kp(4) ‖ word2(4) ‖ word3(4) = 22 B (d = 1)
        return abi.encodePacked(uint8(0), uint64(0), typ, kp, w2, w3);
    }

    function _th(bytes16 seed, bytes memory adrs, bytes memory m) internal pure returns (bytes16) {
        return bytes16(sha256(abi.encodePacked(seed, bytes32(0), bytes16(0), adrs, m)));
    }

    function _n(bytes memory sig, uint256 off) internal pure returns (bytes16 r) {
        assembly {
            r := mload(add(add(sig, 0x20), off))
        }
    }

    /// @dev FIPS 205 external SLH-DSA-SHA2-128-24 verify (n=16 h=22 d=1 a=24 k=6 w=4).
    function _ref(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig)
        internal
        pure
        returns (Trace memory tr)
    {
        bytes16 seed = bytes16(pkSeed);
        bytes16 R = _n(sig, 0);
        bytes32 inner = sha256(abi.encodePacked(R, seed, bytes16(pkRoot), hex"0000", message));
        bytes32 dig = sha256(abi.encodePacked(R, seed, inner, uint32(0))); // MGF1 block 0
        tr.leafIdx = (uint256(dig) >> 88) & 0x3FFFFF;
        uint32 kp = uint32(tr.leafIdx);

        bytes memory roots;
        for (uint256 t = 0; t < 6; t++) {
            uint256 md = (uint256(dig) >> (232 - 24 * t)) & 0xFFFFFF;
            uint256 off = 16 + t * 400;
            bytes16 node = _th(seed, _adrs(3, kp, 0, uint32((t << 24) | md)), abi.encodePacked(_n(sig, off)));
            if (t == 0) tr.leaf = bytes32(node);
            uint256 idx = md;
            for (uint256 j = 0; j < 24; j++) {
                bytes16 sib = _n(sig, off + 16 + 16 * j);
                uint256 parent = idx >> 1;
                bytes memory adrs = _adrs(3, kp, uint32(j + 1), uint32((t << (23 - j)) | parent));
                node = (idx & 1) == 0
                    ? _th(seed, adrs, abi.encodePacked(node, sib))
                    : _th(seed, adrs, abi.encodePacked(sib, node));
                if (t == 0) tr.nodes[j] = bytes32(node);
                idx = parent;
            }
            roots = abi.encodePacked(roots, node);
        }
        bytes16 pkFors = _th(seed, _adrs(4, kp, 0, 0), roots);

        uint256 v = uint256(uint128(pkFors));
        uint256 csum;
        uint256[68] memory d;
        for (uint256 i = 0; i < 64; i++) {
            d[i] = (v >> (126 - 2 * i)) & 3;
            csum += 3 - d[i];
        }
        for (uint256 j = 0; j < 4; j++) {
            d[64 + j] = (csum >> (6 - 2 * j)) & 3;
        }
        bytes memory tops;
        uint256 wOff = 16 + 2400;
        for (uint256 i = 0; i < 68; i++) {
            bytes16 val = _n(sig, wOff + 16 * i);
            for (uint256 s = d[i]; s < 3; s++) {
                val = _th(seed, _adrs(0, kp, uint32(i), uint32(s)), abi.encodePacked(val));
            }
            tops = abi.encodePacked(tops, val);
        }
        bytes16 node2 = _th(seed, _adrs(1, kp, 0, 0), tops);
        uint256 mIdx = tr.leafIdx;
        uint256 aOff = wOff + 68 * 16;
        for (uint256 h = 0; h < 22; h++) {
            bytes16 sib = _n(sig, aOff + 16 * h);
            uint256 parent = mIdx >> 1;
            bytes memory adrs = _adrs(2, 0, uint32(h + 1), uint32(parent));
            node2 = (mIdx & 1) == 0
                ? _th(seed, adrs, abi.encodePacked(node2, sib))
                : _th(seed, adrs, abi.encodePacked(sib, node2));
            mIdx = parent;
        }
        tr.rebuiltRoot = bytes32(node2);
    }

    function testTree0TraceMatchesVerifierPath() public {
        bytes memory sig = new SLH_DSA_SHA2_128_24_KAT_Test().sigVector();
        assertTrue(new SLH_DSA_SHA2_128_24_Verifier().verify(SEED, ROOT, MSG, sig), "pinned KAT must verify");

        Trace memory tr = _ref(SEED, ROOT, MSG, sig);
        assertEq(tr.rebuiltRoot, ROOT, "reference must rebuild pkRoot (= the verifier's path)");
        assertEq(tr.leafIdx, 2085853, "FORS key pair of the pinned KAT");

        (bytes32 leaf, bytes32 c0, bytes32 c5, bytes32 c11, bytes32 c17, bytes32 c22, bytes32 r0) =
            new SLH_DSA_SHA2_128_24_Diagnostic().forsTree0Trace(SEED, ROOT, MSG, sig);
        assertEq(leaf, tr.leaf, "leaf");
        assertEq(c0, tr.nodes[0], "c0");
        assertEq(c5, tr.nodes[5], "c5");
        assertEq(c11, tr.nodes[11], "c11");
        assertEq(c17, tr.nodes[17], "c17");
        assertEq(c22, tr.nodes[22], "c22");
        assertEq(r0, tr.nodes[23], "r0");

        emit log_named_bytes32("leaf", leaf);
        emit log_named_bytes32("r0", r0);
    }
}
