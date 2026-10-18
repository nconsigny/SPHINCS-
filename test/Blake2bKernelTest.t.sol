// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";

/// @dev Isolated harness for the BLAKE2b-over-0x09 kernel used by the src/blake/
///      verifiers. Validates the LE/BE endianness bridge against hashlib.blake2b
///      reference vectors BEFORE the kernel is wired into any SPHINCS+ verifier.
///      The blake2b() Yul function here is the exact kernel copied into each
///      src/blake verifier (with inPtr=0x00 there; here the input is copied to 0x80
///      to preserve the Solidity free-memory pointer; the verifiers also place the
///      scratch S at 0xA00, above their fixed single-block F/H precompile buffers at
///      0x800/0x900). Keep them in lockstep. The verifiers' F/H fast path (one block,
///      constant IV and t/f) is not this kernel; it is covered end to end by the
///      SphincsC1{1,2,3}BlakeTest signer vectors.
///      Inputs must stay below 0x780 bytes (0x80 + len must not reach the 0x800
///      scratch), which also keeps the kernel's 2-byte counter swap exact.
contract Blake2bHarness {
    function h16(bytes calldata input) external view returns (bytes32) {
        return _run(input, 16);
    }

    function h32(bytes calldata input) external view returns (bytes32) {
        return _run(input, 32);
    }

    function _run(bytes calldata input, uint256 nn) internal view returns (bytes32 out) {
        assembly {
            let len := input.length
            if gt(len, 0x780) { revert(0, 0) } // input at 0x80 must not reach the 0x800 scratch
            calldatacopy(0x80, input.offset, len) // keep 0x00..0x80 (FMP/zero-slot) intact
            out := blake2b(0x80, len, nn)

            // BLAKE2b(inPtr[0..inLen]) truncated to nn bytes, built on the 0x09 (BLAKE2F)
            // compression precompile. Returns the digest top-aligned in a 256-bit word
            // (nn=16 → 16 bytes in the high half, low half zero; nn=32 → full word).
            function blake2b(inPtr, inLen, nnLocal) -> result {
                let S := 0x800
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

contract Blake2bKernelTest is Test {
    Blake2bHarness h;

    function setUp() public {
        h = new Blake2bHarness();
    }

    function _seq(uint256 n, uint256 mul, uint256 add_) internal pure returns (bytes memory b) {
        b = new bytes(n);
        for (uint256 i = 0; i < n; i++) b[i] = bytes1(uint8((i * mul + add_) & 0xff));
    }

    function test_empty() public view {
        assertEq(h.h16(""), bytes32(uint256(0xcae66941d9efbd404e4d88758ea67670) << 128));
        assertEq(h.h32(""), bytes32(uint256(0x0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8)));
    }

    function test_abc() public view {
        assertEq(h.h16(hex"616263"), bytes32(uint256(0xcf4ab791c62b8d2b2109c90275287816) << 128));
        assertEq(h.h32(hex"616263"), bytes32(uint256(0xbddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319)));
    }

    function test_oneFullBlock_128() public view {
        bytes memory b = _seq(128, 1, 0); // 0x00,0x01,...,0x7f
        assertEq(h.h16(b), bytes32(uint256(0xa74787004ef589e31149183900d0294a) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xc3582f71ebb2be66fa5dd750f80baae97554f3b015663c8be377cfcb2488c1d1)));
    }

    function test_multiBlock_200() public view {
        bytes memory b = _seq(200, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0x245dc987e68b6b005bad7fc96c26d62f) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xf5f9dd0c4e4023e68a8c5e4b9332acde4b16e7c51441723fe02a34084a394104)));
    }

    function test_96() public view {
        bytes memory b = _seq(96, 3, 1);
        assertEq(h.h16(b), bytes32(uint256(0xeb0e31ac0453312cf1d0f86514cfdd38) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xfa797d02319e8b5b77f8e2d40734ec9cae9a96f52aa0447f18a87b4b5878feac)));
    }

    // Lengths the SPHINCS+ verifier actually hashes: 160 (H_msg), 288 (T_k),
    // 1440 (T_l), plus 256/384 (exact multi-block boundaries). All _seq(n,7,0).
    function test_160() public view {
        bytes memory b = _seq(160, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0x86a61fc2d20d3675732102c47bf0baa7) << 128));
        assertEq(h.h32(b), bytes32(uint256(0x49dffb6782726602823e193751df5d3f8eae22e70825e74254cee845c46e2698)));
    }

    function test_256() public view {
        bytes memory b = _seq(256, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0xdbb08d79105462394550aa4d4e10133f) << 128));
        assertEq(h.h32(b), bytes32(uint256(0x3d0cb2693dfbac42af5a6cc960953fea8714aa39c4bcd054ef61d6b5e98ade4a)));
    }

    function test_288() public view {
        bytes memory b = _seq(288, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0x3bff59dc54c6edf64fa10f3b805c6a1b) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xc168c5c43aa79c0779e2dcdd85575b97d8bd6ad990d58d8dab6fb4dae3facae5)));
    }

    function test_384() public view {
        bytes memory b = _seq(384, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0xe6be43a2ad0479eddecb2156d202c43a) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xc1657697b6e9c44f9086f3103635482bdb0f16550335765aad643f155aa714c0)));
    }

    // Block-boundary neighbours (127/129/255) and C12-BLAKE's T_l length (1536 = 0x600,
    // the largest input any src/blake verifier hashes). All _seq(n,7,0).
    function test_127() public view {
        bytes memory b = _seq(127, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0x40efb3ed1b6eb973c5f774422adb0230) << 128));
        assertEq(h.h32(b), bytes32(uint256(0x4ff62e7c4c43fe101a078479c48836be4907d9d498dcc577ca89d694b2c11f9b)));
    }

    function test_129() public view {
        bytes memory b = _seq(129, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0x2ec7e7bf8a8265ffd68aadd70ecd2b7e) << 128));
        assertEq(h.h32(b), bytes32(uint256(0x3934215260b1039be9d9d2b073b059bcd50120c327a22af93eb4d98cf821c14c)));
    }

    function test_255() public view {
        bytes memory b = _seq(255, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0xb4b6fa7ac93abe0503b7ac802593eadd) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xa3bb8b4fa098078d32bb5a89e905e237862fd83e99141ca7d8a073bb268ba2a0)));
    }

    function test_1536() public view {
        bytes memory b = _seq(1536, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0x480e2938156ec4548e311310aa107cda) << 128));
        assertEq(h.h32(b), bytes32(uint256(0xf62734fdc4ebbb200a0c6c58803addce49f1ba0f5b8d408aa9b66cd26a4fff01)));
    }

    function test_1440() public view {
        bytes memory b = _seq(1440, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0xfa6114512d87fca1cb13168ecd55d313) << 128));
        assertEq(h.h32(b), bytes32(uint256(0x2154d3017cbb6eebc1360f5dd25304d536d0f676281ea4070717e0d6786ad6ec)));
    }
}
