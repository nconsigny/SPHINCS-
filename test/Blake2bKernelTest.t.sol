// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

/// @dev Isolated harness for the BLAKE2b-over-0x09 kernel used by the src/blake/
///      verifiers. Validates the LE/BE endianness bridge against hashlib.blake2b
///      reference vectors BEFORE the kernel is wired into any SPHINCS+ verifier.
///      The blake2b()/bswap64() Yul functions here are the exact kernel that will
///      be copied into each src/blake verifier (with inPtr=0x00 there; here the
///      input is copied to 0x80 to preserve the Solidity free-memory pointer).
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
            calldatacopy(0x80, input.offset, len) // keep 0x00..0x80 (FMP/zero-slot) intact
            out := blake2b(0x80, len, nn)

            // BLAKE2b(inPtr[0..inLen]) truncated to nn bytes, built on the 0x09 (BLAKE2F)
            // compression precompile. Returns the digest top-aligned in a 256-bit word
            // (nn=16 → 16 bytes in the high half, low half zero; nn=32 → full word).
            function blake2b(inPtr, inLen, nnLocal) -> result {
                let S := 0x800 // scratch for the 213-byte precompile input (clear of inPtr region); matches src/blake/

                // rounds = 12 (big-endian, first 4 bytes)
                mstore(S, shl(224, 12))

                // init state h: 8 little-endian 64-bit words at S+4..S+68.
                // h0 = IV0 ^ 0x01010000 ^ nn (kk=0); h1..h7 = IV1..IV7.
                let h0 := bswap64(xor(xor(0x6a09e667f3bcc908, 0x01010000), nnLocal))
                mstore(add(S, 4), or(or(shl(192, h0), shl(128, bswap64(0xbb67ae8584caa73b))),
                                     or(shl(64, bswap64(0x3c6ef372fe94f82b)), bswap64(0xa54ff53a5f1d36f1))))
                mstore(add(S, 36), or(or(shl(192, bswap64(0x510e527fade682d1)), shl(128, bswap64(0x9b05688c2b3e6c1f))),
                                      or(shl(64, bswap64(0x1f83d9abfb41bd6b)), bswap64(0x5be0cd19137e2179))))

                let remaining := inLen
                let blockOff := 0
                let processed := 0
                for {} 1 {} {
                    let thisLen := 128
                    let isLast := 0
                    if lt(remaining, 128) { thisLen := remaining isLast := 1 }
                    if eq(remaining, 128) { isLast := 1 }
                    processed := add(processed, thisLen)

                    // m field (128 bytes): zero then copy thisLen raw bytes (no swap — BLAKE2b
                    // reads the message block as 16 LE words, which is the raw byte order).
                    mstore(add(S, 68), 0) mstore(add(S, 100), 0)
                    mstore(add(S, 132), 0) mstore(add(S, 164), 0)
                    let src := add(inPtr, blockOff)
                    let dst := add(S, 68)
                    let full := and(thisLen, not(31))
                    let o := 0
                    for {} lt(o, full) { o := add(o, 32) } { mstore(add(dst, o), mload(add(src, o))) }
                    let rest := and(thisLen, 31)
                    if rest {
                        let mask := not(shr(mul(rest, 8), not(0))) // top `rest` bytes set
                        mstore(add(dst, o), and(mload(add(src, o)), mask))
                    }

                    // t_0 = processed (LE), t_1 = 0 (clears bytes through the f slot)
                    mstore(add(S, 196), shl(192, bswap64(processed)))
                    mstore8(add(S, 212), isLast) // final-block flag

                    // compress; output (new state) overwrites the h field in place
                    if iszero(staticcall(gas(), 0x09, S, 213, add(S, 4), 64)) { revert(0, 0) }

                    remaining := sub(remaining, thisLen)
                    blockOff := add(blockOff, 128)
                    if iszero(remaining) { break }
                }

                switch nnLocal
                case 16 { result := and(mload(add(S, 4)), 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000) }
                default { result := mload(add(S, 4)) }
            }

            function bswap64(x) -> y {
                for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                    y := or(shl(8, y), and(x, 0xff))
                    x := shr(8, x)
                }
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

    function test_1440() public view {
        bytes memory b = _seq(1440, 7, 0);
        assertEq(h.h16(b), bytes32(uint256(0xfa6114512d87fca1cb13168ecd55d313) << 128));
        assertEq(h.h32(b), bytes32(uint256(0x2154d3017cbb6eebc1360f5dd25304d536d0f676281ea4070717e0d6786ad6ec)));
    }
}
