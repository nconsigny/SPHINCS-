// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Sagar Rana

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SLH-DSA-Keccak-128sAsm.sol";

/// @notice Tests for SLH-DSA-Keccak-128sAsm: C12's plain SPHINCS+ (FIPS uncompressed ADRS, keccak256) at the
///         NIST 128s parameters (n=16, h=63, d=7, h'=9, a=12, k=14, w=16), 7,872-byte signature.
///         - Known answers: test/fixtures/slh-dsa-keccak-128s-kat.json, from script/slh_dsa_keccak_128s_signer.py
///           via script/make_slh_dsa_keccak_128s_kat.py (`--check` reproduces it byte for byte).
///         - Rejection: wrong message, wrong key, a flipped byte in every signature field (R, each FORS
///           tree's secret and top auth node, each layer's first message chain, checksum chain and first and
///           last XMSS auth node), and a fuzzed byte flip.
///         - Malformed input: the two Error(string) reverts (bad length, non-canonical key).
///         - Gas: a ceiling on the gas verify spends in its own call frame.
///         - FFI: a fresh signature from the Python signer (needs pycryptodome; ~15 s).
///         Requires fs read access to test/fixtures (see `fs_permissions` in foundry.toml).
contract SlhDsaKeccak128sTest is Test {
    SLH_DSA_Keccak_128sAsm verifier;

    string constant FIXTURE = "test/fixtures/slh-dsa-keccak-128s-kat.json";
    string constant SIGNER = "script/slh_dsa_keccak_128s_signer.py";

    uint256 constant SIG_LEN = 7872;
    uint256 constant N = 16;
    uint256 constant R_LEN = 32;
    uint256 constant FORS_STRIDE = 13 * N; //       sk + 12 auth nodes per FORS tree
    uint256 constant OFF_HT = R_LEN + 14 * FORS_STRIDE; // 2,944: first hypertree layer
    uint256 constant LAYER_STRIDE = 44 * N; //      35 WOTS values + 9 auth nodes per layer
    uint256 constant OFF_AUTH = 35 * N; //          XMSS auth path within a layer

    // Ceiling on the gas `verify` spends in its own call frame (vm.lastCallGas().gasTotalUsed) on every
    // valid signature this file verifies (the fixture and the FFI one). Unlike the WOTS+C sets, the cost
    // varies per signature: each WOTS chain runs 15 - digit steps, so the frame gas follows the 35 digits
    // of all 7 layers (everything else is constant). Measured 360,391..382,336 over the fixture and
    // 366,376 on the FFI signature (forge 1.3.1, solc 0.8.30, via-IR, optimizer_runs = 200). This is a
    // regression gate on real signatures, not a bound over all signatures: an all-zero-digit signature
    // would cost far more. If a toolchain change moves the measurement, re-measure and update.
    uint256 constant VERIFY_GAS_MAX = 386_000;

    struct Vector {
        string label;
        bytes32 pkSeed;
        bytes32 pkRoot;
        bytes32 message;
        bytes sig;
    }

    Vector[] vectors;

    function setUp() public {
        verifier = new SLH_DSA_Keccak_128sAsm();
        string memory json = vm.readFile(FIXTURE);
        for (uint256 i = 0; vm.keyExistsJson(json, string.concat(".vectors[", vm.toString(i), "]")); i++) {
            string memory b = string.concat(".vectors[", vm.toString(i), "].");
            vectors.push(
                Vector({
                    label: vm.parseJsonString(json, string.concat(b, "label")),
                    pkSeed: vm.parseJsonBytes32(json, string.concat(b, "pkSeed")),
                    pkRoot: vm.parseJsonBytes32(json, string.concat(b, "pkRoot")),
                    message: vm.parseJsonBytes32(json, string.concat(b, "message")),
                    sig: vm.parseJsonBytes(json, string.concat(b, "sig"))
                })
            );
        }
        assertGe(vectors.length, 4, "fixture vectors");
    }

    function _verifySilent(bytes32 seed, bytes32 root, bytes32 msg_, bytes memory sig) internal view returns (bool ok) {
        (bool callOk, bytes memory res) =
            address(verifier).staticcall(abi.encodeWithSelector(verifier.verify.selector, seed, root, msg_, sig));
        if (!callOk || res.length < 32) return false;
        ok = abi.decode(res, (bool));
    }

    function _flip(bytes memory sig, uint256 at) internal pure returns (bytes memory out) {
        out = bytes.concat(sig);
        out[at] = bytes1(uint8(out[at]) ^ 0x01);
    }

    /// verify must accept, within the gas ceiling; logs the frame gas.
    function _acceptWithinCeiling(string memory label, bytes32 seed, bytes32 root, bytes32 msg_, bytes memory sig)
        internal
    {
        bool ok = verifier.verify(seed, root, msg_, sig);
        uint256 frameGas = vm.lastCallGas().gasTotalUsed;
        emit log_named_uint(string.concat(label, ": verify frame gas"), frameGas);
        assertTrue(ok, label);
        assertLe(frameGas, VERIFY_GAS_MAX, "verify gas above the ceiling");
    }

    // ── Known answers and gas ──

    function testAcceptsKnownAnswers() public {
        for (uint256 i = 0; i < vectors.length; i++) {
            Vector storage v = vectors[i];
            assertEq(v.sig.length, SIG_LEN, "fixture signature length");
            _acceptWithinCeiling(v.label, v.pkSeed, v.pkRoot, v.message, v.sig);
        }
    }

    // ── Rejection ──

    function testRejectsWrongMessage() public view {
        for (uint256 i = 0; i < vectors.length; i++) {
            Vector storage v = vectors[i];
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message ^ bytes32(uint256(1)), v.sig), v.label);
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, ~v.message, v.sig), v.label);
        }
    }

    function testRejectsWrongKey() public view {
        Vector storage a = vectors[0];
        Vector storage b = vectors[1];
        assertFalse(_verifySilent(b.pkSeed, b.pkRoot, a.message, a.sig), "other vector's key");
        assertFalse(_verifySilent(a.pkSeed, b.pkRoot, a.message, a.sig), "other root");
        assertFalse(_verifySilent(b.pkSeed, a.pkRoot, a.message, a.sig), "other seed");
        assertFalse(_verifySilent(a.pkSeed, a.pkRoot ^ bytes32(uint256(1) << 200), a.message, a.sig), "root bit");
        assertFalse(_verifySilent(a.pkSeed ^ bytes32(uint256(1) << 200), a.pkRoot, a.message, a.sig), "seed bit");
    }

    function testRejectsTamperedFields() public view {
        assertEq(OFF_HT + 7 * LAYER_STRIDE, SIG_LEN, "layout covers the signature");
        Vector storage v = vectors[0];
        // R: first and last byte of the 32-byte word
        assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, 0)), "R[0]");
        assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, R_LEN - 1)), "R[31]");
        // every FORS tree: its secret and its top auth node
        for (uint256 t = 0; t < 14; t++) {
            uint256 base = R_LEN + t * FORS_STRIDE;
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, base)), "FORS sk");
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, base + FORS_STRIDE - 1)), "FORS auth");
        }
        // every hypertree layer: first message chain, last checksum chain, first and last XMSS auth node
        for (uint256 l = 0; l < 7; l++) {
            uint256 base = OFF_HT + l * LAYER_STRIDE;
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, base)), "WOTS chain 0");
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, base + 34 * N)), "WOTS chain 34");
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, base + OFF_AUTH)), "XMSS auth 0");
            assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, _flip(v.sig, base + LAYER_STRIDE - 1)), "XMSS auth 8");
        }
    }

    /// A flipped bit anywhere in the signature must reject: R is read as a full word in H_msg, and every
    /// other 16-byte value is read whole.
    function testFuzz_RejectsFlippedByte(uint256 at, uint8 mask) public view {
        vm.assume(mask != 0);
        Vector storage v = vectors[0];
        bytes memory sig = bytes.concat(v.sig);
        at = bound(at, 0, SIG_LEN - 1);
        sig[at] = bytes1(uint8(sig[at]) ^ mask);
        assertFalse(_verifySilent(v.pkSeed, v.pkRoot, v.message, sig));
    }

    // ── Malformed input ──

    function testRevertsOnBadLength() public {
        Vector storage v = vectors[0];
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot, v.message, new bytes(SIG_LEN - 1));
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot, v.message, bytes.concat(v.sig, hex"00"));
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot, v.message, new bytes(6592)); // a C12 signature
    }

    function testFuzz_RevertsOnNonCanonicalKey(uint128 low, bool onRoot) public {
        vm.assume(low != 0);
        Vector storage v = vectors[0];
        bytes32 seed = onRoot ? v.pkSeed : v.pkSeed | bytes32(uint256(low));
        bytes32 root = onRoot ? v.pkRoot | bytes32(uint256(low)) : v.pkRoot;
        vm.expectRevert(bytes("Invalid public key"));
        verifier.verify(seed, root, v.message, v.sig);
    }

    // ── FFI: a fresh signature from the Python signer ──

    function testVerifyFFI_Python() public {
        bytes32 masterSk = keccak256("SLH-DSA-Keccak-128s FFI master key");
        bytes32 message = keccak256("SLH-DSA-Keccak-128s FFI message");
        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = SIGNER;
        inputs[2] = vm.toString(masterSk);
        inputs[3] = vm.toString(message);
        (bytes32 seed, bytes32 root, bytes memory sig) = abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
        assertEq(sig.length, SIG_LEN, "FFI signature length");

        _acceptWithinCeiling("FFI", seed, root, message, sig);
        assertFalse(_verifySilent(seed, root, message ^ bytes32(uint256(1)), sig), "FFI: wrong message");
        assertFalse(_verifySilent(seed, root, message, _flip(sig, SIG_LEN / 2)), "FFI: tampered");
    }
}
