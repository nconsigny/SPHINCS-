// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/LeanSphincs-SAsm.sol";

/// @notice Tests for the leanSphincs-S keccak256 verifier (spec: docs/leanSphincs-S-keccak.md,
///         "spec §N" below). leanSphincs-S is leanSphincs-23 with one more XMSS level (h = 26,
///         4,164-byte signature) and the upstream keccak branch's merged encoding: no FORS key
///         hash, the WOTS+C encoding absorbs the 26 FORS tops and then the counter (spec §6, §7).
///         - Known answers: test/fixtures/leansphincs-s-keccak-kat.json holds `lssk kat` vectors
///           from the Rust signer (signers/leansphincs-s-keccak), each confirmed by the independent
///           Python verifier (script/leansphincs_s_signer.py --verify). Regenerate with
///           `.venv/bin/python signers/leansphincs-s-keccak/make_kat_fixture.py`. The vectors use
///           pruned keys (kept subtree height b = 6, 10, 12); the verifier cannot tell those from
///           a full b = 26 key. The fixture must cover both sides of the two placements that
///           depend on an index bit and touch the signature end or the counter (bit 25 of idx,
///           bit 11 of u_12).
///         - Rejection: message, key (zero key words included) and per-field signature tampering,
///           plus a fuzzed byte flip.
///         - Spec model: a plain-Solidity re-implementation of verification (bottom of the file),
///           used to show the WOTS+C target-sum check is enforced on its own, on both sides
///           (Σ < T and Σ > T), and that the verifier accepts exactly what the model accepts on
///           signatures no signer produced: at the fixture digests (WOTS values and auth path
///           changed), and at random digests, where the leaf index, all 13 FORS indices and the
///           codeword are fresh, so every FORS climb, WOTS chain and XMSS level is checked
///           against the model at inputs no fixture vector has.
///         - Malformed input: the two Error(string) reverts of spec §12 (fuzzed over the key's low
///           half), and dirty ABI padding past the signature on every vector.
///         - Gas: a ceiling on the gas verify spends in its own call frame, on the known answers
///           and on every random-digest signature.
///         - FFI: a fresh signature from the Rust CLI, and one from a Light-tier key file
///           (`lssk keygen` + `sign-key`, spec §14), which must equal the stateless signer's
///           bytes (skipped when the CLI is not built, except under CI; fails when the binary is
///           older than the crate sources).
///         Requires fs read access to test/fixtures (see `fs_permissions` in foundry.toml).
contract LeanSphincsSTest is Test {
    LeanSphincsSAsm verifier;

    string constant FIXTURE = "test/fixtures/leansphincs-s-keccak-kat.json";
    string constant LSSK = "signers/leansphincs-s-keccak/target/release/lssk";
    // Prints `fresh`, `missing`, or `stale` when a crate source (Cargo.toml, Cargo.lock, src/**.rs,
    // as crosscheck.py's ensure_binary) is newer than the binary.
    string constant LSSK_PROBE = "d=signers/leansphincs-s-keccak; b=$d/target/release/lssk; "
        "if [ ! -x $b ]; then echo missing; "
        "elif [ -n \"$(find $d/Cargo.toml $d/Cargo.lock $d/src -newer $b \\( -name '*.rs' -o -name 'Cargo.*' \\) "
        "2>/dev/null | head -n 1)\" ]; then echo stale; else echo fresh; fi";
    // `sh -c LSSK_LIGHT_SIGN sh <lssk> <seed> <msg>`: a Light-tier key file in a fresh `mktemp -d`
    // directory, the seed on keygen's standard input, then `sign-key`, whose output is the script's.
    // The key file is removed and the directory with it, non-recursively: `rmdir` fails, and so
    // does the script, if keygen left anything else there.
    string constant LSSK_LIGHT_SIGN = "d=$(mktemp -d) || exit 1; k=\"$d/light.key\"; "
        "printf '%s\\n' \"$2\" | \"$1\" keygen --seed-stdin --tier light -o \"$k\" >/dev/null "
        "&& \"$1\" sign-key \"$k\" \"$3\"; s=$?; rm -f -- \"$k\"; rmdir -- \"$d\" || s=1; exit $s";

    uint256 constant SIG_LEN = 4164;

    // Signature layout (spec §11).
    uint256 constant OFF_FORS_SK = 16; //   FORS secret sk_κ       at 16 + 208κ
    uint256 constant OFF_FORS_PATH = 32; // FORS path p_κ[ℓ]       at 32 + 208κ + 16ℓ
    uint256 constant FORS_STRIDE = 208; //  (1 + a)·n = 13·16, one tree's opening
    uint256 constant OFF_COUNTER = 2720; // WOTS+C counter, u32 LE (4 B)
    uint256 constant OFF_WOTS = 2724; //    WOTS value σ_i         at 2724 + 16i
    uint256 constant OFF_AUTH = 3748; //    XMSS auth path[ℓ]      at 3748 + 16ℓ

    uint256 constant H = 26;
    uint256 constant K = 13;

    // Ceiling on the gas `verify` spends in its own call frame (vm.lastCallGas().gasTotalUsed), on
    // every known answer (testKatVectorsVerify) and every random-digest signature
    // (testFuzz_AcceptsRandomDigestUnderModelRoot). The frame figure is the verifier's alone: it is
    // the same with or without `forge test --isolate`. A gasleft() delta around the call is not: it
    // adds the CALL's account access (2,500 more when the verifier is cold, as on every call under
    // --isolate) and the caller's ABI encoding of the 4,164-byte argument (about 1.43 K here), so
    // it is only logged.
    // The work is constant (249 keccak256, 259 Keccak-f permutations). The gas depends on nothing
    // but the WOTS step counts, through the chain dispatch (the verifier's section 4): each chain
    // costs a fixed amount per step count n_i = 3 - x_i, 5 less for n_i > 0 in the last of the 4
    // unrolled chains. Those costs, fitted with zero residual over 400 random signatures (they
    // then predict 300 more and every fixture vector exactly) and extremised over every
    // step-count split with Σ n_i = 64, put the frame gas of ANY admissible signature in
    // 38,441..39,470 (the top is all x_i = 2): leanSphincs-23's range moved up 75 by the extra
    // XMSS level and the 452-byte encoding input, net of the dropped FORS key hash. Measured
    // 38,935..39,052 over the fixture, and 38,730..39,212 over 700 random digests (forge 1.5.1,
    // solc 0.8.33, via-ir). The ceiling is 200 above the worst admissible case.
    // Re-adding one of the masks the verifier's MASKING note leaves out of the hot paths costs at
    // least 1,344 (the chain-step outputs 1,344, σ_i 1,388, the 143 FORS nodes 3,015), giving at
    // least 39,785 on every signature, so any one of them fails here. If a toolchain change moves
    // the measurement, re-measure and update these numbers.
    uint256 constant VERIFY_GAS_MAX = 39_670;

    struct Vector {
        string label;
        uint256 b;
        bytes32 pkSeed;
        bytes32 pkRoot;
        bytes32 message;
        bytes sig;
        uint256 idx;
        uint256 counter;
        bytes randomizer;
        uint256[] forsIndices;
        // make_kat_fixture.py: the least counter whose codeword sum exceeds T for this signature's
        // FORS tops (testRejectsAboveTargetCounterUnderItsOwnRoot).
        uint256 aboveTargetCounter;
    }

    function setUp() public {
        verifier = new LeanSphincsSAsm();
    }

    // ------------------------------------------------------------------
    // Fixture loading
    // ------------------------------------------------------------------

    function _key(uint256 i, string memory field) internal pure returns (string memory) {
        return string.concat(".vectors[", vm.toString(i), "].", field);
    }

    function _count(string memory json) internal view returns (uint256 n) {
        while (vm.keyExistsJson(json, string.concat(".vectors[", vm.toString(n), "]"))) n++;
    }

    function _vector(string memory json, uint256 i) internal pure returns (Vector memory v) {
        v.label = vm.parseJsonString(json, _key(i, "label"));
        v.b = vm.parseJsonUint(json, _key(i, "b"));
        v.pkSeed = vm.parseJsonBytes32(json, _key(i, "pkSeed"));
        v.pkRoot = vm.parseJsonBytes32(json, _key(i, "pkRoot"));
        v.message = vm.parseJsonBytes32(json, _key(i, "message"));
        v.sig = vm.parseJsonBytes(json, _key(i, "sig"));
        v.idx = vm.parseJsonUint(json, _key(i, "idx"));
        v.counter = vm.parseJsonUint(json, _key(i, "counter"));
        v.randomizer = vm.parseJsonBytes(json, _key(i, "randomizer"));
        v.forsIndices = vm.parseJsonUintArray(json, _key(i, "fors_indices"));
        v.aboveTargetCounter = vm.parseJsonUint(json, _key(i, "above_target_counter"));
    }

    function _vectors() internal view returns (Vector[] memory vs) {
        string memory json = vm.readFile(FIXTURE);
        uint256 n = _count(json);
        assertGe(n, 6, "fixture must hold at least 6 vectors");
        vs = new Vector[](n);
        for (uint256 i = 0; i < n; i++) {
            vs[i] = _vector(json, i);
        }
    }

    function _verify(Vector memory v, bytes memory sig) internal view returns (bool) {
        return verifier.verify(v.pkSeed, v.pkRoot, v.message, sig);
    }

    /// @dev A copy of `sig` with `sig[at] ^= delta`.
    function _flipped(bytes memory sig, uint256 at, uint8 delta) internal pure returns (bytes memory t) {
        t = bytes.concat(sig);
        t[at] = bytes1(uint8(t[at]) ^ delta);
    }

    /// @dev A copy of `sig` with the counter field set to LE32(c) (spec §11).
    function _withCounter(bytes memory sig, uint256 c) internal pure returns (bytes memory t) {
        require(c < 2 ** 32, "counter is a u32");
        t = bytes.concat(sig);
        bytes memory le = _leBytes(c, 4);
        for (uint256 j = 0; j < 4; j++) {
            t[OFF_COUNTER + j] = le[j];
        }
    }

    /// @dev Flipping the first byte (top bit) or the last byte (bottom bit) of the `len`-byte field at
    ///      `off` must make every vector fail. Hitting both ends of a 16-byte value also checks that
    ///      the verifier reads the whole field: a misplaced or truncated read would miss one end.
    function _assertFieldBound(uint256 off, uint256 len, string memory what) internal view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            assertFalse(
                _verify(vs[i], _flipped(vs[i].sig, off, 0x80)), string.concat(what, ": first byte, ", vs[i].label)
            );
            assertFalse(
                _verify(vs[i], _flipped(vs[i].sig, off + len - 1, 0x01)),
                string.concat(what, ": last byte, ", vs[i].label)
            );
        }
    }

    // ------------------------------------------------------------------
    // Known answers
    // ------------------------------------------------------------------

    /// Every fixture vector verifies, within VERIFY_GAS_MAX. The gated figure is the gas spent in
    /// verify's own call frame (vm.lastCallGas), which neither the caller nor --isolate changes.
    /// The gasleft() delta around the external call is logged next to it for reference; the
    /// warm-up call keeps the cold account access out of that logged figure in the default mode
    /// (under --isolate each call is its own transaction and pays it anyway).
    function testKatVectorsVerify() public {
        Vector[] memory vs = _vectors();
        string memory json = vm.readFile(FIXTURE);
        assertEq(vm.parseJsonUint(json, ".sig_len"), SIG_LEN, "fixture sig_len");

        assertTrue(_verify(vs[0], vs[0].sig), "warm-up");
        uint256 minGas = type(uint256).max;
        uint256 maxGas;
        for (uint256 i = 0; i < vs.length; i++) {
            assertEq(vs[i].sig.length, SIG_LEN, "leanSphincs-S sig must be 4164 bytes");
            uint256 g = gasleft();
            bool ok = verifier.verify(vs[i].pkSeed, vs[i].pkRoot, vs[i].message, vs[i].sig);
            uint256 outer = g - gasleft();
            uint256 used = vm.lastCallGas().gasTotalUsed;
            assertTrue(ok, string.concat("KAT must verify: ", vs[i].label));
            emit log_named_uint(string.concat("leanSphincs-S verify gas, call frame [", vs[i].label, "]"), used);
            emit log_named_uint(string.concat("  gasleft() delta around the call [", vs[i].label, "]"), outer);
            if (used < minGas) minGas = used;
            if (used > maxGas) maxGas = used;
        }
        emit log_named_uint("leanSphincs-S verify gas, call frame, min", minGas);
        emit log_named_uint("leanSphincs-S verify gas, call frame, max", maxGas);
        assertLe(maxGas, VERIFY_GAS_MAX, "verify gas ceiling (call frame)");
    }

    /// The fixture's own fields agree with its signature bytes and with spec §5 / §9, recomputed in
    /// plain Solidity (independently of the Yul verifier): ρ and the counter are the bytes at their
    /// §11 offsets, the digest D = keccak256(P ‖ address(MSG) ‖ m ‖ ρ) splits into the recorded leaf
    /// index and FORS indices, and the leaf lies in the kept subtree that P selects. Catches a
    /// hand-edited or mislabelled fixture.
    function testKatFixtureFieldsMatchSpec() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            assertEq(v.sig.length, SIG_LEN, "sig length");

            bytes16 rho = bytes16(_slice16(v.sig, 0));
            assertEq(v.randomizer, abi.encodePacked(rho), "randomizer = sig[0:16]");
            uint256 ctr = uint8(v.sig[OFF_COUNTER]) | uint256(uint8(v.sig[OFF_COUNTER + 1])) << 8
                | uint256(uint8(v.sig[OFF_COUNTER + 2])) << 16 | uint256(uint8(v.sig[OFF_COUNTER + 3])) << 24;
            assertEq(ctr, v.counter, "counter = LE32(sig[2720:2724])");

            bytes32 d = keccak256(abi.encodePacked(bytes16(v.pkSeed), _adr(12, 0, 0, 0), v.message, rho));
            assertEq(_le64(d, 3) & (2 ** H - 1), v.idx, "idx = word_3 & (2^26 - 1)");
            assertEq(v.forsIndices.length, K, "13 FORS indices");
            for (uint256 k = 0; k < K; k++) {
                assertEq((_le64(d, k / 5) >> (12 * (k % 5))) & 0xFFF, v.forsIndices[k], "u_k");
            }

            // §9: the kept subtree is s = LE64(P[0:8]) mod 2^(26-b), so idx >> b == s.
            uint256 s = _le64(v.pkSeed, 0) & (2 ** (H - v.b) - 1);
            assertEq(v.idx >> v.b, s, "idx lies in the kept subtree");
        }
    }

    /// The merged encoding's one ordering constraint (the verifier's MASKING note): when bit 11 of
    /// u_12 is set, tree 12's level-11 node is the right top, and its 32-byte store spills 16 stray
    /// bytes onto 0x228..0x237, the 4 bytes after the tops where the counter goes. The counter is
    /// copied there after the FORS loop, so it overwrites the start of the spill, and the ENC hash
    /// stops at 0x22B. A verifier that copied the counter before the loop passes only the vectors
    /// with that bit clear (checked by mutation), so the fixture must hold vectors with both values
    /// of it.
    function testFixtureCoversTree12TopSpill() public view {
        checkCoversU12Bit11(_vectors());
    }

    /// @dev The coverage guard of testFixtureCoversTree12TopSpill: both values of bit 11 of u_12.
    ///      Public so testFixtureCoverageGuardsAreTwoSided can call it and expect a revert.
    function checkCoversU12Bit11(Vector[] memory vs) public pure {
        uint256 spill;
        for (uint256 i = 0; i < vs.length; i++) {
            if ((vs[i].forsIndices[K - 1] >> 11) & 1 == 1) spill++;
        }
        assertGt(spill, 0, "fixture needs a vector with bit 11 of u_12 set (tree 12's top store spills)");
        assertLt(spill, vs.length, "fixture needs a vector with bit 11 of u_12 clear");
    }

    // ------------------------------------------------------------------
    // Rejection: message and key
    // ------------------------------------------------------------------

    function testRejectsFlippedMessageBit() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            for (uint256 bit = 0; bit < 256; bit += 85) {
                bytes32 m = v.message ^ bytes32(uint256(1) << bit);
                assertFalse(verifier.verify(v.pkSeed, v.pkRoot, m, v.sig), string.concat("message flip, ", v.label));
            }
        }
    }

    /// A different (canonical) P changes every tweakable hash, so the signature cannot verify.
    function testRejectsWrongPkSeed() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            bytes32 lowBit = bytes32(uint256(1) << 128); // lowest bit of P (still canonical)
            bytes32 topBit = bytes32(uint256(1) << 255);
            assertFalse(verifier.verify(v.pkSeed ^ lowBit, v.pkRoot, v.message, v.sig), "P low bit");
            assertFalse(verifier.verify(v.pkSeed ^ topBit, v.pkRoot, v.message, v.sig), "P top bit");
        }
    }

    function testRejectsWrongPkRoot() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            assertFalse(
                verifier.verify(v.pkSeed, v.pkRoot ^ bytes32(uint256(1) << 128), v.message, v.sig), "root low bit"
            );
            assertFalse(
                verifier.verify(v.pkSeed, v.pkRoot ^ bytes32(uint256(1) << 255), v.message, v.sig), "root top bit"
            );
            // Another vector's key, and the other vector's root with this P.
            Vector memory o = vs[(i + 1) % vs.length];
            assertFalse(verifier.verify(o.pkSeed, o.pkRoot, v.message, v.sig), "another key");
            assertFalse(verifier.verify(v.pkSeed, o.pkRoot, v.message, v.sig), "another root");
        }
    }

    // ------------------------------------------------------------------
    // Rejection: one tampered byte per signature region (spec §11)
    // ------------------------------------------------------------------

    function testRejectsTamperedRandomizer() public view {
        _assertFieldBound(0, 16, "rho");
    }

    function testRejectsTamperedForsSecretTree0() public view {
        _assertFieldBound(OFF_FORS_SK, 16, "FORS sk_0");
    }

    function testRejectsTamperedForsSecretTree12() public view {
        _assertFieldBound(OFF_FORS_SK + FORS_STRIDE * 12, 16, "FORS sk_12");
    }

    /// Level 0 of every one of the 13 trees.
    function testRejectsTamperedForsPathLevel0() public view {
        for (uint256 k = 0; k < K; k++) {
            _assertFieldBound(OFF_FORS_PATH + FORS_STRIDE * k, 16, string.concat("FORS p_", vm.toString(k), "[0]"));
        }
    }

    /// Level 11 (the sibling top that goes straight into the WOTS+C encoding) of every tree.
    function testRejectsTamperedForsPathLevel11() public view {
        for (uint256 k = 0; k < K; k++) {
            _assertFieldBound(
                OFF_FORS_PATH + FORS_STRIDE * k + 16 * 11, 16, string.concat("FORS p_", vm.toString(k), "[11]")
            );
        }
    }

    /// Each of the 4 counter bytes: the encoding changes, which is (almost always) inadmissible and
    /// otherwise moves every chain's start position.
    function testRejectsTamperedCounter() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            for (uint256 j = 0; j < 4; j++) {
                assertFalse(
                    _verify(vs[i], _flipped(vs[i].sig, OFF_COUNTER + j, 0x01)), string.concat("counter, ", vs[i].label)
                );
                assertFalse(
                    _verify(vs[i], _flipped(vs[i].sig, OFF_COUNTER + j, 0x80)), string.concat("counter, ", vs[i].label)
                );
            }
        }
    }

    function testRejectsTamperedWotsValue0() public view {
        _assertFieldBound(OFF_WOTS, 16, "WOTS sigma_0");
    }

    function testRejectsTamperedWotsValue63() public view {
        _assertFieldBound(OFF_WOTS + 16 * 63, 16, "WOTS sigma_63");
    }

    function testRejectsTamperedAuthPathLevel0() public view {
        _assertFieldBound(OFF_AUTH, 16, "auth path[0]");
    }

    /// The last 16 signature bytes, the auth-path level leanSphincs-23 does not have. The verifier
    /// calldatacopies exactly these 16 bytes; a 32-byte read here would be the only one to run past
    /// the signature (see testIgnoresDirtyCalldataPadding).
    function testRejectsTamperedAuthPathLevel25() public view {
        _assertFieldBound(OFF_AUTH + 16 * 25, 16, "auth path[25]");
        assertEq(OFF_AUTH + 16 * 26, SIG_LEN, "auth path[25] ends the signature");
    }

    /// Any nonzero xor at any signature byte of any vector is rejected.
    /// forge-config: default.fuzz.runs = 512
    function testFuzz_RejectsTamperedByte(uint256 vecSel, uint256 at, uint8 delta) public view {
        string memory json = vm.readFile(FIXTURE);
        Vector memory v = _vector(json, vecSel % _count(json));
        at = bound(at, 0, SIG_LEN - 1);
        delta = uint8(bound(delta, 1, 255));
        assertFalse(_verify(v, _flipped(v.sig, at, delta)), "tampered signature must not verify");
    }

    // ------------------------------------------------------------------
    // Against the spec model: the WOTS+C target-sum check is load-bearing
    // ------------------------------------------------------------------

    /// The plain-Solidity spec model (bottom of this file) reaches every fixture root, with an
    /// admissible encoding.
    function testSpecModelReachesKatRoots() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            (bytes32 root, uint256 sum) = _modelRoot(vs[i].pkSeed, vs[i].message, vs[i].sig);
            assertEq(sum, 128, string.concat("model: codeword sum, ", vs[i].label));
            assertEq(root, vs[i].pkRoot, string.concat("model: root, ", vs[i].label));
        }
    }

    /// A changed counter gives an inadmissible encoding (Σ x_i ≠ 128). Presented with the root its
    /// own (shifted) chains fold to, everything but the target-sum check matches, so only that check
    /// can reject it. Without it, chains could be advanced from a known signature: with x'_i ≥ x_i
    /// for every i, σ'_i = chain(σ_i, x_i → x'_i) reaches the same chain ends.
    function testRejectsInadmissibleCounterUnderItsOwnRoot() public view {
        Vector[] memory vs = _vectors();
        uint256 checked;
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            for (uint8 delta = 1; delta <= 4; delta++) {
                bytes memory sig = _flipped(v.sig, OFF_COUNTER, delta);
                (bytes32 root, uint256 sum) = _modelRoot(v.pkSeed, v.message, sig);
                if (sum == 128) continue; // admissible by chance (p ≈ 6.8e-5): not this test's case
                assertFalse(verifier.verify(v.pkSeed, root, v.message, sig), string.concat("inadmissible, ", v.label));
                checked++;
            }
        }
        assertGe(checked, 4 * vs.length - 1, "inadmissible cases exercised");
    }

    /// The other side of the target-sum check: an encoding ABOVE T. Each vector's
    /// `above_target_counter` (the least counter whose codeword sum exceeds 128 for that
    /// signature's FORS tops) goes into the counter field, and the signature is presented under the
    /// root its own chains fold to. Accepting Σ ≥ T is the forgery above in general form: any
    /// counter whose codeword dominates the signed one lets anyone advance the chains. The changed
    /// counters above all land below T (P[Σ > 128] ≈ 1.2e-4 per counter, 1 in ~8,250), so a
    /// verifier that rejected only Σ < T would pass them and the fuzz tests; hence pinned counters.
    function testRejectsAboveTargetCounterUnderItsOwnRoot() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            bytes memory sig = _withCounter(v.sig, v.aboveTargetCounter);
            (bytes32 root, uint256 sum) = _modelRoot(v.pkSeed, v.message, sig);
            assertGt(sum, 128, string.concat("above_target_counter: codeword sum > T, ", v.label));
            assertFalse(verifier.verify(v.pkSeed, root, v.message, sig), string.concat("sum > T, ", v.label));
        }
    }

    /// Fields that do not feed the encoding (WOTS values, auth path) can be changed freely: the
    /// result is a signature that is valid under the root the spec model computes for it. Shows
    /// the verifier's `false` above comes from the target-sum check alone, and that it accepts
    /// signatures no signer produced exactly when the spec says so.
    function testAcceptsSyntheticSignatureUnderItsOwnRoot() public view {
        Vector[] memory vs = _vectors();
        uint256[4] memory offs = [OFF_WOTS, OFF_WOTS + 16 * 63 + 15, OFF_AUTH, OFF_AUTH + 16 * 25 + 15];
        for (uint256 i = 0; i < vs.length; i++) {
            for (uint256 j = 0; j < offs.length; j++) {
                bytes memory sig = _flipped(vs[i].sig, offs[j], 0x5a);
                (bytes32 root, uint256 sum) = _modelRoot(vs[i].pkSeed, vs[i].message, sig);
                assertEq(sum, 128, "encoding unchanged");
                assertTrue(root != vs[i].pkRoot, "root moved");
                assertTrue(
                    verifier.verify(vs[i].pkSeed, root, vs[i].message, sig), string.concat("synthetic, ", vs[i].label)
                );
            }
        }
    }

    /// The verifier equals the spec model on arbitrary single-byte tampering, judged under the root
    /// the model computes for the tampered signature: true iff the encoding is admissible.
    /// What this compares depends on the byte. A WOTS-value or auth-path flip keeps the fixture's
    /// digest and codeword, so both sides accept and the chains and the XMSS fold are compared,
    /// but only at the six fixture leaf indices. A ρ, FORS or counter flip changes the encoding's
    /// input (the FORS tops or the counter; a ρ flip also the leaf index and FORS indices), so the
    /// encoding is inadmissible except with probability ≈ 6.8e-5 and both sides stop at the
    /// target-sum check: only that 1-bit verdict is compared. Acceptance at fresh digests is
    /// testFuzz_AcceptsRandomDigestUnderModelRoot.
    /// forge-config: default.fuzz.runs = 256
    function testFuzz_VerifierMatchesSpecModel(uint256 vecSel, uint256 at, uint8 delta) public view {
        string memory json = vm.readFile(FIXTURE);
        Vector memory v = _vector(json, vecSel % _count(json));
        bytes memory sig = _flipped(v.sig, bound(at, 0, SIG_LEN - 1), uint8(bound(delta, 1, 255)));
        (bytes32 root, uint256 sum) = _modelRoot(v.pkSeed, v.message, sig);
        assertEq(verifier.verify(v.pkSeed, root, v.message, sig), sum == 128, "verifier != spec model");
    }

    /// Acceptance at digests no fixture vector has. P, m and the whole 4,164-byte signature are
    /// random, so ρ, and with it the leaf index and all 13 FORS indices, is uniform, as are the
    /// FORS openings, WOTS values and auth path. The counter is then ground until the encoding of
    /// the model's FORS tops is admissible, and the signature is judged under the root the spec
    /// model folds it to. The verifier must accept it, which checks every FORS climb (at 13 fresh
    /// indices), the 416 bytes of tops and the counter in the merged encoding, all 64 chains (at a
    /// fresh leaf index and codeword) and all 26 XMSS levels (at a fresh leaf index) against the
    /// model, within VERIFY_GAS_MAX in its own frame. It must reject the same signature under that
    /// root with its lowest bit flipped (the root mismatch path, which no fixture-based model
    /// comparison reaches).
    /// forge-config: default.fuzz.runs = 256
    function testFuzz_AcceptsRandomDigestUnderModelRoot(bytes32 pSeed, bytes32 m, bytes32 bodySeed) public view {
        bytes32 pkSeed = pSeed & bytes32(~uint256(type(uint128).max)); // canonical P ‖ 0^16
        bytes memory sig = _randomSig(bodySeed);

        bytes16 p = bytes16(pkSeed);
        bytes32 d = keccak256(abi.encodePacked(p, _adr(12, 0, 0, 0), m, _n(sig, 0)));
        uint256 idx = _le64(d, 3) & (2 ** H - 1);
        sig = _withCounter(sig, _grindCounter(p, idx, _modelForsTops(p, d, idx, sig)));

        (bytes32 root, uint256 sum) = _modelRoot(pkSeed, m, sig);
        assertEq(sum, 128, "model: ground counter is admissible");
        bool ok = verifier.verify(pkSeed, root, m, sig);
        uint256 used = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok, "random digest: verifier must accept under the model's root");
        assertLe(used, VERIFY_GAS_MAX, "verify gas ceiling (call frame), random digest");
        assertFalse(verifier.verify(pkSeed, root ^ bytes32(uint256(1) << 128), m, sig), "random digest: wrong root");
    }

    /// The model's address encoding against spec §3's upstream test vector.
    function testSpecModelAddressVector() public pure {
        bytes16 expected = hex"efcdab89563412aa0000000000000000";
        assertEq(_adr(10, 5, 0x123456, 0x89abcdef), expected);
    }

    // ------------------------------------------------------------------
    // Malformed input (spec §12): Error(string) reverts
    // ------------------------------------------------------------------

    function testRevertsOnBadSigLength() public {
        Vector[] memory vs = _vectors();
        Vector memory v = vs[0];

        bytes memory shortSig = new bytes(SIG_LEN - 1);
        for (uint256 j = 0; j < shortSig.length; j++) {
            shortSig[j] = v.sig[j];
        }
        bytes memory longSig = bytes.concat(v.sig, hex"00");

        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot, v.message, "");
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot, v.message, shortSig);
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot, v.message, longSig);
    }

    /// A key word with a nonzero low half is not a key (spec §12: pkSeed = P ‖ 0^16,
    /// pkRoot = root ‖ 0^16), even with an otherwise valid signature.
    function testRevertsOnNonCanonicalPkSeed() public {
        Vector[] memory vs = _vectors();
        Vector memory v = vs[0];
        uint256[3] memory bits = [uint256(0), 64, 127]; // low half: bottom, middle, top
        for (uint256 j = 0; j < bits.length; j++) {
            vm.expectRevert(bytes("Invalid public key"));
            verifier.verify(v.pkSeed | bytes32(uint256(1) << bits[j]), v.pkRoot, v.message, v.sig);
        }
    }

    function testRevertsOnNonCanonicalPkRoot() public {
        Vector[] memory vs = _vectors();
        Vector memory v = vs[0];
        uint256[3] memory bits = [uint256(0), 64, 127]; // low half: bottom, middle, top
        for (uint256 j = 0; j < bits.length; j++) {
            vm.expectRevert(bytes("Invalid public key"));
            verifier.verify(v.pkSeed, v.pkRoot | bytes32(uint256(1) << bits[j]), v.message, v.sig);
        }
    }

    /// Any nonzero low half reverts, in pkSeed, pkRoot or both, on any vector. The fixed cases
    /// above try a few bits; a check that looked only at those would still pass them.
    /// forge-config: default.fuzz.runs = 256
    function testFuzz_RevertsOnNonCanonicalKey(uint256 vecSel, uint256 low, uint8 which) public {
        string memory json = vm.readFile(FIXTURE);
        Vector memory v = _vector(json, vecSel % _count(json));
        bytes32 dirt = bytes32(bound(low, 1, type(uint128).max));
        which %= 3; // 0: pkSeed, 1: pkRoot, 2: both
        bytes32 pkSeed = which == 1 ? v.pkSeed : v.pkSeed | dirt;
        bytes32 pkRoot = which == 0 ? v.pkRoot : v.pkRoot | dirt;
        vm.expectRevert(bytes("Invalid public key"));
        verifier.verify(pkSeed, pkRoot, v.message, v.sig);
    }

    /// Zero key words are canonical (spec §12) and are what an uninitialised storage slot holds,
    /// so they get no special treatment: a valid signature under another key is just `false`. A
    /// verifier that accepted anything for P = 0 or root = 0 would pass every other test here.
    function testRejectsZeroKeyWords() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            assertFalse(verifier.verify(v.pkSeed, bytes32(0), v.message, v.sig), string.concat("root 0, ", v.label));
            assertFalse(verifier.verify(bytes32(0), v.pkRoot, v.message, v.sig), string.concat("P 0, ", v.label));
            assertFalse(verifier.verify(bytes32(0), bytes32(0), v.message, v.sig), string.concat("both 0, ", v.label));
        }
    }

    /// Spec §12 checks the length first when both are wrong. The verifier, the Rust `lssk verify`
    /// and the Python mirror all do; this pins that order.
    function testLengthCheckedBeforeKey() public {
        Vector[] memory vs = _vectors();
        Vector memory v = vs[0];
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed | bytes32(uint256(1)), v.pkRoot, v.message, "");
        bytes memory longSig = bytes.concat(v.sig, hex"00");
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot | bytes32(uint256(1)), v.message, longSig);
    }

    /// The ABI pads the 4,164-byte signature with 28 zero bytes, and the verifier never reads them:
    /// every sibling is calldatacopy'd, exactly 16 bytes. Of the last auth-path node (path[25],
    /// signature bytes 4148..4163), the 16 bytes after it are padding and beyond calldata; a
    /// 32-byte read of it would put them in the R slot, into the hash input, exactly when path[25]
    /// is the LEFT child, i.e. bit 25 of idx is 1 (as the right child they would land past the
    /// input). So every vector is run, with dirty padding alone and with a trailing all-ones word
    /// too, and the fixture must hold a vector of that kind, and one of the other kind too
    /// (testFixtureCoverageGuardsAreTwoSided says why).
    function testIgnoresDirtyCalldataPadding() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            bytes memory cd = abi.encodeCall(LeanSphincsSAsm.verify, (v.pkSeed, v.pkRoot, v.message, v.sig));
            // selector(4) ‖ pkSeed ‖ pkRoot ‖ message ‖ offset ‖ length ‖ sig(4164) ‖ 28 zero bytes.
            uint256 sigEnd = 4 + 5 * 32 + SIG_LEN;
            assertEq(cd.length, sigEnd + 28, "abi layout");
            for (uint256 j = sigEnd; j < cd.length; j++) {
                cd[j] = 0xff;
            }
            _assertCallAccepts(cd, string.concat("dirty padding, ", v.label));
            _assertCallAccepts(
                bytes.concat(cd, bytes32(type(uint256).max)), string.concat("dirty padding + trailing word, ", v.label)
            );
        }
        checkCoversIdxBit25(vs);
    }

    /// @dev The coverage guard of testIgnoresDirtyCalldataPadding: both values of bit 25 of idx.
    ///      Public so testFixtureCoverageGuardsAreTwoSided can call it and expect a revert.
    function checkCoversIdxBit25(Vector[] memory vs) public pure {
        uint256 left;
        for (uint256 i = 0; i < vs.length; i++) {
            if ((vs[i].idx >> 25) & 1 == 1) left++;
        }
        assertGt(left, 0, "fixture needs a vector whose path[25] is the left child (bit 25 of idx set)");
        assertLt(left, vs.length, "fixture needs a vector whose path[25] is the right child (bit 25 of idx clear)");
    }

    function _assertCallAccepts(bytes memory cd, string memory what) internal view {
        (bool ok, bytes memory ret) = address(verifier).staticcall(cd);
        assertTrue(ok, string.concat("call succeeds: ", what));
        assertTrue(abi.decode(ret, (bool)), string.concat("must not affect a valid signature: ", what));
    }

    /// The two coverage guards (checkCoversIdxBit25, checkCoversU12Bit11) must each require BOTH
    /// values of their bit: each bit picks between two placements, and a fault in one shows only on
    /// the vectors that take it. At ℓ = 25, copying path[25] before storing the node fails only the
    /// vectors with bit 25 clear (the node is the left child, and its 32-byte store overwrites the
    /// sibling just copied). Against a fixture holding only bit-25-set vectors, that fault passes
    /// every deterministic test and is caught only by the random-digest fuzz test and by
    /// testVerifyFFI_Rust, whose fresh signature happens to have bit 25 clear (checked by mutation).
    /// So each guard must pass the real fixture and reject two one-sided copies of it, one per
    /// value of its bit, so that a regenerated fixture cannot lose that coverage silently (the
    /// guards are pure counting loops: their only revert is a failed assertion).
    function testFixtureCoverageGuardsAreTwoSided() public {
        Vector[] memory vs = _vectors();
        this.checkCoversIdxBit25(vs);
        this.checkCoversU12Bit11(vs);
        for (uint256 value = 0; value < 2; value++) {
            vm.expectRevert();
            this.checkCoversIdxBit25(_oneSided(vs, true, value));
            vm.expectRevert();
            this.checkCoversU12Bit11(_oneSided(vs, false, value));
        }
    }

    /// @dev A copy of the fixture as large as `vs` that holds only its vectors whose bit 25 of idx
    ///      (`idxBit25`) or bit 11 of u_12 (otherwise) equals `value`, repeated in turn.
    function _oneSided(Vector[] memory vs, bool idxBit25, uint256 value) internal pure returns (Vector[] memory out) {
        Vector[] memory kept = new Vector[](vs.length);
        uint256 n;
        for (uint256 i = 0; i < vs.length; i++) {
            uint256 bit = idxBit25 ? (vs[i].idx >> 25) & 1 : (vs[i].forsIndices[K - 1] >> 11) & 1;
            if (bit == value) kept[n++] = vs[i];
        }
        assertGt(n, 0, "the fixture holds both values of the bit");
        out = new Vector[](vs.length);
        for (uint256 i = 0; i < vs.length; i++) {
            out[i] = kept[i % n];
        }
    }

    // ------------------------------------------------------------------
    // FFI: fresh signature from the Rust CLI
    // ------------------------------------------------------------------

    /// Signs a fresh message with `lssk sign <seed> 8 <msg>` (kept subtree b = 8, ~50 ms) and
    /// verifies it. Build the binary with:
    ///     (cd signers/leansphincs-s-keccak && cargo build --release)
    function testVerifyFFI_Rust() public {
        _requireLssk();

        bytes32 seed = keccak256("leanSphincs-S-keccak FFI seed");
        bytes32 message = keccak256("leanSphincs-S-keccak FFI message");

        string[] memory inputs = new string[](5);
        inputs[0] = LSSK;
        inputs[1] = "sign";
        inputs[2] = vm.toString(seed);
        inputs[3] = "8";
        inputs[4] = vm.toString(message);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
        assertEq(sig.length, SIG_LEN, "leanSphincs-S sig must be 4164 bytes");

        bool ok = verifier.verify(pkSeed, pkRoot, message, sig);
        uint256 used = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok, "Rust CLI signature must verify");
        emit log_named_uint("leanSphincs-S verify gas, call frame (rust sig)", used);
        assertLe(used, VERIFY_GAS_MAX, "verify gas ceiling (call frame), rust sig");
        assertFalse(verifier.verify(pkSeed, pkRoot, message ^ bytes32(uint256(1)), sig), "wrong message");
    }

    /// The tiered signer (spec §14): `lssk keygen --seed-stdin --tier light` (b = 13, a 16 KiB
    /// node cache, about 1.85e6 keccak256 calls) writes a key file into a `mktemp -d` directory,
    /// `lssk sign-key` signs from it, and the key file is removed, all in one `sh -c`
    /// (LSSK_LIGHT_SIGN). The output must verify and be byte-identical to the stateless
    /// `lssk sign <seed> 13 <msg>`: the key file changes where the auth path comes from, nothing
    /// in the signature.
    function testVerifyFFI_RustLightTierKeyFile() public {
        _requireLssk();

        bytes32 seed = keccak256("leanSphincs-S-keccak FFI light-tier seed");
        bytes32 message = keccak256("leanSphincs-S-keccak FFI light-tier message");

        string[] memory tiered = new string[](7);
        tiered[0] = "sh";
        tiered[1] = "-c";
        tiered[2] = LSSK_LIGHT_SIGN;
        tiered[3] = "sh";
        tiered[4] = LSSK;
        tiered[5] = vm.toString(seed);
        tiered[6] = vm.toString(message);
        Vm.FfiResult memory run = vm.tryFfi(tiered);
        assertEq(run.exitCode, 0, string.concat("lssk keygen --tier light, sign-key: ", string(run.stderr)));

        string[] memory stateless = new string[](5);
        stateless[0] = LSSK;
        stateless[1] = "sign";
        stateless[2] = vm.toString(seed);
        stateless[3] = "13";
        stateless[4] = vm.toString(message);
        assertEq(run.stdout, vm.ffi(stateless), "sign-key must print what `lssk sign <seed> 13 <msg>` prints");

        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(run.stdout, (bytes32, bytes32, bytes));
        assertEq(sig.length, SIG_LEN, "leanSphincs-S sig must be 4164 bytes");

        bool ok = verifier.verify(pkSeed, pkRoot, message, sig);
        uint256 used = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok, "Light-tier key-file signature must verify");
        emit log_named_uint("leanSphincs-S verify gas, call frame (light-tier key-file sig)", used);
        assertLe(used, VERIFY_GAS_MAX, "verify gas ceiling (call frame), light-tier key-file sig");
        assertFalse(verifier.verify(pkSeed, pkRoot, message ^ bytes32(uint256(1)), sig), "wrong message");
    }

    /// The Rust CLI must be built and not older than any crate source: the binary is gitignored,
    /// and a stale one signs under the old scheme with no error (the repo's stale-binary rule,
    /// f5c09ae), so a stale binary fails the test. A missing one skips it (reported as skipped,
    /// not passed), except under CI (`CI` set), where the solidity job builds it.
    function _requireLssk() internal {
        string[] memory probe = new string[](3);
        probe[0] = "sh";
        probe[1] = "-c";
        probe[2] = LSSK_PROBE;
        bytes memory state = vm.ffi(probe);
        string memory build = " (cd signers/leansphincs-s-keccak && cargo build --release)";
        if (keccak256(state) == keccak256("missing")) {
            assertEq(vm.envOr("CI", string("")), "", string.concat(LSSK, " is not built under CI:", build));
            vm.skip(true, string.concat(LSSK, " not built:", build));
        }
        assertEq(string(state), "fresh", string.concat(LSSK, " is older than the crate sources:", build));
    }

    // ------------------------------------------------------------------
    // Helpers (spec byte orders)
    // ------------------------------------------------------------------

    /// 16 bytes of `b` at `off`, high-aligned in a word.
    function _slice16(bytes memory b, uint256 off) internal pure returns (bytes32 w) {
        assembly ("memory-safe") {
            w := and(mload(add(add(b, 0x20), off)), not(sub(shl(128, 1), 1)))
        }
    }

    /// u64 little endian of bytes 8w..8w+8 of the word `d` (byte 0 = most significant).
    function _le64(bytes32 d, uint256 w) internal pure returns (uint256 x) {
        for (uint256 j = 0; j < 8; j++) {
            x |= uint256(uint8(d[8 * w + j])) << (8 * j);
        }
    }

    function _leBytes(uint256 x, uint256 len) internal pure returns (bytes memory b) {
        b = new bytes(len);
        for (uint256 j = 0; j < len; j++) {
            b[j] = bytes32(x)[31 - j];
        }
    }

    /// SIG_LEN bytes, word j/32 = keccak256(abi.encode(seed, j)).
    function _randomSig(bytes32 seed) internal pure returns (bytes memory sig) {
        sig = new bytes(SIG_LEN);
        assembly ("memory-safe") {
            // The last store runs 28 bytes past the data, inside the word-rounded allocation.
            for { let j := 0 } lt(j, SIG_LEN) { j := add(j, 0x20) } {
                mstore(0x00, seed)
                mstore(0x20, j)
                mstore(add(add(sig, 0x20), j), keccak256(0x00, 0x40))
            }
        }
    }

    /// The least counter whose encoding d = Th(P, ENC(0, idx), tops ‖ LE32(c)) has digit sum
    /// T = 128 (the merged encoding, spec §6: 32 + 416 + 4 = 452 input bytes). Only a search: the
    /// digit sum here is popcount(d) + popcount(d & 0xAA…AA) (a 2-bit digit is its low bit plus
    /// twice its high bit), and callers check the spec model's own sum.
    function _grindCounter(bytes16 p, uint256 idx, bytes memory tops) internal pure returns (uint256 c) {
        require(tops.length == 416, "26 FORS tops");
        bytes memory buf = abi.encodePacked(p, _adr(4, 0, 0, idx), tops, bytes4(0)); // 452 bytes
        bool found;
        assembly ("memory-safe") {
            function popcount128(x) -> r {
                x := sub(x, and(shr(1, x), 0x55555555555555555555555555555555))
                x := add(and(x, 0x33333333333333333333333333333333), and(shr(2, x), 0x33333333333333333333333333333333))
                x := and(add(x, shr(4, x)), 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F)
                r := and(shr(120, mul(x, 0x01010101010101010101010101010101)), 0xFF)
            }
            let ctr := add(buf, 0x1E0) // buf bytes 448..451: LE32(c)
            for {} lt(c, 0x100000000) { c := add(c, 1) } {
                mstore8(ctr, c)
                mstore8(add(ctr, 1), shr(8, c))
                mstore8(add(ctr, 2), shr(16, c))
                mstore8(add(ctr, 3), shr(24, c))
                let x := shr(128, keccak256(add(buf, 0x20), 452))
                if eq(add(popcount128(x), popcount128(and(x, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA))), 128) {
                    found := 1
                    break
                }
            }
        }
        require(found, "no admissible counter below 2^32");
    }

    // ------------------------------------------------------------------
    // Spec model: verification in plain, byte-oriented Solidity (spec §2-§8), independent of the
    // Yul verifier's word packing. It returns the root a signature folds to and the codeword sum,
    // WITHOUT the target-sum check, so the tests above can build inputs on which only that check
    // decides.
    // ------------------------------------------------------------------

    /// §3: LE32(lo) ‖ LE24(hi) ‖ (t | step << 5) ‖ 0^8.
    function _adr(uint256 t, uint256 step, uint256 hi, uint256 lo) internal pure returns (bytes16) {
        require(t < 32 && step < 8 && hi < 2 ** 24 && lo < 2 ** 32, "address field range");
        return bytes16(abi.encodePacked(_leBytes(lo, 4), _leBytes(hi, 3), _leBytes(t | (step << 5), 1), bytes8(0)));
    }

    /// §2: Th(P, tw, M) = keccak256(P ‖ address(tw) ‖ M)[0:16].
    function _th(bytes16 p, bytes16 tw, bytes memory payload) internal pure returns (bytes16) {
        return bytes16(keccak256(abi.encodePacked(p, tw, payload)));
    }

    /// §4: pos(κ, ℓ, j) = κ + 32ℓ + 512j.
    function _pos(uint256 kappa, uint256 level, uint256 j) internal pure returns (uint256) {
        return kappa + 32 * level + 512 * j;
    }

    function _n(bytes memory sig, uint256 off) internal pure returns (bytes16) {
        return bytes16(_slice16(sig, off));
    }

    function _modelRoot(bytes32 pkSeed, bytes32 m, bytes memory sig) internal pure returns (bytes32 root, uint256 sum) {
        bytes16 p = bytes16(pkSeed); // pkSeed = P ‖ 0^16 (spec §12)
        // §5: D = ThFull(P, address(MSG), m ‖ ρ); idx from word 3, u_κ from word ⌊κ/5⌋.
        bytes32 d = keccak256(abi.encodePacked(p, _adr(12, 0, 0, 0), m, _n(sig, 0)));
        uint256 idx = _le64(d, 3) & (2 ** H - 1);
        bytes memory tops = _modelForsTops(p, d, idx, sig);
        (bytes16 leaf, uint256 s) = _modelWotsLeaf(p, idx, tops, sig);
        root = bytes32(_modelXmssRoot(p, idx, leaf, sig));
        sum = s;
    }

    /// §7: recover the two level-11 nodes of each tree, in the order top_{0,0} ‖ top_{0,1} ‖ … ‖
    /// top_{12,1} (416 bytes). No hash folds them: they are the encoding's input as they are.
    function _modelForsTops(bytes16 p, bytes32 d, uint256 idx, bytes memory sig)
        internal
        pure
        returns (bytes memory tops)
    {
        for (uint256 k = 0; k < K; k++) {
            uint256 u = (_le64(d, k / 5) >> (12 * (k % 5))) & 0xFFF;
            uint256 off = OFF_FORS_SK + FORS_STRIDE * k;
            bytes16 node = _th(p, _adr(9, 0, _pos(k, 0, u), idx), abi.encodePacked(_n(sig, off)));
            for (uint256 l = 0; l < 11; l++) {
                bytes16 sib = _n(sig, off + 16 + 16 * l);
                bytes memory lr = (u >> l) & 1 == 0 ? abi.encodePacked(node, sib) : abi.encodePacked(sib, node);
                node = _th(p, _adr(10, 0, _pos(k, l + 1, u >> (l + 1)), idx), lr);
            }
            bytes16 p11 = _n(sig, off + 16 + 16 * 11);
            tops = (u >> 11) & 1 == 0 ? abi.encodePacked(tops, node, p11) : abi.encodePacked(tops, p11, node);
        }
    }

    /// §6: encoding d = Th(ENC, tops ‖ LE32(c)), x_i = 2-bit digit i of d as u128 LE; chains from
    /// x_i to 3 (the step onto position `to` has step field to - 1); WOTS leaf over the 64 ends.
    function _modelWotsLeaf(bytes16 p, uint256 idx, bytes memory tops, bytes memory sig)
        internal
        pure
        returns (bytes16 leaf, uint256 sum)
    {
        uint256 c;
        for (uint256 j = 0; j < 4; j++) {
            c |= uint256(uint8(sig[OFF_COUNTER + j])) << (8 * j);
        }
        bytes16 enc = _th(p, _adr(4, 0, 0, idx), abi.encodePacked(tops, _leBytes(c, 4)));
        uint256 x;
        for (uint256 j = 0; j < 16; j++) {
            x |= uint256(uint8(enc[j])) << (8 * j);
        }
        bytes memory ends;
        for (uint256 i = 0; i < 64; i++) {
            uint256 xi = (x >> (2 * i)) & 3;
            sum += xi;
            bytes16 val = _n(sig, OFF_WOTS + 16 * i);
            for (uint256 pos = xi; pos < 3; pos++) {
                val = _th(p, _adr(1, pos, i, idx), abi.encodePacked(val));
            }
            ends = abi.encodePacked(ends, val);
        }
        leaf = _th(p, _adr(2, 0, 0, idx), ends);
    }

    /// §8: fold the leaf up the 26 auth-path nodes.
    function _modelXmssRoot(bytes16 p, uint256 idx, bytes16 leaf, bytes memory sig)
        internal
        pure
        returns (bytes16 cur)
    {
        cur = leaf;
        for (uint256 l = 0; l < H; l++) {
            bytes16 sib = _n(sig, OFF_AUTH + 16 * l);
            bytes memory lr = (idx >> l) & 1 == 0 ? abi.encodePacked(cur, sib) : abi.encodePacked(sib, cur);
            cur = _th(p, _adr(3, 0, l + 1, idx >> (l + 1)), lr);
        }
    }
}
