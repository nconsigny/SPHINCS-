// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/LeanSphincs-LayeredAsm.sol";

/// @notice Tests for the leanSPHINCS layered (2^30) keccak256 verifier. The normative spec is EthLib's
///         Lean module EthLib/Cryptography/Sphincs/ (ethereum/EthLib PR #152 at aa99d5f); the summary is
///         docs/leanSphincs-layered-keccak.md. Three layers of heights 10 (top), 8, 8; FORS k = 24, a = 10
///         with no root hash; WOTS+C v = 64, w = 4, T = 128; n = 16; 7,740-byte signature.
///         - EthLib conformance: test/fixtures/leansphincs-layered-ethlib.json vendors EthLib's own
///           vectors (CC0; script/ethlib_sphincs_fixture.py): every `verify` case (valid, tampered, wrong
///           key or message, bad lengths), the `sign` outputs under the `key_gen` keys, and the Lean known
///           answer (Proofs/Sphincs/KnownAnswer.lean), whose intermediate values (digest, idx, FORS leaves,
///           FORS key, and each layer's codeword, one-time leaf and root) the spec model below reproduces.
///         - Known answers: test/fixtures/leansphincs-layered-keccak-kat.json, from the Python reference
///           signer (script/make_leansphincs_layered_kat.py), with per-layer counter substitutions.
///         - Rejection: message, key (zero key words included) and per-field signature tampering on every
///           layer, plus a fuzzed byte flip.
///         - Target sum, layer by layer: for each layer, a counter whose codeword sums below T, one above
///           T, and a second admissible one, with every layer above re-ground (fixture `isolate`), judged
///           under the root the spec model folds the result to: only that layer's check can reject the
///           first two, and the third must verify.
///         - Spec model: a plain-Solidity re-implementation of verification (bottom of this file), without
///           the target-sum check, checked against the Lean known answer. The verifier must accept exactly
///           what the model accepts on tampered signatures, and on random signatures whose three counters
///           are ground here (fresh idx, FORS leaves, codewords and paths on every run).
///         - Malformed input: the two Error(string) reverts (fuzzed over the key's low half), the length
///           checked first, and dirty ABI padding past the signature on every vector.
///         - Gas: a ceiling on the gas verify spends in its own call frame.
///         - FFI: a fresh signature from the Python reference signer.
///         Requires fs read access to test/fixtures (see `fs_permissions` in foundry.toml).
contract LeanSphincsLayeredTest is Test {
    LeanSphincsLayeredAsm verifier;

    string constant ETHLIB = "test/fixtures/leansphincs-layered-ethlib.json";
    string constant FIXTURE = "test/fixtures/leansphincs-layered-keccak-kat.json";
    string constant SIGNER = "script/leansphincs_layered_signer.py";

    uint256 constant SIG_LEN = 7740;
    uint256 constant T = 128; // TARGET_SUM

    // Signature layout (Serialization.lean).
    uint256 constant OFF_FORS_SK = 16; //   FORS secret of tree κ        at 16 + 176κ
    uint256 constant OFF_FORS_PATH = 32; // FORS path node ℓ of tree κ   at 32 + 176κ + 16ℓ
    uint256 constant FORS_STRIDE = 176; //  (1 + a)·n = 11·16, one tree's opening
    uint256 constant K = 24;
    uint256 constant A = 10;
    uint256 constant H = 26;
    // Layer L at OFF_LAYER[L]: counter (4 B), chain value σ_i at +4 + 16i, path node ℓ at +1028 + 16ℓ.
    uint256 constant OFF_BOTTOM = 4240;
    uint256 constant OFF_MIDDLE = 5396;
    uint256 constant OFF_TOP = 6552;

    // Ceiling on the gas `verify` spends in its own call frame (vm.lastCallGas().gasTotalUsed), on every
    // valid signature this file verifies: the EthLib and Lean known answers, the fixture vectors, the
    // synthetic ones, the random-digest ones and the FFI one. The frame figure is the verifier's alone;
    // a gasleft() delta around the call adds the CALL's account access and the caller's ABI encoding, so
    // it is only logged. The hashing is constant (466 keccak256, 492 Keccak-f permutations); the gas
    // depends on the WOTS step counts, through the chain dispatch (the verifier's layerRoot), and on
    // nothing else: each chain costs a fixed amount per step count n_i = 3 - x_i, 5 less for n_i > 0 in
    // the last of the 4 unrolled chains. Those costs, fitted with zero residual over 381 random-digest
    // signatures (testFuzz_AcceptsRandomDigestUnderModelRoot's construction) and extremised over every
    // step-count split with Σ n_i = 192 - T = 64 on each layer, put the frame gas of ANY admissible
    // signature in 80,395..83,482. Measured 81,958..82,289 over the EthLib and fixture signatures and
    // 81,749..82,456 over the 381 (forge 1.5.1, solc 0.8.33, via-IR). The ceiling is ~200 above the
    // worst admissible case. If a toolchain change moves the measurement, re-measure and update these.
    uint256 constant VERIFY_GAS_MAX = 83_700;

    struct Vector {
        string label;
        bytes32 seed;
        bytes32 pkSeed;
        bytes32 pkRoot;
        bytes32 message;
        bytes sig;
        uint256 idx;
        uint256[] forsIndices;
        uint256[] counters;
    }

    function setUp() public {
        verifier = new LeanSphincsLayeredAsm();
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
        v.seed = vm.parseJsonBytes32(json, _key(i, "seed"));
        v.pkSeed = vm.parseJsonBytes32(json, _key(i, "pkSeed"));
        v.pkRoot = vm.parseJsonBytes32(json, _key(i, "pkRoot"));
        v.message = vm.parseJsonBytes32(json, _key(i, "message"));
        v.sig = vm.parseJsonBytes(json, _key(i, "sig"));
        v.idx = vm.parseJsonUint(json, _key(i, "idx"));
        v.forsIndices = vm.parseJsonUintArray(json, _key(i, "fors_indices"));
        v.counters = vm.parseJsonUintArray(json, _key(i, "counters"));
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

    /// @dev EthLib's 32-byte public key root ‖ P as the verifier's high-aligned key words.
    function _keyWords(bytes memory pk) internal pure returns (bytes32 pkSeed, bytes32 pkRoot) {
        require(pk.length == 32, "public key is 32 bytes");
        bytes32 w;
        assembly ("memory-safe") {
            w := mload(add(pk, 0x20))
        }
        pkRoot = w & bytes32(~uint256(type(uint128).max));
        pkSeed = w << 128;
    }

    /// @dev A copy of `sig` with `sig[at] ^= delta`.
    function _flipped(bytes memory sig, uint256 at, uint8 delta) internal pure returns (bytes memory t) {
        t = bytes.concat(sig);
        t[at] = bytes1(uint8(t[at]) ^ delta);
    }

    function _layerOff(uint256 layer) internal pure returns (uint256) {
        return layer == 0 ? OFF_BOTTOM : layer == 1 ? OFF_MIDDLE : OFF_TOP;
    }

    function _layerHeight(uint256 layer) internal pure returns (uint256) {
        return layer == 2 ? 10 : 8;
    }

    /// @dev A copy of `sig` with layer `layer`'s counter set to LE32(c).
    function _withCounter(bytes memory sig, uint256 layer, uint256 c) internal pure returns (bytes memory t) {
        require(c < 2 ** 32, "counter is a u32");
        t = bytes.concat(sig);
        _setCounter(t, layer, c);
    }

    function _setCounter(bytes memory t, uint256 layer, uint256 c) internal pure {
        uint256 off = _layerOff(layer);
        for (uint256 j = 0; j < 4; j++) {
            t[off + j] = bytes1(uint8(c >> (8 * j)));
        }
    }

    function _counterAt(bytes memory sig, uint256 layer) internal pure returns (uint256 c) {
        uint256 off = _layerOff(layer);
        for (uint256 j = 0; j < 4; j++) {
            c |= uint256(uint8(sig[off + j])) << (8 * j);
        }
    }

    /// @dev Flipping the first byte (top bit) or the last byte (bottom bit) of the `len`-byte field at
    ///      `off` must make every vector fail. Hitting both ends of a 16-byte value also checks that the
    ///      verifier reads the whole field: a misplaced or truncated read would miss one end.
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

    function _assertAcceptsWithinGas(bytes32 pkSeed, bytes32 pkRoot, bytes32 m, bytes memory sig, string memory what)
        internal
        returns (uint256 used)
    {
        bool ok = verifier.verify(pkSeed, pkRoot, m, sig);
        used = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok, string.concat("must verify: ", what));
        assertLe(used, VERIFY_GAS_MAX, string.concat("verify gas ceiling (call frame): ", what));
    }

    // ------------------------------------------------------------------
    // EthLib conformance (the normative vectors)
    // ------------------------------------------------------------------

    /// Every EthLib `verify` case. A case whose inputs have the declared lengths must give its `output`;
    /// a signature of another length must revert (EthLib rejects it: `output: null`). A public key or
    /// message of another length cannot be expressed through verify(bytes32, bytes32, bytes32, bytes):
    /// those two cases are named and counted, so that a new EthLib case of another kind fails here.
    function testEthLibVerifyVectors() public {
        string memory json = vm.readFile(ETHLIB);
        uint256 checked;
        uint256 unrepresentable;
        for (uint256 i = 0;; i++) {
            string memory k = string.concat(".verify[", vm.toString(i), "].");
            if (!vm.keyExistsJson(json, string.concat(".verify[", vm.toString(i), "]"))) break;
            string memory name = vm.parseJsonString(json, string.concat(k, "name"));
            string memory verdict = vm.parseJsonString(json, string.concat(k, "verdict"));
            bytes memory pk = vm.parseJsonBytes(json, string.concat(k, "public_key"));
            bytes memory m = vm.parseJsonBytes(json, string.concat(k, "message"));
            bytes memory sig = vm.parseJsonBytes(json, string.concat(k, "signature"));
            if (pk.length != 32 || m.length != 32) {
                assertEq(verdict, "rejected", string.concat("EthLib rejects a short key or message: ", name));
                assertTrue(
                    _eq(name, "verify_short_message") || _eq(name, "verify_short_public_key"),
                    string.concat("unexpected unrepresentable case: ", name)
                );
                unrepresentable++;
                continue;
            }
            (bytes32 pkSeed, bytes32 pkRoot) = _keyWords(pk);
            if (sig.length != SIG_LEN) {
                assertEq(verdict, "rejected", string.concat("EthLib rejects a bad length: ", name));
                vm.expectRevert(bytes("Invalid sig length"));
                verifier.verify(pkSeed, pkRoot, bytes32(m), sig);
            } else if (_eq(verdict, "valid")) {
                _assertAcceptsWithinGas(pkSeed, pkRoot, bytes32(m), sig, name);
            } else {
                assertEq(verdict, "invalid", name);
                assertFalse(verifier.verify(pkSeed, pkRoot, bytes32(m), sig), name);
            }
            checked++;
        }
        assertEq(checked, 22, "EthLib verify cases checked");
        assertEq(unrepresentable, 2, "EthLib verify cases with a short key or message");
    }

    /// EthLib's `sign` outputs verify under the `key_gen` key of the same seed ("The valid cases come
    /// from the sign cases, and the public keys from the key_gen cases"), and not under a flipped message.
    function testEthLibSignOutputsVerifyUnderKeyGenKeys() public {
        string memory json = vm.readFile(ETHLIB);
        uint256 signed;
        for (uint256 i = 0; vm.keyExistsJson(json, string.concat(".sign[", vm.toString(i), "]")); i++) {
            string memory k = string.concat(".sign[", vm.toString(i), "].");
            bytes memory seed = vm.parseJsonBytes(json, string.concat(k, "seed"));
            bytes memory m = vm.parseJsonBytes(json, string.concat(k, "message"));
            if (seed.length != 32 || m.length != 32) continue; // the rejected cases (output: null)
            bytes memory sig = vm.parseJsonBytes(json, string.concat(k, "output"));
            assertEq(sig.length, SIG_LEN, "EthLib signature length");
            bytes memory pk = _ethlibKeyGen(json, seed);
            (bytes32 pkSeed, bytes32 pkRoot) = _keyWords(pk);
            string memory name = vm.parseJsonString(json, string.concat(k, "name"));
            _assertAcceptsWithinGas(pkSeed, pkRoot, bytes32(m), sig, name);
            assertFalse(verifier.verify(pkSeed, pkRoot, bytes32(m) ^ bytes32(uint256(1)), sig), name);
            signed++;
        }
        assertEq(signed, 3, "EthLib sign cases");
    }

    function _ethlibKeyGen(string memory json, bytes memory seed) internal view returns (bytes memory) {
        for (uint256 i = 0; vm.keyExistsJson(json, string.concat(".key_gen[", vm.toString(i), "]")); i++) {
            string memory k = string.concat(".key_gen[", vm.toString(i), "].");
            if (keccak256(vm.parseJsonBytes(json, string.concat(k, "seed"))) == keccak256(seed)) {
                return vm.parseJsonBytes(json, string.concat(k, "output"));
            }
        }
        revert("no key_gen case for the seed");
    }

    /// The Lean known answer (KnownAnswer.lean: scheme seed S[i] = 37i + 11, message m[i] = 7i + 3,
    /// checked by the Lean kernel) verifies, and the plain-Solidity spec model computes every value the
    /// Lean file pins on the way: the digest, idx, the 24 FORS leaves, the FORS key, and each layer's
    /// codeword, one-time leaf and root. This is what ties the model, used as the oracle below, to Lean.
    function testLeanKnownAnswer() public {
        string memory json = vm.readFile(ETHLIB);
        string memory k = ".lean_known_answer.";
        (bytes32 pkSeed, bytes32 pkRoot) = _keyWords(vm.parseJsonBytes(json, string.concat(k, "public_key")));
        bytes32 m = vm.parseJsonBytes32(json, string.concat(k, "message"));
        bytes memory sig = vm.parseJsonBytes(json, string.concat(k, "signature"));
        _assertAcceptsWithinGas(pkSeed, pkRoot, m, sig, "Lean known answer");
        assertFalse(verifier.verify(pkSeed, pkRoot, m ^ bytes32(uint256(1)), sig), "Lean known answer: other m");

        bytes16 p = bytes16(pkSeed);
        (bytes32 d0, bytes32 d1) = _digests(p, m, _n(sig, 0));
        assertEq(abi.encodePacked(d0, d1), vm.parseJsonBytes(json, string.concat(k, "digest")), "digest");
        uint256 idx = _idx(d0, d1);
        assertEq(idx, vm.parseJsonUint(json, string.concat(k, "idx")), "idx");
        uint256[] memory leaves = vm.parseJsonUintArray(json, string.concat(k, "leaves"));
        for (uint256 kappa = 0; kappa < K; kappa++) {
            assertEq(_forsLeaf(d0, d1, kappa), leaves[kappa], "FORS leaf");
        }
        bytes memory forsKey = _modelForsKey(p, d0, d1, idx, sig);
        assertEq(forsKey, vm.parseJsonBytes(json, string.concat(k, "fors_key")), "FORS key");

        string[3] memory names = ["bottom", "middle", "top"];
        bytes memory msg = forsKey;
        for (uint256 layer = 0; layer < 3; layer++) {
            ModelLayer memory r = _modelLayer(p, layer, idx, msg, sig);
            uint256[] memory cw = vm.parseJsonUintArray(json, string.concat(k, names[layer], "_codeword"));
            for (uint256 i = 0; i < 64; i++) {
                assertEq((r.x >> (2 * i)) & 3, cw[i], string.concat(names[layer], " codeword"));
            }
            assertEq(r.sum, T, string.concat(names[layer], " codeword sum"));
            assertEq(
                abi.encodePacked(r.leaf),
                vm.parseJsonBytes(json, string.concat(k, names[layer], "_leaf")),
                string.concat(names[layer], " leaf")
            );
            assertEq(
                abi.encodePacked(r.root),
                vm.parseJsonBytes(json, string.concat(k, names[layer], "_root")),
                string.concat(names[layer], " root")
            );
            msg = abi.encodePacked(r.root);
        }
        assertEq(bytes32(bytes16(msg)), pkRoot, "the top root is the key's");
    }

    // ------------------------------------------------------------------
    // Known answers (the generated fixture)
    // ------------------------------------------------------------------

    /// Every fixture vector verifies, within VERIFY_GAS_MAX in verify's own call frame. The gasleft()
    /// delta around the call is logged next to it; the warm-up call keeps the cold account access out of
    /// that logged figure.
    function testKatVectorsVerify() public {
        Vector[] memory vs = _vectors();
        string memory json = vm.readFile(FIXTURE);
        assertEq(vm.parseJsonUint(json, ".sig_len"), SIG_LEN, "fixture sig_len");

        assertTrue(_verify(vs[0], vs[0].sig), "warm-up");
        uint256 minGas = type(uint256).max;
        uint256 maxGas;
        for (uint256 i = 0; i < vs.length; i++) {
            assertEq(vs[i].sig.length, SIG_LEN, "signature length");
            uint256 g = gasleft();
            bool ok = verifier.verify(vs[i].pkSeed, vs[i].pkRoot, vs[i].message, vs[i].sig);
            uint256 outer = g - gasleft();
            uint256 used = vm.lastCallGas().gasTotalUsed;
            assertTrue(ok, string.concat("KAT must verify: ", vs[i].label));
            emit log_named_uint(string.concat("verify gas, call frame [", vs[i].label, "]"), used);
            emit log_named_uint(string.concat("  gasleft() delta around the call [", vs[i].label, "]"), outer);
            if (used < minGas) minGas = used;
            if (used > maxGas) maxGas = used;
        }
        emit log_named_uint("verify gas, call frame, min", minGas);
        emit log_named_uint("verify gas, call frame, max", maxGas);
        assertLe(maxGas, VERIFY_GAS_MAX, "verify gas ceiling (call frame)");
    }

    /// The fixture's own fields agree with its signature bytes and with the spec, recomputed here in
    /// plain Solidity (independently of the Yul verifier): the counters are the bytes at their offsets,
    /// the digest gives the recorded idx and FORS leaves, the key words are the public key's halves, and
    /// the spec model reaches pkRoot with three admissible codewords. Catches a hand-edited fixture.
    function testKatFixtureFieldsMatchSpec() public view {
        string memory json = vm.readFile(FIXTURE);
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            (bytes32 pkSeed, bytes32 pkRoot) = _keyWords(vm.parseJsonBytes(json, _key(i, "publicKey")));
            assertEq(pkSeed, v.pkSeed, "pkSeed = publicKey[16:32]");
            assertEq(pkRoot, v.pkRoot, "pkRoot = publicKey[0:16]");
            for (uint256 layer = 0; layer < 3; layer++) {
                assertEq(_counterAt(v.sig, layer), v.counters[layer], "counter = LE32 at the layer's offset");
            }
            (bytes32 d0, bytes32 d1) = _digests(bytes16(v.pkSeed), v.message, _n(v.sig, 0));
            assertEq(_idx(d0, d1), v.idx, "idx");
            assertEq(v.forsIndices.length, K, "24 FORS leaves");
            for (uint256 kappa = 0; kappa < K; kappa++) {
                assertEq(_forsLeaf(d0, d1, kappa), v.forsIndices[kappa], "FORS leaf");
            }
            (bytes32 root, uint256[3] memory sums) = _modelRoot(v.pkSeed, v.message, v.sig);
            assertEq(root, v.pkRoot, string.concat("model root, ", v.label));
            for (uint256 layer = 0; layer < 3; layer++) {
                assertEq(sums[layer], T, string.concat("model codeword sum, ", v.label));
            }
        }
    }

    /// Two placements depend on an index bit and touch the end of a region: bit 25 of idx (bit 9 of the
    /// top leaf) decides whether the top path's last node, the last 16 signature bytes, is the left or
    /// the right child (testIgnoresDirtyCalldataPadding), and bit 9 of u_23 orders tree 23's FORS key
    /// pair, whose 32-byte store spills onto 0x388..0x397 where the bottom counter goes (the verifier's
    /// MASKING note). A fault in either placement shows only on the vectors that take it, so the fixture
    /// must hold both values of both bits (testFixtureCoverageGuardsAreTwoSided).
    function testFixtureCoversIndexBits() public view {
        Vector[] memory vs = _vectors();
        checkCoversIdxBit25(vs);
        checkCoversU23Bit9(vs);
    }

    /// @dev Public so testFixtureCoverageGuardsAreTwoSided can call it and expect a revert.
    function checkCoversIdxBit25(Vector[] memory vs) public pure {
        uint256 ones;
        for (uint256 i = 0; i < vs.length; i++) {
            if ((vs[i].idx >> 25) & 1 == 1) ones++;
        }
        assertGt(ones, 0, "fixture needs a vector whose top path[9] is the left child (bit 25 of idx set)");
        assertLt(ones, vs.length, "fixture needs a vector whose top path[9] is the right child (bit 25 clear)");
    }

    /// @dev Public so testFixtureCoverageGuardsAreTwoSided can call it and expect a revert.
    function checkCoversU23Bit9(Vector[] memory vs) public pure {
        uint256 ones;
        for (uint256 i = 0; i < vs.length; i++) {
            if ((vs[i].forsIndices[K - 1] >> 9) & 1 == 1) ones++;
        }
        assertGt(ones, 0, "fixture needs a vector with bit 9 of u_23 set (tree 23's key store spills)");
        assertLt(ones, vs.length, "fixture needs a vector with bit 9 of u_23 clear");
    }

    /// Each coverage guard must pass the real fixture and reject two one-sided copies of it, one per value
    /// of its bit, so that a regenerated fixture cannot lose that coverage silently.
    function testFixtureCoverageGuardsAreTwoSided() public {
        Vector[] memory vs = _vectors();
        this.checkCoversIdxBit25(vs);
        this.checkCoversU23Bit9(vs);
        for (uint256 value = 0; value < 2; value++) {
            vm.expectRevert();
            this.checkCoversIdxBit25(_oneSided(vs, true, value));
            vm.expectRevert();
            this.checkCoversU23Bit9(_oneSided(vs, false, value));
        }
    }

    function _oneSided(Vector[] memory vs, bool idxBit25, uint256 value) internal pure returns (Vector[] memory out) {
        Vector[] memory kept = new Vector[](vs.length);
        uint256 n;
        for (uint256 i = 0; i < vs.length; i++) {
            uint256 bit = idxBit25 ? (vs[i].idx >> 25) & 1 : (vs[i].forsIndices[K - 1] >> 9) & 1;
            if (bit == value) kept[n++] = vs[i];
        }
        assertGt(n, 0, "the fixture holds both values of the bit");
        out = new Vector[](vs.length);
        for (uint256 i = 0; i < vs.length; i++) {
            out[i] = kept[i % n];
        }
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
            assertFalse(verifier.verify(v.pkSeed ^ bytes32(uint256(1) << 128), v.pkRoot, v.message, v.sig), "P low");
            assertFalse(verifier.verify(v.pkSeed ^ bytes32(uint256(1) << 255), v.pkRoot, v.message, v.sig), "P top");
        }
    }

    function testRejectsWrongPkRoot() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            assertFalse(verifier.verify(v.pkSeed, v.pkRoot ^ bytes32(uint256(1) << 128), v.message, v.sig), "root low");
            assertFalse(verifier.verify(v.pkSeed, v.pkRoot ^ bytes32(uint256(1) << 255), v.message, v.sig), "root top");
            // Another key's words (the next vector with another seed; two vectors may share a key), and
            // the other key's root with this P.
            uint256 oi = (i + 1) % vs.length;
            while (vs[oi].pkSeed == v.pkSeed) oi = (oi + 1) % vs.length;
            Vector memory o = vs[oi];
            assertFalse(verifier.verify(o.pkSeed, o.pkRoot, v.message, v.sig), "another key");
            assertFalse(verifier.verify(v.pkSeed, o.pkRoot, v.message, v.sig), "another root");
        }
    }

    /// Every bit of P, of the root and of the message is bound. P and m feed every hash (through the
    /// digest), so a flipped bit almost always fails a target-sum check; the root is only compared, at the
    /// end, so a comparison that skipped some of its 128 bits would still accept the honest signature and
    /// would let a forger fit the rest of the root by grinding: each one of them is flipped here.
    function testRejectsEveryKeyAndMessageBitFlip() public view {
        Vector[] memory vs = _vectors();
        uint256[2] memory sel = [uint256(0), 3]; // bit 25 of idx clear, then set (top path[9] on each side)
        for (uint256 s = 0; s < sel.length; s++) {
            Vector memory v = vs[sel[s]];
            for (uint256 b = 128; b < 256; b++) {
                bytes32 bit = bytes32(uint256(1) << b);
                assertFalse(verifier.verify(v.pkSeed ^ bit, v.pkRoot, v.message, v.sig), "P bit");
                assertFalse(verifier.verify(v.pkSeed, v.pkRoot ^ bit, v.message, v.sig), "root bit");
            }
            for (uint256 b = 0; b < 256; b++) {
                bytes32 bit = bytes32(uint256(1) << b);
                assertFalse(verifier.verify(v.pkSeed, v.pkRoot, v.message ^ bit, v.sig), "message bit");
            }
        }
        assertTrue((vs[0].idx >> 25) & 1 != (vs[3].idx >> 25) & 1, "the two vectors differ in bit 25 of idx");
    }

    /// Signatures whose bottom layer is inadmissible (random bytes: each layer is admissible with probability
    /// 2^-13.8) are false under the zero root and under all-zero key words, as are the per-layer isolated
    /// signatures (_assertIsolatedRejects): no inadmissible layer reaches the root comparison.
    function testZeroRootRejectsInadmissibleSignatures() public view {
        Vector memory v = _vectors()[0];
        for (uint256 i = 0; i < 4; i++) {
            bytes memory sig = _randomSig(keccak256(abi.encode("inadmissible", i)));
            bytes32 m = keccak256(abi.encode("message", i));
            assertFalse(verifier.verify(bytes32(0), bytes32(0), m, sig), "uninitialised key");
            assertFalse(verifier.verify(v.pkSeed, bytes32(0), m, sig), "zero root");
        }
        assertFalse(verifier.verify(v.pkSeed, bytes32(0), v.message, new bytes(SIG_LEN)), "all-zero signature");
    }

    /// Zero key words are canonical and are what an uninitialised storage slot holds, so they get no
    /// special treatment: a valid signature under another key is just `false`.
    function testRejectsZeroKeyWords() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            assertFalse(verifier.verify(v.pkSeed, bytes32(0), v.message, v.sig), string.concat("root 0, ", v.label));
            assertFalse(verifier.verify(bytes32(0), v.pkRoot, v.message, v.sig), string.concat("P 0, ", v.label));
            assertFalse(verifier.verify(bytes32(0), bytes32(0), v.message, v.sig), string.concat("both 0, ", v.label));
        }
    }

    // ------------------------------------------------------------------
    // Rejection: one tampered byte per signature region
    // ------------------------------------------------------------------

    function testRejectsTamperedRandomizer() public view {
        _assertFieldBound(0, 16, "rho");
    }

    /// Trees 0, 22 and 23 (the last leaf of D_0's 256 bits and the one from D_1), and tree 12.
    function testRejectsTamperedForsSecrets() public view {
        uint256[4] memory trees = [uint256(0), 12, 22, 23];
        for (uint256 t = 0; t < trees.length; t++) {
            _assertFieldBound(OFF_FORS_SK + FORS_STRIDE * trees[t], 16, string.concat("FORS sk_", vm.toString(trees[t])));
        }
    }

    /// Level 0 of every one of the 24 trees.
    function testRejectsTamperedForsPathLevel0() public view {
        for (uint256 k = 0; k < K; k++) {
            _assertFieldBound(OFF_FORS_PATH + FORS_STRIDE * k, 16, string.concat("FORS p_", vm.toString(k), "[0]"));
        }
    }

    /// Level 9 (the sibling level-9 node, which goes straight into the FORS key) of every tree.
    function testRejectsTamperedForsPathLevel9() public view {
        for (uint256 k = 0; k < K; k++) {
            _assertFieldBound(
                OFF_FORS_PATH + FORS_STRIDE * k + 16 * (A - 1), 16, string.concat("FORS p_", vm.toString(k), "[9]")
            );
        }
        assertEq(OFF_FORS_PATH + FORS_STRIDE * (K - 1) + 16 * A, OFF_BOTTOM, "p_23[9] ends the FORS part");
    }

    /// Each of the 4 counter bytes of each layer: the encoding changes, which is (almost always)
    /// inadmissible and otherwise moves every chain's start position.
    function testRejectsTamperedCounters() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            for (uint256 layer = 0; layer < 3; layer++) {
                for (uint256 j = 0; j < 4; j++) {
                    uint256 at = _layerOff(layer) + j;
                    assertFalse(_verify(vs[i], _flipped(vs[i].sig, at, 0x01)), string.concat("counter, ", vs[i].label));
                    assertFalse(_verify(vs[i], _flipped(vs[i].sig, at, 0x80)), string.concat("counter, ", vs[i].label));
                }
            }
        }
    }

    /// The first and the last chain value, and the first and the last path node, of every layer.
    function testRejectsTamperedLayerFields() public view {
        string[3] memory names = ["bottom", "middle", "top"];
        for (uint256 layer = 0; layer < 3; layer++) {
            uint256 off = _layerOff(layer);
            uint256 h = _layerHeight(layer);
            _assertFieldBound(off + 4, 16, string.concat(names[layer], " sigma_0"));
            _assertFieldBound(off + 4 + 16 * 63, 16, string.concat(names[layer], " sigma_63"));
            _assertFieldBound(off + 1028, 16, string.concat(names[layer], " path[0]"));
            _assertFieldBound(off + 1028 + 16 * (h - 1), 16, string.concat(names[layer], " path[last]"));
            assertEq(off + 1028 + 16 * h, layer == 2 ? SIG_LEN : _layerOff(layer + 1), "the layer's path ends it");
        }
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
    // The WOTS+C target sum, layer by layer
    // ------------------------------------------------------------------

    /// @dev The fixture's substitution `kind` of layer `layer` of vector `i`: the signature with its three
    ///      counters, checked against the model's sums and root as recorded.
    function _isolated(string memory json, uint256 i, uint256 layer, string memory kind)
        internal
        view
        returns (Vector memory v, bytes memory sig, bytes32 modelRoot, uint256[3] memory sums)
    {
        v = _vector(json, i);
        string memory k = string.concat(_key(i, "isolate"), "[", vm.toString(layer), "].", kind, ".");
        uint256[] memory counters = vm.parseJsonUintArray(json, string.concat(k, "counters"));
        sig = bytes.concat(v.sig);
        for (uint256 l = 0; l < 3; l++) {
            _setCounter(sig, l, counters[l]);
            // Below the substituted layer nothing changes.
            if (l < layer) assertEq(counters[l], v.counters[l], "layers below keep their counters");
        }
        (modelRoot, sums) = _modelRoot(v.pkSeed, v.message, sig);
        assertEq(modelRoot, vm.parseJsonBytes32(json, string.concat(k, "modelRoot")), "fixture model root");
        uint256[] memory want = vm.parseJsonUintArray(json, string.concat(k, "sums"));
        for (uint256 l = 0; l < 3; l++) {
            assertEq(sums[l], want[l], "fixture codeword sums");
        }
    }

    /// For every vector and layer: layer L's counter replaced by one whose codeword sums to T - 1 = 127,
    /// every layer above re-ground to an admissible counter, judged under the root the spec model folds it
    /// to. Everything but layer L's target-sum check matches, so only that check can reject it. The sum is
    /// on the boundary: a counter merely below T almost always sums far below it (the mean is 96), and a
    /// check that also let 127 through would pass such a test. Accepting a sum below T is a departure from
    /// EthLib (it rejects), not a forgery by itself: a codeword that dominates a signed one sums to ≥ T.
    function testRejectsBelowTargetCounterUnderItsOwnRoot() public view {
        _assertIsolatedRejects("below");
    }

    /// The other side of each layer's check: a codeword summing to T + 1 = 129, in the same isolated
    /// setting. Accepting a sum above T IS a forgery: chains can be advanced from a known signature (with
    /// x'_i ≥ x_i for every i, σ'_i = chain(σ_i, x_i → x'_i) reaches the same chain ends), so a forger can
    /// move to any dominating codeword. A random counter lands above T only now and then, so the fixture
    /// pins one per layer and vector, on the boundary.
    function testRejectsAboveTargetCounterUnderItsOwnRoot() public view {
        _assertIsolatedRejects("above");
    }

    function _assertIsolatedRejects(string memory kind) internal view {
        string memory json = vm.readFile(FIXTURE);
        uint256 n = _count(json);
        for (uint256 i = 0; i < n; i++) {
            for (uint256 layer = 0; layer < 3; layer++) {
                (Vector memory v, bytes memory sig, bytes32 root, uint256[3] memory sums) =
                    _isolated(json, i, layer, kind);
                for (uint256 l = 0; l < 3; l++) {
                    if (l == layer) {
                        assertEq(sums[l], _eq(kind, "below") ? T - 1 : T + 1, "the layer's sum is T - 1 or T + 1");
                    } else {
                        assertEq(sums[l], T, "every other layer is admissible");
                    }
                }
                string memory what = string.concat(kind, " T on layer ", vm.toString(layer), ", ", v.label);
                assertFalse(verifier.verify(v.pkSeed, root, v.message, sig), what);
                // An inadmissible layer must end verification with `false`, not hand a placeholder root to
                // the comparison: under the zero root (an uninitialised key word) and under the honest root
                // it is still false.
                assertFalse(verifier.verify(v.pkSeed, bytes32(0), v.message, sig), string.concat(what, ", root 0"));
                assertFalse(verifier.verify(v.pkSeed, v.pkRoot, v.message, sig), string.concat(what, ", key root"));
            }
        }
    }

    /// The positive control of the two tests above: layer L's counter replaced by the next admissible one
    /// (a second codeword), the layers above re-ground, judged under the model's root. The chain values
    /// were revealed for the signed codeword, not this one, yet verification accepts: the spec checks the
    /// target sum and the root, nothing more, so the rejections above come from the target-sum check
    /// alone, and the verifier accepts signatures no signer produced exactly when the spec does.
    function testAcceptsSecondAdmissibleCounterUnderItsOwnRoot() public {
        string memory json = vm.readFile(FIXTURE);
        uint256 n = _count(json);
        for (uint256 i = 0; i < n; i++) {
            for (uint256 layer = 0; layer < 3; layer++) {
                (Vector memory v, bytes memory sig, bytes32 root, uint256[3] memory sums) =
                    _isolated(json, i, layer, "other");
                assertTrue(sums[0] == T && sums[1] == T && sums[2] == T, "all admissible");
                assertTrue(_counterAt(sig, layer) != v.counters[layer], "another counter");
                assertTrue(root != v.pkRoot, "root moved");
                _assertAcceptsWithinGas(v.pkSeed, root, v.message, sig, string.concat("other codeword, ", v.label));
            }
        }
    }

    /// The top layer's chain values and path feed no encoding, so changing one gives a signature that is
    /// valid under the root the spec model computes for it.
    function testAcceptsSyntheticTopLayerUnderItsOwnRoot() public {
        Vector[] memory vs = _vectors();
        uint256[4] memory offs = [OFF_TOP + 4, OFF_TOP + 4 + 16 * 63 + 15, OFF_TOP + 1028, SIG_LEN - 1];
        for (uint256 i = 0; i < vs.length; i++) {
            for (uint256 j = 0; j < offs.length; j++) {
                bytes memory sig = _flipped(vs[i].sig, offs[j], 0x5a);
                (bytes32 root, uint256[3] memory sums) = _modelRoot(vs[i].pkSeed, vs[i].message, sig);
                assertTrue(sums[0] == T && sums[1] == T && sums[2] == T, "encodings unchanged");
                assertTrue(root != vs[i].pkRoot, "root moved");
                _assertAcceptsWithinGas(vs[i].pkSeed, root, vs[i].message, sig, string.concat("synthetic, ", vs[i].label));
            }
        }
    }

    // ------------------------------------------------------------------
    // Against the spec model
    // ------------------------------------------------------------------

    /// The verifier equals the spec model on arbitrary single-byte tampering, judged under the root the
    /// model computes for the tampered signature: true iff all three encodings are admissible. A top-layer
    /// chain value or path flip keeps every codeword, so both sides accept and the top layer is compared;
    /// any other flip changes some encoding, which is inadmissible except with probability ≈ 2^-13.8, and
    /// only that 1-bit verdict is compared. Acceptance at fresh digests is the random-digest test below.
    /// forge-config: default.fuzz.runs = 256
    function testFuzz_VerifierMatchesSpecModel(uint256 vecSel, uint256 at, uint8 delta) public view {
        string memory json = vm.readFile(FIXTURE);
        Vector memory v = _vector(json, vecSel % _count(json));
        bytes memory sig = _flipped(v.sig, bound(at, 0, SIG_LEN - 1), uint8(bound(delta, 1, 255)));
        (bytes32 root, uint256[3] memory sums) = _modelRoot(v.pkSeed, v.message, sig);
        bool admissible = sums[0] == T && sums[1] == T && sums[2] == T;
        assertEq(verifier.verify(v.pkSeed, root, v.message, sig), admissible, "verifier != spec model");
    }

    /// Acceptance at digests no fixture vector has. P, m and the whole 7,740-byte signature are random, so
    /// ρ, and with it idx (every layer's tree and leaf) and all 24 FORS leaves, is uniform, as are the
    /// FORS openings, chain values and paths. Each layer's counter is then ground, from the bottom up,
    /// until the encoding of the message the model gives that layer is admissible, and the signature is
    /// judged under the root the model folds it to. The verifier must accept it, which checks every FORS
    /// climb (at 24 fresh leaves), the FORS key and the counter in the bottom encoding, the root and the
    /// counter in the two upper encodings, all 192 chains (at fresh keys and codewords) and all 26 tree
    /// levels against the model, within VERIFY_GAS_MAX. It must reject the same signature under that root
    /// with its lowest bit flipped (the root mismatch path). Each run grinds about 3·2^13.8 counters, so
    /// the run count is lower than the other fuzz tests'.
    /// forge-config: default.fuzz.runs = 48
    function testFuzz_AcceptsRandomDigestUnderModelRoot(bytes32 pSeed, bytes32 m, bytes32 bodySeed) public {
        bytes32 pkSeed = pSeed & bytes32(~uint256(type(uint128).max)); // canonical P ‖ 0^16
        bytes16 p = bytes16(pkSeed);
        bytes memory sig = _randomSig(bodySeed);

        (bytes32 d0, bytes32 d1) = _digests(p, m, _n(sig, 0));
        uint256 idx = _idx(d0, d1);
        bytes memory msg = _modelForsKey(p, d0, d1, idx, sig);
        for (uint256 layer = 0; layer < 3; layer++) {
            (uint256 tree, uint256 leaf) = _otsKey(layer, idx);
            _setCounter(sig, layer, _grindCounter(p, _adr(4, 0, layer, tree, 0, leaf), msg));
            ModelLayer memory r = _modelLayer(p, layer, idx, msg, sig);
            assertEq(r.sum, T, "model: the ground counter is admissible");
            msg = abi.encodePacked(r.root);
        }
        bytes32 root = bytes32(bytes16(msg));
        (bytes32 root2,) = _modelRoot(pkSeed, m, sig);
        assertEq(root2, root, "model root");

        _assertAcceptsWithinGas(pkSeed, root, m, sig, "random digest");
        assertFalse(verifier.verify(pkSeed, root ^ bytes32(uint256(1) << 128), m, sig), "random digest: wrong root");
    }

    /// The model's address encoding (Address.lean encodeAddress) on a vector with every field nonzero.
    function testSpecModelAddressEncoding() public pure {
        // lo 0x89abcdef, hi 0x123456, type 17, step 5, layer 2, tree 0x01020304.
        bytes16 expected = hex"efcdab89563412b10204030201000000";
        assertEq(_adr(17, 5, 2, 0x01020304, 0x123456, 0x89abcdef), expected);
    }

    // ------------------------------------------------------------------
    // Malformed input: Error(string) reverts
    // ------------------------------------------------------------------

    function testRevertsOnBadSigLength() public {
        Vector[] memory vs = _vectors();
        Vector memory v = vs[0];
        bytes memory shortSig = new bytes(SIG_LEN - 1);
        for (uint256 j = 0; j < shortSig.length; j++) {
            shortSig[j] = v.sig[j];
        }
        uint256[5] memory lens = [uint256(0), SIG_LEN - 1, SIG_LEN + 1, SIG_LEN + 32, 5684]; // 5684: leanSphincs
        for (uint256 j = 0; j < lens.length; j++) {
            bytes memory s = new bytes(lens[j]);
            for (uint256 b = 0; b < s.length && b < SIG_LEN; b++) {
                s[b] = v.sig[b];
            }
            vm.expectRevert(bytes("Invalid sig length"));
            verifier.verify(v.pkSeed, v.pkRoot, v.message, s);
        }
    }

    /// A key word with a nonzero low half is not a key (pkSeed = P ‖ 0^16, pkRoot = root ‖ 0^16), even
    /// with an otherwise valid signature.
    function testRevertsOnNonCanonicalKey() public {
        Vector memory v = _vectors()[0];
        uint256[3] memory bits = [uint256(0), 64, 127];
        for (uint256 j = 0; j < bits.length; j++) {
            vm.expectRevert(bytes("Invalid public key"));
            verifier.verify(v.pkSeed | bytes32(uint256(1) << bits[j]), v.pkRoot, v.message, v.sig);
            vm.expectRevert(bytes("Invalid public key"));
            verifier.verify(v.pkSeed, v.pkRoot | bytes32(uint256(1) << bits[j]), v.message, v.sig);
        }
    }

    /// Any nonzero low half reverts, in pkSeed, pkRoot or both, on any vector.
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

    /// The length is checked before the key when both are wrong.
    function testLengthCheckedBeforeKey() public {
        Vector memory v = _vectors()[0];
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed | bytes32(uint256(1)), v.pkRoot, v.message, "");
        vm.expectRevert(bytes("Invalid sig length"));
        verifier.verify(v.pkSeed, v.pkRoot | bytes32(uint256(1)), v.message, bytes.concat(v.sig, hex"00"));
    }

    /// The ABI pads the 7,740-byte signature with 4 zero bytes, and the verifier never reads them: every
    /// sibling is calldatacopy'd, exactly 16 bytes. The top path's last node is the last 16 signature
    /// bytes; a 32-byte read of it would put the padding and 12 bytes beyond it into the R slot, into the
    /// hash input, exactly when it is the LEFT child (bit 25 of idx set). So every vector is run with
    /// dirty padding alone and with a trailing all-ones word too, and the fixture must hold both kinds
    /// (checkCoversIdxBit25).
    function testIgnoresDirtyCalldataPadding() public view {
        Vector[] memory vs = _vectors();
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            bytes memory cd = abi.encodeCall(LeanSphincsLayeredAsm.verify, (v.pkSeed, v.pkRoot, v.message, v.sig));
            // selector(4) ‖ pkSeed ‖ pkRoot ‖ message ‖ offset ‖ length ‖ sig(7740) ‖ 4 zero bytes.
            uint256 sigEnd = 4 + 5 * 32 + SIG_LEN;
            assertEq(cd.length, sigEnd + 4, "abi layout");
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

    /// The verifier reads the signature where the ABI decoder puts it (sig.offset, sig.length), not at the
    /// canonical position: under non-canonical encodings (junk between the head and the length word, 32 or
    /// 64 bytes of it, or 3, which leaves the offset unaligned) a valid signature still verifies and a
    /// tampered one still fails. A verifier that hard-coded the canonical position, for the data or for the
    /// length, would read the junk instead (both checked by mutation).
    function testNonCanonicalAbiEncodings() public view {
        Vector[] memory vs = _vectors();
        uint256[3] memory gaps = [uint256(32), 64, 3];
        for (uint256 i = 0; i < vs.length; i++) {
            Vector memory v = vs[i];
            for (uint256 g = 0; g < gaps.length; g++) {
                bytes memory junk = new bytes(gaps[g]);
                for (uint256 j = 0; j < junk.length; j++) {
                    junk[j] = 0xff;
                }
                assertTrue(_callWithGap(v, v.sig, junk), string.concat("valid, non-canonical offset, ", v.label));
                assertFalse(
                    _callWithGap(v, _flipped(v.sig, SIG_LEN - 1, 0x01), junk),
                    string.concat("tampered, non-canonical offset, ", v.label)
                );
            }
        }
    }

    /// @dev verify(v's key, v.message, sig) encoded with `junk` between the head and sig's length word:
    ///      selector ‖ pkSeed ‖ pkRoot ‖ message ‖ offset (0x80 + junk.length) ‖ junk ‖ length ‖ sig ‖ 0^32.
    function _callWithGap(Vector memory v, bytes memory sig, bytes memory junk) internal view returns (bool) {
        bytes memory cd = abi.encodePacked(
            LeanSphincsLayeredAsm.verify.selector,
            v.pkSeed,
            v.pkRoot,
            v.message,
            uint256(0x80 + junk.length),
            junk,
            uint256(sig.length),
            sig,
            bytes32(0)
        );
        (bool ok, bytes memory ret) = address(verifier).staticcall(cd);
        assertTrue(ok, "call succeeds");
        assertEq(ret.length, 32, "one return word");
        return abi.decode(ret, (bool));
    }

    function _assertCallAccepts(bytes memory cd, string memory what) internal view {
        (bool ok, bytes memory ret) = address(verifier).staticcall(cd);
        assertTrue(ok, string.concat("call succeeds: ", what));
        assertTrue(abi.decode(ret, (bool)), string.concat("must not affect a valid signature: ", what));
    }

    // ------------------------------------------------------------------
    // FFI: a fresh signature from the Python reference signer
    // ------------------------------------------------------------------

    /// Signs a fresh message with `python3 script/leansphincs_layered_signer.py sign <seed> <msg>` (a few
    /// seconds: the top tree, both lower trees, FORS and three counter searches) and verifies it. Needs
    /// pycryptodome (`pip install pycryptodome`, or run forge with the repo venv on PATH).
    function testVerifyFFI_Python() public {
        bytes32 seed = keccak256("leanSphincs-layered FFI seed");
        bytes32 message = keccak256("leanSphincs-layered FFI message");
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = _pySign(seed, message);
        assertEq(sig.length, SIG_LEN, "signature length");
        uint256 used = _assertAcceptsWithinGas(pkSeed, pkRoot, message, sig, "Python signature");
        emit log_named_uint("verify gas, call frame (Python sig)", used);
        assertFalse(verifier.verify(pkSeed, pkRoot, message ^ bytes32(uint256(1)), sig), "wrong message");

        // The key words are the halves of `keygen`'s root ‖ P.
        string[] memory kg = new string[](4);
        kg[0] = "python3";
        kg[1] = SIGNER;
        kg[2] = "keygen";
        kg[3] = vm.toString(seed);
        (bytes32 s2, bytes32 r2) = _keyWords(vm.ffi(kg));
        assertEq(s2, pkSeed, "keygen P");
        assertEq(r2, pkRoot, "keygen root");
    }

    function _pySign(bytes32 seed, bytes32 message) internal returns (bytes32, bytes32, bytes memory) {
        string[] memory inputs = new string[](5);
        inputs[0] = "python3";
        inputs[1] = SIGNER;
        inputs[2] = "sign";
        inputs[3] = vm.toString(seed);
        inputs[4] = vm.toString(message);
        return abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    function _eq(string memory a, string memory b) internal pure returns (bool) {
        return keccak256(bytes(a)) == keccak256(bytes(b));
    }

    /// 16 bytes of `b` at `off`.
    function _n(bytes memory b, uint256 off) internal pure returns (bytes16 w) {
        assembly ("memory-safe") {
            w := and(mload(add(add(b, 0x20), off)), not(sub(shl(128, 1), 1)))
        }
    }

    function _leBytes(uint256 x, uint256 len) internal pure returns (bytes memory b) {
        b = new bytes(len);
        for (uint256 j = 0; j < len; j++) {
            b[j] = bytes1(uint8(x >> (8 * j)));
        }
    }

    /// SIG_LEN bytes, word j/32 = keccak256(abi.encode(seed, j)).
    function _randomSig(bytes32 seed) internal pure returns (bytes memory sig) {
        sig = new bytes(SIG_LEN);
        assembly ("memory-safe") {
            // The last store runs 4 bytes past the data, inside the word-rounded allocation.
            for { let j := 0 } lt(j, SIG_LEN) { j := add(j, 0x20) } {
                mstore(0x00, seed)
                mstore(0x20, j)
                mstore(add(add(sig, 0x20), j), keccak256(0x00, 0x40))
            }
        }
    }

    /// The least counter c whose encoding d = Th(P, A_enc, msg ‖ LE32(c)) has digit sum T. Only a search:
    /// the digit sum here is popcount(d) + popcount(d & 0xAA…AA) (a 2-bit digit is its low bit plus twice
    /// its high bit), and callers check the spec model's own sum.
    function _grindCounter(bytes16 p, bytes16 adr, bytes memory msg) internal pure returns (uint256 c) {
        bytes memory buf = abi.encodePacked(p, adr, msg, bytes4(0));
        bool found;
        assembly ("memory-safe") {
            function popcount128(x) -> r {
                x := sub(x, and(shr(1, x), 0x55555555555555555555555555555555))
                x := add(and(x, 0x33333333333333333333333333333333), and(shr(2, x), 0x33333333333333333333333333333333))
                x := and(add(x, shr(4, x)), 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F)
                r := and(shr(120, mul(x, 0x01010101010101010101010101010101)), 0xFF)
            }
            let len := mload(buf)
            let data := add(buf, 0x20)
            let ctr := add(data, sub(len, 4)) // the last 4 bytes: LE32(c)
            for {} lt(c, 0x100000000) { c := add(c, 1) } {
                mstore8(ctr, c)
                mstore8(add(ctr, 1), shr(8, c))
                mstore8(add(ctr, 2), shr(16, c))
                mstore8(add(ctr, 3), shr(24, c))
                let x := shr(128, keccak256(data, len))
                if eq(add(popcount128(x), popcount128(and(x, 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA))), 128) {
                    found := 1
                    break
                }
            }
        }
        require(found, "no admissible counter below 2^32");
    }

    // ------------------------------------------------------------------
    // Spec model: verification in plain, byte-oriented Solidity, following EthLib's Lean definitions
    // (named below), independent of the Yul verifier's word packing. It returns the root a signature
    // folds to and each layer's codeword sum, WITHOUT the target-sum check, so the tests above can build
    // inputs on which only that check decides. testLeanKnownAnswer ties it to the Lean values.
    // ------------------------------------------------------------------

    /// Address.lean encodeAddress: LE32(lo) ‖ LE24(hi) ‖ (type + 32 step) ‖ layer ‖ LE32(tree) ‖ 0^3.
    function _adr(uint256 t, uint256 step, uint256 layer, uint256 tree, uint256 hi, uint256 lo)
        internal
        pure
        returns (bytes16)
    {
        require(t < 32 && step < 8 && layer < 256 && tree < 2 ** 32 && hi < 2 ** 24 && lo < 2 ** 32, "field range");
        return bytes16(
            abi.encodePacked(_leBytes(lo, 4), _leBytes(hi, 3), uint8(t + 32 * step), uint8(layer), _leBytes(tree, 4), bytes3(0))
        );
    }

    /// TweakableHash.lean th: H_0(P ‖ A ‖ M).
    function _th(bytes16 p, bytes16 a, bytes memory payload) internal pure returns (bytes16) {
        return bytes16(keccak256(abi.encodePacked(p, a, payload)));
    }

    /// Digest.lean messageDigest: D_c = H(P ‖ A_msg(c) ‖ m ‖ R), c = 0, 1; A_msg(c) = type 12, hi = c.
    function _digests(bytes16 p, bytes32 m, bytes16 rho) internal pure returns (bytes32 d0, bytes32 d1) {
        d0 = keccak256(abi.encodePacked(p, _adr(12, 0, 0, 0, 0, 0), m, rho));
        d1 = keccak256(abi.encodePacked(p, _adr(12, 0, 0, 0, 1, 0), m, rho));
    }

    /// Bits [start, start + len) of D_0 ‖ D_1 read as one 512-bit little-endian number, bit by bit.
    function _digestBits(bytes32 d0, bytes32 d1, uint256 start, uint256 len) internal pure returns (uint256 v) {
        for (uint256 t = 0; t < len; t++) {
            uint256 b = start + t;
            bytes32 w = b < 256 ? d0 : d1;
            v |= ((uint256(uint8(w[(b / 8) % 32])) >> (b % 8)) & 1) << t;
        }
    }

    /// digestIndex: the low h = 26 bits.
    function _idx(bytes32 d0, bytes32 d1) internal pure returns (uint256) {
        return _digestBits(d0, d1, 0, H);
    }

    /// digestLeaves: bits 26 + 10κ .. 35 + 10κ.
    function _forsLeaf(bytes32 d0, bytes32 d1, uint256 kappa) internal pure returns (uint256) {
        return _digestBits(d0, d1, H + A * kappa, A);
    }

    /// Types.lean OtsKey.ofIndex.
    function _otsKey(uint256 layer, uint256 idx) internal pure returns (uint256 tree, uint256 leaf) {
        uint256 below = layer == 0 ? 0 : layer == 1 ? 8 : 16;
        uint256 height = _layerHeight(layer);
        tree = idx >> (below + height);
        leaf = (idx >> below) % 2 ** height;
    }

    /// Fors.lean forsRecover / treeRecover, then forsKeyBytes: the two level-9 nodes of each tree, in the
    /// order t_0[0] ‖ t_0[1] ‖ … ‖ t_23[1] (768 bytes).
    function _modelForsKey(bytes16 p, bytes32 d0, bytes32 d1, uint256 idx, bytes memory sig)
        internal
        pure
        returns (bytes memory key)
    {
        for (uint256 kappa = 0; kappa < K; kappa++) {
            uint256 u = _forsLeaf(d0, d1, kappa);
            uint256 off = OFF_FORS_SK + FORS_STRIDE * kappa;
            // forsLeafHash: type 15, hi = κ + 64u, lo = idx.
            bytes16 node = _th(p, _adr(15, 0, 0, 0, kappa + 64 * u, idx), abi.encodePacked(_n(sig, off)));
            // Merkle.climb over levels 0..8: the parent of (level, j) is (level + 1, j / 2).
            uint256 j = u;
            for (uint256 level = 0; level < A - 1; level++) {
                bytes16 sib = _n(sig, off + 16 + 16 * level);
                bytes memory lr = j % 2 == 0 ? abi.encodePacked(node, sib) : abi.encodePacked(sib, node);
                // forsNodeHash: type 17, hi = κ + 64·(level + 16·index).
                node = _th(p, _adr(17, 0, 0, 0, kappa + 64 * ((level + 1) + 16 * (j / 2)), idx), lr);
                j /= 2;
            }
            bytes16 p9 = _n(sig, off + 16 + 16 * (A - 1));
            key = j % 2 == 0 ? abi.encodePacked(key, node, p9) : abi.encodePacked(key, p9, node);
        }
    }

    struct ModelLayer {
        uint256 x; // the 128-bit encoding, as a little-endian number (digit i = bits 2i, 2i+1)
        uint256 sum;
        bytes16 leaf;
        bytes16 root;
    }

    /// Verify.lean layerRoot without the codeword? check: Ots.lean otsLeaf (encode, chains, leaf), then
    /// Tree.lean fold, at OtsKey.ofIndex(layer, idx).
    function _modelLayer(bytes16 p, uint256 layer, uint256 idx, bytes memory msg, bytes memory sig)
        internal
        pure
        returns (ModelLayer memory r)
    {
        (uint256 tree, uint256 leaf) = _otsKey(layer, idx);
        uint256 off = _layerOff(layer);
        bytes16 enc = _th(p, _adr(4, 0, layer, tree, 0, leaf), abi.encodePacked(msg, _leBytes(_counterAt(sig, layer), 4)));
        for (uint256 j = 0; j < 16; j++) {
            r.x |= uint256(uint8(enc[j])) << (8 * j);
        }
        bytes memory ends;
        for (uint256 i = 0; i < 64; i++) {
            uint256 xi = (r.x >> (2 * i)) & 3;
            r.sum += xi;
            bytes16 val = _n(sig, off + 4 + 16 * i);
            for (uint256 mu = xi; mu < 3; mu++) {
                // addrChain: type 1, step mu, hi = i, lo = leaf.
                val = _th(p, _adr(1, mu, layer, tree, i, leaf), abi.encodePacked(val));
            }
            ends = abi.encodePacked(ends, val);
        }
        r.leaf = _th(p, _adr(2, 0, layer, tree, 0, leaf), ends);
        bytes16 cur = r.leaf;
        uint256 jj = leaf;
        for (uint256 level = 0; level < _layerHeight(layer); level++) {
            bytes16 sib = _n(sig, off + 1028 + 16 * level);
            bytes memory lr = jj % 2 == 0 ? abi.encodePacked(cur, sib) : abi.encodePacked(sib, cur);
            // addrNode: type 3, hi = level + 1, lo = j / 2.
            cur = _th(p, _adr(3, 0, layer, tree, level + 1, jj / 2), lr);
            jj /= 2;
        }
        r.root = cur;
    }

    function _modelRoot(bytes32 pkSeed, bytes32 m, bytes memory sig)
        internal
        pure
        returns (bytes32 root, uint256[3] memory sums)
    {
        bytes16 p = bytes16(pkSeed); // pkSeed = P ‖ 0^16
        (bytes32 d0, bytes32 d1) = _digests(p, m, _n(sig, 0));
        uint256 idx = _idx(d0, d1);
        bytes memory msg = _modelForsKey(p, d0, d1, idx, sig);
        for (uint256 layer = 0; layer < 3; layer++) {
            ModelLayer memory r = _modelLayer(p, layer, idx, msg, sig);
            sums[layer] = r.sum;
            msg = abi.encodePacked(r.root);
        }
        root = bytes32(bytes16(msg));
    }
}
