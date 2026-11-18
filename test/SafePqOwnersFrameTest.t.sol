// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "./helpers/SafePqHarness.sol";

/// @notice End-to-end EIP-8141 frame transactions for a Safe with post-quantum owners:
///         `[self_verify, SENDER -> Safe.execTransaction]` sent from an owner account.
///
///         forge/revm has no EIP-8141, so a transaction is run in two halves:
///           * the VERIFY frame runs in test/py/frame8141_emu.py (`exec`): the real deployed
///             code of the owner account, of the SphincsFrameVerify module and of the
///             leanSphincs-f verifier, in a metered EVM that implements the EIP-8141
///             instructions as the EIP text of ethereum/EIPs master dc5d5fa688b7 (2026-11-01)
///             defines them. The verifier call it made is replayed natively here and must give
///             the same answer for the same gas;
///           * the SENDER frame runs natively, only after the VERIFY frame approved: a call to
///             the frame's target with the frame's data and value, with `msg.sender` and
///             `tx.origin` both the sender (in a SENDER frame ORIGIN is the frame's caller).
///             The target is an unmodified Safe (v1.4.1, v1.5.0, main), with owner accounts as
///             owners.
///         The transactions come from test/fixtures/safe_pq_owners_frame.json, built by the
///         tooling in script/safe_pq_owners.py (regenerate with test/py/gen_safe_pq_fixture.py).
///         Its keys, addresses and chain id are installed in setUp.
///
///         Security invariants of docs/safe-pq-owners.md covered here:
///           1. test_Verify_RejectsAnEntryWithAnExplicitMsg, test_Verify_UsesTheCanonicalHash
///           2. test_Verify_RejectsAnEntryWithAnExplicitMsg (a valid signature over a supplied
///              digest approves nothing)
///           5. test_CoSignatureIsNotAFrameWitness, test_FrameWitnessIsNotACoSignature_*
abstract contract SafePqOwnersFrameBase is SafePqHarness {
    string constant EMU = "test/py/frame8141_emu.py";
    string constant FX = "test/fixtures/safe_pq_owners_frame.json";

    uint8 constant OUT_HALT = 0;
    uint8 constant OUT_REVERT = 1;
    uint8 constant OUT_APPROVE = 2;
    uint256 constant MODE_VERIFY = 1;
    uint256 constant MODE_SENDER = 2;
    uint256 constant MAX_VERIFY_GAS = 100_000;
    /// Gas of the sender's VERIFY frame outside the verifier's own call frame.
    uint256 constant VERIFY_FRAME_OVERHEAD = 7_068;
    bytes4 constant MAGIC_HASH = 0x1626ba7e;

    struct Frame {
        uint256 mode;
        uint256 flags;
        address target;
        uint256 value;
        uint256 execLimit;
        uint256 stateLimit;
        bytes data;
        bytes32 sigHash;
        address sender;
    }

    /// One VERIFY frame in the emulator.
    struct VerifyRun {
        uint8 outcome;
        uint256 scope;
        uint256 gasUsed;
        address staticTo; // the frame's last STATICCALL: the verifier call
        bytes staticData;
        uint256 staticGas;
        bytes staticRet;
        string violations; // public-mempool trace-rule violations
        string detail;
    }

    struct TxResult {
        bool valid; // every VERIFY frame approved
        uint256 verifyGas; // VERIFY frames, EIP-8141 accounting (emulator)
        uint256 senderGas; // SENDER frames, entry access charge + native execution (revm)
        bool senderOk; // every SENDER frame succeeded
        string detail;
    }

    function _lib() internal pure virtual returns (string memory);

    string fx;
    address[5] owner;
    address recipient;
    address singleton;
    ISafeLike safe23;
    ISafeLike safe35;

    function setUp() public {
        fx = vm.readFile(FX);
        vm.chainId(vm.parseJsonUint(fx, ".chain_id"));
        recipient = vm.parseJsonAddress(fx, ".recipient");
        vm.deal(recipient, 1); // an existing account: paying it creates no state

        // The verifier at the fixture's address; the module wherever it lands (no hash names it).
        address v = vm.parseJsonAddress(fx, ".verifier");
        deployCodeTo("LeanSphincs-FAsm.sol:LeanSphincsFAsm", v);
        verifier = LeanSphincsFAsm(v);
        bytes memory initcode =
            vm.parseJsonBytes(vm.readFile("out/SphincsFrameVerify.yul/SphincsFrameVerify.json"), ".bytecode.object");
        frameModule = _create(initcode);

        for (uint256 i = 0; i < 5; i++) {
            string memory o = string.concat(".owners[", vm.toString(i), "].");
            owner[i] = vm.parseJsonAddress(fx, string.concat(o, "address"));
            deployCodeTo(
                "SphincsOwnerAccount.sol:SphincsOwnerAccount",
                abi.encode(
                    vm.parseJsonBytes32(fx, string.concat(o, "pkSeed")),
                    vm.parseJsonBytes32(fx, string.concat(o, "pkRoot")),
                    v,
                    frameModule
                ),
                owner[i]
            );
            vm.deal(owner[i], 1 ether); // gas money: the sender pays for its own frame transaction
        }

        singleton = _create(_safeArtifact(string.concat(_lib(), "/contracts/Safe.sol"), "Safe"));
        address factory =
            _create(_safeArtifact(string.concat(_lib(), "/contracts/proxies/SafeProxyFactory.sol"), "SafeProxyFactory"));
        safe23 = _installSafe(factory, "2of3", 3);
        safe35 = _installSafe(factory, "3of5", 5);
    }

    /// A real SafeProxy at the fixture's address: the code of a proxy the real factory just
    /// created, pointed at the real singleton, then `setup` with the owner accounts. The
    /// fixture's Safe transactions are for Safe nonce 1 (a Safe that has executed before, so
    /// its nonce slot exists), hence the nonce slot (5 in SafeStorage) is set to 1.
    function _installSafe(address factory, string memory key, uint256 n) internal returns (ISafeLike safe) {
        string memory k = string.concat(".safes['", key, "'].");
        address at = vm.parseJsonAddress(fx, string.concat(k, "address"));
        address proxy = ISafeProxyFactoryLike(factory).createProxyWithNonce(singleton, "", n);
        vm.etch(at, proxy.code);
        vm.store(at, bytes32(0), bytes32(uint256(uint160(singleton))));
        address[] memory os = new address[](n);
        for (uint256 i = 0; i < n; i++) os[i] = owner[i];
        safe = ISafeLike(at);
        safe.setup(os, vm.parseJsonUint(fx, string.concat(k, "threshold")), address(0), "", address(0), address(0), 0, payable(address(0)));
        vm.store(at, bytes32(uint256(5)), bytes32(uint256(1)));
        assertEq(safe.nonce(), 1, "Safe nonce slot");
        assertEq(safe.getThreshold(), vm.parseJsonUint(fx, string.concat(k, "threshold")));
        vm.deal(at, 10 ether);
    }

    // ───────────────────────────── emulator ─────────────────────────────

    function _emu(string[] memory args) internal returns (bytes memory) {
        string[] memory c = new string[](args.length + 3);
        c[0] = "python3";
        c[1] = "-I";
        c[2] = EMU;
        for (uint256 i; i < args.length; ++i) c[i + 3] = args[i];
        return vm.ffi(c);
    }

    function _scenario(string memory cmd, string memory sc) internal returns (bytes memory) {
        string[] memory a = new string[](3);
        (a[0], a[1], a[2]) = (cmd, FX, sc);
        return _emu(a);
    }

    function _frame(string memory sc, uint256 i) internal returns (Frame memory f) {
        string[] memory a = new string[](4);
        (a[0], a[1], a[2], a[3]) = ("framex", FX, sc, vm.toString(i));
        (f.mode, f.flags, f.target, f.value, f.execLimit, f.stateLimit, f.data, f.sigHash, f.sender) =
            abi.decode(_emu(a), (uint256, uint256, address, uint256, uint256, uint256, bytes, bytes32, address));
    }

    function _witness(string memory sc) internal returns (bytes memory) {
        string[] memory a = new string[](4);
        (a[0], a[1], a[2], a[3]) = ("witness", FX, sc, "0");
        return abi.decode(_emu(a), (bytes));
    }

    function _code(address a) internal view returns (string memory) {
        return string.concat(vm.toString(a), "=", vm.toString(a.code));
    }

    /// Frame `fi` of scenario `sc` in the metered EVM, with `limit` as its execution gas
    /// ("-" for the frame's own limit).
    function _execVerify(string memory sc, uint256 fi, string memory limit, address target) internal returns (VerifyRun memory r) {
        string[] memory a = new string[](8);
        (a[0], a[1], a[2], a[3], a[4]) = ("exec", FX, sc, vm.toString(fi), limit);
        (a[5], a[6], a[7]) = (_code(target), _code(frameModule), _code(address(verifier)));
        (r.outcome, r.scope, r.gasUsed, r.staticTo, r.staticData, r.staticGas, r.staticRet, r.violations, r.detail) =
            abi.decode(_emu(a), (uint8, uint256, uint256, address, bytes, uint256, bytes, string, string));
    }

    /// The verifier call the emulated frame made, replayed natively: same answer, same gas.
    function _replayVerifierCall(VerifyRun memory r) internal {
        assertEq(r.staticTo, address(verifier), "the frame called another verifier");
        (bool ok, bytes memory ret) = r.staticTo.staticcall(r.staticData);
        uint256 native = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok, "native verifier call");
        assertEq(keccak256(ret), keccak256(r.staticRet), "emulator and revm disagree on the verifier's answer");
        assertEq(r.staticGas, native, "emulator and revm disagree on the verifier's gas");
    }

    /// The whole transaction, frame by frame, as EIP-8141's Behavior section orders it.
    function _runTransaction(string memory sc, uint256 frames) internal returns (TxResult memory res) {
        bool senderApproved;
        res.valid = true;
        res.senderOk = true;
        for (uint256 i = 0; i < frames; i++) {
            Frame memory f = _frame(sc, i);
            if (f.mode == MODE_VERIFY) {
                VerifyRun memory r = _execVerify(sc, i, "-", f.target);
                res.verifyGas += r.gasUsed;
                if (r.outcome != OUT_APPROVE) {
                    // A VERIFY frame that fails makes the transaction invalid: nothing runs.
                    res.valid = false;
                    res.detail = r.detail;
                    return res;
                }
                assertEq(r.violations, "", "public-mempool trace rules");
                _replayVerifierCall(r);
                if (r.scope & 2 != 0) senderApproved = true;
            } else {
                assertEq(f.mode, MODE_SENDER, "DEFAULT frames are not used here");
                assertTrue(senderApproved, "SENDER frame before the sender approved: invalid transaction");
                vm.prank(f.sender, f.sender);
                (bool ok,) = f.target.call{value: f.value, gas: f.execLimit - 2600}(f.data);
                // The frame's gas: its target's (cold) access at frame entry, then the call.
                res.senderGas += 2600 + vm.lastCallGas().gasTotalUsed;
                if (!ok) res.senderOk = false;
            }
        }
    }

    // ───────────────────────────── the Safe transactions ─────────────────────────────

    function _safeTx(string memory sc) internal view returns (SafeTx memory t, uint256 nonce) {
        string memory k = string.concat(".scenarios.", sc, ".safeTx.");
        t.to = vm.parseJsonAddress(fx, string.concat(k, "to"));
        t.value = vm.parseJsonUint(fx, string.concat(k, "value"));
        t.data = vm.parseJsonBytes(fx, string.concat(k, "data"));
        t.operation = uint8(vm.parseJsonUint(fx, string.concat(k, "operation")));
        t.safeTxGas = vm.parseJsonUint(fx, string.concat(k, "safeTxGas"));
        t.baseGas = vm.parseJsonUint(fx, string.concat(k, "baseGas"));
        t.gasPrice = vm.parseJsonUint(fx, string.concat(k, "gasPrice"));
        t.gasToken = vm.parseJsonAddress(fx, string.concat(k, "gasToken"));
        t.refundReceiver = vm.parseJsonAddress(fx, string.concat(k, "refundReceiver"));
        nonce = vm.parseJsonUint(fx, string.concat(k, "nonce"));
    }

    /// What the tooling produced, against the Safe and against this repo's Solidity encoders.
    function _checkTooling(string memory sc, ISafeLike safe, uint256 cosigners) internal returns (bytes32 h) {
        string memory k = string.concat(".scenarios.", sc, ".");
        (SafeTx memory t, uint256 nonce) = _safeTx(sc);
        assertEq(nonce, safe.nonce(), "fixture Safe nonce");
        h = vm.parseJsonBytes32(fx, string.concat(k, "safeTxHash"));
        assertEq(h, _getTransactionHash(safe, t, nonce), "tooling Safe transaction hash vs Safe.getTransactionHash");
        assertEq(h, _safeTxHash(address(safe), t, nonce), "tooling Safe transaction hash vs EIP-712 by hand");

        address sender = owner[vm.parseJsonUint(fx, string.concat(k, "senderOwner"))];
        uint256[] memory who = vm.parseJsonUintArray(fx, string.concat(k, "coSigners"));
        bytes[] memory sigs = vm.parseJsonBytesArray(fx, string.concat(k, "coSignatures"));
        assertEq(who.length, cosigners);
        Entry[] memory es = new Entry[](cosigners + 1);
        es[0] = _preValidated(sender, h); // s = the Safe transaction hash
        for (uint256 i = 0; i < cosigners; i++) {
            es[i + 1] = _contractSig(owner[who[i]], sigs[i]);
            assertEq(SphincsOwnerAccount(payable(owner[who[i]])).isValidSignature(h, sigs[i]), MAGIC_HASH, "co-signature");
        }
        bytes memory blob = _blob(_sorted(es));
        assertEq(vm.parseJsonBytes(fx, string.concat(k, "safeSignatures")), blob, "tooling signatures bytes");
        assertEq(blob.length, (cosigners + 1) * 65 + cosigners * (32 + SIG_LEN));

        Frame memory f0 = _frame(sc, 0);
        Frame memory f1 = _frame(sc, 1);
        assertEq(f0.sender, sender);
        assertEq(f0.target, sender, "the VERIFY frame targets the sender");
        assertEq(f0.flags, 3, "self_verify");
        assertEq(f0.data, abi.encodeWithSignature("verifyFrameAndApprove(uint256)", uint256(0)));
        assertEq(f1.target, address(safe), "the SENDER frame targets the Safe");
        assertEq(f1.value, 0);
        assertEq(f1.data, _execCalldata(t, blob), "tooling execTransaction calldata");
        // One contract signature as the Safe Transaction Service receives it.
        assertEq(vm.parseJsonUint(fx, string.concat(k, "serviceSignatureBytes")), 65 + 32 + SIG_LEN);
        assertEq(65 + 32 + SIG_LEN, 4757);
    }

    function _endToEnd(string memory sc, ISafeLike safe, uint256 cosigners, uint256 expectedFloor) internal {
        _checkTooling(sc, safe, cosigners);

        // Public mempool: [self_verify] is the whole validation prefix, and it declares less
        // than MAX_VERIFY_GAS including the 100 gas of the one ARBITRARY signature entry.
        (bool ok, uint256 prefixLen, uint256 prefixGas, string memory problems) =
            abi.decode(_scenario("mempool", sc), (bool, uint256, uint256, string));
        assertTrue(ok, problems);
        assertEq(prefixLen, 1, "validation prefix is the one self_verify frame");
        assertEq(prefixGas, 60_100, "declared prefix gas");
        assertLe(prefixGas, MAX_VERIFY_GAS);

        uint256 safeBalance = address(safe).balance;
        uint256 recipientBalance = recipient.balance;
        TxResult memory res = _runTransaction(sc, 2);
        assertTrue(res.valid, res.detail);
        assertTrue(res.senderOk, "execTransaction");
        assertEq(safe.nonce(), 2, "Safe nonce");
        assertEq(recipient.balance - recipientBalance, 1000);
        assertEq(safeBalance - address(safe).balance, 1000);

        (uint256 intrinsic, uint256 floor,,,, uint256 maxGas) =
            abi.decode(_scenario("gas", sc), (uint256, uint256, uint256, uint256, uint256, uint256));
        uint256 execution = intrinsic + res.verifyGas + res.senderGas;
        emit log_named_uint(string.concat("[", sc, "] VERIFY frame gas (emulator, EIP-8141 accounting)"), res.verifyGas);
        emit log_named_uint(string.concat("[", sc, "] SENDER frame gas (2,600 entry + revm execTransaction)"), res.senderGas);
        emit log_named_uint(string.concat("[", sc, "] intrinsic gas"), intrinsic);
        emit log_named_uint(string.concat("[", sc, "] execution component (intrinsic + frames)"), execution);
        emit log_named_uint(string.concat("[", sc, "] calldata floor = gas used (no state gas)"), floor);
        emit log_named_uint(string.concat("[", sc, "] max_gas (what max_fee must cover)"), maxGas);
        // The transaction is floor-bound: it pays the calldata floor, whatever the frames used.
        assertLt(execution, floor, "the calldata floor sets the gas used");
        assertEq(floor, expectedFloor, "calldata floor");
        // 44,546 is the verifier's frame for the costliest admissible signature (LeanSphincsFTest).
        assertLe(res.verifyGas, 44_546 + VERIFY_FRAME_OVERHEAD, "VERIFY frame gas ceiling");
    }

    function test_EndToEnd_TwoOfThree() public {
        _endToEnd("safe_2of3", safe23, 1, 647_674);
    }

    function test_EndToEnd_ThreeOfFive() public {
        _endToEnd("safe_3of5", safe35, 2, 952_826);
    }

    // ───────────────────────────── invariant 5 ─────────────────────────────

    /// A frame witness is not a Safe co-signature: the Safe rejects the sender's real witness
    /// when it is presented as that owner's contract signature. (The account does answer the
    /// magic value for the frame's own signature hash, which no Safe transaction hashes to:
    /// one is keccak256(0x06 ‖ rlp(..)), the other keccak256(0x19 0x01 ‖ ..).)
    function test_FrameWitnessIsNotACoSignature() public {
        bytes32 h = _checkTooling("safe_2of3", safe23, 1);
        (SafeTx memory t,) = _safeTx("safe_2of3");
        Frame memory f0 = _frame("safe_2of3", 0);
        bytes memory witness = _witness("safe_2of3");
        address sender = owner[vm.parseJsonUint(fx, ".scenarios.safe_2of3.senderOwner")];
        address cosigner = owner[vm.parseJsonUintArray(fx, ".scenarios.safe_2of3.coSigners")[0]];
        bytes memory cosig = vm.parseJsonBytesArray(fx, ".scenarios.safe_2of3.coSignatures")[0];

        SphincsOwnerAccount a = SphincsOwnerAccount(payable(sender));
        assertEq(a.isValidSignature(f0.sigHash, witness), MAGIC_HASH, "the witness is the key's signature over the sig hash");
        assertEq(a.isValidSignature(h, witness), bytes4(0xffffffff), "and not over the Safe transaction hash");
        assertEq(a.isValidSignature(_safeTxPreimage(address(safe23), t, 1), witness), bytes4(0xffffffff), "legacy form");

        // A relayer presents the witness as the sender's contract signature, next to the real
        // co-signature: the Safe refuses it.
        bytes memory sigs = _blob(_sorted(_entries(_contractSig(sender, witness), _contractSig(cosigner, cosig))));
        address relayer = makeAddr("relayer");
        vm.expectRevert(bytes("GS024"));
        vm.prank(relayer, relayer);
        safe23.execTransaction(t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas, t.gasPrice, t.gasToken, payable(t.refundReceiver), sigs);

        // Control: with the sender's real signature over the Safe transaction hash it executes.
        bytes memory real = _witness("cosig_as_witness");
        sigs = _blob(_sorted(_entries(_contractSig(sender, real), _contractSig(cosigner, cosig))));
        vm.prank(relayer, relayer);
        assertTrue(
            safe23.execTransaction(t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas, t.gasPrice, t.gasToken, payable(t.refundReceiver), sigs)
        );
    }

    /// A Safe co-signature is not a frame witness: the same transaction as safe_2of3 with the
    /// sender key's valid signature over the Safe transaction hash in the witness slot. The
    /// VERIFY frame reverts, so the transaction is invalid and the Safe is never called.
    function test_CoSignatureIsNotAFrameWitness() public {
        bytes32 h = vm.parseJsonBytes32(fx, ".scenarios.cosig_as_witness.witnessSignedOver");
        assertEq(h, vm.parseJsonBytes32(fx, ".scenarios.safe_2of3.safeTxHash"));
        Frame memory f0 = _frame("cosig_as_witness", 0);
        assertEq(f0.sigHash, _frame("safe_2of3", 0).sigHash, "same transaction, another witness of the same length");
        bytes memory w = _witness("cosig_as_witness");
        assertEq(SphincsOwnerAccount(payable(f0.sender)).isValidSignature(h, w), MAGIC_HASH, "a valid co-signature of the sender's key");

        TxResult memory res = _runTransaction("cosig_as_witness", 2);
        assertFalse(res.valid, "the VERIFY frame must not approve");
        assertEq(res.detail, "REVERT invalid SPHINCS+ signature");
        assertEq(safe23.nonce(), 1, "the Safe was not called");
    }

    // ───────────────────────────── invariant 1 ─────────────────────────────

    /// The VERIFY frame verifies over TXPARAM(0x08) and nothing else: another owner's valid
    /// signature over the right hash fails, and the sender's valid witness for one transaction
    /// fails on a transaction that differs only in a SENDER frame argument
    /// (compute_sig_hash covers every frame).
    function test_Verify_UsesTheCanonicalHash() public {
        VerifyRun memory r = _execVerify("wrong_key", 0, "-", _frame("wrong_key", 0).target);
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT invalid SPHINCS+ signature");
        // That witness is a good signature over the same hash, by owner 0's key.
        bytes32 d = _frame("wrong_key", 0).sigHash;
        assertEq(SphincsOwnerAccount(payable(owner[0])).isValidSignature(d, _witness("wrong_key")), MAGIC_HASH);

        Frame memory f = _frame("tampered_frame", 0);
        bytes32 signedOver = vm.parseJsonBytes32(fx, ".scenarios.tampered_frame.witnessSignedOver");
        assertTrue(f.sigHash != signedOver, "the changed SENDER frame changes the signature hash");
        assertEq(signedOver, _frame("safe_2of3", 0).sigHash);
        r = _execVerify("tampered_frame", 0, "-", f.target);
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT invalid SPHINCS+ signature");
        // What reached the verifier is the transaction's own hash, not the one the witness signs.
        assertEq(this.verifyMessage(r.staticData), f.sigHash, "message = TXPARAM(0x08)");
    }

    /// Invariants 1 and 2: a signature entry with an explicit msg is refused before the
    /// verifier is called, although its bytes are this key's valid signature over that msg.
    /// So a signature over a digest somebody supplies never approves a transaction.
    function test_Verify_RejectsAnEntryWithAnExplicitMsg() public {
        bytes32 digest = vm.parseJsonBytes32(fx, ".scenarios.explicit_msg.witnessSignedOver");
        Frame memory f = _frame("explicit_msg", 0);
        bytes memory sig = _witness("explicit_msg");
        assertEq(SphincsOwnerAccount(payable(f.sender)).isValidSignature(digest, sig), MAGIC_HASH, "valid over the explicit digest");

        VerifyRun memory r = _execVerify("explicit_msg", 0, "-", f.target);
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT not an ARBITRARY tx signature");
        assertEq(r.staticData.length, 0, "the verifier was never called");

        r = _execVerify("explicit_msg_scan", 0, "-", f.target);
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT no ARBITRARY tx signature");
        assertEq(r.staticData.length, 0, "the verifier was never called");
    }

    function verifyMessage(bytes calldata verifierCalldata) external pure returns (bytes32) {
        // verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig)
        return bytes32(verifierCalldata[0x44:0x64]);
    }

    // ───────────────────────────── the VERIFY frame ─────────────────────────────

    /// What the sender's VERIFY frame does and costs: it passes this account's key and
    /// TXPARAM(0x08) to the verifier, approves execution and payment, and breaks no trace rule.
    function test_Verify_SenderFrame() public {
        Frame memory f = _frame("safe_2of3", 0);
        VerifyRun memory r = _execVerify("safe_2of3", 0, "-", f.target);
        assertEq(r.outcome, OUT_APPROVE, r.detail);
        assertEq(r.scope, 3, "APPROVE_EXECUTION_AND_PAYMENT");
        assertEq(r.violations, "");
        SphincsOwnerAccount a = SphincsOwnerAccount(payable(f.target));
        assertEq(
            r.staticData,
            abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", a.pkSeed(), a.pkRoot(), f.sigHash, _witness("safe_2of3")),
            "verifier calldata: the account's key, TXPARAM(0x08), the witness"
        );
        _replayVerifierCall(r);
        emit log_named_uint("VERIFY frame gas (entry 100 + account + module + verifier)", r.gasUsed);
        emit log_named_uint("  of which the verifier's own frame", r.staticGas);
        // Everything but the verifier: the frame's entry charge (100, tx.sender is warm), the
        // account's dispatch, two cold accesses (module and verifier, 2 x 2,600), the copy of
        // the 4,660-byte witness and the memory it needs. It does not depend on the signature.
        // (forge 1.5.1, solc 0.8.33, via-ir; re-measure if the toolchain changes.)
        assertEq(r.gasUsed - r.staticGas, VERIFY_FRAME_OVERHEAD, "frame overhead on top of the verifier");

        // The 63/64 rule at two call depths: the frame needs more than it ends up using.
        VerifyRun memory tight = _execVerify("safe_2of3", 0, vm.toString(r.gasUsed), f.target);
        assertTrue(tight.outcome != OUT_APPROVE, "the gas used is not a sufficient limit");
        VerifyRun memory enough = _execVerify("safe_2of3", 0, vm.toString(r.gasUsed + 1_500), f.target);
        assertEq(enough.outcome, OUT_APPROVE, enough.detail);
        assertEq(enough.gasUsed, r.gasUsed, "gas used does not depend on the limit");
    }

    /// The public-mempool structural rules on the two shapes that break them.
    function test_Mempool_RejectsOversizedOrMisplacedVerifyFrames() public {
        (bool ok,, uint256 gas, string memory problems) =
            abi.decode(_scenario("mempool", "verify_gas_300k"), (bool, uint256, uint256, string));
        assertFalse(ok, "a 300,000-gas VERIFY frame is over MAX_VERIFY_GAS");
        assertEq(gas, 300_100);
        assertEq(problems, "prefix gas 300100 exceeds MAX_VERIFY_GAS");

        (ok,,, problems) = abi.decode(_scenario("mempool", "verify_after_prefix"), (bool, uint256, uint256, string));
        assertFalse(ok);
        assertEq(problems, "VERIFY frame after the prefix");
    }

    /// ETH held by an owner account is spent through a SENDER frame with a value. The frame
    /// does not enter the account's code, which has no way to send anything.
    function test_Sweep_ValueLeavesThroughASenderFrame() public {
        Frame memory f1 = _frame("sweep", 1);
        assertEq(f1.data.length, 0);
        assertEq(f1.target, recipient);
        uint256 before = f1.sender.balance;
        uint256 recipientBefore = recipient.balance;
        TxResult memory res = _runTransaction("sweep", 2);
        assertTrue(res.valid, res.detail);
        assertTrue(res.senderOk);
        assertEq(before - f1.sender.balance, f1.value);
        assertEq(recipient.balance - recipientBefore, f1.value);
        (, uint256 floor,,,,) = abi.decode(_scenario("gas", "sweep"), (uint256, uint256, uint256, uint256, uint256, uint256));
        emit log_named_uint("[sweep] calldata floor (plain transfer from an owner account)", floor);
    }

    // ───────────────────────────── the emulator against revm ─────────────────────────────

    function _call(uint256 gas, address caller, address to, bytes memory data, string memory warm, address[] memory codes)
        internal
        returns (bool ok, uint256 gasUsed, bytes memory ret)
    {
        string[] memory a = new string[](6 + codes.length);
        (a[0], a[1], a[2], a[3]) = ("call", vm.toString(gas), vm.toString(caller), vm.toString(to));
        (a[4], a[5]) = (vm.toString(data), warm);
        for (uint256 i = 0; i < codes.length; i++) a[6 + i] = _code(codes[i]);
        string memory detail;
        (ok, gasUsed, ret, detail) = abi.decode(_emu(a), (bool, uint256, bytes, string));
    }

    /// The metered EVM that produces the VERIFY-frame figure, on calls revm can run too: the
    /// verifier alone (accept, reject, revert) and isValidSignature through the account with
    /// the verifier warm and cold. Gas and return data must match revm exactly.
    function test_Emulator_MatchesRevmGas() public {
        Frame memory f = _frame("safe_2of3", 0);
        SphincsOwnerAccount a = SphincsOwnerAccount(payable(f.target));
        bytes memory w = _witness("safe_2of3");
        bytes memory bad = bytes.concat(w);
        bad[100] = bytes1(uint8(bad[100]) ^ 0x01);
        address[] memory one = new address[](1);
        one[0] = address(verifier);
        address[] memory two = new address[](2);
        (two[0], two[1]) = (address(a), address(verifier));

        bytes[3] memory cases = [
            abi.encodeCall(verifier.verify, (a.pkSeed(), a.pkRoot(), f.sigHash, w)), // true
            abi.encodeCall(verifier.verify, (a.pkSeed(), a.pkRoot(), f.sigHash, bad)), // false
            abi.encodeCall(verifier.verify, (a.pkSeed(), a.pkRoot(), f.sigHash, hex"00")) // revert: length
        ];
        for (uint256 i = 0; i < cases.length; i++) {
            (bool nOk, bytes memory nRet) = address(verifier).staticcall{gas: 200_000}(cases[i]);
            uint256 native = vm.lastCallGas().gasTotalUsed;
            (bool eOk, uint256 eGas, bytes memory eRet) = _call(200_000, address(this), address(verifier), cases[i], "-", one);
            assertEq(eOk, nOk, "verifier: success");
            assertEq(eRet, nRet, "verifier: return data");
            assertEq(eGas, native, "verifier: gas");
        }

        // isValidSignature through the account, the verifier warm from the calls above.
        bytes memory q = abi.encodeWithSelector(MAGIC_HASH, f.sigHash, w);
        (bool ok, bytes memory ret) = address(a).staticcall{gas: 200_000}(q);
        uint256 warm = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok);
        (bool eOk2, uint256 eWarm, bytes memory eRet2) =
            _call(200_000, address(this), address(a), q, vm.toString(address(verifier)), two);
        assertTrue(eOk2);
        assertEq(eRet2, ret);
        assertEq(eWarm, warm, "isValidSignature, warm verifier: gas");
        emit log_named_uint("isValidSignature gas, call frame, verifier warm", warm);
    }

    /// The same with a cold verifier: nothing has touched it in this transaction, so the
    /// account's STATICCALL pays the 2,600 cold access, as the first co-signer check of a
    /// Safe transaction does.
    function test_Emulator_MatchesRevmGas_ColdVerifier() public {
        Frame memory f = _frame("safe_2of3", 0);
        bytes memory q = abi.encodeWithSelector(MAGIC_HASH, f.sigHash, _witness("safe_2of3"));
        address[] memory two = new address[](2);
        (two[0], two[1]) = (f.target, address(verifier));

        (bool ok, bytes memory ret) = f.target.staticcall{gas: 200_000}(q);
        uint256 cold = vm.lastCallGas().gasTotalUsed;
        assertTrue(ok);
        (bool eOk, uint256 eCold, bytes memory eRet) = _call(200_000, address(this), f.target, q, "-", two);
        assertTrue(eOk);
        assertEq(eRet, ret);
        assertEq(eCold, cold, "isValidSignature, cold verifier: gas");

        (ok,) = f.target.staticcall{gas: 200_000}(q);
        assertEq(cold - vm.lastCallGas().gasTotalUsed, 2_500, "cold minus warm account access");
        emit log_named_uint("isValidSignature gas, call frame, verifier cold", cold);
    }
}

contract SafePqOwnersFrame141Test is SafePqOwnersFrameBase {
    function _lib() internal pure override returns (string memory) {
        return "lib/safe-smart-account-1.4.1";
    }
}

contract SafePqOwnersFrame150Test is SafePqOwnersFrameBase {
    function _lib() internal pure override returns (string memory) {
        return "lib/safe-smart-account-1.5.0";
    }
}

contract SafePqOwnersFrameMainTest is SafePqOwnersFrameBase {
    function _lib() internal pure override returns (string memory) {
        return "lib/safe-smart-account-main";
    }
}
