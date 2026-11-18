// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/LeanSphincs-FAsm.sol";
import "../src/SphincsOwnerAccount.sol";
import {CalldataRecorder} from "./SphincsFrameAccountC13Test.t.sol";
import {OpcodeScan} from "./helpers/OpcodeScan.sol";

/// @notice Unit tests for SphincsOwnerAccount with the leanSphincs-f verifier: the contract
///         surface, the opcodes it can execute, the VERIFY-frame entry points up to the module
///         boundary, and `isValidSignature` in both forms.
///
///         Security invariants of docs/safe-pq-owners.md covered here (the Safe and frame
///         transaction sides are in SafePqOwnersTest and SafePqOwnersFrameTest):
///           1. test_VerifyFrame_ForwardsOnlyKeysAndIndex, test_FrameModule_VerifiesOnlyTheCanonicalHash
///           2. test_Surface_IsExactlyTheSpecifiedFunctions, test_Code_HasNoCallAndNoFrameOpcode
///           3. test_Code_CannotWriteStateOrCallOut, test_NoEntryPointTouchesStorage
///           4. test_IsValidSignature_* and test_Code_IsValidSignatureIsAPureCheck
contract SphincsOwnerAccountTest is Test {
    LeanSphincsFAsm verifier;
    address frameModule;
    SphincsOwnerAccount account; // key of fixture vector 0

    address constant ENTRY_POINT = address(0xaa);
    bytes4 constant MAGIC_HASH = 0x1626ba7e;
    bytes4 constant MAGIC_DATA = 0x20c13b0b;
    bytes4 constant INVALID = 0xffffffff;

    string constant FIXTURE = "test/fixtures/leansphincs-f-keccak-kat.json";
    string constant LSFK = "signers/leansphincs-f-keccak/target/release/lsfk";
    // Prints `fresh`, `missing`, or `stale` when a crate source is newer than the binary. Same
    // probe as LeanSphincsFTest.
    string constant LSFK_PROBE = "d=signers/leansphincs-f-keccak; b=$d/target/release/lsfk; "
        "if [ ! -x $b ]; then echo missing; "
        "elif [ -n \"$(find $d/Cargo.toml $d/Cargo.lock $d/src -newer $b \\( -name '*.rs' -o -name 'Cargo.*' \\) "
        "2>/dev/null | head -n 1)\" ]; then echo stale; else echo fresh; fi";

    // Ceiling on the gas one isValidSignature(bytes32,bytes) call spends in its own call frame,
    // verifier included, with the verifier already warm. It is the verifier's frame (at most
    // 44,546 for any admissible signature, LeanSphincsFTest) plus this account's dispatch, the
    // copy of the 4,660-byte signature and the warm STATICCALL: 1,664 more than the verifier's
    // own frame on every fixture vector. Measured 45,641..45,797 on the fixture (forge 1.5.1,
    // solc 0.8.33, via-ir); a cold verifier adds 2,500.
    uint256 constant IS_VALID_SIGNATURE_GAS_MAX = 46_300;

    function setUp() public {
        verifier = new LeanSphincsFAsm();
        frameModule = _deployFrameModule();
        (bytes32 pkSeed, bytes32 pkRoot,,) = _vector(0);
        account = _newAccount(pkSeed, pkRoot);
    }

    function _deployFrameModule() internal returns (address addr) {
        bytes memory initcode =
            vm.parseJsonBytes(vm.readFile("out/SphincsFrameVerify.yul/SphincsFrameVerify.json"), ".bytecode.object");
        assembly {
            addr := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(addr != address(0), "module deploy failed");
    }

    function _newAccount(bytes32 pkSeed, bytes32 pkRoot) internal returns (SphincsOwnerAccount) {
        return new SphincsOwnerAccount(pkSeed, pkRoot, address(verifier), frameModule);
    }

    function _vector(uint256 i)
        internal
        view
        returns (bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig)
    {
        string memory json = vm.readFile(FIXTURE);
        string memory v = string.concat(".vectors[", vm.toString(i), "].");
        pkSeed = vm.parseJsonBytes32(json, string.concat(v, "pkSeed"));
        pkRoot = vm.parseJsonBytes32(json, string.concat(v, "pkRoot"));
        message = vm.parseJsonBytes32(json, string.concat(v, "message"));
        sig = vm.parseJsonBytes(json, string.concat(v, "sig"));
    }

    function _count() internal view returns (uint256 n) {
        string memory json = vm.readFile(FIXTURE);
        while (vm.keyExistsJson(json, string.concat(".vectors[", vm.toString(n), "]"))) n++;
    }

    // ───────────────────────────── construction ─────────────────────────────

    function test_Constructor_StoresImmutables() public view {
        (bytes32 pkSeed, bytes32 pkRoot,,) = _vector(0);
        assertEq(account.pkSeed(), pkSeed);
        assertEq(account.pkRoot(), pkRoot);
        assertEq(account.verifier(), address(verifier));
        assertEq(account.frameModule(), frameModule);
    }

    /// The same checks as SphincsFrameAccount.
    function test_Constructor_Guards() public {
        bytes32 good = bytes32(uint256(1) << 128);
        vm.expectRevert(SphincsOwnerAccount.NonCanonicalKey.selector);
        new SphincsOwnerAccount(bytes32(uint256(1)), good, address(verifier), frameModule);
        vm.expectRevert(SphincsOwnerAccount.NonCanonicalKey.selector);
        new SphincsOwnerAccount(good, bytes32((uint256(2) << 128) | 1), address(verifier), frameModule);
        vm.expectRevert(SphincsOwnerAccount.VerifierHasNoCode.selector);
        new SphincsOwnerAccount(good, good, makeAddr("eoa"), frameModule);
        vm.expectRevert(SphincsOwnerAccount.FrameModuleHasNoCode.selector);
        new SphincsOwnerAccount(good, good, address(verifier), makeAddr("eoa"));

        // A zero module is a co-signer-only account: it answers isValidSignature and can
        // never send a frame transaction.
        SphincsOwnerAccount cosigner = new SphincsOwnerAccount(good, good, address(verifier), address(0));
        vm.prank(ENTRY_POINT);
        vm.expectRevert(SphincsOwnerAccount.NoFrameModule.selector);
        cosigner.verifyFrameAndApprove();
        vm.prank(ENTRY_POINT);
        vm.expectRevert(SphincsOwnerAccount.NoFrameModule.selector);
        cosigner.verifyFrameAndApprove(0);
    }

    // ───────────────────────────── surface and code ─────────────────────────────

    /// Invariant 2 (and "nothing else"): the external surface is exactly the four getters, the
    /// two frame entry points, the two isValidSignature forms and receive(). Adding `execute`,
    /// `verifyAndApprove(bytes32,bytes,uint256)`, an `owner` getter or a fallback fails here.
    function test_Surface_IsExactlyTheSpecifiedFunctions() public {
        string memory artifact = vm.readFile("out/SphincsOwnerAccount.sol/SphincsOwnerAccount.json");
        string[] memory fns = vm.parseJsonKeys(artifact, ".methodIdentifiers");
        string[8] memory want = [
            "frameModule()",
            "isValidSignature(bytes,bytes)",
            "isValidSignature(bytes32,bytes)",
            "pkRoot()",
            "pkSeed()",
            "verifier()",
            "verifyFrameAndApprove()",
            "verifyFrameAndApprove(uint256)"
        ];
        assertEq(fns.length, want.length, "number of external functions");
        for (uint256 i = 0; i < want.length; i++) {
            bool found;
            for (uint256 j = 0; j < fns.length; j++) {
                if (keccak256(bytes(fns[j])) == keccak256(bytes(want[i]))) found = true;
            }
            assertTrue(found, string.concat("missing ", want[i]));
        }

        // No fallback: every other selector reverts, with or without value. These are the
        // ones SphincsFrameAccount has and this contract must not.
        bytes[4] memory absent = [
            abi.encodeWithSignature("execute(address,uint256,bytes)", address(this), uint256(0), bytes("")),
            abi.encodeWithSignature("verifyAndApprove(bytes32,bytes,uint256)", bytes32(0), bytes(""), uint256(3)),
            abi.encodeWithSignature("owner()"),
            hex"deadbeef"
        ];
        vm.deal(address(this), 1 ether);
        for (uint256 i = 0; i < absent.length; i++) {
            (bool ok,) = address(account).call(absent[i]);
            assertFalse(ok, "unknown selector must revert");
            vm.prank(address(account));
            (ok,) = address(account).call(absent[i]);
            assertFalse(ok, "unknown selector must revert for a self-call too");
            (ok,) = address(account).call{value: 1}(absent[i]);
            assertFalse(ok, "unknown selector with value must revert");
        }
    }

    /// Invariant 3: the deployed code has no instruction that writes state, creates a contract,
    /// emits a log, destroys the account or makes a state-changing call. The key, the verifier
    /// and the module are immutables in that code, so nothing can change them.
    function test_Code_CannotWriteStateOrCallOut() public view {
        OpcodeScan.Report memory r = OpcodeScan.scan(address(account).code, true);
        assertEq(r.count[0x55], 0, "SSTORE");
        assertEq(r.count[0x5d], 0, "TSTORE");
        assertEq(r.count[0xf1], 0, "CALL");
        assertEq(r.count[0xf2], 0, "CALLCODE");
        assertEq(r.count[0xf0], 0, "CREATE");
        assertEq(r.count[0xf5], 0, "CREATE2");
        assertEq(r.count[0xff], 0, "SELFDESTRUCT");
        for (uint256 op = 0xa0; op <= 0xa4; op++) assertEq(r.count[op], 0, "LOG");
        // The only outgoing calls: one STATICCALL (the verifier, in isValidSignature) and the
        // module DELEGATECALL, once per verifyFrameAndApprove overload.
        assertEq(r.count[0xfa], 1, "STATICCALL");
        assertEq(r.count[0xf4], 2, "DELEGATECALL");
        // The scan covered all of the code in front of the metadata.
        assertGt(r.end, 1000, "scanned the runtime code");
    }

    /// Invariant 4: `isValidSignature` reads no storage and cannot see `tx.origin`, and the
    /// whole contract has no instruction the validation prefix bans. CALLER appears exactly
    /// twice, in the two inlined copies of the frame entry gate (test_VerifyFrame_* below
    /// show both gates; test_IsValidSignature_IgnoresCallerAndOrigin shows the 1271 side).
    function test_Code_IsValidSignatureIsAPureCheck() public view {
        OpcodeScan.Report memory r = OpcodeScan.scan(address(account).code, true);
        assertEq(r.count[0x54], 0, "SLOAD");
        assertEq(r.count[0x5c], 0, "TLOAD");
        assertEq(r.count[0x32], 0, "ORIGIN");
        assertEq(r.count[0x33], 2, "CALLER");
        // Banned in a validation prefix (EIP-8141, Banned Opcodes).
        uint8[13] memory banned = [0x3a, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x48, 0x4a, 0x4b, 0x31, 0x47, 0xfe];
        for (uint256 i = 0; i < banned.length; i++) assertEq(r.count[banned[i]], 0, "banned opcode");
        // GAS is allowed only immediately before a *CALL.
        assertEq(r.count[0x5a], 3, "GAS");
        assertEq(r.strayGas, 0, "GAS not immediately followed by a call");
    }

    /// Invariants 1 and 2: the account itself has no EIP-8141 instruction. Approval can only
    /// happen in the module, which is reached only through verifyFrameAndApprove.
    function test_Code_HasNoCallAndNoFrameOpcode() public view {
        OpcodeScan.Report memory r = OpcodeScan.scan(address(account).code, true);
        assertEq(r.count[0xaa], 0, "APPROVE");
        for (uint256 op = 0xb0; op <= 0xb5; op++) assertEq(r.count[op], 0, "frame introspection opcode");
    }

    /// Invariant 1, module side: the module reads the digest from TXPARAM(0x08) once, takes
    /// the witness only from SIGDATACOPY after checking scheme and msg with SIGPARAM, and has
    /// no instruction that could change state or call out other than its one STATICCALL. Its
    /// behaviour on real transactions is in SafePqOwnersFrameTest.
    function test_FrameModule_VerifiesOnlyTheCanonicalHash() public view {
        OpcodeScan.Report memory r = OpcodeScan.scan(frameModule.code, false);
        assertEq(r.count[0xb0], 3, "TXPARAM: sig hash, frame index, signature count");
        assertEq(r.count[0xb5], 1, "SIGDATACOPY");
        assertEq(r.count[0xaa], 1, "APPROVE");
        assertEq(r.count[0xb1], 0, "FRAMEDATALOAD");
        assertEq(r.count[0xb2], 0, "FRAMEDATACOPY");
        assertEq(r.count[0xfa], 1, "STATICCALL");
        assertEq(r.count[0xf1] + r.count[0xf2] + r.count[0xf4], 0, "CALL / CALLCODE / DELEGATECALL");
        assertEq(r.count[0x54] + r.count[0x55] + r.count[0x5c] + r.count[0x5d], 0, "storage");
        assertEq(r.count[0xf0] + r.count[0xf5] + r.count[0xff], 0, "CREATE / CREATE2 / SELFDESTRUCT");
        assertEq(r.strayGas, 0, "GAS not immediately followed by a call");
    }

    // ───────────────────────────── VERIFY frame entry points ─────────────────────────────

    function test_VerifyFrame_RejectsNonEntryPointCaller() public {
        address[3] memory callers = [makeAddr("attacker"), address(account), address(this)];
        for (uint256 i = 0; i < callers.length; i++) {
            vm.prank(callers[i]);
            vm.expectRevert(SphincsOwnerAccount.NotEntryPoint.selector);
            account.verifyFrameAndApprove();
            vm.prank(callers[i]);
            vm.expectRevert(SphincsOwnerAccount.NotEntryPoint.selector);
            account.verifyFrameAndApprove(0);
        }
    }

    /// From ENTRY_POINT the call reaches the module and halts on TXPARAM, an undefined opcode
    /// before EIP-8141: the path is wired through and is not a silent no-op today.
    function test_VerifyFrame_HaltsOnPre8141Evm() public {
        vm.prank(ENTRY_POINT);
        (bool ok, bytes memory ret) = address(account).call{gas: 100_000}(abi.encodeWithSignature("verifyFrameAndApprove()"));
        assertFalse(ok);
        assertEq(ret.length, 0, "undefined opcode, not a revert reason");
        vm.prank(ENTRY_POINT);
        (ok, ret) = address(account).call{gas: 100_000}(abi.encodeWithSignature("verifyFrameAndApprove(uint256)", uint256(0)));
        assertFalse(ok);
        assertEq(ret.length, 0);
    }

    /// Invariants 1 and 2: the module input is `pkSeed ‖ pkRoot ‖ verifier [‖ sigIndex]` from
    /// the account's immutables and nothing else. A digest and a signature appended to the
    /// frame data do not reach it, so nothing a caller supplies is ever verified on the
    /// approval path.
    function test_VerifyFrame_ForwardsOnlyKeysAndIndex() public {
        address recorder = address(new CalldataRecorder());
        (bytes32 seed, bytes32 root, bytes32 message, bytes memory sig) = _vector(0);
        SphincsOwnerAccount a = new SphincsOwnerAccount(seed, root, address(verifier), recorder);

        vm.prank(ENTRY_POINT);
        (bool ok, bytes memory ret) = address(a).call(abi.encodeWithSignature("verifyFrameAndApprove()"));
        assertFalse(ok, "the recorder bounces the payload as revert data");
        assertEq(ret, abi.encode(seed, root, address(verifier)), "no-index payload");

        vm.prank(ENTRY_POINT);
        (ok, ret) = address(a).call(abi.encodeWithSignature("verifyFrameAndApprove(uint256)", uint256(7)));
        assertFalse(ok);
        assertEq(ret, abi.encode(seed, root, address(verifier), uint256(7)), "indexed payload");

        // Frame data that also carries a digest and a valid signature over it.
        vm.prank(ENTRY_POINT);
        (ok, ret) = address(a).call(bytes.concat(abi.encodeWithSignature("verifyFrameAndApprove()"), abi.encode(message, sig)));
        assertFalse(ok);
        assertEq(ret, abi.encode(seed, root, address(verifier)), "trailing frame data is not forwarded");

        vm.prank(ENTRY_POINT);
        (ok, ret) = address(a).call(
            bytes.concat(abi.encodeWithSignature("verifyFrameAndApprove(uint256)", uint256(7)), abi.encode(message, sig))
        );
        assertFalse(ok);
        assertEq(ret, abi.encode(seed, root, address(verifier), uint256(7)), "trailing frame data is not forwarded");
    }

    // ───────────────────────────── isValidSignature ─────────────────────────────

    /// Every fixture vector, on an account holding that vector's key. The gated figure is the
    /// gas of the isValidSignature call frame (verifier included, verifier warm).
    function test_IsValidSignature_AcceptsFixtureVectors() public {
        uint256 n = _count();
        assertGe(n, 6, "fixture vectors");
        uint256 minGas = type(uint256).max;
        uint256 maxGas;
        for (uint256 i = 0; i < n; i++) {
            (bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig) = _vector(i);
            SphincsOwnerAccount a = _newAccount(pkSeed, pkRoot);
            assertEq(a.isValidSignature(message, sig), MAGIC_HASH, "warm-up");
            assertEq(a.isValidSignature(message, sig), MAGIC_HASH, "fixture vector");
            uint256 used = vm.lastCallGas().gasTotalUsed;
            if (used < minGas) minGas = used;
            if (used > maxGas) maxGas = used;
        }
        emit log_named_uint("isValidSignature(bytes32,bytes) gas, call frame, verifier warm, min", minGas);
        emit log_named_uint("isValidSignature(bytes32,bytes) gas, call frame, verifier warm, max", maxGas);
        assertLe(maxGas, IS_VALID_SIGNATURE_GAS_MAX, "isValidSignature gas ceiling");
    }

    /// Bad inputs return 0xffffffff and never revert: a tampered byte, another hash, another
    /// key's signature, and every wrong length (the verifier reverts on those).
    function test_IsValidSignature_RejectsWithoutReverting() public {
        (,, bytes32 message, bytes memory sig) = _vector(0);
        assertEq(account.isValidSignature(message, sig), MAGIC_HASH, "control");

        bytes memory tampered = bytes.concat(sig);
        tampered[3000] = bytes1(uint8(tampered[3000]) ^ 0x01);
        assertEq(account.isValidSignature(message, tampered), INVALID, "tampered");
        assertEq(account.isValidSignature(message ^ bytes32(uint256(1)), sig), INVALID, "other hash");

        (,, bytes32 message1, bytes memory sig1) = _vector(1);
        assertEq(account.isValidSignature(message1, sig1), INVALID, "another key's signature");

        assertEq(account.isValidSignature(message, new bytes(0)), INVALID, "empty");
        assertEq(account.isValidSignature(message, _slice(sig, sig.length - 1)), INVALID, "one byte short");
        assertEq(account.isValidSignature(message, bytes.concat(sig, hex"00")), INVALID, "one byte long");
        assertEq(account.isValidSignature(message, bytes.concat(sig, sig)), INVALID, "doubled");
        assertEq(account.isValidSignature(message, new bytes(4660)), INVALID, "zeros");
    }

    /// Invariant 4: valid only when the verifier call succeeds and returns exactly 32 bytes
    /// equal to 1. Each mock verifier breaks one part of that.
    function test_IsValidSignature_RequiresExactlyOneWordEqualToOne() public {
        (bytes32 seed, bytes32 root, bytes32 message, bytes memory sig) = _vector(0);

        // (return data, revert?) of the mock verifier, and whether it may count as valid.
        bytes memory one = abi.encode(uint256(1));
        assertEq(_withVerifier(seed, root, address(new MockVerifier(one, false))).isValidSignature(message, sig), MAGIC_HASH, "control: 32 bytes, 1");

        bytes[8] memory bad = [
            bytes(""), // success, no return data
            abi.encode(uint256(0)), // false
            abi.encode(uint256(2)), // a non-boolean word
            abi.encode(uint256(1) << 255), // dirty high bits
            abi.encode(uint256(1), uint256(1)), // 64 bytes
            _slice(one, 31), // 31 bytes
            bytes.concat(one, hex"00"), // 33 bytes
            abi.encode(type(uint256).max)
        ];
        for (uint256 i = 0; i < bad.length; i++) {
            SphincsOwnerAccount a = _withVerifier(seed, root, address(new MockVerifier(bad[i], false)));
            assertEq(a.isValidSignature(message, sig), INVALID, "malformed verifier answer");
            assertEq(a.isValidSignature(abi.encodePacked(message), sig), INVALID, "malformed verifier answer, legacy form");
        }

        // A verifier that reverts, even with return data that reads as `true`.
        SphincsOwnerAccount r = _withVerifier(seed, root, address(new MockVerifier(one, true)));
        assertEq(r.isValidSignature(message, sig), INVALID, "verifier revert");
        assertEq(r.isValidSignature(abi.encodePacked(message), sig), INVALID, "verifier revert, legacy form");

        // A verifier whose code is gone: the STATICCALL succeeds and returns nothing.
        SphincsOwnerAccount gone = _withVerifier(seed, root, address(new MockVerifier(one, false)));
        vm.etch(gone.verifier(), "");
        assertEq(gone.isValidSignature(message, sig), INVALID, "code-less verifier");
    }

    /// Starved of gas, the call either reverts (out of gas in the account) or returns
    /// 0xffffffff (out of gas in the verifier). It never returns the magic value.
    function test_IsValidSignature_NeverValidWhenOutOfGas() public {
        (,, bytes32 message, bytes memory sig) = _vector(0);
        bytes memory call_ = abi.encodeWithSelector(MAGIC_HASH, message, sig);
        uint256 accepted;
        for (uint256 g = 2_000; g <= 60_000; g += 500) {
            (bool ok, bytes memory ret) = address(account).staticcall{gas: g}(call_);
            if (!ok) continue;
            assertEq(ret.length, 32);
            bytes4 answer = abi.decode(ret, (bytes4));
            assertTrue(answer == MAGIC_HASH || answer == INVALID, "only the two answers");
            if (answer == MAGIC_HASH) accepted++;
            else assertLt(g, 50_000, "0xffffffff with enough gas");
        }
        assertGt(accepted, 0, "valid once there is enough gas");
    }

    /// Invariant 4: the answer does not depend on who asks, on tx.origin, or on the block.
    function test_IsValidSignature_IgnoresCallerAndOrigin() public {
        (,, bytes32 message, bytes memory sig) = _vector(0);
        address[4] memory who = [ENTRY_POINT, address(account), makeAddr("safe"), address(0)];
        for (uint256 i = 0; i < who.length; i++) {
            vm.prank(who[i], who[i]); // msg.sender and tx.origin
            assertEq(account.isValidSignature(message, sig), MAGIC_HASH);
            vm.prank(who[i], who[i]);
            assertEq(account.isValidSignature(message ^ bytes32(uint256(1)), sig), INVALID);
        }
        vm.roll(block.number + 1000);
        vm.warp(block.timestamp + 1 days);
        vm.chainId(8141);
        vm.deal(address(account), 5 ether);
        assertEq(account.isValidSignature(message, sig), MAGIC_HASH);
    }

    /// Invariants 3 and 4: no entry point reads or writes a storage slot of the account.
    function test_NoEntryPointTouchesStorage() public {
        (,, bytes32 message, bytes memory sig) = _vector(0);
        vm.record();
        account.isValidSignature(message, sig);
        account.isValidSignature(abi.encodePacked(message), sig);
        account.pkSeed();
        account.pkRoot();
        account.verifier();
        account.frameModule();
        vm.deal(address(this), 1 ether);
        (bool ok,) = address(account).call{value: 1}("");
        assertTrue(ok);
        vm.prank(ENTRY_POINT);
        (ok,) = address(account).call{gas: 100_000}(abi.encodeWithSignature("verifyFrameAndApprove()"));
        (bytes32[] memory reads, bytes32[] memory writes) = vm.accesses(address(account));
        assertEq(reads.length, 0, "storage reads");
        assertEq(writes.length, 0, "storage writes");
    }

    /// The (bytes, bytes) form with a real signature from the Rust CLI: `data` is shaped like
    /// the EIP-712 pre-image a Safe 1.4.1 passes, and the signature is over keccak256(data).
    function test_IsValidSignature_LegacyForm_FFI() public {
        _requireLsfk();
        bytes32 seed = keccak256("leanSphincs-f-keccak owner account FFI seed");
        (bytes32 pkSeed, bytes32 pkRoot,) = _sign(seed, bytes32(0));
        SphincsOwnerAccount a = _newAccount(pkSeed, pkRoot);

        bytes memory data = abi.encodePacked(bytes1(0x19), bytes1(0x01), keccak256("domain"), keccak256("safeTx"));
        assertEq(data.length, 66);
        (,, bytes memory sig) = _sign(seed, keccak256(data));

        assertEq(a.isValidSignature(data, sig), MAGIC_DATA, "legacy form over keccak256(data)");
        emit log_named_uint("isValidSignature(bytes,bytes) gas, call frame, verifier warm", vm.lastCallGas().gasTotalUsed);
        assertEq(a.isValidSignature(keccak256(data), sig), MAGIC_HASH, "same signature, hash form");

        // The legacy form hashes `data`; it does not take a 32-byte `data` as the digest.
        assertEq(a.isValidSignature(abi.encodePacked(keccak256(data)), sig), INVALID, "data is hashed, not used as the digest");
        bytes memory other = bytes.concat(data);
        other[65] = bytes1(uint8(other[65]) ^ 0x01);
        assertEq(a.isValidSignature(other, sig), INVALID, "other data");
        assertEq(a.isValidSignature(bytes.concat(data, hex"00"), sig), INVALID, "longer data");
        assertEq(a.isValidSignature(new bytes(0), sig), INVALID, "empty data");
    }

    // ───────────────────────────── receive ─────────────────────────────

    /// Safe up to 1.4.1 pays refunds with `send`: receive() must fit the 2,300-gas stipend.
    function test_Receive_FitsTheSendStipend() public {
        Sender s = new Sender();
        vm.deal(address(s), 1 ether);
        assertTrue(s.viaSend(payable(address(account)), 123), "send");
        s.viaTransfer(payable(address(account)), 77);
        assertEq(address(account).balance, 200);

        (bool ok,) = address(account).call{value: 0, gas: 2300}("");
        assertTrue(ok);
        uint256 used = vm.lastCallGas().gasTotalUsed;
        emit log_named_uint("receive() gas, call frame", used);
        assertLt(used, 200, "receive() is a few opcodes");
    }

    // ───────────────────────────── helpers ─────────────────────────────

    function _withVerifier(bytes32 seed, bytes32 root, address v) internal returns (SphincsOwnerAccount) {
        return new SphincsOwnerAccount(seed, root, v, frameModule);
    }

    function _slice(bytes memory b, uint256 n) internal pure returns (bytes memory out) {
        out = new bytes(n);
        for (uint256 i = 0; i < n; i++) out[i] = b[i];
    }

    /// As SphincsAccountLeanSphincsFTest: a stale binary fails, a missing one skips except under CI.
    function _requireLsfk() internal {
        string[] memory probe = new string[](3);
        probe[0] = "sh";
        probe[1] = "-c";
        probe[2] = LSFK_PROBE;
        bytes memory state = vm.ffi(probe);
        string memory build = " (cd signers/leansphincs-f-keccak && cargo build --release)";
        if (keccak256(state) == keccak256("missing")) {
            assertEq(vm.envOr("CI", string("")), "", string.concat(LSFK, " is not built under CI:", build));
            vm.skip(true, string.concat(LSFK, " not built:", build));
        }
        assertEq(string(state), "fresh", string.concat(LSFK, " is older than the crate sources:", build));
    }

    function _sign(bytes32 seed, bytes32 message) internal returns (bytes32, bytes32, bytes memory) {
        string[] memory inputs = new string[](5);
        inputs[0] = LSFK;
        inputs[1] = "sign";
        inputs[2] = vm.toString(seed);
        inputs[3] = "8";
        inputs[4] = vm.toString(message);
        return abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }
}

/// @dev Answers every call with fixed return data, or reverts with it.
contract MockVerifier {
    bytes ret;
    bool fail;

    constructor(bytes memory _ret, bool _fail) {
        ret = _ret;
        fail = _fail;
    }

    fallback() external {
        bytes memory r = ret;
        bool f = fail;
        assembly {
            if f { revert(add(r, 0x20), mload(r)) }
            return(add(r, 0x20), mload(r))
        }
    }
}

contract Sender {
    function viaSend(address payable to, uint256 amount) external returns (bool) {
        return to.send(amount);
    }

    function viaTransfer(address payable to, uint256 amount) external {
        to.transfer(amount);
    }
}
