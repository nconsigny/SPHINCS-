// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C13Asm.sol";
import "../src/SphincsFrameAccount.sol";

/// @notice Integration test: SphincsFrameAccount + C13 verifier. Covers three
///         things:
///           1. the legacy `verifyAndApprove` demo path — its APPROVE assembly is
///              still a placeholder, so it returns normally on a standard EVM once
///              the verifier staticcall succeeds;
///           2. `execute` access control (self-call only);
///           3. the EIP-8141-conformant `verifyFrameAndApprove`, whose Yul module
///              cannot run on a pre-8141 EVM — asserted by bytecode inspection
///              plus an undefined-opcode halt.
contract SphincsFrameAccountC13Test is Test {
    SphincsC13Asm verifier;
    address frameOwner;
    address frameModule;

    function setUp() public {
        verifier = new SphincsC13Asm();
        frameOwner = address(0xBEEF);
        frameModule = _deployFrameModule();
    }

    /// @dev Deploy the Yul EIP-8141 verify module from its compiled artifact.
    ///      Read straight from the artifact JSON because `vm.getCode` cannot resolve
    ///      Yul objects (forge emits them without an ABI).
    function _deployFrameModule() internal returns (address addr) {
        bytes memory initcode = vm.parseJsonBytes(
            vm.readFile("out/SphincsFrameVerify.yul/SphincsFrameVerify.json"),
            ".bytecode.object"
        );
        assembly {
            addr := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(addr != address(0), "module deploy failed");
    }

    function _newFrame(bytes32 pkSeed, bytes32 pkRoot) internal returns (SphincsFrameAccount) {
        return new SphincsFrameAccount(pkSeed, pkRoot, address(verifier), frameOwner, frameModule);
    }

    function testFrameVerifyAndApproveAcceptsRealC13SignatureFFI() public {
        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c13";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));

        SphincsFrameAccount frame = _newFrame(pkSeed, pkRoot);

        assertEq(frame.verifier(), address(verifier), "verifier wired");
        assertEq(frame.pkSeed(), pkSeed, "pkSeed stored");
        assertEq(frame.pkRoot(), pkRoot, "pkRoot stored");
        assertEq(frame.owner(), frameOwner, "owner stored");

        // verifyAndApprove must not revert on a valid C13 sig.
        frame.verifyAndApprove(message, sig, 1);
    }

    function testFrameVerifyAndApproveRevertsOnBadSignature() public {
        // Canonical (top-128-aligned) keys so we exercise the actual bad-SIGNATURE
        // path, not the non-canonical-key input guard.
        bytes32 pkSeed = bytes32(uint256(1) << 128);
        bytes32 pkRoot = bytes32(uint256(2) << 128);
        SphincsFrameAccount frame = _newFrame(pkSeed, pkRoot);

        // 3688 zero bytes: correct length, but the FORS+C forced-zero / WOTS+C
        // target-sum / root checks all fail. The verifier now RETURNS false for
        // these (review C13-evm-f2), so the frame's descriptive require fires.
        bytes memory zeroSig = new bytes(3688);
        bytes32 message = bytes32(uint256(0xdead));
        vm.expectRevert(bytes("invalid SPHINCS+ signature"));
        frame.verifyAndApprove(message, zeroSig, 1);
    }

    // ── execute() access control ───────────────────────────────────────────
    //
    // `execute` is self-call-only: the SENDER-frame context, reachable only after
    // the VERIFY frame has checked the SPHINCS+ signature.

    function _canonicalFrame() internal returns (SphincsFrameAccount) {
        return _newFrame(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128));
    }

    function test_RandomEoa_CannotCallExecute() public {
        SphincsFrameAccount frame = _canonicalFrame();
        vm.deal(address(frame), 1 ether);
        address attacker = makeAddr("attacker");

        vm.prank(attacker);
        vm.expectRevert(SphincsFrameAccount.NotSelf.selector);
        frame.execute(attacker, 1 ether, "");

        assertEq(address(frame).balance, 1 ether, "account funds untouched");
        assertEq(attacker.balance, 0, "attacker gained nothing");
    }

    /// @dev The ECDSA owner is deliberately NOT an authorized executor: this
    ///      account is pure-PQ, so a broken/leaked ECDSA key alone must not
    ///      authorize execution (same invariant as SphincsAccount).
    function test_Owner_CannotCallExecute() public {
        SphincsFrameAccount frame = _canonicalFrame();
        vm.deal(address(frame), 1 ether);

        vm.prank(frameOwner);
        vm.expectRevert(SphincsFrameAccount.NotSelf.selector);
        frame.execute(frameOwner, 1 ether, "");

        assertEq(address(frame).balance, 1 ether, "account funds untouched");
    }

    // ── EIP-8141-conformant verify frame ───────────────────────────────────
    //
    // `verifyFrameAndApprove` reads the digest from TXPARAM(0x08), the witness from
    // an ARBITRARY tx.signatures entry via SIGPARAM / SIGDATACOPY, and the scope from
    // FRAMEPARAM(0x06). Those opcodes (0xb0 / 0xb4 / 0xb5 / 0xb3) and APPROVE (0xaa)
    // do not exist on a pre-8141 EVM, so the path CANNOT be executed here —
    // conformance is asserted by inspecting the module's bytecode, and by pinning
    // that the caller gate fires before any undefined opcode is reached. The module
    // is run end to end under the current spec text by the EIP-8141 emulator in
    // test/SphincsFrameModuleEmuTest.t.sol.

    function test_FrameModule_EmitsTheSpecifiedInstructions() public view {
        bytes memory code = frameModule.code;
        assertGt(code.length, 0, "module has runtime code");

        // TXPARAM(0x08) = compute_sig_hash(tx); TXPARAM(0x0A) = current frame index;
        // TXPARAM(0x0B) = len(signatures).
        assertTrue(_contains(code, hex"6008b0"), "TXPARAM(0x08) sig hash");
        assertTrue(_contains(code, hex"600ab0"), "TXPARAM(0x0A) frame index");
        assertTrue(_contains(code, hex"600bb0"), "TXPARAM(0x0B) num signatures");

        // SIGPARAM metadata reads: PUSH1 param; SWAP1; SIGPARAM — signatureIndex
        // ends up on top, param second, as the spec requires.
        assertTrue(_contains(code, hex"600190b4"), "SIGPARAM(0x01) scheme");
        assertTrue(_contains(code, hex"600290b4"), "SIGPARAM(0x02) msg");
        assertTrue(_contains(code, hex"600390b4"), "SIGPARAM(0x03) len");

        // FRAMEPARAM(0x06) = allowed_scope.
        assertTrue(_contains(code, hex"600690b3"), "FRAMEPARAM(0x06) allowed scope");

        // Witness copy: DUP1, len fetch, then SIGDATACOPY (0xb5) with memOffset 0x00a4
        // (= the module's ARGS_SIG) on top, dataOffset 0, length, signatureIndex. The
        // SIGPARAM(0x04) copy form of the 2026-07-28 draft was removed from the spec
        // (any undefined SIGPARAM param halts), so it must not come back.
        // (review frame-sigparam-copy-removed)
        assertTrue(_contains(code, hex"80600390b460006100a4b5"), "SIGDATACOPY witness copy");
        assertFalse(_contains(code, hex"600490b4"), "no SIGPARAM(0x04)");
        assertFalse(_contains(code, hex"80600390b46100a49160009190600490b4"), "no 07-28 SIGPARAM copy form");

        // APPROVE(offset=0, length=0, scope).
        assertTrue(_contains(code, hex"60006000aa"), "APPROVE");

        // GAS must sit IMMEDIATELY before the *CALL — the only form the
        // validation-prefix banned-opcode list exempts for GAS (0x5A).
        assertTrue(_contains(code, hex"5afa"), "GAS immediately followed by STATICCALL");

        // The verifier selector the module builds calldata for. solc may emit it
        // literally or as a shifted constant (0x057eddb5 << 0xe3 == 0x2bf6eda8),
        // which is what the optimizer currently picks; accept either.
        assertTrue(
            _contains(code, hex"2bf6eda8") || _contains(code, hex"057eddb560e31b"),
            "verify(bytes32,bytes32,bytes32,bytes) selector"
        );
    }

    function test_VerifyFrameAndApprove_RejectsNonEntryPointCaller() public {
        SphincsFrameAccount frame = _canonicalFrame();
        vm.prank(makeAddr("attacker"));
        vm.expectRevert(SphincsFrameAccount.NotEntryPoint.selector);
        frame.verifyFrameAndApprove();
    }

    /// @dev From ENTRY_POINT the call reaches the module and dies on TXPARAM, which
    ///      is an undefined opcode pre-8141. Pins that the path is wired through to
    ///      the module and that it is not silently a no-op on today's EVM.
    function test_VerifyFrameAndApprove_HaltsOnPre8141Evm() public {
        SphincsFrameAccount frame = _canonicalFrame();
        vm.prank(address(0xaa));
        vm.expectRevert();
        frame.verifyFrameAndApprove();
    }

    /// @dev The module takes pkSeed / pkRoot / verifier from its DELEGATECALL
    ///      input. A VERIFY frame aimed at the module itself must not be able to
    ///      feed it an attacker's keys and verifier and so APPROVE for the module.
    ///      The guard runs before any EIP-8141 opcode, so on today's EVM it shows
    ///      up as a clean Error revert, not an undefined-opcode halt.
    function test_FrameModule_RejectsDirectCall() public {
        bytes memory attackerInput = abi.encode(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128), address(verifier));
        vm.prank(address(0xaa));
        (bool ok, bytes memory ret) = frameModule.call(attackerInput);
        assertFalse(ok, "direct call must fail");
        assertEq(ret, abi.encodeWithSignature("Error(string)", "delegatecall only"), "guard reason");
    }

    /// @dev Delegatecalled through the account, the guard passes and execution
    ///      goes on to the first EIP-8141 opcode. That opcode halts exceptionally
    ///      with no return data, so the guard's Error must NOT appear here.
    function test_FrameModule_GuardPassesUnderDelegatecall() public {
        SphincsFrameAccount frame = _canonicalFrame();
        vm.prank(address(0xaa));
        (bool ok, bytes memory ret) = address(frame).call(abi.encodeWithSignature("verifyFrameAndApprove()"));
        assertFalse(ok, "pre-8141 EVM halts");
        assertEq(ret.length, 0, "halted on an undefined opcode, not on the guard");
    }

    /// @dev The verify path is storage-free. A frame transaction starts with
    ///      accessed_storage_keys empty, so every SLOAD would be a cold
    ///      2,100-gas read. The keys are account immutables forwarded as the
    ///      DELEGATECALL input instead.
    function test_FrameModule_HasNoStorageOpcodes() public view {
        bytes memory code = frameModule.code;
        for (uint256 i = 0; i < code.length; i++) {
            uint8 op = uint8(code[i]);
            assertTrue(op != 0x54, "module must not SLOAD");
            assertTrue(op != 0x55, "module must not SSTORE");
            if (op >= 0x60 && op <= 0x7f) i += op - 0x5f; // skip PUSHn immediates
        }
    }

    function test_VerifyFrameAndApprove_RevertsWithoutModule() public {
        SphincsFrameAccount frame = new SphincsFrameAccount(
            bytes32(uint256(1) << 128), bytes32(uint256(2) << 128), address(verifier), frameOwner, address(0)
        );
        vm.prank(address(0xaa));
        vm.expectRevert(SphincsFrameAccount.NoFrameModule.selector);
        frame.verifyFrameAndApprove();
    }

    function _contains(bytes memory haystack, bytes memory needle) internal pure returns (bool) {
        if (needle.length == 0 || haystack.length < needle.length) return false;
        for (uint256 i = 0; i <= haystack.length - needle.length; i++) {
            bool hit = true;
            for (uint256 j = 0; j < needle.length; j++) {
                if (haystack[i + j] != needle[j]) { hit = false; break; }
            }
            if (hit) return true;
        }
        return false;
    }

    // ── constructor guards (review frame-ctor-unchecked-module) ─────────────
    //
    // Nothing the constructor stores can be rotated later, so a value that can never
    // verify would brick the account and lock its ETH. These are refused up front.

    function testFrameRevertsOnNonCanonicalKey() public {
        // Low 128 bits set: every verifier rejects such a key ("Invalid public key").
        vm.expectRevert(SphincsFrameAccount.NonCanonicalKey.selector);
        _newFrame(bytes32(uint256(1)), bytes32(uint256(2) << 128));
        vm.expectRevert(SphincsFrameAccount.NonCanonicalKey.selector);
        _newFrame(bytes32(uint256(1) << 128), bytes32((uint256(2) << 128) | 1));
    }

    function testFrameRejectsCodelessVerifier() public {
        vm.expectRevert(SphincsFrameAccount.VerifierHasNoCode.selector);
        new SphincsFrameAccount(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128), makeAddr("eoa"), frameOwner, frameModule);
    }

    function testFrameRejectsCodelessModule() public {
        // A DELEGATECALL into a code-less address "succeeds" without running APPROVE,
        // so every frame transaction would be invalid.
        vm.expectRevert(SphincsFrameAccount.FrameModuleHasNoCode.selector);
        new SphincsFrameAccount(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128), address(verifier), frameOwner, makeAddr("eoa"));
    }

    function testFrameAcceptsFullTopHalfKey() public {
        bytes32 top = bytes32(~uint256(type(uint128).max));
        SphincsFrameAccount frame = _newFrame(top, top);
        assertEq(frame.pkSeed(), top);
        assertEq(frame.pkRoot(), top);
    }

    /// @dev Both entry points forward exactly `pkSeed ‖ pkRoot ‖ verifier [‖ sigIndex]`
    ///      to the module. A recorder module bounces its calldata back as revert data.
    function test_VerifyFrameAndApprove_ForwardsKeysAndIndex() public {
        address recorder = address(new CalldataRecorder());
        bytes32 seed = bytes32(uint256(1) << 128);
        bytes32 root = bytes32(uint256(2) << 128);
        SphincsFrameAccount frame = new SphincsFrameAccount(seed, root, address(verifier), frameOwner, recorder);

        vm.prank(address(0xaa));
        (bool ok, bytes memory ret) = address(frame).call(abi.encodeWithSignature("verifyFrameAndApprove()"));
        assertFalse(ok);
        assertEq(ret, abi.encode(seed, root, address(verifier)), "no-index payload");

        vm.prank(address(0xaa));
        (ok, ret) = address(frame).call(abi.encodeWithSignature("verifyFrameAndApprove(uint256)", uint256(7)));
        assertFalse(ok);
        assertEq(ret, abi.encode(seed, root, address(verifier), uint256(7)), "indexed payload");
    }

    function test_VerifyFrameAndApproveIndexed_RejectsNonEntryPointCaller() public {
        SphincsFrameAccount frame = _canonicalFrame();
        vm.prank(makeAddr("attacker"));
        vm.expectRevert(SphincsFrameAccount.NotEntryPoint.selector);
        frame.verifyFrameAndApprove(1);
    }

    function test_Account_GasImmediatelyBeforeDelegatecall() public {
        assertTrue(_contains(address(_canonicalFrame()).code, hex"5af4"), "GAS immediately followed by DELEGATECALL");
    }
}

/// @dev Test helper: reverts with its own calldata, so a delegatecaller sees exactly what
///      it sent.
contract CalldataRecorder {
    fallback() external {
        assembly {
            calldatacopy(0, 0, calldatasize())
            revert(0, calldatasize())
        }
    }
}
