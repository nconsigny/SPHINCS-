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
    // `execute` previously had NO caller check: any address could call it and
    // move the account's ETH or make arbitrary calls as the account. It is now
    // self-call-only (the SENDER-frame context, reached after the VERIFY frame
    // has checked the SPHINCS+ signature).

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
    // an ARBITRARY tx.signatures entry via SIGPARAM, and the scope from
    // FRAMEPARAM(0x06). Those opcodes (0xb0 / 0xb4 / 0xb3) and APPROVE (0xaa) do not
    // exist on a pre-8141 EVM, so the path CANNOT be executed here — conformance is
    // asserted by inspecting the module's bytecode, and by pinning that the caller
    // gate fires before any undefined opcode is reached.

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

        // SIGPARAM(0x04) copy: DUP1, len fetch, then the five-item stack setup
        // ending with signatureIndex on top. 0x00a4 must equal the module's ARGS_SIG.
        assertTrue(_contains(code, hex"80600390b46100a49160009190600490b4"), "SIGPARAM(0x04) copy");

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

    function testFrameRevertsOnNonCanonicalKey() public {
        // Non-canonical pkSeed (low 128 bits set) now trips the verifier's
        // "Invalid public key" guard, surfaced by the frame as "verify call failed".
        bytes32 pkSeed = bytes32(uint256(1));
        bytes32 pkRoot = bytes32(uint256(2) << 128);
        SphincsFrameAccount frame = _newFrame(pkSeed, pkRoot);
        bytes memory zeroSig = new bytes(3688);
        vm.expectRevert(bytes("verify call failed"));
        frame.verifyAndApprove(bytes32(uint256(0xdead)), zeroSig, 1);
    }
}
