// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C13Asm.sol";
import "../src/SphincsFrameAccount.sol";
import {CalldataRecorder} from "./SphincsFrameAccountC13Test.t.sol";

/// @notice Runs the REAL deployed SphincsFrameVerify module under the CURRENT EIP-8141 text
///         (ethereum/EIPs master af3a7802c8ea) for concrete frame transactions.
///
///         forge/revm has no EIP-8141, so test/py/frame8141_emu.py executes the module's
///         runtime code as the DELEGATECALL target of the frame's account, with TXPARAM /
///         FRAMEPARAM / SIGPARAM / SIGDATACOPY / APPROVE answered from the transaction in
///         test/fixtures/frame8141_two_accounts.json (regenerate with
///         test/py/gen_frame_fixture.py). Everything else is real: the account builds the
///         module input from the frame's data (captured by swapping a recorder in at the
///         module address), and the module's STATICCALL is answered by the real
///         SphincsC13Asm (phase 1 captures the verifier calldata, phase 2 replays with the
///         verifier's answer).
///
///         Regression tests for:
///           * frame-sigparam-copy-removed: the witness copy used the SIGPARAM(0x04) copy form
///             of the 2026-07-28 draft, which the current spec removed (undefined SIGPARAM
///             params halt), so every VERIFY frame halted. It is SIGDATACOPY (0xb5) now.
///           * frame-first-arbitrary-entry: the module always took the FIRST ARBITRARY
///             empty-msg entry, so two SphincsFrameAccounts (sender + sponsor) could never
///             both verify in one transaction. `verifyFrameAndApprove(uint256)` names the
///             entry explicitly.
contract SphincsFrameModuleEmuTest is Test {
    string constant EMU = "test/py/frame8141_emu.py";
    string constant FX = "test/fixtures/frame8141_two_accounts.json";

    uint8 constant OUT_HALT = 0;
    uint8 constant OUT_REVERT = 1;
    uint8 constant OUT_APPROVE = 2;

    struct Run {
        uint8 outcome;
        uint256 scope;
        uint256 copied;
        address callTo;
        bytes cd;
        string detail;
    }

    address A;
    address B;
    bytes32 seedA;
    bytes32 rootA;
    bytes32 seedB;
    bytes32 rootB;
    address verifierAddr;
    address module;
    bytes moduleCode;

    function _emu(string[] memory args) internal returns (bytes memory) {
        string[] memory c = new string[](args.length + 3);
        c[0] = "python3";
        c[1] = "-I";
        c[2] = EMU;
        for (uint256 i; i < args.length; ++i) c[i + 3] = args[i];
        return vm.ffi(c);
    }

    function _args(string memory a, string memory b, string memory c) internal pure returns (string[] memory r) {
        r = new string[](3);
        (r[0], r[1], r[2]) = (a, b, c);
    }

    function setUp() public {
        string[] memory a = new string[](2);
        (a[0], a[1]) = ("accounts", FX);
        (A, seedA, rootA, B, seedB, rootB, verifierAddr) =
            abi.decode(_emu(a), (address, bytes32, bytes32, address, bytes32, bytes32, address));

        deployCodeTo("SPHINCs-C13Asm.sol:SphincsC13Asm", verifierAddr);
        bytes memory init = vm.parseJsonBytes(vm.readFile("out/SphincsFrameVerify.yul/SphincsFrameVerify.json"), ".bytecode.object");
        address m;
        assembly {
            m := create(0, add(init, 0x20), mload(init))
        }
        require(m != address(0), "module deploy failed");
        module = m;
        moduleCode = m.code;
        deployCodeTo("SphincsFrameAccount.sol:SphincsFrameAccount", abi.encode(seedA, rootA, verifierAddr, address(0xBEEF), m), A);
        deployCodeTo("SphincsFrameAccount.sol:SphincsFrameAccount", abi.encode(seedB, rootB, verifierAddr, address(0xBEEF), m), B);
    }

    /// @dev The module input the real account builds when ENTRY_POINT calls it with `data`:
    ///      swap a recorder in at the module address, call, restore the module.
    function _payload(address account, bytes memory data) internal returns (bytes memory payload) {
        vm.etch(module, type(CalldataRecorder).runtimeCode);
        vm.prank(address(0xaa));
        bool ok;
        (ok, payload) = account.call(data);
        assertFalse(ok, "recorder bounces the payload as revert data");
        vm.etch(module, moduleCode);
    }

    function _run(string memory sc, uint256 fi, bytes memory payload, string memory verdict) internal returns (Run memory r) {
        string[] memory c = new string[](7);
        (c[0], c[1], c[2], c[3]) = ("run", FX, sc, vm.toString(fi));
        (c[4], c[5], c[6]) = (vm.toString(moduleCode), vm.toString(payload), verdict);
        (r.outcome, r.scope, r.copied, r.callTo, r.cd, r.detail) =
            abi.decode(_emu(c), (uint8, uint256, uint256, address, bytes, string));
    }

    /// @dev One VERIFY frame: module (emulated) -> real verifier -> module.
    function _module(string memory sc, uint256 fi, address account, bytes memory payload) internal returns (Run memory fin) {
        Run memory p1 = _run(sc, fi, payload, "00");
        if (p1.cd.length == 0) return p1; // never reached the verifier
        assertEq(p1.callTo, SphincsFrameAccount(payable(account)).verifier(), "module called another verifier");
        (bool ok, bytes memory ret) = p1.callTo.staticcall(p1.cd);
        string memory verdict = "revert";
        if (ok) verdict = vm.toString(ret.length >= 32 ? abi.decode(ret, (bytes32)) : bytes32(0));
        fin = _run(sc, fi, payload, verdict);
        assertEq(keccak256(fin.cd), keccak256(p1.cd), "phase 2 sent different calldata");
    }

    /// @dev The frame as the transaction defines it: the account is called with the frame's
    ///      own data.
    function _frame(string memory sc, uint256 fi) internal returns (Run memory r) {
        (address target,, bytes memory data,) =
            abi.decode(_emu(_argsFrame(sc, fi)), (address, uint256, bytes, bytes32));
        r = _module(sc, fi, target, _payload(target, data));
        console.log(string.concat("[", sc, "] frame ", vm.toString(fi), ": ", r.detail));
    }

    function _argsFrame(string memory sc, uint256 fi) internal pure returns (string[] memory r) {
        r = new string[](4);
        (r[0], r[1], r[2], r[3]) = ("frame", FX, sc, vm.toString(fi));
    }

    function _witness(string memory sc, uint256 i) internal returns (bytes memory w) {
        string[] memory r = new string[](4);
        (r[0], r[1], r[2], r[3]) = ("witness", FX, sc, vm.toString(i));
        w = abi.decode(_emu(r), (bytes));
    }

    function _sigHash(string memory sc) internal returns (bytes32 d) {
        (,,, d) = abi.decode(_emu(_argsFrame(sc, 0)), (address, uint256, bytes, bytes32));
    }

    // ───────────────────────────── tests ─────────────────────────────

    function test_FixtureWitnessesAreValid() public {
        SphincsC13Asm v = SphincsC13Asm(verifierAddr);
        bytes32 d = _sigHash("sponsored");
        bytes memory wA = _witness("sponsored", 0);
        bytes memory wB = _witness("sponsored", 1);
        assertTrue(v.verify(seedA, rootA, d, wA), "wA valid under key A");
        assertTrue(v.verify(seedB, rootB, d, wB), "wB valid under key B");
        assertFalse(v.verify(seedB, rootB, d, wA), "wA invalid under key B");
        assertFalse(v.verify(seedA, rootA, d, wB), "wB invalid under key A");
        assertTrue(v.verify(seedA, rootA, _sigHash("first-match"), _witness("first-match", 2)), "first-match wA");
    }

    /// @dev frame-first-arbitrary-entry: sender A (only_verify, flags 0x2) and sponsor B
    ///      (pay, flags 0x1) are both SphincsFrameAccounts. With explicit indices each frame
    ///      copies its own witness (via SIGDATACOPY) and APPROVEs, so the transaction is valid.
    function test_Sponsored_BothAccountsApproveWithExplicitIndices() public {
        Run memory f0 = _frame("sponsored", 0);
        assertEq(f0.copied, 0, "A's frame copied entry 0");
        assertEq(f0.outcome, OUT_APPROVE, f0.detail);
        assertEq(f0.scope, 2, "APPROVE_EXECUTION");

        Run memory f1 = _frame("sponsored", 1);
        assertEq(f1.copied, 1, "B's frame copied entry 1");
        assertEq(f1.outcome, OUT_APPROVE, f1.detail);
        assertEq(f1.scope, 1, "APPROVE_PAYMENT");
    }

    /// @dev The old behaviour, kept as the no-argument fallback: first match. In the
    ///      sponsored transaction B's frame would take entry 0 (A's witness) and fail.
    function test_Sponsored_FirstMatchCannotServeTheSponsor() public {
        Run memory r = _module("sponsored", 1, B, abi.encode(seedB, rootB, verifierAddr));
        assertEq(r.copied, 0, "first match is A's witness");
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT invalid SPHINCS+ signature");
    }

    /// @dev frame-sigparam-copy-removed + first-match fallback: self_verify (flags 0x3) skips
    ///      a SECP256K1 entry and an ARBITRARY entry with an explicit msg, copies entry 2 with
    ///      SIGDATACOPY and APPROVEs. With the old SIGPARAM(0x04) copy this halted.
    function test_FirstMatch_SelfVerifyApprovesUnderCurrentSpec() public {
        Run memory r = _frame("first-match", 0);
        assertEq(r.copied, 2);
        assertEq(r.outcome, OUT_APPROVE, r.detail);
        assertEq(r.scope, 3, "APPROVE_EXECUTION_AND_PAYMENT");
    }

    /// @dev An index that names another account's witness verifies that witness against
    ///      this account's key and fails; the index never grants anything by itself.
    function test_Index_PointingAtAnotherWitnessFails() public {
        Run memory r = _module("sponsored", 1, B, abi.encode(seedB, rootB, verifierAddr, uint256(0)));
        assertEq(r.copied, 0);
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT invalid SPHINCS+ signature");
    }

    function test_Index_OutOfRangeReverts() public {
        Run memory r = _module("sponsored", 0, A, abi.encode(seedA, rootA, verifierAddr, uint256(2)));
        assertEq(r.outcome, OUT_REVERT);
        assertEq(r.detail, "REVERT signature index out of range");
        assertEq(r.cd.length, 0, "verifier never called");
    }

    function test_Index_MustNameAnArbitraryEmptyMsgEntry() public {
        // entry 0: SECP256K1; entry 1: ARBITRARY with an explicit 32-byte msg
        for (uint256 i; i < 2; ++i) {
            Run memory r = _module("first-match", 0, A, abi.encode(seedA, rootA, verifierAddr, i));
            assertEq(r.outcome, OUT_REVERT);
            assertEq(r.detail, "REVERT not an ARBITRARY tx signature");
            assertEq(r.cd.length, 0, "verifier never called");
        }
    }
}
