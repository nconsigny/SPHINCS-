// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/SphincsAccount.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";

/// @notice Pins the AND-composition invariant for SphincsAccount.
///
/// Before this hardening `_requireForExecute` accepted either the EntryPoint
/// OR the owner EOA. That made the hybrid validation OR-composed in practice:
/// a broken/leaked ECDSA key alone could call `execute` and chain into
/// `rotateKeys` / `rotateOwner` via the `address(this)` self-call branch,
/// fully capturing the account without any SPHINCS+ signature.
///
/// These tests assert that:
///   1. Owner-EOA cannot call `execute` / `executeBatch` directly.
///   2. The EntryPoint can.
///   3. `rotateKeys` / `rotateOwner` are not reachable from owner-EOA or any
///      external account — only from `address(this)` (self-call) or the EP.
contract SphincsAccountAccessControlTest is Test {
    SphincsAccount account;

    address ep      = makeAddr("entryPoint");
    address owner   = makeAddr("owner");
    address attacker = makeAddr("attacker");
    address verifier = makeAddr("verifier"); // never invoked in these tests

    // Arbitrary sentinels — the verifier is never invoked here. They must still be
    // TOP-aligned (low 128 bits zero): `SphincsAccount` now rejects non-canonical
    // keys wherever they would be committed, so a low-aligned sentinel would trip
    // NonCanonicalKey in the constructor instead of exercising access control.
    bytes32 constant PK_SEED = bytes32(uint256(0xA1) << 128);
    bytes32 constant PK_ROOT = bytes32(uint256(0xA2) << 128);

    function setUp() public {
        account = new SphincsAccount(
            IEntryPoint(ep),
            owner,
            verifier,
            PK_SEED,
            PK_ROOT
        );
    }

    // ── execute / executeBatch ─────────────────────────────────────────────

    function test_OwnerEoa_CannotCallExecute_Directly() public {
        vm.prank(owner);
        vm.expectRevert(SphincsAccount.NotEntryPoint.selector);
        account.execute(address(0xdead), 0, "");
    }

    function test_RandomEoa_CannotCallExecute_Directly() public {
        vm.prank(attacker);
        vm.expectRevert(SphincsAccount.NotEntryPoint.selector);
        account.execute(address(0xdead), 0, "");
    }

    function test_OwnerEoa_CannotCallExecuteBatch_Directly() public {
        BaseAccount.Call[] memory calls = new BaseAccount.Call[](1);
        calls[0] = BaseAccount.Call({target: address(0xdead), value: 0, data: ""});
        vm.prank(owner);
        vm.expectRevert(SphincsAccount.NotEntryPoint.selector);
        account.executeBatch(calls);
    }

    function test_EntryPoint_CanCallExecute() public {
        // Empty calldata to an EOA is a no-op and does not revert.
        vm.prank(ep);
        account.execute(makeAddr("target"), 0, "");
    }

    // ── rotateKeys ─────────────────────────────────────────────────────────
    //
    // The bug being prevented: previously, owner-EOA could
    //     account.execute(account, 0, abi.encodeCall(rotateKeys, (s, r)))
    // and the inner self-call would satisfy `msg.sender == address(this)`.
    // With execute now EP-only, that chain requires a fully validated
    // (ECDSA + SPHINCS+) UserOp.

    function test_OwnerEoa_CannotCallRotateKeys_Directly() public {
        vm.prank(owner);
        vm.expectRevert(SphincsAccount.NotSelfOrEntryPoint.selector);
        account.rotateKeys(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128));
    }

    function test_RandomEoa_CannotCallRotateKeys_Directly() public {
        vm.prank(attacker);
        vm.expectRevert(SphincsAccount.NotSelfOrEntryPoint.selector);
        account.rotateKeys(bytes32(uint256(1) << 128), bytes32(uint256(2) << 128));
    }

    function test_EntryPoint_CanCallRotateKeys() public {
        vm.prank(ep);
        account.rotateKeys(bytes32(uint256(0xB1) << 128), bytes32(uint256(0xB2) << 128));
        assertEq(account.pkSeed(), bytes32(uint256(0xB1) << 128));
        assertEq(account.pkRoot(), bytes32(uint256(0xB2) << 128));
    }

    // ── key-shape validation ───────────────────────────────────────────────
    //
    // A non-canonical key is unusable by every verifier, so committing one would
    // brick the account: `rotateKeys` is only reachable through a fully validated
    // UserOp, which can no longer be produced once the stored key is unusable.

    function test_EntryPoint_CannotRotateToNonCanonicalKey() public {
        vm.prank(ep);
        vm.expectRevert(SphincsAccount.NonCanonicalKey.selector);
        account.rotateKeys(bytes32(uint256(0xB1)), bytes32(uint256(0xB2) << 128));
    }

    function test_Constructor_RejectsNonCanonicalKey() public {
        vm.expectRevert(SphincsAccount.NonCanonicalKey.selector);
        new SphincsAccount(IEntryPoint(ep), owner, verifier, PK_SEED, bytes32(uint256(0xA2)));
    }

    // ── rotateOwner ────────────────────────────────────────────────────────

    function test_OwnerEoa_CannotCallRotateOwner_Directly() public {
        vm.prank(owner);
        vm.expectRevert(SphincsAccount.NotSelfOrEntryPoint.selector);
        account.rotateOwner(attacker);
    }

    function test_RandomEoa_CannotCallRotateOwner_Directly() public {
        vm.prank(attacker);
        vm.expectRevert(SphincsAccount.NotSelfOrEntryPoint.selector);
        account.rotateOwner(attacker);
    }

    function test_EntryPoint_CanCallRotateOwner() public {
        address newOwner = makeAddr("newOwner");
        vm.prank(ep);
        account.rotateOwner(newOwner);
        assertEq(account.owner(), newOwner);
    }
}
