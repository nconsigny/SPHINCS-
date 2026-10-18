// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/SphincsAccount.sol";
import "../src/SphincsAccountFactory.sol";
import "account-abstraction/core/EntryPoint.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";

/// @dev Verifier stand-in that answers every call with one fixed 32-byte word.
contract FixedWordVerifier {
    uint256 immutable word;

    constructor(uint256 w) {
        word = w;
    }

    fallback() external {
        uint256 w = word;
        assembly {
            mstore(0, w)
            return(0, 0x20)
        }
    }
}

/// @notice Review hardening for the ERC-4337 account and its factory:
///   * acct-brickable-owner-zero-key: owner 0 or pkRoot 0 can never validate and could never
///     be repaired, so the constructor / rotation refuse them; rotations emit events.
///   * factory-undeployable-prediction-nonidempotent: `getAddress` predicted addresses that
///     `createAccount` could never deploy, and a second `createAccount` reverted (breaking
///     EntryPoint `getSenderAddress` after deployment).
///   * acct-gas-calldata-decode (also closes acct-bool-decode-not-total): validation decodes
///     the hybrid signature from calldata and must stay total — malformed blobs and odd
///     verifier answers return SIG_VALIDATION_FAILED, never revert.
contract SphincsAccountHardeningTest is Test {
    bytes32 constant SEED = bytes32(uint256(0xA1) << 128);
    bytes32 constant ROOT = bytes32(uint256(0xA2) << 128);

    address ep = makeAddr("entryPoint");
    address verifier = makeAddr("verifier");

    // ── account constructor / rotation ─────────────────────────────────────

    function test_Constructor_RejectsZeroOwner() public {
        vm.expectRevert(SphincsAccount.ZeroOwner.selector);
        new SphincsAccount(IEntryPoint(ep), address(0), verifier, SEED, ROOT);
    }

    function test_Constructor_RejectsZeroRoot() public {
        vm.expectRevert(SphincsAccount.ZeroRoot.selector);
        new SphincsAccount(IEntryPoint(ep), makeAddr("owner"), verifier, SEED, bytes32(0));
    }

    function test_Rotation_RejectsZeroAndEmitsEvents() public {
        SphincsAccount a = new SphincsAccount(IEntryPoint(ep), makeAddr("owner"), verifier, SEED, ROOT);

        vm.startPrank(ep);
        vm.expectRevert(SphincsAccount.ZeroRoot.selector);
        a.rotateKeys(SEED, bytes32(0));
        vm.expectRevert(SphincsAccount.ZeroOwner.selector);
        a.rotateOwner(address(0));

        bytes32 s2 = bytes32(uint256(0xB1) << 128);
        bytes32 r2 = bytes32(uint256(0xB2) << 128);
        vm.expectEmit(address(a));
        emit SphincsAccount.KeysRotated(s2, r2);
        a.rotateKeys(s2, r2);

        address o2 = makeAddr("owner2");
        vm.expectEmit(address(a));
        emit SphincsAccount.OwnerRotated(makeAddr("owner"), o2);
        a.rotateOwner(o2);
        vm.stopPrank();

        assertEq(a.pkSeed(), s2);
        assertEq(a.pkRoot(), r2);
        assertEq(a.owner(), o2);
    }

    // ── factory ────────────────────────────────────────────────────────────

    function test_Factory_NeverPredictsAnUndeployableAddress() public {
        SphincsAccountFactory f = new SphincsAccountFactory(IEntryPoint(ep), verifier);
        address o = makeAddr("owner");
        // a 16-byte key passed low-aligned
        vm.expectRevert(SphincsAccountFactory.NonCanonicalKey.selector);
        f.getAddress(o, SEED >> 128, ROOT);
        vm.expectRevert(SphincsAccountFactory.NonCanonicalKey.selector);
        f.getAddress(o, SEED, ROOT >> 128);
        vm.expectRevert(SphincsAccountFactory.ZeroOwner.selector);
        f.getAddress(address(0), SEED, ROOT);
        vm.expectRevert(SphincsAccountFactory.ZeroRoot.selector);
        f.getAddress(o, SEED, bytes32(0));
        vm.expectRevert(SphincsAccountFactory.NonCanonicalKey.selector);
        f.createAccount(o, SEED >> 128, ROOT);
    }

    function test_Factory_CreateAccountIsIdempotent() public {
        SphincsAccountFactory f = new SphincsAccountFactory(IEntryPoint(ep), verifier);
        address o = makeAddr("owner");
        address predicted = f.getAddress(o, SEED, ROOT);
        SphincsAccount a1 = f.createAccount(o, SEED, ROOT);
        assertEq(address(a1), predicted);
        SphincsAccount a2 = f.createAccount(o, SEED, ROOT);
        assertEq(address(a2), address(a1), "second call returns the existing account");
    }

    /// @dev Real EntryPoint v0.9: getSenderAddress(initCode) must keep answering the account
    ///      address after the account exists (it used to return address(0) once the second
    ///      CREATE2 collided and reverted).
    function test_Factory_GetSenderAddressBeforeAndAfterDeployment() public {
        EntryPoint entryPoint = new EntryPoint();
        SphincsAccountFactory f = new SphincsAccountFactory(IEntryPoint(address(entryPoint)), verifier);
        address o = makeAddr("owner");
        address predicted = f.getAddress(o, SEED, ROOT);
        bytes memory initCode =
            abi.encodePacked(address(f), abi.encodeCall(SphincsAccountFactory.createAccount, (o, SEED, ROOT)));

        vm.expectRevert(abi.encodeWithSelector(IEntryPoint.SenderAddressResult.selector, predicted));
        entryPoint.getSenderAddress(initCode);

        f.createAccount(o, SEED, ROOT);
        vm.expectRevert(abi.encodeWithSelector(IEntryPoint.SenderAddressResult.selector, predicted));
        entryPoint.getSenderAddress(initCode);
    }

    // ── validation stays total ─────────────────────────────────────────────

    function _op(address sender, bytes memory signature) internal pure returns (PackedUserOperation memory op) {
        op.sender = sender;
        op.signature = signature;
    }

    function _validate(SphincsAccount a, bytes memory signature, bytes32 h) internal returns (bool ok, uint256 vd) {
        vm.prank(ep);
        bytes memory ret;
        (ok, ret) = address(a).call(abi.encodeCall(BaseAccount.validateUserOp, (_op(address(a), signature), h, 0)));
        if (ok) vd = abi.decode(ret, (uint256));
    }

    function test_Validation_VerifierAnswerMustBeExactlyOne() public {
        (address o, uint256 pk) = makeAddrAndKey("owner");
        bytes32 h = keccak256("userOpHash");
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, h);
        bytes memory sig = abi.encode(abi.encodePacked(r, s, v), new bytes(3688));

        uint256[4] memory words = [uint256(1), 0, 2, type(uint256).max];
        for (uint256 i; i < words.length; ++i) {
            SphincsAccount a =
                new SphincsAccount(IEntryPoint(ep), o, address(new FixedWordVerifier(words[i])), SEED, ROOT);
            (bool ok, uint256 vd) = _validate(a, sig, h);
            assertTrue(ok, "validateUserOp must not revert");
            assertEq(vd, words[i] == 1 ? 0 : 1, "only the word 1 validates");
        }
    }

    function test_Validation_MalformedBlobsFailWithoutReverting() public {
        (address o, uint256 pk) = makeAddrAndKey("owner");
        bytes32 h = keccak256("userOpHash");
        SphincsAccount a = new SphincsAccount(IEntryPoint(ep), o, address(new FixedWordVerifier(1)), SEED, ROOT);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, h);
        bytes memory good = abi.encode(abi.encodePacked(r, s, v), new bytes(3688));
        (bool ok, uint256 vd) = _validate(a, good, h);
        assertTrue(ok);
        assertEq(vd, 0, "well-formed blob validates");

        bytes[] memory bad = new bytes[](5);
        bad[0] = "";
        bad[1] = new bytes(0x3f);
        bad[2] = abi.encode(uint256(1) << 64, uint256(0x40)); // first offset out of range
        bad[3] = abi.encode(uint256(0x40), uint256(0x40), uint256(type(uint64).max)); // huge length
        // 3688 is not a multiple of 32, so the encoding has 24 bytes of tail padding;
        // cut 25 bytes so the second element really runs past the end of the blob.
        bytes memory trunc = new bytes(good.length - 25);
        for (uint256 i; i < trunc.length; ++i) trunc[i] = good[i];
        bad[4] = trunc;
        for (uint256 i; i < bad.length; ++i) {
            (ok, vd) = _validate(a, bad[i], h);
            assertTrue(ok, "malformed blob must not revert");
            assertEq(vd, 1, "malformed blob must fail validation");
        }
    }
}
