// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "account-abstraction/core/BaseAccount.sol";
import "account-abstraction/core/Helpers.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

/// @title SphincsAccount - Hybrid ECDSA + SPHINCS+ account using a SHARED verifier
/// @notice Keys stored in storage (not immutable) to support future key rotation.
///         The shared verifier is deployed once and used by all accounts.
/// @dev    Storage: slot 0 = `owner`, slot 1 = `_pkSeed16 ‖ _pkRoot16`. Both
///         n=16 key halves share ONE slot, so validation pays a single cold
///         SLOAD for the SPHINCS+ key instead of two.
contract SphincsAccount is BaseAccount {
    using ECDSA for bytes32;

    IEntryPoint private immutable _entryPoint;
    address public immutable verifier;       // Shared verifier (same for all users)
    address public owner;                    // ECDSA signer (rotatable)
    bytes16 private _pkSeed16;               // SPHINCS+ public seed, top 16 B (rotatable)
    bytes16 private _pkRoot16;               // SPHINCS+ Merkle root, top 16 B (rotatable)

    /// @dev n=16 key shape: the 16-byte pkSeed / pkRoot occupy the TOP half of
    ///      each word, low 128 bits zero — the same mask every verifier and the
    ///      signer applies.
    bytes32 private constant N_MASK =
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000;

    error NotSelfOrEntryPoint();
    error NotEntryPoint();
    error NonCanonicalKey();
    /// @notice The ECDSA owner would be address(0), which no signature recovers to.
    error ZeroOwner();
    /// @notice pkRoot would be zero, which no honest verify ever produces.
    error ZeroRoot();

    event KeysRotated(bytes32 pkSeed, bytes32 pkRoot);
    event OwnerRotated(address indexed previousOwner, address indexed newOwner);

    constructor(
        IEntryPoint ep,
        address _owner,
        address _verifier,
        bytes32 _pkSeed,
        bytes32 _pkRoot
    ) {
        // An owner-0 account can never validate (ECDSA.tryRecover never yields
        // address(0) without an error) and could never be repaired, because
        // rotation itself needs a validated UserOp. (review acct-brickable-owner-zero-key)
        require(_owner != address(0), ZeroOwner());
        _requireCanonicalKey(_pkSeed, _pkRoot);
        _entryPoint = ep;
        verifier = _verifier;
        owner = _owner;
        // Lossless: `_requireCanonicalKey` proved the low 128 bits are zero.
        _pkSeed16 = bytes16(_pkSeed);
        _pkRoot16 = bytes16(_pkRoot);
    }

    /// @dev Reject a non-canonical key at the point it would be COMMITTED, not
    ///      just when it is used. Every verifier reverts on a non-top-aligned
    ///      pkSeed/pkRoot, so storing one permanently bricks the account:
    ///      recovery would have to run `rotateKeys` through `execute` →
    ///      EntryPoint → `_validateSignature`, and that path can never pass
    ///      again once the stored key is unusable. Validating here also keeps
    ///      `SphincsAccountFactory`'s CREATE2 salt canonical, so one logical key
    ///      maps to exactly one account address.
    ///      A zero pkRoot is rejected for the same reason: the verifier's final
    ///      node equals 0 with probability 2^-128, so that key is unusable and is
    ///      almost certainly an uninitialised value.
    function _requireCanonicalKey(bytes32 _pkSeed, bytes32 _pkRoot) private pure {
        require(_pkRoot != 0, ZeroRoot());
        require(
            (_pkSeed & N_MASK) == _pkSeed && (_pkRoot & N_MASK) == _pkRoot,
            NonCanonicalKey()
        );
    }

    function entryPoint() public view override returns (IEntryPoint) {
        return _entryPoint;
    }

    /// @notice SPHINCS+ public seed as the canonical top-aligned word (low 128
    ///         bits zero) — the exact value passed to the verifier. Same ABI as
    ///         the former `bytes32 public pkSeed`.
    function pkSeed() public view returns (bytes32) {
        return bytes32(_pkSeed16);
    }

    /// @notice SPHINCS+ Merkle root as the canonical top-aligned word (low 128
    ///         bits zero). Same ABI as the former `bytes32 public pkRoot`.
    function pkRoot() public view returns (bytes32) {
        return bytes32(_pkRoot16);
    }

    /// @notice Only the EntryPoint can drive `execute` / `executeBatch`.
    /// @dev    Direct owner-EOA calls are intentionally forbidden so that the
    ///         hybrid ECDSA + SPHINCS+ check in `_validateSignature` cannot be
    ///         bypassed. Without this, a leaked/broken ECDSA key alone would
    ///         authorize execution and reach `rotateKeys`/`rotateOwner` via
    ///         the `address(this)` self-call branch.
    function _requireForExecute() internal view override {
        require(msg.sender == address(entryPoint()), NotEntryPoint());
    }

    /// @notice Rotate SPHINCS+ keys. Can only be called by the account itself
    ///         (via execute) or by the EntryPoint during a UserOp.
    function rotateKeys(bytes32 newPkSeed, bytes32 newPkRoot) external {
        // Authorization first, so an unauthorized caller always gets
        // NotSelfOrEntryPoint regardless of the key shape it passed.
        require(msg.sender == address(this) || msg.sender == address(entryPoint()), NotSelfOrEntryPoint());
        _requireCanonicalKey(newPkSeed, newPkRoot);
        _pkSeed16 = bytes16(newPkSeed);
        _pkRoot16 = bytes16(newPkRoot);
        emit KeysRotated(newPkSeed, newPkRoot);
    }

    /// @notice Rotate ECDSA owner.
    function rotateOwner(address newOwner) external {
        require(msg.sender == address(this) || msg.sender == address(entryPoint()), NotSelfOrEntryPoint());
        require(newOwner != address(0), ZeroOwner());
        emit OwnerRotated(owner, newOwner);
        owner = newOwner;
    }

    /// @dev `bytes4(keccak256("verify(bytes32,bytes32,bytes32,bytes)"))` = 0x2bf6eda8.
    bytes4 private constant VERIFY_SELECTOR =
        bytes4(keccak256("verify(bytes32,bytes32,bytes32,bytes)"));

    /// @notice Validate hybrid signature: abi.encode(ecdsaSig, sphincsSig)
    /// @dev ERC-4337 requires `_validateSignature` to be TOTAL: any signature
    ///      failure must RETURN `SIG_VALIDATION_FAILED`, never revert (a revert
    ///      becomes EntryPoint `AA23` and reverts the whole bundle). Every
    ///      failure path below returns (review C13-acc-g1):
    ///        (1) a malformed 2-tuple — `_sliceHybridSignature` applies the exact
    ///            bounds rules of `abi.decode(sig, (bytes, bytes))` and reports
    ///            failure instead of reverting;
    ///        (2) ECDSA recovery on a bad-length / high-`s` / bad-`v` signature —
    ///            `tryRecoverCalldata`, never the reverting `recover`;
    ///        (3) a verifier that reverts, returns < 32 bytes, or returns any
    ///            first word other than 1 (no strict `abi.decode(.., (bool))`).
    ///      Both elements are read as calldata views of `userOp.signature`: no
    ///      self-call, no memory decode, one `calldatacopy` into the verify call.
    function _validateSignature(
        PackedUserOperation calldata userOp,
        bytes32 userOpHash
    ) internal view override returns (uint256 validationData) {
        (bool ok, bytes calldata ecdsaSig, bytes calldata sphincsSig) =
            _sliceHybridSignature(userOp.signature);
        if (!ok) return SIG_VALIDATION_FAILED;

        (address recovered, ECDSA.RecoverError err, ) =
            ECDSA.tryRecoverCalldata(userOpHash, ecdsaSig);
        if (err != ECDSA.RecoverError.NoError || recovered != owner) {
            return SIG_VALIDATION_FAILED;
        }

        if (!_sphincsVerify(pkSeed(), pkRoot(), userOpHash, sphincsSig)) {
            return SIG_VALIDATION_FAILED;
        }
        return SIG_VALIDATION_SUCCESS;
    }

    /// @dev Calldata views `(a, b)` of `blob = abi.encode(bytes a, bytes b)`.
    ///      `ok` is false exactly when `abi.decode(blob, (bytes, bytes))` would
    ///      revert: `len >= 0x40`, and for each element `i`
    ///      `off_i <= len - 0x20` and `len_i <= len - 0x20 - off_i`. (Those two
    ///      bounds also imply the decoder's `<= 2^64-1` offset/length guards.)
    ///      Like `abi.decode`, offsets need not be canonical and trailing bytes
    ///      are ignored. On failure the returned views are empty.
    function _sliceHybridSignature(bytes calldata blob)
        private pure returns (bool ok, bytes calldata a, bytes calldata b)
    {
        assembly ("memory-safe") {
            let base := blob.offset
            let len := blob.length
            ok := iszero(lt(len, 0x40))
            let lim := sub(len, 0x20) // only meaningful while ok (len >= 0x40)
            let o0 := mul(ok, calldataload(base))
            ok := and(ok, iszero(gt(o0, lim)))
            o0 := mul(ok, o0)
            let l0 := calldataload(add(base, o0))
            ok := and(ok, iszero(gt(l0, sub(lim, o0))))
            let o1 := mul(ok, calldataload(add(base, 0x20)))
            ok := and(ok, iszero(gt(o1, lim)))
            o1 := mul(ok, o1)
            let l1 := calldataload(add(base, o1))
            ok := and(ok, iszero(gt(l1, sub(lim, o1))))
            a.offset := add(add(base, o0), 0x20)
            a.length := mul(ok, l0)
            b.offset := add(add(base, o1), 0x20)
            b.length := mul(ok, l1)
        }
    }

    /// @dev `verifier.verify(seed, root, m, sig)` with `sig` copied straight from
    ///      calldata. The call data is byte-identical to
    ///      `abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", ..)`
    ///      (zero-padded tail). True iff the call succeeds, returns >= 32 bytes,
    ///      and the first returned word is exactly 1.
    function _sphincsVerify(bytes32 seed, bytes32 root, bytes32 m, bytes calldata sig)
        private view returns (bool valid)
    {
        address v = verifier;
        bytes4 sel = VERIFY_SELECTOR;
        assembly ("memory-safe") {
            let p := mload(0x40)
            let l := sig.length
            mstore(p, sel)
            mstore(add(p, 0x04), seed)
            mstore(add(p, 0x24), root)
            mstore(add(p, 0x44), m)
            mstore(add(p, 0x64), 0x80)
            mstore(add(p, 0x84), l)
            mstore(add(add(p, 0xa4), and(l, not(31))), 0) // zero the padding word
            calldatacopy(add(p, 0xa4), sig.offset, l)
            let okc := staticcall(gas(), v, p, add(0xa4, and(add(l, 31), not(31))), 0x00, 0x20)
            valid := and(okc, and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x00), 1)))
        }
    }

    receive() external payable {}
}
