// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsOwnerAccount - a post-quantum owner for an unmodified Safe on EIP-8141
/// @notice One contract per Safe owner, holding one public key of a SPHINCs- family verifier
///         (the prototype uses leanSphincs-f). It does two things and nothing else:
///
///           1. As the sender of an EIP-8141 frame transaction it checks its own signature in a
///              VERIFY frame (`verifyFrameAndApprove`). The transaction's SENDER frame then calls
///              `Safe.execTransaction` with `msg.sender` equal to this account, which the Safe
///              counts as a pre-validated signature (v = 1).
///           2. As a co-signer it answers the Safe's contract-signature check (v = 0) through
///              `isValidSignature`, in both forms the Safe has used: `(bytes32, bytes)` since
///              Safe 1.5.0 and `(bytes, bytes)` up to Safe 1.4.1.
///
///         There is no `execute`, no owner and no way to change the key, the verifier or the
///         module. Design, invariants and measured gas: docs/safe-pq-owners.md.
///
///         Research code. Not audited.
/// @dev    The key, the verifier and the module are immutables: they live in code as PUSH32, so
///         no path reads storage. A frame transaction starts with an empty
///         `accessed_storage_keys`, where each SLOAD would cost 2,100 gas, and the public
///         mempool only lets a validation prefix read the sender's own storage.
///
///         The contract has no CALL, CREATE, SSTORE, LOG or SELFDESTRUCT. Its only outgoing
///         calls are the STATICCALL to the verifier and the DELEGATECALL to the frame module,
///         which itself only STATICCALLs the verifier and runs `APPROVE`.
///         (test/SphincsOwnerAccountTest.t.sol scans the deployed code for this.)
///
///         A frame transaction's SENDER frames run with this account as `caller` at the
///         protocol level, without entering this code. Whatever the key signs in a frame
///         transaction therefore executes as this account, including a plain value transfer:
///         that is how ETH held here (gas money, Safe refunds) is spent.
contract SphincsOwnerAccount {
    bytes32 public immutable pkSeed;
    bytes32 public immutable pkRoot;
    /// @notice Shared stateless verifier, `verify(bytes32,bytes32,bytes32,bytes) -> bool`.
    address public immutable verifier;
    /// @notice `src/SphincsFrameVerify.yul`, DELEGATECALLed by `verifyFrameAndApprove`.
    /// @dev A DELEGATECALL target owns the account, so it is fixed at deploy time and never
    ///      taken from calldata. Zero means the account can only co-sign: it can never send a
    ///      frame transaction, and ETH sent to it stays there.
    address public immutable frameModule;

    /// @notice EIP-8141 `ENTRY_POINT`, the `caller` of every VERIFY and DEFAULT frame.
    address internal constant ENTRY_POINT = address(0xaa);

    /// @dev `bytes4(keccak256("isValidSignature(bytes32,bytes)"))`, ERC-1271.
    bytes4 internal constant MAGIC_HASH = 0x1626ba7e;
    /// @dev `bytes4(keccak256("isValidSignature(bytes,bytes)"))`, the pre-standard form.
    bytes4 internal constant MAGIC_DATA = 0x20c13b0b;
    bytes4 internal constant INVALID = 0xffffffff;

    /// @notice A frame entry point was called by something other than `ENTRY_POINT`.
    error NotEntryPoint();
    /// @notice No EIP-8141 verify module was configured at deploy time.
    error NoFrameModule();
    /// @notice pkSeed or pkRoot has low-128 bits set; every verifier rejects such a key.
    error NonCanonicalKey();
    /// @notice The verifier address has no code.
    error VerifierHasNoCode();
    /// @notice A non-zero frame module address has no code.
    error FrameModuleHasNoCode();

    /// @dev Low half of a 32-byte word. n=16 keys are top-aligned, so these bits must be zero.
    bytes32 private constant N_MASK_LOW = bytes32(uint256(type(uint128).max));

    /// @dev The same checks as SphincsFrameAccount. Nothing here can be changed later, so a key
    ///      the verifiers reject, a code-less verifier or a code-less module would leave an
    ///      account that can never sign.
    constructor(bytes32 _seed, bytes32 _root, address _verifier, address _frameModule) {
        require((_seed & N_MASK_LOW) == 0 && (_root & N_MASK_LOW) == 0, NonCanonicalKey());
        require(_verifier.code.length != 0, VerifierHasNoCode());
        require(_frameModule == address(0) || _frameModule.code.length != 0, FrameModuleHasNoCode());
        pkSeed = _seed;
        pkRoot = _root;
        verifier = _verifier;
        frameModule = _frameModule;
    }

    // ───────────────────────────── EIP-8141 VERIFY frame ─────────────────────────────

    /// @notice VERIFY-frame entry point. Verifies the first `ARBITRARY` entry of
    ///         `tx.signatures` that has an empty `msg`, over `TXPARAM(0x08)`
    ///         (`compute_sig_hash(tx)`), then `APPROVE`s the scope the frame's flags allow.
    /// @dev Nothing in the frame's data is a digest or a signature. The module takes the digest
    ///      from `TXPARAM(0x08)` and the witness from `SIGDATACOPY`; its only input from here is
    ///      `pkSeed ‖ pkRoot ‖ verifier`, read from this account's immutables.
    function verifyFrameAndApprove() external {
        _verifyFrame(0, 0);
    }

    /// @notice As `verifyFrameAndApprove()`, for `tx.signatures[sigIndex]`, which must be an
    ///         `ARBITRARY` entry with an empty `msg`.
    /// @dev The index only selects which entry is checked against this account's key. It comes
    ///      from frame data, which `compute_sig_hash(tx)` covers.
    function verifyFrameAndApprove(uint256 sigIndex) external {
        _verifyFrame(0x20, sigIndex);
    }

    /// @param extra 0 (first match) or 0x20 (append `sigIndex` to the module input).
    function _verifyFrame(uint256 extra, uint256 sigIndex) private {
        // VERIFY and DEFAULT frames have `caller == ENTRY_POINT`. Anything else is refused, so
        // the module is never reached from an ordinary call.
        require(msg.sender == ENTRY_POINT, NotEntryPoint());
        address module = frameModule;
        require(module != address(0), NoFrameModule());

        bytes32 seed = pkSeed;
        bytes32 root = pkRoot;
        address v = verifier;
        assembly ("memory-safe") {
            // Scratch above the free-memory pointer; the function returns or reverts next.
            let p := mload(0x40)
            mstore(p, seed)
            mstore(add(p, 0x20), root)
            mstore(add(p, 0x40), v)
            mstore(add(p, 0x60), sigIndex)
            // `gas()` is evaluated last, so GAS sits immediately before DELEGATECALL, the only
            // form of GAS the validation-prefix opcode rules allow.
            if iszero(delegatecall(gas(), module, p, add(0x60, extra), 0, 0)) {
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
    }

    // ───────────────────────────── Safe contract signatures ─────────────────────────────

    /// @notice ERC-1271, as Safe 1.5.0 and later call it. `hash` is the Safe transaction hash
    ///         (or any other 32-byte digest the caller wants checked).
    /// @return `0x1626ba7e` when `signature` is this key's signature over `hash`, otherwise
    ///         `0xffffffff`. Never reverts on a bad signature.
    /// @dev `hash` is verified as given. It is not wrapped or re-hashed: an unmodified Safe
    ///      passes its own transaction hash, and that is what the owner signs.
    function isValidSignature(bytes32 hash, bytes calldata signature) external view returns (bytes4) {
        return _verify(hash, signature) ? MAGIC_HASH : INVALID;
    }

    /// @notice The pre-standard form, as Safe up to 1.4.1 calls it. `data` is the EIP-712
    ///         pre-image of the Safe transaction (`0x19 0x01 ‖ domainSeparator ‖ safeTxHash`).
    /// @return `0x20c13b0b` when `signature` is this key's signature over `keccak256(data)`,
    ///         otherwise `0xffffffff`.
    function isValidSignature(bytes calldata data, bytes calldata signature) external view returns (bytes4) {
        return _verify(keccak256(data), signature) ? MAGIC_DATA : INVALID;
    }

    /// @dev A pure check: the key from immutables, one STATICCALL to the verifier. True only
    ///      when the call succeeds and returns exactly 32 bytes equal to 1. A verifier revert
    ///      (wrong signature length), a short or long return, or any other word is false.
    function _verify(bytes32 digest, bytes calldata signature) private view returns (bool ok) {
        bytes32 seed = pkSeed;
        bytes32 root = pkRoot;
        address v = verifier;
        assembly ("memory-safe") {
            // verify(bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes sig), 0x2bf6eda8,
            // built in scratch above the free-memory pointer.
            let p := mload(0x40)
            mstore(p, shl(224, 0x2bf6eda8))
            mstore(add(p, 0x04), seed)
            mstore(add(p, 0x24), root)
            mstore(add(p, 0x44), digest)
            mstore(add(p, 0x64), 0x80)
            mstore(add(p, 0x84), signature.length)
            let tail := add(p, 0xa4)
            // Zero the last word first, so the ABI padding after the signature is zero.
            mstore(add(tail, and(signature.length, not(31))), 0)
            calldatacopy(tail, signature.offset, signature.length)
            let len := add(0xa4, and(add(signature.length, 31), not(31)))
            // The output word is cleared first: a call that returns nothing leaves it at 0.
            mstore(0x00, 0)
            let success := staticcall(gas(), v, p, len, 0x00, 0x20)
            ok := and(success, and(eq(returndatasize(), 0x20), eq(mload(0x00), 1)))
        }
    }

    /// @notice Accepts ETH: gas money for the frame transactions this account sends, and the
    ///         refunds a Safe pays to `tx.origin`. Safe up to 1.4.1 pays them with `send`, so
    ///         this must run within the 2,300-gas stipend.
    receive() external payable {}
}
