// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @title SphincsFrameAccount - EIP-8141 Frame Transaction account with SPHINCS+ C6
/// @notice Delegates SPHINCS+ verification to an external verifier (SphincsC6Asm).
///         In a VERIFY frame: calls verifier.verify(sigHash, sig), then calls APPROVE.
///         In a SENDER frame: executes arbitrary calls.
/// @dev The APPROVE opcode (0xaa) is EIP-8141 specific and only works on frame-enabled chains.
///      This contract is compiled normally; the APPROVE call is done via a raw CALL to
///      a precompile-like address or inline assembly with the custom opcode.
contract SphincsFrameAccount {
    /// @dev The public key and verifier are immutables, so they live in code as
    ///      PUSH32 and are never in storage. In a frame transaction
    ///      accessed_storage_keys starts empty, so storage keys would cost three
    ///      cold SLOADs (3 x 2100 gas) on every verify. They also keep the verify
    ///      path free of storage reads.
    bytes32 public immutable pkSeed;
    bytes32 public immutable pkRoot;
    address public immutable verifier; // shared SPHINCs- verifier
    address public owner;    // slot 0 — bookkeeping only; see `execute`

    /// @notice EIP-8141 `ENTRY_POINT` — the `caller` of every VERIFY / DEFAULT frame.
    address internal constant ENTRY_POINT = address(0xaa);

    /// @notice `src/SphincsFrameVerify.yul`, DELEGATECALLed by `verifyFrameAndApprove`.
    /// @dev A malicious module would own the account outright via DELEGATECALL,
    ///      so it is fixed at deploy time and is never taken from calldata or
    ///      rotated.
    address public immutable frameModule;

    /// @notice `execute` was called by anything other than the account itself.
    error NotSelf();
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

    /// @dev Low half of a 32-byte word. n=16 keys are top-aligned, so these bits must
    ///      be zero. A constant, so it takes no storage slot.
    bytes32 private constant N_MASK_LOW = bytes32(uint256(type(uint128).max));

    constructor(bytes32 _seed, bytes32 _root, address _verifier, address _owner, address _frameModule) {
        // Nothing here can be changed later (no key, verifier or module rotation), and
        // `execute` only runs after an approved VERIFY frame. A key the verifiers reject,
        // a code-less verifier or a code-less module would therefore brick the account
        // and lock any ETH it receives, so refuse them at deploy time.
        // `_frameModule == address(0)` stays allowed for the legacy `verifyAndApprove`
        // configuration. (review frame-ctor-unchecked-module)
        require((_seed & N_MASK_LOW) == 0 && (_root & N_MASK_LOW) == 0, NonCanonicalKey());
        require(_verifier.code.length != 0, VerifierHasNoCode());
        require(_frameModule == address(0) || _frameModule.code.length != 0, FrameModuleHasNoCode());
        pkSeed = _seed;
        pkRoot = _root;
        verifier = _verifier;
        owner = _owner;
        frameModule = _frameModule;
    }

    /// @notice EIP-8141-conformant VERIFY-frame entry point: verifies the FIRST
    ///         `ARBITRARY` entry of `tx.signatures` with an empty `msg`. Use the
    ///         `verifyFrameAndApprove(uint256)` overload when this account's witness
    ///         is not that entry, e.g. a sponsored transaction whose sender and
    ///         sponsor are both SphincsFrameAccounts.
    /// @dev The digest comes from `TXPARAM(0x08)` (`compute_sig_hash(tx)`), the
    ///      witness bytes from `SIGDATACOPY`, and the approval scope from
    ///      `FRAMEPARAM(0x06)`. This is the function a frame-enabled chain should
    ///      target; `verifyAndApprove` below is the pre-`signatures` demo path and
    ///      is NOT replay-safe.
    ///
    ///      Logic lives in `src/SphincsFrameVerify.yul` because TXPARAM (0xb0),
    ///      FRAMEPARAM (0xb3), SIGPARAM (0xb4), SIGDATACOPY (0xb5) and APPROVE
    ///      (0xaa) are unknown to solc and only reachable via Yul `verbatim`, which
    ///      Solidity inline assembly does not expose. DELEGATECALL keeps `ADDRESS`
    ///      equal to this account, which `APPROVE` requires. The module reads no
    ///      storage. Its only input is the DELEGATECALL payload built below from
    ///      this account's immutables, `pkSeed ‖ pkRoot ‖ verifier` (0x60 bytes),
    ///      plus `sigIndex` for the overload (0x80 bytes). The module refuses to
    ///      run unless it is delegatecalled. On success the module ends in
    ///      `APPROVE`, which exits the delegatecall frame successfully. The
    ///      approval is transaction-scoped and survives the return.
    ///
    ///      Reverts on any pre-8141 EVM: the five instructions above are
    ///      undefined opcodes there.
    function verifyFrameAndApprove() external {
        _verifyFrame(0, 0);
    }

    /// @notice As `verifyFrameAndApprove()`, but verifies `tx.signatures[sigIndex]`,
    ///         which must be an `ARBITRARY` entry with an empty `msg`.
    /// @dev The index comes from this frame's data, which `compute_sig_hash(tx)`
    ///      covers, so the witness commits to it. It only selects which entry's
    ///      bytes are checked against this account's key; a wrong index fails
    ///      verification. (review frame-first-arbitrary-entry)
    function verifyFrameAndApprove(uint256 sigIndex) external {
        _verifyFrame(0x20, sigIndex);
    }

    /// @param extra 0 (first-match) or 0x20 (append `sigIndex` to the module input).
    function _verifyFrame(uint256 extra, uint256 sigIndex) private {
        // VERIFY and DEFAULT frames both have `caller == ENTRY_POINT`; a SENDER
        // frame would have `caller == tx.sender`. Refusing anything else keeps this
        // inert outside a frame transaction (where APPROVE halts exceptionally).
        require(msg.sender == ENTRY_POINT, NotEntryPoint());
        address module = frameModule;
        require(module != address(0), NoFrameModule());

        bytes32 seed = pkSeed;
        bytes32 root = pkRoot;
        address v = verifier;
        assembly ("memory-safe") {
            // Scratch space above the free-memory pointer. Nothing is allocated,
            // and the function returns or reverts right after.
            let p := mload(0x40)
            mstore(p, seed)
            mstore(add(p, 0x20), root)
            mstore(add(p, 0x40), v)
            mstore(add(p, 0x60), sigIndex)
            let len := add(0x60, extra)
            // `gas()` is evaluated last, so GAS sits immediately before
            // DELEGATECALL, the form the validation-prefix opcode rules allow.
            if iszero(delegatecall(gas(), module, p, len, 0, 0)) {
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
    }

    /// @notice Verify SPHINCS+ signature and approve.
    ///         Called in a VERIFY frame with the signature as calldata.
    /// @dev DEMO PATH, NOT REPLAY-SAFE — kept for `script/send_frame_tx_c13.py`
    ///      and the existing tests, and because it is the shape the deployed
    ///      ethrex runtime uses. It trusts a caller-supplied `sigHash`, so a
    ///      witness is reusable for any transaction presenting the same digest;
    ///      the script compensates off-chain by binding the digest to
    ///      (chain_id, account, nonce, recipient, value). EIP-8141 also requires
    ///      a witness over the canonical hash to travel in an `ARBITRARY`
    ///      signature entry rather than in frame data, which this signature
    ///      cannot express. Use `verifyFrameAndApprove` on a frame-enabled chain.
    /// @param sigHash The transaction signature hash (passed by the frame)
    /// @param sig The raw SPHINCS+ C6 signature (3352 bytes)
    /// @param scope Approval scope: 1=sender, 2=payment, 3=both
    function verifyAndApprove(bytes32 sigHash, bytes calldata sig, uint256 scope) external {
        // Verify SPHINCS+ signature via the external verifier.
        // All SPHINCs- verifiers expose verify(pkSeed, pkRoot, message, sig);
        // pass the account's stored public key alongside the message hash.
        (bool success, bytes memory result) = verifier.staticcall(
            abi.encodeWithSignature(
                "verify(bytes32,bytes32,bytes32,bytes)",
                pkSeed,
                pkRoot,
                sigHash,
                sig
            )
        );
        // Error-surface contract (review C13-evm-f2 / L-01): every live verifier
        // RETURNS `false` for every soundness rejection — invalid Merkle root, FORS+C
        // forced-zero violation, and WOTS+C target-sum violation — so those all
        // land on the descriptive "invalid SPHINCS+ signature" path below. The
        // verifier only REVERTS on malformed *inputs* (wrong sig length /
        // non-canonical public key), for which "verify call failed" is correct.
        require(success && result.length >= 32, "verify call failed");
        bool valid = abi.decode(result, (bool));
        require(valid, "invalid SPHINCS+ signature");

        // Call APPROVE opcode (0xaa): stack args = (offset, length, scope)
        // This is EIP-8141 specific — only works on frame-enabled EVM
        assembly {
            // APPROVE(offset=0, length=0, scope=scope)
            // Since APPROVE is opcode 0xaa, we need custom bytecode.
            // For now, we use a placeholder that will work on ethrex.
            // In standard EVM this would revert (0xaa = LOG* family on some versions)
            //
            // The actual APPROVE call will be handled by the frame_tx.py script
            // which constructs the VERIFY frame data to include the APPROVE at the end.
        }
    }

    /// @notice Execute a call (for SENDER frames).
    /// @dev Self-call only. In a SENDER frame the account's own code runs with
    ///      `msg.sender == address(this)`, after the VERIFY frame has checked the
    ///      SPHINCS+ signature and APPROVEd — so authorization always comes from
    ///      the PQ-verified frame, never from a bare external call.
    ///
    ///      `owner` is deliberately NOT accepted here. This account is pure-PQ:
    ///      admitting the ECDSA owner would mean a broken or leaked ECDSA key
    ///      alone authorizes execution, the same OR-composition that
    ///      `SphincsAccount._requireForExecute` exists to prevent. `owner` stays
    ///      a bookkeeping field for off-chain tooling.
    function execute(address dest, uint256 value, bytes calldata data) external returns (bytes memory) {
        require(msg.sender == address(this), NotSelf());
        (bool success, bytes memory result) = dest.call{value: value}(data);
        require(success, "exec failed");
        return result;
    }

    receive() external payable {}
}
