// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "./helpers/SafePqHarness.sol";

/// @notice Unmodified Safe code (v1.4.1, v1.5.0 and main at 247b8ce, see foundry.toml) whose
///         owners are SphincsOwnerAccounts with leanSphincs-f keys. One owner calls
///         `execTransaction` as `msg.sender` (and `tx.origin`, as in an EIP-8141 SENDER frame)
///         and counts as a pre-validated signature (v = 1). Every co-signer is a contract
///         signature (v = 0) that the Safe checks by calling `isValidSignature` on the
///         co-signer's owner account. All signatures are real, from the Rust CLI over FFI.
///
///         The frame transaction around this call (the sender's VERIFY frame, then this call as
///         the SENDER frame) is in SafePqOwnersFrameTest.
///
///         Security invariants of docs/safe-pq-owners.md covered here:
///           6. test_CoSignature_BoundToNonce, test_CoSignature_BoundToSafe,
///              test_CoSignature_BoundToChain
///         and the Safe-side facts the design relies on: test_PreValidated_*, test_Refund_*.
abstract contract SafePqOwnersBase is SafePqHarness {
    /// `lib/safe-smart-account-<revision>`.
    function _lib() internal pure virtual returns (string memory);
    function _version() internal pure virtual returns (string memory);
    /// Safe main: a non-zero `s` in a pre-validated entry must equal the Safe transaction hash.
    function _bindsPreValidatedHash() internal pure virtual returns (bool);
    /// Safe up to 1.4.1 pays the refund with `send` (2,300 gas); later versions with `call`.
    function _refundsWithSend() internal pure virtual returns (bool);

    address singleton;
    ISafeProxyFactoryLike factory;
    PqOwner[] owners; // five, ascending by account address
    PqOwner outsider; // a valid owner account that owns no Safe
    ISafeLike safe23; // 2-of-3 over owners[0..2]
    ISafeLike safe35; // 3-of-5 over owners[0..4]
    address recipient = makeAddr("recipient");

    bytes32 constant EXECUTION_SUCCESS = keccak256("ExecutionSuccess(bytes32,uint256)");

    function setUp() public {
        _requireLsfk();
        _deployVerifierAndModule();
        singleton = _create(_safeArtifact(string.concat(_lib(), "/contracts/Safe.sol"), "Safe"));
        factory = ISafeProxyFactoryLike(
            _create(_safeArtifact(string.concat(_lib(), "/contracts/proxies/SafeProxyFactory.sol"), "SafeProxyFactory"))
        );
        PqOwner[] memory os = _newOwners("safe-pq owner ", 5);
        for (uint256 i = 0; i < os.length; i++) owners.push(os[i]);
        outsider = _newOwner("safe-pq outsider");

        safe23 = _newSafe(3, 2, 23);
        safe35 = _newSafe(5, 3, 35);
    }

    function _newSafe(uint256 n, uint256 threshold, uint256 salt) internal returns (ISafeLike safe) {
        PqOwner[] memory os = owners;
        safe = ISafeLike(factory.createProxyWithNonce(singleton, _setupData(_ownerAddresses(os, n), threshold), salt));
        vm.deal(address(safe), 10 ether);
    }

    function _transfer(uint256 amount) internal view returns (SafeTx memory t) {
        t.to = recipient;
        t.value = amount;
    }

    function _owner(uint256 i) internal view returns (PqOwner memory) {
        return owners[i];
    }

    function _addr(uint256 i) internal view returns (address) {
        return address(owners[i].account);
    }

    /// `execTransaction` with `msg.sender == tx.origin == executor`, as in a SENDER frame.
    function _exec(ISafeLike safe, SafeTx memory t, bytes memory sigs, address executor) internal returns (bool ok) {
        vm.prank(executor, executor);
        ok = safe.execTransaction(
            t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas, t.gasPrice, t.gasToken, payable(t.refundReceiver), sigs
        );
    }

    function _execReverts(ISafeLike safe, SafeTx memory t, bytes memory sigs, address executor, string memory code) internal {
        uint256 nonce = safe.nonce();
        uint256 balance = address(safe).balance;
        vm.expectRevert(bytes(code));
        vm.prank(executor, executor);
        safe.execTransaction(
            t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas, t.gasPrice, t.gasToken, payable(t.refundReceiver), sigs
        );
        assertEq(safe.nonce(), nonce, "nonce unchanged after a rejected transaction");
        assertEq(address(safe).balance, balance, "balance unchanged after a rejected transaction");
    }

    // ───────────────────────────── the Safe under test ─────────────────────────────

    function test_SafeIsTheUnmodifiedRelease() public view {
        assertEq(safe23.VERSION(), _version());
        assertEq(safe23.getThreshold(), 2);
        assertEq(safe35.getThreshold(), 3);
        address[] memory o3 = safe23.getOwners();
        address[] memory o5 = safe35.getOwners();
        assertEq(o3.length, 3);
        assertEq(o5.length, 5);
        for (uint256 i = 0; i < 5; i++) {
            assertTrue(safe35.isOwner(_addr(i)));
            assertEq(safe23.isOwner(_addr(i)), i < 3);
            assertGt(_addr(i).code.length, 0, "owners are contracts");
            if (i > 0) assertGt(uint160(_addr(i)), uint160(_addr(i - 1)), "test owners are sorted");
        }
        assertEq(DOMAIN_SEPARATOR_TYPEHASH, keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"));
        assertEq(
            SAFE_TX_TYPEHASH,
            keccak256(
                "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)"
            )
        );
        assertEq(safe23.domainSeparator(), keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH, block.chainid, address(safe23))));
    }

    // ───────────────────────────── happy paths ─────────────────────────────

    /// 2-of-3: every owner as the sender, with each other owner as the co-signer.
    function test_TwoOfThree_SenderPlusOneCoSigner() public {
        uint256 paid;
        for (uint256 s = 0; s < 3; s++) {
            for (uint256 c = 0; c < 3; c++) {
                if (c == s) continue;
                SafeTx memory t = _transfer(1 + 3 * s + c);
                uint256 nonce = safe23.nonce();
                bytes32 h = _getTransactionHash(safe23, t, nonce);
                assertEq(h, _safeTxHash(address(safe23), t, nonce), "Safe transaction hash");

                bytes memory sigs = _blob(_sorted(_entries(_preValidated(_addr(s), h), _cosign(_owner(c), h))));
                assertEq(sigs.length, 2 * 65 + 32 + SIG_LEN, "signatures size");
                assertTrue(_exec(safe23, t, sigs, _addr(s)), "execTransaction");
                assertEq(safe23.nonce(), nonce + 1);
                paid += t.value;
                assertEq(recipient.balance, paid);
            }
        }
    }

    /// 3-of-5: the sender plus two co-signers, with the sender lowest, highest and in between.
    function test_ThreeOfFive_SenderPlusTwoCoSigners() public {
        uint8[3][5] memory combos = [[0, 1, 2], [4, 0, 2], [2, 1, 3], [1, 3, 4], [3, 0, 4]];
        uint256 paid;
        for (uint256 k = 0; k < combos.length; k++) {
            SafeTx memory t = _transfer(100 + k);
            uint256 nonce = safe35.nonce();
            bytes32 h = _getTransactionHash(safe35, t, nonce);
            assertEq(h, _safeTxHash(address(safe35), t, nonce), "Safe transaction hash");
            bytes memory sigs = _blob(
                _sorted(
                    _entries(_preValidated(_addr(combos[k][0]), h), _cosign(_owner(combos[k][1]), h), _cosign(_owner(combos[k][2]), h))
                )
            );
            assertEq(sigs.length, 3 * 65 + 2 * (32 + SIG_LEN), "signatures size");
            assertTrue(_exec(safe35, t, sigs, _addr(combos[k][0])), "execTransaction");
            assertEq(safe35.nonce(), nonce + 1);
            paid += t.value;
            assertEq(recipient.balance, paid);
        }
    }

    /// A threshold-1 Safe: the sender alone, with no co-signature at all.
    function test_OneOfThree_SenderAlone() public {
        ISafeLike safe13 = _newSafe(3, 1, 13);
        SafeTx memory t = _transfer(5);
        bytes32 h = _getTransactionHash(safe13, t, 0);
        Entry[] memory es = new Entry[](1);
        es[0] = _preValidated(_addr(1), h);
        assertTrue(_exec(safe13, t, _blob(es), _addr(1)));
        assertEq(recipient.balance, 5);
    }

    /// Without EIP-8141: any account can execute when every signer is a contract signature.
    function test_AllContractSignatures_ExecutedByARelayer() public {
        SafeTx memory t = _transfer(9);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes memory sigs = _blob(_entries(_cosign(_owner(0), h), _cosign(_owner(2), h)));
        assertTrue(_exec(safe23, t, sigs, makeAddr("relayer")));
        assertEq(recipient.balance, 9);
    }

    /// A Safe call with data, not only a transfer: the Safe adds an owner account to itself.
    function test_SafeCallWithData() public {
        SafeTx memory t;
        t.to = address(safe23);
        t.data = abi.encodeWithSignature("addOwnerWithThreshold(address,uint256)", address(outsider.account), uint256(2));
        bytes32 h = _getTransactionHash(safe23, t, 0);
        assertEq(h, _safeTxHash(address(safe23), t, 0));
        assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(1), h))), _addr(0)));
        assertTrue(safe23.isOwner(address(outsider.account)), "owner added by a PQ-signed Safe transaction");
    }

    // ───────────────────────────── rejected signatures ─────────────────────────────

    function test_BadCoSignature_GS024() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        Entry memory good = _cosign(_owner(1), h);

        bytes memory tampered = bytes.concat(good.sig);
        tampered[2000] = bytes1(uint8(tampered[2000]) ^ 0x01);
        _execReverts(safe23, t, _blob(_entries(_preValidated(_addr(0), h), _contractSig(_addr(1), tampered))), _addr(0), "GS024");

        // Wrong length: the verifier reverts, the owner account answers 0xffffffff.
        bytes memory short_ = new bytes(SIG_LEN - 1);
        for (uint256 i = 0; i < short_.length; i++) short_[i] = good.sig[i];
        _execReverts(safe23, t, _blob(_entries(_preValidated(_addr(0), h), _contractSig(_addr(1), short_))), _addr(0), "GS024");
        _execReverts(safe23, t, _blob(_entries(_preValidated(_addr(0), h), _contractSig(_addr(1), ""))), _addr(0), "GS024");

        // Owner 2's valid signature presented as owner 1's.
        Entry memory other = _cosign(_owner(2), h);
        _execReverts(safe23, t, _blob(_entries(_preValidated(_addr(0), h), _contractSig(_addr(1), other.sig))), _addr(0), "GS024");

        // A valid signature over another transaction.
        Entry memory otherTx = _cosign(_owner(1), _getTransactionHash(safe23, _transfer(2), 0));
        _execReverts(safe23, t, _blob(_entries(_preValidated(_addr(0), h), otherTx)), _addr(0), "GS024");

        // Control.
        assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), good)), _addr(0)));
    }

    function test_CoSignerNotAnOwner_GS026() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        // A valid signature by an owner account that does not own this Safe, as co-signer...
        bytes memory sigs = _blob(_sorted(_entries(_preValidated(_addr(0), h), _cosign(outsider, h))));
        _execReverts(safe23, t, sigs, _addr(0), "GS026");
        // ...and as the sender.
        sigs = _blob(_sorted(_entries(_preValidated(address(outsider.account), h), _cosign(_owner(0), h))));
        _execReverts(safe23, t, sigs, address(outsider.account), "GS026");
        // owners[3] owns the 3-of-5 Safe, not this one.
        sigs = _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(3), h)));
        _execReverts(safe23, t, sigs, _addr(0), "GS026");
    }

    function test_DuplicateOwner_GS026() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe35, t, 0);
        Entry memory c = _cosign(_owner(2), h);

        // 3-of-5 with one co-signer counted twice.
        _execReverts(safe35, t, _blob(_sorted(_entries(_preValidated(_addr(0), h), c, c))), _addr(0), "GS026");
        _execReverts(safe35, t, _blob(_sorted(_entries(_preValidated(_addr(4), h), c, c))), _addr(4), "GS026");
        // The sender counted twice, once pre-validated and once as a contract signature.
        _execReverts(safe35, t, _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(0), h), c)), _addr(0), "GS026");

        // 2-of-3 with the sender twice.
        bytes32 h2 = _getTransactionHash(safe23, t, 0);
        _execReverts(safe23, t, _blob(_entries(_preValidated(_addr(1), h2), _preValidated(_addr(1), h2))), _addr(1), "GS026");

        // Valid, distinct signers in descending order are rejected the same way.
        _execReverts(safe23, t, _blob(_entries(_cosign(_owner(2), h2), _preValidated(_addr(1), h2))), _addr(1), "GS026");
    }

    // ───────────────────────────── invariant 6: co-signature binding ─────────────────────────────

    /// A co-signature is over one Safe nonce. The sender's entry carries `s = 0` here, so the
    /// rejection comes from the co-signature alone, on every Safe version.
    function test_CoSignature_BoundToNonce() public {
        SafeTx memory a = _transfer(1);
        SafeTx memory b = _transfer(2);
        bytes32 hA0 = _getTransactionHash(safe23, a, 0);
        bytes32 hA1 = _getTransactionHash(safe23, a, 1);
        bytes memory sigsA0 = _blob(_entries(_preValidated(_addr(0), 0), _cosign(_owner(1), hA0)));
        bytes memory sigsA1 = _blob(_entries(_preValidated(_addr(0), 0), _cosign(_owner(1), hA1)));

        // A co-signature for the next nonce does not work at this one.
        _execReverts(safe23, a, sigsA1, _addr(0), "GS024");

        // The Safe nonce moves (another transaction executes first): the co-signature for
        // nonce 0 is dead.
        bytes32 hB0 = _getTransactionHash(safe23, b, 0);
        assertTrue(_exec(safe23, b, _blob(_entries(_preValidated(_addr(0), hB0), _cosign(_owner(2), hB0))), _addr(0)));
        assertEq(safe23.nonce(), 1);
        _execReverts(safe23, a, sigsA0, _addr(0), "GS024");

        // The one for nonce 1 works now, once.
        assertTrue(_exec(safe23, a, sigsA1, _addr(0)));
        assertEq(safe23.nonce(), 2);
        _execReverts(safe23, a, sigsA1, _addr(0), "GS024");
        assertEq(recipient.balance, 3);
    }

    /// A co-signature is over one Safe: the same owners, threshold, transaction and nonce in
    /// another Safe give another hash.
    function test_CoSignature_BoundToSafe() public {
        ISafeLike twin = _newSafe(3, 2, 2323);
        assertTrue(address(twin) != address(safe23));
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes32 hTwin = _getTransactionHash(twin, t, 0);
        assertTrue(h != hTwin);

        bytes memory sigs = _blob(_entries(_preValidated(_addr(0), 0), _cosign(_owner(1), h)));
        _execReverts(twin, t, sigs, _addr(0), "GS024");
        assertTrue(_exec(safe23, t, sigs, _addr(0)), "control: the Safe it was signed for");
        assertTrue(_exec(twin, t, _blob(_entries(_preValidated(_addr(0), 0), _cosign(_owner(1), hTwin))), _addr(0)));
    }

    /// A co-signature is over one chain id (the Safe's EIP-712 domain separator).
    function test_CoSignature_BoundToChain() public {
        // Literal chain ids: under via-IR a `block.chainid` read into a local is re-evaluated
        // after vm.chainId, so it cannot hold the "home" chain.
        SafeTx memory t = _transfer(1);
        vm.chainId(8141);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes memory sigs = _blob(_entries(_preValidated(_addr(0), 0), _cosign(_owner(1), h)));

        vm.chainId(1);
        assertTrue(_getTransactionHash(safe23, t, 0) != h);
        _execReverts(safe23, t, sigs, _addr(0), "GS024");

        vm.chainId(8141);
        assertTrue(_exec(safe23, t, sigs, _addr(0)), "control: the chain it was signed for");
    }

    // ───────────────────────────── the sender's pre-validated entry ─────────────────────────────

    /// v = 1 counts only for `msg.sender` (no hash was approved on chain).
    function test_PreValidated_OnlyForTheSender_GS025() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes memory sigs = _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(1), h)));
        _execReverts(safe23, t, sigs, makeAddr("relayer"), "GS025");
        _execReverts(safe23, t, sigs, _addr(1), "GS025");
        _execReverts(safe23, t, sigs, _addr(2), "GS025");
        assertTrue(_exec(safe23, t, sigs, _addr(0)));
    }

    /// The tooling sets `s` to the Safe transaction hash. Safe main rejects any other non-zero
    /// `s`; Safe up to 1.5.0 does not read it.
    function test_PreValidated_HashBinding() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        Entry memory c = _cosign(_owner(1), h);

        bytes memory wrong = _blob(_entries(_preValidated(_addr(0), h ^ bytes32(uint256(1))), c));
        if (_bindsPreValidatedHash()) {
            _execReverts(safe23, t, wrong, _addr(0), "GS025");
            assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), c)), _addr(0)), "s = hash");
        } else {
            assertTrue(_exec(safe23, t, wrong, _addr(0)), "s is not read before Safe main");
        }
    }

    // ───────────────────────────── refund ─────────────────────────────

    /// With `gasPrice > 0` and no refund receiver, the Safe pays `tx.origin`. In a SENDER
    /// frame ORIGIN is the frame's caller, the sender's owner account, which is also the
    /// account that paid for the frame transaction. Safe up to 1.4.1 pays with `send`, so the
    /// owner account's receive() has 2,300 gas.
    function test_Refund_GoesToTheSendersOwnerAccount() public {
        SafeTx memory t = _transfer(1);
        t.safeTxGas = 50_000;
        t.baseGas = 100_000;
        t.gasPrice = 1 gwei;
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes memory sigs = _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(1), h)));

        vm.txGasPrice(3 gwei);
        uint256 senderBefore = _addr(0).balance;
        uint256 safeBefore = address(safe23).balance;
        vm.recordLogs();
        assertTrue(_exec(safe23, t, sigs, _addr(0)));

        uint256 payment = _paymentFromLogs(h);
        assertGt(payment, t.baseGas * t.gasPrice, "payment covers baseGas plus the gas used");
        assertEq(payment % t.gasPrice, 0, "priced at min(gasPrice, tx.gasprice)");
        assertEq(_addr(0).balance - senderBefore, payment, "refund paid to the sender's owner account");
        assertEq(safeBefore - address(safe23).balance, payment + t.value);
        emit log_named_uint("refund to the sender's owner account (wei)", payment);
    }

    /// Pins how each version pays: a receiver that needs more than 2,300 gas fails under
    /// `send` (GS011) and is paid under `call`.
    function test_Refund_SendOrCall() public {
        address hungry = address(new HungryReceiver());
        SafeTx memory t = _transfer(1);
        t.safeTxGas = 50_000;
        t.baseGas = 100_000;
        t.gasPrice = 1 gwei;
        t.refundReceiver = hungry;
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes memory sigs = _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(1), h)));
        vm.txGasPrice(3 gwei);
        if (_refundsWithSend()) {
            _execReverts(safe23, t, sigs, _addr(0), "GS011");
        } else {
            assertTrue(_exec(safe23, t, sigs, _addr(0)));
            assertGt(hungry.balance, 0);
        }
    }

    function _paymentFromLogs(bytes32 safeTxHash) internal returns (uint256 payment) {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        bool found;
        for (uint256 i = 0; i < logs.length; i++) {
            if (logs[i].topics[0] != EXECUTION_SUCCESS) continue;
            // `txHash` became indexed in Safe 1.4.0.
            assertEq(logs[i].topics.length, 2);
            assertEq(logs[i].topics[1], safeTxHash, "ExecutionSuccess for this transaction");
            payment = abi.decode(logs[i].data, (uint256));
            found = true;
        }
        assertTrue(found, "ExecutionSuccess emitted");
    }

    // ───────────────────────────── gas ─────────────────────────────

    /// Gas of `execTransaction`'s own call frame (revm, today's schedule), for a 1 wei transfer
    /// to an existing account, everything cold at the start of the transaction. The difference
    /// between rows is one more co-signer: one `isValidSignature` call plus the Safe's
    /// handling of 4,757 more bytes of signatures.
    function test_Gas_ExecTransaction() public {
        vm.deal(recipient, 1);
        ISafeLike safe13 = _newSafe(3, 1, 13);
        SafeTx memory t = _transfer(1);

        bytes32 h = _getTransactionHash(safe13, t, 0);
        Entry[] memory one = new Entry[](1);
        one[0] = _preValidated(_addr(0), h);
        assertTrue(_exec(safe13, t, _blob(one), _addr(0)));
        uint256 g1 = vm.lastCallGas().gasTotalUsed;

        h = _getTransactionHash(safe23, t, 0);
        assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(1), h))), _addr(0)));
        uint256 g2 = vm.lastCallGas().gasTotalUsed;

        h = _getTransactionHash(safe35, t, 0);
        bytes memory sigs = _blob(_entries(_preValidated(_addr(0), h), _cosign(_owner(1), h), _cosign(_owner(2), h)));
        assertTrue(_exec(safe35, t, sigs, _addr(0)));
        uint256 g3 = vm.lastCallGas().gasTotalUsed;

        emit log_named_uint(string.concat("Safe ", _version(), " execTransaction gas, sender alone (1-of-3)"), g1);
        emit log_named_uint(string.concat("Safe ", _version(), " execTransaction gas, sender + 1 co-signer (2-of-3)"), g2);
        emit log_named_uint(string.concat("Safe ", _version(), " execTransaction gas, sender + 2 co-signers (3-of-5)"), g3);
        emit log_named_uint("  first co-signer (verifier cold)", g2 - g1);
        emit log_named_uint("  second co-signer (verifier warm)", g3 - g2);
        // Measured (forge 1.5.1; Safe built with solc 0.7.6, optimizer off, as upstream):
        //   1.4.1  37,431 / 110,577 / 172,070      1.5.0  36,971 / 109,117 / 169,696
        //   main   36,911 / 123,402 / 198,263
        // A co-signer is one isValidSignature call (about 45.7 K warm, plus 2,600 for the cold
        // owner account and 2,500 for a cold verifier) and the Safe's own copying of the
        // signature bytes in memory.
        assertLt(g2 - g1, 95_000, "first co-signer");
        assertLt(g3 - g2, 85_000, "second co-signer");
    }
}

/// @dev A refund receiver whose receive() needs more than the 2,300-gas stipend.
contract HungryReceiver {
    uint256 public received;

    receive() external payable {
        received += msg.value;
    }
}

contract SafePqOwners141Test is SafePqOwnersBase {
    function _lib() internal pure override returns (string memory) {
        return "lib/safe-smart-account-1.4.1";
    }

    function _version() internal pure override returns (string memory) {
        return "1.4.1";
    }

    function _bindsPreValidatedHash() internal pure override returns (bool) {
        return false;
    }

    function _refundsWithSend() internal pure override returns (bool) {
        return true;
    }

    /// Safe 1.4.1 hands the co-signer the EIP-712 pre-image, not the hash: the owner account
    /// answers the `(bytes, bytes)` form with 0x20c13b0b over keccak256(data).
    function test_LegacyForm_IsWhatThisSafeCalls() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        bytes memory preimage = _safeTxPreimage(address(safe23), t, 0);
        assertEq(preimage.length, 66);
        assertEq(keccak256(preimage), h);
        Entry memory c = _cosign(_owner(1), h);

        vm.expectCall(_addr(1), abi.encodeWithSelector(bytes4(0x20c13b0b), preimage, c.sig));
        assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), c)), _addr(0)));
    }
}

contract SafePqOwners150Test is SafePqOwnersBase {
    function _lib() internal pure override returns (string memory) {
        return "lib/safe-smart-account-1.5.0";
    }

    function _version() internal pure override returns (string memory) {
        return "1.5.0";
    }

    function _bindsPreValidatedHash() internal pure override returns (bool) {
        return false;
    }

    function _refundsWithSend() internal pure override returns (bool) {
        return false;
    }

    /// Safe 1.5.0 calls ERC-1271 `isValidSignature(bytes32, bytes)` with the Safe transaction hash.
    function test_HashForm_IsWhatThisSafeCalls() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        Entry memory c = _cosign(_owner(1), h);
        vm.expectCall(_addr(1), abi.encodeWithSelector(bytes4(0x1626ba7e), h, c.sig));
        assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), c)), _addr(0)));
    }
}

/// Safe main at 247b8ce3bdbf (2026-11, still reporting VERSION 1.5.0).
contract SafePqOwnersMainTest is SafePqOwnersBase {
    function _lib() internal pure override returns (string memory) {
        return "lib/safe-smart-account-main";
    }

    function _version() internal pure override returns (string memory) {
        return "1.5.0";
    }

    function _bindsPreValidatedHash() internal pure override returns (bool) {
        return true;
    }

    function _refundsWithSend() internal pure override returns (bool) {
        return false;
    }

    function test_HashForm_IsWhatThisSafeCalls() public {
        SafeTx memory t = _transfer(1);
        bytes32 h = _getTransactionHash(safe23, t, 0);
        Entry memory c = _cosign(_owner(1), h);
        vm.expectCall(_addr(1), abi.encodeWithSelector(bytes4(0x1626ba7e), h, c.sig));
        assertTrue(_exec(safe23, t, _blob(_entries(_preValidated(_addr(0), h), c)), _addr(0)));
    }

    /// On main the sender's entry pins the Safe nonce by itself: with `s` set to the hash the
    /// sender signed for, a moved nonce is rejected at the sender's entry (GS025) before any
    /// co-signature is looked at.
    function test_PreValidated_PinsTheNonceOnMain() public {
        SafeTx memory a = _transfer(1);
        SafeTx memory b = _transfer(2);
        bytes32 hA0 = _getTransactionHash(safe23, a, 0);
        bytes memory sigsA0 = _blob(_entries(_preValidated(_addr(0), hA0), _cosign(_owner(1), hA0)));
        bytes32 hB0 = _getTransactionHash(safe23, b, 0);
        assertTrue(_exec(safe23, b, _blob(_entries(_preValidated(_addr(0), hB0), _cosign(_owner(2), hB0))), _addr(0)));
        _execReverts(safe23, a, sigsA0, _addr(0), "GS025");
    }
}
