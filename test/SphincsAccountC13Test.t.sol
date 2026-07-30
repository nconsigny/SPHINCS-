// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C13Asm.sol";
import "../src/SphincsAccount.sol";
import "../src/SphincsAccountFactory.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";

/// @notice Integration test: SphincsAccountFactory + SphincsAccount with the C13 verifier.
///         The account contract is variant-agnostic (it staticcalls verifier.verify),
///         so we exercise the wiring rather than re-testing C13's algebra
///         (which SphincsC13Test already covers).
contract SphincsAccountC13Test is Test {
    SphincsC13Asm verifier;
    SphincsAccountFactory factory;

    // Use the canonical EntryPoint v0.9 address; we don't need it deployed because
    // we never call entryPoint.handleOps in this test — we only assert wiring.
    address constant ENTRYPOINT_V09 = 0x433709009B8330FDa32311DF1C2AFA402eD8D009;

    address ecdsaOwner;

    function setUp() public {
        verifier = new SphincsC13Asm();
        factory = new SphincsAccountFactory(IEntryPoint(ENTRYPOINT_V09), address(verifier));
        ecdsaOwner = address(0xCAFE);
    }

    function testFactoryWiresVerifierAndKeys() public {
        bytes32 pkSeed = 0x012dd57311a3728fd6988fb2a583bb9e00000000000000000000000000000000;
        bytes32 pkRoot = 0xd937b687fe8c5a0d329b30a2cb88705b00000000000000000000000000000000;

        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

        assertEq(address(account.verifier()), address(verifier), "verifier wired");
        assertEq(account.pkSeed(), pkSeed, "pkSeed stored");
        assertEq(account.pkRoot(), pkRoot, "pkRoot stored");
        assertEq(account.owner(), ecdsaOwner, "ecdsa owner stored");

        // CREATE2 prediction matches
        address predicted = factory.getAddress(ecdsaOwner, pkSeed, pkRoot);
        assertEq(predicted, address(account), "CREATE2 prediction matches deployment");
    }

    /// @notice End-to-end: real C13 sig from the Python signer must verify
    ///         when the account staticcalls the wired verifier.
    function testAccountAcceptsRealC13SignatureFFI() public {
        bytes32 message = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef;

        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = "script/signer.py";
        inputs[2] = "c13";
        inputs[3] = "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        bytes memory result = vm.ffi(inputs);
        (bytes32 pkSeed, bytes32 pkRoot, bytes memory sig) = abi.decode(result, (bytes32, bytes32, bytes));

        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

        // Reproduce the verify call the way SphincsAccount._validateSignature does it
        (bool success, bytes memory raw) = account.verifier().staticcall(
            abi.encodeWithSignature(
                "verify(bytes32,bytes32,bytes32,bytes)",
                account.pkSeed(),
                account.pkRoot(),
                message,
                sig
            )
        );
        assertTrue(success, "staticcall to verifier failed");
        assertEq(raw.length, 32, "verifier returned wrong size");
        assertTrue(abi.decode(raw, (bool)), "C13 signature should verify through account.verifier()");
    }
}
