// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/LeanSphincs-23Asm.sol";
import "../src/SphincsAccount.sol";
import "../src/SphincsAccountFactory.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";
import "account-abstraction/core/Helpers.sol";

/// @notice Integration test: SphincsAccountFactory + SphincsAccount wired to the leanSphincs-23
///         keccak256 verifier. The account is verifier-agnostic: it staticcalls
///         `verify(bytes32,bytes32,bytes32,bytes)` with its stored high-aligned key words and has
///         no signature-size assumptions, so leanSphincs-23 (4148-B signature, same interface as
///         the C-series) plugs in unchanged. LeanSphincs23Test covers the verifier itself; this
///         drives the real `validateUserOp` path (pranked as the EntryPoint), hybrid signature
///         `abi.encode(ecdsaSig, sphincsSig)` included.
contract SphincsAccountLeanSphincs23Test is Test {
    LeanSphincs23Asm verifier;
    SphincsAccountFactory factory;

    // Canonical EntryPoint v0.9 address. Not deployed: validateUserOp only checks msg.sender, and
    // userOpHash is an input to it, so the test pranks as the EntryPoint and supplies the hash.
    address constant ENTRYPOINT_V09 = 0x433709009B8330FDa32311DF1C2AFA402eD8D009;

    string constant FIXTURE = "test/fixtures/leansphincs23-keccak-kat.json";
    string constant LS23K = "signers/leansphincs23-keccak/target/release/ls23k";
    // Prints `fresh`, `missing`, or `stale` when a crate source (Cargo.toml, Cargo.lock, src/**.rs,
    // as crosscheck.py's ensure_binary) is newer than the binary. Same probe as LeanSphincs23Test.
    string constant LS23K_PROBE = "d=signers/leansphincs23-keccak; b=$d/target/release/ls23k; "
        "if [ ! -x $b ]; then echo missing; "
        "elif [ -n \"$(find $d/Cargo.toml $d/Cargo.lock $d/src -newer $b \\( -name '*.rs' -o -name 'Cargo.*' \\) "
        "2>/dev/null | head -n 1)\" ]; then echo stale; else echo fresh; fi";

    uint256 ownerKey;
    address ecdsaOwner;

    function setUp() public {
        verifier = new LeanSphincs23Asm();
        factory = new SphincsAccountFactory(IEntryPoint(ENTRYPOINT_V09), address(verifier));
        (ecdsaOwner, ownerKey) = makeAddrAndKey("leanSphincs-23 ecdsa owner");
    }

    /// Fixture vector `i`: (pkSeed, pkRoot, message, sig).
    function _vector(uint256 i)
        internal
        view
        returns (bytes32 pkSeed, bytes32 pkRoot, bytes32 message, bytes memory sig)
    {
        string memory json = vm.readFile(FIXTURE);
        string memory v = string.concat(".vectors[", vm.toString(i), "].");
        pkSeed = vm.parseJsonBytes32(json, string.concat(v, "pkSeed"));
        pkRoot = vm.parseJsonBytes32(json, string.concat(v, "pkRoot"));
        message = vm.parseJsonBytes32(json, string.concat(v, "message"));
        sig = vm.parseJsonBytes(json, string.concat(v, "sig"));
    }

    function _count() internal view returns (uint256 n) {
        string memory json = vm.readFile(FIXTURE);
        while (vm.keyExistsJson(json, string.concat(".vectors[", vm.toString(n), "]"))) n++;
    }

    function _userOp(address sender, bytes memory signature) internal pure returns (PackedUserOperation memory op) {
        op.sender = sender;
        op.signature = signature;
    }

    /// The hybrid signature the account decodes: abi.encode(ecdsaSig, sphincsSig), with the ECDSA
    /// half a real signature by the account owner over `userOpHash`.
    function _hybrid(bytes32 userOpHash, bytes memory sphincsSig) internal view returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerKey, userOpHash);
        return abi.encode(abi.encodePacked(r, s, v), sphincsSig);
    }

    function _validate(SphincsAccount account, bytes32 userOpHash, bytes memory sphincsSig) internal returns (uint256) {
        PackedUserOperation memory op = _userOp(address(account), _hybrid(userOpHash, sphincsSig));
        vm.prank(ENTRYPOINT_V09);
        return account.validateUserOp(op, userOpHash, 0);
    }

    function testFactoryWiresLeanSphincs23Verifier() public {
        (bytes32 pkSeed, bytes32 pkRoot,,) = _vector(0);
        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);
        assertEq(address(account.verifier()), address(verifier), "verifier wired");
        assertEq(account.pkSeed(), pkSeed, "pkSeed stored");
        assertEq(account.pkRoot(), pkRoot, "pkRoot stored");
        assertEq(factory.getAddress(ecdsaOwner, pkSeed, pkRoot), address(account), "CREATE2 prediction");
    }

    /// Every fixture vector, its message used as the userOpHash, passes validateUserOp on an account
    /// holding that vector's key. (The first call's gas includes the cold access to the verifier.)
    function testValidateUserOpAcceptsLeanSphincs23Signature() public {
        uint256 n = _count();
        assertGe(n, 4, "fixture vectors");
        for (uint256 i = 0; i < n; i++) {
            (bytes32 pkSeed, bytes32 pkRoot, bytes32 userOpHash, bytes memory sig) = _vector(i);
            SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

            PackedUserOperation memory op = _userOp(address(account), _hybrid(userOpHash, sig));
            vm.prank(ENTRYPOINT_V09);
            uint256 g = gasleft();
            uint256 validationData = account.validateUserOp(op, userOpHash, 0);
            uint256 used = g - gasleft();
            assertEq(validationData, SIG_VALIDATION_SUCCESS, "leanSphincs-23 userOp must validate");
            emit log_named_uint("validateUserOp gas (ECDSA + leanSphincs-23)", used);
        }
    }

    /// With a valid ECDSA half, a bad leanSphincs-23 half fails validation without reverting:
    /// a tampered byte or another userOpHash (verify returns false), and a wrong-length signature
    /// (verify reverts; the account turns the failed staticcall into SIG_VALIDATION_FAILED).
    function testValidateUserOpRejectsBadLeanSphincs23Signature() public {
        (bytes32 pkSeed, bytes32 pkRoot, bytes32 userOpHash, bytes memory sig) = _vector(0);
        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

        bytes memory tampered = bytes.concat(sig);
        tampered[3000] = bytes1(uint8(tampered[3000]) ^ 0x01);
        assertEq(_validate(account, userOpHash, tampered), SIG_VALIDATION_FAILED, "tampered sig");

        assertEq(_validate(account, userOpHash ^ bytes32(uint256(1)), sig), SIG_VALIDATION_FAILED, "other userOpHash");

        bytes memory truncated = new bytes(sig.length - 1);
        for (uint256 j = 0; j < truncated.length; j++) {
            truncated[j] = sig[j];
        }
        assertEq(_validate(account, userOpHash, truncated), SIG_VALIDATION_FAILED, "wrong-length sig");

        // Control: the untouched signature still validates on the same account.
        assertEq(_validate(account, userOpHash, sig), SIG_VALIDATION_SUCCESS, "control");
    }

    /// End to end with a fresh key from the Rust CLI: the userOpHash commits to the deployed
    /// account address and chain id (a stand-in for EntryPoint.getUserOpHash), so it can only be
    /// signed after the account exists. Build the binary with:
    ///     (cd signers/leansphincs23-keccak && cargo build --release)
    function testValidateUserOpFFI_Rust() public {
        _requireLs23k();

        bytes32 seed = keccak256("leanSphincs-23-keccak account FFI seed");
        // Keygen is deterministic: any first signature yields the key words.
        (bytes32 pkSeed, bytes32 pkRoot,) = _sign(seed, bytes32(0));
        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

        bytes32 userOpHash = keccak256(abi.encode(address(account), uint256(0), ENTRYPOINT_V09, block.chainid));
        (bytes32 seed2, bytes32 root2, bytes memory sig) = _sign(seed, userOpHash);
        assertEq(seed2, pkSeed, "same key: pkSeed");
        assertEq(root2, pkRoot, "same key: pkRoot");

        assertEq(_validate(account, userOpHash, sig), SIG_VALIDATION_SUCCESS, "fresh leanSphincs-23 userOp");
    }

    /// The Rust CLI must be built and not older than any crate source (a stale binary signs under
    /// the old scheme with no error: the repo's stale-binary rule, f5c09ae), or the test fails. A
    /// missing binary skips it (reported as skipped), except under CI, where the solidity job
    /// builds it.
    function _requireLs23k() internal {
        string[] memory probe = new string[](3);
        probe[0] = "sh";
        probe[1] = "-c";
        probe[2] = LS23K_PROBE;
        bytes memory state = vm.ffi(probe);
        string memory build = " (cd signers/leansphincs23-keccak && cargo build --release)";
        if (keccak256(state) == keccak256("missing")) {
            assertEq(vm.envOr("CI", string("")), "", string.concat(LS23K, " is not built under CI:", build));
            vm.skip(true, string.concat(LS23K, " not built:", build));
        }
        assertEq(string(state), "fresh", string.concat(LS23K, " is older than the crate sources:", build));
    }

    function _sign(bytes32 seed, bytes32 message) internal returns (bytes32, bytes32, bytes memory) {
        string[] memory inputs = new string[](5);
        inputs[0] = LS23K;
        inputs[1] = "sign";
        inputs[2] = vm.toString(seed);
        inputs[3] = "8";
        inputs[4] = vm.toString(message);
        return abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }
}
