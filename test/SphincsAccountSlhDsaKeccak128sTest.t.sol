// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Sagar Rana

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SLH-DSA-Keccak-128sAsm.sol";
import "../src/SphincsAccount.sol";
import "../src/SphincsAccountFactory.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";
import "account-abstraction/core/Helpers.sol";

/// @notice Integration test: SphincsAccountFactory + SphincsAccount wired to the SLH-DSA-Keccak-128s verifier.
///         The account is verifier-agnostic: it staticcalls `verify(bytes32,bytes32,bytes32,bytes)` with its
///         stored high-aligned key words and has no signature-size assumptions, so the 7,872-byte signature
///         plugs in unchanged. SlhDsaKeccak128sTest covers the verifier itself; this drives the real
///         `validateUserOp` path (pranked as the EntryPoint), hybrid signature `abi.encode(ecdsaSig, sphincsSig)`
///         included.
contract SphincsAccountSlhDsaKeccak128sTest is Test {
    SLH_DSA_Keccak_128sAsm verifier;
    SphincsAccountFactory factory;

    // Canonical EntryPoint v0.9 address. Not deployed: validateUserOp only checks msg.sender, and
    // userOpHash is an input to it, so the test pranks as the EntryPoint and supplies the hash.
    address constant ENTRYPOINT_V09 = 0x433709009B8330FDa32311DF1C2AFA402eD8D009;

    string constant FIXTURE = "test/fixtures/slh-dsa-keccak-128s-kat.json";
    string constant SIGNER = "script/slh_dsa_keccak_128s_signer.py";

    uint256 ownerKey;
    address ecdsaOwner;

    function setUp() public {
        verifier = new SLH_DSA_Keccak_128sAsm();
        factory = new SphincsAccountFactory(IEntryPoint(ENTRYPOINT_V09), address(verifier));
        (ecdsaOwner, ownerKey) = makeAddrAndKey("SLH-DSA-Keccak-128s ecdsa owner");
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

    /// The hybrid signature the account decodes: abi.encode(ecdsaSig, sphincsSig), with the ECDSA half a
    /// real signature by the account owner over `userOpHash`.
    function _hybrid(bytes32 userOpHash, bytes memory sphincsSig) internal view returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerKey, userOpHash);
        return abi.encode(abi.encodePacked(r, s, v), sphincsSig);
    }

    function _validate(SphincsAccount account, bytes32 userOpHash, bytes memory sphincsSig) internal returns (uint256) {
        PackedUserOperation memory op = _userOp(address(account), _hybrid(userOpHash, sphincsSig));
        vm.prank(ENTRYPOINT_V09);
        return account.validateUserOp(op, userOpHash, 0);
    }

    function _sign(bytes32 masterSk, bytes32 message) internal returns (bytes32 seed, bytes32 root, bytes memory sig) {
        string[] memory inputs = new string[](4);
        inputs[0] = "python3";
        inputs[1] = SIGNER;
        inputs[2] = vm.toString(masterSk);
        inputs[3] = vm.toString(message);
        (seed, root, sig) = abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }

    function testFactoryWires128sVerifier() public {
        (bytes32 pkSeed, bytes32 pkRoot,,) = _vector(0);
        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);
        assertEq(address(account.verifier()), address(verifier), "verifier wired");
        assertEq(account.pkSeed(), pkSeed, "pkSeed stored");
        assertEq(account.pkRoot(), pkRoot, "pkRoot stored");
        assertEq(factory.getAddress(ecdsaOwner, pkSeed, pkRoot), address(account), "CREATE2 prediction");
    }

    /// Every fixture vector, its message used as the userOpHash, passes validateUserOp on an account
    /// holding that vector's key. (The first call's gas includes the cold access to the verifier.)
    function testValidateUserOpAccepts128sSignature() public {
        uint256 n = _count();
        assertGe(n, 4, "fixture vectors");
        for (uint256 i = 0; i < n; i++) {
            (bytes32 pkSeed, bytes32 pkRoot, bytes32 userOpHash, bytes memory sig) = _vector(i);
            SphincsAccount account = factory.getAddress(ecdsaOwner, pkSeed, pkRoot).code.length == 0
                ? factory.createAccount(ecdsaOwner, pkSeed, pkRoot)
                : SphincsAccount(payable(factory.getAddress(ecdsaOwner, pkSeed, pkRoot)));

            PackedUserOperation memory op = _userOp(address(account), _hybrid(userOpHash, sig));
            vm.prank(ENTRYPOINT_V09);
            uint256 g = gasleft();
            uint256 validationData = account.validateUserOp(op, userOpHash, 0);
            uint256 used = g - gasleft();
            assertEq(validationData, SIG_VALIDATION_SUCCESS, "128s userOp must validate");
            emit log_named_uint("validateUserOp gas (ECDSA + SLH-DSA-Keccak-128s)", used);
        }
    }

    /// With a valid ECDSA half, a bad SPHINCS+ half fails validation without reverting: a tampered byte in
    /// R, FORS, the bottom and the top hypertree layer, or another userOpHash (verify returns false), and a
    /// wrong-length signature (verify reverts; the account turns the failed staticcall into
    /// SIG_VALIDATION_FAILED).
    function testValidateUserOpRejectsBad128sSignature() public {
        (bytes32 pkSeed, bytes32 pkRoot, bytes32 userOpHash, bytes memory sig) = _vector(0);
        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

        uint256[4] memory at = [uint256(5), 1500, 3000, 7871]; // R, FORS, bottom layer, top layer (last byte)
        for (uint256 j = 0; j < at.length; j++) {
            bytes memory tampered = bytes.concat(sig);
            tampered[at[j]] = bytes1(uint8(tampered[at[j]]) ^ 0x01);
            assertEq(_validate(account, userOpHash, tampered), SIG_VALIDATION_FAILED, "tampered sig");
        }

        assertEq(_validate(account, userOpHash ^ bytes32(uint256(1)), sig), SIG_VALIDATION_FAILED, "other userOpHash");

        bytes memory truncated = new bytes(sig.length - 1);
        for (uint256 j = 0; j < truncated.length; j++) {
            truncated[j] = sig[j];
        }
        assertEq(_validate(account, userOpHash, truncated), SIG_VALIDATION_FAILED, "wrong-length sig");

        // Control: the untouched signature still validates on the same account.
        assertEq(_validate(account, userOpHash, sig), SIG_VALIDATION_SUCCESS, "control");
    }

    /// End to end with a fresh key from the Python signer: the userOpHash commits to the deployed account
    /// address and chain id (a stand-in for EntryPoint.getUserOpHash), so it can only be signed after the
    /// account exists. The signer has no keygen-only mode, so the first call (any message) gives the key.
    /// Needs pycryptodome (`pip install pycryptodome`); two signatures, ~30 s.
    function testValidateUserOpFFI_Python() public {
        bytes32 masterSk = keccak256("SLH-DSA-Keccak-128s account FFI master key");
        (bytes32 pkSeed, bytes32 pkRoot,) = _sign(masterSk, bytes32(0));
        SphincsAccount account = factory.createAccount(ecdsaOwner, pkSeed, pkRoot);

        bytes32 userOpHash = keccak256(abi.encode(address(account), uint256(0), ENTRYPOINT_V09, block.chainid));
        (bytes32 seed2, bytes32 root2, bytes memory sig) = _sign(masterSk, userOpHash);
        assertEq(seed2, pkSeed, "same key: pkSeed");
        assertEq(root2, pkRoot, "same key: pkRoot");

        assertEq(_validate(account, userOpHash, sig), SIG_VALIDATION_SUCCESS, "fresh 128s userOp");
    }
}
