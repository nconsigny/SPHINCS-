// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../../src/keccak/LeanSphincs-FAsm.sol";
import "../../src/SphincsOwnerAccount.sol";

/// @dev The Safe functions the tests use. They have this ABI at v1.4.1, v1.5.0 and main
///      (`Enum.Operation` is a uint8 on the wire).
interface ISafeLike {
    function setup(
        address[] calldata owners,
        uint256 threshold,
        address to,
        bytes calldata data,
        address fallbackHandler,
        address paymentToken,
        uint256 payment,
        address payable paymentReceiver
    ) external;

    function execTransaction(
        address to,
        uint256 value,
        bytes calldata data,
        uint8 operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address payable refundReceiver,
        bytes memory signatures
    ) external payable returns (bool);

    function getTransactionHash(
        address to,
        uint256 value,
        bytes calldata data,
        uint8 operation,
        uint256 safeTxGas,
        uint256 baseGas,
        uint256 gasPrice,
        address gasToken,
        address refundReceiver,
        uint256 nonce
    ) external view returns (bytes32);

    function nonce() external view returns (uint256);
    function getThreshold() external view returns (uint256);
    function getOwners() external view returns (address[] memory);
    function isOwner(address owner) external view returns (bool);
    function domainSeparator() external view returns (bytes32);
    function VERSION() external view returns (string memory);
}

interface ISafeProxyFactoryLike {
    function createProxyWithNonce(address singleton, bytes memory initializer, uint256 saltNonce)
        external
        returns (address proxy);
}

/// @notice Shared pieces of the Safe + SphincsOwnerAccount tests: real Safe artifacts, owner
///         accounts with leanSphincs-f keys, signatures from the Rust CLI, and the Safe
///         `signatures` encoding.
abstract contract SafePqHarness is Test {
    string constant LSFK = "signers/leansphincs-f-keccak/target/release/lsfk";
    // Prints `fresh`, `missing`, or `stale` when a crate source is newer than the binary. Same
    // probe as LeanSphincsFTest.
    string constant LSFK_PROBE = "d=signers/leansphincs-f-keccak; b=$d/target/release/lsfk; "
        "if [ ! -x $b ]; then echo missing; "
        "elif [ -n \"$(find $d/Cargo.toml $d/Cargo.lock $d/src -newer $b \\( -name '*.rs' -o -name 'Cargo.*' \\) "
        "2>/dev/null | head -n 1)\" ]; then echo stale; else echo fresh; fi";

    // keccak256("EIP712Domain(uint256 chainId,address verifyingContract)")
    bytes32 constant DOMAIN_SEPARATOR_TYPEHASH = 0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218;
    // keccak256("SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,
    //            uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)")
    bytes32 constant SAFE_TX_TYPEHASH = 0xbb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8;

    uint256 constant SIG_LEN = 4660; // leanSphincs-f

    struct PqOwner {
        bytes32 seed; // test seed of the leanSphincs-f key (pruned key, b = 8)
        SphincsOwnerAccount account;
    }

    struct SafeTx {
        address to;
        uint256 value;
        bytes data;
        uint8 operation;
        uint256 safeTxGas;
        uint256 baseGas;
        uint256 gasPrice;
        address gasToken;
        address refundReceiver;
    }

    /// One entry of a Safe `signatures` blob.
    struct Entry {
        address owner;
        bool isContract; // true: v = 0, `sig` goes to the dynamic part; false: v = 1, `s` is the word after `owner`
        bytes32 s;
        bytes sig;
    }

    LeanSphincsFAsm verifier;
    address frameModule;

    // ───────────────────────────── signer ─────────────────────────────

    /// As SphincsAccountLeanSphincsFTest: a stale binary fails, a missing one skips except under CI.
    function _requireLsfk() internal {
        string[] memory probe = new string[](3);
        probe[0] = "sh";
        probe[1] = "-c";
        probe[2] = LSFK_PROBE;
        bytes memory state = vm.ffi(probe);
        string memory build = " (cd signers/leansphincs-f-keccak && cargo build --release)";
        if (keccak256(state) == keccak256("missing")) {
            assertEq(vm.envOr("CI", string("")), "", string.concat(LSFK, " is not built under CI:", build));
            vm.skip(true, string.concat(LSFK, " not built:", build));
        }
        assertEq(string(state), "fresh", string.concat(LSFK, " is older than the crate sources:", build));
    }

    function _lsfkSign(bytes32 seed, bytes32 message) internal returns (bytes32, bytes32, bytes memory) {
        string[] memory inputs = new string[](5);
        inputs[0] = LSFK;
        inputs[1] = "sign";
        inputs[2] = vm.toString(seed);
        inputs[3] = "8";
        inputs[4] = vm.toString(message);
        return abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes));
    }

    // ───────────────────────────── deployment ─────────────────────────────

    function _deployVerifierAndModule() internal {
        verifier = new LeanSphincsFAsm();
        bytes memory initcode =
            vm.parseJsonBytes(vm.readFile("out/SphincsFrameVerify.yul/SphincsFrameVerify.json"), ".bytecode.object");
        frameModule = _create(initcode);
    }

    function _newOwner(string memory label) internal returns (PqOwner memory o) {
        o.seed = keccak256(bytes(label));
        // Keygen is deterministic: any signature yields the key words.
        (bytes32 pkSeed, bytes32 pkRoot,) = _lsfkSign(o.seed, bytes32(0));
        o.account = new SphincsOwnerAccount(pkSeed, pkRoot, address(verifier), frameModule);
    }

    /// `n` owners, sorted by account address ascending (the order a Safe wants signatures in).
    function _newOwners(string memory prefix, uint256 n) internal returns (PqOwner[] memory os) {
        os = new PqOwner[](n);
        for (uint256 i = 0; i < n; i++) os[i] = _newOwner(string.concat(prefix, vm.toString(i)));
        for (uint256 i = 1; i < n; i++) {
            for (uint256 j = i; j > 0 && address(os[j - 1].account) > address(os[j].account); j--) {
                (os[j - 1], os[j]) = (os[j], os[j - 1]);
            }
        }
    }

    /// The creation code of the unmodified Safe contract `name` compiled from `source`.
    /// Three Safe revisions are built side by side, so forge writes their artifacts under
    /// collision-resolved directories (`out/Safe.sol`, `out/contracts/Safe.sol`, ...) and
    /// `vm.getCode("...:Safe")` cannot tell them apart. This walks the candidates and takes the
    /// one whose metadata names `source` as its compilation target.
    function _safeArtifact(string memory source, string memory name) internal view returns (bytes memory) {
        string[] memory parts = vm.split(source, "/");
        string memory suffix = "";
        for (uint256 k = 1; k <= parts.length; k++) {
            suffix = k == 1 ? parts[parts.length - 1] : string.concat(parts[parts.length - k], "/", suffix);
            string memory path = string.concat("out/", suffix, "/", name, ".json");
            if (!vm.exists(path)) continue;
            string memory json = vm.readFile(path);
            string[] memory target = vm.parseJsonKeys(json, ".metadata.settings.compilationTarget");
            if (target.length == 1 && keccak256(bytes(target[0])) == keccak256(bytes(source))) {
                assertEq(vm.parseJsonString(json, ".metadata.compiler.version"), "0.7.6+commit.7338295f", "Safe compiler");
                return vm.parseJsonBytes(json, ".bytecode.object");
            }
        }
        revert(string.concat("no artifact for ", source, ":", name));
    }

    function _create(bytes memory initcode) internal returns (address a) {
        assembly ("memory-safe") {
            a := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(a != address(0), "create failed");
    }

    function _ownerAddresses(PqOwner[] memory os, uint256 n) internal pure returns (address[] memory a) {
        a = new address[](n);
        for (uint256 i = 0; i < n; i++) a[i] = address(os[i].account);
    }

    function _setupData(address[] memory owners, uint256 threshold) internal pure returns (bytes memory) {
        return abi.encodeCall(
            ISafeLike.setup, (owners, threshold, address(0), "", address(0), address(0), 0, payable(address(0)))
        );
    }

    // ───────────────────────────── Safe transaction hash ─────────────────────────────

    /// The EIP-712 pre-image a Safe hashes: `0x19 0x01 ‖ domainSeparator ‖ structHash`.
    /// Safe up to 1.4.1 passes these 66 bytes to `isValidSignature(bytes,bytes)`.
    function _safeTxPreimage(address safe, SafeTx memory t, uint256 nonce) internal view returns (bytes memory) {
        bytes32 domain = keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH, block.chainid, safe));
        bytes32 structHash = keccak256(
            abi.encode(
                SAFE_TX_TYPEHASH,
                t.to,
                t.value,
                keccak256(t.data),
                t.operation,
                t.safeTxGas,
                t.baseGas,
                t.gasPrice,
                t.gasToken,
                t.refundReceiver,
                nonce
            )
        );
        return abi.encodePacked(bytes1(0x19), bytes1(0x01), domain, structHash);
    }

    function _safeTxHash(address safe, SafeTx memory t, uint256 nonce) internal view returns (bytes32) {
        return keccak256(_safeTxPreimage(safe, t, nonce));
    }

    function _getTransactionHash(ISafeLike safe, SafeTx memory t, uint256 nonce) internal view returns (bytes32) {
        return safe.getTransactionHash(
            t.to, t.value, t.data, t.operation, t.safeTxGas, t.baseGas, t.gasPrice, t.gasToken, t.refundReceiver, nonce
        );
    }

    function _execCalldata(SafeTx memory t, bytes memory signatures) internal pure returns (bytes memory) {
        return abi.encodeCall(
            ISafeLike.execTransaction,
            (
                t.to,
                t.value,
                t.data,
                t.operation,
                t.safeTxGas,
                t.baseGas,
                t.gasPrice,
                t.gasToken,
                payable(t.refundReceiver),
                signatures
            )
        );
    }

    // ───────────────────────────── signatures ─────────────────────────────

    /// The sender's entry: `{owner}{s}{v = 1}`. The Safe accepts it because `owner` is
    /// `msg.sender`. Safe main requires a non-zero `s` to equal the Safe transaction hash;
    /// earlier versions ignore `s`.
    function _preValidated(address owner, bytes32 s) internal pure returns (Entry memory e) {
        e.owner = owner;
        e.s = s;
    }

    /// A co-signer's entry: `{owner}{offset}{v = 0}` plus `{length}{signature}`.
    function _contractSig(address owner, bytes memory sig) internal pure returns (Entry memory e) {
        e.owner = owner;
        e.isContract = true;
        e.sig = sig;
    }

    function _cosign(PqOwner memory o, bytes32 hash) internal returns (Entry memory) {
        (,, bytes memory sig) = _lsfkSign(o.seed, hash);
        return _contractSig(address(o.account), sig);
    }

    /// The Safe `signatures` bytes for `es`, in the order given (a Safe wants owners ascending;
    /// tests also build wrong orders on purpose).
    function _blob(Entry[] memory es) internal pure returns (bytes memory out) {
        bytes memory dynamicPart;
        uint256 offset = es.length * 65;
        for (uint256 i = 0; i < es.length; i++) {
            if (es[i].isContract) {
                out = bytes.concat(out, bytes32(uint256(uint160(es[i].owner))), bytes32(offset), bytes1(0x00));
                dynamicPart = bytes.concat(dynamicPart, bytes32(es[i].sig.length), es[i].sig);
                offset += 32 + es[i].sig.length;
            } else {
                out = bytes.concat(out, bytes32(uint256(uint160(es[i].owner))), es[i].s, bytes1(0x01));
            }
        }
        out = bytes.concat(out, dynamicPart);
    }

    function _entries(Entry memory a, Entry memory b) internal pure returns (Entry[] memory es) {
        es = new Entry[](2);
        (es[0], es[1]) = (a, b);
    }

    function _entries(Entry memory a, Entry memory b, Entry memory c) internal pure returns (Entry[] memory es) {
        es = new Entry[](3);
        (es[0], es[1], es[2]) = (a, b, c);
    }

    /// Sorted by owner ascending.
    function _sorted(Entry[] memory es) internal pure returns (Entry[] memory) {
        for (uint256 i = 1; i < es.length; i++) {
            for (uint256 j = i; j > 0 && es[j - 1].owner > es[j].owner; j--) {
                (es[j - 1], es[j]) = (es[j], es[j - 1]);
            }
        }
        return es;
    }
}
