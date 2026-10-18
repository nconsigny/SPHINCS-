// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/keccak/SPHINCs-C12Asm.sol";
import "../src/blake/SPHINCs-C12-BLAKE.sol";

/// @notice Regression test for the C12 / C12-BLAKE signer FORS PRF (review finding
///         c12-fors-prf-not-position-bound). The FORS leaf secrets used to depend only on
///         (FORS tree, leaf), so every one of the 2^20 FORS instances under a key shared one
///         table of 2,560 secrets. About 1,000 honest signatures revealed the whole table and
///         an attacker could then build a signature on any message: grind R until H_msg lands
///         on a position that already has an honest signature, rebuild the FORS trees there
///         from the harvested secrets and reuse that signature's hypertree half.
///
///         The helper (test/py/c12_fors_binding.py) signs two honest messages at different
///         hypertree positions that open the same FORS slot (t, j), and moves A's revealed
///         secret for that slot into B. With the position-bound PRF the secrets differ and the
///         transplanted signature fails; with the old PRF it was a byte-identical no-op that
///         still verified.
contract SphincsC12ForsBindingTest is Test {
    struct Pair {
        bytes32 seed;
        bytes32 root;
        bytes32 msgA;
        bytes sigA;
        bytes32 msgB;
        bytes sigB;
        bytes sigBT;
        uint256 t;
    }

    function _pair(string memory backend) internal returns (Pair memory p) {
        string[] memory inputs = new string[](3);
        inputs[0] = "python3";
        inputs[1] = "test/py/c12_fors_binding.py";
        inputs[2] = backend;
        (p.seed, p.root, p.msgA, p.sigA, p.msgB, p.sigB, p.sigBT, p.t) =
            abi.decode(vm.ffi(inputs), (bytes32, bytes32, bytes32, bytes, bytes32, bytes, bytes, uint256));
    }

    function _forsSecret(bytes memory sig, uint256 t) internal pure returns (bytes16 sk) {
        uint256 off = 32 + t * 128; // R(32) | FORS tree t = sk(16) | auth(7 x 16)
        assembly {
            sk := mload(add(add(sig, 0x20), off))
        }
    }

    function _verify(address v, Pair memory p, bytes32 m, bytes memory s) internal view returns (bool ok) {
        (bool callOk, bytes memory ret) = v.staticcall(
            abi.encodeWithSignature("verify(bytes32,bytes32,bytes32,bytes)", p.seed, p.root, m, s)
        );
        if (!callOk || ret.length < 32) return false;
        ok = abi.decode(ret, (bool));
    }

    function _check(address v, string memory backend) internal {
        Pair memory p = _pair(backend);
        assertTrue(_verify(v, p, p.msgA, p.sigA), "honest sig A must verify");
        assertTrue(_verify(v, p, p.msgB, p.sigB), "honest sig B must verify");
        assertTrue(
            _forsSecret(p.sigA, p.t) != _forsSecret(p.sigB, p.t),
            "same FORS slot revealed the same secret at two hypertree positions"
        );
        assertFalse(_verify(v, p, p.msgB, p.sigBT), "secret harvested at another position rebuilt the FORS leaf");
    }

    function testC12ForsSecretsArePositionBound() public {
        _check(address(new SPHINCs_C12Asm()), "keccak");
    }

    function testC12BlakeForsSecretsArePositionBound() public {
        _check(address(new SPHINCs_C12BlakeAsm()), "blake");
    }
}
