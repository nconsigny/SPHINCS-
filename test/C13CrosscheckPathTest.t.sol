// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

/// @notice Regression test for review finding c13-crosscheck-stale-verifier-path: the
///         Python / Rust / Solidity C13 crosscheck (signers/c13-crosscheck/crosscheck.py)
///         passed `src/SPHINCs-C13Asm.sol:SphincsC13Asm` to `forge create` after the verifier
///         moved to src/keccak/, so its on-chain step died before any verify call. CI does
///         not run that harness, so this checks its VERIFIER_SRC still resolves.
contract C13CrosscheckPathTest is Test {
    function testCrosscheckVerifierSourceExists() public {
        string[] memory inputs = new string[](3);
        inputs[0] = "python3";
        inputs[1] = "-c";
        inputs[2] = "import sys; sys.path.insert(0, 'signers/c13-crosscheck'); import crosscheck as c; "
            "print('0x' + ('%064x' % int(c.verifier_src_ok())))";
        bool ok = abi.decode(vm.ffi(inputs), (bool));
        assertTrue(ok, "crosscheck.py VERIFIER_SRC does not name an existing verifier contract");
    }
}
