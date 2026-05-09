// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/SLH-DSA-keccak-128-24verifier.sol";

contract SLH_DSA_Keccak_128_24_CalldataGas is Test {
    SLH_DSA_Keccak_128_24_Verifier verifier;
    bytes32 cachedSeed;
    bytes32 cachedRoot;
    bytes   cachedSig;

    bytes32 constant MSG = 0xdeadbeef00000000000000000000000000000000000000000000000000000000;
    bytes32 constant SK  = 0x1111111111111111111111111111111111111111111111111111111111111111;

    function setUp() public {
        verifier = new SLH_DSA_Keccak_128_24_Verifier();
        string[] memory inputs = new string[](4);
        inputs[0] = ".venv/bin/python";
        inputs[1] = "script/slh_dsa_keccak_128_24_fast_signer.py";
        inputs[2] = vm.toString(SK);
        inputs[3] = vm.toString(MSG);
        bytes memory result = vm.ffi(inputs);
        (cachedSeed, cachedRoot, cachedSig) = abi.decode(result, (bytes32, bytes32, bytes));
    }

    function _measure(bytes32 seed, bytes32 root, bytes32 m, bytes calldata sig)
        external view returns (uint256 gasUsed)
    {
        uint256 g0 = gasleft();
        verifier.verify(seed, root, m, sig);
        gasUsed = g0 - gasleft();
    }

    function testVerifyGasCalldata() public {
        uint256 g = this._measure(cachedSeed, cachedRoot, MSG, cachedSig);
        emit log_named_uint("Keccak verify gas (sig in calldata)", g);
    }
}
