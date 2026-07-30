// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Script.sol";
import "forge-std/console2.sol";
import "../src/blake/SPHINCs-C11-BLAKE.sol";
import "../src/blake/SPHINCs-C13-BLAKE.sol";
import "../src/blake/SPHINCs-C12-BLAKE.sol";

/// @notice Deploys the three BLAKE2b (precompile 0x09) SPHINCS+ verifiers to Sepolia.
///         PRIVATE_KEY is read from .env via vm.envUint (never on the CLI).
contract DeployBlakeSepolia is Script {
    function run() external {
        uint256 deployerKey = vm.envUint("PRIVATE_KEY");
        vm.startBroadcast(deployerKey);

        SphincsC11BlakeAsm c11 = new SphincsC11BlakeAsm();
        SphincsC13BlakeAsm c13 = new SphincsC13BlakeAsm();
        SPHINCs_C12BlakeAsm c12 = new SPHINCs_C12BlakeAsm();

        vm.stopBroadcast();

        console2.log("C11-BLAKE:", address(c11));
        console2.log("C13-BLAKE:", address(c13));
        console2.log("C12-BLAKE:", address(c12));
    }
}
