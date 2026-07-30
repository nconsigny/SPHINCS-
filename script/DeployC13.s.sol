// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Script.sol";
import "../src/keccak/SPHINCs-C13Asm.sol";
import "../src/SphincsAccountFactory.sol";
import "account-abstraction/interfaces/IEntryPoint.sol";

/// @title DeployC13 — deploys shared C13 verifier + hybrid-4337 factory
/// @notice Sepolia (11155111) and ethrex (1729) both expose EntryPoint v0.9
///         at the canonical address. Run e.g.:
///           forge script script/DeployC13.s.sol --rpc-url sepolia --broadcast
///           forge script script/DeployC13.s.sol --rpc-url ethrex  --broadcast
///         Frame accounts (EIP-8141, ethrex only in practice) are deployed
///         separately via legacy/script/deploy_frame_account.py with --variant c13.
contract DeployC13 is Script {
    address constant ENTRYPOINT_V09 = 0x433709009B8330FDa32311DF1C2AFA402eD8D009;

    function run() external {
        uint256 deployerKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerKey);

        console.log("=== DeployC13 ===");
        console.log("Chain id  :", block.chainid);
        console.log("Deployer  :", deployer);
        console.log("EntryPoint:", ENTRYPOINT_V09);

        // Sanity: confirm EntryPoint v0.9 is deployed on this chain. Skip the
        // check on Anvil (chainid 31337) so unit tests can still drive the script.
        if (block.chainid != 31337) {
            uint256 epCodeSize;
            address ep = ENTRYPOINT_V09;
            assembly { epCodeSize := extcodesize(ep) }
            require(epCodeSize > 0, "EntryPoint v0.9 not deployed on this chain");
        }

        vm.startBroadcast(deployerKey);

        SphincsC13Asm verifier = new SphincsC13Asm();
        console.log("Shared C13 verifier:", address(verifier));

        SphincsAccountFactory factory = new SphincsAccountFactory(
            IEntryPoint(ENTRYPOINT_V09),
            address(verifier)
        );
        console.log("SphincsAccountFactory:", address(factory));

        vm.stopBroadcast();
    }
}
