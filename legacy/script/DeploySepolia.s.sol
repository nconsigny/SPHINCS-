// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

import "forge-std/Script.sol";
import "../src/SPHINCs-C6Asm.sol";
import "../src/SphincsAccountFactory.sol";

/// @title DeploySepolia - Deploy shared C6 verifier + factory
/// @notice Run: forge script script/DeploySepolia.s.sol --rpc-url sepolia --broadcast
contract DeploySepolia is Script {
    address constant ENTRYPOINT_V09 = 0x433709009B8330FDa32311DF1C2AFA402eD8D009;

    function run() external {
        uint256 deployerKey = vm.envUint("PRIVATE_KEY");

        vm.startBroadcast(deployerKey);

        // 1. Deploy shared verifier (once for everyone)
        SphincsC6Asm verifier = new SphincsC6Asm();
        console.log("Shared verifier:", address(verifier));

        // 2. Deploy factory (points to shared verifier)
        SphincsAccountFactory factory = new SphincsAccountFactory(
            IEntryPoint(ENTRYPOINT_V09),
            address(verifier)
        );
        console.log("Factory:", address(factory));

        vm.stopBroadcast();
    }
}
