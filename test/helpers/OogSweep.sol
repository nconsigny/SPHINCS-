// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @notice Gas-limit sweep for the SHA-256 twins (C10/C11/C12/C13-SHA). Their kernel pop()s
///         every 0x02 call and has the precompile write its output straight into the next
///         call's input slot, so a call that failed while the frame went on would pass its
///         input through as its output. What rules that out is EIP-150: an out-of-gas 0x02
///         call burns all the gas it was forwarded (all but 1/64 of what was left), leaving
///         the verifier at most P/63 gas (P <= 372 here), too little to go on. The sweep
///         calls `verify` with every gas limit from `window` below the smallest limit that
///         does not revert up to a little above it. Each limit runs the frame dry one gas
///         later, so over the window every 0x02 call in that stretch of the run is the one
///         that fails. A valid signature must then either revert or verify: a `false` means
///         some call failed and the frame carried on with a stale buffer.
library OogSweep {
    function run(address v, bytes memory data, uint256 maxGas, uint256 window)
        internal
        view
        returns (uint256 minGas, uint256 nFalse, uint256 nTrue)
    {
        uint256 lo = window;
        uint256 hi = maxGas;
        while (lo < hi) {
            uint256 mid = (lo + hi) / 2;
            (bool ok,) = v.staticcall{gas: mid}(data);
            if (ok) hi = mid;
            else lo = mid + 1;
        }
        minGas = lo;
        for (uint256 g = lo - window; g < lo + 32; ++g) {
            (bool ok, bytes memory ret) = v.staticcall{gas: g}(data);
            if (!ok) continue;
            if (ret.length == 32 && uint256(bytes32(ret)) == 1) nTrue++;
            else nFalse++;
        }
    }
}
