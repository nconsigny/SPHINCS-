// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity ^0.8.28;

/// @notice Linear disassembly of deployed code, for tests that pin which instructions a
///         contract can execute. PUSH immediates are skipped, so a data byte inside a PUSH32
///         (an immutable, a constant) is never read as an instruction.
library OpcodeScan {
    struct Report {
        uint256[256] count; // instructions per opcode
        uint256 strayGas; // GAS (0x5a) not immediately followed by CALL, CALLCODE, DELEGATECALL or STATICCALL
        uint256 end; // first byte past the scanned instructions
    }

    /// @param solcMetadata strip the CBOR metadata solc appends (its length is the last two
    ///        bytes) and the INVALID byte solc puts in front of it. False for raw Yul objects.
    function scan(bytes memory code, bool solcMetadata) internal pure returns (Report memory r) {
        uint256 end = code.length;
        if (solcMetadata) {
            uint256 metaLen = (uint256(uint8(code[end - 2])) << 8) | uint8(code[end - 1]);
            end = end - 2 - metaLen;
            // 0xa2: a CBOR map of two entries (ipfs, solc), what this repo's builds emit.
            require(uint8(code[end]) == 0xa2, "OpcodeScan: no CBOR metadata where expected");
            require(uint8(code[end - 1]) == 0xfe, "OpcodeScan: no INVALID separator before metadata");
            end -= 1;
        }
        r.end = end;
        uint256 prev = 0x100;
        for (uint256 i = 0; i < end; i++) {
            uint256 op = uint8(code[i]);
            r.count[op]++;
            if (prev == 0x5a && op != 0xf1 && op != 0xf2 && op != 0xf4 && op != 0xfa) r.strayGas++;
            prev = op;
            if (op >= 0x60 && op <= 0x7f) i += op - 0x5f;
        }
        if (prev == 0x5a) r.strayGas++;
    }
}
