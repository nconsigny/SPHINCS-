// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity >=0.7.0 <0.9.0;

// Compiles the unmodified Safe main sources (lib/safe-smart-account-main) under the "safe" compiler
// profile of foundry.toml. Tests load the artifacts by path; nothing imports this file.
import "safe-main/Safe.sol";
import "safe-main/proxies/SafeProxyFactory.sol";
