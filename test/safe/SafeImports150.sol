// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>

pragma solidity >=0.7.0 <0.9.0;

// Compiles the unmodified Safe 1.5.0 sources (lib/safe-smart-account-1.5.0) under the "safe" compiler
// profile of foundry.toml. Tests load the artifacts by path; nothing imports this file.
import "safe-1.5.0/Safe.sol";
import "safe-1.5.0/proxies/SafeProxyFactory.sol";
