# Deployments

Every deployment recorded in the README so far (moved here unchanged when the README was shortened). The README lists only the current ones.

EntryPoint v0.9: `0x433709009B8330FDa32311DF1C2AFA402eD8D009` (Sepolia)

## 2026-10-20: leanSphincs, leanSphincs-s, leanSphincs-f

Built from `main` at `e22c861`; each deployed runtime is byte-identical to the build.

**Sepolia, verifiers only.** Each verified a KAT signature (fixture vector 3, message `0xdeadbeef…`) in a real
transaction. The tx gas is the calldata floor (about 64 gas per calldata byte), not the verifier's execution
(39–53K).

| Variant | Verifier | Verify tx | Tx gas |
|---|---|---|---|
| leanSphincs | [`0x4B1CF99FD1C9dfD6F3F4BE6751E902F71C6f0db0`](https://sepolia.etherscan.io/address/0x4B1CF99FD1C9dfD6F3F4BE6751E902F71C6f0db0) | [`0xb59d6e9a…`](https://sepolia.etherscan.io/tx/0xb59d6e9a77e7d5791631d614334756ead97e45f2a5476f5a5352a8fa4d673a23) | 390,040 |
| leanSphincs-s | [`0x7E4060786AE34E143978dF07da82A388292316a7`](https://sepolia.etherscan.io/address/0x7E4060786AE34E143978dF07da82A388292316a7) | [`0xd81ea86d…`](https://sepolia.etherscan.io/tx/0xd81ea86d6d9f53b9b6944462ec8eb6d2f9f185128884951c8c7be5cfc7020b81) | 293,784 |
| leanSphincs-f | [`0xd75974064757B7C3C7988AbD38B3D722E0d8011B`](https://sepolia.etherscan.io/address/0xd75974064757B7C3C7988AbD38B3D722E0d8011B) | [`0xbf3677bc…`](https://sepolia.etherscan.io/tx/0xbf3677bccba221825c3d60f573cf135ce83f006f6bb54a5f690e896f1b2d1f1a) | 324,504 |

**ethrex privacy testnet (chain 8141, `rpc1.privacy.ethrex.xyz`), full EIP-8141 frame transactions.** This network runs
the current EIP-8141 opcodes (SIGDATACOPY at `0xb5`), so `src/SphincsFrameVerify.yul` runs unchanged. Shared frame
module [`0xAA481E835ec1b82E528d6D36D432F9Af440B4295`](https://dora.privacy.ethrex.xyz/address/0xAA481E835ec1b82E528d6D36D432F9Af440B4295). One
`SphincsFrameAccount` per variant, each holding a fresh Light-tier (2^13) key. Each tx has two frames: VERIFY (the
account checks its leanSphincs signature over `compute_sig_hash(tx)`, carried in an ARBITRARY signature entry, and
approves execution and payment), then SENDER (0.00001 ETH to `0x…dEaD`). The account pays its own gas.

| Variant | Verifier | Frame account | Frame tx | VERIFY frame | Tx gas |
|---|---|---|---|---|---|
| leanSphincs | [`0x6594157F…F5C9`](https://dora.privacy.ethrex.xyz/address/0x6594157F1d690CbeBAA93dD13579FEb14E81F5C9) | [`0x874f5ba1d47B477CB70999795cAf7E6Bb53EeDD7`](https://dora.privacy.ethrex.xyz/address/0x874f5ba1d47B477CB70999795cAf7E6Bb53EeDD7) | [`0x86d8c16f…`](https://dora.privacy.ethrex.xyz/tx/0x86d8c16fcf091851de57dcd08eddd7fd91ee34f180568506308cdd5241764404) | 60,767 | 385,322 |
| leanSphincs-s | [`0xae3bA3e1…481a`](https://dora.privacy.ethrex.xyz/address/0xae3bA3e1DC1bD3866608ECA1498D3e9263B3481a) | [`0x8e2812cc597389b0E6522E610eAaeD635acbaE62`](https://dora.privacy.ethrex.xyz/address/0x8e2812cc597389b0E6522E610eAaeD635acbaE62) | [`0x56f1d1fd…`](https://dora.privacy.ethrex.xyz/tx/0x56f1d1fd23119f716244f55956047fd0b8b650b7e51c52752ec5a272d7307993) | 46,899 | 288,042 |
| leanSphincs-f | [`0x89FCf098…14D4`](https://dora.privacy.ethrex.xyz/address/0x89FCf098dCf39fc3445a435504162f91bECa14D4) | [`0xaD6b0De1E1b5792AF346E192346D120B484560b7`](https://dora.privacy.ethrex.xyz/address/0xaD6b0De1E1b5792AF346E192346D120B484560b7) | [`0x97b498ee…`](https://dora.privacy.ethrex.xyz/tx/0x97b498ee82654113c62c88934d827897d33e921a6050ff641efb95cbb99999dc) | 51,948 | 319,786 |

Frame tx gas is the EIP-7976 calldata floor (16 gas per token, every byte 4 tokens) plus 19,050 fixed (base 12,000,
475 per frame, 100 per ARBITRARY entry, 6,000 for the value transfer): about 21.4K + 64 gas per signature byte.
The VERIFY frame's execution (47–61K) stays far below that floor. Send one with
`script/send_frame_tx_leansphincs.py <rpc> <account> <signer> <key file> <recipient> <wei>`. It uses the
`hegota-testnet` wire format of lambdaclass/ethrex, signs with `lsk` / `lssk` / `lsfk sign-key`, and dry-runs the
tx with `ethrex_simulateFrameTransaction` first. The Hegotá devnet (chain 3151908) has SIGDATACOPY at `0xBA`
instead and would need a module built with that byte.

## 2026-06-04 redeploy: new accounts & factories

Hardened C13 verifiers (commit 16732a7), new C13 `SphincsAccountFactory` instances and freshly-deployed accounts (each account funded 0.1 ETH):

| Chain | Contract | Address |
|---|---|---|
| Sepolia | C13 verifier (hardened) | [`0xc6f400...`](https://sepolia.etherscan.io/address/0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2) |
| Sepolia | SphincsAccountFactory | [`0x8830d3...`](https://sepolia.etherscan.io/address/0x8830d36284829656F2A60CD028062686069FABA4) |
| Sepolia | SphincsAccountFactory (fresh) | [`0x79FDD0...`](https://sepolia.etherscan.io/address/0x79FDD0aFcb2214D6C17E639dA7eF6357956Cd857) |
| Sepolia | SphincsAccount (ERC-4337 hybrid, C13) | [`0x012801...`](https://sepolia.etherscan.io/address/0x01280171F336869e9c96F9e6eb674b1548D10dD4) |
| ethrex | C13 verifier (hardened) | [`0xAA481E...`](https://explorer.eip-8141.ethrex.xyz/address/0xAA481E835ec1b82E528d6D36D432F9Af440B4295) |
| ethrex | SphincsAccountFactory | [`0x874f5b...`](https://explorer.eip-8141.ethrex.xyz/address/0x874f5ba1d47B477CB70999795cAf7E6Bb53EeDD7) |
| ethrex | Frame account (EIP-8141, C13) | [`0x253A4d...`](https://explorer.eip-8141.ethrex.xyz/address/0x253A4d0100fe7A2a6d6839b37BDC283FD1dF693d) |

> ethrex's `SphincsAccountFactory` is deployed for completeness, but EntryPoint v0.9 has no code on ethrex, so accounts created there are inert for ERC-4337. ethrex's functional PQ path is the EIP-8141 frame account. The full address record is kept locally in the gitignored `script/.c13_addresses.json` (read by `script/send_userop_c13.py` and `script/send_frame_tx_c13.py`).

## Sepolia (ERC-4337 Hybrid, C-series)

| Variant | Verifier | Account | Gas | Tx |
|---|---|---|---|---|
| C9 | [`0x18F005...`](https://sepolia.etherscan.io/address/0x18F005EECd41624644AA364bA8857258FEB3C26D) | [`0xA94111...`](https://sepolia.etherscan.io/address/0xA941116763AE386a50133c5af40356c9D93b2978) | 300 K | [`0x8366513b...`](https://sepolia.etherscan.io/tx/0x8366513b096ee53dd1cb105363ab21a52267dd966b822b4bb2cf5492abf1550f) |
| C11 | [`0xC25ef5...`](https://sepolia.etherscan.io/address/0xC25ef566884DC36649c3618EEDF66d715427Fd74) | [`0x3C3b0c...`](https://sepolia.etherscan.io/address/0x3C3b0c3498E5ed9350F6fBFA0Ef8dC55f524eA50) | 308 K | [`0x9fba169c...`](https://sepolia.etherscan.io/tx/0x9fba169ca76b6712586e44e1a4a2d0407b8b8b9ce767272a193e41a756260b74) |
| **C13** | [`0xce176d...`](https://sepolia.etherscan.io/address/0xce176df2680f6612a61486f74502db62d014d23d) | [`0xcef985...`](https://sepolia.etherscan.io/address/0xcef985d4db485e96ab9187ad462561bff241db0d) (factory [`0xcaf5d2...`](https://sepolia.etherscan.io/address/0xcaf5d2582eb405e3c4b65f3a52d147badfd96fed)) | 293 K | [`0xbbf06456...`](https://sepolia.etherscan.io/tx/0xbbf06456145a4daea1b5006f1f5d7b214c62c1c2877eabb61ae4b26e453189d0) |

> **C13 on Sepolia uses the FIPS 205 §4.2 uncompressed 32-byte ADRS** (keccak256 hash). First verifier in the repo on the FIPS address layout. Standalone verify tx-level gas: **188,278**. Full hybrid-4337 `handleOps` UserOp gas: **292,727** (ECDSA recovery + C13 verify + 0.00001 ETH self-transfer through `SphincsAccount.execute`). The verifier, factory, account and tx in this row predate the 2026-06-04 hardening redeploy; the current verifier is in the table above, and the canonical address record is the gitignored local `script/.c13_addresses.json`.

## Sepolia (SLH-DSA-128-24 standalone verifiers, no account wired yet)

> The SHA-2 verifier below predates the 2026-06-03 switch to FIPS 205 *external* mode (review SLH-X-f1). The
> external-mode verifier is `0x12B712ad3ca6D81d4B3690B2f93420cd65EA0553` (Sepolia; it verified the pinned KAT in
> `signers/slhvk-sha2-128-24/kat-counter0.json`, as did `0xa191d77902CaB41e95fec589DE3d72bA36c57b4f` on the
> now-defunct ethrex devnet).

| Variant | Verifier | Deploy tx | Sample verify tx | Verify-tx gas |
|---|---|---|---|---|
| SLH-DSA-SHA2-128-24 | [`0x9Fe417...`](https://sepolia.etherscan.io/address/0x9Fe41769395BC9fefb7e0d340064ed29F4a4Af91) | [`0x09be3c59...`](https://sepolia.etherscan.io/tx/0x09be3c5984ed99a93f9c43881822d9937e1efa9b31aee0630f59fca814d90e15) | [`0x00fa6b37...`](https://sepolia.etherscan.io/tx/0x00fa6b37347e2bedf37429a74563b2c68502becdffe3257ebde90f63e165030a) | **225,642** |
| SLH-DSA-Keccak-128-24 | [`0x2Ac9Ec...`](https://sepolia.etherscan.io/address/0x2Ac9Ec4a2A062aFc1be718e77ec3300D087E6205) | [`0x253aa6dc...`](https://sepolia.etherscan.io/tx/0x253aa6dc5c93a201abc7a5cfb4ce27cdeafb35e34fc69c23ef1daae0535c4c4a) | [`0x90d785a1...`](https://sepolia.etherscan.io/tx/0x90d785a112fd0198b4506caf432632777aef43b00ceb648e864dcb119311fed4) | **177,910** |

Verify-tx gas is the full top-level tx cost including 21 K tx base + ~63 K for the 3,872-B calldata payload; pure assembly execution is ~142 K (SHA-2) / ~94 K (Keccak). Keccak wins by ~21 % tx-level and ~34 % assembly-level because every F / H / T is a single native `keccak256` opcode, while the SHA-2 variant pays a `staticcall(0x02)` dispatch per hash × ~280 hashes.

## ethrex Testnet (EIP-8141 Frame Tx - Pure PQ)

> **Defunct (checked 2026-10-18).** The `*.eip-8141.ethrex.xyz` names no longer resolve, and chain
> id 3151908 now belongs to ethrex's Hegotá devnet (`*.hegota.ethrex.xyz`, genesis 2026-08-06),
> where none of the addresses below (or the ethrex rows of the 2026-06-04 table) exist. They are
> kept as a record of the June demo. Before a new frame-account deploy, see
> [docs/SECURITY-REVIEW-2026-10.md §10](SECURITY-REVIEW-2026-10.md): the witness-copy opcode
> differs between the current EIP-8141 text (SIGDATACOPY `0xb5`) and the Hegotá devnet (`0xba`).

Older demo devnet at `demo.eip-8141.ethrex.xyz` (chain 1729): C9 / C10 / C11 frame accounts:

| Variant | Verifier | Frame Account | Gas | Verify | Tx |
|---|---|---|---|---|---|
| C9 | [`0xc0F115...`](https://demo.eip-8141.ethrex.xyz:8082/address/0xc0F115A19107322cFBf1cDBC7ea011C19EbDB4F8) | [`0xc96304...`](https://demo.eip-8141.ethrex.xyz:8082/address/0xc96304e3c037f81dA488ed9dEa1D8F2a48278a75) | 195K | 117K | [`0x393588ec...`](https://demo.eip-8141.ethrex.xyz:8082/tx/0x393588eceeda4839371f103e16b10c5e2900416d7b194faee8478b6561792813) |
| C10 | [`0xD0141E...`](https://demo.eip-8141.ethrex.xyz:8082/address/0xD0141E899a65C95a556fE2B27e5982A6DE7fDD7A) | [`0x07882A...`](https://demo.eip-8141.ethrex.xyz:8082/address/0x07882Ae1ecB7429a84f1D53048d35c4bB2056877) | 203K | 122K | [`0x0a2571f8...`](https://demo.eip-8141.ethrex.xyz:8082/tx/0x0a2571f8423ab4ec75e09623773b22ff91794a82d1b3db2d616b8af354730353) |
| C11 | [`0x315575...`](https://demo.eip-8141.ethrex.xyz:8082/address/0x3155755b79aA083bd953911C92705B7aA82a18F9) | [`0x5bf5b1...`](https://demo.eip-8141.ethrex.xyz:8082/address/0x5bf5b11053e734690269C6B9D438F8C9d48F528A) | 202K | 122K | [`0x053428f5...`](https://demo.eip-8141.ethrex.xyz:8082/tx/0x053428f530521a5c42c4d2406d1cfb8e07baefa0328c0e425045a3ba9317106b) |

Current `eip-8141.ethrex.xyz` devnet (chain **3151908**, Osaka fork, frame opcodes enabled from genesis; RPCs `rpc1`/`rpc2`/`rpc3.eip-8141.ethrex.xyz`):

| Variant | Verifier | Frame Account | Frame Gas | Sample Frame Tx |
|---|---|---|---|---|
| **C13** | [`0x659415...`](https://explorer.eip-8141.ethrex.xyz/address/0x6594157F1d690CbeBAA93dD13579FEb14E81F5C9) | [`0xae3bA3...`](https://explorer.eip-8141.ethrex.xyz/address/0xae3bA3e1DC1bD3866608ECA1498D3e9263B3481a) | **188 K** | [`0xabf3ce2f...`](https://explorer.eip-8141.ethrex.xyz/tx/0xabf3ce2f989fbb1480af2a6c0026f2335b643adb54561ebb536824af8faee81d) |

> EIP-8141 type-0x06 frame tx, two frames: `[VERIFY(frame_account, sigHash‖c13_sig, flags=approve sender+payer), SENDER(0x...dead, value=0.00001 ETH)]`. The VERIFY frame's runtime staticcalls the shared C13 verifier and `APPROVE(0,0,3)`s on success. Sender by the frame account itself (no protocol-level signature needed). Reproduce with `script/send_frame_tx_c13.py`. Note: ethrex's on-chain `FrameTransaction` RLP layout differs from the draft EIP-8141 markdown by omitting the `signatures` field: the script handles this; the deviation is documented inline.
