# Deployments

Every deployment recorded in the README so far (moved here unchanged when the README was shortened). The README lists only the current ones.

EntryPoint v0.9: `0x433709009B8330FDa32311DF1C2AFA402eD8D009` (Sepolia)

## 2026-11-19: Safe PQ owners (leanSphincs-f)

Built from `main` at `2b09a0e` with `script/deploy_safe_pq_ethrex.py`, on the **ethrex privacy testnet (chain 8141)**.
Three `SphincsOwnerAccount`s with fresh Light-tier leanSphincs-f keys own a 2-of-3 Safe 1.5.0. The Safe is built from
`lib/safe-smart-account-1.5.0` (solc 0.7.6, optimizer off), not the official release bytecode: the canonical Safe
deployments do not exist on this chain. The owner accounts use the leanSphincs-f verifier and frame module of
2026-10-20 (same code as the build, apart from the verifier's metadata hash). Design and results:
[safe-pq-owners.md](safe-pq-owners.md#on-the-ethrex-testnet).

| Contract / tx | Address or hash | Gas |
|---|---|---|
| Owner account 0 (sender) | [`0x8624a856…8f55`](https://dora.privacy.ethrex.xyz/address/0x8624a8560b93d219200004314b434d96426a8f55) (deploy [`0x5153ef0f…`](https://dora.privacy.ethrex.xyz/tx/0x5153ef0f37946e6c38bfd48b9beb47a676126203d28d7480631df8455b51e60b)) | 2,477,216 |
| Owner account 1 (co-signer) | [`0x559ae500…4c71`](https://dora.privacy.ethrex.xyz/address/0x559ae50033fbf0de6b54a13d068ab363fbcf4c71) (deploy [`0xcd12ccc0…`](https://dora.privacy.ethrex.xyz/tx/0xcd12ccc07b71ad9906bd24a25ce015bb19b5afb0854b9bac900f80290d0e0435)) | 2,477,216 |
| Owner account 2 | [`0x2537d07e…8ff1`](https://dora.privacy.ethrex.xyz/address/0x2537d07e56bd56f7721d1d9914547dd5df4f8ff1) (deploy [`0xab37ad78…`](https://dora.privacy.ethrex.xyz/tx/0xab37ad78b4cc96eddd4b1e7cfc4fdfa1a4e213f6c1fdb3dc65d74d6814ba10ab)) | 2,477,216 |
| Safe 1.5.0 singleton | [`0x0d602723…5979`](https://dora.privacy.ethrex.xyz/address/0x0d602723d7f78653a9eefaee9e93bdc944455979) (deploy [`0x7a9746be…`](https://dora.privacy.ethrex.xyz/tx/0x7a9746beeab13af8a506b81ed5cacbe3f0df7bfcce2d932ad660837260a9dd7a)) | 33,469,622 |
| SafeProxyFactory 1.5.0 | [`0x411be15f…9cc0`](https://dora.privacy.ethrex.xyz/address/0x411be15fc959fe9ac978f559f6f2300dfea29cc0) (deploy [`0xf0ecab9f…`](https://dora.privacy.ethrex.xyz/tx/0xf0ecab9f75773df12baf26fbf24017ceaef4ad1bf68240ac5af619939bc46f75)) | 5,341,376 |
| 2-of-3 Safe (proxy) | [`0x593cfd52…7b38`](https://dora.privacy.ethrex.xyz/address/0x593cfd52268c573b9da780038dd1b0b82c8e7b38) (create [`0x07ba4069…`](https://dora.privacy.ethrex.xyz/tx/0x07ba4069bab7212d048ee2bfbe2463f4ca24e04b7f9f1c0f20fa8f3ffb082d80)) | 1,299,284 |
| Frame tx: Safe transfer of 0.001 ETH (block 883,831) | [`0xcdcf2198…`](https://dora.privacy.ethrex.xyz/tx/0xcdcf21985c8807e9a6cbd44fff42be7d08389d0471cbbe279feacb0cdda5d446) | **745,786** |
| VERIFY frame | | 51,904 |
| SENDER frame (`execTransaction`) | | 110,316 + 97,920 state |

The frame tx is `[self_verify, SENDER -> Safe.execTransaction]` from owner 0's account, with owner 1's co-signature
checked by the Safe through `isValidSignature`. Its gas is the calldata floor (647,866) plus the state gas of the
Safe's first nonce write (97,920). Code costs most of the deploys: this testnet prices new code as state growth
(EIP-8037), about 1,530 gas per byte. The key files are outside the repo, in `/projects/safepq-testnet-keys/`.

## 2026-11-04: leanSphincs-layered

Built from the `feat/leansphincs-layered-keccak` working tree (verifier source sha256 `a13a4ed2…`, the reviewed
version). The deployed runtime (3,283 bytes) is byte-identical to the build, and before the frame tx an `eth_call`
of `verify` accepted the Lean known answer and the EthLib `verify_valid_known_answer` vector and rejected a changed
message and `verify_tampered_top_last_sibling`.

**ethrex privacy testnet (chain 8141), full EIP-8141 frame transaction**, the same shape as the 2026-10-20 ones:
the shared frame module [`0xAA481E83…4295`](https://dora.privacy.ethrex.xyz/address/0xAA481E835ec1b82E528d6D36D432F9Af440B4295), one
`SphincsFrameAccount` with a fresh key (`script/leansphincs_layered_signer.py keygen-file`), VERIFY then SENDER
(0.00001 ETH to `0x…dEaD`), the account paying its own gas. Sent with `script/send_frame_tx_leansphincs.py`, with the
Python signer's `sign-key` as the signer.

| Contract / tx | Address or hash | Gas |
|---|---|---|
| Verifier `LeanSphincsLayeredAsm` | [`0xDeFd9710…0026`](https://dora.privacy.ethrex.xyz/address/0xDeFd97108a29c65968C0312573de6ef500970026) (deploy [`0x00315cd1…`](https://dora.privacy.ethrex.xyz/tx/0x00315cd1427d1de504962ce06e7ecb635a70d73d269defc3f11427a04f27348f)) | 5,282,081 |
| Frame account | [`0x08351d32…08C0`](https://dora.privacy.ethrex.xyz/address/0x08351d320f84F93D3605C5688Ff0feFbCC2F08C0) (deploy [`0xfcb733aa…`](https://dora.privacy.ethrex.xyz/tx/0xfcb733aa06179d29a87b17b017f86232d9fda1141ea9c1a2e2ca577dde7d4130)) | 3,067,807 |
| Frame tx (block 685,211) | [`0x902c9423…b3ab`](https://dora.privacy.ethrex.xyz/tx/0x902c942324fa1195bee3e9aa1b48fb84fdee45931250d904cd0992859985b3ab) | **516,906** |
| VERIFY frame | | 90,385 |
| SENDER frame | | 3,000 |

The tx gas is the calldata-floor formula below to the gas, `21,546 + 64 × 7,740 = 516,906`, as it is for the
2026-10-20 txs. The VERIFY frame is the verifier's ~82K plus the frame module's ~8K. The deploys cost more than code
size alone suggests because this testnet prices new code as state growth (EIP-8037).

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
| C13 (for comparison; the 2026-06-04 hardened verifier, same code as `main` apart from the metadata hash) | [`0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2`](https://sepolia.etherscan.io/address/0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2) | [`0x64793ac4…`](https://sepolia.etherscan.io/tx/0x64793ac48235ec1d77f4fb2bbb9f735a2f072a182c3ba69a75a447f88536afa6) | 263,064 |

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
| C13 (for comparison) | [`0x499b3FA0…D96C`](https://dora.privacy.ethrex.xyz/address/0x499b3FA08944317f9fc3F8C8307360E971A8D96C) | [`0x74533B2378568EfBC85E80c8295a6147597cc8e9`](https://dora.privacy.ethrex.xyz/address/0x74533B2378568EfBC85E80c8295a6147597cc8e9) | [`0x1d08eded…`](https://dora.privacy.ethrex.xyz/tx/0x1d08ededcaeb9b7bcc2b220fc5cc81faa34f9c1a6b509dcd19956ccc1277ae2e) | 114,300 | 257,578 |

Frame tx gas is the EIP-7976 calldata floor (16 gas per token, every byte 4 tokens) plus 19,050 fixed (base 12,000,
475 per frame, 100 per ARBITRARY entry, 6,000 for the value transfer): about 21.4K + 64 gas per signature byte.
The VERIFY frame's execution (47–61K) stays far below that floor. Send one with
`script/send_frame_tx_leansphincs.py <rpc> <account> <signer> <key file> <recipient> <wei>` (a `.json` key file
from `signer-c13 keygen` selects the C13 signer). It uses the
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
