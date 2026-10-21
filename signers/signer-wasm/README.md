# signer-wasm: C13 signer

Rust crate `sphincs-c13-signer` for the C13 scheme (`src/keccak/SPHINCs-C13Asm.sol`: WOTS+C / FORS+C,
h = 22, d = 2, a = 19, k = 7, w = 8, 3,688-byte signatures). `src/lib.rs` is the WASM signer with BIP-39/44 key
derivation; the CLI `signer-c13` is the fast path for the C13 Forge FFI tests:

```bash
cargo build --release --bin signer-c13
./target/release/signer-c13 keygen <seed_material_hex>                # JSON {seed, sk_seed, root}
./target/release/signer-c13 sign-with <seed> <sk_seed> <root> <msg>   # raw signature, hex
./target/release/signer-c13 sign <msg>                                # test vector: keys derived from <msg>
cargo test --release -- --ignored
```

`sign-with` takes the secret seed on the command line, so use it for test keys only. Overview of every signer:
[signers/README.md](../README.md).

## Deployments

Measured in October 2026; the full record of every deployment is in [docs/deployments.md](../../docs/deployments.md).

**Sepolia, verifier only.** Verifier [`0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2`](https://sepolia.etherscan.io/address/0xc6f4009D4a8220527b849670431Cbde5FeD8A5F2). This is the hardened verifier deployed on 2026-06-04; its code is identical to `main` apart from the compiler metadata hash (the source moved into `src/keccak/`). One standalone `verify` transaction with a
real signature: [`0x64793ac4…`](https://sepolia.etherscan.io/tx/0x64793ac48235ec1d77f4fb2bbb9f735a2f072a182c3ba69a75a447f88536afa6), **263,064 gas**.

**ethrex privacy testnet (chain 8141), full EIP-8141 frame transaction.** Verifier [`0x499b3FA08944317f9fc3F8C8307360E971A8D96C`](https://dora.privacy.ethrex.xyz/address/0x499b3FA08944317f9fc3F8C8307360E971A8D96C), the
shared frame module [`0xAA481E835ec1b82E528d6D36D432F9Af440B4295`](https://dora.privacy.ethrex.xyz/address/0xAA481E835ec1b82E528d6D36D432F9Af440B4295), and a `SphincsFrameAccount` [`0x74533B2378568EfBC85E80c8295a6147597cc8e9`](https://dora.privacy.ethrex.xyz/address/0x74533B2378568EfBC85E80c8295a6147597cc8e9) holding a fresh
key from `signer-c13 keygen <seed material>` (JSON). The frame tx [`0x1d08eded…`](https://dora.privacy.ethrex.xyz/tx/0x1d08ededcaeb9b7bcc2b220fc5cc81faa34f9c1a6b509dcd19956ccc1277ae2e) has a VERIFY frame, where the account checks its signature over
`compute_sig_hash(tx)` from an ARBITRARY signature entry and approves execution and payment, then a SENDER frame
sending 0.00001 ETH. The account pays its own gas: **257,578 gas** in total, of which the VERIFY frame is **114,300**.

Both transactions are priced by the calldata floor, about 64 gas per byte of the 3,688-byte signature: the verifier's
own execution (~107 K) stays below it. To send another frame tx:

```bash
python3 script/send_frame_tx_leansphincs.py https://rpc1.privacy.ethrex.xyz <account> signers/signer-wasm/target/release/signer-c13 <key.json> <recipient> <wei>
```

It dry-runs the tx with `ethrex_simulateFrameTransaction` before sending. The key files of the deployed accounts are
not in the repository.
