# Post-quantum owners for an unmodified Safe on EIP-8141

**Research code. Not audited. Do not use it to hold funds.**

This prototype lets a Safe use leanSphincs-f keys as owners on a chain with EIP-8141 frame transactions. The Safe
contracts are not changed and neither is the EIP. It was checked against Safe v1.4.1, v1.5.0 and `main` at `247b8ce`,
and against the EIP-8141 text of ethereum/EIPs master `dc5d5fa688b7` (2026-11-01). EIP-8141 is a draft: re-check
this document against the text a chain implements.

Nothing here has run on a live network. The numbers below come from Forge (revm) and from the EIP-8141 emulator in
`test/py/frame8141_emu.py`.

## Design

Each Safe owner is a small contract, the **owner account** (`src/SphincsOwnerAccount.sol`), that holds one
leanSphincs-f public key. A Safe transaction is one frame transaction, sent by one of the owners from their own
owner account:

```
tx.sender  = the sender's owner account
frame[0]   = VERIFY, flags 0x3 (self_verify), target = tx.sender
             data = verifyFrameAndApprove(uint256 0)
frame[1]   = SENDER, target = the Safe
             data = execTransaction(to, value, data, operation, safeTxGas, baseGas, gasPrice,
                                    gasToken, refundReceiver, signatures)
signatures = [ARBITRARY, empty signer, empty msg, the sender's leanSphincs-f signature]
```

1. **VERIFY frame.** The owner account checks one signature: the sender's, over `compute_sig_hash(tx)`. It then
   approves execution and payment, so the sender's owner account pays for the transaction.
2. **SENDER frame.** The protocol calls the Safe with `msg.sender` equal to the sender's owner account.
3. **Inside `execTransaction`.** The Safe counts the sender as a pre-validated signature (`v = 1`, accepted because
   the owner is `msg.sender`). It checks every co-signer as a contract signature (`v = 0`) by calling
   `isValidSignature` on that co-signer's owner account, which runs the leanSphincs-f verifier.

### Why this shape

The public mempool allows a validation prefix at most `MAX_VERIFY_GAS = 100,000`: the sum of `limits.execution` over
the prefix, plus 100 for each `ARBITRARY` signature entry. One leanSphincs-f verification costs about 51K in a VERIFY
frame. A Safe that verified every owner in the prefix would stop at one signer. Here only the sender is verified in
the prefix, and the co-signers are verified in the SENDER frame, which the mempool does not simulate.

`[self_verify]` is one of the four validation prefixes the public mempool recognizes, and no VERIFY frame follows it.

### The owner account

`SphincsOwnerAccount` has four immutables (`pkSeed`, `pkRoot`, `verifier`, `frameModule`) and these functions:

| Function | Purpose |
|---|---|
| `verifyFrameAndApprove()`, `verifyFrameAndApprove(uint256 sigIndex)` | VERIFY-frame entry points. They DELEGATECALL the existing `src/SphincsFrameVerify.yul` module, unchanged. |
| `isValidSignature(bytes32 hash, bytes signature)` | Returns `0x1626ba7e` when the signature is valid over `hash`. Safe 1.5.0 and later call this form. |
| `isValidSignature(bytes data, bytes signature)` | Returns `0x20c13b0b` when the signature is valid over `keccak256(data)`. Safe up to 1.4.1 calls this form. |
| `receive()` | Accepts ETH. |

There is no `execute`, no owner field and no `verifyAndApprove`. The constructor makes the same checks as
`SphincsFrameAccount`: canonical key words, a verifier with code, and a module that is either zero or has code.

Three properties follow from that surface and are worth knowing before using it:

- **SENDER frames act as the account without entering its code.** After the VERIFY frame approves, every SENDER
  frame of the transaction runs with the account as caller. The key therefore controls the account fully through
  frame transactions. ETH held by the account is spent with a SENDER frame that carries a value
  (`test_Sweep_ValueLeavesThroughASenderFrame`).
- **A module address of zero gives a co-signer-only account.** It answers `isValidSignature` and can never send a
  frame transaction. ETH sent to such an account cannot be moved.
- **One key, one owner account.** The Safe transaction hash does not name the co-signer's account. If two owner
  accounts of the same Safe held the same key, one signature would count for both.

### What each Safe version does

| | v1.4.1 | v1.5.0 | main (`247b8ce`) |
|---|---|---|---|
| Contract signature call | `isValidSignature(bytes data, bytes sig)` with the EIP-712 pre-image, expects `0x20c13b0b` | `isValidSignature(bytes32 hash, bytes sig)`, expects `0x1626ba7e` | the same, and the call must succeed with exactly 32 bytes |
| Pre-validated entry (`v = 1`) | accepted when the owner is `msg.sender`; `s` is not read | the same | a non-zero `s` must equal the Safe transaction hash |
| Refund (`gasPrice > 0`) | `send` (2,300 gas) to `refundReceiver`, or to `tx.origin` when it is zero | `call` | `call` |

The tooling sets `s` to the Safe transaction hash in the sender's entry, which is valid on all three.

Signatures are sorted by owner address, ascending. A contract signature is `{owner}{offset}{0x00}` in the static part
and `{length}{bytes}` in the dynamic part. In a SENDER frame `ORIGIN` is the frame's caller, so a refund with no
receiver goes to the sender's owner account, which is the account that paid for the frame transaction. Its
`receive()` uses 67 gas.

## Security invariants

Every invariant has at least one test that fails when it is broken. Test files: `SphincsOwnerAccountTest`
(unit), `SafePqOwnersTest` (Safe integration) and `SafePqOwnersFrameTest` (end to end). The last two run once per
Safe version.

| # | Invariant | Tests |
|---|---|---|
| 1 | The VERIFY path accepts only an `ARBITRARY` entry with empty `msg` and verifies it over `TXPARAM(0x08)`. | `test_Verify_RejectsAnEntryWithAnExplicitMsg`, `test_Verify_UsesTheCanonicalHash`, `test_Verify_SenderFrame`, `test_VerifyFrame_ForwardsOnlyKeysAndIndex`, `test_FrameModule_VerifiesOnlyTheCanonicalHash` |
| 2 | No function verifies a caller-supplied digest and then approves or makes a call. | `test_Surface_IsExactlyTheSpecifiedFunctions`, `test_Code_HasNoCallAndNoFrameOpcode`, `test_VerifyFrame_ForwardsOnlyKeysAndIndex`, `test_Verify_RejectsAnEntryWithAnExplicitMsg` |
| 3 | The account makes no state-changing call of its own. Key, verifier and module cannot change. | `test_Code_CannotWriteStateOrCallOut`, `test_NoEntryPointTouchesStorage`, `test_Surface_IsExactlyTheSpecifiedFunctions` |
| 4 | `isValidSignature` is a pure check. It is valid only when the verifier call succeeds and returns exactly 32 bytes equal to 1, and returns `0xffffffff` otherwise. It reads no storage, uses no frame opcode and ignores `msg.sender` and `tx.origin`. | `test_IsValidSignature_RequiresExactlyOneWordEqualToOne`, `test_IsValidSignature_RejectsWithoutReverting`, `test_IsValidSignature_NeverValidWhenOutOfGas`, `test_IsValidSignature_IgnoresCallerAndOrigin`, `test_Code_IsValidSignatureIsAPureCheck`, `test_NoEntryPointTouchesStorage` |
| 5 | A frame witness is not accepted as a Safe co-signature, and a Safe co-signature is not accepted as a frame witness. | `test_FrameWitnessIsNotACoSignature`, `test_CoSignatureIsNotAFrameWitness` |
| 6 | A co-signature for one Safe, chain or nonce is not accepted for another. | `test_CoSignature_BoundToSafe`, `test_CoSignature_BoundToChain`, `test_CoSignature_BoundToNonce` |

Invariants 2, 3 and 4 are partly checked on the deployed bytecode. The tests disassemble the account and require:
no SLOAD, SSTORE, TLOAD, TSTORE, CALL, CALLCODE, CREATE, CREATE2, SELFDESTRUCT, LOG or ORIGIN; no EIP-8141 opcode;
no opcode banned in a validation prefix; exactly one STATICCALL; DELEGATECALL only to the module; and GAS only
directly before a call.

### Invariant 5 holds between the two hashes, not inside the account

The account verifies exactly the hash the Safe passes. That is required for compatibility with unmodified Safes, and
it means the account cannot tell the two kinds of digest apart: `isValidSignature(sigHash, witness)` returns the
magic value, because the key did sign `sigHash`.

What separates them is the pre-image. A frame signature hash is `keccak256(0x06 ‖ rlp(...))`. A Safe transaction hash
is `keccak256(0x19 0x01 ‖ domainSeparator ‖ structHash)`. One can stand for the other only through a keccak256
collision. The tests show both directions on real signatures: the Safe rejects a real witness presented as a
co-signature (`GS024`), and the VERIFY frame rejects a real co-signature presented as the witness.

The tooling adds a second barrier. `cosign` signs only the Safe transaction hash it computed from a Safe transaction
file, and `frame-tx` signs only the signature hash of the transaction it assembled. Neither takes a digest from the
command line.

## Things that are true and easy to miss

- **A failed SENDER frame still costs the sender.** Payment is approved in the VERIFY frame. If `execTransaction`
  then reverts, for example because another Safe transaction took the nonce first, the frame transaction is valid
  and the sender pays for it. That is about 648K gas for a 2-signer transaction.
- **Before Safe main, only the co-signatures pin the Safe nonce.** The sender's approval covers the SENDER frame's
  data, which does not contain the Safe nonce, and Safe up to 1.5.0 does not read `s` in the `v = 1` entry. With at
  least one co-signer the transaction is still pinned, because every co-signature is over the Safe transaction hash.
  A threshold-1 Safe at v1.5.0 or earlier executes the sender's call at whatever its nonce is at inclusion. The
  frame transaction's own nonce still makes it execute at most once.
- **Each signature spends from the key's lifetime.** Frame witnesses and co-signatures come from the same key. The
  leanSphincs-f lifetimes in `docs/leanSphincs-f-keccak.md` apply to their total.
- **The Safe's refund is a lower bound.** The Safe refunds at `min(gasPrice, tx.gasprice)`. Under EIP-8141,
  `GASPRICE` is a lower bound on the price the payer pays.

## Gas

Measured with forge 1.5.1 and solc 0.8.33 (via-IR) for this repo's contracts, and with solc 0.7.6 without the
optimizer for the Safe, which is upstream's default build.

| Quantity | Estimate | Measured |
|---|---|---|
| VERIFY frame gas for the sender | about 51,948 | **51,069** and **51,079** on the two fixture transactions |
| One `isValidSignature` call | | **45,665** in its own call frame with the verifier warm, **48,165** with it cold |
| Total gas, 2 signers (sender and 1 co-signer) | about 648K | **647,674** |
| Total gas, 3 signers (sender and 2 co-signers) | about 952K | **952,826** |
| One contract signature for the Safe Transaction Service | 4,757 bytes | **4,757 bytes** (65 + 32 + 4,660) |

### VERIFY frame

The frame's gas is the verifier's own call frame plus a fixed 7,068. The fixed part is the frame's entry charge
(100, because `tx.sender` starts warm), the account's dispatch, two cold account accesses (module and verifier,
2,600 each) and the copy of the 4,660-byte witness. The verifier's frame is 43,479 to 44,546 for any admissible
leanSphincs-f signature (`LeanSphincsFTest`), so the VERIFY frame is **50,547 to 51,614**.

The frame needs a higher limit than it uses, because of the 63/64 rule at two call depths. The measured minimum is
1,329 above the gas used (52,398 for a frame that uses 51,069). The tooling declares `limits.execution = 60,000`, so
the validation prefix declares **60,100** of the 100,000 allowed. The existing
`script/send_frame_tx_leansphincs.py` declares 300,000, which the public mempool would reject; it was not changed.

The estimate of 51,948 is the VERIFY frame of the 2026-10-20 testnet transaction of a `SphincsFrameAccount`. The
figure measured here is about 870 lower. Up to about 500 of that can come from the signature, since the verifier's
gas depends on it. The rest is not explained: it would take replaying that transaction's witness in the emulator,
which needs a read from the testnet.

### `isValidSignature`

The call frame costs the verifier's frame plus 1,664 (dispatch, the copy of the signature and a warm STATICCALL):
45,641 to 45,797 on the KAT fixture. A cold verifier adds 2,500. The Safe also pays 2,600 for the co-signer's cold
account and its own handling of the signature bytes. In `execTransaction`, one more co-signer costs:

| Safe | First co-signer | Second co-signer |
|---|---|---|
| v1.4.1 | 73,146 | 61,493 |
| v1.5.0 | 72,146 | 60,579 |
| main | 86,491 | 74,861 |

The first co-signer of a plain Safe call pays the cold verifier. In a frame transaction the VERIFY frame has already
warmed it.

### Whole transaction

The gas a frame transaction pays is `max(execution component, calldata floor)` plus state gas. For these
transactions the calldata floor wins by a wide margin, so the total is set by the bytes alone:

```
calldata floor = 12,000 + 475 × frames + 100 × ARBITRARY entries + 64 × bytes
bytes          = frame data + signature entries
```

| | 2 signers | 3 signers |
|---|---|---|
| Witness (signature entry) | 4,660 B | 4,660 B |
| VERIFY frame data | 36 B | 36 B |
| SENDER frame data (`execTransaction`) | 5,220 B | 9,988 B |
| Raw transaction | 10,043 B | 14,811 B |
| **Calldata floor = gas used** | **647,674** | **952,826** |
| Intrinsic gas | 164,986 | 239,846 |
| VERIFY frame | 51,069 | 51,079 |
| SENDER frame, Safe v1.4.1 / v1.5.0 / main | 89,199 / 87,660 / 101,779 | 153,353 / 150,784 / 179,355 |
| Execution component, at most | 317,834 | 470,280 |

Each further co-signer adds 4,768 bytes to the SENDER frame data, which is 305,152 gas.

The Safe transaction in these figures is a 1,000 wei transfer to an existing account, from a Safe that has executed
before. State gas (EIP-8037) is then zero. A Safe's first transaction creates its nonce slot and adds 97,920 state
gas, and a payment to a new account adds 183,600. The frame's `limits.state` must cover them (`--state-gas`).

The SENDER frame figures are revm's, under today's gas schedule, plus the 2,600 entry charge for the cold Safe. A
chain with EIP-8141 also has EIP-8037 and EIP-2780, which price storage writes differently. This does not move the
total while the transaction stays floor-bound.

## Tooling

`script/safe_pq_owners.py` works offline and needs only the standard library and the `lsfk` binary. It does not
talk to a node, and nothing in this prototype was sent to a network.

```bash
(cd signers/leansphincs-f-keccak && cargo build --release)

python3 script/safe_pq_owners.py hash safe-tx.json                       # Safe transaction hash and pre-image
python3 script/safe_pq_owners.py cosign safe-tx.json --owner 0x<co-signer account> \
        --key-file cosigner.lsfk -o cosig.json                           # one co-signature (4,757 B for the service)
python3 script/safe_pq_owners.py signatures safe-tx.json --sender 0x<sender account> cosig.json
python3 script/safe_pq_owners.py frame-tx safe-tx.json --sender 0x<sender account> --account-nonce 0 \
        --base-fee 1000000000 --key-file sender.lsfk cosig.json -o tx.json   # the signed frame transaction
python3 script/safe_pq_owners.py selftest
```

`frame-tx` refuses to assemble a transaction that breaks the public mempool's structural rules, such as a prefix
over 100,000 gas. `--wire eip` (the default) encodes the transaction as the current EIP text defines it.
`--wire ethrex` emits the wire format of the ethrex testnet, as `script/send_frame_tx_leansphincs.py` does; that
path is checked against ethrex's golden vector but has not been run against a node.

## Tests

```bash
forge build                                                          # required first, see below
(cd signers/leansphincs-f-keccak && cargo build --release)           # lsfk, for the FFI signatures
forge test --match-contract '^SphincsOwnerAccountTest$' -vv          # 18 tests
forge test --match-contract '^SafePqOwners(141|150|Main)Test$' -vv   # 55 tests, real signatures over FFI
forge test --match-contract '^SafePqOwnersFrame(141|150|Main)Test$' -vv   # 33 tests, emulator over FFI
python3 -I test/py/gen_safe_pq_fixture.py --check                    # the fixture still reproduces
```

The Safe sources are three submodules under `lib/`, pinned to v1.4.1, v1.5.0 and `247b8ce`. They are compiled with
solc 0.7.6 under a separate compiler profile (`foundry.toml`), because Safe 1.4.1 does not compile under via-IR.

Run `forge build` before a filtered `forge test`. The tests load the Safe and the Yul module from their build
artifacts instead of importing them, and a `forge test --match-contract ...` run compiles only the files its tests
import. Without the build the Safe suites fail in `setUp` with "no artifact ... run `forge build` first". An
unfiltered `forge test` compiles everything.
The integration tests cover a 2-of-3 and a 3-of-5 Safe: the happy path with the sender as `msg.sender` in every
position, a bad co-signature, a co-signer that is not an owner, a duplicate owner, a shifted Safe nonce, and the
refund to the sender.

### How the end-to-end test runs a frame transaction

Forge has no EIP-8141, so a transaction is run in two halves.

- **The VERIFY frame runs in the emulator.** The real deployed code of the owner account, the module and the
  verifier is executed in a metered EVM that implements the EIP-8141 opcodes. The verifier call it made is replayed
  in revm and must return the same data for the same gas.
- **The SENDER frame runs in Forge**, and only if the VERIFY frame approved. It is a call to the frame's target with
  the frame's data and value, with `msg.sender` and `tx.origin` both set to the sender. The target is the real Safe.

The fixture `test/fixtures/safe_pq_owners_frame.json` is built by the tooling above. The Safe proxies are placed at
the fixture's addresses by copying the code of a proxy the real factory created and calling `setup` on it.

### What changed in the emulator

`test/py/frame8141_emu.py` could run only the module, with the verifier's answer supplied by the caller, and had no
gas accounting. The existing commands and the existing fixture are unchanged. Added:

- **Spec revisions.** A fixture names its EIP revision. Under `dc5d5fa688b7` the signature hash commits to the
  length of each elided signature, `fees` is `[max_fee, max_priority_fee_per_gas]`, a frame's target access is
  charged at frame entry and SENDER frames may carry a value.
- **A metered EVM for a whole VERIFY frame** (`exec`): computation, memory, KECCAK256, STATICCALL, DELEGATECALL and
  the EIP-8141 opcodes, with gas. It has no storage, value transfer, log or contract creation; those opcodes halt.
  It also reports a GAS that is not directly before a call and a call to an address without code.
- **A plain metered call** (`call`), so the Forge tests can compare the emulator with revm. Gas and return data
  match exactly for the verifier (accept, reject, revert) and for `isValidSignature` with the verifier warm and cold.
- **The public mempool's structural rules** (`mempool`) and **the Gas Accounting formulas** (`gas`).

## Not tested

- **No live network.** Nothing was sent to the ethrex testnet or anywhere else, and `--wire ethrex` was not run
  against a node.
- **The SENDER frame is not run under EIP-8141 rules.** It runs in revm with `msg.sender` and `tx.origin` set by
  hand. `APPROVE`'s effects on nonce and balance, fee settlement, state gas and the receipt are not modelled.
- **The mempool's trace rules are checked only as far as the emulator goes.** It halts on storage access and banned
  opcodes and reports the two violations listed above. It is not a mempool implementation.
- **The Safe Transaction Service** was not used. Its 5,000 limit was read from its source
  (`SIGNATURE_LENGTH = 5_000`), not tested against the service.
- **Guards, modules and fallback handlers** of the Safe are not exercised.
- **The Ledger signer** is out of scope.
