# leansphincs23-keccak

Rust signer for **leanSphincs-23 over keccak256**, the scheme the on-chain verifier
`src/keccak/LeanSphincs-23Asm.sol` checks. The spec is
[`docs/leanSphincs-23-keccak.md`](../../docs/leanSphincs-23-keccak.md).

It is a port of Tom Wambsgans' upstream leanSphincs crate
([leanXMSS-leanSPHINCS-candidates](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates), `crates/sphincs`,
MIT OR Apache-2.0, see `LICENSE.upstream`). The module layout and names are the same as upstream. Diffed against
upstream, the changes are:

- the parameters: `h = 25`, `a = 12`, `k = 13`, `T = 128`. The signature is 4,148 B and the public key 32 B.
- the hash: Ethereum keccak256 (`0x01` padding) via `tiny-keccak` instead of BLAKE2s. The BLAKE2s midstate is
  gone, and a thread-local keccak-call counter replaces the compression counter. `Th` keeps the first 16 output bytes.
- the FORS position bound: `j < 2^12`.
- the message digest: one call over `P | address(MSG) | m | ρ` (80 B). The leaf index is in word 3, and the FORS indices
  are five per 64-bit word in words 0–2 (spec §5).
- multithreading: keygen spreads the kept subtree's leaves over all cores, and signing builds the 13 FORS trees in
  parallel.

Verification costs a constant **249 keccak256 calls** (`VERIFY_KECCAK_CALLS`).

## CLI

```sh
cargo build --release
./target/release/ls23k sign   <seed_hex64> <b> <msg_hex64>         # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)
./target/release/ls23k kat    <seed_hex64> <b> <msg_hex64>         # one JSON object (key, sig, idx, counter, randomizer, fors_indices)
./target/release/ls23k verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>   # true | false
```

`b` is the height of the kept subtree (pruned key). `b = 25` is a full key, which costs about 7.6·10⁹ keccak calls to
generate (`2^25 · 226`; upstream's 8.1·10⁹ for leanSphincs-23 counts BLAKE2s compressions). The verifier cannot tell a
pruned key from a full one. The key words are high-aligned, which is the form the verifier takes: `pkSeed = P ‖ 0^16`
and `pkRoot = root ‖ 0^16`. Each run of `sign` regenerates the kept subtree. On a 32-thread machine, `sign` at `b = 10`
takes about 35 ms and at `b = 18` about 2.6 s.

## Tests

```sh
cargo test --release
```

The tests check:

- the address and digest layouts
- the exact keygen and verify keccak-call counts, and the full-key keygen figure (`2^25 · 226`)
- tampering with every signature field
- a known-answer vector for `key_gen(seed(1), 11)`
- the WOTS+C mean number of encoding tries, about 14,670

## Cross-check against the Python signer

```sh
# from the repo root; needs pycryptodome (the repo venv has it)
.venv/bin/python signers/leansphincs23-keccak/crosscheck.py [--jobs N] [--no-build] [--b 8 10 ...]
```

`crosscheck.py` runs `ls23k kat` and the independent `script/leansphincs23_signer.py --json` on 16 vectors (b from 4
to 11; seeds and messages including all-zero and all-`0xff`), and requires every field to match byte for byte. It
also verifies each side's signature with the other side's verifier, recomputes the digest, the randomizer (`ρ = R_0 + i`
with `i < 2^40`, and minimal up to `2^22`), the counter minimality and the root from the spec in a third
implementation, and checks that `ls23k sign` matches the Python ABI output and that both verifiers give the contract's
revert reasons. Negative controls check that the randomizer check fails for an `R_0` derived any other way: `R_0` is
used only by the signers, so nothing else would notice a derivation bug they share. It takes about 45 s with 4 jobs
and exits nonzero on any difference. It refuses an `ls23k` older than the crate sources, even with `--no-build`.

## KAT fixture for the Forge tests

```sh
.venv/bin/python signers/leansphincs23-keccak/make_kat_fixture.py [--check] [--no-build]
```

`make_kat_fixture.py` writes `test/fixtures/leansphincs23-keccak-kat.json`: six `ls23k kat` vectors (b = 6, 10, 12;
messages all-zero, all-`0xff`, `0xdeadbeef` × 8 and a keccak-derived one), each confirmed by the Python `--verify`
(valid, and invalid for a one-bit message flip). Each vector also carries `above_target_counter`, the least counter
whose codeword sum exceeds `T = 128` for that signature's FORS key, which the Forge tests use to check the `Σ > T`
side of the target-sum check. `test/LeanSphincs23Test.t.sol` and `test/SphincsAccountLeanSphincs23Test.t.sol` read
it. The output is deterministic; `--check` fails if the committed file is stale. Like `crosscheck.py`, it refuses an
`ls23k` older than the crate sources, so `--no-build` cannot write a fixture the sources do not reproduce.

```sh
forge test --match-contract LeanSphincs23Test -vv
```

The two Forge FFI tests (`testVerifyFFI_Rust`, `testValidateUserOpFFI_Rust`) sign with `ls23k`. They fail if the
binary is older than the crate sources. If it is not built they are reported as skipped, except under CI (`CI` set),
where they fail: the CI `solidity` job builds `ls23k` before `forge test`, and the `leansphincs23` job runs the cargo
tests, the crosscheck, `make_kat_fixture.py --check` and these Forge suites.
