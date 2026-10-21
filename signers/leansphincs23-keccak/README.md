# leansphincs23-keccak

Rust signer for **leanSphincs-23 over keccak256**, the scheme the on-chain verifier
`legacy/src/LeanSphincs-23Asm.sol` checks. The spec is
[`legacy/docs/leanSphincs-23-keccak.md`](../../legacy/docs/leanSphincs-23-keccak.md).

**Legacy (verifier in `legacy/src`).** leanSphincs-23 is superseded by leanSphincs-s
([`signers/leansphincs-s-keccak`](../leansphincs-s-keccak)); this crate stays here, maintained, to keep the
legacy verifier's KAT fixture and Forge suites reproducible.

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

The crate adds the one-signer tiers (below): a pruned key generated once and stored with a bounded node cache, which
signs the same bytes as `sign(key_gen(seed, b), m)`.

Verification costs a constant **249 keccak256 calls** (`VERIFY_KECCAK_CALLS`).

## CLI

```sh
cargo build --release
./target/release/ls23k sign   <seed_hex64> <b> <msg_hex64>         # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)
./target/release/ls23k kat    <seed_hex64> <b> <msg_hex64>         # one JSON object (key, sig, idx, counter, randomizer, fors_indices)
./target/release/ls23k verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>   # true | false

# one-signer tiers (below): the key is generated once and stored in a key file
./target/release/ls23k keygen (--seed-file <path> | --seed-stdin) (--tier light|standard|full | --b N --cache-bytes N)
                              -o <keyfile> [--force] [--threads N]   # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot)
./target/release/ls23k sign-key <keyfile> <msg_hex64>              # what `sign` prints for the key's seed and b
./target/release/ls23k info     <keyfile>                          # one JSON object: tier, plan, key words, costs; no secret
```

`b` is the height of the kept subtree (pruned key). `b = 25` is a full key, which costs about 7.6·10⁹ keccak calls to
generate (`2^25 · 226`; upstream's 8.1·10⁹ for leanSphincs-23 counts BLAKE2s compressions). The verifier cannot tell a
pruned key from a full one. The key words are high-aligned, which is the form the verifier takes: `pkSeed = P ‖ 0^16`
and `pkRoot = root ‖ 0^16`. Each run of `sign` regenerates the kept subtree, `2^b · 226` keccak calls, which outweighs
the signature itself (about 155,000 calls) from about `b = 10` up. On 8 cores of a shared host, `sign` took about 35 ms
at `b = 10` and about 110 ms at `b = 13`.

`sign` and `kat` take the seed on the command line, where every local user can read it in the process list and the
shell history keeps it. They are for test vectors and the Forge FFI tests. A real key goes through `keygen` (below),
which reads the seed from a private file or from standard input. No `ls23k` error message repeats an argument's value.

## One-signer tiers

The tiers of sphincs-art's "One signer, leanSphincs-23" table (`src/tiers.rs`, `src/keyfile.rs`). The key is generated
once and stored in a key file with a node cache of bounded size. Each signature recomputes only what is not cached:

| Tier       | `b` (kept subtree) | Cache  | Plan             | Auth-path calls / sig | Keygen calls         |
|------------|-------------------:|-------:|------------------|----------------------:|---------------------:|
| `light`    | 13                 | 16 KiB | level 3 only     | 2,830                 | 1,851,416            |
| `standard` | 20                 | 1 MiB  | top levels 5..20 | 7,231                 | 236,978,186          |
| `full`     | 25 (whole tree)    | 16 MiB | top levels 6..25 | 14,463                | 7,583,301,632        |

Light is the page's Ledger Nano S+ class tier: its 16 KiB cache is the page's budget for such a device. The page's times
for it (60 s keygen, 4.7 s per signature) are BLAKE2s figures. A keccak256 call costs more than a BLAKE2s compression on
such a device, so they are optimistic here, and this crate is a host-side reference signer, not a device implementation.
Any `(b, cache_bytes)` also works. The keys, the randomizer grind (`ρ = R_0 + i`) and the WOTS+C counter are those of
`key_gen` and `sign`, so `sign_with_cache` gives the same bytes as `sign(&key_gen(seed, b).0, m)`. Only the source of
the auth path changes. The verifier, the spec and the fixtures are unaffected.

**Cache plan.** A budget of `cache_bytes` holds `⌊cache_bytes / 16⌋` nodes of the kept subtree (levels `0..=b`). The plan
is the one with the least `tree_cost` from sphincs-art's `sweep_leansphincs_pruned.py`, in keccak256 calls (a WOTS
leaf from the seed is 225 calls, a node is 1):

| Plan              | Cached nodes      | Auth-path calls per signature        |
|-------------------|-------------------|--------------------------------------|
| whole subtree     | `2^(b+1) − 1`     | 0                                    |
| top levels `c..b` | `2^(b−c+1) − 1`   | `2^c·225 + 2^c − 1`                  |
| level `c` only    | `2^(b−c)`         | `2^c·225 + 2^c − 1 + 2^(b−c) − 1`    |
| none              | 0                 | `2^b·225 + 2^b − 1`                  |

`2^c·225 + 2^c − 1` rebuilds the `2^c`-leaf bottom subtree that holds the signed leaf, and gives the path below level
`c`. The path's levels `c..b−1` come from the cache, or, with level `c` only, from the `2^(b−c) − 1` nodes above it. Its
levels `b..24` are the stored surrogates. The tie-break follows the sweep: candidates are tried in its order (none, then
for `c = 1..b`: top levels `c..b`, then level `c` only), and a candidate replaces the current best only if it is
strictly cheaper. The only ties are the kept subtree's root alone (top levels `b..b` or level `b`) against no cache,
and none wins them.

**What is checked.** Loading a key file checks every cached node (see "Key file" below for what that does and does not
prove). At signing, the recomputed bottom subtree is checked against the cached node at its root (with no cache, against
the kept subtree's root), and with `level c only` the rehashed levels above `c` are checked against the kept subtree's
root, at no extra hash. A `top levels` path reads its levels `c..b−1` straight from the cache, and a `whole subtree`
path reads everything from it. Last, `sign_with_cache` verifies the signature under the key's public key (249 calls,
reported apart from the signature's cost) and returns an error rather than a signature that does not verify. So a
corrupt key file is refused when it is loaded, a cache corrupted in memory afterwards is refused at signing wherever it
touches the signature, and a signature that `sign-key` prints always verifies under the key words it prints.

**Keygen** streams the kept subtree. It runs one stack-based treehash per chunk (about four chunks per thread), each
recording only the nodes the plan keeps, and then hashes the chunk roots together. It costs exactly `key_gen`'s
`2^b·226 + 2(25 − b)` keccak256 calls. sphincs-art's keygen figure, `1 + 2^b·226 + 2(25 − b)`, is one call higher: it
counts `2^b` nodes in a tree that has `2^b − 1`.

**Cost against the model.** Against `tier_model.py` (the sphincs-art model): keygen is one call under it, as above. The
auth path equals `tree_cost` exactly; with `level c only`, the rehash up to the kept subtree's root that the model
counts is the signer's cache check. A signature costs the model's mean plus 13 calls for `b < 25`, because the 13
opened FORS secrets are derived a second time. At `b = 25` it costs the model's mean plus 14: also one grind try and
the digest recomputed after it, where the model counts no grind. That gives means of 154,866 for Light, 155,203 for
Standard and 162,404 for Full. `sign-key` then spends 249 calls verifying the signature, and every run loads and
checks the key file: 1,048, 32,778 and 524,288 calls for Light, Standard and Full. The model counts neither.

**Memory.** `keygen_cached` holds the cache, the `2^t` chunk roots and a `b + 1`-node stack per thread. Writing the key
file streams it (header, surrogates, cache, then the checksum computed on the way), so `ls23k keygen` holds one copy of
the cache. Loading reads the cache straight into place and checks it without a second copy. The peak heap was
measured with a counting allocator at `b ≤ 13` (Light; `b = 13` with a 256 KiB whole-subtree cache; `b = 13`, top
levels 1..13, 128 KiB; `b = 12`, top levels 3..12):

- keygen plus the write: the cache plus 8.6–10.7 KB. The earlier in-memory serialization peaked at twice the cache.
- loading: the cache plus about 9 KB, plus the rows above level `c` (at most half the cache) for a `level c only` plan
  (Light: the cache plus 21 KB). The earlier loader held the file and the parsed cache together: 2.75 to 3.55 times
  the cache in these runs.
- signing: about 2.56 MB on top of the loaded key, whatever the cache (the 13 FORS trees and their leaves).

The process itself takes about 3 MB of RSS (Linux x86-64). By the same accounting (not run), Standard needs about
1 MiB of heap for keygen and about 3.6 MB for `sign-key`, and Full about 16 MiB and about 19.3 MB.

```sh
./target/release/ls23k keygen --seed-file seed.hex --tier light -o key.ls23k   # or --seed-stdin; --tier standard|full, or --b N --cache-bytes N
                                                                               # [--force] [--threads N]; prints 0x || abi.encode(pkSeed, pkRoot)
./target/release/ls23k sign-key key.ls23k <msg_hex64>                          # the same output as `ls23k sign <seed_hex64> <b> <msg_hex64>`
./target/release/ls23k info key.ls23k                                          # JSON: tier, b, s, plan, cache, key words, costs; no secret
pass show ls23k/seed | ./target/release/ls23k keygen --seed-stdin --tier standard -o standard.ls23k   # the seed from a password manager
```

`keygen` reads the seed from `--seed-file <path>` or from standard input (`--seed-stdin`, for a pipe from a password
manager or a wallet): 64 hex digits, `0x` optional, one trailing newline allowed. It refuses a seed file that group or
others can access, as ssh refuses such a private key, and it never takes the seed on the command line. `--threads` is
1 to 1,024; the default is the number of cores available.

`keygen` checks the output path before the keygen: a missing or read-only directory, or an existing file without
`--force`, fails at once. It writes the key file into a uniquely named temporary file beside it (mode `0600`), syncs
it, and publishes it. Without `--force` it publishes with a hard link, which never replaces an existing file. With
`--force` it renames the new file over the old one, which stays whole until then. Then it syncs the directory. Any
error removes the temporary file. A kill or a power loss in the middle can leave it behind: a hidden
`.<name>.<pid>.<n>.tmp`, mode `0600`, which holds the seed. The next `keygen` to that path warns about it. Nothing
partial is ever at the key file's path. Publishing without `--force` needs a filesystem with hard links.

`keygen` and `sign-key` print the keccak256 calls and the wall time on stderr, and `sign-key` reports its 249-call
verification apart from the signature. `sign-key` prints nothing on standard output when it fails. `sign-key` and
`info` warn when group or others can access the key file, or another user owns it. With `LS23K_RSS=1`, every command
also prints `VmHWM` at exit. That is a lower bound on the peak RSS: the kernel's high-water mark can miss a short-lived
peak.

### Operational rules

- **One seed, one key.** Never use a seed with two different `b`: two tiers, a tier and a custom `b`, or `keygen` and
  `ls23k sign` at another `b`. `P`, the WOTS and FORS keys and the real tree nodes depend only on the seed and the leaf
  index, not on `b`. Where two same-seed keys' kept subtrees overlap (always, against a full key; Light inside
  Standard for 1 seed in 32), a signature of one key becomes a valid signature of the other by swapping in path nodes
  that the other key's signatures and surrogates make public. No secret is needed, so the stronger key falls to the
  weaker one's lifetime. Use a fresh, independent seed for every key. `keygen` cannot detect reuse, and nothing in the
  scheme or the key derivation changes this.
- **The key file is the secret.** It holds the seed in the clear: keep it mode `0600` and back it up like a private key.
- **Check the key words.** A key file proves that its `P`, `s` and surrogates are its seed's, and that its cache, kept
  subtree root and root are consistent with each other. It does not prove that the root is the seed's: that would
  cost a keygen. Compare the `pkSeed` and `pkRoot` that `keygen`, `sign-key` and `info` print with the registered key.
- **Signing is deterministic.** The signer and the key file keep no count of signatures: staying under the tier's
  rated lifetime (Light 20,000) is the caller's job.

### Key file (version 1)

```text
offset         length          field
0              8               magic "LS23KKEY"
8              4               format version, u32 little endian: 1
12             1               tier: 0 custom, 1 light, 2 standard, 3 full
13             1               b, the kept subtree's height (0..=25)
14             1               cache plan: 0 none, 1 top levels c..b, 2 level c only, 3 whole subtree
15             1               c (0 for none and whole subtree)
16             8               s, u64 little endian: the kept subtree holds leaves s 2^b .. (s + 1) 2^b
24             8               cache budget in bytes, u64 little endian
32             16              P
48             16              root
64             16              the kept subtree's root (level b)
80             32              the seed S (secret)
112            16 (25 - b)     surrogates, levels b..24
112+16(25-b)   16 nodes        the cache: the plan's levels from the lowest, each level's nodes from the left
end - 32       32              keccak256 of every byte before it
```

A Light key file is 16,720 B, a Standard one 1,048,784 B, a Full one 16,777,344 B; no key file is longer than
1,073,741,952 B (a full key caching its whole tree). The seed is stored in the clear, so the file is only as safe as its
permissions. Loading fails closed with a specific error, in this order:

1. The path must be a regular file (it is checked before opening, so a FIFO or a device is not opened) no longer
   than any key file. It is read through a bound of the length it has when opened.
2. The magic, then the checksum, before any other header field is trusted: a corrupt header reads as a checksum
   mismatch.
3. The version, `b`, the plan and the exact length.
4. Bound to the seed: `P` must be the seed's, `s` the position `P` selects, and the surrogates the seed's.
5. Self-consistent: the plan must be the one the budget selects (and a preset tier must match `b` and the budget),
   every cached node must hash from its cached children, the cache's top level must hash up to the kept subtree's
   root, and that root must fold through the surrogates to the stored root.

That does not prove that the root, the kept subtree's root and the cache are the seed's: binding them would cost a
keygen. A file whose cache was edited consistently (some nodes changed, then every level above them, the kept subtree's
root and the root recomputed, and the file re-checksummed) loads, and `info` reports its root. The checksum is not a
MAC, but it covers the seed, so only someone who holds the seed, and so can sign anyway, can re-seal a file. Signing
re-checks what it recomputes and verifies every signature before `sign-key` prints it, so the signature always
verifies under the key words printed beside it. Compare those with the registered key.

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
- the tiers: the plan is the sweep's `tree_cost` for every `b ≤ 25` and every cache size at and around each threshold.
  For every `b` in 1..=12 and every cache plan, keygen costs exactly `key_gen`'s calls and reaches its key, and
  `sign_with_cache` gives `sign`'s bytes at `sign`'s cost plus exactly `tree_cost` for the path, then a 249-call
  verification. The tests also cover:
  - the streaming keygen on 1 to 100 threads, and absurd thread counts;
  - caches corrupted after loading failing the signature, and consistently re-sealed key files: a returned signature
    always verifies under the key's root;
  - a Light-tier end to end;
  - key files: round trips; every flipped bit of every byte, every truncation and extension rejected; a corrupt header
    read as a checksum mismatch; single-field re-checksummed edits caught; FIFOs, devices, directories and oversized
    files refused before reading; warnings on files others can access;
  - the writer: `0600`, refused overwrites, a write failing part way through leaving no file, the path checked before
    the keygen, concurrent writers;
  - the `keygen`/`sign-key`/`info` CLI against `sign`; the seed never repeated in an error, nor printed (`tests/cli.rs`
    runs `ls23k` as a process); a seed file others can access refused; `keygen` killed mid-write leaving nothing at the
    key file's path; `sign-key` printing nothing for a re-sealed key file.

  `cargo test --release -- --include-ignored` adds a Standard-tier end to end (two `b = 20` keygens).

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

`make_kat_fixture.py` writes `legacy/test/fixtures/leansphincs23-keccak-kat.json`: six `ls23k kat` vectors (b = 6, 10, 12;
messages all-zero, all-`0xff`, `0xdeadbeef` × 8 and a keccak-derived one), each confirmed by the Python `--verify`
(valid, and invalid for a one-bit message flip). Each vector also carries `above_target_counter`, the least counter
whose codeword sum exceeds `T = 128` for that signature's FORS key, which the Forge tests use to check the `Σ > T`
side of the target-sum check. `legacy/test/LeanSphincs23Test.t.sol` and `legacy/test/SphincsAccountLeanSphincs23Test.t.sol` read
it. The output is deterministic; `--check` fails if the committed file is stale. Like `crosscheck.py`, it refuses an
`ls23k` older than the crate sources, so `--no-build` cannot write a fixture the sources do not reproduce.

```sh
FOUNDRY_TEST=legacy/test forge test --match-contract LeanSphincs23 -vv   # legacy suites, from the repo root
```

The three Forge FFI tests sign with `ls23k`: `testVerifyFFI_Rust` and `testValidateUserOpFFI_Rust` with `sign`, and
`testVerifyFFI_RustLightTierKeyFile` with a key file. In one `sh -c`, that one runs a Light-tier `keygen --seed-stdin`
into a `mktemp -d` directory and `sign-key`, then removes the key file and the directory. The verifier must accept the
result, and it must equal `ls23k sign <seed> 13 <msg>` byte for byte. They fail if the binary is older than the crate
sources. If it is not built they are reported as skipped, except under CI (`CI` set), where they fail: the CI
`legacy-verifiers` job builds `ls23k` before the legacy `forge test`, and the `leansphincs23` job runs the cargo tests, the crosscheck,
`make_kat_fixture.py --check`, a Light-tier `keygen` + `sign-key` against `sign`, `tier_model.py --check` and
`--json`, and these Forge suites.
