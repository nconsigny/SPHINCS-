# leansphincs-s-keccak

Rust signer for **leanSphincs-S over keccak256**, the scheme the on-chain verifier
`src/keccak/LeanSphincs-SAsm.sol` checks. The spec is
[`docs/leanSphincs-S-keccak.md`](../../docs/leanSphincs-S-keccak.md).

It is a port of Tom Wambsgans' upstream leanSphincs crate on its **`keccak` branch**
([leanXMSS-leanSPHINCS-candidates](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates), `crates/sphincs`
on branch `keccak`, MIT OR Apache-2.0, see `LICENSE.upstream`), by way of this repo's leanSphincs-23 signer
(`signers/leansphincs23-keccak`), whose tiers, key file and CLI it keeps. The module layout and names are upstream's.
Diffed against the upstream keccak branch, the changes are:

- the parameters: `h = 26` as upstream, `a = 12`, `k = 13`, `T = 128` (upstream: `a = 10`, `k = 24`, `T = 120`). The
  signature is 4,164 B and the public key 32 B.
- the hash: Ethereum keccak256 (`0x01` padding) via `tiny-keccak`, where upstream has its own Keccak-256 crate. A
  thread-local keccak-call counter sits next to upstream's Keccak-f permutation counter, and both are aggregated across
  worker threads. A call over `L` input bytes is `⌊L/136⌋ + 1` permutations; a `Midstate` counts its whole blocks once,
  and each `finish` is one call and pays for the rest. `Th` keeps the first 16 output bytes.
- the FORS position bound: `j < 2^12`.
- the message digest: one call over `P | address(MSG) | m | ρ` (80 B). The leaf index is `word_3 & (2^26 − 1)`, and
  the FORS indices are five per 64-bit word in words 0–2 (spec §5). Upstream's two-call layout is specific to `a = 10`.
- multithreading: keygen spreads the kept subtree's leaves over all cores, and signing builds the 13 FORS trees in
  parallel.

The encoding is upstream's, unchanged: there is no FORS key hash (tweak type 11 is unused), and the WOTS+C encoding of
the one-time key at `e` is `Th(P, address(ENC, 0, 0, e), tops ‖ LE32(c))` over the 26 FORS tops (`ForsTops`,
`encoding_midstate`, `encode_from`, `encode`, `wots_encode`, `wots_sign`, `wots_recover`, `fors_recover`). The 452-byte
input is 4 permutations for the verifier; the signer absorbs its 3 whole blocks once and pays one permutation per
counter.

Against leanSphincs-23 (`signers/leansphincs23-keccak`), leanSphincs-S has one more tree level and the merged encoding;
everything else (tweak, `P`, secrets, digest layout, FORS positions, serialization, surrogates, randomizer grind) is
the same. Its public key at `key_gen(seed(1), 11)` is the one upstream's `known_answer` pins, since at `h = 26` the key
depends on neither the FORS parameters, nor `T`, nor the encoding. **Never use one seed for both schemes**: they derive
the same one-time keys, and each would sign a different encoding with them (spec §9).

The crate adds the one-signer tiers (below): a pruned key generated once and stored with a bounded node cache, which
signs the same bytes as `sign(key_gen(seed, b), m)`.

Verification costs a constant **249 keccak256 calls**, or **259 Keccak-f permutations** (`VERIFY_KECCAK_CALLS`,
`VERIFY_PERMUTATIONS`): digest 1, FORS 13·(1 + 11), encoding 1 call of 4 permutations, chains 64, leaf 1 call of 8,
path 26. An inadmissible counter stops it after 158 calls (161 permutations).

## CLI

```sh
cargo build --release
./target/release/lssk sign   <seed_hex64> <b> <msg_hex64>         # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)
./target/release/lssk kat    <seed_hex64> <b> <msg_hex64>         # one JSON object (key, sig, idx, counter, randomizer, fors_indices)
./target/release/lssk verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>   # true | false

# one-signer tiers (below): the key is generated once and stored in a key file
./target/release/lssk keygen (--seed-file <path> | --seed-stdin) (--tier light|standard|full | --b N --cache-bytes N)
                             -o <keyfile> [--force] [--threads N]   # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot)
./target/release/lssk sign-key <keyfile> <msg_hex64>              # what `sign` prints for the key's seed and b
./target/release/lssk info     <keyfile>                          # one JSON object: tier, plan, key words, costs; no secret
```

`b` is the height of the kept subtree (pruned key). `b = 26` is a full key, which costs about 1.52·10¹⁰ keccak calls
(`2^26 · 226`), or 1.56·10¹⁰ Keccak-f permutations (`2^26 · 233`, sphincs-art's 15.6B), to generate. The verifier
cannot tell a pruned key from a full one. The key words are high-aligned, which is the form the verifier takes:
`pkSeed = P ‖ 0^16` and `pkRoot = root ‖ 0^16`. Each run of `sign` regenerates the kept subtree, `2^b · 226` keccak
calls, and grinds about `2^(26 − b)` randomizers. On 8 cores of a shared host, `sign` took about 80 ms at `b = 10` and
about 190 ms at `b = 13`.

`sign` and `kat` take the seed on the command line, where every local user can read it in the process list and the
shell history keeps it. They are for test vectors and the Forge FFI tests. A real key goes through `keygen` (below),
which reads the seed from a private file or from standard input. No `lssk` error message repeats an argument's value.

## One-signer tiers

The tiers of sphincs-art's "One signer, leanSphincs-S" table, FORS variant (`src/tiers.rs`, `src/keyfile.rs`). The key
is generated once and stored in a key file with a node cache of bounded size. Each signature recomputes only what is not
cached:

| Tier       | `b` (kept subtree) | Cache  | Plan             | Auth path / sig: calls | permutations | Keygen calls   | Keygen permutations |
|------------|-------------------:|-------:|------------------|-----------------------:|-------------:|---------------:|--------------------:|
| `light`    | 13                 | 16 KiB | level 3 only     | 2,830                  | 2,886        | 1,851,418      | 1,908,762           |
| `standard` | 20                 | 1 MiB  | top levels 5..20 | 7,231                  | 7,455        | 236,978,188    | 244,318,220         |
| `full`     | 26 (whole tree)    | 16 MiB | top levels 7..26 | 28,927                 | 29,823       | 15,166,603,264 | 15,636,365,312      |

The page's Keccak figures for these tiers are keygen 1.91M / 244M / 15.6B permutations and signing 159K / 155K / 178K
permutations, which `tier_model.py` reproduces exactly (it transcribes sphincs-art's `scripts/keccak_model.py`; below).
Light is the page's Ledger Nano S+ class tier: its 16 KiB cache is the page's budget for such a device, and the page
estimates 5.5 min to generate it and 27 s per signature at 5.8K permutations per second. This crate is a host-side
reference signer, not a device implementation. Any `(b, cache_bytes)` also works. The keys, the randomizer grind
(`ρ = R_0 + i`) and the WOTS+C counter are those of `key_gen` and `sign`, so `sign_with_cache` gives the same bytes as
`sign(&key_gen(seed, b).0, m)`. Only the source of the auth path changes. The verifier, the spec and the fixtures are
unaffected.

**Cache plan.** A budget of `cache_bytes` holds `⌊cache_bytes / 16⌋` nodes of the kept subtree (levels `0..=b`). The plan
is the one with the least `tree_cost` from sphincs-art's `sweep_leansphincs_pruned.py`, in keccak256 calls (a WOTS
leaf from the seed is 225 calls, a node is 1):

| Plan              | Cached nodes      | Auth-path calls per signature        |
|-------------------|-------------------|--------------------------------------|
| whole subtree     | `2^(b+1) − 1`     | 0                                    |
| top levels `c..b` | `2^(b−c+1) − 1`   | `2^c·225 + 2^c − 1`                  |
| level `c` only    | `2^(b−c)`         | `2^c·225 + 2^c − 1 + 2^(b−c) − 1`    |
| none              | 0                 | `2^b·225 + 2^b − 1`                  |

In permutations the WOTS leaf is 232 (its 1,056-byte input takes 8), which is how `keccak_model.py` calls
`tree_cost`; the plan is the same for every `b` and budget either way (the only comparison the leaf's cost decides is
`top levels c + 1..b` against `level c only`, and it would take a power of two in `226..=233` to flip it). The tests
check both counts against the sweep at every threshold. `2^c·225 + 2^c − 1` rebuilds the `2^c`-leaf bottom subtree
that holds the signed leaf, and gives the path below level `c`. The path's levels `c..b−1` come from the cache, or,
with level `c` only, from the `2^(b−c) − 1` nodes above it. Its levels `b..25` are the stored surrogates. The
tie-break follows the sweep: candidates are tried in its order (none, then for `c = 1..b`: top levels `c..b`, then
level `c` only), and a candidate replaces the current best only if it is strictly cheaper. The only ties are the kept
subtree's root alone (top levels `b..b` or level `b`) against no cache, and none wins them.

**What is checked.** Loading a key file checks every cached node (see "Key file" below for what that does and does not
prove). At signing, the recomputed bottom subtree is checked against the cached node at its root (with no cache, against
the kept subtree's root), and with `level c only` the rehashed levels above `c` are checked against the kept subtree's
root, at no extra hash. A `top levels` path reads its levels `c..b−1` straight from the cache, and a `whole subtree`
path reads everything from it. Last, `sign_with_cache` verifies the signature under the key's public key (249 calls,
259 permutations, reported apart from the signature's cost) and returns an error rather than a signature that does not
verify. So a corrupt key file is refused when it is loaded, a cache corrupted in memory afterwards is refused at signing
wherever it touches the signature, and a signature that `sign-key` prints always verifies under the key words it
prints.

**Keygen** streams the kept subtree. It runs one stack-based treehash per chunk (about four chunks per thread), each
recording only the nodes the plan keeps, and then hashes the chunk roots together. It costs exactly `key_gen`'s
`2^b·226 + 2(26 − b)` keccak256 calls and `2^b·233 + 2(26 − b)` permutations. sphincs-art's keygen figures,
`1 + 2^b·226 + 2(26 − b)` and `1 + 2^b·233 + 2(26 − b)`, are one higher: they count `2^b` nodes in a tree that has
`2^b − 1`.

**Cost against the model.** Against `tier_model.py` (the sphincs-art model), in calls and in permutations alike: keygen
is one under it, as above. The auth path equals `tree_cost` exactly; with `level c only`, the rehash up to the kept
subtree's root that the model counts is the signer's cache check. A signature costs the model's mean plus 13 for
`b < 26`, because the 13 opened FORS secrets are derived a second time. At `b = 26` it costs the model's mean plus 14:
also one grind try and the digest recomputed after it, where the model counts no grind. That gives means of 158,961
calls (159,020 permutations) for Light, 155,234 (155,461) for Standard and 176,867 (177,766) for Full. `sign-key` then
spends 249 calls (259 permutations) verifying the signature, and every run loads and checks the key file: 1,050, 32,780
and 524,288 calls (as many permutations) for Light, Standard and Full. The model counts neither.

**Memory.** `keygen_cached` holds the cache, the `2^t` chunk roots and a `b + 1`-node stack per thread. Writing the key
file streams it (header, surrogates, cache, then the checksum computed on the way), so `lssk keygen` holds one copy of
the cache. Loading reads the cache straight into place and checks it without a second copy. Signing needs about
2.56 MB on top of the loaded key, whatever the cache (the 13 FORS trees and their leaves). These are the leanSphincs-23
crate's measurements (a counting allocator at `b ≤ 13`), whose keygen, key file and signing code this crate shares
with one more surrogate; they were not re-measured here. By the same accounting, Standard needs about 1 MiB of heap for
keygen and about 3.6 MB for `sign-key`, and Full about 16 MiB and about 19.3 MB.

```sh
./target/release/lssk keygen --seed-file seed.hex --tier light -o key.lssk   # or --seed-stdin; --tier standard|full, or --b N --cache-bytes N
                                                                             # [--force] [--threads N]; prints 0x || abi.encode(pkSeed, pkRoot)
./target/release/lssk sign-key key.lssk <msg_hex64>                          # the same output as `lssk sign <seed_hex64> <b> <msg_hex64>`
./target/release/lssk info key.lssk                                          # JSON: tier, b, s, plan, cache, key words, costs; no secret
pass show lssk/seed | ./target/release/lssk keygen --seed-stdin --tier standard -o standard.lssk   # the seed from a password manager
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

`keygen` and `sign-key` print the keccak256 calls, the Keccak-f permutations and the wall time on stderr, and
`sign-key` reports its 249-call verification apart from the signature. `sign-key` prints nothing on standard output
when it fails. `sign-key` and `info` warn when group or others can access the key file, or another user owns it. With
`LSSK_RSS=1`, every command also prints `VmHWM` at exit. That is a lower bound on the peak RSS: the kernel's
high-water mark can miss a short-lived peak.

### Operational rules

- **One seed, one key.** Never use a seed with two different `b`: two tiers, a tier and a custom `b`, or `keygen` and
  `lssk sign` at another `b`. `P`, the WOTS and FORS keys and the real tree nodes depend only on the seed and the leaf
  index, not on `b`. Where two same-seed keys' kept subtrees overlap (always, against a full key; Light inside
  Standard for 1 seed in 64), a signature of one key becomes a valid signature of the other by swapping in path nodes
  that the other key's signatures and surrogates make public. No secret is needed, so the stronger key falls to the
  weaker one's lifetime. Use a fresh, independent seed for every key. `keygen` cannot detect reuse, and nothing in the
  scheme or the key derivation changes this.
- **One seed, one scheme.** Never use a leanSphincs-23 seed for leanSphincs-S, or the reverse: their one-time keys
  are the same, and they sign a FORS key with them there and FORS tops here. The key files cannot be confused (another
  magic), but the seed is the same 32 bytes.
- **The key file is the secret.** It holds the seed in the clear: keep it mode `0600` and back it up like a private key.
- **Check the key words.** A key file proves that its `P`, `s` and surrogates are its seed's, and that its cache, kept
  subtree root and root are consistent with each other. It does not prove that the root is the seed's: that would
  cost a keygen. Compare the `pkSeed` and `pkRoot` that `keygen`, `sign-key` and `info` print with the registered key.
- **Signing is deterministic.** The signer and the key file keep no count of signatures: staying under the tier's
  design target (Light 20,000) is the caller's job.

### Key file (version 1)

```text
offset         length          field
0              8               magic "LS-SKKEY"
8              4               format version, u32 little endian: 1
12             1               tier: 0 custom, 1 light, 2 standard, 3 full
13             1               b, the kept subtree's height (0..=26)
14             1               cache plan: 0 none, 1 top levels c..b, 2 level c only, 3 whole subtree
15             1               c (0 for none and whole subtree)
16             8               s, u64 little endian: the kept subtree holds leaves s 2^b .. (s + 1) 2^b
24             8               cache budget in bytes, u64 little endian
32             16              P
48             16              root
64             16              the kept subtree's root (level b)
80             32              the seed S (secret)
112            16 (26 - b)     surrogates, levels b..25
112+16(26-b)   16 nodes        the cache: the plan's levels from the lowest, each level's nodes from the left
end - 32       32              keccak256 of every byte before it
```

The layout is leanSphincs-23's at `h = 26`, under another magic: `lssk` refuses an `ls23k` key file (`"LS23KKEY"`) as
not a key file, and `ls23k` refuses this one. A Light key file is 16,736 B, a Standard one 1,048,800 B, a Full one
16,777,344 B; no key file is longer than 2,147,483,776 B (a full key caching its whole tree). The seed is stored in the
clear, so the file is only as safe as its permissions. Loading fails closed with a specific error, in this order:

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

## Cost model

```sh
python3 tier_model.py                                  # the three tiers, keccak256 calls then Keccak-f permutations
python3 tier_model.py --b 16 --cache-bytes 64KiB       # and a custom (b, cache) column
python3 tier_model.py --json                           # both units, machine-readable
python3 tier_model.py --check                          # the pinned figures; exit 1 on a miss
python3 tier_model.py --sphincs-art ~/sphincs-art      # run that checkout's scripts/keccak_model.py and compare (numpy, scipy)
```

`tier_model.py` transcribes sphincs-art's `scripts/keccak_model.py` (commit 537dfd9), the upstream keccak branch's cost
model with the merged encoding, and counts both units. In permutations it reproduces the page: verification 259,
keygen 1,908,763 / 244,318,221 / 15,636,365,313, mean signing 159,007 / 155,448 / 177,752, and the page's times. Its
lifetimes are the cover estimate at 127 bits, 43.7K / 3.05M / 108M, each clearing the tier's design target (20K / 2^21
/ 2^23) by the sweep's 25% margin; the page's newer figures, 38.2K / 2.87M / 103M, lower the estimate by the
proposal's proof gaps and are quoted, not recomputed. The repo docs rate Full at 2^26, the page's headline lifetime for
leanSphincs-S, which both estimates also clear by that margin (spec §14). It needs only the standard library.

## Tests

```sh
cargo test --release
```

The tests check:

- the address, digest (26-bit leaf index) and signature layouts
- the exact keygen calls and permutations at `b ∈ {3, 10}`, verification at 249 calls and 259 permutations, an
  inadmissible counter's early exit at 158 calls, and the full-key keygen figures (`2^26 · 226` calls, `2^26 · 233`
  permutations)
- the permutation counter: `⌊L/136⌋ + 1` per call, midstates (upstream's `midstate_matches_one_pass`), and the
  aggregation across worker threads
- the merged encoding's input and costs (upstream's `encoding_absorbs_the_tops_and_the_counter`, at `k = 13`: 452
  bytes, 4 permutations one pass, 3 once plus 1 per counter from the midstate), and that the midstate search finds the
  least admissible counter
- tampering with every signature field, and other counters
- a known-answer vector for `key_gen(seed(1), 11)` and `m[i] = 7i`: public key
  `63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00` (upstream's), `keccak256(sig)`
  `33c69b6c1bd1fd1c7a10e932f0dd988b7cfb178c8e2080c9f24c4a38eea2db83`, counter 14,828
- the WOTS+C mean number of encoding tries, about 14,670
- the tiers: the plan is the sweep's `tree_cost` for every `b ≤ 26` and every cache size at and around each threshold,
  in calls and in permutations. For every `b` in 1..=12 and every cache plan, keygen costs exactly `key_gen`'s calls
  and permutations and reaches its key, and `sign_with_cache` gives `sign`'s bytes at `sign`'s cost plus exactly
  `tree_cost` for the path, then a 249-call, 259-permutation verification. The tests also cover:
  - the streaming keygen on 1 to 100 threads, and absurd thread counts;
  - caches corrupted after loading failing the signature, and consistently re-sealed key files: a returned signature
    always verifies under the key's root;
  - a Light-tier end to end;
  - key files: round trips; every flipped bit of every byte, every truncation and extension rejected; a corrupt header
    read as a checksum mismatch; single-field re-checksummed edits caught; a leanSphincs-23 key file refused; FIFOs,
    devices, directories and oversized files refused before reading; warnings on files others can access;
  - the writer: `0600`, refused overwrites, a write failing part way through leaving no file, the path checked before
    the keygen, concurrent writers;
  - the `keygen`/`sign-key`/`info` CLI against `sign`; the seed never repeated in an error, nor printed (`tests/cli.rs`
    runs `lssk` as a process); a seed file others can access refused; `keygen` killed mid-write leaving nothing at the
    key file's path; `sign-key` printing nothing for a re-sealed key file.

  `cargo test --release -- --include-ignored` adds a Standard-tier end to end (two `b = 20` keygens).

## Cross-check against the Python signer

```sh
# from the repo root; needs pycryptodome (the repo venv has it)
.venv/bin/python signers/leansphincs-s-keccak/crosscheck.py [--jobs N] [--no-build] [--b 8 10 ...]
```

`crosscheck.py` runs `lssk kat` and the independent `script/leansphincs_s_signer.py --json` on 16 vectors (b from 4
to 11; seeds and messages including all-zero and all-`0xff`, and the known-answer vector), and requires every field to
match byte for byte. It also verifies each side's signature with the other side's verifier, recomputes the digest, the
randomizer (`ρ = R_0 + i` with `i < 2^40`, and minimal up to `2^23`), the FORS tops, the merged encoding over them, the
counter minimality and the root from the spec in a third implementation, and checks that `lssk sign` matches the
Python ABI output and that both verifiers give the contract's revert reasons. Negative controls check that the
randomizer check fails for an `R_0` derived any other way: `R_0` is used only by the signers, so nothing else would
notice a derivation bug they share. The Python signer grinds about `2^(26 − b)` randomizers per signature, so the
`b = 4` vectors dominate its run time. It exits nonzero on any difference, and it refuses an `lssk` older than the
crate sources, even with `--no-build`.

## KAT fixture for the Forge tests

```sh
.venv/bin/python signers/leansphincs-s-keccak/make_kat_fixture.py [--check] [--no-build]
```

`make_kat_fixture.py` writes `test/fixtures/leansphincs-s-keccak-kat.json`: six `lssk kat` vectors (b = 6, 10, 12;
messages all-zero, all-`0xff`, `0xdeadbeef` × 8 and a keccak-derived one), each confirmed by the Python `--verify`
(valid, and invalid for a one-bit message flip). Each vector also carries `above_target_counter`, the least counter
whose codeword sum exceeds `T = 128` for that signature's FORS tops, which the Forge tests use to check the `Σ > T`
side of the target-sum check. `test/LeanSphincsSTest.t.sol` and `test/SphincsAccountLeanSphincsSTest.t.sol` read it.
The output is deterministic; `--check` fails if the committed file is stale. Like `crosscheck.py`, it refuses an `lssk`
older than the crate sources, so `--no-build` cannot write a fixture the sources do not reproduce. It also refuses a
vector set without both values of bit 25 of `idx` and of bit 11 of `u_12`: each bit picks between two verifier
placements (the last auth-path node as the left or the right child; tree 12's top store spilling onto the counter or
not), and the Forge tests require both sides of each (`testFixtureCoverageGuardsAreTwoSided`).

```sh
forge test --match-contract LeanSphincsSTest -vv
```

The Forge FFI tests sign with `lssk`: with `sign`, and with a Light-tier key file (`keygen --seed-stdin` into a
temporary directory, then `sign-key`), whose output must equal `lssk sign <seed> 13 <msg>` byte for byte. They fail if
the binary is older than the crate sources. The `leansphincs-s` CI job builds `lssk` and runs the cargo tests, the
crosscheck, `make_kat_fixture.py --check`, a Light-tier `keygen` + `sign-key` against `sign`, `tier_model.py --check`
and `--json`, and these Forge suites.
