# leansphincs-keccak

Rust signer for **leanSphincs over keccak256**: Tom Wambsgans' proposal at its own parameters, the scheme the on-chain
verifier `src/keccak/LeanSphincsAsm.sol` checks. The spec is
[`docs/leanSphincs-keccak.md`](../../docs/leanSphincs-keccak.md).

It is a port of the upstream leanSphincs crate on its **`keccak` branch**
([leanXMSS-leanSPHINCS-candidates](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates), `crates/sphincs`
on branch `keccak`, MIT OR Apache-2.0, see `LICENSE.upstream`), **with nothing re-parameterized**: `h = 26`, `a = 10`,
`k = 24`, WOTS+C with `w = 4`, 64 chains and `T = 120`, upstream's two-call message digest, a 5,684-byte signature and
a 32-byte public key. The upstream crate is normative: its `known_answer` test passes here unchanged. The tiers, the
key file and the CLI are those of this repo's leanSphincs-S signer (`signers/leansphincs-s-keccak`). The module layout
and names are upstream's. Diffed against the upstream keccak branch, the changes are:

- the hash: Ethereum keccak256 (`0x01` padding) via `tiny-keccak`, where upstream has its own Keccak-256 crate. A
  thread-local keccak-call counter sits next to upstream's Keccak-f permutation counter, and both are aggregated across
  worker threads. A call over `L` input bytes is `⌊L/136⌋ + 1` permutations; a `Midstate` counts its whole blocks once,
  and each `finish` is one call and pays for the rest. `Th` keeps the first 16 output bytes.
- multithreading: keygen spreads the kept subtree's leaves over all cores, and signing builds the 24 FORS trees in
  parallel.
- factored out, with the same hash inputs: `split_digest` (what `message_digest` reads from its two calls),
  `derive_public_param`, `subtree_position`, `derive_surrogates`, `fold_surrogates`, `wots_leaf`, and `sign_with`
  (`sign` with the authentication path left to a closure, which the tiers use).

Everything that reaches the signature bytes is upstream's: the 16-byte tweak, `P`, the secrets, the FORS positions
(`κ + 32ℓ + 512j`, `j < 2^10`), the merged encoding (no FORS key hash, tweak type 11 unused; the WOTS+C encoding of the
one-time key at `e` is `Th(P, address(ENC, 0, 0, e), tops ‖ LE32(c))` over the 48 FORS tops, an 804-byte input of 6
permutations, of which the signer absorbs the 5 whole blocks once and pays one permutation per counter), the
surrogates, the randomizer grind, the serialization, and the message digest:

```text
D_c   = keccak256(P ‖ address(MSG, step 0, hi = c, lo = 0) ‖ m ‖ ρ)     c = 0, 1   (80 input bytes, one permutation each)
idx   = LE64(D_0[16..24]) & (2^26 − 1)
u_κ   = (LE64(D_{⌊κ/12⌋}[8w .. 8w + 8]) >> 10·(r mod 6)) & 0x3FF          r = κ mod 12,  w = ⌊r/6⌋
```

Six indices per 64-bit word, words 0 and 1 of each call; no field crosses a word. The randomizer grind reads call 0
only, from a midstate of `P ‖ address ‖ m`: one call and one permutation per attempt.

Verification costs a constant **342 keccak256 calls**, or **354 Keccak-f permutations** (`VERIFY_KECCAK_CALLS`,
`VERIFY_PERMUTATIONS`, the sphincs.art figure): digest 2, FORS 24·(1 + 9), encoding 1 call of 6 permutations, chains
72 (`192 − 120`), leaf 1 call of 8, path 26. An inadmissible counter stops it after 243 calls (248 permutations).

leanSphincs, leanSphincs-S and leanSphincs-f derive `P`, the one-time keys, the FORS secrets and the surrogates from
the seed in the same way: their public key at one seed and `b` is the same (at `key_gen(seed(1), 11)`, the pk that
upstream's `known_answer` pins). **Never use one seed for two variants**: each would sign a different encoding with
the same one-time keys (the spec, "Key separation").

## CLI

```sh
cargo build --release
./target/release/lsk sign   <seed_hex64> <b> <msg_hex64>         # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)
./target/release/lsk kat    <seed_hex64> <b> <msg_hex64>         # one JSON object (key, sig, idx, counter, randomizer, fors_indices)
./target/release/lsk verify <pkSeed_hex64> <pkRoot_hex64> <msg_hex64> <sig_hex>   # true | false

# one-signer tiers (below): the key is generated once and stored in a key file
./target/release/lsk keygen (--seed-file <path> | --seed-stdin) (--tier light|standard|full | --b N --cache-bytes N)
                            -o <keyfile> [--force] [--threads N]   # 0x || abi.encode(bytes32 pkSeed, bytes32 pkRoot)
./target/release/lsk sign-key <keyfile> <msg_hex64>              # what `sign` prints for the key's seed and b
./target/release/lsk info     <keyfile>                          # one JSON object: tier, plan, key words, costs; no secret
```

`b` is the height of the kept subtree (pruned key). `b = 26` is a full key, which costs about 1.52·10¹⁰ keccak calls
(`2^26 · 226`), or 1.56·10¹⁰ Keccak-f permutations (`2^26 · 233`, sphincs-art's 15.6B), to generate. The verifier
cannot tell a pruned key from a full one. The key words are high-aligned, which is the form the verifier takes:
`pkSeed = P ‖ 0^16` and `pkRoot = root ‖ 0^16`. Each run of `sign` regenerates the kept subtree, `2^b · 226` keccak
calls, and grinds about `2^(26 − b)` randomizers. On 8 cores of a busy shared host (load average about 55 on 32 cores),
`sign` took about 0.3 s at `b = 10` and 0.7 s at `b = 13`, a little less than `lssk` under the same load (its FORS is
61K calls against leanSphincs-S's 133K).

`sign` and `kat` take the seed on the command line, where every local user can read it in the process list and the
shell history keeps it. They are for test vectors and the Forge FFI tests. A real key goes through `keygen` (below),
which reads the seed from a private file or from standard input. No `lsk` error message repeats an argument's value.

## One-signer tiers

The tiers of sphincs-art's "One signer" table, which are the proposal's own (`src/tiers.rs`, `src/keyfile.rs`). The key
is generated once and stored in a key file with a node cache of bounded size. Each signature recomputes only what is not
cached:

| Tier       | `b` (kept subtree) | Cache  | Plan             | Auth path / sig: calls | permutations | Keygen calls   | Keygen permutations | Lifetime |
|------------|-------------------:|-------:|------------------|-----------------------:|-------------:|---------------:|--------------------:|---------:|
| `light`    | 13                 | 16 KiB | level 3 only     | 2,830                  | 2,886        | 1,851,418      | 1,908,762           | 210K     |
| `standard` | 20                 | 1 MiB  | top levels 5..20 | 7,231                  | 7,455        | 236,978,188    | 244,318,220         | 22M      |
| `full`     | 26 (whole tree)    | 16 MiB | top levels 7..26 | 28,927                 | 29,823       | 15,166,603,264 | 15,636,365,312      | 1.15B    |

The lifetimes are the proposal's, proved in Lean (the full tree: `2^30`). The tree, the WOTS leaf, the plans and the
keygen are leanSphincs-S's; only FORS, `T` and the digest differ, so only the signing cost does. The page's Keccak
figures for these tiers are keygen 1.91M / 244M / 15.6B permutations and signing 74K / 70K / 92K permutations, which
`tier_model.py` reproduces (it transcribes sphincs-art's `scripts/keccak_model.py`, "Tom FORS (check 354)": 73,459 /
69,900 / 92,204; below). Light is the page's Ledger Nano S+ class tier: its 16 KiB cache is the page's budget for such
a device, and the page estimates 5.5 min to generate it and 13 s per signature at 5.8K permutations per second. This
crate is a host-side reference signer, not a device implementation. Any `(b, cache_bytes)` also works. The keys, the
randomizer grind (`ρ = R_0 + i`) and the WOTS+C counter are those of `key_gen` and `sign`, so `sign_with_cache` gives
the same bytes as `sign(&key_gen(seed, b).0, m)`. Only the source of the auth path changes. The verifier, the spec and
the fixtures are unaffected.

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
path reads everything from it. Last, `sign_with_cache` verifies the signature under the key's public key (342 calls,
354 permutations, reported apart from the signature's cost) and returns an error rather than a signature that does not
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
subtree's root that the model counts is the signer's cache check. A signature costs the model's mean plus 24 for
`b < 26`, because the 24 opened FORS secrets are derived a second time. At `b = 26` it costs the model's mean plus 25:
also one grind try, where the model counts no grind. That gives means of 73,422 calls (73,483 permutations) for Light,
69,695 (69,924) for Standard and 91,328 (92,229) for Full. `sign-key` then spends 342 calls (354 permutations)
verifying the signature, and every run loads and checks the key file: 1,050, 32,780 and 524,288 calls (as many
permutations) for Light, Standard and Full. The model counts neither.

**Memory.** `keygen_cached` holds the cache, the `2^t` chunk roots and a `b + 1`-node stack per thread. Writing the key
file streams it (header, surrogates, cache, then the checksum computed on the way), so `lsk keygen` holds one copy of
the cache. Loading reads the cache straight into place and checks it without a second copy. Signing holds the 24 FORS
trees and their leaves, about 1.18 MB on top of the loaded key whatever the cache (`24 · (1024 + 2046) · 16` bytes; the
leanSphincs-S crate's 13 trees of `2^12` leaves take 2.56 MB). These are counts, not measurements; the leanSphincs-23
crate measured the same code with a counting allocator at `b ≤ 13`. By the same accounting, Standard needs about 1 MiB
of heap for keygen and about 2.2 MB for `sign-key`, and Full about 16 MiB and about 18 MB.

```sh
./target/release/lsk keygen --seed-file seed.hex --tier light -o key.lsk   # or --seed-stdin; --tier standard|full, or --b N --cache-bytes N
                                                                           # [--force] [--threads N]; prints 0x || abi.encode(pkSeed, pkRoot)
./target/release/lsk sign-key key.lsk <msg_hex64>                          # the same output as `lsk sign <seed_hex64> <b> <msg_hex64>`
./target/release/lsk info key.lsk                                          # JSON: tier, b, s, plan, cache, key words, costs; no secret
pass show lsk/seed | ./target/release/lsk keygen --seed-stdin --tier standard -o standard.lsk   # the seed from a password manager
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
`sign-key` reports its 342-call verification apart from the signature. `sign-key` prints nothing on standard output
when it fails. `sign-key` and `info` warn when group or others can access the key file, or another user owns it. With
`LSK_RSS=1`, every command also prints `VmHWM` at exit. That is a lower bound on the peak RSS: the kernel's
high-water mark can miss a short-lived peak.

### Operational rules

- **One seed, one key.** Never use a seed with two different `b`: two tiers, a tier and a custom `b`, or `keygen` and
  `lsk sign` at another `b`. `P`, the WOTS and FORS keys and the real tree nodes depend only on the seed and the leaf
  index, not on `b`. Where two same-seed keys' kept subtrees overlap (always, against a full key; Light inside
  Standard for 1 seed in 64), a signature of one key becomes a valid signature of the other by swapping in path nodes
  that the other key's signatures and surrogates make public. No secret is needed, so the stronger key falls to the
  weaker one's lifetime. Use a fresh, independent seed for every key. `keygen` cannot detect reuse, and nothing in the
  scheme or the key derivation changes this.
- **One seed, one scheme.** Never use a seed for two leanSphincs variants (leanSphincs, leanSphincs-S, leanSphincs-f,
  leanSphincs-23): their one-time keys are the same, and each signs a different encoding with them. The key files
  cannot be confused (each variant has its own magic), but the seed is the same 32 bytes.
- **The key file is the secret.** It holds the seed in the clear: keep it mode `0600` and back it up like a private key.
- **Check the key words.** A key file proves that its `P`, `s` and surrogates are its seed's, and that its cache, kept
  subtree root and root are consistent with each other. It does not prove that the root is the seed's: that would
  cost a keygen. Compare the `pkSeed` and `pkRoot` that `keygen`, `sign-key` and `info` print with the registered key.
- **Signing is deterministic.** The signer and the key file keep no count of signatures: staying under the tier's
  lifetime (Light 210K) is the caller's job.

### Key file (version 1)

```text
offset         length          field
0              8               magic "LS-KKKEY"
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

The layout is leanSphincs-S's and leanSphincs-f's, under another magic: `lsk` refuses an `lssk` (`"LS-SKKEY"`),
`lsfk` (`"LS-FKKEY"`) or `ls23k` (`"LS23KKEY"`) key file as not a key file, before reading anything else, and those
signers refuse this one. A Light key file is 16,736 B, a Standard one 1,048,800 B, a Full one 16,777,344 B; no key
file is longer than 2,147,483,776 B (a full key caching its whole tree). The seed is stored in the clear, so the file
is only as safe as its permissions. Loading fails closed with a specific error, in this order:

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

`tier_model.py` transcribes sphincs-art's `scripts/keccak_model.py` (commit 537dfd9) at its "Tom FORS (check 354)"
parameters, `fors(26, 24, 10, 120)`: the upstream keccak branch's cost model with the merged encoding, in both units.
In permutations it reproduces the page: verification 354, keygen 1,908,763 / 244,318,221 / 15,636,365,313, mean
signing 73,459 / 69,900 / 92,204, and the page's figures and times (74K / 70K / 92K: the page rounds 73.5K again, to
two figures). In keccak256 calls, verification is 342 and mean signing 73,398 / 69,671 / 91,303 (the digest is two
calls). The tiers' lifetimes, 210K / 22M / 1.15B, are the proposal's, proved in Lean, and are quoted, not recomputed.
The model also computes the cover estimate at 127 bits, 242,283 / 23,797,924 / 1,203,134,883: the proved figures sit
13.3% / 7.6% / 4.4% below it, within the 4–17% proof gap the sphincs-art README gives, and the full tree's 1.15B
clears `2^30`. `--sphincs-art` checks the verification, keygen, signing and estimate figures against the script
itself. It needs only the standard library.

## Tests

```sh
cargo test --release
```

Upstream's tests run verbatim (but for `keccak::hash`, which is `keccak256` here): in `scheme.rs`,
`pruned_sign_verify_and_costs` (`b ∈ {3, 12}`), `tampered_signatures_are_rejected`, `known_answer` (public key
`63b118353523319f8f74f387824956482e582128e480149accc2ed4f19edcd00`, `keccak256(sig)`
`9a21b6bc61d6ba500b4d67809912c1424be1f58486eda144e4ef70afd01cf94d`, counter 1,176),
`a_randomizer_attempt_costs_one_permutation`, `randomizer_and_digest_inputs`, `digest_fields`,
`encoding_absorbs_the_tops_and_the_counter` and `wots_encoding_takes_about_829_tries`; in `hash.rs`, `address_layout`
and `midstate_matches_one_pass`. The crate's own tests check:

- keccak256 calls besides permutations: keygen at `b ∈ {7, 9}` and the full-key figures (`2^26 · 226` calls,
  `2^26 · 233` permutations), every signature's exact work (R_0, the grind's attempts, the two digest calls, FORS
  with the 24 opened secrets derived again, the encoding search, the WOTS secrets and the 120 chain steps),
  verification at 342 calls and 354 permutations, and an inadmissible counter's early exit at 243 calls
  (248 permutations)
- the signature layout at the spec's offsets (FORS `16 + 176κ`, counter 4240, WOTS 4244, auth path 5268), and one
  flipped bit in every field rejected
- every one of the 512 bits of the two digest calls: which field reads it (266 of them), the grind reading call 0 only
- the permutation counter: `⌊L/136⌋ + 1` per call, midstates in calls, and the aggregation across worker threads; the
  encoding search (5 permutations once, then one per counter) finding the least admissible counter
- the tiers: the plan is the sweep's `tree_cost` for every `b ≤ 26` and every cache size at and around each threshold,
  in calls and in permutations. For every `b` in 1..=12 and every cache plan, keygen costs exactly `key_gen`'s calls
  and permutations and reaches its key, and `sign_with_cache` gives `sign`'s bytes at `sign`'s cost plus exactly
  `tree_cost` for the path, then a 342-call, 354-permutation verification. The tests also cover:
  - the streaming keygen on 1 to 100 threads, and absurd thread counts;
  - caches corrupted after loading failing the signature, and consistently re-sealed key files: a returned signature
    always verifies under the key's root;
  - a Light-tier end to end;
  - key files: round trips; every flipped bit of every byte, every truncation and extension rejected; a corrupt header
    read as a checksum mismatch; single-field re-checksummed edits caught; `lssk`, `lsfk` and `ls23k` key files
    refused; FIFOs, devices, directories and oversized files refused before reading; warnings on files others can
    access;
  - the writer: `0600`, refused overwrites, a write failing part way through leaving no file, the path checked before
    the keygen, concurrent writers;
  - the `keygen`/`sign-key`/`info` CLI against `sign`, and the other variants' key files refused by `info` and
    `sign-key`; the seed never repeated in an error, nor printed (`tests/cli.rs` runs `lsk` as a process); a seed file
    others can access refused; `keygen` killed mid-write leaving nothing at the key file's path; `sign-key` printing
    nothing for a re-sealed key file.

  `cargo test --release -- --include-ignored` adds a Standard-tier end to end (two `b = 20` keygens).

## Cross-check against the Python signer

```sh
# from the repo root; needs pycryptodome (the repo venv has it)
.venv/bin/python signers/leansphincs-keccak/crosscheck.py [--jobs N] [--no-build] [--b 8 10 ...]
```

`crosscheck.py` runs `lsk kat` and the independent `script/leansphincs_s_signer.py --variant regular --json` on 16
vectors (b from 4 to 11; seeds and messages including all-zero and all-`0xff`, and the known-answer vector), and
requires every field to match byte for byte. It also verifies each side's signature with the other side's verifier,
recomputes the two-call digest and its split, the randomizer (`ρ = R_0 + i` with `i < 2^40`, and minimal up to
`2^23`), the FORS tops, the merged encoding over them, the counter minimality and the root from the spec in a third
implementation. That implementation also recomputes, from the seed, what no verifier sees: the WOTS and FORS secrets
and the surrogates, hence the key's root (which must be `pkRoot`) and every byte of the signature (every FORS tree
rebuilt, the least counter, `σ_i`, the auth path). The script checks that both signers reproduce upstream's
`known_answer` pins, that `lsk sign` matches the Python ABI output and that both verifiers give the contract's revert
reasons. Negative controls check that the randomizer check fails for an `R_0` derived any other way: `R_0` is used
only by the signers, so nothing else would notice a derivation bug they share. The Python signer grinds about
`2^(26 − b)` randomizers per signature, so the `b = 4` vectors dominate its run time. It exits nonzero on any
difference, and it refuses an `lsk` older than the crate sources, even with `--no-build`.

## KAT fixture for the Forge tests

```sh
.venv/bin/python signers/leansphincs-keccak/make_kat_fixture.py [--check] [--no-build]
```

`make_kat_fixture.py` writes `test/fixtures/leansphincs-keccak-kat.json`: six `lsk kat` vectors (b = 6, 10, 12;
messages all-zero, all-`0xff`, `0xdeadbeef` × 8 and a keccak-derived one), each confirmed by the Python
`--variant regular --verify` (valid, and invalid for a one-bit message flip). Each vector also carries
`above_target_counter`, the least counter whose codeword sum exceeds `T = 120` for that signature's FORS tops, which
the Forge tests use to check the `Σ > T` side of the target-sum check. The output is deterministic; `--check` fails if
the committed file is stale. Like `crosscheck.py`, it refuses an `lsk` older than the crate sources, so `--no-build`
cannot write a fixture the sources do not reproduce. It also refuses a vector set without both values of bit 25 of
`idx` and of bit 9 of `u_23`: each bit picks between two verifier placements (the last auth-path node as the left or
the right child; the order of the last FORS tree's top pair, the last store before the counter), as leanSphincs-S's
fixture guards bit 25 of `idx` and bit 11 of `u_12`.

```sh
forge test --match-contract '^LeanSphincsTest$|^SphincsAccountLeanSphincsTest$' -vv
```

`test/LeanSphincsTest.t.sol` and `test/SphincsAccountLeanSphincsTest.t.sol` read the fixture and sign with `lsk`.
`--match-contract` is a regex: anchor it, since `LeanSphincs` alone also matches the leanSphincs-S and leanSphincs-f
suites. The `leansphincs` CI job builds `lsk` and runs the cargo tests (release and debug), the crosscheck, the Python
signer's `--variant regular --selftest` (with the upstream known answer), `make_kat_fixture.py --check`, a Light-tier
`keygen` + `sign-key` against `sign`, `tier_model.py --check` and `--json`, and these Forge suites. The `solidity` job
also builds `lsk` before its full forge test, where the FFI tests fail rather than skip without it.
