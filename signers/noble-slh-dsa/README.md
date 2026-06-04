# noble-post-quantum SLH-DSA-SHA2-128-24 signer

A second, independent off-chain signer for the live `src/SLH-DSA-SHA2-128-24verifier.sol`
verifier, backed by [`@noble/post-quantum`](https://github.com/paulmillr/noble-post-quantum)'s
SLH-DSA engine instead of the forked C reference (`signers/sphincsplus-128-24/`).

It exists to cross-validate the on-chain verifier against a *third* implementation
(Solidity ⟷ C ⟷ noble) and to offer a dependency-light, pure-JS signing path.
**It is not used on-chain and is not in any trusted path** — like every signer here,
its output is only trusted insofar as the stateless verifier re-checks it.

## Why this only works for SHA-2-128-24, not C13

noble implements stock **FIPS 205 SLH-DSA**. The SHA-2-128-24 verifier *is* a FIPS 205
external SLH-DSA verify (empty context), just at a custom parameter set — so a
(lightly patched) noble can reproduce it bit-for-bit. **C13 cannot use noble at all**:
it is the ePrint 2025/2203 WOTS+C / FORS+C *counter-grinding* construction over
keccak256, which is not standard SLH-DSA. Use `script/signer.py c13` /
`signer-wasm` for C13.

## Parameter set (NIST SP 800-230 Table 1)

```
n = 16   h = 22   d = 1 (single XMSS tree)   a = 24   k = 6   w = 4 (lg w = 2)
external SLH-DSA.Sign, empty context:  M' = 0x00 0x00 || M
signature = 3856 bytes   pk = pkSeed(16) || pkRoot(16)
```

This is **not** one of noble's six published sets — `slh_dsa_sha2_128s/f` use
`w=16, d≥7`. We instantiate noble's generic `gen()` engine with these params.

## The patch (6 edits, applied at build time)

`gen()` and `SHA256_SIMPLE` are module-internal in noble, and `gen()` hardcodes
`w=16` and a 2-byte key-pair-address field (every standard set has `h' ≤ 16`).
`patch-noble.mjs` applies six explicit, asserted edits to the **pinned** installed
`slh-dsa.js` and writes `build/slh-dsa-w4.mjs`:

1. repoint the local `./utils.js` import to the package subpath;
2. `export` `gen()`;
3. **generalize the Winternitz parameter** — `WOTS_LOGW = log2(W)` and the FIPS 205
   `WOTS_LEN2 = floor(log2(len1·(w−1))/lg w) + 1` (integer bit-length form).
   Reproduces noble's hardcoded table exactly at `w=16`; yields `len=68` at `w=4`;
4. **widen the key-pair-address write** to the full FIPS 4-byte field, guarded by
   `TREE_HEIGHT > 16 / > 24` so standard sets are byte-identical. Needed because
   `h'=22 ⇒ leafIdx` can exceed 2¹⁶ and must match the C ref's `u32 set_keypair_addr`
   and the verifier's `shl(144, leafIdx)`;
5. same widening for the key-pair-address *copy* path;
6. `export` `SHA256_SIMPLE`.

Every edit asserts its target appears exactly once, so a noble version bump that
moves the code **fails the build loudly** rather than silently changing behavior.
Versions are pinned (`@noble/post-quantum@0.6.1`, `@noble/hashes@2.2.0`) via the
committed lockfile; `build/` and `node_modules/` are gitignored (regenerable).

## Build & run

```bash
cd signers/noble-slh-dsa
npm ci                       # pinned deps
node patch-noble.mjs         # writes build/slh-dsa-w4.mjs

# Sign (drop-in for script/slh_dsa_sha2_128_24_fast_signer.py):
node slh_dsa_sha2_128_24_signer.mjs <master_sk_hex> <message_hex> [sig_counter]
#   -> 0x + abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)
#   sig_counter given  -> deterministic (opt_rand = counter(BE,4)||zeros), reproducible
#   sig_counter absent -> hedged (random opt_rand)
```

## Validation (the trust gate)

noble is only trustworthy here if it is **byte-identical** to the C reference the
verifier was validated against. Two gates:

```bash
# Gate A — fast, reduced params. Build a reduced C binary, then diff every byte.
#   (At H=18 keygen hashes leaves with keypair >= 2^16, so a pk_root match also
#    validates edit #4.)
cp -r ../sphincsplus-128-24 /tmp/csign-reduced && cd /tmp/csign-reduced
make CFLAGS="-O3 -std=c99 -I. -DSPX_FULL_HEIGHT=18 -DSPX_FORS_HEIGHT=10"
cd -; node crosscheck.mjs <seed48_hex> <msg_hex> <optrand16_hex> \
        /tmp/csign-reduced/slhdsa-sha2-128-24 --H 18 --A 10

# Gate B — authoritative, full params. Reproduce the pinned, on-chain-verified KAT
#   from test/SLH-DSA-SHA2-128-24-KAT.t.sol byte-for-byte (slow: 2^22 keygen in JS).
node kat-check.mjs
```

Both gates pass against the forked sphincs/sphincsplus C signer and the pinned KAT.
