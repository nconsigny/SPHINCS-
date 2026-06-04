#!/usr/bin/env node
/*
 * patch-noble.mjs — build a w-generic copy of noble-post-quantum's SLH-DSA
 * engine so it can produce the SPHINCs- repo's NIST SP 800-230 custom set
 * (SLH-DSA-SHA2-128-24: n=16, h=22, d=1, a=24, k=6, w=4).
 *
 * Upstream @noble/post-quantum/slh-dsa.js is a clean, FIPS-205-conformant
 * engine, but two things keep it from emitting this set out of the box:
 *   1. `gen()` and `SHA256_SIMPLE` are module-internal (only the 12 fixed NIST
 *      named sets are exported).
 *   2. `gen()` hardcodes the Winternitz parameter to w=16 (lg w = 4) and the
 *      key-pair-address field to 2 bytes (every standard set has h' <= 16).
 *
 * Rather than vendor a whole fork, this script applies SIX explicit, auditable
 * edits to the *pinned* installed copy and writes build/slh-dsa-w4.mjs. Each
 * edit asserts its target appears exactly once, so a noble version bump that
 * moves the code fails loudly here instead of silently changing behavior.
 *
 * Every edit is a no-op for the standard w=16 / h'<=16 sets (the generalized
 * WOTS_LEN2 formula reproduces upstream's hardcoded table; the extra keypair
 * bytes are guarded by TREE_HEIGHT>16 / >24). Re-run after `npm ci`.
 *
 * Usage: node patch-noble.mjs
 */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const here = new URL('./', import.meta.url);
// The "./package.json" subpath isn't in noble's exports map, so read the manifest
// straight off node_modules rather than require()-ing it.
const srcPath = fileURLToPath(new URL('node_modules/@noble/post-quantum/slh-dsa.js', here));
const verPath = fileURLToPath(new URL('node_modules/@noble/post-quantum/package.json', here));
let version;
try {
  version = JSON.parse(readFileSync(verPath, 'utf8')).version;
} catch {
  console.error('[patch-noble] @noble/post-quantum not installed — run `npm ci` first.');
  process.exit(1);
}

let src = readFileSync(srcPath, 'utf8');

const EDITS = [
  {
    name: 'repoint local utils import to the package subpath',
    from: `from "./utils.js";`,
    to: `from "@noble/post-quantum/utils.js";`,
  },
  {
    name: 'export gen()',
    from: `function gen(opts, hashOpts_) {`,
    to: `export function gen(opts, hashOpts_) {`,
  },
  {
    name: 'generalize the Winternitz parameter w',
    from:
`    if (W !== 16)
        throw new Error('Unsupported Winternitz parameter');
    const WOTS_LOGW = 4;
    const WOTS_LEN1 = Math.floor((8 * N) / WOTS_LOGW);
    const WOTS_LEN2 = N <= 8 ? 2 : N <= 136 ? 3 : 4;`,
    to:
`    // PATCH(SPHINCs-): generalize the Winternitz parameter w (upstream hardcodes w=16).
    // SP 800-230 SLH-DSA-SHA2-128-24 uses w=4 (lg w = 2). lg(w) must be a positive integer
    // that divides 8*N. WOTS_LEN2 = floor(log2(len1*(w-1))/lg w) + 1 (FIPS 205 Eq. for len2),
    // computed via integer bit-length to avoid FP edge cases; reproduces upstream's hardcoded
    // table exactly at w=16 (n in {8,16,24,32,..} -> 2/3/3/3, n>136 -> 4).
    const WOTS_LOGW = Math.log2(W);
    if (!Number.isInteger(WOTS_LOGW) || WOTS_LOGW < 1 || (8 * N) % WOTS_LOGW !== 0)
        throw new Error('Unsupported Winternitz parameter');
    const WOTS_LEN1 = Math.floor((8 * N) / WOTS_LOGW);
    const __bitLen = (x) => { let b = 0; while (x > 0) { b++; x >>>= 1; } return b; };
    const WOTS_LEN2 = Math.floor((__bitLen(WOTS_LEN1 * (W - 1)) - 1) / WOTS_LOGW) + 1;`,
  },
  {
    name: 'widen key-pair-address write to the full FIPS field',
    from:
`        if (keypair !== undefined) {
            addr[OFFSET_KP_ADDR1] = keypair;
            if (TREE_HEIGHT > 8)
                addr[OFFSET_KP_ADDR2] = keypair >>> 8;
        }`,
    to:
`        if (keypair !== undefined) {
            // PATCH(SPHINCs-): write the full FIPS key-pair-address field (up to 4 bytes).
            // Upstream writes only 2 bytes (h' <= 16 in every standard set); SP 800-230's
            // d=1/h'=22 set needs up to 3 so leafIdx >= 2^16 matches the C ref's u32
            // set_keypair_addr and the on-chain verifier (shl(144, leafIdx)). The high
            // bytes sit just below OFFSET_KP_ADDR1; guarded so standard sets are unchanged.
            addr[OFFSET_KP_ADDR1] = keypair;
            if (TREE_HEIGHT > 8)
                addr[OFFSET_KP_ADDR2] = keypair >>> 8;
            if (TREE_HEIGHT > 16)
                addr[OFFSET_KP_ADDR2 - 1] = keypair >>> 16;
            if (TREE_HEIGHT > 24)
                addr[OFFSET_KP_ADDR2 - 2] = keypair >>> 24;
        }`,
  },
  {
    name: 'widen key-pair-address copy to the full FIPS field',
    from:
`        if (keypairAddr) {
            addr.set(keypairAddr.subarray(0, OFFSET_TREE + 8));
            addr[OFFSET_KP_ADDR1] = keypairAddr[OFFSET_KP_ADDR1];
            if (TREE_HEIGHT > 8)
                addr[OFFSET_KP_ADDR2] = keypairAddr[OFFSET_KP_ADDR2];
        }`,
    to:
`        if (keypairAddr) {
            addr.set(keypairAddr.subarray(0, OFFSET_TREE + 8));
            // PATCH(SPHINCs-): copy the full key-pair-address field width (see widen note above).
            addr[OFFSET_KP_ADDR1] = keypairAddr[OFFSET_KP_ADDR1];
            if (TREE_HEIGHT > 8)
                addr[OFFSET_KP_ADDR2] = keypairAddr[OFFSET_KP_ADDR2];
            if (TREE_HEIGHT > 16)
                addr[OFFSET_KP_ADDR2 - 1] = keypairAddr[OFFSET_KP_ADDR2 - 1];
            if (TREE_HEIGHT > 24)
                addr[OFFSET_KP_ADDR2 - 2] = keypairAddr[OFFSET_KP_ADDR2 - 2];
        }`,
  },
  {
    name: 'export SHA256_SIMPLE',
    from: `const SHA256_SIMPLE = /* @__PURE__ */ (() => ({`,
    to: `export const SHA256_SIMPLE = /* @__PURE__ */ (() => ({`,
  },
];

for (const e of EDITS) {
  const count = src.split(e.from).length - 1;
  if (count !== 1) {
    console.error(`[patch-noble] target not unique (${count}x) for edit: "${e.name}"`);
    console.error(`  Upstream @noble/post-quantum@${version} drifted from the pinned shape.`);
    console.error(`  Re-review slh-dsa.js and update patch-noble.mjs before trusting output.`);
    process.exit(1);
  }
  src = src.replace(e.from, e.to);
}

const banner =
`// AUTO-GENERATED by signers/noble-slh-dsa/patch-noble.mjs — DO NOT EDIT.
// Source: @noble/post-quantum@${version} slh-dsa.js + 6 documented SPHINCs- edits
// (export gen + SHA256_SIMPLE; generalize Winternitz w; widen key-pair-address field).
// Regenerate with: (cd signers/noble-slh-dsa && npm ci && node patch-noble.mjs)
`;

const outDir = fileURLToPath(new URL('build/', here));
const outPath = fileURLToPath(new URL('build/slh-dsa-w4.mjs', here));
mkdirSync(outDir, { recursive: true });
writeFileSync(outPath, banner + src);
console.log(`[patch-noble] wrote build/slh-dsa-w4.mjs from @noble/post-quantum@${version} (6 edits applied)`);
