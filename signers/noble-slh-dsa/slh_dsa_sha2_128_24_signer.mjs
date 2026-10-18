#!/usr/bin/env node
/*
 * SLH-DSA-SHA2-128-24 signer backed by (patched) noble-post-quantum.
 *
 * Drop-in replacement for script/slh_dsa_sha2_128_24_fast_signer.py — same CLI,
 * same JARDIN key derivation, same ABI-encoded output, so it can be swapped into
 * the Forge FFI test (vm.ffi) for the on-chain SLH-DSA-SHA2-128-24 verifier.
 *
 *   node slh_dsa_sha2_128_24_signer.mjs <master_sk_hex> <message_hex> [sig_counter]
 *
 * Output (stdout): 0x + abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig),
 * with the 16-byte keys right-padded into bytes32 (low 16 bytes zero — the
 * verifier's canonicality requirement).
 *
 * Param set (NIST SP 800-230 Table 1): n=16, h=22, d=1, a=24, k=6, w=4.
 * Envelope: FIPS 205 EXTERNAL with empty context — noble's sign() prepends
 * M' = 0x00 0x00 || M itself, so the 32-byte message is passed through as-is.
 * Determinism: with `sig_counter`, opt_rand = counter(BE,4) || zeros(12) is fed
 * to noble via {extraEntropy}, matching the C signer's deterministic mode
 * byte-for-byte. Without it, hedged (noble draws a random opt_rand).
 *
 * Prerequisite: `npm ci && node patch-noble.mjs` in this directory.
 */
import { createHmac } from 'node:crypto';
import { gen, SHA256_SIMPLE } from './build/slh-dsa-w4.mjs';

const N = 16;
/** NIST SP 800-230 SLH-DSA-SHA2-128-24 (custom set; see CLAUDE.md). */
const slh = gen({ N: 16, W: 4, H: 22, D: 1, K: 6, A: 24, securityLevel: 128 }, SHA256_SIMPLE);

/**
 * Parse a hex CLI argument the way the Python wrappers do: optional 0x prefix, an
 * odd-length string is left-padded with '0', and any non-hex character is an error.
 * Buffer.from(s, 'hex') alone silently drops a trailing odd nibble and stops at the
 * first non-hex character, so the same input would sign different bytes here.
 */
function hexToBuf(name, s) {
  let h = String(s).replace(/^0x/i, '');
  if (!/^[0-9a-fA-F]*$/.test(h)) {
    console.error(`${name} is not a hex string`);
    process.exit(1);
  }
  if (h.length % 2) h = '0' + h;
  return Buffer.from(h, 'hex');
}
const hmac512 = (key, msg) => createHmac('sha512', key).update(msg).digest();

/** Mirrors derive_seed_48 in slh_dsa_sha2_128_24_fast_signer.py (JARDIN scheme). */
function deriveSeed48(masterSk) {
  const skSeed = hmac512(masterSk, Buffer.from('JARDIN/SLH2128_24/SKSEED')).subarray(0, N);
  const skPrf = hmac512(masterSk, Buffer.from('JARDIN/SLH2128_24/SKPRF')).subarray(0, N);
  const pkSeed = hmac512(masterSk, Buffer.from('JARDIN/SLH2128_24/PKSEED')).subarray(0, N);
  return Buffer.concat([skSeed, skPrf, pkSeed]);
}

/** abi.encode(bytes32 seed, bytes32 root, bytes sig) — matches the Python wrapper. */
function abiEncode(seed16, root16, sig) {
  const word = (n) => { const b = Buffer.alloc(32); b.writeUInt32BE(n >>> 0, 28); return b; };
  const pad32 = (b) => Buffer.concat([Buffer.from(b), Buffer.alloc(32 - b.length)]);
  const tail = Buffer.concat([sig, Buffer.alloc((32 - (sig.length % 32)) % 32)]);
  return Buffer.concat([pad32(seed16), pad32(root16), word(0x60), word(sig.length), tail]);
}

function main() {
  const [mskHex, msgHex, counterArg] = process.argv.slice(2);
  if (!mskHex || !msgHex) {
    console.error('usage: slh_dsa_sha2_128_24_signer.mjs <master_sk_hex> <message_hex> [sig_counter]');
    process.exit(2);
  }
  const masterSk = hexToBuf('master_sk', mskHex);
  if (masterSk.length !== 32) { console.error('master_sk must be 32 bytes'); process.exit(1); }
  const msg = hexToBuf('message', msgHex); // signed as-is; noble applies the 0x00 0x00 empty-ctx envelope
  if (msg.length !== 32) {
    console.error('message must be exactly 32 bytes (the verifier takes bytes32)');
    process.exit(1);
  }

  const seed48 = deriveSeed48(masterSk);
  const { publicKey, secretKey } = slh.keygen(new Uint8Array(seed48));
  const pkSeed = Buffer.from(publicKey.subarray(0, N));
  const pkRoot = Buffer.from(publicKey.subarray(N, 2 * N));

  const opts = {};
  if (counterArg !== undefined) {
    const optrand = Buffer.alloc(N);                 // opt_rand = counter(BE,4) || zeros(12)
    optrand.writeUInt32BE(Number(counterArg) >>> 0, 0);
    opts.extraEntropy = new Uint8Array(optrand);
  } // else: hedged — noble draws a random opt_rand (non-reproducible, like the Python default)

  const sig = Buffer.from(slh.sign(new Uint8Array(msg), secretKey, opts));
  if (sig.length !== 3856) { console.error(`unexpected sig length ${sig.length}`); process.exit(1); }

  process.stderr.write(`  pk_seed = 0x${pkSeed.toString('hex').slice(0, 16)}…\n`);
  process.stderr.write(`  pk_root = 0x${pkRoot.toString('hex').slice(0, 16)}…\n`);
  process.stdout.write('0x' + abiEncode(pkSeed, pkRoot, sig).toString('hex') + '\n');
}

main();
