#!/usr/bin/env node
/*
 * kat-check.mjs — Gate B: reproduce the pinned, on-chain-verified KAT at full
 * NIST params using the real signer CLI.
 *
 * Reads the expected (MSG, SK, SEED, ROOT, SIG) straight out of the Forge KAT
 * (test/SLH-DSA-SHA2-128-24-KAT.t.sol) so it can't drift, runs the noble signer
 * deterministically (sig_counter = 0), and asserts byte-for-byte equality. The
 * pinned SIG is exactly the one the on-chain verifier accepts, so a match proves
 * the noble path is interoperable with the deployed verifier.
 *
 * Slow: full-params keygen is a 2^22-leaf XMSS tree in pure JS (several minutes).
 * Run in the background.  Usage: node kat-check.mjs
 */
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const here = new URL('./', import.meta.url);
const katPath = fileURLToPath(new URL('../../test/SLH-DSA-SHA2-128-24-KAT.t.sol', here));
const signer = fileURLToPath(new URL('slh_dsa_sha2_128_24_signer.mjs', here));
const src = readFileSync(katPath, 'utf8');

const grabWord = (name) => {
  const m = src.match(new RegExp(`${name}\\s*=\\s*(0x[0-9a-fA-F]+)`));
  if (!m) throw new Error(`could not find ${name} in KAT`);
  return m[1].toLowerCase();
};
const grabSig = () => {
  const m = src.match(/SIG\s*=\s*hex"([0-9a-fA-F]+)"/);
  if (!m) throw new Error('could not find SIG hex in KAT');
  return m[1].toLowerCase();
};

const MSG = grabWord('MSG');
// The KAT pins only SEED/ROOT/SIG; the master key + counter live in its generation
// comment ("...fast_signer.py 0x1111..1111 0xdeadbeef..00 0"). Hardcode them here.
// A wrong SK would surface below as a pk_seed mismatch (SEED is re-derived from SK).
const SK = '0x' + '11'.repeat(32);
const SIG_COUNTER = '0';
const SEED = grabWord('SEED').slice(2, 34);  // top 16 bytes (low 16 are zero padding)
const ROOT = grabWord('ROOT').slice(2, 34);
const SIG = grabSig();

console.log('  running noble signer at full params (2^22 keygen — minutes)...');
const out = execFileSync('node', [signer, SK, MSG, SIG_COUNTER],
  { stdio: ['ignore', 'pipe', 'ignore'], maxBuffer: 1 << 24 }).toString().trim();

// decode abi.encode(bytes32 seed, bytes32 root, bytes sig)
const enc = Buffer.from(out.replace(/^0x/, ''), 'hex');
const seed = enc.subarray(0, 16).toString('hex');
const root = enc.subarray(32, 48).toString('hex');
const sigLen = Number(BigInt('0x' + enc.subarray(96, 128).toString('hex')));
const sig = enc.subarray(128, 128 + sigLen).toString('hex');

const okSeed = seed === SEED, okRoot = root === ROOT, okSig = sig === SIG;
console.log(`  pk_seed  ${okSeed ? 'OK' : `DIFF noble=${seed} kat=${SEED}`}`);
console.log(`  pk_root  ${okRoot ? 'OK' : `DIFF noble=${root} kat=${ROOT}`}`);
if (okSig) {
  console.log(`  sig      OK (${sigLen} bytes match pinned KAT)`);
} else {
  const at = [...Buffer.from(sig, 'hex')].findIndex((b, i) => b !== Buffer.from(SIG, 'hex')[i]);
  console.log(`  sig      DIFF (len noble=${sig.length / 2} kat=${SIG.length / 2}; first mismatch byte ${at})`);
}
if (okSeed && okRoot && okSig) { console.log('  KAT MATCH: true'); }
else { console.error('  KAT MATCH: false'); process.exit(1); }
