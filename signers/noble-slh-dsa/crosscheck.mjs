#!/usr/bin/env node
/*
 * crosscheck.mjs — byte-for-byte cross-validation of the (patched) noble
 * SLH-DSA engine against the forked sphincs/sphincsplus C signer, at arbitrary
 * reduced params for fast iteration.
 *
 * Both sides are fed identical (seed48, message, opt_rand) and must produce the
 * SAME pk_seed, pk_root, and signature bytes. This is the trust gate for using
 * noble as a signer: it proves the patched engine is bit-identical to the C
 * reference the on-chain verifier was validated against.
 *
 *   node crosscheck.mjs <seed48_hex> <msg_hex> <optrand16_hex> <c_binary> [--H n --A n]
 *
 * The C binary signs raw bytes, so it is handed M' = 0x00 0x00 || M directly;
 * noble is handed M and applies the empty-ctx envelope itself. Defaults H=22,
 * A=24 (full NIST set). Use e.g. --H 18 --A 10 with a matching reduced C build.
 */
import { execFileSync } from 'node:child_process';
import { gen, SHA256_SIMPLE } from './build/slh-dsa-w4.mjs';

const argv = process.argv.slice(2);
const [seedHex, msgHex, optHex, cbin] = argv;
if (!seedHex || !msgHex || !optHex || !cbin) {
  console.error('usage: crosscheck.mjs <seed48_hex> <msg_hex> <optrand16_hex> <c_binary> [--H n --A n]');
  process.exit(2);
}
let H = 22, A = 24;
for (let i = 4; i < argv.length; i++) {
  if (argv[i] === '--H') H = Number(argv[++i]);
  else if (argv[i] === '--A') A = Number(argv[++i]);
}

const buf = (s) => Buffer.from(String(s).replace(/^0x/i, ''), 'hex');
const seed48 = buf(seedHex), msg = buf(msgHex), optrand = buf(optHex);
if (seed48.length !== 48) { console.error('seed must be 48 bytes'); process.exit(1); }
if (optrand.length !== 16) { console.error('optrand must be 16 bytes'); process.exit(1); }

const slh = gen({ N: 16, W: 4, H, D: 1, K: 6, A, securityLevel: 128 }, SHA256_SIMPLE);

// ── noble side ──
const { publicKey, secretKey } = slh.keygen(new Uint8Array(seed48));
const nPkSeed = Buffer.from(publicKey.subarray(0, 16));
const nPkRoot = Buffer.from(publicKey.subarray(16, 32));
const nSig = Buffer.from(slh.sign(new Uint8Array(msg), secretKey, { extraEntropy: new Uint8Array(optrand) }));

// ── C side (signs M' = 0000 || msg directly) ──
const mPrime = '0000' + msg.toString('hex');
const cOut = execFileSync(cbin, [seed48.toString('hex'), mPrime, optrand.toString('hex')],
  { stdio: ['ignore', 'pipe', 'ignore'], maxBuffer: 1 << 24 }).toString().trim();
const cRaw = Buffer.from(cOut, 'hex');
const cPkSeed = cRaw.subarray(0, 16), cPkRoot = cRaw.subarray(16, 32), cSig = cRaw.subarray(32);

// ── compare ──
const eq = (a, b) => Buffer.compare(a, b) === 0;
const okSeed = eq(nPkSeed, cPkSeed), okRoot = eq(nPkRoot, cPkRoot), okSig = eq(nSig, cSig);

console.log(`  params: H=${H} A=${A} (n=16 d=1 k=6 w=4), sig=${nSig.length} B`);
console.log(`  pk_seed  noble=0x${nPkSeed.toString('hex')}  C=0x${cPkSeed.toString('hex')}  ${okSeed ? 'OK' : 'DIFF'}`);
console.log(`  pk_root  noble=0x${nPkRoot.toString('hex')}  C=0x${cPkRoot.toString('hex')}  ${okRoot ? 'OK' : 'DIFF'}`);
console.log(`  sig      noble[..8]=0x${nSig.subarray(0, 8).toString('hex')}  C[..8]=0x${cSig.subarray(0, 8).toString('hex')}  ${okSig ? 'OK' : 'DIFF'}`);

if (!(okSeed && okRoot && okSig)) {
  if (!okSig && nSig.length === cSig.length) {
    const at = [...nSig].findIndex((b, i) => b !== cSig[i]);
    console.error(`  sig first mismatch at byte ${at}: noble=0x${nSig[at].toString(16)} C=0x${cSig[at].toString(16)}`);
  } else if (nSig.length !== cSig.length) {
    console.error(`  sig length differs: noble=${nSig.length} C=${cSig.length}`);
  }
  console.error('  MATCH: false');
  process.exit(1);
}
console.log('  MATCH: true');
