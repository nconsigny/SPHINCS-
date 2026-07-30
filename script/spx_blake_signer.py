#!/usr/bin/env python3
"""
SPX BLAKE2b signer — plain SPHINCS+ (C12) on the FIPS 205 §4.2 uncompressed
32-byte ADRS with BLAKE2b instead of keccak256.

BLAKE2b twin of `spx_fips_signer.py`. The signing algorithm, parameters, digest
parsing and signature byte layout are identical; we reuse the shared signer
(`jardin_spx_signer.py`) and configure these module globals (resolved at call
time):
  * the corrected C12 WOTS+ width -> l1=43, l2=3, l=46;
  * `make_adrs`  -> the FIPS uncompressed 32-byte ADRS constructor; and
  * `F`, `H_`, `T_l`, `T_k`, `h_msg` -> BLAKE2b tweakable hashes.
The PRFs (`wots_secret`, `fors_secret`, `derive_R`) keep keccak — they are
signer-only (the verifier reads their outputs from the signature, never
recomputes them), so the on-chain BLAKE2b verifier is unaffected by them.

On-chain these run on the BLAKE2F compression precompile (0x09); here
hashlib.blake2b is BLAKE2b directly. F/H/T use a 16-byte digest (top-aligned,
matching keccak's & N_MASK); H_msg uses a 32-byte digest (full, for the index
slice). H_msg keeps the C12 domain tag 0xFF..FC (HMSG_DOMAIN_SPX).

Usage:
    python3 script/spx_blake_signer.py <master_sk_hex> <message_hex> [sig_counter]

Output: ABI-encoded (bytes32 seed, bytes32 root, bytes sig) hex on stdout.
"""

import sys, os, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import jardin_spx_signer as spx
from jardin_primitives import to_b32

# The legacy shared module retains the historical 42-chain JARDIN parameters.
# Current on-chain C12 covers all 128 message bits with 43 base-8 digits.
spx.L1 = 43
spx.L2 = 3
spx.L = spx.L1 + spx.L2
spx.HT_LAYER_LEN = spx.L * spx.N + spx.H_PRIME * spx.N
spx.HT_LEN = spx.D * spx.HT_LAYER_LEN
spx.SIG_LEN = spx.R_LEN + spx.FORS_BODY_LEN + spx.HT_LEN


def make_adrs_fips(layer, tree, atype, kp, ci, cp, ha):
    """FIPS 205 §4.2 uncompressed 32-byte ADRS (identical to spx_fips_signer)."""
    if atype == 0:
        w1, w2, w3 = kp, ci, cp
    elif atype == 1:
        w1, w2, w3 = kp, 0, 0
    elif atype == 2:
        w1, w2, w3 = 0, cp, ha
    elif atype == 3:
        w1, w2, w3 = kp, cp, ha
    elif atype == 4:
        w1, w2, w3 = kp, 0, 0
    else:
        raise ValueError(f"unknown ADRS type {atype}")
    return ((layer & 0xFFFFFFFF) << 224 |
            (tree & 0xFFFFFFFFFFFFFFFFFFFFFFFF) << 128 |
            (atype & 0xFFFFFFFF) << 96 |
            (w1 & 0xFFFFFFFF) << 64 |
            (w2 & 0xFFFFFFFF) << 32 |
            (w3 & 0xFFFFFFFF))


def _b16(data: bytes) -> int:
    return int.from_bytes(hashlib.blake2b(data, digest_size=16).digest(), "big") << 128


def _b32(data: bytes) -> int:
    return int.from_bytes(hashlib.blake2b(data, digest_size=32).digest(), "big")


def F(seed, adrs, M):
    return _b16(to_b32(seed) + to_b32(adrs) + to_b32(M))


def H_(seed, adrs, left, right):
    return _b16(to_b32(seed) + to_b32(adrs) + to_b32(left) + to_b32(right))


def T_multi(seed, adrs, vals):
    data = to_b32(seed) + to_b32(adrs)
    for v in vals:
        data += to_b32(v)
    return _b16(data)


def h_msg(seed, root, R, message):
    return _b32(to_b32(seed) + to_b32(root) + to_b32(R) +
                to_b32(message) + to_b32(spx.HMSG_DOMAIN_SPX))


# Swap ADRS + tweakable hashes before signing (call sites resolve these as
# module globals at call time, so every WOTS/XMSS/FORS/h_msg site picks them up).
spx.make_adrs = make_adrs_fips
spx.F = F
spx.H_ = H_
spx.T_l = T_multi
spx.T_k = T_multi
spx.h_msg = h_msg


if __name__ == "__main__":
    spx.main()
