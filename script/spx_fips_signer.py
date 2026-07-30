#!/usr/bin/env python3
"""
SPX FIPS signer — plain SPHINCS+ (C12) on the FIPS 205 §4.2 uncompressed
32-byte ADRS.

This is the FIPS-layout twin of `jardin_spx_signer.py`. We reuse the shared
implementation, configure the corrected C12 WOTS+ width (l1=43, l2=3, l=46),
and swap its ADRS constructor for the FIPS one. Python resolves these values and
`make_adrs` as module globals at call time, so every call site (WOTS, XMSS,
FORS, and the signer's own self-check verifier) picks up the C12 layout.

The shared `jardin_spx_signer.py` is intentionally left untouched because it is
cross-referenced verbatim by the nconsigny/JARDIN repo (as JardinSpxVerifier).

Usage:
    python3 script/spx_fips_signer.py <master_sk_hex> <message_hex> [sig_counter]

Output: ABI-encoded (bytes32 seed, bytes32 root, bytes sig) hex on stdout.
"""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import jardin_spx_signer as spx

# The legacy shared module retains the historical 42-chain JARDIN parameters.
# Current on-chain C12 covers all 128 message bits with 43 base-8 digits.
spx.L1 = 43
spx.L2 = 3
spx.L = spx.L1 + spx.L2
spx.HT_LAYER_LEN = spx.L * spx.N + spx.H_PRIME * spx.N
spx.HT_LEN = spx.D * spx.HT_LAYER_LEN
spx.SIG_LEN = spx.R_LEN + spx.FORS_BODY_LEN + spx.HT_LEN


def make_adrs_fips(layer, tree, atype, kp, ci, cp, ha):
    """FIPS 205 §4.2 uncompressed 32-byte ADRS.

    Layout: layer(4) || tree(12) || type(4) || word1(4) || word2(4) || word3(4).
    Preserves the JARDIN (layer, tree, type, kp, ci, cp, ha) call signature so
    the shared signer's call sites stay identical; maps to FIPS word positions
    per type (FIPS 205 Table 1):
      0 WOTS_HASH  : w1=kp, w2=chain_address(=ci), w3=hash_address(=cp)
      1 WOTS_PK    : w1=kp, w2=0, w3=0
      2 XMSS_TREE  : w1=0,  w2=tree_height(=cp),   w3=tree_index(=ha)
      3 FORS_TREE  : w1=kp, w2=tree_height(=cp),   w3=tree_index(=ha)
      4 FORS_ROOTS : w1=kp, w2=0, w3=0
    """
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
            (tree & 0xFFFFFFFFFFFFFFFFFFFFFFFF) << 128 |   # 96-bit tree field
            (atype & 0xFFFFFFFF) << 96 |
            (w1 & 0xFFFFFFFF) << 64 |
            (w2 & 0xFFFFFFFF) << 32 |
            (w3 & 0xFFFFFFFF))


# Swap the shared signer's ADRS constructor for the FIPS one before signing.
spx.make_adrs = make_adrs_fips


if __name__ == "__main__":
    spx.main()
