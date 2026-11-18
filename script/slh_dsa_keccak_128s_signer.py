#!/usr/bin/env python3
"""
SLH-DSA-Keccak-128s signer — plain SPHINCS+ (C12's construction) at the NIST
SLH-DSA-128s parameters, on the FIPS 205 §4.2 uncompressed 32-byte ADRS.

    n = 16, h = 63, d = 7, h' = 9, a = 12, k = 14, w = 16 (l1 = 32, l2 = 3, l = 35)
    R = 32 B. Signature 7,872 B. 2^64 signatures per key.

Like `spx_fips_signer.py` (C12), this reuses the shared `jardin_spx_signer.py`
implementation: it takes the FIPS ADRS constructor from `spx_fips_signer.py`,
sets the 128s parameters, and replaces the three helpers whose bit widths are
written for C12 (a = 7, w = 8): digest parsing, base-w digits and the WOTS+
checksum. Python resolves these as module globals at call time, so every call
site (WOTS, XMSS, FORS, and the signer's own self-check verifier) picks them up.
Hash framing, key derivation (HMAC-SHA512 labels, FORS PRF bound to the
hypertree position) and serialization are C12's, unchanged. H_msg uses its own
domain word, 0xFF..FA.

Verified on-chain by src/keccak/SLH-DSA-Keccak-128sAsm.sol.

Usage:
    python3 script/slh_dsa_keccak_128s_signer.py <master_sk_hex> <message_hex> [sig_counter]

Output: ABI-encoded (bytes32 seed, bytes32 root, bytes sig) hex on stdout.
Stateless from the seed: each call rebuilds the top tree for pk_root, then 7
XMSS trees of 2^9 leaves and 14 FORS trees of 2^12 leaves for the signature
(about 2.5 M keccak calls).
"""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import jardin_spx_signer as spx
from spx_fips_signer import make_adrs_fips  # also configures C12; overridden below

# ============================================================
#  Parameters (FIPS 205 Table 2, SLH-DSA-128s)
# ============================================================

spx.H       = 63
spx.D       = 7
spx.H_PRIME = 9
spx.A       = 12
spx.K       = 14
spx.W       = 16
spx.LOG_W   = 4
spx.L1      = 32
spx.L2      = 3
spx.L       = spx.L1 + spx.L2

spx.A_MASK        = (1 << spx.A) - 1
spx.H_PRIME_MASK  = (1 << spx.H_PRIME) - 1
spx.TREE_TOP_BITS = spx.H - spx.H_PRIME                 # 54
spx.TREE_TOP_MASK = (1 << spx.TREE_TOP_BITS) - 1
spx.W_MASK        = spx.W - 1

spx.FORS_TREE_LEN = spx.N + spx.A * spx.N               # 208
spx.FORS_BODY_LEN = spx.K * spx.FORS_TREE_LEN           # 2,912
spx.HT_LAYER_LEN  = spx.L * spx.N + spx.H_PRIME * spx.N # 704
spx.HT_LEN        = spx.D * spx.HT_LAYER_LEN            # 4,928
spx.SIG_LEN       = spx.R_LEN + spx.FORS_BODY_LEN + spx.HT_LEN   # 7,872

spx.HMSG_DOMAIN_SPX = spx.FULL - 5    # 0xFF..FA (C12 0xFF..FC, SLH-DSA-Keccak-128-24 0xFF..FB)

spx.make_adrs = make_adrs_fips

# ============================================================
#  The helpers written for C12's bit widths
# ============================================================

def digest_indices(d_int: int):
    """LSB-first: md[t] = 12 bits at 12t, tree = 54 bits at 168, leaf = 9 bits at 222."""
    md = [(d_int >> (spx.A * t)) & spx.A_MASK for t in range(spx.K)]
    tree_idx = (d_int >> (spx.K * spx.A)) & spx.TREE_TOP_MASK
    leaf_idx = (d_int >> (spx.K * spx.A + spx.TREE_TOP_BITS)) & spx.H_PRIME_MASK
    return md, tree_idx, leaf_idx

def base_w_node(node_int: int):
    """32 base-16 digits of the 128-bit node value (high 16 bytes of node_int), LSB-first."""
    v = node_int >> 128
    return [(v >> (4 * i)) & spx.W_MASK for i in range(spx.L1)]

def wots_checksum(msg_digits):
    assert len(msg_digits) == spx.L1
    csum = sum((spx.W - 1) - d for d in msg_digits)
    # l2·lg(w) = 12 bits, byte-aligned to 16: shift by 4; MSB-first 4-bit chunks (SLH-DSA base_w)
    csum_shifted = csum << 4
    return [(csum_shifted >> (12 - 4 * j)) & spx.W_MASK for j in range(spx.L2)]

spx.digest_indices = digest_indices
spx.base_w_node = base_w_node
spx.wots_checksum = wots_checksum


if __name__ == "__main__":
    spx.main()
