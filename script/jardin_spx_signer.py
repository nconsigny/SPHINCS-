#!/usr/bin/env python3
"""
JARDÍN SPX signer — plain SPHINCS+ (JARDIN 32-byte ADRS).

Parameters:
    n = 16 bytes (128-bit keccak truncation)
    h = 20 total hypertree height
    d = 5  layers
    h' = h/d = 4  (16 WOTS+ keypairs per XMSS tree)
    a = 7         FORS tree height (128 leaves/tree)
    k = 20        FORS trees
    w = 8         Winternitz
    l1 = 42, l2 = 3, l = 45  (plain WOTS+ with checksum)
    R  = 32 B     per-signature randomness

Hash primitives (all keccak256 truncated to 16B):
    F     keccak(seed32 ‖ adrs32 ‖ M32)                      96 B
    H     keccak(seed32 ‖ adrs32 ‖ L32 ‖ R32)               128 B
    T_l   keccak(seed32 ‖ adrs32 ‖ v0..v44  × 32B)        1,504 B
    T_k   keccak(seed32 ‖ adrs32 ‖ r0..r19  × 32B)          704 B
    Hmsg  keccak(seed32 ‖ root32 ‖ R32 ‖ msg32 ‖ 0xFF..FC)  160 B

Signature layout (6,512 B):
    R(32) | FORS = 20 × (sk 16 + auth 7×16) = 2,560 | HT = 5 × (WOTS 45×16 + auth 4×16) = 3,920

Usage:
    python3 script/jardin_spx_signer.py <master_sk_hex> <message_hex> [sig_counter]

Output: ABI-encoded (bytes32 seed, bytes32 root, bytes sig) hex on stdout.
"""

import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from jardin_primitives import (
    keccak256, to_b32, to_b4,
    make_adrs, th, th_pair, th_multi,
    ADRS_WOTS_HASH, ADRS_WOTS_PK, ADRS_XMSS_TREE, ADRS_FORS_TREE, ADRS_FORS_ROOTS,
    N, N_MASK, FULL, hmac512,
)

# ============================================================
#  Parameters
# ============================================================

H          = 20
D          = 5
H_PRIME    = 4
A          = 7
K          = 20
W          = 8
LOG_W      = 3
L1         = 42
L2         = 3
L          = 45
R_LEN      = 32

A_MASK        = (1 << A) - 1
H_PRIME_MASK  = (1 << H_PRIME) - 1
TREE_TOP_BITS = H - H_PRIME
TREE_TOP_MASK = (1 << TREE_TOP_BITS) - 1
W_MASK        = W - 1

FORS_TREE_LEN = N + A * N                          # 128
FORS_BODY_LEN = K * FORS_TREE_LEN                  # 2560
HT_LAYER_LEN  = L * N + H_PRIME * N                # 720 + 64 = 784
HT_LEN        = D * HT_LAYER_LEN                   # 3920
SIG_LEN       = R_LEN + FORS_BODY_LEN + HT_LEN     # 6512

HMSG_DOMAIN_SPX = FULL - 3    # 0xFF..FC

# ============================================================
#  Hash primitives with SPX-specific shapes
# ============================================================

def F(seed, adrs, M):
    """F(seed, adrs, M) = keccak(seed32 || adrs32 || M32)[0..15]."""
    return th(seed, adrs, M)

def H_(seed, adrs, left, right):
    return th_pair(seed, adrs, left, right)

def T_l(seed, adrs, vals):
    return th_multi(seed, adrs, vals)

def T_k(seed, adrs, roots):
    return th_multi(seed, adrs, roots)

def h_msg(seed, root, R, message):
    """keccak(seed32 || root32 || R32 || msg32 || domain32) — full 256-bit output."""
    return keccak256(to_b32(seed) + to_b32(root) + to_b32(R) +
                     to_b32(message) + to_b32(HMSG_DOMAIN_SPX))

# ============================================================
#  Digest parsing (LSB-first, matches JARDIN family)
# ============================================================

def digest_indices(d_int: int):
    md = [(d_int >> (7 * t)) & A_MASK for t in range(K)]
    tree_idx = (d_int >> (K * A)) & TREE_TOP_MASK      # bits 140..155
    leaf_idx = (d_int >> (K * A + TREE_TOP_BITS)) & H_PRIME_MASK  # bits 156..159
    return md, tree_idx, leaf_idx

# ============================================================
#  base_w + WOTS+ checksum
# ============================================================

def base_w_node(node_int: int):
    """Extract 42 base-w=8 digits from the 128-bit node value (LSB-first).
    node_int has the 128-bit value in its high 16 bytes (low 16 zeroed)."""
    # value occupies bits 128..255 of node_int
    v = node_int >> 128
    return [(v >> (3 * i)) & W_MASK for i in range(L1)]

def wots_checksum(msg_digits):
    assert len(msg_digits) == L1
    csum = sum((W - 1) - d for d in msg_digits)
    # byte-align: l2·lg(w) = 9 bits; ceil to 16; shift by 16-9 = 7
    csum_shifted = csum << 7
    # MSB-first 3-bit chunks (SLH-DSA base_w)
    return [(csum_shifted >> (13 - 3 * j)) & W_MASK for j in range(L2)]

def wots_digits(node_int):
    md = base_w_node(node_int)
    cs = wots_checksum(md)
    return md + cs

# ============================================================
#  Key derivation
# ============================================================

def derive_spx_keys(master_sk: bytes):
    """Derive (sk_seed, sk_prf, pk_seed) — each is a 256-bit int with the
    128-bit value in the HIGH 16 bytes (low 16 bytes zero)."""
    def to_high(b16):
        return int.from_bytes(b16 + b"\x00" * 16, "big")
    sk_seed = to_high(hmac512(master_sk, b"JARDIN/SPX/SKSEED")[:N])
    sk_prf  = to_high(hmac512(master_sk, b"JARDIN/SPX/SKPRF" )[:N])
    pk_seed = to_high(hmac512(master_sk, b"JARDIN/SPX/PKSEED")[:N])
    return sk_seed, sk_prf, pk_seed

def wots_secret(sk_seed, layer, tree, kp, chain_idx):
    data = to_b32(sk_seed) + b"spx_wots" + to_b4(layer) + tree.to_bytes(8, "big") + \
           to_b4(kp) + to_b4(chain_idx)
    return keccak256(data) & N_MASK

def fors_secret(sk_seed, ht_tree, ht_leaf, fors_t, j):
    """FORS leaf secret for leaf j of FORS tree fors_t of the FORS instance at
    hypertree position (ht_tree, ht_leaf).

    The position MUST be in the PRF input. Every one of the 2^h FORS instances
    under a key needs its own secrets; if the PRF only takes (fors_t, j), all
    instances share one table of K * 2^A secrets. The verifier binds the FORS
    ADRS to the position, but that does not help: a leaf is F(pkSeed, ADRS, sk)
    and pkSeed / ADRS are public, so a secret revealed at one position rebuilds
    the matching leaf at every other position. About 1,000 honest signatures
    then fill the whole table and allow a universal forgery (grind R until
    H_msg lands on a position that already has an honest hypertree signature).
    This matches script/signer.py (ht_idx folded in) and the FIPS 205 PRF over
    ADRS(FORS_PRF, tree, kp, ...) used by slh_dsa_sha2_c12_signer.py.
    """
    data = (to_b32(sk_seed) + b"spx_fors" + ht_tree.to_bytes(8, "big") +
            to_b4(ht_leaf) + to_b4(fors_t) + to_b4(j))
    return keccak256(data) & N_MASK

def derive_R(sk_prf, message, sig_counter):
    return keccak256(to_b32(sk_prf) + b"spx_R" + to_b32(message) +
                     to_b4(sig_counter)) & N_MASK

# ============================================================
#  WOTS+
# ============================================================

def wots_chain(seed, layer, tree, kp, chain_i, x_start, steps, val):
    v = val
    for s in range(steps):
        adrs = make_adrs(layer, tree, ADRS_WOTS_HASH, kp, chain_i, x_start + s, 0)
        v = F(seed, adrs, v)
    return v

def wots_keygen(seed, sk_seed, layer, tree, kp):
    sks = []
    tops = []
    for i in range(L):
        sk_i = wots_secret(sk_seed, layer, tree, kp, i)
        sks.append(sk_i)
        tops.append(wots_chain(seed, layer, tree, kp, i, 0, W - 1, sk_i))
    pk_adrs = make_adrs(layer, tree, ADRS_WOTS_PK, kp, 0, 0, 0)
    return sks, T_l(seed, pk_adrs, tops)

def wots_sign(seed, sks, layer, tree, kp, msg_int):
    digits = wots_digits(msg_int)
    sigma = [wots_chain(seed, layer, tree, kp, i, 0, digits[i], sks[i]) for i in range(L)]
    return sigma, digits

def wots_pk_from_sig(seed, sigma, layer, tree, kp, msg_int):
    digits = wots_digits(msg_int)
    tops = [wots_chain(seed, layer, tree, kp, i, digits[i], W - 1 - digits[i], sigma[i])
            for i in range(L)]
    pk_adrs = make_adrs(layer, tree, ADRS_WOTS_PK, kp, 0, 0, 0)
    return T_l(seed, pk_adrs, tops)

# ============================================================
#  XMSS per layer (h' = 4 ⇒ 16 WOTS keypairs per tree)
# ============================================================

def build_xmss_tree(seed, sk_seed, layer, tree):
    n_leaves = 1 << H_PRIME
    wots_sks = []
    leaves = []
    for kp in range(n_leaves):
        sks, pk = wots_keygen(seed, sk_seed, layer, tree, kp)
        wots_sks.append(sks)
        leaves.append(pk)
    nodes = [leaves]
    for h in range(H_PRIME):
        prev = nodes[h]
        level = []
        for idx in range(0, len(prev), 2):
            parent_idx = idx // 2
            adrs = make_adrs(layer, tree, ADRS_XMSS_TREE, 0, 0, h + 1, parent_idx)
            level.append(H_(seed, adrs, prev[idx], prev[idx + 1]))
        nodes.append(level)
    return wots_sks, nodes, nodes[H_PRIME][0]

def xmss_auth_path(nodes, leaf_idx, height):
    path = []
    idx = leaf_idx
    for h in range(height):
        path.append(nodes[h][idx ^ 1])
        idx >>= 1
    return path

# ============================================================
#  FORS (ADRS: layer=0, tree=init_tree_idx, type=3, kp=init_leaf_idx,
#              cp=height, ha=(t<<(A-h))|parent)
# ============================================================

def build_fors_subtree(seed, sk_seed, fors_t, ht_tree, ht_leaf):
    n_leaves = 1 << A
    leaves = []
    for j in range(n_leaves):
        sk = fors_secret(sk_seed, ht_tree, ht_leaf, fors_t, j)
        adrs = make_adrs(0, ht_tree, ADRS_FORS_TREE, ht_leaf, 0, 0, (fors_t << A) | j)
        leaves.append(F(seed, adrs, sk))
    nodes = [leaves]
    for h in range(A):
        prev = nodes[h]
        level = []
        for idx in range(0, len(prev), 2):
            parent_idx = idx // 2
            global_y = (fors_t << (A - h - 1)) | parent_idx
            adrs = make_adrs(0, ht_tree, ADRS_FORS_TREE, ht_leaf, 0, h + 1, global_y)
            level.append(H_(seed, adrs, prev[idx], prev[idx + 1]))
        nodes.append(level)
    return nodes, nodes[A][0]

def build_pk_root(seed, sk_seed):
    """pk_root = XMSS root at top layer (d-1), tree=0."""
    _, _, root = build_xmss_tree(seed, sk_seed, D - 1, 0)
    return root

# ============================================================
#  Signing
# ============================================================

def spx_sign(pk_seed, sk_seed, sk_prf, pk_root, message: int, sig_counter: int = 0):
    R = derive_R(sk_prf, message, sig_counter)
    digest = h_msg(pk_seed, pk_root, R, message)
    md, tree_idx, leaf_idx = digest_indices(digest)
    eprint(f"  digest = {hex(digest)[:18]}..., tree_idx = {tree_idx}, leaf_idx = {leaf_idx}")

    # FORS
    eprint("  Signing FORS...")
    fors_pieces = []   # per-tree (sk, auth_path)
    roots = []
    for t in range(K):
        nodes, root = build_fors_subtree(pk_seed, sk_seed, t, tree_idx, leaf_idx)
        sk = fors_secret(sk_seed, tree_idx, leaf_idx, t, md[t])
        idx = md[t]
        path = []
        for h in range(A):
            path.append(nodes[h][idx ^ 1])
            idx >>= 1
        fors_pieces.append((sk, path))
        roots.append(root)
    roots_adrs = make_adrs(0, tree_idx, ADRS_FORS_ROOTS, leaf_idx, 0, 0, 0)
    fors_pk = T_k(pk_seed, roots_adrs, roots)

    # Hypertree
    eprint("  Signing hypertree...")
    current = fors_pk
    cur_tree = tree_idx
    cur_leaf = leaf_idx
    ht_layers = []
    for layer in range(D):
        eprint(f"    Layer {layer}: tree={cur_tree}, leaf={cur_leaf}")
        wots_sks, tree_nodes, _ = build_xmss_tree(pk_seed, sk_seed, layer, cur_tree)
        sigma, _ = wots_sign(pk_seed, wots_sks[cur_leaf], layer, cur_tree, cur_leaf, current)
        auth = xmss_auth_path(tree_nodes, cur_leaf, H_PRIME)
        ht_layers.append((sigma, auth))

        wots_pk = wots_pk_from_sig(pk_seed, sigma, layer, cur_tree, cur_leaf, current)
        node = wots_pk
        m_idx = cur_leaf
        for h in range(H_PRIME):
            sib = auth[h]
            parent_idx = m_idx >> 1
            adrs = make_adrs(layer, cur_tree, ADRS_XMSS_TREE, 0, 0, h + 1, parent_idx)
            node = H_(pk_seed, adrs, node, sib) if (m_idx & 1) == 0 else H_(pk_seed, adrs, sib, node)
            m_idx = parent_idx
        current = node
        cur_leaf = cur_tree & H_PRIME_MASK
        cur_tree = cur_tree >> H_PRIME

    if current != pk_root:
        raise AssertionError(f"sign: root mismatch {hex(current)} vs {hex(pk_root)}")

    # Serialize
    out = bytearray()
    out += to_b32(R)[:R_LEN]   # 32 bytes
    for sk, path in fors_pieces:
        out += to_b32(sk)[:N]
        for node in path:
            out += to_b32(node)[:N]
    for sigma, auth in ht_layers:
        for chain_v in sigma:
            out += to_b32(chain_v)[:N]
        for node in auth:
            out += to_b32(node)[:N]
    assert len(out) == SIG_LEN, f"sig len {len(out)} != {SIG_LEN}"
    return bytes(out)

# ============================================================
#  Local verifier (mirror of on-chain Yul, byte-for-byte)
# ============================================================

def spx_verify(pk_seed, pk_root, message: int, sig: bytes) -> bool:
    assert len(sig) == SIG_LEN, f"len {len(sig)} != {SIG_LEN}"
    R = int.from_bytes(sig[:R_LEN], "big")
    digest = h_msg(pk_seed, pk_root, R, message)
    md, tree_idx, leaf_idx = digest_indices(digest)

    # FORS
    fors_off = R_LEN
    roots = []
    for t in range(K):
        sk = int.from_bytes(sig[fors_off:fors_off + N] + b"\x00" * 16, "big")
        auth = [int.from_bytes(sig[fors_off + N + j * N : fors_off + N + (j + 1) * N] + b"\x00" * 16, "big")
                for j in range(A)]
        fors_off += FORS_TREE_LEN

        adrs = make_adrs(0, tree_idx, ADRS_FORS_TREE, leaf_idx, 0, 0, (t << A) | md[t])
        node = F(pk_seed, adrs, sk)
        idx = md[t]
        for j in range(A):
            sib = auth[j]
            parent_idx = idx >> 1
            global_y = (t << (A - j - 1)) | parent_idx
            adrs = make_adrs(0, tree_idx, ADRS_FORS_TREE, leaf_idx, 0, j + 1, global_y)
            node = H_(pk_seed, adrs, node, sib) if (idx & 1) == 0 else H_(pk_seed, adrs, sib, node)
            idx = parent_idx
        roots.append(node)
    roots_adrs = make_adrs(0, tree_idx, ADRS_FORS_ROOTS, leaf_idx, 0, 0, 0)
    current = T_k(pk_seed, roots_adrs, roots)

    # Hypertree
    ht_off = R_LEN + FORS_BODY_LEN
    cur_tree = tree_idx
    cur_leaf = leaf_idx
    for layer in range(D):
        base = ht_off + layer * HT_LAYER_LEN
        sigma = [int.from_bytes(sig[base + i * N : base + (i + 1) * N] + b"\x00" * 16, "big")
                 for i in range(L)]
        auth  = [int.from_bytes(sig[base + L * N + j * N : base + L * N + (j + 1) * N] + b"\x00" * 16, "big")
                 for j in range(H_PRIME)]
        wots_pk = wots_pk_from_sig(pk_seed, sigma, layer, cur_tree, cur_leaf, current)
        node = wots_pk
        m_idx = cur_leaf
        for h in range(H_PRIME):
            sib = auth[h]
            parent_idx = m_idx >> 1
            adrs = make_adrs(layer, cur_tree, ADRS_XMSS_TREE, 0, 0, h + 1, parent_idx)
            node = H_(pk_seed, adrs, node, sib) if (m_idx & 1) == 0 else H_(pk_seed, adrs, sib, node)
            m_idx = parent_idx
        current = node
        cur_leaf = cur_tree & H_PRIME_MASK
        cur_tree = cur_tree >> H_PRIME

    return current == pk_root

# ============================================================
#  CLI
# ============================================================

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def abi_encode(seed, root, sig):
    enc = to_b32(seed) + to_b32(root) + to_b32(0x60) + to_b32(len(sig))
    enc += sig + b"\x00" * ((32 - len(sig) % 32) % 32)
    return enc

def main():
    if len(sys.argv) < 3:
        eprint("Usage: jardin_spx_signer.py <master_sk_hex> <message_hex> [sig_counter]")
        sys.exit(1)
    master_sk = bytes.fromhex(sys.argv[1].replace("0x", ""))
    if len(master_sk) != 32:
        eprint("master_sk must be 32 bytes"); sys.exit(1)
    msg_hex = sys.argv[2].replace("0x", "")
    if len(msg_hex) % 2:
        msg_hex = "0" + msg_hex
    message = int(msg_hex, 16) if msg_hex else 0
    sig_counter = int(sys.argv[3]) if len(sys.argv) > 3 else 0

    t0 = time.time()
    sk_seed, sk_prf, pk_seed = derive_spx_keys(master_sk)
    eprint(f"  pk_seed = {hex(pk_seed)[:18]}...")
    eprint(f"  Building top-layer XMSS (layer={D-1}, {1 << H_PRIME} WOTS keypairs)...")
    pk_root = build_pk_root(pk_seed, sk_seed)
    eprint(f"  pk_root = {hex(pk_root)[:18]}...")

    eprint(f"  Signing at sig_counter={sig_counter}...")
    sig = spx_sign(pk_seed, sk_seed, sk_prf, pk_root, message, sig_counter)
    assert spx_verify(pk_seed, pk_root, message, sig), "local verify failed"
    eprint(f"  Local verify OK. Sig: {len(sig)} bytes. Total: {time.time() - t0:.1f}s")

    print("0x" + abi_encode(pk_seed, pk_root, sig).hex())

if __name__ == "__main__":
    main()
