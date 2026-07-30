#!/usr/bin/env python3
"""
C12-SHA signer — full FIPS 205 SLH-DSA-SHA2 algorithm at the C12 parameter set.

C12 is plain SPHINCS+ (SPX), so unlike the WOTS+C/FORS+C compact variants it can
take the *full* FIPS 205 SHA-2 instantiation. This signer is the SHA-2 twin of
the keccak C12 (script/spx_fips_signer.py): same hypertree shape, but FIPS-faithful
hashing and parsing — SHA-256 + 22-byte ADRSc, MGF1 H_msg, 0x00‖0x00 empty-context
envelope, and MSB-first base_2b digit/index parsing.

It is the d=5 generalisation of script/slh_dsa_sha2_128_24_signer.py (d=1) with
w=8 WOTS. NOT a NIST parameter set (params differ from the 12 standardized sets),
so it won't match published KATs — it's a true SLH-DSA *algorithm* at research
params. Drives src/sha/SPHINCs-C12-SHA.sol.

Parameters: n=16 h=20 d=5 h'=4 a=7 k=20 w=8 (lgw=3) l1=43 l2=3 l=46, m=21.
Signature layout (6,576 B): R(16) | FORS 20×(sk 16 + auth 7·16)=2560 |
                            HT 5×(WOTS 46·16 + XMSS auth 4·16)=4000

Usage: python3 script/slh_dsa_sha2_c12_signer.py <master_sk_hex> <message_hex> [sig_counter]
Output: ABI-encoded (bytes32 seed, bytes32 root, bytes sig) hex on stdout.
"""

import sys, time, hmac, hashlib, struct

N = 16
H = 20
D = 5
H_PRIME = 4
A = 7
K = 20
W = 8
LOG_W = 3
L1 = 43
L2 = 3
L = 46
M_LEN = ((K * A + 7) // 8) + ((H - H_PRIME + 7) // 8) + ((H_PRIME + 7) // 8)  # 18+2+1 = 21
R_LEN = N

ADRS_WOTS_HASH, ADRS_WOTS_PK, ADRS_TREE = 0, 1, 2
ADRS_FORS_TREE, ADRS_FORS_ROOTS, ADRS_WOTS_PRF, ADRS_FORS_PRF = 3, 4, 5, 6

# ── SHA-256 helpers ─────────────────────────────────────────
def sha256(d): return hashlib.sha256(d).digest()
def hmac_sha256(k, d): return hmac.new(k, d, hashlib.sha256).digest()
def hmac512(k, m): return hmac.new(k, m, hashlib.sha512).digest()

def mgf1_sha256(seed, length):
    out, c = b"", 0
    while len(out) < length:
        out += sha256(seed + struct.pack(">I", c)); c += 1
    return out[:length]

# ── ADRSc (22-byte compressed ADRS, FIPS 205 §11.2) ─────────
def adrsc(layer, tree, atype, kp=0, chain=0, height=0, tree_index=0):
    out = bytes([layer & 0xFF]) + (tree & ((1 << 64) - 1)).to_bytes(8, "big") + bytes([atype & 0xFF])
    if atype == ADRS_WOTS_HASH:   out += struct.pack(">III", kp, chain, height)
    elif atype == ADRS_WOTS_PK:   out += struct.pack(">I", kp) + b"\x00" * 8
    elif atype == ADRS_TREE:      out += b"\x00" * 4 + struct.pack(">II", height, tree_index)
    elif atype == ADRS_FORS_TREE: out += struct.pack(">III", kp, height, tree_index)
    elif atype == ADRS_FORS_ROOTS:out += struct.pack(">I", kp) + b"\x00" * 8
    elif atype == ADRS_WOTS_PRF:  out += struct.pack(">II", kp, chain) + b"\x00" * 4
    elif atype == ADRS_FORS_PRF:  out += struct.pack(">I", kp) + b"\x00" * 4 + struct.pack(">I", tree_index)
    else: raise ValueError(atype)
    assert len(out) == 22
    return out

# ── Tweakable hashes (PK.seed zero-padded to one SHA block) ──
_PAD48 = b"\x00" * (64 - N)
def F(ps, a, m):  return sha256(ps + _PAD48 + a + m)[:N]
def H_(ps, a, m): return sha256(ps + _PAD48 + a + m)[:N]
def T_l(ps, a, m):return sha256(ps + _PAD48 + a + m)[:N]
def PRF(ps, ss, a): return sha256(ps + _PAD48 + a + ss)[:N]
def PRFmsg(sp, opt, m): return hmac_sha256(sp, opt + m)[:N]

def Hmsg(R, ps, root, M):
    inner = sha256(R + ps + root + M)
    return mgf1_sha256(R + ps + inner, M_LEN)

# ── FIPS 205 base_2b (MSB-first) ────────────────────────────
def base_2b(X, b, out_len):
    res = [0] * out_len; inp = 0; total = 0; bits = 0
    for o in range(out_len):
        while bits < b:
            total = (total << 8) | X[inp]; inp += 1; bits += 8
        bits -= b
        res[o] = (total >> bits) & ((1 << b) - 1)
    return res

def digest_indices(digest):
    fors_bytes = (K * A + 7) // 8       # 18
    tree_bytes = (H - H_PRIME + 7) // 8 # 2
    leaf_bytes = (H_PRIME + 7) // 8     # 1
    md = base_2b(digest[:fors_bytes], A, K)
    idx_tree = int.from_bytes(digest[fors_bytes:fors_bytes + tree_bytes], "big") & ((1 << (H - H_PRIME)) - 1)
    idx_leaf = int.from_bytes(digest[fors_bytes + tree_bytes:fors_bytes + tree_bytes + leaf_bytes], "big") & ((1 << H_PRIME) - 1)
    return md, idx_tree, idx_leaf

# ── WOTS+ (standard checksum, MSB-first) ────────────────────
def wots_checksum(md):
    csum = sum((W - 1) - d for d in md)
    shift = (8 - ((L2 * LOG_W) % 8)) % 8         # 7
    csum_bytes = (L2 * LOG_W + 7) // 8           # 2
    return base_2b((csum << shift).to_bytes(csum_bytes, "big"), LOG_W, L2)

def wots_digits(M):
    # lg(w)=3 does not divide 8*n=128. Append zero padding so digit 42
    # contains the final two message bits followed by one zero bit.
    md = base_2b(M + b"\x00", LOG_W, L1)
    return md + wots_checksum(md)

def wots_secret(ps, ss, layer, tree, kp, chain_i):
    return PRF(ps, ss, adrsc(layer, tree, ADRS_WOTS_PRF, kp=kp, chain=chain_i))

def wots_chain(ps, layer, tree, kp, chain_i, start, steps, val):
    v = val
    for s in range(steps):
        v = F(ps, adrsc(layer, tree, ADRS_WOTS_HASH, kp=kp, chain=chain_i, height=start + s), v)
    return v

def wots_pk_only(ps, ss, layer, tree, kp):
    tops = [wots_chain(ps, layer, tree, kp, i, 0, W - 1, wots_secret(ps, ss, layer, tree, kp, i)) for i in range(L)]
    return T_l(ps, adrsc(layer, tree, ADRS_WOTS_PK, kp=kp), b"".join(tops))

def wots_keygen(ps, ss, layer, tree, kp):
    sks = [wots_secret(ps, ss, layer, tree, kp, i) for i in range(L)]
    tops = [wots_chain(ps, layer, tree, kp, i, 0, W - 1, sks[i]) for i in range(L)]
    return sks, T_l(ps, adrsc(layer, tree, ADRS_WOTS_PK, kp=kp), b"".join(tops))

def wots_sign(ps, sks, layer, tree, kp, M):
    digits = wots_digits(M)
    return [wots_chain(ps, layer, tree, kp, i, 0, digits[i], sks[i]) for i in range(L)]

def wots_pk_from_sig(ps, sigma, layer, tree, kp, M):
    digits = wots_digits(M)
    tops = [wots_chain(ps, layer, tree, kp, i, digits[i], W - 1 - digits[i], sigma[i]) for i in range(L)]
    return T_l(ps, adrsc(layer, tree, ADRS_WOTS_PK, kp=kp), b"".join(tops))

# ── XMSS (per layer, h'=4 → 16 leaves) ──────────────────────
def build_xmss(ps, ss, layer, tree):
    leaves, sks_per = [], []
    for kp in range(1 << H_PRIME):
        sks, pk = wots_keygen(ps, ss, layer, tree, kp)
        sks_per.append(sks); leaves.append(pk)
    nodes = [leaves]
    for h in range(H_PRIME):
        prev = nodes[h]; lvl = []
        for i in range(0, len(prev), 2):
            adr = adrsc(layer, tree, ADRS_TREE, height=h + 1, tree_index=i // 2)
            lvl.append(H_(ps, adr, prev[i] + prev[i + 1]))
        nodes.append(lvl)
    return sks_per, nodes, nodes[H_PRIME][0]

def xmss_auth(nodes, leaf):
    path, idx = [], leaf
    for h in range(H_PRIME):
        path.append(nodes[h][idx ^ 1]); idx >>= 1
    return path

# ── FORS (k=20 trees of 2^7 leaves; ADRS tree=idx_tree kp=idx_leaf) ──
def fors_secret(ps, ss, idx_tree, idx_leaf, fors_t, j):
    return PRF(ps, ss, adrsc(0, idx_tree, ADRS_FORS_PRF, kp=idx_leaf, tree_index=(fors_t << A) | j))

def build_fors_tree(ps, ss, idx_tree, idx_leaf, fors_t, open_leaf):
    auth = [None] * A; sk_open = None; nodes_leaves = []
    for j in range(1 << A):
        sk = fors_secret(ps, ss, idx_tree, idx_leaf, fors_t, j)
        if j == open_leaf: sk_open = sk
        adr = adrsc(0, idx_tree, ADRS_FORS_TREE, kp=idx_leaf, height=0, tree_index=(fors_t << A) | j)
        nodes_leaves.append(F(ps, adr, sk))
    nodes = [nodes_leaves]
    for h in range(A):
        prev = nodes[h]; lvl = []
        for i in range(0, len(prev), 2):
            parent = i // 2
            gy = (fors_t << (A - h - 1)) | parent
            adr = adrsc(0, idx_tree, ADRS_FORS_TREE, kp=idx_leaf, height=h + 1, tree_index=gy)
            lvl.append(H_(ps, adr, prev[i] + prev[i + 1]))
        nodes.append(lvl)
    idx = open_leaf
    for h in range(A):
        auth[h] = nodes[h][idx ^ 1]; idx >>= 1
    return auth, nodes[A][0], sk_open

# ── Key derivation (JARDIN convention, distinct from NIST) ───
def derive_keys(master_sk):
    ss = hmac512(master_sk, b"JARDIN/C12SHA/SKSEED")[:N]
    sp = hmac512(master_sk, b"JARDIN/C12SHA/SKPRF")[:N]
    ps = hmac512(master_sk, b"JARDIN/C12SHA/PKSEED")[:N]
    return ss, sp, ps

def build_pk_root(ps, ss):
    _, _, root = build_xmss(ps, ss, D - 1, 0)
    return root

# ── Sign ────────────────────────────────────────────────────
def eprint(*a, **k): print(*a, file=sys.stderr, **k)

def slh_sign(ps, ss, sp, pk_root, M, sig_counter):
    opt = struct.pack(">I", sig_counter) + b"\x00" * (N - 4)
    R = PRFmsg(sp, opt, M)
    digest = Hmsg(R, ps, pk_root, M)
    md, idx_tree, idx_leaf = digest_indices(digest)
    eprint(f"  idx_tree={idx_tree} idx_leaf={idx_leaf}")

    # FORS
    fors_pieces, fors_roots = [], []
    for t in range(K):
        auth, root, sk = build_fors_tree(ps, ss, idx_tree, idx_leaf, t, md[t])
        fors_pieces.append((sk, auth)); fors_roots.append(root)
    fors_pk = T_l(ps, adrsc(0, idx_tree, ADRS_FORS_ROOTS, kp=idx_leaf), b"".join(fors_roots))

    # Hypertree (d=5)
    ht_layers = []
    current = fors_pk
    cur_tree, cur_leaf = idx_tree, idx_leaf
    for layer in range(D):
        sks_per, nodes, _ = build_xmss(ps, ss, layer, cur_tree)
        sigma = wots_sign(ps, sks_per[cur_leaf], layer, cur_tree, cur_leaf, current)
        auth = xmss_auth(nodes, cur_leaf)
        ht_layers.append((sigma, auth))
        # advance: recompute this layer's root from sigma to get the next message
        wpk = wots_pk_from_sig(ps, sigma, layer, cur_tree, cur_leaf, current)
        node = wpk; m_idx = cur_leaf
        for h in range(H_PRIME):
            adr = adrsc(layer, cur_tree, ADRS_TREE, height=h + 1, tree_index=m_idx >> 1)
            node = H_(ps, adr, node + auth[h]) if (m_idx & 1) == 0 else H_(ps, adr, auth[h] + node)
            m_idx >>= 1
        current = node
        cur_leaf = cur_tree & ((1 << H_PRIME) - 1)
        cur_tree >>= H_PRIME
    if current != pk_root:
        raise AssertionError(f"sign root mismatch {current.hex()} vs {pk_root.hex()}")

    out = bytearray()
    out += R
    for sk, auth in fors_pieces:
        out += sk
        for nd in auth: out += nd
    for sigma, auth in ht_layers:
        for s in sigma: out += s
        for nd in auth: out += nd
    assert len(out) == R_LEN + K * (N + A * N) + D * (L * N + H_PRIME * N), len(out)
    return bytes(out)

# ── Local verify (mirror of on-chain Yul) ───────────────────
def slh_verify(ps, pk_root, M, sig):
    R = sig[:R_LEN]
    digest = Hmsg(R, ps, pk_root, M)
    md, idx_tree, idx_leaf = digest_indices(digest)
    fors_tree_len = N + A * N
    off = R_LEN
    roots = []
    for t in range(K):
        sk = sig[off:off + N]
        auth = [sig[off + N + j * N: off + N + (j + 1) * N] for j in range(A)]
        off += fors_tree_len
        node = F(ps, adrsc(0, idx_tree, ADRS_FORS_TREE, kp=idx_leaf, height=0, tree_index=(t << A) | md[t]), sk)
        idx = md[t]
        for j in range(A):
            parent = idx >> 1
            gy = (t << (A - j - 1)) | parent
            adr = adrsc(0, idx_tree, ADRS_FORS_TREE, kp=idx_leaf, height=j + 1, tree_index=gy)
            node = H_(ps, adr, node + auth[j]) if (idx & 1) == 0 else H_(ps, adr, auth[j] + node)
            idx = parent
        roots.append(node)
    current = T_l(ps, adrsc(0, idx_tree, ADRS_FORS_ROOTS, kp=idx_leaf), b"".join(roots))

    cur_tree, cur_leaf = idx_tree, idx_leaf
    for layer in range(D):
        sigma = [sig[off + i * N: off + (i + 1) * N] for i in range(L)]
        auth = [sig[off + L * N + j * N: off + L * N + (j + 1) * N] for j in range(H_PRIME)]
        off += L * N + H_PRIME * N
        wpk = wots_pk_from_sig(ps, sigma, layer, cur_tree, cur_leaf, current)
        node = wpk; m_idx = cur_leaf
        for h in range(H_PRIME):
            adr = adrsc(layer, cur_tree, ADRS_TREE, height=h + 1, tree_index=m_idx >> 1)
            node = H_(ps, adr, node + auth[h]) if (m_idx & 1) == 0 else H_(ps, adr, auth[h] + node)
            m_idx >>= 1
        current = node
        cur_leaf = cur_tree & ((1 << H_PRIME) - 1)
        cur_tree >>= H_PRIME
    return current == pk_root

# ── CLI ─────────────────────────────────────────────────────
def abi_encode(seed, root, sig):
    enc = seed + b"\x00" * (32 - N) + root + b"\x00" * (32 - N)
    enc += (0x60).to_bytes(32, "big") + len(sig).to_bytes(32, "big")
    enc += sig + b"\x00" * ((32 - len(sig) % 32) % 32)
    return enc

def main():
    if len(sys.argv) < 3:
        eprint("Usage: slh_dsa_sha2_c12_signer.py <master_sk_hex> <message_hex> [sig_counter]"); sys.exit(1)
    master_sk = bytes.fromhex(sys.argv[1].replace("0x", ""))
    if len(master_sk) != 32: eprint("master_sk must be 32 bytes"); sys.exit(1)
    mh = sys.argv[2].replace("0x", "")
    if len(mh) % 2: mh = "0" + mh
    msg_raw = bytes.fromhex(mh) if mh else b""
    M = b"\x00\x00" + msg_raw   # FIPS external SLH-DSA, empty context
    sig_counter = int(sys.argv[3]) if len(sys.argv) > 3 else 0

    t0 = time.time()
    ss, sp, ps = derive_keys(master_sk)
    pk_root = build_pk_root(ps, ss)
    eprint(f"  pk_root = 0x{pk_root.hex()[:16]}…")
    sig = slh_sign(ps, ss, sp, pk_root, M, sig_counter)
    assert slh_verify(ps, pk_root, M, sig), "local verify failed"
    eprint(f"  Local verify OK. Sig {len(sig)} B. {time.time()-t0:.1f}s")
    print("0x" + abi_encode(ps, pk_root, sig).hex())

if __name__ == "__main__":
    main()
