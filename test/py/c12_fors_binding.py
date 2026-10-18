#!/usr/bin/env python3
"""Regression helper for the C12 FORS PRF position binding.

Usage: python3 test/py/c12_fors_binding.py <keccak|blake>

Uses the real C12 signer (script/spx_fips_signer.py or script/spx_blake_signer.py).
It looks for two honest signatures A and B at different hypertree positions that
open the same FORS slot (t, j), signs both, and prints
    abi.encode(seed, root, msgA, sigA, msgB, sigB, sigBTransplanted, t)
where sigBTransplanted is sigB with the FORS secret of tree t replaced by the one
revealed in sigA. With a position-bound FORS PRF the two secrets differ, so the
transplanted signature must fail on chain. With the old position-free PRF the
secrets were byte-identical and the "transplant" was a no-op that still verified,
which is the building block of the harvest-and-forge attack.
"""
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "script"))

backend = sys.argv[1] if len(sys.argv) > 1 else "keccak"
if backend == "blake":
    import spx_blake_signer  # noqa: F401  (configures the shared module for C12-BLAKE)
elif backend == "keccak":
    import spx_fips_signer  # noqa: F401  (configures the shared module for C12)
else:
    sys.exit(f"unknown backend {backend}")
import jardin_spx_signer as spx
from jardin_primitives import keccak256, to_b32

spx.eprint = lambda *a, **k: None

MASTER_SK = bytes.fromhex("11" * 32)
sk_seed, sk_prf, pk_seed = spx.derive_spx_keys(MASTER_SK)
pk_root = spx.build_pk_root(pk_seed, sk_seed)


def position(msg):
    R = spx.derive_R(sk_prf, msg, 0)
    md, tree, leaf = spx.digest_indices(spx.h_msg(pk_seed, pk_root, R, msg))
    return md, (tree, leaf)


def find_pair():
    seen = []
    for i in range(10_000):
        m = keccak256(b"c12-fors-binding " + i.to_bytes(4, "big"))
        md, pos = position(m)
        for (m2, md2, pos2) in seen:
            if pos2 == pos:
                continue
            for t in range(spx.K):
                if md[t] == md2[t]:
                    return m2, m, t
        seen.append((m, md, pos))
    raise RuntimeError("no shared FORS slot found")


msg_a, msg_b, t = find_pair()
sig_a = spx.spx_sign(pk_seed, sk_seed, sk_prf, pk_root, msg_a, 0)
sig_b = spx.spx_sign(pk_seed, sk_seed, sk_prf, pk_root, msg_b, 0)
off = spx.R_LEN + t * spx.FORS_TREE_LEN
sig_bt = sig_b[:off] + sig_a[off:off + spx.N] + sig_b[off + spx.N:]
assert len(sig_bt) == len(sig_b)


def enc_bytes(b):
    return to_b32(len(b)) + b + b"\x00" * ((32 - len(b) % 32) % 32)


heads = [to_b32(pk_seed), to_b32(pk_root), to_b32(msg_a), None, to_b32(msg_b), None, None, to_b32(t)]
tails = {3: sig_a, 5: sig_b, 6: sig_bt}
out_head = b""
out_tail = b""
base = 32 * len(heads)
for i, h in enumerate(heads):
    if h is None:
        out_head += to_b32(base + len(out_tail))
        out_tail += enc_bytes(tails[i])
    else:
        out_head += h
print("0x" + (out_head + out_tail).hex())
