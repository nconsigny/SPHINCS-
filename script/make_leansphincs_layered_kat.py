#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>
"""Regenerate test/fixtures/leansphincs-layered-keccak-kat.json, the fixture test/LeanSphincsLayeredTest.t.sol
and test/SphincsAccountLeanSphincsLayeredTest.t.sol read.

Each vector is a key and a signature from the Python reference signer (script/leansphincs_layered_signer.py,
which reproduces every EthLib vector and the Lean known answer byte for byte), with the values verification
computes from it (idx, the 24 FORS leaves, the three counters) and, per layer, three counter substitutions
that isolate that layer's WOTS+C target-sum check:

    isolate[L] = {"below": ..., "above": ..., "other": ...}   L = 0 bottom, 1 middle, 2 top

Each substitution sets layer L's counter to the least counter whose codeword sums to exactly T - 1 ("below"),
exactly T + 1 ("above"), or T but is not the signed one ("other"), then re-grinds every layer above L (the
least admissible counter for the root the layer below now folds to), keeping every other signature byte. The
off-T sums sit on the boundary, so a check that is off by one on either side fails on them (a counter merely
below T almost always sums far below it: the mean digit sum is 96). It
records the three counters, the three codeword sums, and the root the spec model folds the result to with
no target-sum check. So under that root, layer L's check is the only thing that can reject the "below" and
"above" signatures, and the "other" signature must verify (the chain values are not a valid signature of
the new codeword, and only the target sum is checked: the spec says nothing more).

Keygen and signing are deterministic, so rerunning this script reproduces the committed file byte for byte;
--check fails if it would change. Vectors are picked so that the fixture holds both values of bit 25 of idx
(the top path's last node, the last 16 signature bytes, is the left child exactly when it is 1) and of bit 9
of u_23 (the order of tree 23's FORS key pair, the last FORS store before the bottom counter).

Usage (pycryptodome is needed; the repo venv has it, about a minute):
    .venv/bin/python script/make_leansphincs_layered_kat.py [--check]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import leansphincs_layered_signer as L  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE = REPO_ROOT / "test" / "fixtures" / "leansphincs-layered-keccak-kat.json"

SEEDS = {
    "x11": b"\x11" * 32,
    "ramp": bytes(range(32)),
    "zero": bytes(32),
    "ff": b"\xff" * 32,
    "kat-seed": L.keccak256(b"leanSphincs-layered KAT seed"),
}
MSGS = {
    "zero": bytes(32),
    "ff": b"\xff" * 32,
    "deadbeef": bytes.fromhex("deadbeef") * 8,
    "kat-msg": L.keccak256(b"leanSphincs-layered KAT message"),
}
LABELS = {
    "x11": "0x11 x 32",
    "ramp": "0x00 01 .. 1f",
    "zero": "0x00 x 32",
    "ff": "0xff x 32",
    "deadbeef": "0xdeadbeef x 8",
    "kat-seed": 'keccak256("leanSphincs-layered KAT seed")',
    "kat-msg": 'keccak256("leanSphincs-layered KAT message")',
}
BASE = [("x11", "zero"), ("ramp", "kat-msg"), ("zero", "ff"), ("ff", "deadbeef"), ("kat-seed", "kat-msg"), ("kat-seed", "zero")]
COVERAGE_SEED = "kat-seed"
MAX_VECTORS = 10

EVEN_MASK = int("AA" * 16, 16)  # the high bit of every 2-bit digit


def digit_sum(d: bytes) -> int:
    """Σ x_i of the 64 2-bit digits: each digit is its low bit plus twice its high bit."""
    v = int.from_bytes(d, "little")
    return v.bit_count() + (v & EVEN_MASK).bit_count()


def least_counter(pp: bytes, key: L.OtsKey, msg: bytes, pred, start: int = 0, skip=None) -> int:
    prefix = pp + L.addr_encoding(key) + msg
    for c in range(start, 2**32):
        if c == skip:
            continue
        if pred(digit_sum(L.half_of(0, L.keccak256(prefix + c.to_bytes(4, "little"))))):
            return c
    raise RuntimeError("no counter")


def model(pp: bytes, m: bytes, sig: L.Signature):
    """Verification with no target-sum check: the roots of the three layers and their codeword sums."""
    d = L.message_digest(pp, m, sig.randomizer)
    idx = L.digest_index(d)
    leaves = L.digest_leaves(d)
    msg = L.fors_key_bytes([L.tree_recover(pp, idx, k, leaves[k], sig.fors[k]) for k in range(L.FORS_TREES)])
    roots, sums, msgs = [], [], []
    for layer in (L.BOTTOM, L.MIDDLE, L.TOP):
        key = L.ots_key_of_index(layer, idx)
        s = sig.layers[layer]
        dg = L.th(pp, L.addr_encoding(key), msg + s.counter.to_bytes(4, "little"))
        x = L.digits(dg)
        ends = [L.chain(pp, key, i, x[i], L.CHAIN_LENGTH - 1 - x[i], s.chain_values[i]) for i in range(L.V)]
        root = L.tree_fold(pp, layer, key.tree, key.leaf, L.ots_leaf_hash(pp, key, ends), s.path)
        msgs.append(msg)
        roots.append(root)
        sums.append(sum(x))
        msg = root
    return idx, leaves, msgs, roots, sums


def isolate(pp: bytes, m: bytes, sig: L.Signature, layer: int, kind: str):
    """Counters that make layer `layer` the only inadmissible one ("below"/"above"), or a second
    admissible signature ("other"), with every layer above re-ground."""
    _, _, msgs, _, sums = model(pp, m, sig)
    assert sums == [L.TARGET_SUM] * 3
    idx = model(pp, m, sig)[0]
    key = L.ots_key_of_index(layer, idx)
    honest = sig.layers[layer].counter
    T = L.TARGET_SUM
    if kind == "below":
        c = least_counter(pp, key, msgs[layer], lambda s: s == T - 1)
    elif kind == "above":
        c = least_counter(pp, key, msgs[layer], lambda s: s == T + 1)
    else:
        c = least_counter(pp, key, msgs[layer], lambda s: s == T, skip=honest)
    new = L.Signature(sig.randomizer, sig.fors, [L.LayerSignature(s.counter, s.chain_values, s.path) for s in sig.layers])
    new.layers[layer].counter = c
    for above in range(layer + 1, L.LAYERS):
        _, _, msgs2, _, _ = model(pp, m, new)
        k2 = L.ots_key_of_index(above, idx)
        new.layers[above].counter = least_counter(pp, k2, msgs2[above], lambda s: s == T)
    _, _, _, roots, sums = model(pp, m, new)
    want = [T] * 3
    want[layer] = {"below": T - 1, "above": T + 1, "other": T}[kind]
    assert sums == want, (layer, kind, sums)
    # The reference verifier agrees: "other" verifies under its model root, the other two do not.
    sig_bytes = L.encode_signature(new)
    ok = L.verify(roots[2] + pp, m, sig_bytes)
    assert ok == (kind == "other"), (layer, kind, ok)
    return {
        "counters": [s.counter for s in new.layers],
        "sums": sums,
        "modelRoot": "0x" + (roots[2] + bytes(16)).hex(),
    }


def make_vector(seed_name: str, msg_name: str, signers: dict) -> dict:
    seed, m = SEEDS[seed_name], MSGS.get(msg_name)
    if m is None:
        m = L.keccak256(f"leanSphincs-layered KAT coverage {msg_name}".encode())
    if seed_name not in signers:
        signers[seed_name] = L.Signer.from_seed(seed)
    s = signers[seed_name]
    sig_bytes = s.sign(m)
    pk = s.public_key()
    assert L.verify(pk, m, sig_bytes)
    assert not L.verify(pk, bytes([m[0] ^ 1]) + m[1:], sig_bytes)
    sig = L.decode_signature(sig_bytes)
    idx, leaves, _, roots, sums = model(s.pp, m, sig)
    assert roots[2] == s.root and sums == [L.TARGET_SUM] * 3
    msg_label = LABELS.get(msg_name, f'keccak256("leanSphincs-layered KAT coverage {msg_name}")')
    return {
        "label": f"seed {LABELS[seed_name]}, message {msg_label}",
        "seed": "0x" + seed.hex(),
        "message": "0x" + m.hex(),
        "publicKey": "0x" + pk.hex(),
        "pkSeed": "0x" + (s.pp + bytes(16)).hex(),
        "pkRoot": "0x" + (s.root + bytes(16)).hex(),
        "sig": "0x" + sig_bytes.hex(),
        "idx": idx,
        "fors_indices": leaves,
        "counters": [layer.counter for layer in sig.layers],
        "isolate": [{kind: isolate(s.pp, m, sig, layer, kind) for kind in ("below", "above", "other")} for layer in range(3)],
    }


def digest_bits(seed_name: str, m: bytes, signers: dict):
    """idx and u_23 of the signature of m, from the digest alone (cheap: no signing)."""
    if seed_name not in signers:
        signers[seed_name] = L.Signer.from_seed(SEEDS[seed_name])
    s = signers[seed_name]
    rho = L.randomizer(s.pp, s.seed, m)
    d = L.message_digest(s.pp, m, rho)
    return L.digest_index(d), L.digest_leaves(d)[23]


def build() -> dict:
    signers: dict = {}
    pairs = list(BASE)
    have = set()
    for seed_name, msg_name in pairs:
        idx, u23 = digest_bits(seed_name, MSGS[msg_name], signers)
        have.add(("idx25", (idx >> 25) & 1))
        have.add(("u23b9", (u23 >> 9) & 1))
    need = {("idx25", 0), ("idx25", 1), ("u23b9", 0), ("u23b9", 1)}
    i = 0
    while not need <= have:
        m = L.keccak256(f"leanSphincs-layered KAT coverage {i}".encode())
        idx, u23 = digest_bits(COVERAGE_SEED, m, signers)
        new = {("idx25", (idx >> 25) & 1), ("u23b9", (u23 >> 9) & 1)}
        if not new <= have:
            MSGS[str(i)] = m
            pairs.append((COVERAGE_SEED, str(i)))
            have |= new
        i += 1
    assert len(pairs) <= MAX_VECTORS
    vectors = []
    for seed_name, msg_name in pairs:
        print(f"  signing {seed_name} / {msg_name}", file=sys.stderr)
        vectors.append(make_vector(seed_name, msg_name, signers))
    return {
        "scheme": "leanSPHINCS, layered key for 2^30 signatures, Keccak-256 (EthLib PR #152)",
        "spec": "docs/leanSphincs-layered-keccak.md; normative: EthLib/Cryptography/Sphincs/ at aa99d5f",
        "params": {"n": 16, "h": 26, "layers": [10, 8, 8], "k": 24, "a": 10, "v": 64, "w": 4, "T": 128},
        "key_words": "pkSeed = P || 0^16, pkRoot = root || 0^16 (publicKey = root || P)",
        "signer": "script/leansphincs_layered_signer.py",
        "reproduce": ".venv/bin/python script/make_leansphincs_layered_kat.py",
        "sig_len": L.SIG_SIZE,
        "vectors": vectors,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="fail if the committed fixture would change")
    args = ap.parse_args()
    text = json.dumps(build(), indent=1) + "\n"
    if args.check:
        if FIXTURE.read_text() != text:
            print(f"{FIXTURE} is stale: rerun without --check", file=sys.stderr)
            return 1
        print(f"{FIXTURE} matches", file=sys.stderr)
        return 0
    FIXTURE.write_text(text)
    print(f"wrote {FIXTURE}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
