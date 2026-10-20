#!/usr/bin/env python3
"""
Regenerate test/fixtures/leansphincs-keccak-kat.json, the known-answer
fixture that test/LeanSphincsTest.t.sol reads.

Each vector is the JSON object printed by the Rust signer,
`lsk kat <seed> <b> <message>` (docs/leanSphincs-keccak.md, "the spec"),
plus a short label and `above_target_counter`: the least WOTS+C counter whose
codeword sum EXCEEDS the target T = 120 for that signature's FORS tops (the
merged encoding over the 48 tops, 804 input bytes), which the Forge tests use
to check the Σ > T side of the target-sum check (a random counter gets there
with probability ~3.0e-3). Before writing, every vector is confirmed by the
independent Python signer's spec-literal verifier
(`script/leansphincs_s_signer.py --variant regular --verify`): the signature
must verify, and the same signature over the message with one bit flipped
must not.

Keygen and signing are deterministic, so rerunning this script reproduces the
committed file byte for byte; `--check` fails if it would change. Like
crosscheck.py, it refuses an `lsk` older than the crate sources, with or
without --no-build, so it never writes a fixture the sources do not reproduce.
It also refuses a vector set that lacks either value of bit 25 of idx or of
bit 9 of u_23: each picks between two verifier placements (path[25] as the
left or the right child; the order of the last tree's top pair, the last
store before the counter), and the Forge tests need both sides of each. These
are leanSphincs-S's two guards (bit 11 of u_12 there) at k = 24, a = 10.

Usage (pycryptodome is needed; the repo venv has it):
    .venv/bin/python signers/leansphincs-keccak/make_kat_fixture.py [--check] [--no-build]
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

CRATE_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(CRATE_DIR))
from crosscheck import (  # noqa: E402  (pycryptodome is imported there)
    DEFAULT_LSK as LSK, PY_VARIANT, SCHEME, SIG_LEN, A, H, K, T_SUM, TW_ENC, V, adr, ensure_binary, hx, keccak256,
    spec_recover, th,
)

REPO_ROOT = CRATE_DIR.parents[1]
PY_SIGNER = REPO_ROOT / "script" / "leansphincs_s_signer.py"
FIXTURE = REPO_ROOT / "test" / "fixtures" / "leansphincs-keccak-kat.json"


SEEDS = {
    "x11": b"\x11" * 32,
    "ramp": bytes(range(32)),
    "zero": bytes(32),
    "ff": b"\xff" * 32,
    "kat-seed": keccak256(b"leanSphincs-keccak KAT seed"),
}
MSGS = {
    "zero": bytes(32),
    "ff": b"\xff" * 32,
    "deadbeef": bytes.fromhex("deadbeef") * 8,
    "kat-msg": keccak256(b"leanSphincs-keccak KAT message"),
}
LABELS = {
    "x11": "0x11 x 32",
    "ramp": "0x00 01 .. 1f",
    "zero": "0x00 x 32",
    "ff": "0xff x 32",
    "deadbeef": "0xdeadbeef x 8",
    "kat-seed": 'keccak256("leanSphincs-keccak KAT seed")',
    "kat-msg": 'keccak256("leanSphincs-keccak KAT message")',
}

# (b, seed, message): b in {6, 10, 12}, every seed and message at least once.
VECTORS = [
    (6, "x11", "zero"),
    (6, "ramp", "kat-msg"),
    (10, "zero", "ff"),
    (10, "kat-seed", "deadbeef"),
    (12, "ff", "deadbeef"),
    (12, "kat-seed", "kat-msg"),
]


def run(cmd):
    out = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return out.stdout.strip()


def above_target_counter(kat):
    """The least counter c whose codeword sum exceeds T for this signature's FORS tops (§6: the encoding hashes
    tops ‖ LE32(c), 804 input bytes in all)."""
    pp, m, sig = hx(kat["pkSeed"])[:16], hx(kat["message"]), hx(kat["sig"])
    idx, _, tops, *_ = spec_recover(pp, m, sig)
    tw = adr(TW_ENC, 0, 0, idx)
    for c in range(1 << 32):
        x = int.from_bytes(th(pp, tw, tops + c.to_bytes(4, "little")), "little")
        if sum((x >> (2 * i)) & 3 for i in range(V)) > T_SUM:
            return c
    raise SystemExit("no counter has a codeword sum above T")


def make_vector(b, seed, msg):
    seed_hex, msg_hex = "0x" + SEEDS[seed].hex(), "0x" + MSGS[msg].hex()
    kat = json.loads(run([str(LSK), "kat", seed_hex, str(b), msg_hex]))
    assert kat["seed"] == seed_hex and kat["message"] == msg_hex and kat["b"] == b and kat["scheme"] == SCHEME
    assert len(hx(kat["sig"])) == SIG_LEN and len(kat["fors_indices"]) == K

    py_verify = [sys.executable, "-I", str(PY_SIGNER), *PY_VARIANT, "--verify", kat["pkSeed"], kat["pkRoot"]]
    if run(py_verify + [msg_hex, kat["sig"]]) != "true":
        raise SystemExit(f"Python --verify rejects b={b} seed={seed} msg={msg}")
    flipped = "0x" + (int(msg_hex, 16) ^ 1).to_bytes(32, "big").hex()
    if run(py_verify + [flipped, kat["sig"]]) != "false":
        raise SystemExit(f"Python --verify accepts a flipped message for b={b} seed={seed} msg={msg}")

    label = f"b={b}, seed {LABELS[seed]}, message {LABELS[msg]}"
    above = above_target_counter(kat)
    print(f"  ok  {label}: idx {kat['idx']}, counter {kat['counter']}, above-target counter {above}",
          file=sys.stderr)
    return {"label": label, **kat, "above_target_counter": above}


# The index bits whose two values the fixture must both hold (module docstring): name -> bit of a vector.
COVERED_BITS = {
    f"bit {H - 1} of idx": lambda v: (v["idx"] >> (H - 1)) & 1,
    f"bit {A - 1} of u_{K - 1}": lambda v: (v["fors_indices"][K - 1] >> (A - 1)) & 1,
}


def check_coverage(vectors):
    """Refuse a vector set that holds only one value of a bit in COVERED_BITS."""
    for what, bit in COVERED_BITS.items():
        missing = sorted({0, 1} - {bit(v) for v in vectors})
        if missing:
            raise SystemExit(f"no vector has {what} = {missing[0]}: change VECTORS so that both values occur")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[1])
    ap.add_argument("--check", action="store_true", help="fail if the committed fixture differs")
    ap.add_argument("--no-build", action="store_true", help="skip `cargo build --release`")
    args = ap.parse_args()

    ensure_binary(LSK, not args.no_build)

    fixture = {
        "scheme": SCHEME,
        "spec": "docs/leanSphincs-keccak.md",
        "params": "n=16 h=26 d=1 a=10 k=24 w=2 v=64 T=120, sig=5684 B",
        "hash": "keccak256 (Ethereum, 0x01 padding)",
        "digest": "two calls: D_c = keccak256(P || address(MSG, hi = c) || m || rho), c = 0, 1; idx = word 2 of D_0",
        "encoding": "merged: d = Th(P, address(ENC, 0, 0, e), tops || LE32(c)), no FORS key hash",
        "key_words": "pkSeed = P || 0^16, pkRoot = root || 0^16 (high-aligned)",
        "pruned_keys": "b = height of the kept subtree; the verifier cannot tell a pruned key from a full one",
        "signer": "signers/leansphincs-keccak (Rust port of upstream crates/sphincs, branch keccak, own parameters)",
        "confirmed_by": "script/leansphincs_s_signer.py --variant regular --verify (independent Python, spec-literal)",
        "reproduce": ".venv/bin/python signers/leansphincs-keccak/make_kat_fixture.py",
        "sig_len": SIG_LEN,
        "vectors": [make_vector(*v) for v in VECTORS],
    }
    check_coverage(fixture["vectors"])
    text = json.dumps(fixture, indent=2) + "\n"

    if args.check:
        if not FIXTURE.exists() or FIXTURE.read_text() != text:
            raise SystemExit(f"{FIXTURE.relative_to(REPO_ROOT)} is stale: rerun without --check")
        print(f"{FIXTURE.relative_to(REPO_ROOT)} is up to date", file=sys.stderr)
        return
    FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    FIXTURE.write_text(text)
    print(f"wrote {FIXTURE.relative_to(REPO_ROOT)} ({len(VECTORS)} vectors)", file=sys.stderr)


if __name__ == "__main__":
    main()
