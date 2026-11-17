#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 Sagar Rana
"""Regenerate test/fixtures/slh-dsa-keccak-128s-kat.json, the fixture test/SLH-DSA-Keccak-128s-Test.t.sol reads.

Each vector is a key and a signature from script/slh_dsa_keccak_128s_signer.py (C12's plain SPHINCS+ at the
NIST 128s parameters), self-verified by the signer's own verifier before it is written. Keygen and signing are
deterministic (R is derived from the key, the message and sig_counter), so rerunning this script reproduces
the committed file byte for byte; --check fails if it would change.

Usage (pycryptodome is needed; about 15 s per vector):
    python3 script/make_slh_dsa_keccak_128s_kat.py [--check]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import slh_dsa_keccak_128s_signer  # noqa: E402,F401  (configures the shared module for 128s)
import jardin_spx_signer as spx  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE = REPO_ROOT / "test" / "fixtures" / "slh-dsa-keccak-128s-kat.json"

# (label, master_sk, message, sig_counter)
VECTORS = [
    ("0x11 x 32, deadbeef", b"\x11" * 32, bytes.fromhex("deadbeef").rjust(32, b"\x00"), 0),
    ("ramp, zero message", bytes(range(32)), bytes(32), 0),
    ("ramp, zero message, sig_counter 1", bytes(range(32)), bytes(32), 1),
    ("kat seed, kat message", spx.keccak256(b"SLH-DSA-Keccak-128s KAT seed").to_bytes(32, "big"),
     spx.keccak256(b"SLH-DSA-Keccak-128s KAT message").to_bytes(32, "big"), 0),
]


def word(x: int) -> str:
    return "0x" + x.to_bytes(32, "big").hex()


def build() -> str:
    out = []
    for label, master_sk, message, counter in VECTORS:
        sk_seed, sk_prf, pk_seed = spx.derive_spx_keys(master_sk)
        pk_root = spx.build_pk_root(pk_seed, sk_seed)
        msg = int.from_bytes(message, "big")
        sig = spx.spx_sign(pk_seed, sk_seed, sk_prf, pk_root, msg, counter)
        assert spx.spx_verify(pk_seed, pk_root, msg, sig), f"{label}: self-verify failed"
        out.append({
            "label": label,
            "masterSk": "0x" + master_sk.hex(),
            "sigCounter": counter,
            "pkSeed": word(pk_seed),
            "pkRoot": word(pk_root),
            "message": "0x" + message.hex(),
            "sig": "0x" + sig.hex(),
        })
        print(f"  {label}: {len(sig)}-byte signature", file=sys.stderr)
    doc = {
        "scheme": "SLH-DSA-Keccak-128s: C12's plain SPHINCS+ (FIPS uncompressed ADRS, keccak256) at "
                  "n=16 h=63 d=7 h'=9 a=12 k=14 w=16",
        "signer": "script/slh_dsa_keccak_128s_signer.py",
        "vectors": out,
    }
    return json.dumps(doc, indent=2) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the fixture is not what the sources produce")
    args = ap.parse_args()
    text = build()
    if args.check:
        if not FIXTURE.exists() or FIXTURE.read_text() != text:
            sys.exit(f"{FIXTURE.relative_to(REPO_ROOT)} is not what the sources produce; rerun without --check")
        print("fixture matches", file=sys.stderr)
    else:
        FIXTURE.write_text(text)
        print(f"wrote {FIXTURE.relative_to(REPO_ROOT)}", file=sys.stderr)


if __name__ == "__main__":
    main()
