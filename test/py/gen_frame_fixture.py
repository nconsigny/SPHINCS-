#!/usr/bin/env python3
"""Regenerate test/fixtures/frame8141_two_accounts.json for test/SphincsFrameModuleEmuTest.t.sol.

Two C13 keys (A = sender account, B = sponsor account) and, for each scenario, a frame
transaction plus real C13 witnesses over its compute_sig_hash(tx), signed with the Rust
signer (signers/signer-wasm: `signer-c13 keygen` / `sign-with`).

  sponsored   [only_verify(A) verifyFrameAndApprove(0), pay(B) verifyFrameAndApprove(1), SENDER]
              signatures [ARBITRARY wA, ARBITRARY wB]   (both msg empty)
  first-match [self_verify(A) verifyFrameAndApprove(), SENDER]
              signatures [SECP256K1 (placeholder bytes), ARBITRARY msg=<explicit digest>, ARBITRARY wA]

usage: gen_frame_fixture.py <signer-c13 binary> <out.json>
"""
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import frame8141_emu as fe  # noqa: E402

signer, out = sys.argv[1], sys.argv[2]


def sh(*args):
    return subprocess.run([signer, *args], check=True, capture_output=True, text=True).stdout.strip()


keys = {n: json.loads(sh("keygen", "0x" + m * 32)) for n, m in (("A", "a1"), ("B", "b2"))}
A_ADDR = "0xa11ce000000000000000000000000000000a11ce"
B_ADDR = "0x0000000000000000000000000000000000000b0b"
DEAD = "0x000000000000000000000000000000000000dead"
idx_sel = fe.selector("verifyFrameAndApprove(uint256)")
noidx_sel = fe.selector("verifyFrameAndApprove()")

fx = {
    "chain_id": 11155111,
    "verifier": "0x00000000000000000000000000000000000c13c1",
    "accounts": {
        "A": {"address": A_ADDR, "pkSeed": keys["A"]["seed"], "pkRoot": keys["A"]["root"]},
        "B": {"address": B_ADDR, "pkSeed": keys["B"]["seed"], "pkRoot": keys["B"]["root"]},
    },
    "scenarios": {
        "sponsored": {
            "nonce": 0, "sender": A_ADDR,
            "frames": [
                {"mode": fe.VERIFY, "flags": 0x2, "target": "", "data": "0x" + (idx_sel + fe.w(0)).hex()},
                {"mode": fe.VERIFY, "flags": 0x1, "target": B_ADDR, "data": "0x" + (idx_sel + fe.w(1)).hex()},
                {"mode": fe.SENDER, "flags": 0x0, "target": DEAD, "data": "0x"},
            ],
            "signatures": [
                {"scheme": fe.ARBITRARY, "signer": "", "msg": "", "sig": "A"},
                {"scheme": fe.ARBITRARY, "signer": "", "msg": "", "sig": "B"},
            ],
        },
        "first-match": {
            "nonce": 1, "sender": A_ADDR,
            "frames": [
                {"mode": fe.VERIFY, "flags": 0x3, "target": "", "data": "0x" + noidx_sel.hex()},
                {"mode": fe.SENDER, "flags": 0x0, "target": DEAD, "data": "0x"},
            ],
            "signatures": [
                {"scheme": fe.SECP256K1, "signer": "", "msg": "", "sig": "0x1b" + "11" * 64},
                {"scheme": fe.ARBITRARY, "signer": "", "msg": "0x" + "22" * 32, "sig": "0x" + "33" * 40},
                {"scheme": fe.ARBITRARY, "signer": "", "msg": "", "sig": "A"},
            ],
        },
    },
}

for name, sc in fx["scenarios"].items():
    # Witness bytes of empty-msg entries are elided from the hash, so sign after hashing.
    for s in sc["signatures"]:
        if s["sig"] in ("A", "B"):
            s["owner"], s["sig"] = s["sig"], "0x"
    d = "0x" + fe.compute_sig_hash(fe.load_tx(fx, name)).hex()
    sc["sigHash"] = d
    for s in sc["signatures"]:
        if "owner" in s:
            k = keys[s.pop("owner")]
            s["sig"] = sh("sign-with", k["seed"], k["sk_seed"], k["root"], d)
    assert "0x" + fe.compute_sig_hash(fe.load_tx(fx, name)).hex() == d
    print(f"{name}: sigHash={d}", file=sys.stderr)

json.dump(fx, open(out, "w"), indent=1)
