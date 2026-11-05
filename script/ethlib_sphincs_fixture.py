#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 Nicolas Consigny <nicolas@ethereum.org>
"""Vendor EthLib's leanSPHINCS test vectors (CC0) into one JSON fixture.

    python3 script/ethlib_sphincs_fixture.py <ethlib-checkout> [-o test/fixtures/leansphincs-layered-ethlib.json]
    python3 script/ethlib_sphincs_fixture.py <ethlib-checkout> --check

<ethlib-checkout> is a checkout of ethereum/EthLib at PR #152's head (aa99d5f, "feat(sphincs): derive
every secret from H("leanSPHINCS" | S_0)"), for example:

    git init ethlib && cd ethlib && git fetch --depth=1 https://github.com/ethereum/EthLib.git pull/152/head
    git checkout FETCH_HEAD

Two sources, both produced by EthLib's Lean specification (`EthLib/Cryptography/Sphincs/`):
  - tests/cryptography/sphincs/{key_gen,sign,verify}/*/data.yaml, the cases the Python bindings
    (the Lean code, compiled) are tested against; each file is checked against the directory's
    SHA256SUMS before it is read.
  - EthLib/Cryptography/Proofs/Sphincs/KnownAnswer.lean: one key from the scheme seed
    S[i] = 37 i + 11 and one signature of m[i] = 7 i + 3, with every value verification computes
    (digest, FORS leaves and key, each layer's codeword, leaf and root), checked by the Lean kernel.

--check rebuilds the fixture and fails if it differs from the file on disk.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys

ETHLIB_PR = "https://github.com/ethereum/EthLib/pull/152"
ETHLIB_COMMIT = "aa99d5f"  # the PR head the vectors were taken from (short hash, see --help)
DEFAULT_OUT = "test/fixtures/leansphincs-layered-ethlib.json"
VECTORS = "tests/cryptography/sphincs"
KNOWN_ANSWER = "EthLib/Cryptography/Proofs/Sphincs/KnownAnswer.lean"


def _sha256sums(root: str) -> dict:
    sums = {}
    with open(os.path.join(root, VECTORS, "SHA256SUMS")) as f:
        for line in f:
            digest, name = line.split()
            sums[name] = digest
    return sums


_LINE = re.compile(r"^\s*(\w+):\s*(.*?)\s*$")


def _scalar(v: str):
    if v in ("null", "~"):
        return None
    if v == "true":
        return True
    if v == "false":
        return False
    m = re.fullmatch(r"'(0x[0-9a-fA-F]*)'", v) or re.fullmatch(r'"(0x[0-9a-fA-F]*)"', v)
    if not m:
        raise ValueError(f"unexpected YAML scalar {v[:40]!r}")
    return m.group(1).lower()


def _read_case(path: str) -> dict:
    """The vectors' YAML is two levels deep: `input:` with scalar fields, then `output:`."""
    out, section = {}, None
    with open(path) as f:
        for raw in f:
            if not raw.strip():
                continue
            m = _LINE.match(raw)
            if not m:
                raise ValueError(f"{path}: unexpected line {raw[:60]!r}")
            key, val = m.groups()
            indented = raw[0].isspace()
            if not indented:
                section = key
                if key == "output":
                    out["output"] = _scalar(val)
                elif key != "input" or val:
                    raise ValueError(f"{path}: unexpected top-level key {key!r}")
            else:
                if section != "input":
                    raise ValueError(f"{path}: field {key!r} outside input")
                out[key] = _scalar(val)
    if "output" not in out:
        raise ValueError(f"{path}: no output")
    return out


def _cases(root: str, op: str, sums: dict) -> list:
    base = os.path.join(root, VECTORS, op)
    cases = []
    for name in sorted(os.listdir(base)):
        path = os.path.join(base, name, "data.yaml")
        if not os.path.isfile(path):
            continue
        rel = f"{op}/{name}/data.yaml"
        with open(path, "rb") as f:
            digest = hashlib.sha256(f.read()).hexdigest()
        if sums.get(rel) != digest:
            raise ValueError(f"{rel}: SHA-256 {digest} does not match SHA256SUMS ({sums.get(rel)})")
        case = _read_case(path)
        case = {"name": name, **case}
        if op == "verify":
            # Derived, for Forge's JSON reader, which cannot read a null: the same as `output`.
            case["verdict"] = {True: "valid", False: "invalid", None: "rejected"}[case["output"]]
        cases.append(case)
    return cases


def _def_body(text: str, name: str) -> str:
    m = re.search(
        rf"^def {name}\b[^\n]*?:=(.*?)(?=^\s*$|^/--|^def |^theorem |^end |\Z)", text, flags=re.MULTILINE | re.DOTALL
    )
    if not m:
        raise ValueError(f"KnownAnswer.lean: no def {name}")
    return m.group(1)


def _hex_bytes(text: str, name: str) -> str:
    toks = re.findall(r"0x([0-9a-fA-F]{2})\b", _def_body(text, name))
    return "0x" + "".join(toks).lower()


def _decimals(text: str, name: str) -> list:
    body = _def_body(text, name)
    inner = re.search(r"#v\[(.*?)\]", body, flags=re.DOTALL)
    return [int(t) for t in re.findall(r"\b\d+\b", inner.group(1))]


def _known_answer(root: str) -> dict:
    with open(os.path.join(root, KNOWN_ANSWER)) as f:
        text = f.read()
    # The inputs are stated as formulas in the file (seed S[i] = 37 i + 11, m[i] = 7 i + 3).
    if "UInt8.ofNat (37 * i.val + 11)" not in text or "UInt8.ofNat (7 * i.val + 3)" not in text:
        raise ValueError("KnownAnswer.lean: the seed or message formula changed")
    seed = bytes((37 * i + 11) % 256 for i in range(32))
    msg = bytes((7 * i + 3) % 256 for i in range(32))
    ka = {
        "scheme_seed": "0x" + seed.hex(),
        "message": "0x" + msg.hex(),
        "tagged_seed": _hex_bytes(text, "taggedSeed"),
        "public_key": _hex_bytes(text, "publicKeyBytes"),
    }
    sig = "".join(
        _hex_bytes(text, n)[2:] for n in ("randomizerBytes", "forsBytes", "bottomBytes", "middleBytes", "topBytes")
    )
    ka["signature"] = "0x" + sig
    ka["digest"] = _hex_bytes(text, "digest")
    d = int.from_bytes(bytes.fromhex(ka["digest"][2:]), "little")
    ka["idx"] = d % 2**26
    m = re.search(r"The digest picks index `(\d+)`", text)
    if not m or int(m.group(1)) != ka["idx"]:
        raise ValueError("KnownAnswer.lean: the stated index does not match the digest")
    ka["leaves"] = _decimals(text, "leaves")
    ka["fors_key"] = _hex_bytes(text, "forsKey")
    for layer in ("bottom", "middle", "top"):
        ka[f"{layer}_codeword"] = _decimals(text, f"{layer}Codeword")
        ka[f"{layer}_leaf"] = _hex_bytes(text, f"{layer}Leaf")
        ka[f"{layer}_root"] = _hex_bytes(text, f"{layer}Root")
    # Shape checks: lengths every later reader relies on.
    assert len(bytes.fromhex(ka["signature"][2:])) == 7740, "known answer: signature length"
    assert len(bytes.fromhex(ka["public_key"][2:])) == 32
    assert len(bytes.fromhex(ka["digest"][2:])) == 64
    assert len(bytes.fromhex(ka["fors_key"][2:])) == 768
    assert len(ka["leaves"]) == 24
    for layer in ("bottom", "middle", "top"):
        assert len(ka[f"{layer}_codeword"]) == 64 and sum(ka[f"{layer}_codeword"]) == 128
    assert ka["top_root"] == "0x" + ka["public_key"][2:34], "known answer: top root is the key's root"
    return ka


def build(root: str) -> dict:
    sums = _sha256sums(root)
    fx = {
        "_comment": (
            "EthLib's leanSPHINCS test vectors (CC0-1.0), vendored by script/ethlib_sphincs_fixture.py from "
            f"{ETHLIB_PR} at {ETHLIB_COMMIT}: {VECTORS}/ (key_gen, sign, verify; null = input rejected) and "
            f"{KNOWN_ANSWER} (lean_known_answer, from the scheme seed directly, with intermediate values)."
        ),
        "source": {"pr": ETHLIB_PR, "commit": ETHLIB_COMMIT, "sha256sums": sums},
        "key_gen": _cases(root, "key_gen", sums),
        "sign": _cases(root, "sign", sums),
        "verify": _cases(root, "verify", sums),
        "lean_known_answer": _known_answer(root),
    }
    if len(fx["key_gen"]) + len(fx["sign"]) + len(fx["verify"]) != len(sums):
        raise ValueError("not every SHA256SUMS entry was read")
    return fx


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ethlib", help="path to an EthLib checkout at PR #152's head")
    ap.add_argument("-o", "--out", default=DEFAULT_OUT)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text = json.dumps(build(args.ethlib), indent=1) + "\n"
    if args.check:
        with open(args.out) as f:
            if f.read() != text:
                print(f"{args.out} is stale: rerun without --check", file=sys.stderr)
                return 1
        print(f"{args.out} matches", file=sys.stderr)
        return 0
    with open(args.out, "w") as f:
        f.write(text)
    print(f"wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
