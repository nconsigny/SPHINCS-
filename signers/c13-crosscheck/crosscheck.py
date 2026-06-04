#!/usr/bin/env python3
"""
End-to-end Python ↔ Rust ↔ Solidity cross-validation for C13.

Steps:
  1. Run the Python signer (`script/signer.py c13 <msg>`) → (seed, root, sig_py)
  2. Run the Rust CLI (`signer-c13 c13 <msg>`)               → (seed, root, sig_rs)
  3. Assert seed and root match byte-for-byte across both.
  4. Both signers use identical R-grind and count-grind algorithms, so the
     signatures should also match byte-for-byte. Compare and report.
  5. Spin up `anvil`, deploy SphincsC13Asm, and call
     `verify(seed, root, msg, sig)` against each signature via `cast call`.
     Both must return `true`.

Usage:
  python3 signers/c13-crosscheck/crosscheck.py [<msg_hex>]

If <msg_hex> is omitted, defaults to keccak256("c13 crosscheck") so the test is
reproducible.

Assumes (from repo root):
  - `python3 script/signer.py c13 …` works
  - `signers/signer-wasm/target/release/signer-c13` is built
    (run `cargo build --release --bin signer-c13` inside signers/signer-wasm/)
  - `anvil`, `forge`, `cast` are on PATH
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
PYSIG = REPO_ROOT / "script" / "signer.py"
RSCLI = REPO_ROOT / "signers/signer-wasm" / "target" / "release" / "signer-c13"
VERIFIER_SRC = "src/SPHINCs-C13Asm.sol:SphincsC13Asm"

ANVIL_RPC = "http://127.0.0.1:8545"
ANVIL_KEY = "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"


def keccak256_hex(label: bytes) -> str:
    from Crypto.Hash import keccak
    h = keccak.new(digest_bits=256)
    h.update(label)
    return "0x" + h.digest().hex()


def require(cond, msg):
    if not cond:
        print(f"FAIL: {msg}", file=sys.stderr)
        sys.exit(1)


def check_prereqs():
    for tool in ("anvil", "forge", "cast"):
        require(shutil.which(tool) is not None, f"`{tool}` not on PATH")
    require(PYSIG.exists(), f"Python signer missing: {PYSIG}")
    require(RSCLI.exists(),
        f"Rust CLI missing at {RSCLI}\n"
        f"Build it: (cd signers/signer-wasm && cargo build --release --bin signer-c13)")


def decode_abi(hex_payload: str) -> tuple[bytes, bytes, bytes]:
    """Decode (bytes32 seed, bytes32 root, bytes sig) from ABI hex."""
    raw = bytes.fromhex(hex_payload.removeprefix("0x"))
    seed = raw[0:32]
    root = raw[32:64]
    # offset @ 64..96 == 0x60; length @ 96..128
    sig_len = int.from_bytes(raw[96:128], "big")
    sig = raw[128:128 + sig_len]
    return seed, root, sig


def run_python_signer(msg_hex: str) -> tuple[bytes, bytes, bytes]:
    print(f"  [py] python3 {PYSIG} c13 {msg_hex[:18]}…")
    t0 = time.time()
    out = subprocess.check_output(
        ["python3", str(PYSIG), "c13", msg_hex],
        cwd=REPO_ROOT,
        stderr=subprocess.DEVNULL,
    ).decode().strip()
    dt = time.time() - t0
    seed, root, sig = decode_abi(out)
    print(f"  [py]   {dt:.1f}s — sig={len(sig)} B  seed=0x{seed[:8].hex()}  root=0x{root[:8].hex()}")
    return seed, root, sig


def run_rust_signer(msg_hex: str) -> tuple[bytes, bytes, bytes]:
    print(f"  [rs] {RSCLI} c13 {msg_hex[:18]}…")
    t0 = time.time()
    out = subprocess.check_output(
        [str(RSCLI), "c13", msg_hex],
        cwd=REPO_ROOT,
        stderr=subprocess.DEVNULL,
    ).decode().strip()
    dt = time.time() - t0
    seed, root, sig = decode_abi(out)
    print(f"  [rs]   {dt:.1f}s — sig={len(sig)} B  seed=0x{seed[:8].hex()}  root=0x{root[:8].hex()}")
    return seed, root, sig


def start_anvil() -> subprocess.Popen:
    print("  [anvil] starting…")
    proc = subprocess.Popen(
        ["anvil", "--silent", "--port", "8545"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    # Wait for anvil to be ready
    for _ in range(50):
        try:
            subprocess.check_output(
                ["cast", "block-number", "--rpc-url", ANVIL_RPC],
                stderr=subprocess.DEVNULL,
            )
            return proc
        except subprocess.CalledProcessError:
            time.sleep(0.1)
    proc.terminate()
    raise RuntimeError("anvil did not become ready in 5s")


def deploy_verifier() -> str:
    print(f"  [forge] deploying {VERIFIER_SRC}…")
    out = subprocess.check_output(
        ["forge", "create",
         "--rpc-url", ANVIL_RPC,
         "--private-key", ANVIL_KEY,
         "--broadcast",
         VERIFIER_SRC],
        cwd=REPO_ROOT,
    ).decode()
    m = re.search(r"Deployed to:\s*(0x[0-9a-fA-F]{40})", out)
    require(m is not None, f"could not parse forge create output:\n{out}")
    addr = m.group(1)
    print(f"  [forge]   verifier @ {addr}")
    return addr


def call_verify(verifier: str, seed: bytes, root: bytes, msg_hex: str, sig: bytes) -> bool:
    out = subprocess.check_output(
        ["cast", "call", verifier,
         "verify(bytes32,bytes32,bytes32,bytes)(bool)",
         "0x" + seed.hex(),
         "0x" + root.hex(),
         msg_hex,
         "0x" + sig.hex(),
         "--rpc-url", ANVIL_RPC],
    ).decode().strip()
    return out.lower() == "true"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("msg_hex", nargs="?", default=None,
        help="0x-prefixed 32-byte hex; default = keccak256('c13 crosscheck')")
    p.add_argument("--skip-anvil", action="store_true",
        help="Skip the on-chain verify step (just compare signer outputs)")
    args = p.parse_args()

    check_prereqs()

    msg_hex = args.msg_hex or keccak256_hex(b"c13 crosscheck")
    require(re.fullmatch(r"0x[0-9a-fA-F]{64}", msg_hex), "msg_hex must be 0x + 64 hex chars")

    print(f"Message: {msg_hex}\n")

    seed_py, root_py, sig_py = run_python_signer(msg_hex)
    seed_rs, root_rs, sig_rs = run_rust_signer(msg_hex)

    print("\n=== Byte-equality check ===")
    seed_ok = seed_py == seed_rs
    root_ok = root_py == root_rs
    sig_ok = sig_py == sig_rs
    print(f"  seed: {'MATCH' if seed_ok else 'MISMATCH'}")
    print(f"  root: {'MATCH' if root_ok else 'MISMATCH'}")
    print(f"  sig : {'MATCH' if sig_ok else 'MISMATCH (lengths %d/%d)' % (len(sig_py), len(sig_rs))}")

    if not sig_ok and len(sig_py) == len(sig_rs):
        diffs = [i for i in range(len(sig_py)) if sig_py[i] != sig_rs[i]]
        print(f"  first {min(5, len(diffs))} differing byte indices: {diffs[:5]}")

    require(seed_ok and root_ok, "seed/root must match (deterministic from message)")

    if args.skip_anvil:
        print("\nSkipping on-chain verify (--skip-anvil)")
        sys.exit(0 if (seed_ok and root_ok and sig_ok) else 1)

    print("\n=== On-chain verify ===")
    anvil = start_anvil()
    try:
        verifier = deploy_verifier()
        py_valid = call_verify(verifier, seed_py, root_py, msg_hex, sig_py)
        rs_valid = call_verify(verifier, seed_rs, root_rs, msg_hex, sig_rs)
        print(f"  Python sig verifies: {py_valid}")
        print(f"  Rust   sig verifies: {rs_valid}")
        ok = py_valid and rs_valid and sig_ok
        print(f"\nOVERALL: {'PASS' if ok else 'FAIL'}")
        sys.exit(0 if ok else 1)
    finally:
        anvil.terminate()
        try:
            anvil.wait(timeout=5)
        except subprocess.TimeoutExpired:
            anvil.kill()


if __name__ == "__main__":
    main()
