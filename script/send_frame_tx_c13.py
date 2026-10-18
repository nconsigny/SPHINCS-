#!/usr/bin/env python3
"""
Send an EIP-8141 frame transaction on the ethrex EIP-8141 devnet that exercises
the C13 SphincsFrameAccount.

Structure:
  Frame 0: VERIFY mode, flags=3 (approve sender+payer), target=frame_account
            data = sigHash(32) || c13_sig(3688)
            The frame account's runtime staticcalls the shared C13 verifier
            and APPROVEs(0,0,3) on success.
  Frame 1: SENDER mode, flags=0, target=recipient, value=<small>, data=empty
            Executes a plain ETH transfer with tx.sender = frame_account.

Note on sigHash: the legacy frame_account runtime trusts whatever sigHash sits
in `calldata[0:32]` (it does not introspect via TXPARAM). For replay protection
in a production setup this would need to be tied to the canonical sig_hash via
TXPARAM(0x08). For this demo we use a deterministic hash bound to the nonce.

Env:
  PRIVATE_KEY      - funds the deployer for tx submission; the frame_account
                     itself pays its own gas via APPROVE(scope=payer).

Usage:
  python3 script/send_frame_tx_c13.py [--rpc <url>] [--value-wei N]
"""
import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

import requests
import rlp
from Crypto.Hash import keccak as _k

REPO_ROOT = Path(__file__).resolve().parents[1]
RUST_CLI = REPO_ROOT / "signers/signer-wasm" / "target" / "release" / "signer-c13"
ADDRS_JSON = REPO_ROOT / "script" / ".c13_addresses.json"
KP_FILE = REPO_ROOT / "script" / ".c13_frame_keypair.json"

FRAME_TX_TYPE = 0x06
DEFAULT_RPC = "https://rpc1.eip-8141.ethrex.xyz"
DEFAULT_RECIPIENT = "0x000000000000000000000000000000000000dead"


def keccak(b: bytes) -> bytes:
    h = _k.new(digest_bits=256); h.update(b); return h.digest()


def load_env():
    p = REPO_ROOT / ".env"
    if p.exists():
        for line in p.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip())


def rpc(method, params, url):
    r = requests.post(url, json={"jsonrpc": "2.0", "id": 1, "method": method, "params": params}, timeout=30)
    j = r.json()
    if "error" in j:
        raise RuntimeError(f"{method}: {j['error']}")
    return j["result"]


def to_int_min(x):
    """RLP-encode integer with minimal-byte big-endian representation."""
    if x == 0:
        return b""
    return x.to_bytes((x.bit_length() + 7) // 8, "big")


def rust_keygen(seed_material_hex: str) -> dict:
    proc = subprocess.run(
        [str(RUST_CLI), "keygen", seed_material_hex],
        capture_output=True, text=True, timeout=300,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"signer-c13 keygen failed: {proc.stderr}")
    return json.loads(proc.stdout.strip())


def rust_sign_with(seed, sk_seed, root, msg_hex):
    proc = subprocess.run(
        [str(RUST_CLI), "sign-with", seed, sk_seed, root, msg_hex],
        capture_output=True, text=True, timeout=600,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"signer-c13 sign-with failed: {proc.stderr}")
    return bytes.fromhex(proc.stdout.strip().removeprefix("0x"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rpc", default=DEFAULT_RPC)
    ap.add_argument("--recipient", default=DEFAULT_RECIPIENT)
    ap.add_argument("--value-wei", type=int, default=10_000_000_000_000)  # 0.00001 ETH
    args = ap.parse_args()

    load_env()
    rpc_url = args.rpc

    # 0. Load deploy info; locate frame_account and verifier
    info = json.loads(ADDRS_JSON.read_text())
    ethrex = info["ethrex"]
    frame_account = ethrex["frame_account"]
    verifier = ethrex["shared_verifier"]
    print(f"Frame account: {frame_account}")
    print(f"Verifier     : {verifier}")

    chain_id = int(rpc("eth_chainId", [], rpc_url), 16)
    print(f"Chain id     : {chain_id}")

    # The frame_account's bytecode was built around a specific (pkSeed, pkRoot)
    # that came from the deploy_frame_account.py keygen. Reproduce the same
    # derivation to recover sk_seed (the deploy script doesn't persist it).
    # deploy_frame_account.py uses:
    #   entropy = bytes.fromhex(dev_key) + variant.encode()
    #   keygen_msg = keccak("sphincs_keygen" || entropy)
    #   seed, root, _ = sign_variant("c13", keygen_msg)
    # That sign_variant call internally does:
    #   seed, sk_seed = derive_keys(keygen_msg)
    # so seed/sk_seed are determined by keygen_msg.
    dev_key = os.environ.get("PRIVATE_KEY")
    if not dev_key:
        sys.exit("PRIVATE_KEY not in env")
    dev_key = dev_key.removeprefix("0x")
    entropy = bytes.fromhex(dev_key) + b"c13"
    keygen_msg = keccak(b"sphincs_keygen" + entropy)
    kp = rust_keygen("0x" + keygen_msg.hex())
    pk_seed_hex = kp["seed"]; pk_root_hex = kp["root"]; sk_seed_hex = kp["sk_seed"]
    print(f"Re-derived pkSeed: {pk_seed_hex}")
    print(f"Re-derived pkRoot: {pk_root_hex}")

    # Sanity: this must match the keys that were embedded in the frame_account's
    # storage at deploy time. The deployed ethrex runtime (legacy/script/
    # deploy_frame_account.py) stores pkSeed at slot 0, pkRoot at slot 1.
    # src/SphincsFrameAccount.sol keeps them as immutables instead, so for that
    # contract read pkSeed() / pkRoot() rather than raw slots.
    stored_seed = rpc("eth_getStorageAt", [frame_account, "0x0", "latest"], rpc_url)
    stored_root = rpc("eth_getStorageAt", [frame_account, "0x1", "latest"], rpc_url)
    if stored_seed.lower() != pk_seed_hex.lower():
        sys.exit(f"pkSeed mismatch — frame_account stored {stored_seed}, regenerated {pk_seed_hex}")
    if stored_root.lower() != pk_root_hex.lower():
        sys.exit(f"pkRoot mismatch — frame_account stored {stored_root}, regenerated {pk_root_hex}")
    print("Storage key sanity: OK")

    # 1. Outer tx scaffolding
    nonce = int(rpc("eth_getTransactionCount", [frame_account, "pending"], rpc_url), 16)
    block = rpc("eth_getBlockByNumber", ["latest", False], rpc_url)
    base_fee = int(block["baseFeePerGas"], 16)
    max_priority = 1_000_000_000
    max_fee = base_fee * 2 + max_priority
    print(f"Nonce        : {nonce}")
    print(f"Gas base/max : {base_fee} / {max_fee}")

    # 2. Compute a deterministic sigHash bound to (chain_id, frame_account, nonce, recipient, value).
    # The runtime trusts calldata[0:32] for sigHash but our binding ensures different txs
    # produce different sigHash, so a sig can't be reused across nonce/value combos.
    recipient = args.recipient.lower()
    rcpt_b = bytes.fromhex(recipient.removeprefix("0x"))
    sigHash = keccak(
        chain_id.to_bytes(32, "big") +
        bytes.fromhex(frame_account.removeprefix("0x")) +
        nonce.to_bytes(32, "big") +
        rcpt_b +
        args.value_wei.to_bytes(32, "big")
    )
    print(f"sigHash      : 0x{sigHash.hex()}")

    # 3. Sign sigHash with C13
    print("Signing sigHash with C13 (Rust CLI)…")
    t0 = time.time()
    c13_sig = rust_sign_with(pk_seed_hex, sk_seed_hex, pk_root_hex, "0x" + sigHash.hex())
    print(f"  c13 sig: {len(c13_sig)} B, {time.time()-t0:.1f}s")

    # 4. Build the frames
    APPROVAL_SCOPE_BOTH = 3  # bits 0-1 = 3 (sender+payer)
    VERIFY_MODE, SENDER_MODE = 1, 2

    verify_data = sigHash + c13_sig  # frame_account runtime reads sigHash[0:32], sig[32:]
    verify_frame = [
        to_int_min(VERIFY_MODE),
        to_int_min(APPROVAL_SCOPE_BOTH),
        bytes.fromhex(frame_account.removeprefix("0x")),
        to_int_min(400_000),               # gas_limit for verify — C13 verify ≈ 190K + ABI overhead
        b"",                                # value must be 0 for non-SENDER modes
        verify_data,
    ]
    sender_frame = [
        to_int_min(SENDER_MODE),
        b"",                                # flags=0
        rcpt_b,
        to_int_min(30_000),
        to_int_min(args.value_wei),
        b"",
    ]
    frames = [verify_frame, sender_frame]

    # 5. Build the full RLP payload.
    # Note: ethrex's FrameTransaction RLP layout differs from the draft EIP-8141
    # markdown — there is no `signatures` field in the on-chain encoding.
    # See lambdaclass/ethrex@eip-8141-devnet `impl RLPEncode for FrameTransaction`
    # (crates/common/types/transaction.rs): the order is
    #   chain_id, nonce, sender, frames,
    #   max_priority_fee_per_gas, max_fee_per_gas,
    #   max_fee_per_blob_gas, blob_versioned_hashes
    tx_body = [
        to_int_min(chain_id),
        to_int_min(nonce),
        bytes.fromhex(frame_account.removeprefix("0x")),   # sender
        frames,
        to_int_min(max_priority),
        to_int_min(max_fee),
        b"",                                                # max_fee_per_blob_gas = 0
        [],                                                 # blob_versioned_hashes = []
    ]
    encoded = bytes([FRAME_TX_TYPE]) + rlp.encode(tx_body)
    print(f"Encoded tx   : {len(encoded)} B")

    # 6. Send via eth_sendRawTransaction
    print("Submitting frame tx…")
    tx_hash = rpc("eth_sendRawTransaction", ["0x" + encoded.hex()], rpc_url)
    print(f"\n=== Frame tx submitted ===")
    print(f"  tx hash  : {tx_hash}")

    # Wait for receipt
    print("  waiting for receipt…")
    for _ in range(60):
        try:
            r = rpc("eth_getTransactionReceipt", [tx_hash], rpc_url)
            if r:
                break
        except RuntimeError:
            r = None
        time.sleep(2)
    if not r:
        print("  receipt not seen within 120s")
        return
    status = int(r.get("status", "0x0"), 16)
    gas_used = int(r.get("gasUsed", "0x0"), 16)
    block_num = int(r.get("blockNumber", "0x0"), 16)
    print(f"  status   : {status} ({'OK' if status else 'REVERTED'})")
    print(f"  block    : {block_num}")
    print(f"  gas used : {gas_used}")
    print(f"  explorer : https://explorer.eip-8141.ethrex.xyz/tx/{tx_hash}")


if __name__ == "__main__":
    main()
