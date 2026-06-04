#!/usr/bin/env python3
"""
Send a hybrid (ECDSA + C13 SPHINCs-) ERC-4337 UserOperation on Sepolia.

Single-shot pipeline:
  1. Keygen: Rust CLI `signer-c13 keygen <seed_material>` → (seed, sk_seed, root)
  2. createAccount(ecdsaOwner, pkSeed, pkRoot) via SphincsAccountFactory → SphincsAccount address
  3. Fund the account so it can pay handleOps gas
  4. Build a self-transfer UserOp (sender → ecdsaOwner, small value)
  5. Compute EIP-712 userOpHash for EntryPoint v0.9
  6. ECDSA-sign userOpHash; Rust CLI `sign-with <seed> <sk_seed> <root> <userOpHash>` → c13 sig
  7. handleOps([op], beneficiary=ecdsaOwner)

Env (loaded from .env if not exported):
  SEPOLIA_RPC_URL   - Sepolia RPC
  PRIVATE_KEY       - ECDSA private key; also used as the SPHINCs- keygen seed material

Layout assumes you've already deployed the factory + verifier (see
script/.c13_addresses.json).
"""
import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

import requests
from eth_account import Account
from eth_abi import encode

REPO_ROOT = Path(__file__).resolve().parents[1]
RUST_CLI = REPO_ROOT / "signers/signer-wasm" / "target" / "release" / "signer-c13"
ADDRS_JSON = REPO_ROOT / "script" / ".c13_addresses.json"

ENTRYPOINT_V09 = "0x433709009B8330FDa32311DF1C2AFA402eD8D009"
CHAIN_ID = 11155111  # Sepolia


def keccak(data: bytes) -> bytes:
    from Crypto.Hash import keccak as _k
    h = _k.new(digest_bits=256)
    h.update(data)
    return h.digest()


PACKED_USEROP_TYPEHASH = keccak(
    b"PackedUserOperation(address sender,uint256 nonce,bytes initCode,"
    b"bytes callData,bytes32 accountGasLimits,uint256 preVerificationGas,"
    b"bytes32 gasFees,bytes paymasterAndData)"
)

EIP712_DOMAIN_TYPEHASH = keccak(
    b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
)


def load_env():
    env = {}
    p = REPO_ROOT / ".env"
    if p.exists():
        for line in p.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, v = line.split("=", 1)
                env.setdefault(k.strip(), v.strip())
    for k, v in env.items():
        os.environ.setdefault(k, v)


def rpc(method, params, rpc_url):
    r = requests.post(rpc_url, json={"jsonrpc": "2.0", "id": 1, "method": method, "params": params}, timeout=30)
    j = r.json()
    if "error" in j:
        raise RuntimeError(f"rpc {method}: {j['error']}")
    return j["result"]


def cast_send(args, *, rpc_url, key):
    cmd = ["cast", "send", *args, "--rpc-url", rpc_url, "--private-key", key]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
    if proc.returncode != 0:
        raise RuntimeError(f"cast send failed: {proc.stderr}")
    return proc.stdout


def cast_call(args, *, rpc_url):
    cmd = ["cast", "call", *args, "--rpc-url", rpc_url]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if proc.returncode != 0:
        raise RuntimeError(f"cast call failed: {proc.stderr}")
    return proc.stdout.strip()


def domain_separator():
    return keccak(encode(
        ["bytes32", "bytes32", "bytes32", "uint256", "address"],
        [EIP712_DOMAIN_TYPEHASH, keccak(b"ERC4337"), keccak(b"1"), CHAIN_ID, bytes.fromhex(ENTRYPOINT_V09[2:])],
    ))


DOMAIN_SEP = domain_separator()


def user_op_hash(op):
    """EIP-712 userOpHash for EntryPoint v0.9."""
    init_code = bytes.fromhex(op["initCode"][2:]) if op["initCode"] != "0x" else b""
    call_data = bytes.fromhex(op["callData"][2:]) if op["callData"] != "0x" else b""
    pm = bytes.fromhex(op["paymasterAndData"][2:]) if op["paymasterAndData"] != "0x" else b""
    struct_hash = keccak(encode(
        ["bytes32", "address", "uint256", "bytes32", "bytes32",
         "bytes32", "uint256", "bytes32", "bytes32"],
        [
            PACKED_USEROP_TYPEHASH,
            bytes.fromhex(op["sender"][2:]),
            int(op["nonce"], 16),
            keccak(init_code),
            keccak(call_data),
            bytes.fromhex(op["accountGasLimits"][2:]),
            int(op["preVerificationGas"], 16),
            bytes.fromhex(op["gasFees"][2:]),
            keccak(pm),
        ],
    ))
    return keccak(b"\x19\x01" + DOMAIN_SEP + struct_hash)


def build_execute(to_addr: str, value_wei: int, data: bytes = b"") -> bytes:
    sel = keccak(b"execute(address,uint256,bytes)")[:4]
    return sel + encode(["address", "uint256", "bytes"],
                        [bytes.fromhex(to_addr[2:]), value_wei, data])


def rust_keygen(seed_material_hex: str) -> dict:
    proc = subprocess.run(
        [str(RUST_CLI), "keygen", seed_material_hex],
        capture_output=True, text=True, timeout=300,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"signer-c13 keygen failed: {proc.stderr}")
    return json.loads(proc.stdout.strip())


def rust_sign_with(seed: str, sk_seed: str, root: str, msg_hex: str) -> bytes:
    proc = subprocess.run(
        [str(RUST_CLI), "sign-with", seed, sk_seed, root, msg_hex],
        capture_output=True, text=True, timeout=600,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"signer-c13 sign-with failed: {proc.stderr}")
    sig_hex = proc.stdout.strip().removeprefix("0x")
    return bytes.fromhex(sig_hex)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--factory", help="SphincsAccountFactory address (defaults from .c13_addresses.json)")
    ap.add_argument("--to", default=None, help="UserOp recipient (defaults to ecdsaOwner)")
    ap.add_argument("--value-wei", type=int, default=10_000_000_000_000, help="UserOp value in wei (default 1e13 = 0.00001 ETH)")
    ap.add_argument("--fund-wei", type=int, default=20_000_000_000_000_000, help="Pre-fund the account (default 0.02 ETH)")
    ap.add_argument("--keypair-file", default=str(REPO_ROOT / "script" / ".c13_userop_keypair.json"),
                    help="Cache file for SPHINCs- keypair (avoid re-keygen)")
    args = ap.parse_args()

    load_env()
    rpc_url = os.environ.get("SEPOLIA_RPC_URL")
    if not rpc_url:
        sys.exit("SEPOLIA_RPC_URL not set")
    ecdsa_key_hex = os.environ.get("PRIVATE_KEY")
    if not ecdsa_key_hex:
        sys.exit("PRIVATE_KEY not set")
    ecdsa_key_hex = ecdsa_key_hex.removeprefix("0x")
    acct = Account.from_key(bytes.fromhex(ecdsa_key_hex))
    print(f"ECDSA owner : {acct.address}")

    if args.factory is None:
        if not ADDRS_JSON.exists():
            sys.exit(f"missing {ADDRS_JSON}; pass --factory")
        info = json.loads(ADDRS_JSON.read_text())
        args.factory = info["sepolia"]["account_factory"]
    print(f"Factory     : {args.factory}")

    to_addr = args.to or acct.address
    print(f"UserOp dst  : {to_addr}")

    # ============ 1. Keygen (cached) ============
    kp_path = Path(args.keypair_file)
    if kp_path.exists():
        kp = json.loads(kp_path.read_text())
        print(f"Loaded cached SPHINCs- keypair from {kp_path}")
    else:
        # Seed material: keccak("c13-4337" || ecdsaPrivkey || ecdsaAddress).
        # Deterministic per owner, persisted to disk so subsequent UserOps reuse.
        seed_material = keccak(b"c13-4337" + bytes.fromhex(ecdsa_key_hex) + bytes.fromhex(acct.address[2:]))
        print(f"Generating SPHINCs- C13 keypair (seed material = keccak('c13-4337'||sk||addr))…")
        kp = rust_keygen("0x" + seed_material.hex())
        kp_path.write_text(json.dumps(kp, indent=2))
        print(f"Saved keypair to {kp_path}")
    print(f"  pkSeed: {kp['seed']}")
    print(f"  pkRoot: {kp['root']}")

    # ============ 2. Compute counterfactual account address ============
    sel = keccak(b"getAddress(address,bytes32,bytes32)")[:4]
    args_bytes = encode(
        ["address", "bytes32", "bytes32"],
        [bytes.fromhex(acct.address[2:]),
         bytes.fromhex(kp["seed"].removeprefix("0x")),
         bytes.fromhex(kp["root"].removeprefix("0x"))],
    )
    out = cast_call([args.factory, "0x" + (sel + args_bytes).hex()], rpc_url=rpc_url)
    account_addr = "0x" + out[-40:]
    print(f"Account     : {account_addr}")

    # Check if already deployed
    code = rpc("eth_getCode", [account_addr, "latest"], rpc_url)
    if code == "0x":
        print("Deploying account via factory.createAccount…")
        cast_send([
            args.factory,
            "createAccount(address,bytes32,bytes32)",
            acct.address, kp["seed"], kp["root"],
        ], rpc_url=rpc_url, key="0x" + ecdsa_key_hex)
        time.sleep(2)
    else:
        print("Account already deployed.")

    # ============ 3. Fund the account if needed ============
    bal_hex = rpc("eth_getBalance", [account_addr, "latest"], rpc_url)
    bal = int(bal_hex, 16)
    print(f"Account balance: {bal / 1e18:.6f} ETH")
    needed = args.value_wei + 5 * 10**15  # value + 0.005 ETH headroom for gas
    if bal < needed:
        topup = needed - bal
        print(f"Funding account with {topup / 1e18:.6f} ETH…")
        cast_send([account_addr, "--value", str(topup)], rpc_url=rpc_url, key="0x" + ecdsa_key_hex)
        time.sleep(2)

    # ============ 4. Build UserOp ============
    sel_nonce = keccak(b"getNonce(address,uint192)")[:4]
    nonce_calldata = sel_nonce + encode(["address", "uint192"], [bytes.fromhex(account_addr[2:]), 0])
    nonce_hex = rpc("eth_call", [{"to": ENTRYPOINT_V09, "data": "0x" + nonce_calldata.hex()}, "latest"], rpc_url)
    nonce = int(nonce_hex, 16)
    print(f"Nonce       : {nonce}")

    block = rpc("eth_getBlockByNumber", ["latest", False], rpc_url)
    base_fee = int(block["baseFeePerGas"], 16)
    max_priority = 2 * 10**9
    max_fee = base_fee * 2 + max_priority

    # 300K verify (C13 ~190K + account overhead), 35K call (simple ETH transfer)
    ver_gas, call_gas = 300_000, 35_000
    account_gas_limits = ver_gas.to_bytes(16, "big") + call_gas.to_bytes(16, "big")
    gas_fees = max_priority.to_bytes(16, "big") + max_fee.to_bytes(16, "big")
    pre_ver_gas = 100_000

    call_data = build_execute(to_addr, args.value_wei)

    op = {
        "sender": account_addr,
        "nonce": hex(nonce),
        "initCode": "0x",
        "callData": "0x" + call_data.hex(),
        "accountGasLimits": "0x" + account_gas_limits.hex(),
        "preVerificationGas": hex(pre_ver_gas),
        "gasFees": "0x" + gas_fees.hex(),
        "paymasterAndData": "0x",
        "signature": "0x",
    }
    op_hash = user_op_hash(op)
    print(f"userOpHash  : 0x{op_hash.hex()}")

    # ============ 5. Sign ============
    print("ECDSA signing userOpHash…")
    sig = acct.unsafe_sign_hash(op_hash)
    ecdsa_sig = sig.r.to_bytes(32, "big") + sig.s.to_bytes(32, "big") + sig.v.to_bytes(1, "big")

    print("C13 signing userOpHash via Rust CLI…")
    t0 = time.time()
    sphincs_sig = rust_sign_with(kp["seed"], kp["sk_seed"], kp["root"], "0x" + op_hash.hex())
    print(f"  c13 sig: {len(sphincs_sig)} B, {time.time()-t0:.1f}s")

    hybrid = encode(["bytes", "bytes"], [ecdsa_sig, sphincs_sig])
    op["signature"] = "0x" + hybrid.hex()
    print(f"Hybrid sig  : {len(hybrid)} B")

    # ============ 6. handleOps ============
    op_tuple = (
        bytes.fromhex(op["sender"][2:]),
        int(op["nonce"], 16),
        b"",
        bytes.fromhex(op["callData"][2:]),
        bytes.fromhex(op["accountGasLimits"][2:]),
        int(op["preVerificationGas"], 16),
        bytes.fromhex(op["gasFees"][2:]),
        b"",
        bytes.fromhex(op["signature"][2:]),
    )
    sel_handle = keccak(
        b"handleOps((address,uint256,bytes,bytes,bytes32,uint256,bytes32,bytes,bytes)[],address)"
    )[:4]
    params = encode(
        ["(address,uint256,bytes,bytes,bytes32,uint256,bytes32,bytes,bytes)[]", "address"],
        [[op_tuple], bytes.fromhex(acct.address[2:])],
    )
    calldata = "0x" + (sel_handle + params).hex()

    print("\nSubmitting handleOps()…")
    proc = subprocess.run(
        ["cast", "send", ENTRYPOINT_V09, calldata,
         "--rpc-url", rpc_url, "--private-key", "0x" + ecdsa_key_hex,
         "--gas-limit", "1500000",
         "--json"],
        capture_output=True, text=True, timeout=180,
    )
    if proc.returncode != 0:
        print("handleOps FAILED:", file=sys.stderr)
        print(proc.stderr, file=sys.stderr)
        sys.exit(1)
    receipt = json.loads(proc.stdout)
    tx_hash = receipt.get("transactionHash")
    gas_used = int(receipt.get("gasUsed", "0x0"), 16)
    block_num = int(receipt.get("blockNumber", "0x0"), 16)
    status = receipt.get("status", "?")

    print("\n=== UserOp executed ===")
    print(f"  tx hash    : {tx_hash}")
    print(f"  block      : {block_num}")
    print(f"  gas used   : {gas_used}")
    print(f"  status     : {status} ({'OK' if status == '0x1' else 'REVERTED'})")
    print(f"  explorer   : https://sepolia.etherscan.io/tx/{tx_hash}")


if __name__ == "__main__":
    main()
