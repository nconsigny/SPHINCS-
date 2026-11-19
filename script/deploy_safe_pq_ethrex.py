#!/usr/bin/env python3
"""Deploy a Safe with post-quantum owners on the ethrex privacy testnet and send one frame transaction.

Steps (each is skipped when the state file already records it, so the script can be rerun):
  keys     three fresh leanSphincs-f Light-tier key files (lsfk keygen, random seeds), in --key-dir
  owners   three SphincsOwnerAccounts, sharing an existing leanSphincs-f verifier and frame module
  safe     the Safe 1.5.0 singleton and SafeProxyFactory (built from lib/safe-smart-account-1.5.0 by
           `forge build`), then a 2-of-3 Safe over the three owner accounts
  fund     ETH for the Safe (the amount it sends) and for the sender's owner account (it pays for
           the frame transaction)
  frame    one Safe transaction (a transfer to the deployer), co-signed by owner 1 and sent as an
           EIP-8141 frame transaction [self_verify, SENDER -> Safe.execTransaction] from owner 0's
           account, with script/safe_pq_owners.py --wire ethrex. Before signing it checks the Safe
           transaction hash against Safe.getTransactionHash and the co-signature against the
           owner account's isValidSignature, both by eth_call. The transaction is dry-run with
           ethrex_simulateFrameTransaction and sent only if that succeeds (DRY_RUN=1 stops there).

The deployer key is PRIVATE_KEY from .env (the repo root's, or --env). Ordinary deploys are
EIP-1559 transactions signed with eth_account. Needs `forge build` and lsfk built.

Usage: deploy_safe_pq_ethrex.py [--rpc URL] [--key-dir DIR] [--state FILE] [--env FILE]
"""
import argparse
import json
import os
import subprocess
import sys
import time
import urllib.request

from eth_account import Account
from eth_utils import to_checksum_address

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)
import safe_pq_owners as sp  # noqa: E402

LSFK = os.path.join(ROOT, "signers", "leansphincs-f-keccak", "target", "release", "lsfk")
# Deployed 2026-10-20 (docs/deployments.md). Their code equals the current build apart from the
# verifier's metadata hash and the module's own-address immutable; main() checks that.
VERIFIER = "0x89FCf098dCf39fc3445a435504162f91bECa14D4"
MODULE = "0xAA481E835ec1b82E528d6D36D432F9Af440B4295"
SAFE_ART = "out/contracts/Safe.sol/Safe.json"
FACTORY_ART = "out/proxies/SafeProxyFactory.sol/SafeProxyFactory.json"
OWNER_ART = "out/SphincsOwnerAccount.sol/SphincsOwnerAccount.json"
SAFE_FUNDING = 10**16  # 0.01 ETH
SENDER_FUNDING = 2 * 10**16  # 0.02 ETH
SAFE_TX_VALUE = 10**15  # 0.001 ETH
# The Safe's first transaction turns its nonce slot from 0 to 1 (EIP-8037: 64 bytes x 1,530).
SENDER_STATE_GAS = 100_000


class Node:
    def __init__(self, url):
        self.url = url

    def __call__(self, method, params):
        req = urllib.request.Request(self.url, headers={"content-type": "application/json"},
                                     data=json.dumps({"jsonrpc": "2.0", "id": 1, "method": method,
                                                      "params": params}).encode())
        r = json.loads(urllib.request.urlopen(req, timeout=60).read())
        if "error" in r:
            raise RuntimeError(f"{method}: {r['error']}")
        return r["result"]

    def code(self, a):
        return bytes.fromhex(self("eth_getCode", [a, "latest"])[2:])

    def call(self, to, data: bytes) -> bytes:
        return bytes.fromhex(self("eth_call", [{"to": to, "data": "0x" + data.hex()}, "latest"])[2:])

    def receipt(self, h, what):
        for _ in range(100):
            r = self("eth_getTransactionReceipt", [h])
            if r:
                return r
            time.sleep(3)
        sys.exit(f"{what}: {h} not mined within 5 minutes")


def artifact(path):
    a = json.load(open(os.path.join(ROOT, path)))
    return bytes.fromhex(a["bytecode"]["object"][2:]), bytes.fromhex(a["deployedBytecode"]["object"][2:])


def load_env(path):
    env = {}
    for line in open(path):
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            env[k.strip()] = v.strip().strip('"').strip("'")
    return env


class Deployer:
    def __init__(self, node, key):
        self.node, self.acct = node, Account.from_key(key)
        self.chain_id = int(node("eth_chainId", []), 16)

    def send(self, what, to=None, data=b"", value=0):
        base = int(self.node("eth_getBlockByNumber", ["latest", False])["baseFeePerGas"], 16)
        tx = {"from": self.acct.address, "value": hex(value), "data": "0x" + data.hex()}
        if to:
            tx["to"] = to
        gas = int(int(self.node("eth_estimateGas", [tx]), 16) * 1.25) + 50_000
        nonce = int(self.node("eth_getTransactionCount", [self.acct.address, "pending"]), 16)
        fields = {"type": 2, "chainId": self.chain_id, "nonce": nonce, "value": value, "data": data,
                  "gas": gas, "maxFeePerGas": 2 * base + 10**9, "maxPriorityFeePerGas": 10**9}
        if to:
            fields["to"] = to_checksum_address(to)
        signed = self.acct.sign_transaction(fields)
        raw = signed.raw_transaction if hasattr(signed, "raw_transaction") else signed.rawTransaction
        h = self.node("eth_sendRawTransaction", ["0x" + raw.hex()])
        r = self.node.receipt(h, what)
        if int(r["status"], 16) != 1:
            sys.exit(f"{what}: transaction {h} failed")
        print(f"  {what}: tx {h}, gas {int(r['gasUsed'], 16):,}" +
              (f", contract {r['contractAddress']}" if r.get("contractAddress") else ""))
        return h, r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rpc", default="https://rpc1.privacy.ethrex.xyz")
    ap.add_argument("--key-dir", default="/projects/safepq-testnet-keys")
    ap.add_argument("--state", default=os.path.join(HERE, ".frame_safepq_deploy.json"))
    ap.add_argument("--env", default=os.path.join(ROOT, ".env"))
    ap.add_argument("--sender", type=int, default=0, help="owner index that sends the frame transaction")
    ap.add_argument("--cosigner", type=int, default=1, help="owner index that co-signs")
    ap.add_argument("--refund", action="store_true",
                    help="Safe transaction with gasPrice > 0 and no refund receiver: the Safe refunds tx.origin")
    a = ap.parse_args()

    node = Node(a.rpc)
    st = json.load(open(a.state)) if os.path.exists(a.state) else {}

    def save():
        with open(a.state, "w") as f:
            json.dump(st, f, indent=1)

    env = load_env(a.env) if os.path.exists(a.env) else {}
    key = os.environ.get("PRIVATE_KEY") or env.get("PRIVATE_KEY")
    if not key:
        sys.exit("PRIVATE_KEY is not set (.env or environment)")
    dep = Deployer(node, key)
    print(f"chain {dep.chain_id}, deployer {dep.acct.address}, "
          f"balance {int(node('eth_getBalance', [dep.acct.address, 'latest']), 16) / 1e18:.4f} ETH")
    st["chainId"], st["deployer"], st["rpc"] = dep.chain_id, dep.acct.address, a.rpc

    # The shared verifier and module must be the code this repo builds.
    _, v_build = artifact("out/LeanSphincs-FAsm.sol/LeanSphincsFAsm.json")
    v_chain = node.code(VERIFIER)
    meta = int.from_bytes(v_build[-2:], "big") + 2
    assert v_chain[:-meta] == v_build[:-meta], "deployed verifier differs from the build"
    m_build = bytes.fromhex(json.load(open(os.path.join(ROOT, "out/SphincsFrameVerify.yul/SphincsFrameVerify.json")))
                           ["deployedBytecode"]["object"][2:])
    m_chain = node.code(MODULE)
    self_word = bytes(12) + bytes.fromhex(MODULE[2:])
    assert len(m_chain) == len(m_build) and m_chain.replace(self_word, bytes(32)) == m_build.replace(self_word, bytes(32)), \
        "deployed frame module differs from the build"
    st["verifier"], st["frameModule"] = VERIFIER, MODULE
    print(f"verifier {VERIFIER} and module {MODULE}: same code as the build")

    # keys
    os.makedirs(a.key_dir, mode=0o700, exist_ok=True)
    st.setdefault("owners", [])
    while len(st["owners"]) < 3:
        i = len(st["owners"])
        path = os.path.join(a.key_dir, f"safepq-owner{i}.lsfk")
        if not os.path.exists(path):
            subprocess.run([LSFK, "keygen", "--seed-stdin", "--tier", "light", "-o", path],
                           input=os.urandom(32).hex() + "\n", text=True, check=True, capture_output=True)
        info = json.loads(subprocess.run([LSFK, "info", path], check=True, capture_output=True, text=True).stdout)
        st["owners"].append({"keyFile": path, "pkSeed": info["pkSeed"], "pkRoot": info["pkRoot"]})
        save()
    print("keys:", ", ".join(o["keyFile"] for o in st["owners"]))

    # owners
    init, owner_runtime = artifact(OWNER_ART)
    for i, o in enumerate(st["owners"]):
        if "address" in o:
            continue
        args = (bytes.fromhex(o["pkSeed"][2:]) + bytes.fromhex(o["pkRoot"][2:])
                + bytes.fromhex(VERIFIER[2:]).rjust(32, b"\0") + bytes.fromhex(MODULE[2:]).rjust(32, b"\0"))
        h, r = dep.send(f"owner account {i}", data=init + args)
        o["address"], o["deployTx"], o["deployGas"] = r["contractAddress"], h, int(r["gasUsed"], 16)
        save()

    # Safe singleton, factory, proxy
    if "safeSingleton" not in st:
        init, runtime = artifact(SAFE_ART)
        h, r = dep.send("Safe 1.5.0 singleton", data=init)
        st["safeSingleton"], st["safeSingletonTx"], st["safeSingletonGas"] = r["contractAddress"], h, int(r["gasUsed"], 16)
        save()
    if "safeFactory" not in st:
        init, _ = artifact(FACTORY_ART)
        h, r = dep.send("SafeProxyFactory 1.5.0", data=init)
        st["safeFactory"], st["safeFactoryTx"], st["safeFactoryGas"] = r["contractAddress"], h, int(r["gasUsed"], 16)
        save()
    if "safe" not in st:
        owners = [o["address"] for o in st["owners"]]
        setup = sp.selector("setup(address[],uint256,address,bytes,address,address,uint256,address)") + \
            sp.w32(8 * 32) + sp.w32(2) + bytes(32) + sp.w32(8 * 32 + 32 + 32 * len(owners)) + bytes(32 * 4) + \
            sp.w32(len(owners)) + b"".join(sp.addr(x).rjust(32, b"\0") for x in owners) + sp.w32(0)
        create = sp.selector("createProxyWithNonce(address,bytes,uint256)") + \
            sp.addr(st["safeSingleton"]).rjust(32, b"\0") + sp.w32(96) + sp.w32(int(time.time())) + \
            sp.w32(len(setup)) + sp.pad32(setup)
        proxy = "0x" + node.call(st["safeFactory"], create)[12:32].hex()
        h, r = dep.send("2-of-3 Safe proxy", to=st["safeFactory"], data=create)
        st["safe"], st["safeTx"], st["safeGas"] = proxy, h, int(r["gasUsed"], 16)
        save()
    safe = st["safe"]
    assert int.from_bytes(node.call(safe, sp.selector("getThreshold()")), "big") == 2, "threshold"
    print(f"Safe {safe} (2-of-3), owners " + ", ".join(o["address"] for o in st["owners"]))

    # funding
    assert a.sender != a.cosigner and {a.sender, a.cosigner} <= {0, 1, 2}, "sender and co-signer: two owner indices"
    sender, cosigner = st["owners"][a.sender], st["owners"][a.cosigner]
    for name, to, amount in (("Safe", safe, SAFE_FUNDING), (f"owner account {a.sender} (sender)", sender["address"], SENDER_FUNDING)):
        if int(node("eth_getBalance", [to, "latest"]), 16) < amount // 2:
            dep.send(f"fund {name}", to=to, value=amount)

    # the Safe transaction
    safe_nonce = int.from_bytes(node.call(safe, sp.selector("nonce()")), "big")
    refund = (30_000, 50_000, 10**9) if a.refund else (0, 0, 0)  # safeTxGas, baseGas, gasPrice
    stj = {"chainId": dep.chain_id, "safe": safe, "nonce": safe_nonce, "to": dep.acct.address,
           "value": str(SAFE_TX_VALUE), "data": "0x", "operation": 0, "safeTxGas": refund[0], "baseGas": refund[1],
           "gasPrice": refund[2], "gasToken": "0x" + "00" * 20, "refundReceiver": "0x" + "00" * 20}
    t = sp.load_safe_tx(stj)
    h = sp.safe_tx_hash(t)
    get_hash = sp.selector("getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)") + \
        t["to"].rjust(32, b"\0") + sp.w32(t["value"]) + sp.w32(320) + bytes(32) + sp.w32(refund[0]) + sp.w32(refund[1]) + \
        sp.w32(refund[2]) + bytes(64) + sp.w32(safe_nonce) + sp.w32(0)
    assert node.call(safe, get_hash) == h, "tooling Safe transaction hash != Safe.getTransactionHash"
    print(f"Safe transaction: nonce {safe_nonce}, hash 0x{h.hex()} (matches Safe.getTransactionHash)"
          + (f", refund: safeTxGas {refund[0]}, baseGas {refund[1]}, gasPrice {refund[2]}" if a.refund else ""))

    cos = sp.Signer(key_file=cosigner["keyFile"])
    _, _, cosig = cos.sign(h)
    is_valid = sp.selector("isValidSignature(bytes32,bytes)") + h + sp.w32(64) + sp.w32(len(cosig)) + sp.pad32(cosig)
    assert node.call(cosigner["address"], is_valid)[:4] == bytes.fromhex("1626ba7e"), "on-chain isValidSignature"
    print(f"co-signature by owner {a.cosigner}: {len(cosig)} B, accepted by its owner account on chain (eth_call)")

    blob = sp.encode_signatures([{"owner": sp.addr(cosigner["address"]), "sig": cosig},
                                 {"owner": sp.addr(sender["address"]), "s": h}])
    account_nonce = int(node("eth_getTransactionCount", [sender["address"], "latest"]), 16)
    base = int(node("eth_getBlockByNumber", ["latest", False])["baseFeePerGas"], 16)
    prio = 10**9
    state_gas = SENDER_STATE_GAS if safe_nonce == 0 else 0
    tx = sp.build_frame_tx(chain_id=dep.chain_id, sender=sp.addr(sender["address"]), account_nonce=account_nonce,
                           safe_tx=t, signatures_blob=blob, max_fee=2 * base + prio, max_priority_fee_per_gas=prio,
                           exec_gas=sp.default_exec_gas(1), state_gas=state_gas)
    assert sp.public_mempool_problems(tx) == []
    digest = sp.frame_tx_sig_hash(tx, "ethrex")
    _, _, witness = sp.Signer(key_file=sender["keyFile"]).sign(digest)
    tx["signatures"][0]["signature"] = witness
    assert sp.frame_tx_sig_hash(tx, "ethrex") == digest
    raw = "0x" + sp.frame_tx_raw(tx, "ethrex").hex()
    gas = sp.frame_tx_gas(tx)
    print(f"frame tx from owner {a.sender}: account nonce {account_nonce}, sig hash 0x{digest.hex()}, "
          f"raw {len(raw) // 2 - 1:,} B, calldata floor {gas['calldataFloor']:,} (EIP formula)")

    sim = node("ethrex_simulateFrameTransaction", [raw])
    print("simulation:", json.dumps(sim)[:2000])
    st["lastSimulation"] = sim
    save()
    if not (isinstance(sim, dict) and sim.get("valid") and sim.get("executionStatus") == "success"):
        sys.exit("simulation failed; not sending")
    if os.environ.get("DRY_RUN"):
        return

    bal = lambda x: int(node("eth_getBalance", [x, "latest"]), 16)  # noqa: E731
    safe_before, sender_before = bal(safe), bal(sender["address"])
    txh = node("eth_sendRawTransaction", [raw])
    print("submitted", txh)
    r = node.receipt(txh, "frame transaction")
    keep = {k: r.get(k) for k in ("status", "blockNumber", "gasUsed", "from", "payer", "frameReceipts")}
    fr = r.get("frameReceipts") or []
    print(f"status {r.get('status')}, block {int(r['blockNumber'], 16)}, gas {int(r['gasUsed'], 16):,}, payer {r.get('payer')}, "
          "frames " + ", ".join(f"{int(f['status'], 16)}:{int(f['gasUsed'], 16):,}+{int(f.get('stateGasUsed', '0x0'), 16):,}" for f in fr))
    exec_ok = [lg for f in fr for lg in f.get("logs", [])
               if lg["topics"][0] == "0x442e715f626346e8c54381002da614f62bee8d27386535b2521ec8540898556e"]
    payment = int(exec_ok[0]["data"], 16) if exec_ok else None
    new_nonce = int.from_bytes(node.call(safe, sp.selector("nonce()")), "big")
    print(f"ExecutionSuccess: {bool(exec_ok)}, payment {payment}; Safe nonce {safe_nonce} -> {new_nonce}, "
          f"Safe balance -{(safe_before - bal(safe)) / 1e18} ETH, sender balance -{(sender_before - bal(sender['address'])) / 1e18} ETH")
    st.setdefault("frameTxs", []).append({"hash": txh, "sender": a.sender, "cosigner": a.cosigner, "refund": a.refund,
                                          "safeTxHash": "0x" + h.hex(), "sigHash": "0x" + digest.hex(),
                                          "rawBytes": len(raw) // 2 - 1, "receipt": keep, "safePayment": payment,
                                          "safeNonceAfter": new_nonce})
    save()


if __name__ == "__main__":
    main()
