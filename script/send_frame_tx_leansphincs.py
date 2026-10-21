#!/usr/bin/env python3
"""Send an EIP-8141 frame transaction (type 0x06) from a SphincsFrameAccount (leanSphincs variants or C13).

Two frames, the shape the frame module expects:
  frame[0] = VERIFY (mode 1), target = account, flags = 0x03 (APPROVE execution + payment),
             data = verifyFrameAndApprove(uint256 0): the account DELEGATECALLs the frame module,
             which reads signature entry 0 with SIGDATACOPY, STATICCALLs the shared leanSphincs
             verifier on compute_sig_hash(tx), and APPROVEs.
  frame[1] = SENDER (mode 2), target = recipient, value = amount: a plain transfer from the account.
  signatures = [ARBITRARY entry, empty signer, empty msg, leanSphincs signature over the sig hash].

The witness is the ARBITRARY entry's bytes. Its msg is empty, so the entry is elided from the sig
hash, and the signature can only be made after the hash is known: build, hash, sign, insert.

Signing uses the variant's tiered signer and a key file (`lsk` / `lssk` / `lsfk sign-key`), which
verifies every signature before printing it. The transaction is dry-run with
ethrex_simulateFrameTransaction first and sent only if that succeeds.

Wire format: the ethrex hegota-testnet encoder (lambdaclass/ethrex, scripts/hegota-testnet/frametx.py,
MIT OR Apache-2.0), the format the ethrex privacy testnet (chain 8141) runs:
  raw = 0x06 || rlp([chain_id, nonce_keys, nonce_seq, sender, frames, signatures, fees, blob_hashes])
  frame = rlp([mode, flags, target, [execution, state], value, data])
  signature = rlp([scheme, signer, msg, signature_bytes]);  fees = rlp([max_priority, max_fee, max_blob])
  sig_hash = keccak256(0x06 || rlp(envelope with the empty-msg signatures' bytes elided))
The copy below is checked against that file's golden vector on every run.

DRY_RUN=1 stops after the simulation.

Usage: send_frame_tx_leansphincs.py <rpc> <account> <signer_bin> <key_file> <recipient> <amount_wei>
"""
import json
import os
import subprocess
import sys
import time
import urllib.request

from Crypto.Hash import keccak as _keccak


def keccak(b: bytes) -> bytes:
    return _keccak.new(digest_bits=256, data=b).digest()


# ---------- RLP and the frame-tx envelope (from ethrex frametx.py) ----------
def rlp_bytes(b: bytes) -> bytes:
    if len(b) == 1 and b[0] < 0x80:
        return b
    if len(b) < 56:
        return bytes([0x80 + len(b)]) + b
    lb = len(b).to_bytes((len(b).bit_length() + 7) // 8, "big")
    return bytes([0xb7 + len(lb)]) + lb + b


def rlp_list(items) -> bytes:
    body = b"".join(items)
    if len(body) < 56:
        return bytes([0xc0 + len(body)]) + body
    lb = len(body).to_bytes((len(body).bit_length() + 7) // 8, "big")
    return bytes([0xf7 + len(lb)]) + lb + body


def rlp_int(x: int) -> bytes:
    return rlp_bytes(b"") if x == 0 else rlp_bytes(x.to_bytes((x.bit_length() + 7) // 8, "big"))


def addr20(a) -> bytes:
    if isinstance(a, str):
        return bytes.fromhex(a.removeprefix("0x").removeprefix("0X"))
    if isinstance(a, int):
        return a.to_bytes(20, "big")
    return bytes(a)


class Frame:
    def __init__(self, mode, flags, target, gas_limit, value, data, state_limit=0):
        self.mode, self.flags, self.target = mode, flags, target
        self.gas_limit, self.value, self.data, self.state_limit = gas_limit, value, data, state_limit

    def rlp(self):
        tgt = rlp_bytes(addr20(self.target)) if self.target is not None else rlp_bytes(b"")
        limits = rlp_list([rlp_int(self.gas_limit), rlp_int(self.state_limit)])
        return rlp_list([rlp_int(self.mode), rlp_int(self.flags), tgt, limits, rlp_int(self.value),
                         rlp_bytes(self.data)])


class FrameSig:
    ARBITRARY, SECP256K1 = 0, 1

    def __init__(self, scheme, signer, msg, signature):
        self.scheme, self.signer, self.msg, self.signature = scheme, signer, msg, signature

    def rlp(self, elide=False):
        sig = b"" if (elide and len(self.msg) == 0) else self.signature
        return rlp_list([rlp_int(self.scheme), rlp_bytes(addr20(self.signer)), rlp_bytes(self.msg), rlp_bytes(sig)])


class FrameTx:
    def __init__(self, chain_id, nonce_keys, nonce_seq, sender, frames, signatures, max_priority_fee, max_fee,
                 max_blob_fee=0):
        self.chain_id, self.nonce_keys, self.nonce_seq, self.sender = chain_id, nonce_keys, nonce_seq, sender
        self.frames, self.signatures = frames, signatures
        self.max_priority_fee, self.max_fee, self.max_blob_fee = max_priority_fee, max_fee, max_blob_fee

    def _envelope(self, elide):
        return [rlp_int(self.chain_id), rlp_list([rlp_int(k) for k in self.nonce_keys]), rlp_int(self.nonce_seq),
                rlp_bytes(addr20(self.sender)), rlp_list([f.rlp() for f in self.frames]),
                rlp_list([s.rlp(elide=elide) for s in self.signatures]),
                rlp_list([rlp_int(self.max_priority_fee), rlp_int(self.max_fee), rlp_int(self.max_blob_fee)]),
                rlp_list([])]

    def raw(self) -> bytes:
        return bytes([0x06]) + rlp_list(self._envelope(False))

    def sig_hash(self) -> bytes:
        return keccak(bytes([0x06]) + rlp_list(self._envelope(True)))


def check_golden():
    """ethrex frametx.py's golden vector: the copied encoder must reproduce it exactly."""
    tx = FrameTx(1, [0], 7, 0xABCD,
                 [Frame(1, 3, None, 0x5208, 0, bytes([0x11, 0x22])), Frame(2, 0, 0x1234, 0x9c40, 0, b"")],
                 [FrameSig(FrameSig.SECP256K1, 0xABCD, b"", bytes([0x01] * 65))], 0x3b9aca00, 0x6fc23ac00)
    want = ("f8b201c1800794000000000000000000000000000000000000abcdeccc010380c48252088080821122de0280940000000000"
            "000000000000000000000000001234c4829c40808080f85cf85a0194000000000000000000000000000000000000abcd80b8"
            "4101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101"
            "01010101010101010101010101010101cc843b9aca008506fc23ac0080c0")
    assert tx.raw()[1:].hex() == want, "frame-tx encoder does not match ethrex's golden RLP"
    assert tx.sig_hash().hex() == "73827d510b0029220c237a46b27f6b6b8e7a3fd3b52c42a55c6c6e343fc45951", "golden sig hash"


# ---------- node access ----------
def rpc(url, method, params):
    req = urllib.request.Request(url, headers={"content-type": "application/json"},
                                 data=json.dumps({"jsonrpc": "2.0", "id": 1, "method": method,
                                                  "params": params}).encode())
    r = json.loads(urllib.request.urlopen(req, timeout=30).read())
    if "error" in r:
        raise RuntimeError(f"{method}: {r['error']}")
    return r["result"]


def sign_hash(signer_bin, key_file, digest: bytes) -> bytes:
    """The signature over `digest`. leanSphincs: `<signer> sign-key <key file>` (ABI: pkSeed, pkRoot, bytes sig).
    C13 (a `.json` key file from `signer-c13 keygen`): `signer-c13 sign-with <seed> <sk_seed> <root>` (raw hex)."""
    if key_file.endswith(".json"):
        k = json.load(open(key_file))
        out = subprocess.run([signer_bin, "sign-with", k["seed"], k["sk_seed"], k["root"], "0x" + digest.hex()],
                             check=True, capture_output=True, text=True).stdout.strip()
        return bytes.fromhex(out.removeprefix("0x"))
    out = subprocess.run([signer_bin, "sign-key", key_file, "0x" + digest.hex()], check=True, capture_output=True,
                         text=True).stdout.strip()
    abi = bytes.fromhex(out.removeprefix("0x"))
    length = int.from_bytes(abi[96:128], "big")
    return abi[128:128 + length]


VERIFY_SELECTOR = keccak(b"verifyFrameAndApprove(uint256)")[:4]
NEW_ACCOUNT_STATE_GAS = 120 * 1530  # EIP-8037: funding a new recipient, from the SENDER frame's state budget


def main():
    if len(sys.argv) != 7:
        sys.exit(__doc__.strip().splitlines()[-1])
    url, account, signer_bin, key_file, recipient, amount = sys.argv[1:6] + [int(sys.argv[6])]
    check_golden()

    chain_id = int(rpc(url, "eth_chainId", []), 16)
    nonce = int(rpc(url, "eth_getTransactionCount", [account, "latest"]), 16)
    base_fee = int(rpc(url, "eth_getBlockByNumber", ["latest", False]).get("baseFeePerGas", "0x0"), 16)
    balance = int(rpc(url, "eth_getBalance", [account, "latest"]), 16)
    print(f"account {account}: balance {balance / 1e18:.4f} ETH, nonce {nonce}; chain {chain_id}, base fee {base_fee}")
    max_priority = 10**9
    max_fee = 2 * base_fee + max_priority

    tx = FrameTx(chain_id, [0], nonce, account,
                 [Frame(1, 0x03, account, 300_000, 0, VERIFY_SELECTOR + (0).to_bytes(32, "big")),
                  Frame(2, 0, recipient, 30_000, amount, b"", state_limit=NEW_ACCOUNT_STATE_GAS)],
                 [FrameSig(FrameSig.ARBITRARY, b"", b"", b"")], max_priority, max_fee)
    digest = tx.sig_hash()
    t0 = time.time()
    sig = sign_hash(signer_bin, key_file, digest)
    tx.signatures = [FrameSig(FrameSig.ARBITRARY, b"", b"", sig)]
    assert tx.sig_hash() == digest, "the witness must not change the sig hash"
    raw = "0x" + tx.raw().hex()
    print(f"sig hash 0x{digest.hex()}; witness {len(sig)} B signed in {time.time() - t0:.2f} s; raw tx {len(tx.raw())} B")

    sim = rpc(url, "ethrex_simulateFrameTransaction", [raw])
    print("simulation:", json.dumps(sim)[:1500])
    if not (isinstance(sim, dict) and sim.get("valid") and sim.get("executionStatus") == "success"):
        sys.exit("simulation failed; not sending")
    if os.environ.get("DRY_RUN"):
        return 0

    txhash = rpc(url, "eth_sendRawTransaction", [raw])
    print("submitted", txhash)
    for _ in range(60):
        rcpt = rpc(url, "eth_getTransactionReceipt", [txhash])
        if rcpt:
            print(json.dumps({k: rcpt.get(k) for k in ("status", "blockNumber", "gasUsed", "from", "payer",
                                                        "frameReceipts")}, indent=1))
            return 0 if rcpt.get("status") in ("0x1", 1) else 1
        time.sleep(3)
    sys.exit("not mined within 3 minutes")


if __name__ == "__main__":
    sys.exit(main())
