#!/usr/bin/env python3
"""Offline tooling for a Safe whose owners are SphincsOwnerAccounts (leanSphincs-f) on EIP-8141.

One owner, the sender, submits a frame transaction from their own owner account:
  frame[0] = VERIFY (mode 1), flags 0x3 (self_verify), target = the sender's owner account,
             data = verifyFrameAndApprove(uint256 0): the account checks the leanSphincs-f
             signature in tx.signatures[0] over compute_sig_hash(tx) and APPROVEs.
  frame[1] = SENDER (mode 2), target = the Safe, data = execTransaction(...).
  signatures = [ARBITRARY entry, empty signer, empty msg, the sender's leanSphincs-f signature].
Inside execTransaction the Safe counts the sender as a pre-validated signature (v = 1, because it
is msg.sender) and checks every co-signer as a contract signature (v = 0) by calling
isValidSignature on that co-signer's owner account. Design: docs/safe-pq-owners.md.

What a key signs is always a hash this tool computed itself:
  cosign    signs the Safe transaction hash of the Safe transaction file it was given;
  frame-tx  signs the signature hash of the frame transaction it assembled.
Neither takes a digest from the command line, so a co-signer cannot be handed a frame
transaction's hash to sign (or the reverse) through this tool.

Nothing here talks to a node. `frame-tx` prints the raw transaction; sending it is up to you.

Commands (addresses and byte strings are 0x-hex, amounts decimal or 0x-hex):
  hash       <safe-tx.json>
  cosign     <safe-tx.json> --owner <owner account> (--key-file F | --test-seed HEX [--b N]) [-o cosig.json]
  signatures <safe-tx.json> --sender <owner account> [cosig.json ...]
  frame-tx   <safe-tx.json> --sender <owner account> --account-nonce N
             (--max-fee WEI | --base-fee WEI) [--max-priority-fee-per-gas WEI]
             (--key-file F | --test-seed HEX [--b N]) [cosig.json ...]
             [--wire eip|ethrex] [--verify-gas 60000] [--exec-gas N] [--state-gas N] [-o tx.json]
  selftest

<safe-tx.json>:
  {"chainId": 8141, "safe": "0x..", "nonce": 0, "to": "0x..", "value": "1000", "data": "0x",
   "operation": 0, "safeTxGas": 0, "baseGas": 0, "gasPrice": 0,
   "gasToken": "0x0000000000000000000000000000000000000000",
   "refundReceiver": "0x0000000000000000000000000000000000000000"}

Signing uses the leanSphincs-f CLI (signers/leansphincs-f-keccak, `lsfk`): `--key-file` runs
`lsfk sign-key` on a key file from `lsfk keygen`; `--test-seed` runs `lsfk sign <seed> <b>`, which
puts the seed on the command line and is for test vectors only. A binary older than its crate
sources is refused (--allow-stale-binary overrides).

Wire formats (--wire):
  eip     EIP-8141 as of ethereum/EIPs master dc5d5fa688b7 (2026-11-01):
            0x06 || rlp([chain_id, nonce, sender, frames, signatures,
                         [max_fee, max_priority_fee_per_gas], blob_versioned_hashes])
          The signature hash replaces the bytes of every empty-msg signature by their length.
          max_fee is a total budget in wei, not a price per gas.
  ethrex  the ethrex hegota-testnet encoder (lambdaclass/ethrex scripts/hegota-testnet/frametx.py),
          as script/send_frame_tx_leansphincs.py:
            0x06 || rlp([chain_id, nonce_keys, nonce_seq, sender, frames, signatures,
                         [max_priority_fee_per_gas, max_fee_per_gas, max_blob_fee], blob_hashes])
          The signature hash drops the bytes of every empty-msg signature. Here --max-fee is a
          price per gas.
The gas figures printed are the current EIP's formulas (EIP-8141 Gas Accounting) in both cases.

Only the standard library is needed (pycryptodome's keccak is used when it is installed).
"""
import argparse
import json
import os
import subprocess
import sys

# ───────────────────────────── keccak256 ─────────────────────────────
try:
    from Crypto.Hash import keccak as _pyc_keccak

    def keccak256(data: bytes) -> bytes:
        return _pyc_keccak.new(digest_bits=256, data=data).digest()
except ImportError:
    _RC = [
        0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
        0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
        0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
        0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
        0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
        0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
    ]
    _ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
    _W = (1 << 64) - 1

    def _rol(x, n):
        return ((x << n) | (x >> (64 - n))) & _W if n else x

    def _f1600(s):
        for rc in _RC:
            c = [s[x][0] ^ s[x][1] ^ s[x][2] ^ s[x][3] ^ s[x][4] for x in range(5)]
            d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
            s = [[s[x][y] ^ d[x] for y in range(5)] for x in range(5)]
            b = [[0] * 5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    b[y][(2 * x + 3 * y) % 5] = _rol(s[x][y], _ROT[x][y])
            s = [[b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
            s[0][0] ^= rc
        return s

    def keccak256(data: bytes) -> bytes:
        rate = 136
        p = bytearray(data) + b"\x01" + b"\x00" * ((-len(data) - 1) % rate)
        p[-1] |= 0x80
        s = [[0] * 5 for _ in range(5)]
        for off in range(0, len(p), rate):
            blk = p[off:off + rate]
            for i in range(rate // 8):
                s[i % 5][i // 5] ^= int.from_bytes(blk[8 * i:8 * i + 8], "little")
            s = _f1600(s)
        return b"".join(s[i % 5][i // 5].to_bytes(8, "little") for i in range(4))

assert keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"


# ───────────────────────────── small helpers ─────────────────────────────
def hexb(s) -> bytes:
    if isinstance(s, (bytes, bytearray)):
        return bytes(s)
    s = s[2:] if s[:2] in ("0x", "0X") else s
    return bytes.fromhex(s)


def num(x) -> int:
    if isinstance(x, int):
        return x
    return int(x, 16) if x[:2] in ("0x", "0X") else int(x)


def addr(a) -> bytes:
    b = hexb(a)
    if len(b) != 20:
        raise ValueError(f"not a 20-byte address: {a}")
    return b


def w32(x: int) -> bytes:
    return x.to_bytes(32, "big")


def pad32(b: bytes) -> bytes:
    return b + b"\x00" * ((-len(b)) % 32)


def selector(sig: str) -> bytes:
    return keccak256(sig.encode())[:4]


ZERO_ADDRESS = b"\x00" * 20
SIG_LEN = 4660  # leanSphincs-f

# ───────────────────────────── Safe transaction hash ─────────────────────────────
DOMAIN_SEPARATOR_TYPEHASH = keccak256(b"EIP712Domain(uint256 chainId,address verifyingContract)")
SAFE_TX_TYPEHASH = keccak256(
    b"SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,"
    b"uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)")
assert DOMAIN_SEPARATOR_TYPEHASH.hex() == "47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218"
assert SAFE_TX_TYPEHASH.hex() == "bb8310d486368db6bd6f849402fdd73ad53d316b5a4b2644ad6efe0f941286d8"

SAFE_TX_FIELDS = ("chainId", "safe", "nonce", "to", "value", "data", "operation", "safeTxGas", "baseGas",
                  "gasPrice", "gasToken", "refundReceiver")


def load_safe_tx(obj) -> dict:
    """Normalise a Safe transaction description (see the module docstring) to ints and bytes."""
    missing = [k for k in SAFE_TX_FIELDS if k not in obj]
    if missing:
        raise ValueError(f"Safe transaction is missing {missing}")
    t = {
        "chainId": num(obj["chainId"]), "safe": addr(obj["safe"]), "nonce": num(obj["nonce"]),
        "to": addr(obj["to"]), "value": num(obj["value"]), "data": hexb(obj["data"]),
        "operation": num(obj["operation"]), "safeTxGas": num(obj["safeTxGas"]), "baseGas": num(obj["baseGas"]),
        "gasPrice": num(obj["gasPrice"]), "gasToken": addr(obj["gasToken"]),
        "refundReceiver": addr(obj["refundReceiver"]),
    }
    if t["operation"] not in (0, 1):
        raise ValueError("operation must be 0 (CALL) or 1 (DELEGATECALL)")
    return t


def safe_domain_separator(chain_id: int, safe: bytes) -> bytes:
    return keccak256(DOMAIN_SEPARATOR_TYPEHASH + w32(chain_id) + safe.rjust(32, b"\x00"))


def safe_tx_struct_hash(t: dict) -> bytes:
    return keccak256(
        SAFE_TX_TYPEHASH + t["to"].rjust(32, b"\x00") + w32(t["value"]) + keccak256(t["data"]) + w32(t["operation"])
        + w32(t["safeTxGas"]) + w32(t["baseGas"]) + w32(t["gasPrice"]) + t["gasToken"].rjust(32, b"\x00")
        + t["refundReceiver"].rjust(32, b"\x00") + w32(t["nonce"]))


def safe_tx_preimage(t: dict) -> bytes:
    """0x19 0x01 || domainSeparator || structHash: what Safe <= 1.4.1 passes to
    isValidSignature(bytes,bytes). Its keccak256 is the Safe transaction hash."""
    return b"\x19\x01" + safe_domain_separator(t["chainId"], t["safe"]) + safe_tx_struct_hash(t)


def safe_tx_hash(t: dict) -> bytes:
    return keccak256(safe_tx_preimage(t))


# ───────────────────────────── Safe signatures ─────────────────────────────
def encode_signatures(entries) -> bytes:
    """The Safe `signatures` bytes. Each entry is {"owner": bytes20, "sig": bytes} for a contract
    signature (v = 0) or {"owner": bytes20, "s": bytes32} for a pre-validated one (v = 1).
    Entries are sorted by owner, ascending, as checkNSignatures requires; a repeated owner is an
    error (the Safe would reject it with GS026)."""
    entries = sorted(entries, key=lambda e: e["owner"])
    for a, b in zip(entries, entries[1:]):
        if a["owner"] == b["owner"]:
            raise ValueError(f"owner 0x{a['owner'].hex()} appears twice")
    static, dynamic = b"", b""
    offset = 65 * len(entries)
    for e in entries:
        if "sig" in e:
            static += e["owner"].rjust(32, b"\x00") + w32(offset) + b"\x00"
            dynamic += w32(len(e["sig"])) + e["sig"]
            offset += 32 + len(e["sig"])
        else:
            if len(e["s"]) != 32:
                raise ValueError("s must be 32 bytes")
            static += e["owner"].rjust(32, b"\x00") + e["s"] + b"\x01"
    return static + dynamic


def service_signature(owner: bytes, sig: bytes) -> bytes:
    """One contract signature as a confirmation for the Safe Transaction Service: the 65-byte
    static part with the offset of a one-signature blob (65), then the length and the bytes.
    65 + 32 + 4660 = 4,757 bytes for leanSphincs-f; the service's limit is 5,000
    (SIGNATURE_LENGTH in safe-transaction-service utils/constants.py)."""
    return encode_signatures([{"owner": owner, "sig": sig}])


EXEC_TRANSACTION = selector("execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)")
assert EXEC_TRANSACTION.hex() == "6a761202"


def exec_transaction_calldata(t: dict, signatures: bytes) -> bytes:
    head_len = 10 * 32
    data_tail = w32(len(t["data"])) + pad32(t["data"])
    sig_tail = w32(len(signatures)) + pad32(signatures)
    head = (t["to"].rjust(32, b"\x00") + w32(t["value"]) + w32(head_len) + w32(t["operation"]) + w32(t["safeTxGas"])
            + w32(t["baseGas"]) + w32(t["gasPrice"]) + t["gasToken"].rjust(32, b"\x00")
            + t["refundReceiver"].rjust(32, b"\x00") + w32(head_len + len(data_tail)))
    return EXEC_TRANSACTION + head + data_tail + sig_tail


# ───────────────────────────── RLP + frame transaction ─────────────────────────────
def _rlp_len(n, off):
    if n < 56:
        return bytes([off + n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([off + 55 + len(b)]) + b


def rlp(x) -> bytes:
    if isinstance(x, int):
        x = x.to_bytes((x.bit_length() + 7) // 8, "big") if x else b""
    if isinstance(x, (bytes, bytearray)):
        x = bytes(x)
        if len(x) == 1 and x[0] < 0x80:
            return x
        return _rlp_len(len(x), 0x80) + x
    body = b"".join(rlp(i) for i in x)
    return _rlp_len(len(body), 0xC0) + body


FRAME_TX_TYPE = 0x06
DEFAULT, VERIFY, SENDER = 0, 1, 2
ARBITRARY, SECP256K1, P256 = 0, 1, 2
APPROVE_PAYMENT, APPROVE_EXECUTION, APPROVE_SCOPE_MASK, ATOMIC_BATCH_FLAG = 1, 2, 3, 4
WIRES = ("eip", "ethrex")
EIP_REVISION = "dc5d5fa688b7"  # ethereum/EIPs master, 2026-11-01


def frame_tx_payload(tx: dict, wire: str, for_sig_hash: bool):
    """The RLP item list of a frame transaction. `tx`:
      chain_id, nonce, sender (bytes20), frames [{mode, flags, target (bytes20 or None), execution,
      state, value, data}], signatures [{scheme, signer, msg, signature}], max_fee,
      max_priority_fee_per_gas."""
    frames = [[f["mode"], f["flags"], f["target"] or b"", [f["execution"], f["state"]], f["value"], f["data"]]
              for f in tx["frames"]]
    sigs = []
    for s in tx["signatures"]:
        raw = s["signature"]
        if for_sig_hash and len(s["msg"]) == 0:
            # eip: elide the bytes but commit to their length (an RLP integer). ethrex: drop them.
            raw = len(raw) if wire == "eip" else b""
        sigs.append([s["scheme"], s["signer"], s["msg"], raw])
    if wire == "eip":
        return [tx["chain_id"], tx["nonce"], tx["sender"], frames, sigs,
                [tx["max_fee"], tx["max_priority_fee_per_gas"]], []]
    if wire == "ethrex":
        # nonce_keys = [0], nonce_seq = nonce; fees = [max_priority, max_fee (per gas), max_blob = 0].
        return [tx["chain_id"], [0], tx["nonce"], tx["sender"], frames, sigs,
                [tx["max_priority_fee_per_gas"], tx["max_fee"], 0], []]
    raise ValueError(f"unknown wire format {wire}")


def frame_tx_raw(tx: dict, wire: str) -> bytes:
    return bytes([FRAME_TX_TYPE]) + rlp(frame_tx_payload(tx, wire, False))


def frame_tx_sig_hash(tx: dict, wire: str) -> bytes:
    return keccak256(bytes([FRAME_TX_TYPE]) + rlp(frame_tx_payload(tx, wire, True)))


# EIP-8141 Gas Accounting (and the constants it takes from EIP-2780, EIP-7976, EIP-8037).
FRAME_TX_INTRINSIC_COST = 12_000
FRAME_TX_PER_FRAME_COST = 475
TX_VALUE_COST = 6_000
STANDARD_TOKEN_COST = 4
TOTAL_COST_FLOOR_PER_TOKEN = 16
SIGNATURE_GAS = {ARBITRARY: 100, SECP256K1: 2_800, P256: 6_700}
MAX_VERIFY_GAS = 100_000
MAX_VERIFY_STATE_GAS = 500_000
CPSB = 1_530
STATE_BYTES_PER_NEW_ACCOUNT = 120
STATE_BYTES_PER_STORAGE_SET = 64


def _tokens_in(data: bytes) -> int:
    zero = data.count(0)
    return zero + (len(data) - zero) * 4


def frame_tx_gas(tx: dict) -> dict:
    """intrinsic, calldata floor and limits, from the transaction fields alone."""
    frames, sigs = tx["frames"], tx["signatures"]
    signature_verification_cost = sum(SIGNATURE_GAS[s["scheme"]] for s in sigs)
    frame_data_cost = sum(STANDARD_TOKEN_COST * _tokens_in(f["data"]) for f in frames)
    signature_data_cost = sum(
        STANDARD_TOKEN_COST * (_tokens_in(s["signer"]) + _tokens_in(s["msg"])
                               # elided bytes are priced as if all non-zero
                               + (4 * len(s["signature"]) if len(s["msg"]) == 0 else _tokens_in(s["signature"])))
        for s in sigs)
    value_transfer_cost = sum(TX_VALUE_COST for f in frames
                              if f["value"] > 0 and f["target"] is not None and f["target"] != tx["sender"])
    base = FRAME_TX_INTRINSIC_COST + len(frames) * FRAME_TX_PER_FRAME_COST + signature_verification_cost \
        + value_transfer_cost
    intrinsic = base + frame_data_cost + signature_data_cost
    floor_bytes = sum(len(f["data"]) for f in frames) \
        + sum(len(s["signer"]) + len(s["msg"]) + len(s["signature"]) for s in sigs)
    calldata_floor = base + TOTAL_COST_FLOOR_PER_TOKEN * 4 * floor_bytes
    execution_limits = sum(f["execution"] for f in frames)
    state_limits = sum(f["state"] for f in frames)
    standard_gas_limit = intrinsic + execution_limits + state_limits
    return {
        "intrinsic": intrinsic, "calldataFloor": calldata_floor, "floorBytes": floor_bytes,
        "executionLimits": execution_limits, "stateLimits": state_limits,
        "standardGasLimit": standard_gas_limit, "maxGas": max(standard_gas_limit, calldata_floor + state_limits),
    }


def validation_prefix_len(tx: dict):
    """Length of the recognised public-mempool validation prefix, read from the frames' shape
    (the frame that approves payment ends it), or None."""
    fr = tx["frames"]

    def is_verify(f, flags):
        return f["mode"] == VERIFY and f["flags"] == flags

    def targets_sender(f):
        return f["target"] is None or f["target"] == tx["sender"]

    i = 0
    if fr and fr[0]["mode"] == DEFAULT and fr[0]["flags"] == 0:
        i = 1  # deploy
    if i < len(fr) and is_verify(fr[i], 0x3) and targets_sender(fr[i]):
        return i + 1  # self_verify
    if i + 1 < len(fr) and is_verify(fr[i], 0x2) and targets_sender(fr[i]) and is_verify(fr[i + 1], 0x1):
        return i + 2  # only_verify, pay
    return None


def public_mempool_problems(tx: dict) -> list:
    """Structural rules of EIP-8141's public mempool that follow from the transaction alone
    (Structural Rules 1, 5, 6 and 8). Simulating the prefix is the node's job."""
    n = validation_prefix_len(tx)
    if n is None:
        return ["the frames do not start with a recognised validation prefix"]
    problems = []
    prefix = tx["frames"][:n]
    verify_gas = sum(f["execution"] for f in prefix) + sum(SIGNATURE_GAS[s["scheme"]] for s in tx["signatures"])
    if verify_gas > MAX_VERIFY_GAS:
        problems.append(f"validation prefix declares {verify_gas} gas, over MAX_VERIFY_GAS = {MAX_VERIFY_GAS}")
    if sum(f["state"] for f in prefix) > MAX_VERIFY_STATE_GAS:
        problems.append("validation prefix declares more state gas than MAX_VERIFY_STATE_GAS")
    if any(f["flags"] & ATOMIC_BATCH_FLAG for f in prefix):
        problems.append("a frame of the validation prefix has the atomic batch flag")
    if any(f["mode"] == VERIFY for f in tx["frames"][n:]):
        problems.append("a VERIFY frame follows the validation prefix")
    return problems


VERIFY_FRAME_SELECTOR = selector("verifyFrameAndApprove(uint256)")
# The sender's VERIFY frame uses 50,547..51,614 gas for any admissible leanSphincs-f signature
# (measured 51,069 and 51,079, docs/safe-pq-owners.md) and needs about 1,350 more than it uses
# as its limit, for the 63/64 rule at two call depths. 60,000 leaves room, and with the 100 gas
# of the one ARBITRARY entry the validation prefix declares 60,100 of MAX_VERIFY_GAS = 100,000.
DEFAULT_VERIFY_GAS = 60_000


def build_frame_tx(*, chain_id, sender, account_nonce, safe_tx, signatures_blob, max_fee, max_priority_fee_per_gas,
                   verify_gas=DEFAULT_VERIFY_GAS, exec_gas, state_gas=0, witness_len=SIG_LEN) -> dict:
    """[self_verify, SENDER -> Safe.execTransaction] with a placeholder witness of the right
    length (the signature hash commits to that length under the current EIP text)."""
    if safe_tx["chainId"] != chain_id:
        raise ValueError("the Safe transaction is for another chain")
    return {
        "chain_id": chain_id, "nonce": account_nonce, "sender": sender,
        "frames": [
            {"mode": VERIFY, "flags": APPROVE_SCOPE_MASK, "target": sender, "execution": verify_gas, "state": 0,
             "value": 0, "data": VERIFY_FRAME_SELECTOR + w32(0)},
            {"mode": SENDER, "flags": 0, "target": safe_tx["safe"], "execution": exec_gas, "state": state_gas,
             "value": 0, "data": exec_transaction_calldata(safe_tx, signatures_blob)},
        ],
        "signatures": [{"scheme": ARBITRARY, "signer": b"", "msg": b"", "signature": b"\x00" * witness_len}],
        "max_fee": max_fee, "max_priority_fee_per_gas": max_priority_fee_per_gas,
    }


def default_exec_gas(cosigners: int) -> int:
    """A SENDER frame limit with room to spare for a simple inner call: execTransaction measured
    37 K with no co-signer and up to 87 K more per co-signer (Safe main, revm). Raise it with
    --exec-gas for a Safe transaction that does real work. Unused gas is not charged."""
    return 150_000 + 100_000 * cosigners


# ───────────────────────────── leanSphincs-f signer ─────────────────────────────
DEFAULT_LSFK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "signers", "leansphincs-f-keccak",
                            "target", "release", "lsfk")


def _stale_sources(binary: str) -> list:
    """Crate sources newer than the binary (parameters are compile-time: a stale binary signs
    under the old scheme with no error)."""
    crate = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(binary)), "..", ".."))
    built = os.path.getmtime(binary)
    candidates = [os.path.join(crate, "Cargo.toml"), os.path.join(crate, "Cargo.lock")]
    for root, _dirs, files in os.walk(os.path.join(crate, "src")):
        candidates += [os.path.join(root, f) for f in files if f.endswith(".rs")]
    return [c for c in candidates if os.path.exists(c) and os.path.getmtime(c) > built]


class Signer:
    def __init__(self, *, key_file=None, test_seed=None, b=8, lsfk=DEFAULT_LSFK, allow_stale=False):
        if (key_file is None) == (test_seed is None):
            raise ValueError("give exactly one of --key-file and --test-seed")
        self.key_file, self.test_seed, self.b, self.lsfk = key_file, test_seed, b, lsfk
        if not os.path.exists(lsfk):
            sys.exit(f"{lsfk} is not built: (cd signers/leansphincs-f-keccak && cargo build --release)")
        stale = _stale_sources(lsfk)
        if stale and not allow_stale:
            sys.exit(f"{lsfk} is older than {', '.join(stale)}: rebuild it "
                     "(cd signers/leansphincs-f-keccak && cargo build --release), or pass --allow-stale-binary")

    def sign(self, digest: bytes):
        """(pkSeed, pkRoot, signature) for a 32-byte digest."""
        assert len(digest) == 32
        if self.key_file:
            cmd = [self.lsfk, "sign-key", self.key_file, "0x" + digest.hex()]
        else:
            cmd = [self.lsfk, "sign", "0x" + hexb(self.test_seed).hex(), str(self.b), "0x" + digest.hex()]
        out = subprocess.run(cmd, check=True, capture_output=True, text=True).stdout.strip()
        abi = hexb(out)  # abi.encode(bytes32 pkSeed, bytes32 pkRoot, bytes sig)
        n = int.from_bytes(abi[96:128], "big")
        sig = abi[128:128 + n]
        if len(sig) != SIG_LEN:
            raise RuntimeError(f"signer returned {len(sig)} bytes, expected {SIG_LEN}")
        return abi[0:32], abi[32:64], sig


# ───────────────────────────── CLI ─────────────────────────────
def _hex(b: bytes) -> str:
    return "0x" + b.hex()


def _read_json(path):
    with open(path) as f:
        return json.load(f)


def _emit(obj, out):
    text = json.dumps(obj, indent=1)
    if out:
        with open(out, "w") as f:
            f.write(text + "\n")
    else:
        print(text)


def _load_cosigs(paths, expected_hash: bytes) -> list:
    entries = []
    for p in paths:
        c = _read_json(p)
        if hexb(c["safeTxHash"]) != expected_hash:
            sys.exit(f"{p} is a co-signature over {c['safeTxHash']}, not over this Safe transaction")
        entries.append({"owner": addr(c["owner"]), "sig": hexb(c["signature"])})
    return entries


def cmd_hash(a):
    t = load_safe_tx(_read_json(a.safe_tx))
    _emit({"safeTxHash": _hex(safe_tx_hash(t)), "domainSeparator": _hex(safe_domain_separator(t["chainId"], t["safe"])),
           "structHash": _hex(safe_tx_struct_hash(t)), "preimage": _hex(safe_tx_preimage(t))}, None)


def cmd_cosign(a):
    t = load_safe_tx(_read_json(a.safe_tx))
    h = safe_tx_hash(t)
    owner = addr(a.owner)
    signer = Signer(key_file=a.key_file, test_seed=a.test_seed, b=a.b, lsfk=a.lsfk, allow_stale=a.allow_stale_binary)
    pk_seed, pk_root, sig = signer.sign(h)
    svc = service_signature(owner, sig)
    _emit({"safeTxHash": _hex(h), "owner": _hex(owner), "pkSeed": _hex(pk_seed), "pkRoot": _hex(pk_root),
           "signature": _hex(sig), "serviceSignature": _hex(svc), "serviceSignatureBytes": len(svc)}, a.output)


def cmd_signatures(a):
    t = load_safe_tx(_read_json(a.safe_tx))
    h = safe_tx_hash(t)
    entries = _load_cosigs(a.cosigs, h) + [{"owner": addr(a.sender), "s": h}]
    blob = encode_signatures(entries)
    _emit({"safeTxHash": _hex(h), "signatures": _hex(blob), "signaturesBytes": len(blob),
           "execTransaction": _hex(exec_transaction_calldata(t, blob))}, None)


def cmd_frame_tx(a):
    t = load_safe_tx(_read_json(a.safe_tx))
    h = safe_tx_hash(t)
    sender = addr(a.sender)
    cosigs = _load_cosigs(a.cosigs, h)
    # The sender's entry: v = 1, s = the Safe transaction hash (binding on Safe main, unread before).
    blob = encode_signatures(cosigs + [{"owner": sender, "s": h}])
    exec_gas = num(a.exec_gas) if a.exec_gas is not None else default_exec_gas(len(cosigs))
    prio = num(a.max_priority_fee_per_gas)
    tx = build_frame_tx(chain_id=t["chainId"], sender=sender, account_nonce=num(a.account_nonce), safe_tx=t,
                        signatures_blob=blob, max_fee=0, max_priority_fee_per_gas=prio,
                        verify_gas=num(a.verify_gas), exec_gas=exec_gas, state_gas=num(a.state_gas))
    gas = frame_tx_gas(tx)
    if a.max_fee is not None:
        tx["max_fee"] = num(a.max_fee)
    elif a.wire == "eip":
        # A total budget: twice the base fee plus the tip, on the most gas the transaction can use.
        tx["max_fee"] = gas["maxGas"] * (2 * num(a.base_fee) + prio)
    else:
        tx["max_fee"] = 2 * num(a.base_fee) + prio  # a price per gas
    problems = public_mempool_problems(tx)
    if problems and not a.allow_non_mempool:
        sys.exit("not a public-mempool transaction: " + "; ".join(problems))

    digest = frame_tx_sig_hash(tx, a.wire)
    signer = Signer(key_file=a.key_file, test_seed=a.test_seed, b=a.b, lsfk=a.lsfk, allow_stale=a.allow_stale_binary)
    _pk_seed, _pk_root, witness = signer.sign(digest)
    tx["signatures"][0]["signature"] = witness
    assert frame_tx_sig_hash(tx, a.wire) == digest, "the witness must not change the signature hash"
    raw = frame_tx_raw(tx, a.wire)
    prefix = validation_prefix_len(tx)
    _emit({
        "wire": a.wire, "eipRevision": EIP_REVISION, "raw": _hex(raw), "rawBytes": len(raw),
        "sigHash": _hex(digest), "safeTxHash": _hex(h), "sender": _hex(sender), "safe": _hex(t["safe"]),
        "coSigners": [_hex(c["owner"]) for c in sorted(cosigs, key=lambda e: e["owner"])],
        "maxFee": str(tx["max_fee"]), "maxPriorityFeePerGas": str(prio),
        "frames": [{"mode": f["mode"], "flags": f["flags"], "target": _hex(f["target"]), "execution": f["execution"],
                    "state": f["state"], "value": str(f["value"]), "dataBytes": len(f["data"])} for f in tx["frames"]],
        "validationPrefixGas": sum(f["execution"] for f in tx["frames"][:prefix])
        + sum(SIGNATURE_GAS[s["scheme"]] for s in tx["signatures"]),
        "gas": gas, "publicMempoolProblems": problems,
    }, a.output)


def selftest():
    # 1. The ethrex wire format against ethrex frametx.py's golden vector (the one
    #    script/send_frame_tx_leansphincs.py checks).
    tx = {"chain_id": 1, "nonce": 7, "sender": (0xABCD).to_bytes(20, "big"),
          "frames": [{"mode": 1, "flags": 3, "target": None, "execution": 0x5208, "state": 0, "value": 0,
                      "data": bytes([0x11, 0x22])},
                     {"mode": 2, "flags": 0, "target": (0x1234).to_bytes(20, "big"), "execution": 0x9c40, "state": 0,
                      "value": 0, "data": b""}],
          "signatures": [{"scheme": SECP256K1, "signer": (0xABCD).to_bytes(20, "big"), "msg": b"",
                          "signature": bytes([0x01] * 65)}],
          "max_fee": 0x6fc23ac00, "max_priority_fee_per_gas": 0x3b9aca00}
    want = ("f8b201c1800794000000000000000000000000000000000000abcdeccc010380c48252088080821122de0280940000000000"
            "000000000000000000000000001234c4829c40808080f85cf85a0194000000000000000000000000000000000000abcd80b8"
            "4101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101"
            "01010101010101010101010101010101cc843b9aca008506fc23ac0080c0")
    assert frame_tx_raw(tx, "ethrex")[1:].hex() == want, "ethrex wire format: golden RLP"
    assert frame_tx_sig_hash(tx, "ethrex").hex() == \
        "73827d510b0029220c237a46b27f6b6b8e7a3fd3b52c42a55c6c6e343fc45951", "ethrex wire format: golden sig hash"

    # 2. The current EIP text: the hash commits to the length of an elided signature and to
    #    nothing else of it.
    arb = dict(tx, signatures=[{"scheme": ARBITRARY, "signer": b"", "msg": b"", "signature": b"\x01" * 100}])
    h = frame_tx_sig_hash(arb, "eip")
    assert frame_tx_sig_hash(dict(arb, signatures=[dict(arb["signatures"][0], signature=b"\x02" * 100)]), "eip") == h
    assert frame_tx_sig_hash(dict(arb, signatures=[dict(arb["signatures"][0], signature=b"\x01" * 101)]), "eip") != h
    assert frame_tx_sig_hash(dict(arb, signatures=[dict(arb["signatures"][0], signature=b"\x01" * 101)]),
                             "ethrex") == frame_tx_sig_hash(arb, "ethrex")

    # 3. Safe signatures: sorting, offsets, sizes.
    o1, o2, o3 = (bytes([i]) * 20 for i in (1, 2, 3))
    sig = bytes(range(256)) * 18 + bytes(52)
    assert len(sig) == SIG_LEN
    blob = encode_signatures([{"owner": o3, "sig": sig}, {"owner": o1, "s": b"\x11" * 32}, {"owner": o2, "sig": sig}])
    assert len(blob) == 3 * 65 + 2 * (32 + SIG_LEN)
    assert blob[12:32] == o1 and blob[64] == 1 and blob[32:64] == b"\x11" * 32
    assert blob[65 + 12:65 + 32] == o2 and blob[129] == 0 and int.from_bytes(blob[97:129], "big") == 195
    assert int.from_bytes(blob[162:194], "big") == 195 + 32 + SIG_LEN and blob[194] == 0
    assert int.from_bytes(blob[195:227], "big") == SIG_LEN and blob[227:227 + SIG_LEN] == sig
    assert len(service_signature(o2, sig)) == 4757
    try:
        encode_signatures([{"owner": o1, "s": b"\x00" * 32}, {"owner": o1, "sig": sig}])
        raise AssertionError("duplicate owner accepted")
    except ValueError:
        pass

    # 4. Public-mempool shape and the 100,000 limit.
    st = {"chainId": 1, "safe": o3, "nonce": 0, "to": o1, "value": 1, "data": b"", "operation": 0, "safeTxGas": 0,
          "baseGas": 0, "gasPrice": 0, "gasToken": ZERO_ADDRESS, "refundReceiver": ZERO_ADDRESS}
    ft = build_frame_tx(chain_id=1, sender=o1, account_nonce=0, safe_tx=st, signatures_blob=blob, max_fee=1,
                        max_priority_fee_per_gas=0, exec_gas=300_000)
    assert validation_prefix_len(ft) == 1 and public_mempool_problems(ft) == []
    over = dict(ft, frames=[dict(ft["frames"][0], execution=99_901), ft["frames"][1]])
    assert len(public_mempool_problems(over)) == 1
    assert public_mempool_problems(dict(ft, frames=[dict(ft["frames"][0], execution=99_900), ft["frames"][1]])) == []
    assert len(public_mempool_problems(dict(ft, frames=ft["frames"] + [dict(ft["frames"][0], flags=0)]))) == 1
    g = frame_tx_gas(ft)
    assert g["calldataFloor"] == 12_000 + 2 * 475 + 100 + 64 * g["floorBytes"]
    assert g["floorBytes"] == 36 + len(ft["frames"][1]["data"]) + SIG_LEN
    print("selftest ok")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    def signer_args(p):
        p.add_argument("--key-file", help="lsfk key file (lsfk keygen)")
        p.add_argument("--test-seed", help="32-byte seed on the command line: test vectors only")
        p.add_argument("--b", type=int, default=8, help="kept-subtree height for --test-seed (default 8)")
        p.add_argument("--lsfk", default=DEFAULT_LSFK)
        p.add_argument("--allow-stale-binary", action="store_true")

    p = sub.add_parser("hash")
    p.add_argument("safe_tx")
    p.set_defaults(fn=cmd_hash)

    p = sub.add_parser("cosign")
    p.add_argument("safe_tx")
    p.add_argument("--owner", required=True, help="the co-signer's owner account")
    p.add_argument("-o", "--output")
    signer_args(p)
    p.set_defaults(fn=cmd_cosign)

    p = sub.add_parser("signatures")
    p.add_argument("safe_tx")
    p.add_argument("--sender", required=True, help="the owner account that will send the frame transaction")
    p.add_argument("cosigs", nargs="*")
    p.set_defaults(fn=cmd_signatures)

    p = sub.add_parser("frame-tx")
    p.add_argument("safe_tx")
    p.add_argument("--sender", required=True)
    p.add_argument("--account-nonce", required=True, help="nonce of the sender's owner account")
    fee = p.add_mutually_exclusive_group(required=True)
    fee.add_argument("--max-fee", help="eip: total budget in wei; ethrex: price per gas")
    fee.add_argument("--base-fee", help="derive max_fee from this base fee per gas (2x base fee + tip)")
    p.add_argument("--max-priority-fee-per-gas", default="1000000000")
    p.add_argument("--wire", choices=WIRES, default="eip")
    p.add_argument("--verify-gas", default=str(DEFAULT_VERIFY_GAS), help="VERIFY frame limits.execution")
    p.add_argument("--exec-gas", help="SENDER frame limits.execution (default 150,000 + 100,000 per co-signer)")
    p.add_argument("--state-gas", default="0",
                   help=f"SENDER frame limits.state: {STATE_BYTES_PER_STORAGE_SET * CPSB} per new storage slot "
                        f"(a Safe's first transaction sets its nonce slot), {STATE_BYTES_PER_NEW_ACCOUNT * CPSB} "
                        "per new account")
    p.add_argument("--allow-non-mempool", action="store_true",
                   help="assemble even if the public-mempool structural rules fail")
    p.add_argument("-o", "--output")
    p.add_argument("cosigs", nargs="*")
    signer_args(p)
    p.set_defaults(fn=cmd_frame_tx)

    p = sub.add_parser("selftest")
    p.set_defaults(fn=lambda a: selftest())

    a = ap.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
