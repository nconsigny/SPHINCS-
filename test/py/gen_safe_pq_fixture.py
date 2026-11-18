#!/usr/bin/env python3
"""Regenerate test/fixtures/safe_pq_owners_frame.json for test/SafePqOwnersFrameTest.t.sol.

Five leanSphincs-f keys (test seeds, pruned keys with b = 8), each in a SphincsOwnerAccount at
a fixed address, a 2-of-3 and a 3-of-5 Safe over them at fixed addresses, and frame
transactions under the EIP-8141 text of ethereum/EIPs master dc5d5fa688b7 (2026-11-01).

Everything a wallet would do is done by the tooling in script/safe_pq_owners.py: the Safe
transaction hash, the co-signatures, the Safe `signatures` bytes, the execTransaction calldata,
the frame transaction and its signature hash, the sender's witness. This script only lays the
result out as an emulator fixture and builds the negative scenarios. For every scenario it
then checks that the emulator (test/py/frame8141_emu.py), which has its own RLP and its own
copy of the EIP's formulas, computes the same signature hash, the same gas figures and the
same public-mempool verdict as the tooling.

Scenarios (all send from owner accounts; the Safe transaction is a 1000 wei transfer at Safe
nonce 1, to an account that exists, so that no state gas is involved):
  safe_2of3          [self_verify, SENDER -> Safe 2-of-3 execTransaction], sender + 1 co-signer
  safe_3of5          [self_verify, SENDER -> Safe 3-of-5 execTransaction], sender + 2 co-signers
  sweep              [self_verify, SENDER value transfer]: ETH leaves an owner account
  cosig_as_witness   safe_2of3 with the witness replaced by the sender key's signature over the
                     Safe transaction hash (a valid Safe co-signature of that key)
  wrong_key          safe_2of3 with the witness made by another owner's key
  tampered_frame     safe_2of3's witness on a transaction whose SENDER frame pays someone else
  explicit_msg       the signature entry carries an explicit 32-byte msg and a valid signature
                     over it; verifyFrameAndApprove(uint256 0)
  explicit_msg_scan  the same with verifyFrameAndApprove()
  verify_gas_300k    safe_2of3's shape with a 300,000-gas VERIFY frame (not signed)
  verify_after_prefix  safe_2of3's shape with a VERIFY frame after the prefix (not signed)

Signing is deterministic, so rerunning reproduces the committed file byte for byte; --check
fails if it would change. Needs the Rust signer: (cd signers/leansphincs-f-keccak && cargo build --release).

usage: python3 -I test/py/gen_safe_pq_fixture.py [--check]
"""
import copy
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "script"))
import frame8141_emu as fe  # noqa: E402
import safe_pq_owners as sp  # noqa: E402

FIXTURE = os.path.join(ROOT, "test", "fixtures", "safe_pq_owners_frame.json")
CHAIN_ID = 8141
B = 8
VERIFIER = "0x00000000000000000000000000000000001ea9f0"
RECIPIENT = "0x000000000000000000000000000000000000dead"
OTHER_RECIPIENT = "0x000000000000000000000000000000000000beef"
SAFES = {
    "2of3": {"address": "0x5afe000000000000000000000000000000002023", "threshold": 2, "owners": [0, 1, 2]},
    "3of5": {"address": "0x5afe000000000000000000000000000000003035", "threshold": 3, "owners": [0, 1, 2, 3, 4]},
}
BASE_FEE = 10**9
PRIORITY_FEE = 10**9
# The Safe has executed a transaction before (its nonce slot exists) and the recipient exists, so
# the SENDER frame needs no state gas. A Safe's first transaction would need 64 * 1530 = 97,920
# for the nonce slot, a payment to a new account 120 * 1530 = 183,600 (EIP-8037).
SAFE_NONCE = 1
SENDER_FRAME_STATE_GAS = 0


def hx(b):
    return "0x" + b.hex()


def make_owners():
    owners = []
    for i in range(5):
        seed = sp.keccak256(f"safe-pq fixture owner {i}".encode())
        pk_seed, pk_root, _ = sp.Signer(test_seed=hx(seed), b=B).sign(bytes(32))
        # Fixed addresses, ascending, so the fixture's owner order is the Safe's signature order.
        address = bytes([0xA1 + i]) + bytes(18) + bytes([i + 1])
        owners.append({"address": hx(address), "seed": hx(seed), "b": B, "pkSeed": hx(pk_seed), "pkRoot": hx(pk_root)})
    return owners


def signer_of(owner):
    return sp.Signer(test_seed=owner["seed"], b=owner["b"])


def safe_tx_json(safe, to=RECIPIENT, value=1000):
    return {"chainId": CHAIN_ID, "safe": safe, "nonce": SAFE_NONCE, "to": to, "value": str(value), "data": "0x",
            "operation": 0, "safeTxGas": 0, "baseGas": 0, "gasPrice": 0,
            "gasToken": hx(sp.ZERO_ADDRESS), "refundReceiver": hx(sp.ZERO_ADDRESS)}


def to_scenario(tx, extra=None):
    """A tooling frame transaction as an emulator scenario."""
    sc = {
        "nonce": tx["nonce"], "sender": hx(tx["sender"]),
        "max_fee": str(tx["max_fee"]), "max_priority_fee_per_gas": str(tx["max_priority_fee_per_gas"]),
        "frames": [{"mode": f["mode"], "flags": f["flags"], "target": hx(f["target"]) if f["target"] else "",
                    "execution": f["execution"], "state": f["state"], "value": str(f["value"]), "data": hx(f["data"])}
                   for f in tx["frames"]],
        "signatures": [{"scheme": s["scheme"], "signer": hx(s["signer"]) if s["signer"] else "",
                        "msg": hx(s["msg"]) if s["msg"] else "", "sig": hx(s["signature"])} for s in tx["signatures"]],
        "sigHash": hx(sp.frame_tx_sig_hash(tx, "eip")),
    }
    sc.update(extra or {})
    return sc


def safe_frame_tx(owners, safe_key, sender_i, cosigner_is, to=RECIPIENT):
    """The unsigned frame transaction (zero witness) and what went into it."""
    safe = SAFES[safe_key]
    stj = safe_tx_json(safe["address"], to=to)
    st = sp.load_safe_tx(stj)
    h = sp.safe_tx_hash(st)
    cosigs = []
    for i in cosigner_is:
        _, _, sig = signer_of(owners[i]).sign(h)
        cosigs.append({"owner": sp.addr(owners[i]["address"]), "sig": sig})
    sender = sp.addr(owners[sender_i]["address"])
    # The sender's entry: v = 1 with s = the Safe transaction hash.
    blob = sp.encode_signatures(cosigs + [{"owner": sender, "s": h}])
    tx = sp.build_frame_tx(chain_id=CHAIN_ID, sender=sender, account_nonce=0, safe_tx=st, signatures_blob=blob,
                           max_fee=0, max_priority_fee_per_gas=PRIORITY_FEE,
                           exec_gas=sp.default_exec_gas(len(cosigs)), state_gas=SENDER_FRAME_STATE_GAS)
    tx["max_fee"] = sp.frame_tx_gas(tx)["maxGas"] * (2 * BASE_FEE + PRIORITY_FEE)
    info = {"safe": safe_key, "senderOwner": sender_i, "coSigners": list(cosigner_is), "safeTx": stj,
            "safeTxHash": hx(h), "safeSignatures": hx(blob), "coSignatures": [hx(c["sig"]) for c in cosigs],
            "serviceSignatureBytes": len(sp.service_signature(cosigs[0]["owner"], cosigs[0]["sig"]))}
    return tx, info


def sign_frame_tx(tx, owner):
    digest = sp.frame_tx_sig_hash(tx, "eip")
    _, _, witness = signer_of(owner).sign(digest)
    tx["signatures"][0]["signature"] = witness
    assert sp.frame_tx_sig_hash(tx, "eip") == digest
    return tx


def build():
    owners = make_owners()
    assert [o["address"] for o in owners] == sorted(o["address"] for o in owners)
    fx = {
        "about": "Generated by test/py/gen_safe_pq_fixture.py with the tooling in script/safe_pq_owners.py. "
                 "Test keys: the seeds are public.",
        "spec": fe.REV_2026_11_01, "chain_id": CHAIN_ID, "verifier": VERIFIER, "recipient": RECIPIENT,
        "owners": owners, "safes": SAFES, "scenarios": {},
    }
    sc = fx["scenarios"]

    # The two transactions the prototype is about.
    tx23, info23 = safe_frame_tx(owners, "2of3", 1, [0])
    assert sp.public_mempool_problems(tx23) == []
    unsigned23 = copy.deepcopy(tx23)
    sign_frame_tx(tx23, owners[1])
    sc["safe_2of3"] = to_scenario(tx23, info23)

    tx35, info35 = safe_frame_tx(owners, "3of5", 2, [0, 4])
    assert sp.public_mempool_problems(tx35) == []
    sign_frame_tx(tx35, owners[2])
    sc["safe_3of5"] = to_scenario(tx35, info35)

    # ETH leaves an owner account: a SENDER frame with a value and no data, no Safe involved.
    sweep = {"chain_id": CHAIN_ID, "nonce": 0, "sender": sp.addr(owners[3]["address"]),
             "frames": [{"mode": sp.VERIFY, "flags": 3, "target": sp.addr(owners[3]["address"]),
                         "execution": sp.DEFAULT_VERIFY_GAS, "state": 0, "value": 0,
                         "data": sp.VERIFY_FRAME_SELECTOR + sp.w32(0)},
                        {"mode": sp.SENDER, "flags": 0, "target": sp.addr(RECIPIENT), "execution": 30_000,
                         "state": 0, "value": 10**15, "data": b""}],
             "signatures": [{"scheme": sp.ARBITRARY, "signer": b"", "msg": b"", "signature": bytes(sp.SIG_LEN)}],
             "max_fee": 0, "max_priority_fee_per_gas": PRIORITY_FEE}
    sweep["max_fee"] = sp.frame_tx_gas(sweep)["maxGas"] * (2 * BASE_FEE + PRIORITY_FEE)
    assert sp.public_mempool_problems(sweep) == []
    sign_frame_tx(sweep, owners[3])
    sc["sweep"] = to_scenario(sweep)

    # Invariant 5: the sender key's signature over the Safe transaction hash is a valid Safe
    # co-signature of that key. As the frame witness it must fail.
    t = copy.deepcopy(unsigned23)
    _, _, cosig = signer_of(owners[1]).sign(sp.hexb(info23["safeTxHash"]))
    t["signatures"][0]["signature"] = cosig
    sc["cosig_as_witness"] = to_scenario(t, {"witnessSignedOver": info23["safeTxHash"], "witnessKey": 1})

    # The VERIFY frame checks the sender's key only: another owner's signature over the right hash fails.
    t = copy.deepcopy(unsigned23)
    sign_frame_tx(t, owners[0])
    sc["wrong_key"] = to_scenario(t, {"witnessKey": 0})

    # compute_sig_hash covers every frame: the witness of safe_2of3 does not carry over to a
    # transaction whose SENDER frame calls the Safe with other arguments.
    t, _ = safe_frame_tx(owners, "2of3", 1, [0], to=OTHER_RECIPIENT)
    t["signatures"][0]["signature"] = tx23["signatures"][0]["signature"]
    assert sp.frame_tx_sig_hash(t, "eip") != sp.frame_tx_sig_hash(tx23, "eip")
    sc["tampered_frame"] = to_scenario(t, {"witnessSignedOver": sc["safe_2of3"]["sigHash"], "witnessKey": 1})

    # Invariant 1: an entry with an explicit msg is refused even though its signature is this
    # key's valid signature over that msg.
    digest = sp.keccak256(b"safe-pq explicit digest")
    _, _, over_digest = signer_of(owners[1]).sign(digest)
    for name, data in (("explicit_msg", sp.VERIFY_FRAME_SELECTOR + sp.w32(0)),
                       ("explicit_msg_scan", sp.selector("verifyFrameAndApprove()"))):
        t = copy.deepcopy(unsigned23)
        t["frames"][0]["data"] = data
        t["signatures"] = [{"scheme": sp.ARBITRARY, "signer": b"", "msg": digest, "signature": over_digest}]
        sc[name] = to_scenario(t, {"witnessSignedOver": hx(digest), "witnessKey": 1})

    # Public-mempool structure. Not signed: the structural rules are checked before any simulation.
    t = copy.deepcopy(unsigned23)
    t["frames"][0]["execution"] = 300_000  # what script/send_frame_tx_leansphincs.py declares
    assert sp.public_mempool_problems(t)
    sc["verify_gas_300k"] = to_scenario(t)

    t = copy.deepcopy(unsigned23)
    t["frames"].append({"mode": sp.VERIFY, "flags": 0, "target": sp.addr(owners[0]["address"]), "execution": 30_000,
                        "state": 0, "value": 0, "data": b""})
    assert sp.public_mempool_problems(t)
    sc["verify_after_prefix"] = to_scenario(t)

    crosscheck(fx, {"safe_2of3": tx23, "safe_3of5": tx35, "sweep": sweep})
    return fx


def crosscheck(fx, tooling_txs):
    """The emulator against the tooling, on every scenario."""
    for name, sc in fx["scenarios"].items():
        tx = fe.load_tx(fx, name)
        fe.static_checks(tx)
        assert hx(fe.compute_sig_hash(tx)) == sc["sigHash"], f"{name}: emulator and tooling disagree on the sig hash"
    for name, t in tooling_txs.items():
        tx = fe.load_tx(fx, name)
        g, eg = sp.frame_tx_gas(t), fe.gas_accounting(tx)
        assert (g["intrinsic"], g["calldataFloor"], g["floorBytes"], g["executionLimits"], g["stateLimits"], g["maxGas"]) \
            == (eg["intrinsic"], eg["floor"], eg["floor_bytes"], eg["exec_limits"], eg["state_limits"], eg["max_gas"]), name
        n, gas, problems = fe.mempool_check(tx)
        assert problems == [] and n == sp.validation_prefix_len(t) == 1 and gas == sp.DEFAULT_VERIFY_GAS + 100, name
        raw = sp.frame_tx_raw(t, "eip")
        assert sp.keccak256(raw) != fe.compute_sig_hash(tx)
        print(f"{name}: sigHash {fx['scenarios'][name]['sigHash']}, raw {len(raw)} B, intrinsic {g['intrinsic']}, "
              f"calldata floor {g['calldataFloor']}", file=sys.stderr)
    for name in ("verify_gas_300k", "verify_after_prefix"):
        assert fe.mempool_check(fe.load_tx(fx, name))[2], name


def main():
    check = "--check" in sys.argv[1:]
    text = json.dumps(build(), indent=1) + "\n"
    if check:
        if not os.path.exists(FIXTURE) or open(FIXTURE).read() != text:
            sys.exit("test/fixtures/safe_pq_owners_frame.json is stale: rerun test/py/gen_safe_pq_fixture.py")
        print("fixture reproduces", file=sys.stderr)
        return
    with open(FIXTURE, "w") as f:
        f.write(text)
    print(f"wrote {os.path.relpath(FIXTURE, ROOT)} ({len(text)} bytes)", file=sys.stderr)


if __name__ == "__main__":
    main()
