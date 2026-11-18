#!/usr/bin/env python3
"""EIP-8141 frame-transaction model + strict mini-EVM for the SphincsFrameVerify module.

forge/revm has no EIP-8141 support, so test/SphincsFrameModuleEmuTest.t.sol runs the
module's REAL deployed runtime code here, through vm.ffi, as the DELEGATECALL target of
the frame's account: ADDRESS = the account, calldata = the payload the account built,
and TXPARAM / FRAMEPARAM / SIGPARAM / SIGDATACOPY / APPROVE answered from a concrete
frame transaction. The module's STATICCALL to the verifier is answered with a
caller-supplied word, so the Forge test can call the REAL verifier in between (phase 1
captures the verifier calldata, phase 2 replays with the verifier's real answer).

Spec: ethereum/EIPs EIPS/eip-8141.md at master af3a7802c8ea (2026-10-09):
  * payload [chain_id, nonce, sender, frames, signatures, fees, blob_versioned_hashes],
    frames [[mode, flags, target, [execution, state], value, data]],
    signatures [[scheme, signer, msg, signature]], fees [prio, max, max_blob];
  * compute_sig_hash elides the raw signature bytes of every empty-msg entry;
  * SIGPARAM (0xb4): signatureIndex on top, param second; params 0x00..0x03 only,
    anything else is an exceptional halt; len(signature) only for ARBITRARY;
  * SIGDATACOPY (0xb5): top-down memOffset, dataOffset, length, signatureIndex;
    halts on an out-of-range index or a non-ARBITRARY entry; zero-fills past the end;
  * TXPARAM (0xb0) 0x08 sig hash, 0x0A current frame index, 0x0B signature count;
  * FRAMEPARAM (0xb3) 0x06 allowed scope (frameIndex on top, param second);
  * APPROVE (0xaa): top-down offset, length, scope; reverts unless scope != 0 and
    scope is within frame.flags & 3 (and EXECUTION needs resolved_target == sender).
Every opcode that is not modelled halts, so the emulator never silently misreads the
bytecode. Only the standard library is used.

Spec revisions. A fixture names the EIP text it was built under in its "spec" field:
  * af3a7802c8ea (2026-10-09, the default): fees [prio, max, max_blob]; compute_sig_hash
    drops the bytes of every empty-msg signature. test/fixtures/frame8141_two_accounts.json.
  * dc5d5fa688b7 (2026-11-01): fees [max_fee, max_priority_fee_per_gas], max_fee being a
    total budget in wei; compute_sig_hash replaces the bytes of every empty-msg signature
    by their length (#12502); a frame's target access is charged at frame entry from the
    frame's own gas; SENDER frames may carry value. test/fixtures/safe_pq_owners_frame.json.
The instructions the module uses are the same in both.

Whole-frame execution (`exec`, `call`), added for test/SafePqOwnersFrameTest.t.sol. `run`
above executes only the module and takes the verifier's answer from the caller. `Evm` below
executes a whole VERIFY frame instead: the account's code, its DELEGATECALL into the module
and the module's STATICCALL into the verifier, all from real deployed code, with gas metered
(today's schedule for the ordinary instructions, EIP-8141's for its own). It covers
computation, memory, KECCAK256, STATICCALL, DELEGATECALL and the EIP-8141 instructions. It
has no storage, value transfer, log or contract creation: those instructions halt, which is
also what makes it a check of the public-mempool trace rules for a validation prefix (no
storage read, no banned opcode, GAS only immediately before a *CALL). It is checked against
revm: the Forge tests run the same calls natively and compare the gas to the unit.
`mempool` and `gas` evaluate the public-mempool structural rules and the Gas Accounting
formulas of the dc5d5fa688b7 text.

CLI (all output is 0x-hex ABI for vm.ffi):
  frame8141_emu.py accounts <fixture.json>
      -> (address A, bytes32 seedA, bytes32 rootA, address B, bytes32 seedB, bytes32 rootB,
          address verifier)
  frame8141_emu.py frame <fixture.json> <scenario> <frameIndex>
      -> (address resolvedTarget, uint256 flags, bytes data, bytes32 sigHash)
  frame8141_emu.py witness <fixture.json> <scenario> <sigIndex>
      -> (bytes signature)
  frame8141_emu.py run <fixture.json> <scenario> <frameIndex> <codeHex> <calldataHex> <verdict>
      verdict: 64-hex word the STATICCALL returns, or "revert"
      -> (uint8 outcome, uint256 scope, uint256 sigIndexCopied, address callTo,
          bytes verifierCalldata, string detail)
      outcome: 0 exceptional halt, 1 REVERT, 2 APPROVE, 3 STOP/RETURN without APPROVE,
               4 APPROVE rejected
  frame8141_emu.py framex <fixture.json> <scenario> <frameIndex>
      -> (uint256 mode, uint256 flags, address resolvedTarget, uint256 value,
          uint256 executionLimit, uint256 stateLimit, bytes data, bytes32 sigHash, address sender)
  frame8141_emu.py mempool <fixture.json> <scenario>
      -> (bool ok, uint256 prefixLength, uint256 prefixGas, string problems)
  frame8141_emu.py gas <fixture.json> <scenario>
      -> (uint256 intrinsic, uint256 calldataFloor, uint256 floorBytes, uint256 executionLimits,
          uint256 stateLimits, uint256 maxGas)
  frame8141_emu.py exec <fixture.json> <scenario> <frameIndex> <gasLimit | -> <addr>=<codeHex>...
      runs the whole frame in the metered EVM; `-` takes the frame's own limits.execution
      -> (uint8 outcome, uint256 scope, uint256 gasUsed, address lastStaticcallTo,
          bytes lastStaticcallData, uint256 lastStaticcallGas, bytes lastStaticcallReturn,
          string traceViolations, string detail)
      outcome as for `run` (a rejected APPROVE shows as 1, REVERT)
  frame8141_emu.py call <gas> <caller> <to> <calldataHex> <warm addr,addr,.. | -> <addr>=<codeHex>...
      a plain metered call outside any frame transaction, for comparison with revm
      -> (bool success, uint256 gasUsed, bytes returnData, string detail)
"""
import json
import sys

M = (1 << 256) - 1
NONE = M
OUT_HALT, OUT_REVERT, OUT_APPROVE, OUT_STOP, OUT_APPROVE_REJECTED = 0, 1, 2, 3, 4
FRAME_TX_TYPE = 0x06
DEFAULT, VERIFY, SENDER = 0, 1, 2
ARBITRARY, SECP256K1 = 0, 1

# ───────────────────────────── keccak256 (pure python) ─────────────────────────────
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


def selector(sig: str) -> bytes:
    return keccak256(sig.encode())[:4]


# ───────────────────────────── RLP + frame transaction ─────────────────────────────
def _rlp_len(n, off):
    if n < 56:
        return bytes([off + n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([off + 55 + len(b)]) + b


def rlp(x):
    if isinstance(x, int):
        x = x.to_bytes((x.bit_length() + 7) // 8, "big") if x else b""
    if isinstance(x, (bytes, bytearray)):
        x = bytes(x)
        if len(x) == 1 and x[0] < 0x80:
            return x
        return _rlp_len(len(x), 0x80) + x
    body = b"".join(rlp(i) for i in x)
    return _rlp_len(len(body), 0xC0) + body


def h(s):
    s = s[2:] if s.startswith("0x") else s
    return bytes.fromhex(s)


REV_2026_10_09 = "af3a7802c8ea"
REV_2026_11_01 = "dc5d5fa688b7"
REVISIONS = (REV_2026_10_09, REV_2026_11_01)


def load_tx(fx, name):
    sc = fx["scenarios"][name]
    spec = fx.get("spec", REV_2026_10_09)
    assert spec in REVISIONS, f"unknown spec revision {spec}"
    frames = [{"mode": f["mode"], "flags": f["flags"], "target": h(f["target"]) if f["target"] else b"",
               "limits": [f.get("execution", 2_000_000), f.get("state", 0)], "value": int(f.get("value", 0)),
               "data": h(f["data"])}
              for f in sc["frames"]]
    sigs = [{"scheme": s["scheme"], "signer": h(s["signer"]) if s["signer"] else b"",
             "msg": h(s["msg"]) if s["msg"] else b"", "sig": h(s["sig"])} for s in sc["signatures"]]
    if spec == REV_2026_10_09:
        fees = [10**9, 30 * 10**9, 0]
    else:
        fees = [int(sc["max_fee"]), int(sc["max_priority_fee_per_gas"])]
    return {"chain_id": fx["chain_id"], "nonce": sc["nonce"], "sender": h(sc["sender"]), "frames": frames,
            "signatures": sigs, "fees": fees, "blob_versioned_hashes": [], "spec": spec}


def compute_sig_hash(tx):
    # dc5d5fa688b7: an elided signature is replaced by its byte length, as an RLP integer.
    commit_length = tx.get("spec", REV_2026_10_09) != REV_2026_10_09

    def elided(s):
        return len(s["sig"]) if commit_length else b""

    sigs = [[s["scheme"], s["signer"], s["msg"], elided(s) if len(s["msg"]) == 0 else s["sig"]]
            for s in tx["signatures"]]
    frames = [[f["mode"], f["flags"], f["target"], f["limits"], f["value"], f["data"]] for f in tx["frames"]]
    payload = [tx["chain_id"], tx["nonce"], tx["sender"], frames, sigs, tx["fees"], tx["blob_versioned_hashes"]]
    return keccak256(bytes([FRAME_TX_TYPE]) + rlp(payload))


def static_checks(tx):
    for s in tx["signatures"]:
        if s["scheme"] == ARBITRARY:
            assert len(s["signer"]) == 0
        else:
            assert s["scheme"] == SECP256K1 and len(s["signer"]) in (0, 20)
        assert len(s["msg"]) in (0, 32) and s["msg"] != b"\x00" * 32
    assert 0 < len(tx["frames"]) <= 64
    for i, f in enumerate(tx["frames"]):
        assert f["mode"] in (DEFAULT, VERIFY, SENDER) and f["flags"] < 8
        assert f["mode"] == SENDER or f["value"] == 0
        if f["flags"] & 0x2:
            assert f["target"] in (b"", tx["sender"])
        if f["flags"] & 0x4:
            assert f["mode"] != VERIFY and i + 1 < len(tx["frames"]) and tx["frames"][i + 1]["mode"] != VERIFY


def resolved_target(tx, fi):
    return tx["frames"][fi]["target"] or tx["sender"]


# ───────────────────────────── strict mini-EVM ─────────────────────────────
class Halt(Exception):
    pass


def run_module(code, *, tx, sig_hash, frame_index, address, calldata, verdict):
    sigs, frames = tx["signatures"], tx["frames"]
    pc, stack, mem = 0, [], bytearray()
    res = {"outcome": None, "scope": 0, "calls": [], "detail": "", "copied": NONE}

    def mext(off, size):
        if size == 0:
            return
        if off + size > (1 << 24):
            raise Halt("memory expansion out of gas")
        if len(mem) < off + size:
            mem.extend(b"\x00" * (((off + size + 31) // 32) * 32 - len(mem)))

    def pop():
        if not stack:
            raise Halt("stack underflow")
        return stack.pop()

    def push(v):
        if len(stack) >= 1024:
            raise Halt("stack overflow")
        stack.append(v & M)

    def cd_slice(off, n):
        out = calldata[off:off + n] if off < len(calldata) else b""
        return out + b"\x00" * (n - len(out))

    def sig_entry(i):
        if i >= len(sigs):
            raise Halt("signatureIndex out of bounds")
        return sigs[i]

    def sigparam(p, i):
        s = sig_entry(i)
        if p == 0x00:
            if s["scheme"] == ARBITRARY:
                raise Halt("SIGPARAM resolved_signer of an ARBITRARY entry")
            return int.from_bytes(s["signer"] or tx["sender"], "big")
        if p == 0x01:
            return s["scheme"]
        if p == 0x02:
            return int.from_bytes(s["msg"], "big") if s["msg"] else 0
        if p == 0x03:
            if s["scheme"] != ARBITRARY:
                raise Halt("SIGPARAM len(signature) of a non-ARBITRARY entry")
            return len(s["sig"])
        raise Halt(f"undefined SIGPARAM param {p:#04x}")

    jumpdests, k = set(), 0
    while k < len(code):
        if code[k] == 0x5B:
            jumpdests.add(k)
        k += 1 + (code[k] - 0x5F if 0x60 <= code[k] <= 0x7F else 0)

    binops = {
        0x01: lambda a, b: a + b, 0x02: lambda a, b: a * b, 0x03: lambda a, b: a - b,
        0x04: lambda a, b: a // b if b else 0, 0x06: lambda a, b: a % b if b else 0,
        0x10: lambda a, b: int(a < b), 0x11: lambda a, b: int(a > b), 0x14: lambda a, b: int(a == b),
        0x16: lambda a, b: a & b, 0x17: lambda a, b: a | b, 0x18: lambda a, b: a ^ b,
        0x1B: lambda sh, v: v << sh if sh < 256 else 0, 0x1C: lambda sh, v: v >> sh if sh < 256 else 0,
    }
    steps = 0
    try:
        while True:
            steps += 1
            if steps > 1_000_000:
                raise Halt("step limit")
            if pc >= len(code):
                res["outcome"], res["detail"] = OUT_STOP, "ran off the end of the code"
                break
            op = code[pc]
            if op == 0x00:
                res["outcome"], res["detail"] = OUT_STOP, "STOP without APPROVE"
                break
            elif op in binops:
                a, b = pop(), pop()
                push(binops[op](a, b))
            elif op == 0x15:
                push(int(pop() == 0))
            elif op == 0x19:
                push(~pop())
            elif op == 0x30:  # ADDRESS: the account (module runs under its DELEGATECALL)
                push(int.from_bytes(address, "big"))
            elif op == 0x35:
                push(int.from_bytes(cd_slice(pop(), 32), "big"))
            elif op == 0x36:
                push(len(calldata))
            elif op == 0x37:
                mo, do, ln = pop(), pop(), pop()
                mext(mo, ln)
                mem[mo:mo + ln] = cd_slice(do, ln)
            elif op == 0x50:
                pop()
            elif op == 0x51:
                off = pop()
                mext(off, 32)
                push(int.from_bytes(mem[off:off + 32], "big"))
            elif op == 0x52:
                off, v = pop(), pop()
                mext(off, 32)
                mem[off:off + 32] = v.to_bytes(32, "big")
            elif op == 0x56:
                d = pop()
                if d not in jumpdests:
                    raise Halt("bad jump destination")
                pc = d
                continue
            elif op == 0x57:
                d, c = pop(), pop()
                if c:
                    if d not in jumpdests:
                        raise Halt("bad jumpi destination")
                    pc = d
                    continue
            elif op == 0x5A:
                push(30_000_000)
            elif op == 0x5B:
                pass
            elif op == 0x5F:
                push(0)
            elif 0x60 <= op <= 0x7F:
                n = op - 0x5F
                push(int.from_bytes(code[pc + 1:pc + 1 + n].ljust(n, b"\x00"), "big"))
                pc += n
            elif 0x80 <= op <= 0x8F:
                n = op - 0x7F
                if len(stack) < n:
                    raise Halt("DUP underflow")
                push(stack[-n])
            elif 0x90 <= op <= 0x9F:
                n = op - 0x8F
                if len(stack) < n + 1:
                    raise Halt("SWAP underflow")
                stack[-1], stack[-1 - n] = stack[-1 - n], stack[-1]
            elif op == 0xF3:
                pop(), pop()
                res["outcome"], res["detail"] = OUT_STOP, "RETURN without APPROVE"
                break
            elif op == 0xFA:  # STATICCALL, answered with the caller-supplied verdict
                _g, addr, ao, al, ro, rl = [pop() for _ in range(6)]
                mext(ao, al)
                res["calls"].append({"to": addr & ((1 << 160) - 1), "calldata": bytes(mem[ao:ao + al])})
                if verdict is None:
                    push(0)
                else:
                    mext(ro, rl)
                    mem[ro:ro + min(rl, 32)] = verdict[:min(rl, 32)]
                    push(1)
            elif op == 0xFD:
                off, ln = pop(), pop()
                mext(off, ln)
                data = bytes(mem[off:off + ln])
                reason = ""
                if data[:4] == bytes.fromhex("08c379a0") and len(data) >= 0x44:
                    sl = int.from_bytes(data[0x24:0x44], "big")
                    reason = data[0x44:0x44 + sl].decode(errors="replace")
                res["outcome"], res["detail"] = OUT_REVERT, f"REVERT {reason}"
                break
            elif op == 0xFE:
                raise Halt("INVALID")
            elif op == 0xB0:  # TXPARAM
                p = pop()
                if p == 0x08:
                    push(int.from_bytes(sig_hash, "big"))
                elif p == 0x0A:
                    push(frame_index)
                elif p == 0x0B:
                    push(len(sigs))
                else:
                    raise Halt(f"TXPARAM {p:#x} not modelled")
            elif op == 0xB3:  # FRAMEPARAM
                idx, p = pop(), pop()
                if idx >= len(frames):
                    raise Halt("FRAMEPARAM frameIndex out of bounds")
                if p != 0x06:
                    raise Halt(f"FRAMEPARAM {p:#x} not modelled")
                push(frames[idx]["flags"] & 3)
            elif op == 0xB4:  # SIGPARAM
                i, p = pop(), pop()
                push(sigparam(p, i))
            elif op == 0xB5:  # SIGDATACOPY
                mo, do, ln, i = pop(), pop(), pop(), pop()
                s = sig_entry(i)
                if s["scheme"] != ARBITRARY:
                    raise Halt("SIGDATACOPY of a non-ARBITRARY entry")
                res["copied"] = i
                mext(mo, ln)
                src = s["sig"][do:do + ln] if do < len(s["sig"]) else b""
                mem[mo:mo + ln] = src + b"\x00" * (ln - len(src))
            elif op == 0xAA:  # APPROVE(offset, length, scope)
                off, ln, scope = pop(), pop(), pop()
                mext(off, ln)
                allowed = frames[frame_index]["flags"] & 3
                bad = scope == 0 or (scope & ~allowed) & M
                if not bad and scope & 2 and resolved_target(tx, frame_index) != tx["sender"]:
                    bad = True
                if bad or address != resolved_target(tx, frame_index):
                    res["outcome"], res["scope"] = OUT_APPROVE_REJECTED, scope
                    res["detail"] = f"APPROVE({scope}) rejected"
                    break
                res["outcome"], res["scope"] = OUT_APPROVE, scope
                res["detail"] = f"APPROVE({scope})"
                break
            else:
                raise Halt(f"unmodelled opcode {op:#04x} at pc {pc}")
            pc += 1
    except Halt as e:
        res["outcome"], res["detail"] = OUT_HALT, f"exceptional halt at pc {pc}: {e}"
    return res


# ───────────────────── public-mempool rules + gas accounting (dc5d5fa688b7) ─────────────────────
MAX_VERIFY_GAS = 100_000
MAX_VERIFY_STATE_GAS = 500_000
SIGNATURE_GAS = {ARBITRARY: 100, SECP256K1: 2_800}
FRAME_TX_INTRINSIC_COST, FRAME_TX_PER_FRAME_COST, TX_VALUE_COST = 12_000, 475, 6_000
STANDARD_TOKEN_COST, TOTAL_COST_FLOOR_PER_TOKEN = 4, 16
ENTRY_POINT = 0xAA


def validation_prefix(tx):
    """Number of frames in the recognised validation prefix, from the frames' shape, or None.
    The four shapes: [self_verify], [deploy, self_verify], [only_verify, pay],
    [deploy, only_verify, pay]. (An expiry verifier frame is not modelled.)"""
    fr = tx["frames"]

    def verify(f, flags):
        return f["mode"] == VERIFY and f["flags"] == flags

    def own(f):
        return f["target"] in (b"", tx["sender"])

    i = 1 if fr[0]["mode"] == DEFAULT and fr[0]["flags"] == 0 else 0
    if i < len(fr) and verify(fr[i], 0x3) and own(fr[i]):
        return i + 1
    if i + 1 < len(fr) and verify(fr[i], 0x2) and own(fr[i]) and verify(fr[i + 1], 0x1):
        return i + 2
    return None


def mempool_check(tx):
    """Structural Rules 1, 5, 6 and 8. Returns (prefix length, prefix gas, problems)."""
    n = validation_prefix(tx)
    if n is None:
        return 0, 0, ["no recognised validation prefix"]
    prefix = tx["frames"][:n]
    gas = sum(f["limits"][0] for f in prefix) + sum(SIGNATURE_GAS[s["scheme"]] for s in tx["signatures"])
    problems = []
    if gas > MAX_VERIFY_GAS:
        problems.append(f"prefix gas {gas} exceeds MAX_VERIFY_GAS")
    if sum(f["limits"][1] for f in prefix) > MAX_VERIFY_STATE_GAS:
        problems.append("prefix state gas exceeds MAX_VERIFY_STATE_GAS")
    if any(f["flags"] & 0x4 for f in prefix):
        problems.append("atomic batch flag in the prefix")
    if any(f["mode"] == VERIFY for f in tx["frames"][n:]):
        problems.append("VERIFY frame after the prefix")
    return n, gas, problems


def tokens_in(data):
    zero = data.count(0)
    return zero + (len(data) - zero) * 4


def gas_accounting(tx):
    """EIP-8141 Gas Accounting, from the transaction fields alone."""
    frames, sigs = tx["frames"], tx["signatures"]
    sig_verification = sum(SIGNATURE_GAS[s["scheme"]] for s in sigs)
    frame_data = sum(STANDARD_TOKEN_COST * tokens_in(f["data"]) for f in frames)
    sig_data = 0
    for s in sigs:
        # Elided bytes are priced as if all non-zero: their cost depends on the length alone.
        sig_tokens = 4 * len(s["sig"]) if len(s["msg"]) == 0 else tokens_in(s["sig"])
        sig_data += STANDARD_TOKEN_COST * (tokens_in(s["signer"]) + tokens_in(s["msg"]) + sig_tokens)
    value_transfer = sum(TX_VALUE_COST for f in frames if f["value"] > 0 and f["target"] not in (b"", tx["sender"]))
    base = FRAME_TX_INTRINSIC_COST + len(frames) * FRAME_TX_PER_FRAME_COST + sig_verification + value_transfer
    intrinsic = base + frame_data + sig_data
    floor_bytes = sum(len(f["data"]) for f in frames) + sum(len(s["signer"]) + len(s["msg"]) + len(s["sig"]) for s in sigs)
    floor = base + TOTAL_COST_FLOOR_PER_TOKEN * 4 * floor_bytes
    exec_limits = sum(f["limits"][0] for f in frames)
    state_limits = sum(f["limits"][1] for f in frames)
    return {"intrinsic": intrinsic, "floor": floor, "floor_bytes": floor_bytes, "exec_limits": exec_limits,
            "state_limits": state_limits, "max_gas": max(intrinsic + exec_limits + state_limits, floor + state_limits)}


# ───────────────────────────── metered EVM for a whole frame ─────────────────────────────
class OutOfGas(Halt):
    pass


def _signed(x):
    return x - (1 << 256) if x >> 255 else x


_BINOPS = {
    0x01: (3, lambda a, b: a + b), 0x02: (5, lambda a, b: a * b), 0x03: (3, lambda a, b: a - b),
    0x04: (5, lambda a, b: a // b if b else 0),
    0x05: (5, lambda a, b: 0 if b == 0 else abs(_signed(a)) // abs(_signed(b)) * (1 if (_signed(a) < 0) == (_signed(b) < 0) else -1)),
    0x06: (5, lambda a, b: a % b if b else 0),
    0x07: (5, lambda a, b: 0 if b == 0 else (abs(_signed(a)) % abs(_signed(b))) * (-1 if _signed(a) < 0 else 1)),
    0x0B: (5, lambda k, x: x if k >= 31 else ((x & ((1 << (8 * k + 8)) - 1)) | (M ^ ((1 << (8 * k + 8)) - 1)) if (x >> (8 * k + 7)) & 1 else x & ((1 << (8 * k + 8)) - 1))),
    0x10: (3, lambda a, b: int(a < b)), 0x11: (3, lambda a, b: int(a > b)),
    0x12: (3, lambda a, b: int(_signed(a) < _signed(b))), 0x13: (3, lambda a, b: int(_signed(a) > _signed(b))),
    0x14: (3, lambda a, b: int(a == b)),
    0x16: (3, lambda a, b: a & b), 0x17: (3, lambda a, b: a | b), 0x18: (3, lambda a, b: a ^ b),
    0x1A: (3, lambda i, x: (x >> (8 * (31 - i))) & 0xFF if i < 32 else 0),
    0x1B: (3, lambda sh, v: v << sh if sh < 256 else 0), 0x1C: (3, lambda sh, v: v >> sh if sh < 256 else 0),
    0x1D: (3, lambda sh, v: _signed(v) >> (sh if sh < 256 else 255)),
}
# Instructions the public mempool bans in a validation prefix (GAS is handled separately).
_BANNED = {0x3A: "GASPRICE", 0x40: "BLOCKHASH", 0x41: "COINBASE", 0x42: "TIMESTAMP", 0x43: "NUMBER",
           0x44: "PREVRANDAO", 0x45: "GASLIMIT", 0x48: "BASEFEE", 0x4A: "BLOBBASEFEE", 0x4B: "SLOTNUM",
           0xF0: "CREATE", 0xF5: "CREATE2", 0xF6: "SETDELEGATE", 0xFF: "SELFDESTRUCT", 0x31: "BALANCE",
           0x47: "SELFBALANCE", 0x55: "SSTORE"}
_UNMODELLED = {0x54: "SLOAD", 0x5C: "TLOAD", 0x5D: "TSTORE", 0xF1: "CALL", 0xF2: "CALLCODE", 0x3C: "EXTCODECOPY",
               0x46: "CHAINID", 0x49: "BLOBHASH", 0xA0: "LOG0", 0xA1: "LOG1", 0xA2: "LOG2", 0xA3: "LOG3", 0xA4: "LOG4"}
_CALLS = (0xF1, 0xF2, 0xF4, 0xFA)


class Evm:
    """See the module docstring. `codes` maps an address (int) to its deployed code; `warm` is
    the set of already-accessed addresses (EIP-2929). With `tx` set, the EIP-8141 instructions
    answer from that transaction and `frame_index`; without it they halt, as on any other
    transaction type."""

    def __init__(self, codes, warm=(), tx=None, sig_hash=None, frame_index=None):
        self.codes = codes
        self.warm = set(warm)
        self.tx, self.sig_hash, self.fi = tx, sig_hash, frame_index
        self.approved = 0  # scope of the APPROVE that stands (journaled with the call frames)
        self.trace = []  # one record per STATICCALL / DELEGATECALL, in completion order
        self.violations = []  # public-mempool trace-rule violations that did not halt
        self.detail = ""
        self._jumpdests = {}

    def _dests(self, code):
        d = self._jumpdests.get(id(code))
        if d is None:
            d, k = set(), 0
            while k < len(code):
                if code[k] == 0x5B:
                    d.add(k)
                k += 1 + (code[k] - 0x5F if 0x60 <= code[k] <= 0x7F else 0)
            self._jumpdests[id(code)] = d
        return d

    def _frame_param(self, p, idx):
        frames = self.tx["frames"]
        if idx >= len(frames):
            raise Halt("FRAMEPARAM frameIndex out of bounds")
        f = frames[idx]
        if p == 0x00:
            return int.from_bytes(resolved_target(self.tx, idx), "big")
        if p == 0x01:
            return f["limits"][0]
        if p == 0x02:
            return f["mode"]
        if p == 0x03:
            return f["flags"]
        if p == 0x04:
            return len(f["data"])
        if p == 0x06:
            return f["flags"] & 3
        if p == 0x07:
            return (f["flags"] >> 2) & 1
        if p == 0x08:
            return f["value"]
        if p == 0x09:
            return f["limits"][1]
        if p in (0x05, 0x0A, 0x0B):
            if idx >= self.fi:
                raise Halt("FRAMEPARAM status / gas used of the current or a later frame")
            raise Halt("FRAMEPARAM status / gas used of an earlier frame is not modelled")
        raise Halt(f"undefined FRAMEPARAM param {p:#04x}")

    def _tx_param(self, p):
        tx = self.tx
        table = {0x00: FRAME_TX_TYPE, 0x01: tx["nonce"], 0x02: int.from_bytes(tx["sender"], "big"),
                 0x07: 0, 0x08: int.from_bytes(self.sig_hash, "big"), 0x09: len(tx["frames"]), 0x0A: self.fi,
                 0x0B: len(tx["signatures"]), 0x0C: tx["frames"][self.fi]["limits"][1]}
        if tx["spec"] == REV_2026_11_01:
            table[0x03], table[0x04] = tx["fees"][1], tx["fees"][0]
        if p not in table:
            raise Halt(f"TXPARAM {p:#x} is undefined or not modelled")
        return table[p]

    def _sig_param(self, p, i):
        sigs = self.tx["signatures"]
        if i >= len(sigs):
            raise Halt("signatureIndex out of bounds")
        s = sigs[i]
        if p == 0x00:
            if s["scheme"] == ARBITRARY:
                raise Halt("SIGPARAM resolved_signer of an ARBITRARY entry")
            return int.from_bytes(s["signer"] or self.tx["sender"], "big")
        if p == 0x01:
            return s["scheme"]
        if p == 0x02:
            return int.from_bytes(s["msg"], "big") if s["msg"] else 0
        if p == 0x03:
            if s["scheme"] != ARBITRARY:
                raise Halt("SIGPARAM len(signature) of a non-ARBITRARY entry")
            return len(s["sig"])
        raise Halt(f"undefined SIGPARAM param {p:#04x}")

    def call(self, *, code_addr, address, caller, origin, calldata, gas, depth=0):
        """Run `code_addr`'s code as `address`. Returns (status, return data, gas left) with
        status "ok", "revert" or "halt" (a halt consumes all the gas)."""
        try:
            return self._run(self.codes[code_addr], address, caller, origin, calldata, gas, depth)
        except Halt as e:
            if not self.detail:
                self.detail = f"exceptional halt in {code_addr:#x}: {e}"
            return "halt", b"", 0

    def _run(self, code, address, caller, origin, calldata, gas, depth):
        if depth > 16:
            raise Halt("call depth")
        dests = self._dests(code)
        stack, mem, ret_data, pc = [], bytearray(), b"", 0
        tx = self.tx

        def use(n):
            nonlocal gas
            gas -= n
            if gas < 0:
                raise OutOfGas("out of gas")

        def mext(off, size):
            if size == 0:
                return
            if off + size > (1 << 26):
                raise OutOfGas("memory expansion out of gas")
            old, new = len(mem) // 32, (off + size + 31) // 32
            if new > old:
                use(3 * new + new * new // 512 - 3 * old - old * old // 512)
                mem.extend(b"\x00" * (32 * (new - old)))

        def copy_cost(size):
            use(3 + 3 * ((size + 31) // 32))

        def padded(src, off, n):
            out = src[off:off + n] if off < len(src) else b""
            return bytes(out) + b"\x00" * (n - len(out))

        def pop():
            if not stack:
                raise Halt("stack underflow")
            return stack.pop()

        def push(v):
            if len(stack) >= 1024:
                raise Halt("stack overflow")
            stack.append(v & M)

        def need_frame_tx(name):
            if tx is None:
                raise Halt(f"{name} outside a frame transaction")

        while True:
            if pc >= len(code):
                return "ok", b"", gas
            op = code[pc]
            if op in _BINOPS:
                cost, fn = _BINOPS[op]
                use(cost)
                a, b = pop(), pop()
                push(fn(a, b))
            elif 0x60 <= op <= 0x7F:
                use(3)
                n = op - 0x5F
                push(int.from_bytes(code[pc + 1:pc + 1 + n].ljust(n, b"\x00"), "big"))
                pc += n
            elif 0x80 <= op <= 0x8F:
                use(3)
                n = op - 0x7F
                if len(stack) < n:
                    raise Halt("DUP underflow")
                push(stack[-n])
            elif 0x90 <= op <= 0x9F:
                use(3)
                n = op - 0x8F
                if len(stack) < n + 1:
                    raise Halt("SWAP underflow")
                stack[-1], stack[-1 - n] = stack[-1 - n], stack[-1]
            elif op == 0x00:
                return "ok", b"", gas
            elif op == 0x08 or op == 0x09:
                use(8)
                a, b, n = pop(), pop(), pop()
                push(0 if n == 0 else ((a + b) if op == 0x08 else (a * b)) % n)
            elif op == 0x0A:
                a, e = pop(), pop()
                use(10 + 50 * ((e.bit_length() + 7) // 8))
                push(pow(a, e, 1 << 256))
            elif op == 0x15:
                use(3)
                push(int(pop() == 0))
            elif op == 0x19:
                use(3)
                push(~pop())
            elif op == 0x20:
                off, size = pop(), pop()
                use(30 + 6 * ((size + 31) // 32))
                mext(off, size)
                push(int.from_bytes(keccak256(bytes(mem[off:off + size])), "big"))
            elif op == 0x30:
                use(2)
                push(address)
            elif op == 0x32:
                use(2)
                push(origin)
            elif op == 0x33:
                use(2)
                push(caller)
            elif op == 0x34:
                use(2)
                push(0)  # no call here carries value
            elif op == 0x35:
                use(3)
                push(int.from_bytes(padded(calldata, pop(), 32), "big"))
            elif op == 0x36:
                use(2)
                push(len(calldata))
            elif op == 0x37 or op == 0x39:
                mo, do, ln = pop(), pop(), pop()
                copy_cost(ln)
                mext(mo, ln)
                mem[mo:mo + ln] = padded(calldata if op == 0x37 else code, do, ln)
            elif op == 0x38:
                use(2)
                push(len(code))
            elif op == 0x3B or op == 0x3F:
                a = pop() & ((1 << 160) - 1)
                use(100 if a in self.warm else 2600)
                self.warm.add(a)
                c = self.codes.get(a, b"")
                if not c:
                    self.violations.append(f"EXTCODE* of the code-less address {a:#x}")
                push(len(c) if op == 0x3B else (int.from_bytes(keccak256(c), "big") if c else 0))
            elif op == 0x3D:
                use(2)
                push(len(ret_data))
            elif op == 0x3E:
                mo, do, ln = pop(), pop(), pop()
                copy_cost(ln)
                if do + ln > len(ret_data):
                    raise Halt("RETURNDATACOPY out of bounds")
                mext(mo, ln)
                mem[mo:mo + ln] = ret_data[do:do + ln]
            elif op == 0x50:
                use(2)
                pop()
            elif op == 0x51:
                use(3)
                off = pop()
                mext(off, 32)
                push(int.from_bytes(mem[off:off + 32], "big"))
            elif op == 0x52:
                use(3)
                off, v = pop(), pop()
                mext(off, 32)
                mem[off:off + 32] = v.to_bytes(32, "big")
            elif op == 0x53:
                use(3)
                off, v = pop(), pop()
                mext(off, 1)
                mem[off] = v & 0xFF
            elif op == 0x56:
                use(8)
                d = pop()
                if d not in dests:
                    raise Halt("bad jump destination")
                pc = d
                continue
            elif op == 0x57:
                use(10)
                d, c = pop(), pop()
                if c:
                    if d not in dests:
                        raise Halt("bad jumpi destination")
                    pc = d
                    continue
            elif op == 0x58:
                use(2)
                push(pc)
            elif op == 0x59:
                use(2)
                push(len(mem))
            elif op == 0x5A:
                use(2)
                if pc + 1 >= len(code) or code[pc + 1] not in _CALLS:
                    self.violations.append(f"GAS at pc {pc} is not immediately followed by a *CALL")
                push(gas)
            elif op == 0x5B:
                use(1)
            elif op == 0x5E:
                dst, src, ln = pop(), pop(), pop()
                copy_cost(ln)
                mext(max(dst, src), ln)
                mem[dst:dst + ln] = bytes(mem[src:src + ln])
            elif op == 0x5F:
                use(2)
                push(0)
            elif op == 0xF3 or op == 0xFD:
                off, ln = pop(), pop()
                mext(off, ln)
                return ("ok" if op == 0xF3 else "revert"), bytes(mem[off:off + ln]), gas
            elif op == 0xFA or op == 0xF4:
                g, to, ao, al, ro, rl = [pop() for _ in range(6)]
                to &= (1 << 160) - 1
                mext(ao, al)
                mext(ro, rl)
                use(100 if to in self.warm else 2600)
                self.warm.add(to)
                if 0 < to <= 0x100 and to not in self.codes:
                    raise Halt(f"precompile {to:#x} is not modelled")
                fwd = min(g, gas - gas // 64)
                gas -= fwd
                data = bytes(mem[ao:ao + al])
                if not self.codes.get(to):
                    # An ordinary call to a code-less address succeeds and returns nothing.
                    self.violations.append(f"*CALL to the code-less address {to:#x}")
                    status, out, left = "ok", b"", fwd
                else:
                    saved = (set(self.warm), self.approved)
                    if op == 0xFA:
                        status, out, left = self.call(code_addr=to, address=to, caller=address, origin=origin,
                                                      calldata=data, gas=fwd, depth=depth + 1)
                    else:
                        status, out, left = self.call(code_addr=to, address=address, caller=caller, origin=origin,
                                                      calldata=data, gas=fwd, depth=depth + 1)
                    if status != "ok":
                        self.warm, self.approved = saved
                self.trace.append({"kind": "STATICCALL" if op == 0xFA else "DELEGATECALL", "to": to, "calldata": data,
                                   "gas": fwd - left, "status": status, "ret": out})
                gas += left
                ret_data = out
                n = min(rl, len(out))
                mem[ro:ro + n] = out[:n]
                push(int(status == "ok"))
            elif op == 0xFE:
                raise Halt("INVALID")
            elif op == 0xB0:
                need_frame_tx("TXPARAM")
                use(2)
                push(self._tx_param(pop()))
            elif op == 0xB1:
                need_frame_tx("FRAMEDATALOAD")
                use(3)
                off, idx = pop(), pop()
                if idx >= len(tx["frames"]):
                    raise Halt("FRAMEDATALOAD frameIndex out of bounds")
                push(int.from_bytes(padded(tx["frames"][idx]["data"], off, 32), "big"))
            elif op == 0xB2:
                need_frame_tx("FRAMEDATACOPY")
                mo, do, ln, idx = pop(), pop(), pop(), pop()
                if idx >= len(tx["frames"]):
                    raise Halt("FRAMEDATACOPY frameIndex out of bounds")
                copy_cost(ln)
                mext(mo, ln)
                mem[mo:mo + ln] = padded(tx["frames"][idx]["data"], do, ln)
            elif op == 0xB3:
                need_frame_tx("FRAMEPARAM")
                use(2)
                idx, p = pop(), pop()
                push(self._frame_param(p, idx))
            elif op == 0xB4:
                need_frame_tx("SIGPARAM")
                use(2)
                i, p = pop(), pop()
                push(self._sig_param(p, i))
            elif op == 0xB5:
                need_frame_tx("SIGDATACOPY")
                mo, do, ln, i = pop(), pop(), pop(), pop()
                if i >= len(tx["signatures"]):
                    raise Halt("signatureIndex out of bounds")
                s = tx["signatures"][i]
                if s["scheme"] != ARBITRARY:
                    raise Halt("SIGDATACOPY of a non-ARBITRARY entry")
                copy_cost(ln)
                mext(mo, ln)
                mem[mo:mo + ln] = padded(s["sig"], do, ln)
            elif op == 0xAA:
                # APPROVE(offset, length, scope): memory expansion only, then exit like RETURN
                # with the approval recorded, or revert this call frame.
                need_frame_tx("APPROVE")
                off, ln, scope = pop(), pop(), pop()
                mext(off, ln)
                target = int.from_bytes(resolved_target(tx, self.fi), "big")
                sender = int.from_bytes(tx["sender"], "big")
                allowed = tx["frames"][self.fi]["flags"] & 3
                why = ""
                if address != target:
                    why = "ADDRESS is not the frame's resolved target"
                elif scope == 0 or scope & ~allowed & M:
                    why = f"scope {scope} is outside the frame's flags ({allowed})"
                elif self.approved:
                    why = "already approved"
                elif scope & 2 and target != sender:
                    why = "execution approved by an account that is not the sender"
                elif scope == 1:
                    why = "payment before execution was approved"  # a lone pay frame; earlier frames are not modelled
                if why:
                    self.detail = f"APPROVE({scope}) rejected: {why}"
                    return "revert", b"", gas
                self.approved = scope
                return "ok", bytes(mem[off:off + ln]), gas
            elif op in _BANNED:
                raise Halt(f"{_BANNED[op]} is banned in a validation prefix")
            elif op in _UNMODELLED:
                raise Halt(f"{_UNMODELLED[op]} is not modelled (no storage, value, log or creation here)")
            else:
                raise Halt(f"unmodelled opcode {op:#04x} at pc {pc}")
            pc += 1


def _revert_reason(data):
    if data[:4] == bytes.fromhex("08c379a0") and len(data) >= 0x44:
        n = int.from_bytes(data[0x24:0x44], "big")
        return data[0x44:0x44 + n].decode(errors="replace")
    return "0x" + data.hex() if data else ""


def exec_frame(tx, sig_hash, fi, codes, gas_limit=None):
    """Execute frame `fi` as the dc5d5fa688b7 text defines it: the resolved target's access is
    charged from the frame's execution gas at entry (tx.sender is warm from the start), then the
    target's code runs with caller = ORIGIN = ENTRY_POINT (VERIFY, DEFAULT) or tx.sender (SENDER).
    Returns the outcome, the gas the frame used and the Evm (trace, violations)."""
    f = tx["frames"][fi]
    target = int.from_bytes(resolved_target(tx, fi), "big")
    sender = int.from_bytes(tx["sender"], "big")
    limit = f["limits"][0] if gas_limit is None else gas_limit
    evm = Evm(codes, warm={sender}, tx=tx, sig_hash=sig_hash, frame_index=fi)
    access = 100 if target in evm.warm else 2600
    res = {"outcome": OUT_HALT, "scope": 0, "gas_used": limit, "detail": "", "evm": evm}
    if limit < access:
        res["detail"] = "exceptional halt: the frame's gas does not cover the target's access"
        return res
    if target not in codes:
        res["detail"] = "the frame's target has no code here (default code is not modelled)"
        return res
    evm.warm.add(target)
    caller = sender if f["mode"] == SENDER else ENTRY_POINT
    status, out, left = evm.call(code_addr=target, address=target, caller=caller, origin=caller, calldata=f["data"],
                                 gas=limit - access)
    res["gas_used"] = limit - left
    if status == "halt":
        res["detail"] = evm.detail
    elif status == "revert":
        res["outcome"] = OUT_REVERT
        res["detail"] = evm.detail or f"REVERT {_revert_reason(out)}"
    elif evm.approved:
        res["outcome"], res["scope"], res["detail"] = OUT_APPROVE, evm.approved, f"APPROVE({evm.approved})"
    else:
        res["outcome"], res["detail"] = OUT_STOP, "returned without APPROVE"
    return res


def _codes(args):
    codes = {}
    for a in args:
        address, code = a.split("=", 1)
        codes[int(address, 16)] = h(code)
    return codes


# ───────────────────────────── ABI helpers + CLI ─────────────────────────────
def w(x):
    return int(x).to_bytes(32, "big")


def abi(*items):
    """abi.encode for static words (int) and dynamic bytes/str."""
    head, tail = b"", b""
    base = 32 * len(items)
    for it in items:
        if isinstance(it, (bytes, str)):
            b = it.encode() if isinstance(it, str) else it
            head += w(base + len(tail))
            tail += w(len(b)) + b + b"\x00" * ((-len(b)) % 32)
        else:
            head += w(it)
    return "0x" + (head + tail).hex()


def main():
    cmd = sys.argv[1]
    if cmd == "call":
        gas, caller, to, calldata, warm = int(sys.argv[2]), int(sys.argv[3], 16), int(sys.argv[4], 16), h(sys.argv[5]), sys.argv[6]
        evm = Evm(_codes(sys.argv[7:]), warm=() if warm == "-" else [int(a, 16) for a in warm.split(",")])
        status, out, left = evm.call(code_addr=to, address=to, caller=caller, origin=caller, calldata=calldata, gas=gas)
        print(abi(int(status == "ok"), gas - left, out, evm.detail or status))
        return
    fxp = sys.argv[2]
    fx = json.load(open(fxp))
    if cmd == "accounts":
        a, b = fx["accounts"]["A"], fx["accounts"]["B"]
        print(abi(int(a["address"], 16), int(a["pkSeed"], 16), int(a["pkRoot"], 16),
                  int(b["address"], 16), int(b["pkSeed"], 16), int(b["pkRoot"], 16), int(fx["verifier"], 16)))
        return
    name = sys.argv[3]
    tx = load_tx(fx, name)
    static_checks(tx)
    sig_hash = compute_sig_hash(tx)
    assert sig_hash == h(fx["scenarios"][name]["sigHash"]), "fixture sigHash != compute_sig_hash(tx)"
    if cmd == "frame":
        fi = int(sys.argv[4])
        f = tx["frames"][fi]
        print(abi(int.from_bytes(resolved_target(tx, fi), "big"), f["flags"], f["data"], int.from_bytes(sig_hash, "big")))
    elif cmd == "framex":
        fi = int(sys.argv[4])
        f = tx["frames"][fi]
        print(abi(f["mode"], f["flags"], int.from_bytes(resolved_target(tx, fi), "big"), f["value"], f["limits"][0],
                  f["limits"][1], f["data"], int.from_bytes(sig_hash, "big"), int.from_bytes(tx["sender"], "big")))
    elif cmd == "witness":
        print(abi(tx["signatures"][int(sys.argv[4])]["sig"]))
    elif cmd == "mempool":
        n, gas, problems = mempool_check(tx)
        print(abi(int(not problems), n, gas, "; ".join(problems)))
    elif cmd == "gas":
        g = gas_accounting(tx)
        print(abi(g["intrinsic"], g["floor"], g["floor_bytes"], g["exec_limits"], g["state_limits"], g["max_gas"]))
    elif cmd == "exec":
        fi, limit = int(sys.argv[4]), sys.argv[5]
        r = exec_frame(tx, sig_hash, fi, _codes(sys.argv[6:]), None if limit == "-" else int(limit))
        statics = [c for c in r["evm"].trace if c["kind"] == "STATICCALL"]
        last = statics[-1] if statics else {"to": 0, "calldata": b"", "gas": 0, "ret": b""}
        print(abi(r["outcome"], r["scope"], r["gas_used"], last["to"], last["calldata"], last["gas"], last["ret"],
                  "; ".join(r["evm"].violations), r["detail"]))
    elif cmd == "run":
        fi, code, calldata, verdict = int(sys.argv[4]), h(sys.argv[5]), h(sys.argv[6]), sys.argv[7]
        vword = None if verdict == "revert" else int(verdict, 16).to_bytes(32, "big")
        r = run_module(code, tx=tx, sig_hash=sig_hash, frame_index=fi, address=resolved_target(tx, fi),
                       calldata=calldata, verdict=vword)
        call = r["calls"][0] if r["calls"] else {"to": 0, "calldata": b"", "detail": ""}
        print(abi(r["outcome"], r["scope"], r["copied"], call["to"], call["calldata"], r["detail"]))
    else:
        sys.exit(f"unknown command {cmd}")


if __name__ == "__main__":
    main()
