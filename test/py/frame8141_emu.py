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


def load_tx(fx, name):
    sc = fx["scenarios"][name]
    frames = [{"mode": f["mode"], "flags": f["flags"], "target": h(f["target"]) if f["target"] else b"",
               "limits": [f.get("execution", 2_000_000), f.get("state", 0)], "value": 0, "data": h(f["data"])}
              for f in sc["frames"]]
    sigs = [{"scheme": s["scheme"], "signer": h(s["signer"]) if s["signer"] else b"",
             "msg": h(s["msg"]) if s["msg"] else b"", "sig": h(s["sig"])} for s in sc["signatures"]]
    return {"chain_id": fx["chain_id"], "nonce": sc["nonce"], "sender": h(sc["sender"]), "frames": frames,
            "signatures": sigs, "fees": [10**9, 30 * 10**9, 0], "blob_versioned_hashes": []}


def compute_sig_hash(tx):
    sigs = [[s["scheme"], s["signer"], s["msg"], b"" if len(s["msg"]) == 0 else s["sig"]] for s in tx["signatures"]]
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
    for f in tx["frames"]:
        assert f["mode"] in (DEFAULT, VERIFY, SENDER) and f["flags"] < 8
        if f["flags"] & 0x2:
            assert f["target"] in (b"", tx["sender"])


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
    cmd, fxp = sys.argv[1], sys.argv[2]
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
    elif cmd == "witness":
        print(abi(tx["signatures"][int(sys.argv[4])]["sig"]))
    elif cmd == "run":
        fi, code, calldata, verdict = int(sys.argv[4]), h(sys.argv[5]), h(sys.argv[6]), sys.argv[7]
        vword = None if verdict == "revert" else int(verdict, 16).to_bytes(32, "big")
        r = run_module(code, tx=tx, sig_hash=sig_hash, frame_index=fi, address=resolved_target(tx, fi),
                       calldata=calldata, verdict=vword)
        call = r["calls"][0] if r["calls"] else {"to": 0, "calldata": b""}
        print(abi(r["outcome"], r["scope"], r["copied"], call["to"], call["calldata"], r["detail"]))
    else:
        sys.exit(f"unknown command {cmd}")


if __name__ == "__main__":
    main()
