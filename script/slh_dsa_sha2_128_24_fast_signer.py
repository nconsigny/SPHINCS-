#!/usr/bin/env python3
"""
Fast SLH-DSA-SHA2-128-24 signer — wraps the forked sphincsplus C binary
(signers/sphincsplus-128-24/slhdsa-sha2-128-24) and emits the same
ABI-encoded (bytes32 seed, bytes32 root, bytes sig) format used by the
pure-Python `slh_dsa_sha2_128_24_signer.py`.

The C binary produces a real NIST-params signature (h=22, d=1, a=24, k=6)
in ~1-3 minutes; our pure-Python signer takes hours for the same task.
Use this wrapper for Forge FFI tests and fixture generation.

A disk cache is used: if a fixture with the same inputs is already on
disk, we return it immediately.

Usage:
    python3 script/slh_dsa_sha2_128_24_fast_signer.py \\
        <master_sk_hex> <message_hex> [sig_counter]

Same CLI shape as the pure-Python signer. Key derivation uses the JARDIN
HMAC-SHA-512 scheme for parity; the 48-byte (sk_seed‖sk_prf‖pk_seed) seed
is handed to the C binary.
"""

import sys, os, json, hashlib, hmac, subprocess, argparse

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
BIN_PATH  = os.path.join(REPO_ROOT, "signers/sphincsplus-128-24/slhdsa-sha2-128-24")
CACHE_DIR = os.path.join(REPO_ROOT, "signers/sphincsplus-128-24/.cache")

N       = 16
SIG_LEN = 3856

def eprint(*a, **kw): print(*a, file=sys.stderr, **kw)

def assert_binary_fresh(allow_stale=False):
    """Refuse to run a C binary older than the sources it was built from.

    The binary is gitignored, so a working tree easily carries sources newer than
    the last local `make`. That has bitten: ec5aae3 made this signer
    hedged-by-default — reshaping its argv — and fixed FORS parsing to MSB-first,
    but a binary built three weeks earlier stayed on disk. The wrapper passed
    `--hedged`, the old argv layout read that flag as the seed, and every SLH-DSA
    FFI test failed with "bad seed hex (need 48 bytes)" for six weeks. CI never
    saw it, because CI runs `make` before `forge test`.

    The crash was the lucky outcome. Parameters and CLI shape are compile-time
    here, so a stale binary can just as easily sign under the *wrong scheme* with
    no error at all — the same rebuild also picked up the FORS MSB-first change.
    So fail closed rather than hand the mismatch to the binary.
    """
    src_dir = os.path.dirname(BIN_PATH)
    bin_mtime = os.path.getmtime(BIN_PATH)
    newer = sorted(
        f for f in os.listdir(src_dir)
        if (f.endswith((".c", ".h")) or f == "Makefile")
        and os.path.getmtime(os.path.join(src_dir, f)) > bin_mtime
    )
    if not newer:
        return
    shown = ", ".join(newer[:6]) + (" ..." if len(newer) > 6 else "")
    eprint(f"  STALE C binary: {os.path.relpath(BIN_PATH, REPO_ROOT)}")
    eprint(f"  {len(newer)} source file(s) newer than it: {shown}")
    eprint(f"  Rebuild:  make -C {os.path.relpath(src_dir, REPO_ROOT)}")
    if allow_stale:
        eprint("  --allow-stale-binary given: using it anyway.")
        return
    sys.exit(1)

def hmac512(key, msg):
    return hmac.new(key, msg, hashlib.sha512).digest()

def derive_seed_48(master_sk: bytes) -> bytes:
    """Mirrors the JARDIN derivation used by slh_dsa_sha2_128_24_signer.py."""
    sk_seed = hmac512(master_sk, b"JARDIN/SLH2128_24/SKSEED")[:N]
    sk_prf  = hmac512(master_sk, b"JARDIN/SLH2128_24/SKPRF" )[:N]
    pk_seed = hmac512(master_sk, b"JARDIN/SLH2128_24/PKSEED")[:N]
    return sk_seed + sk_prf + pk_seed

def abi_encode(seed16: bytes, root16: bytes, sig: bytes) -> bytes:
    seed32 = seed16 + b"\x00" * (32 - N)
    root32 = root16 + b"\x00" * (32 - N)
    enc  = seed32 + root32
    enc += (0x60).to_bytes(32, "big")
    enc += len(sig).to_bytes(32, "big")
    enc += sig + b"\x00" * ((32 - len(sig) % 32) % 32)
    return enc

def _norm(s: str) -> str: return s.lower().removeprefix("0x")

def cache_key(master_sk_hex: str, message_hex: str, sig_counter: int) -> str:
    # Cache key includes a convention tag so that bumping signature
    # conventions (e.g. the FORS digest LE→BE switch for FIPS 205, or the
    # external empty-ctx envelope) breaks the cache for any pre-existing
    # fixtures. It also folds in the C binary's mtime so a rebuild (e.g. a
    # reduced-height dev build) cannot silently serve a stale fixture under
    # different params. (review SLH-X-f1 / SLH-S-f3)
    CONVENTION_TAG = b"fips205-external-empty-ctx-v2"
    h = hashlib.sha256()
    h.update(CONVENTION_TAG)
    h.update(b"|")
    h.update(_norm(master_sk_hex).encode())
    h.update(b"|")
    h.update(_norm(message_hex).encode())
    h.update(b"|")
    h.update(str(sig_counter).encode())
    h.update(b"|")
    h.update(str(os.path.getmtime(BIN_PATH)).encode())
    return h.hexdigest()

def main():
    p = argparse.ArgumentParser(
        description="SLH-DSA-SHA2-128-24 CPU fast signer. Default is HEDGED "
                    "(opt_rand drawn from kernel CSPRNG inside the C binary). "
                    "Pass `sig_counter` (positional) to force deterministic mode.",
    )
    p.add_argument("master_sk_hex")
    p.add_argument("message_hex")
    p.add_argument("sig_counter", nargs="?", default=None, type=int,
                   help="If given, use deterministic mode with opt_rand=<counter,big-endian>||zeros. "
                        "If omitted, hedged.")
    p.add_argument("--no-cache", action="store_true")
    p.add_argument("--hedged", action="store_true",
                   help="(default) Force hedged mode even if sig_counter is given.")
    p.add_argument("--allow-stale-binary", action="store_true",
                   help="Use the C binary even when its sources are newer — only for "
                        "deliberately reproducing an old vector. Off by default: "
                        "parameters and CLI shape are compile-time, so a stale binary "
                        "can sign under the wrong scheme without erroring.")
    args = p.parse_args()

    if not args.hedged and args.sig_counter is None:
        args.hedged = True

    if not os.path.isfile(BIN_PATH):
        eprint(f"  C binary not found at {BIN_PATH}")
        eprint(f"  Build with:  (cd signers/sphincsplus-128-24 && make)")
        sys.exit(1)
    assert_binary_fresh(args.allow_stale_binary)

    master_sk = bytes.fromhex(args.master_sk_hex.removeprefix("0x"))
    if len(master_sk) != 32:
        eprint("master_sk must be 32 bytes"); sys.exit(1)

    msg_hex = args.message_hex.removeprefix("0x")
    if len(msg_hex) % 2: msg_hex = "0" + msg_hex
    # FIPS 205 EXTERNAL SLH-DSA.Sign with empty context: the C binary is
    # slh_sign_internal (signs raw bytes), so we apply the envelope here by
    # prepending M' = toByte(0,1) ‖ toByte(0,1) ‖ M = 0x00 0x00 ‖ M. The
    # on-chain verifier prepends the same two bytes internally. (review SLH-X-f1)
    msg_hex_signed = "0000" + msg_hex

    # In hedged mode (default) we pass --hedged through to the C binary so
    # opt_rand is drawn inside via getrandom(2).
    if not args.hedged:
        sig_counter = args.sig_counter if args.sig_counter is not None else 0
        optrand = sig_counter.to_bytes(4, "big") + b"\x00" * (N - 4)

    # Disk cache (counter mode only — hedged sigs are intentionally non-reproducible
    # across calls, so caching them by (key, msg, counter) is meaningless).
    cache_path = None
    if not args.hedged:
        os.makedirs(CACHE_DIR, exist_ok=True)
        key = cache_key(args.master_sk_hex, args.message_hex, sig_counter)
        cache_path = os.path.join(CACHE_DIR, f"{key}.hex")

        if not args.no_cache and os.path.isfile(cache_path):
            eprint(f"  [cache hit] {cache_path}")
            with open(cache_path, "r") as f:
                print(f.read().strip())
            return

    seed48 = derive_seed_48(master_sk)

    eprint(f"  invoking C signer (h=22, a=24 — ~1-3 min)...")
    if args.hedged:
        cmd = [BIN_PATH, "--hedged", seed48.hex(), msg_hex_signed]
    else:
        cmd = [BIN_PATH, seed48.hex(), msg_hex_signed, optrand.hex()]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if args.hedged:
        for line in result.stderr.splitlines():
            if "mode: hedged" in line:
                eprint(line)
                break
    if result.returncode != 0:
        eprint(f"  C signer failed (rc={result.returncode}):")
        eprint(result.stderr)
        sys.exit(1)

    raw = bytes.fromhex(result.stdout.strip())
    if len(raw) != 2 * N + SIG_LEN:
        eprint(f"  unexpected C output size: {len(raw)} != {2*N + SIG_LEN}")
        sys.exit(1)
    pk_seed = raw[:N]
    pk_root = raw[N:2*N]
    sig     = raw[2*N:]

    eprint(f"  pk_seed = 0x{pk_seed.hex()[:16]}…")
    eprint(f"  pk_root = 0x{pk_root.hex()[:16]}…")
    eprint(f"  sig: {len(sig)} bytes")

    abi_hex = "0x" + abi_encode(pk_seed, pk_root, sig).hex()
    if cache_path is not None:
        with open(cache_path, "w") as f:
            f.write(abi_hex + "\n")
        eprint(f"  cached at {cache_path}")
    print(abi_hex)

if __name__ == "__main__":
    main()
