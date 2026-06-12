#!/usr/bin/env python3
"""
SLH-DSA-SHA2-128-24 GPU signer wrapper.

Mirrors `slh_dsa_sha2_128_24_fast_signer.py` (which wraps the CPU C reference
at signers/sphincsplus-128-24/) but invokes the Vulkan-accelerated GPU signer
at `signers/slhvk-sha2-128-24/slhdsa-sha2-128-24-gpu` instead.

Status:
  - Keygen: BIT-EXACT, deterministic, ~0.6 s/key.
  - Signing: BIT-EXACT, deterministic, ~1 s/sig.
  - ~180x faster than the CPU reference for combined keygen+sign.

Modes:
  - Hedged (DEFAULT): opt_rand drawn from getrandom(2) inside the C binary.
    FIPS 205 §9.2 recommendation. Each sign produces a fresh sig; cache off.
  - Counter (explicit): pass `sig_counter` positional — opt_rand =
    counter(4 B big-endian) || zeros. Reproducible per (key, msg, counter),
    cached on disk. Use for KATs / test fixtures only.

Same CLI shape, disk-cache layout, and JARDIN HMAC-SHA-512 seed derivation
as the CPU fast-signer, so this is a drop-in replacement for any caller that
only needs pk_root.
"""

import sys, os, json, hashlib, hmac, subprocess, argparse

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
BIN_PATH  = os.path.join(REPO_ROOT, "signers/slhvk-sha2-128-24/slhdsa-sha2-128-24-gpu")
CACHE_DIR = os.path.join(REPO_ROOT, "signers/slhvk-sha2-128-24/.cache")

N       = 16
SIG_LEN = 3856

def eprint(*a, **kw): print(*a, file=sys.stderr, **kw)

def hmac512(key, msg):
    return hmac.new(key, msg, hashlib.sha512).digest()

def derive_seed_48(master_sk: bytes) -> bytes:
    """JARDIN derivation — identical to the CPU fast-signer."""
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
    # Convention tag invalidates pre-envelope fixtures (review SLH-X-f1).
    # Like the CPU fast signer, also fold in the GPU binary's mtime so a
    # rebuild (e.g. a reduced-height dev build) cannot silently serve a
    # stale fixture under the same tag.
    h = hashlib.sha256()
    h.update(b"fips205-external-empty-ctx-v2|")
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
        description="SLH-DSA-SHA2-128-24 GPU signer. Default is HEDGED "
                    "(opt_rand drawn from kernel CSPRNG inside the C binary). "
                    "Pass `sig_counter` (positional) to force deterministic mode.",
    )
    p.add_argument("master_sk_hex")
    p.add_argument("message_hex")
    p.add_argument("sig_counter", nargs="?", default=None, type=int,
                   help="If given, use deterministic mode with opt_rand=<counter,big-endian>||zeros "
                        "(reproducible per (key, msg, counter)). If omitted, hedged.")
    p.add_argument("--no-cache", action="store_true")
    p.add_argument("--hedged", action="store_true",
                   help="(default) Force hedged mode even if sig_counter is given.")
    args = p.parse_args()

    # Default: hedged unless the caller passed a sig_counter positional.
    if not args.hedged and args.sig_counter is None:
        args.hedged = True

    if not os.path.isfile(BIN_PATH):
        eprint(f"  GPU binary not found at {BIN_PATH}")
        eprint(f"  Build with:  (cd signers/slhvk-sha2-128-24 && make cli)")
        sys.exit(1)

    master_sk = bytes.fromhex(args.master_sk_hex.removeprefix("0x"))
    if len(master_sk) != 32:
        eprint("master_sk must be 32 bytes"); sys.exit(1)

    msg_hex = args.message_hex.removeprefix("0x")
    if len(msg_hex) % 2: msg_hex = "0" + msg_hex
    # FIPS 205 external SLH-DSA.Sign, empty ctx: sign M' = 0x00 0x00 ‖ M. The GPU
    # binary is slh_sign_internal (raw bytes), so we prepend the envelope here to
    # match the on-chain verifier. (review SLH-X-f1)
    msg_hex_signed = "0000" + msg_hex

    # In hedged mode (the default) we pass --hedged through to the GPU binary
    # so opt_rand is drawn inside the C binary via getrandom(2). Python only
    # orchestrates the seed derivation + caching.
    if not args.hedged:
        sig_counter = args.sig_counter if args.sig_counter is not None else 0
        optrand = sig_counter.to_bytes(4, "big") + b"\x00" * (N - 4)

    # Disk cache (counter mode only — hedged sigs are intentionally non-reproducible).
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

    # GPU sign is bit-deterministic (16/16 verified after the keygen barrier
    # fix in src/keygen.c — see signers/slhvk-sha2-128-24/STATUS.md). One call
    # suffices; no retry needed.
    if args.hedged:
        cmd = [BIN_PATH, "--hedged", seed48.hex(), msg_hex_signed]
    else:
        cmd = [BIN_PATH, seed48.hex(), msg_hex_signed, optrand.hex()]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if args.hedged:
        # Forward the C binary's "mode: hedged (opt_rand=…)" line so the
        # caller can see (and replay) the randomizer.
        for line in result.stderr.splitlines():
            if "mode: hedged" in line:
                eprint(line)
                break
    if result.returncode != 0:
        eprint(f"  GPU signer failed (rc={result.returncode}):")
        eprint(result.stderr)
        sys.exit(1)
    raw = bytes.fromhex(result.stdout.strip())
    if len(raw) != 2 * N + SIG_LEN:
        eprint(f"  unexpected GPU output size: {len(raw)} != {2*N + SIG_LEN}")
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
