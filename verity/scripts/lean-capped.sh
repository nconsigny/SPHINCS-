#!/usr/bin/env bash
set -euo pipefail

# Run Lean/Lake with a virtual-memory cap. This is intended for large proof
# files where an accidentally huge proof term can otherwise consume the whole
# container before failing.
#
# Defaults:
#   LEAN_MEM_KB=12000000  # about 12 GB virtual memory
#
# Examples:
#   scripts/lean-capped.sh lake env lean SphincsMinusVerifiers/SegmentLayer3.lean
#   scripts/lean-capped.sh lake build -j1 SphincsMinusVerifiers

mem_kb="${LEAN_MEM_KB:-12000000}"

if [[ $# -eq 0 ]]; then
  echo "usage: LEAN_MEM_KB=$mem_kb $0 <command> [args...]" >&2
  exit 2
fi

ulimit -v "$mem_kb"
exec /usr/bin/time -v "$@"
