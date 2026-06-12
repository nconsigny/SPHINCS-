#!/usr/bin/env bash
# Memory-safe build wrapper for the verity package.
#
# The proof modules here are very large (Proofs.lean and related bridge
# ~480 KB, ...); a single lean worker on one of them can peak at several GB.
# A bare `lake build` spawns one worker per core (8 on this machine), which
# has OOM'd a 16 GB machine. This wrapper caps Lake's scheduler at 2
# concurrent lean processes (Lake 5 has no -j flag; it schedules onto the
# Lean task pool, bounded by LEAN_NUM_THREADS).
#
# Usage: scripts/build.sh [lake build args, e.g. a module name]
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${VERITY_JOBS:-2}"
exec lake build "$@"
