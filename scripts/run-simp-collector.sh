#!/usr/bin/env bash
# Capture one file under exact candidate setup; JSON and diagnostics are separate.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
cd "$ROOT"
if [ "$#" -ne 4 ]; then
  echo "usage: scripts/run-simp-collector.sh ORIGINAL BUFFER CANDIDATE_SETUP OUTPUT_JSON" >&2
  exit 2
fi
if [ -e "$4" ] || [ -L "$4" ]; then
  echo "COLLECTOR output already exists: $4" >&2
  exit 1
fi
if [ ! -x "$ROOT/.lake/build/bin/simpCollector" ]; then
  echo "REFUSED — build simpCollector through the owned build wrapper first" >&2
  exit 2
fi
. "$SCRIPT_DIR/gate-semaphore.sh"
trap gate_semaphore_release EXIT
# A native frontend worker sits outside the watched owned-build path. Unknown
# production environments use this host's default 8 GiB task estimate; the
# earlier 4 GiB estimate established only Basic and bounded fixture behavior.
COLLECTOR_MEMORY_GIB=8
if [ ! -x "$GATE_SEMAPHORE_ENTRY" ] || [ -n "${BLANC_GATE_SEMAPHORE:-}" ] ||
    [ -n "${BLANC_GATE_SEMAPHORE_MEMORY_GIB:-}" ]; then
  echo "REFUSED — collector requires live host admission without an override" >&2
  exit 2
fi
gate_semaphore_acquire "one-file simplification collector: $1" "$COLLECTOR_MEMORY_GIB" sensitive || exit 2
echo "COLLECTOR-ADMISSION goal=$(gate_semaphore_label) memory_gib=$COLLECTOR_MEMORY_GIB contention=sensitive cwd=$ROOT" >&2
lake env "$ROOT/.lake/build/bin/simpCollector" "$@"
