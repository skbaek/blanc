#!/usr/bin/env bash
# Reproduce the committed Lido CircuitBreaker feasibility runtime in pinned EELS.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — Lido spike: pinned EELS python not found at $EELS_PY" >&2
  exit 1
fi

cd "$ROOT"
PYTHONPATH="$EELS_ROOT/src" EELS_ROOT="$EELS_ROOT" \
  "$EELS_PY" "$SCRIPT_DIR/reproduce-lido-circuit-breaker-spike.py"
