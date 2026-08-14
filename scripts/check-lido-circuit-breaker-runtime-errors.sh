#!/usr/bin/env bash
# Exact dual-world runtime revert-table schema and live emitted-byte mutants.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT

if [ "$#" -ne 0 ]; then
  echo "REGRESSION — Lido runtime error byte gate: expected no arguments" >&2
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-circuit-breaker-artifacts.lean \
    >"$ARTIFACTS" 2>"$ERRORS"); then
  echo "REGRESSION — Lido runtime error byte gate: artifact evaluation failed" >&2
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/lido_circuit_breaker_runtime_error_schema.py" \
  "$ARTIFACTS" >/dev/null
PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/test-lido-circuit-breaker-runtime-error-falsifiers.py" \
  "$ARTIFACTS" >/dev/null

echo "OK — Lido runtime error byte gate: 2 worlds; 23 instruction-aligned entries; 10 compact errors; 3 preserved helpers; 17 falsifiers"
