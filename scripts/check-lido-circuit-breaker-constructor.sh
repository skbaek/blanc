#!/usr/bin/env bash
# Check the emitted Lido constructor once, then run its live byte mutants.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT

if [ "$#" -ne 0 ]; then
  echo "REGRESSION — Lido constructor byte schema: expected no arguments" >&2
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-circuit-breaker-artifacts.lean \
    >"$ARTIFACTS" 2>"$ERRORS"); then
  echo "REGRESSION — Lido constructor byte schema: artifact evaluation failed" >&2
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/lido_circuit_breaker_constructor_schema.py" "$ARTIFACTS" \
  >/dev/null
PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/test-lido-circuit-breaker-constructor-falsifiers.py" "$ARTIFACTS" \
  >/dev/null

echo "OK — Lido constructor byte gate: prefix=616 runtime=4282 creation=4898 full=5122; 2 copies; 10 pre-copy validations; 12 patches; 9 compact errors; 17 falsifiers"
