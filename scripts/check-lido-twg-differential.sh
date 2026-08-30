#!/usr/bin/env bash
# Offline Solidity/Blanc TriggerableWithdrawalsGateway differential in pinned EELS.
set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
GENERATOR_OUT="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS" "$GENERATOR_OUT"' EXIT

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — Lido TWG differential: pinned EELS python not found at $EELS_PY"
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 "$SCRIPT_DIR/check-lido-twg-reference.sh" >/dev/null
PYTHONDONTWRITEBYTECODE=1 "$SCRIPT_DIR/check-lido-twg-census.sh" >/dev/null

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-twg-artifacts.lean >"$ARTIFACTS" 2>"$ERRORS"); then
  echo "REGRESSION — Lido TWG differential: Blanc artifact evaluation failed"
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$EELS_ROOT/src" "$EELS_PY" \
  "$SCRIPT_DIR/gen-lido-twg-differential.py" \
  --eels-root "$EELS_ROOT" --blanc-artifacts "$ARTIFACTS" "$@" >"$GENERATOR_OUT"; then
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/lido_twg_differential_schema.py" >/dev/null
PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/test-lido-twg-differential-falsifiers.py" >/dev/null
PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/lido-twg-compatibility.py" check >/dev/null

cat "$GENERATOR_OUT"
