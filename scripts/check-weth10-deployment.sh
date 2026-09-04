#!/usr/bin/env bash
# Execute Blanc's generic WETH10 initcode in the pinned EELS Prague
# interpreter and compare the deposited code with independently named members
# of the witnessed parameterized runtime family.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPYCACHEPREFIX=/dev/null
JAUNE_BIN="$ROOT/.lake/packages/jaune/.lake/build/bin/jaune"
ARTIFACTS="$(mktemp)"
trap 'rm -f "$ARTIFACTS"' EXIT

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — WETH10 deployment: pinned EELS python not found at $EELS_PY" >&2
  exit 1
fi

if [ ! -x "$JAUNE_BIN" ]; then
  echo "REGRESSION — WETH10 deployment: Jaune runner not found at $JAUNE_BIN" >&2
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-weth10-deployment-code.lean \
    >"$ARTIFACTS" 2>&1); then
  cat "$ARTIFACTS" >&2
  echo "REGRESSION — WETH10 deployment: Blanc artifact evaluation failed" >&2
  exit 1
fi

PYTHONPATH="$EELS_ROOT/src" "$EELS_PY" "$SCRIPT_DIR/check-weth10-deployment.py" \
  --eels-root "$EELS_ROOT" --artifacts "$ARTIFACTS" --jaune-bin "$JAUNE_BIN"
