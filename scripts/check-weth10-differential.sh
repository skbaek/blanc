#!/usr/bin/env bash
# Execute the frozen installed WETH10 and Blanc's concrete compiled runtimes
# through the pinned EELS Prague interpreter, then compare the declared logical
# projection and observable channels.  No network access or fixture rewrite.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPYCACHEPREFIX=/dev/null
RUNTIMES="$(mktemp)"
trap 'rm -f "$RUNTIMES"' EXIT

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — WETH10 differential: pinned EELS python not found at $EELS_PY" >&2
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-weth10-differential-code.lean >"$RUNTIMES"); then
  echo "REGRESSION — WETH10 differential: Blanc runtime evaluation failed" >&2
  exit 1
fi

"$EELS_PY" -I -s -B -X pycache_prefix=/dev/null "$SCRIPT_DIR/run-isolated-python.py" "$EELS_ROOT" "gen-weth10-differential.py" \
  --eels-root "$EELS_ROOT" --blanc-runtimes "$RUNTIMES" "$@"
