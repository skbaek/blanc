#!/bin/sh
set -eu

ROOT=${LIDO_OSSIFIABLE_PROXY_PERFORMANCE_ROOT:-$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)}
EELS=${EELS_ROOT:-$HOME/execution-specs}
PYTHON=$EELS/venv/bin/python

if [ ! -x "$PYTHON" ]; then
  echo "REGRESSION — pinned EELS interpreter is missing: $PYTHON" >&2
  exit 1
fi

export EELS_ROOT=$EELS
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPATH=$EELS/src
exec "$PYTHON" -B "$ROOT/scripts/run-lido-ossifiable-proxy-performance.py" \
  --repo-root "$ROOT" --eels-root "$EELS" "$@"
