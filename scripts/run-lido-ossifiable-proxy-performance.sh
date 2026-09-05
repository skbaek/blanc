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
export PYTHONPYCACHEPREFIX=/dev/null
# Retain the frozen campaign's environment identity. Isolated mode ignores it;
# the bootstrap derives the executable source root from the clean checkout.
export PYTHONPATH=$EELS/src
exec "$PYTHON" -I -s -B -X pycache_prefix=/dev/null "$ROOT/scripts/run-isolated-python.py" "$EELS" "run-lido-ossifiable-proxy-performance.py" \
  --repo-root "$ROOT" --eels-root "$EELS" "$@"
