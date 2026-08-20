#!/usr/bin/env bash
# Report-only proof-module growth ratchet. Threshold evidence: README.md:417-425.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — proof module size: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-proof-module-size.py" "$@"
