#!/usr/bin/env bash
# Blocking, shrink-only whole-tree proof-residue ratchet.
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — proof residue: python3 not found on PATH"; exit 2
fi
exec python3 "$SCRIPT_DIR/check-proof-residue.py" "$@"
