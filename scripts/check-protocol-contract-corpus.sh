#!/usr/bin/env bash
# Static structure only; the catalogue must require claims + claim-hash first.
# This wrapper builds nothing, writes no pins, and opens no Lean process.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 -B "$SCRIPT_DIR/check-protocol-contract-corpus.py" --self-test "$@"
