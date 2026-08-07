#!/usr/bin/env bash
# Network-free cross-derivation gate for Blanc.errorData.
#
# Usage: scripts/check-error-data.sh
#
# The Python helper enumerates the frozen lock's sourceBehavior guard reasons,
# asks Lean to evaluate the landed definition, and independently rebuilds each
# ABI Error(string) payload using weth10-reference.py's Keccak implementation.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — error data: python3 not found on PATH" >&2
  exit 2
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "REGRESSION — error data: lake not found on PATH" >&2
  exit 2
fi

exec python3 "$SCRIPT_DIR/check-error-data.py"
