#!/usr/bin/env bash
# Focused G3 exact-WETH boundary gate for the PRORATA ERC-4626 vault.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--falsify" ]; }; then
  echo "usage: scripts/check-prorata-weth-vault-boundary.sh [--falsify]" >&2
  exit 2
fi

if ! (cd "$ROOT" && lake build Blanc.Composition.ProrataWethVaultStaging); then
  echo "REGRESSION — PRORATA WETH vault boundary: focused Lean build failed" >&2
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/check-prorata-weth-vault-boundary.py" "$@"
