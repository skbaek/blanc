#!/usr/bin/env bash
# Focused G2 identity/surface gate for the PRORATA WETH ERC-4626 vault.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-prorata-weth-vault-artifact.sh" >&2
  exit 2
fi

if ! (cd "$ROOT" && lake build Blanc.ProrataWethVaultArtifact); then
  echo "REGRESSION — PRORATA WETH vault artifact: focused Lean build failed" >&2
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/check-prorata-weth-vault-artifact.py"
