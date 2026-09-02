#!/usr/bin/env bash
# Focused G3 exact-WETH boundary gate for the PRORATA ERC-4626 vault.
#
# Default mode is static and does not run `lake build`. The caller must first
# establish a current `Blanc.Composition.ProrataWethVaultStaging` artifact
# through Creme's single-owner build wrapper. `--falsify` additionally runs an
# isolated Lean mutation campaign and therefore requires the catalogue's
# exclusive-host precondition.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--falsify" ]; }; then
  echo "usage: scripts/check-prorata-weth-vault-boundary.sh [--falsify]" >&2
  exit 2
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/check-prorata-weth-vault-boundary.py" "$@"
