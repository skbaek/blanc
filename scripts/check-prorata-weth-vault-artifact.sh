#!/usr/bin/env bash
# Focused G2 identity/surface gate for the PRORATA WETH ERC-4626 vault.
#
# This gate is deliberately static and does not run `lake build`. The caller
# must first establish a current `Blanc.ProrataWethVaultArtifact` artifact
# through Creme's single-owner build wrapper; stale Lean evidence is therefore
# a failed prerequisite, not compilation work hidden inside this gate.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-prorata-weth-vault-artifact.sh" >&2
  exit 2
fi

PYTHONDONTWRITEBYTECODE=1 python3 \
  "$SCRIPT_DIR/check-prorata-weth-vault-artifact.py"
