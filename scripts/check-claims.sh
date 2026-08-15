#!/usr/bin/env bash
# Lean-checked exact statement pins for common execution, WETH10, and Lido.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if ! (cd "$ROOT" && lake env lean scripts/ClaimCheck.lean); then
  echo "REGRESSION — common/WETH10/Lido claim statements: a pinned statement changed"
  exit 1
fi

echo "OK — common/WETH10/Lido claim statements: 235 definitions/statements and exact record constructors pinned by Lean"
