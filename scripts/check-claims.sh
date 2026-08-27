#!/usr/bin/env bash
# Lean-checked exact statement pins for common execution, WETH10, and Lido.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if ! (cd "$ROOT" && lake env lean scripts/ClaimCheck.lean); then
  echo "REGRESSION — common/WETH10/Lido claim statements: a pinned statement changed"
  exit 1
fi

claim_count="$(grep -Ec '^[[:space:]]*(example|#check)([[:space:]]|$)' \
  "$ROOT/scripts/ClaimCheck.lean")"
if [[ "$claim_count" -ne 268 ]]; then
  echo "REGRESSION — common/WETH10/Lido claim inventory: expected 268 pins, found $claim_count"
  exit 1
fi

echo "OK — common/WETH10/Lido claim statements: $claim_count definitions/statements and exact record constructors pinned by Lean"
