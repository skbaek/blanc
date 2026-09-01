#!/usr/bin/env bash
# Lean-checked statement pins for common execution, WETH10, Lido, PRORATA,
# and BeaconDeposit.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if ! (cd "$ROOT" && lake env lean scripts/ClaimCheck.lean); then
  echo "REGRESSION — claim statements: a pinned statement changed"
  exit 1
fi

claim_count="$(grep -Ec '^[[:space:]]*(example|#check)([[:space:]]|$)' \
  "$ROOT/scripts/ClaimCheck.lean")"
if [[ "$claim_count" -ne 304 ]]; then
  echo "REGRESSION — claim inventory: expected 304 pins, found $claim_count"
  exit 1
fi

echo "OK — claim statements: $claim_count definitions/statements and exact record constructors pinned by Lean"
