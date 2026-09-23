#!/usr/bin/env bash
# Lean-checked statement pins for common execution, WETH10, Lido, PRORATA,
# the PRORATA WETH vault (compiled, capacity, nonrevert, history and attack
# headlines, and the reverting-walk vocabulary they rest on),
# BeaconDeposit, and DRIP.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
. "$SCRIPT_DIR/gate-semaphore.sh"
trap gate_semaphore_release EXIT

gate_semaphore_acquire "the pinned claim statements" || exit 2

if ! (cd "$ROOT" && lake env lean scripts/ClaimCheck.lean); then
  echo "REGRESSION — claim statements: a pinned statement changed"
  exit 1
fi

# Fork-coverage controls (2026-09-23): the four covered forks keep positive
# witnesses, mainnet's schedule discharges the schedule premise, Amsterdam is
# refused, and the covered list is pinned exactly.  Kept out of the audited
# theorem set, so neither published count moves.
if ! (cd "$ROOT" && lake env lean scripts/CoveredForkControls.lean); then
  echo "REGRESSION — claim statements: the fork-coverage controls changed"
  exit 1
fi

claim_count="$(grep -Ec '^[[:space:]]*(example|#check)([[:space:]]|$)' \
  "$ROOT/scripts/ClaimCheck.lean")"
if [[ "$claim_count" -ne 460 ]]; then
  echo "REGRESSION — claim inventory: expected 460 pins, found $claim_count"
  exit 1
fi

echo "OK — claim statements: $claim_count definitions/statements and exact record constructors pinned by Lean"
