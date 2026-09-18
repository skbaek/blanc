#!/usr/bin/env bash
# Independent exact-integer oracle gate for the PRORATA WETH vault.
#
# The oracle in scripts/prorata_weth_vault_oracle.py is written from the frozen
# statement (~/plans/reports/prorata-erc4626-port-sf.md §4) rather than from the
# Lean development, so that it can disagree with the proofs if either side is
# wrong. This gate checks the properties the statement asserts about its own
# formulas -- the representability identity, both capacity bounds' tightness,
# the four rounding directions, round-trip non-profitability, ledger
# conservation over randomized transcripts, and donation classification.
#
# It also runs the offset-disabled control: the same first-depositor inflation
# transcript against a self-contained unoffset ERC-4626 reference must either
# profit the attacker or mint the victim nothing. A control that does not bite
# fails the gate, so this cannot pass vacuously.
#
# Finite evidence, never a theorem: nothing checked here is reflected into Lean.
#
# This gate needs no Lean toolchain, no build and no network, so it is instant,
# takes no report or heavy lock, and runs identically here and in CI.
#
# Usage: scripts/check-prorata-weth-vault-oracle.sh
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — vault oracle: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-prorata-weth-vault-oracle.py" "$@"
