#!/usr/bin/env bash
# Differential gate: the compiled PRORATA WETH vault against the independent
# oracle.
#
# Executes the committed 17481-byte vault runtime on Jaune's EVM through
# `jaune t8n --state-test` and compares the resulting vault and WETH storage,
# and the acceptance or rejection of the call, against
# scripts/prorata_weth_vault_oracle.py -- which is written from the frozen
# statement rather than from the Lean development. Neither side is derived from
# the other, so agreement is evidence and disagreement is a real defect in one.
#
# This is the half of G8 that the property batteries and golden vectors cannot
# supply: those check the model against the statement, this checks the artifact
# against the model.
#
# Every case is chosen so its divisions are inexact -- floor and ceil differ --
# because a case that divides evenly cannot observe a rounding direction. The
# gate was mutation-tested against five perturbations of the oracle (the offset
# and each of the four rounding directions) and catches all five.
#
# Needs the Jaune fixture runner built; exits 2 if it is absent, rather than
# passing vacuously.
#
# Finite evidence, never a theorem.
#
# Usage: scripts/check-prorata-weth-vault-differential.sh
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — vault differential: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-prorata-weth-vault-differential.py" "$@"
