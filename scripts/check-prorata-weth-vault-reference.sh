#!/usr/bin/env bash
# Reference-closure identity gate for the PRORATA WETH vault.
#
# Verifies offline that the vendored OpenZeppelin v5.7.0 closure under
# scripts/reference/prorata-weth-vault/inputs/ is exactly the closure frozen at
# G1 (per-file SHA-256 and Git blob), that the committed standard-JSON compiler
# input is built from those bytes under the frozen settings, that the committed
# compiler output carries the frozen creation/runtime template identities, and
# that the reference's ABI surface is the vault's own 25 selectors (no permit,
# no ERC-165, on either side).
#
# The lock is scripts/prorata-weth-vault-reference.json. Regenerate it only
# through `python3 scripts/check-prorata-weth-vault-reference.py --write-lock`
# after a reviewed change to the frozen closure; the ordinary gate never writes.
#
# Needs no Lean toolchain, no build, no network and no compiler. `--recompile`
# additionally runs the solc 0.8.36 binary named by $SOLC (refused unless its
# SHA-256 is the recorded native identity) and requires it to reproduce the
# frozen artifacts. `--self-test` corrupts the inputs one at a time in a
# temporary copy and requires the gate to notice every time.
#
# Usage: scripts/check-prorata-weth-vault-reference.sh [--recompile] [--self-test]
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — PRORATA WETH vault reference: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-prorata-weth-vault-reference.py" "$@"
