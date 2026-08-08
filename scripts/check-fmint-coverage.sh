#!/usr/bin/env bash
# Selector coverage gate for Blanc's fmint fixture suite (fmint-code Step 2,
# ~/plans/fmint-code.md), the sibling of check-weth-coverage.sh. fmint's
# twelve selectors are obtained from scripts/fmint-selectors.json --
# committed, emitted from Blanc.Fmint.fmintFuncs by
# scripts/gen-fmint-selectors.lean, never retyped here. This gate decodes
# every committed fixture's transactions, reports direct entries separately
# from internal CALLs proven by a changed post-state recorder slot, and labels
# mere selector-shaped PUSHes as uncredited embedding. It fails if the
# unreached set exceeds scripts/fmint-coverage-budget.txt.
#
# This gate needs no Lean toolchain and no frozen oracle at runtime -- it
# reads only the already-committed JSON fixtures and selector/budget files,
# with a self-contained RLP decoder -- so it runs identically here and in CI.
#
# Usage: scripts/check-fmint-coverage.sh [--fixtures-dir DIR]
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line, after a per-selector evidence-class
# breakdown.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — fmint coverage: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-fmint-coverage.py" "$@"
