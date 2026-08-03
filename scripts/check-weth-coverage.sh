#!/usr/bin/env bash
# Selector coverage gate for Blanc's WETH fixture suite (weth-evidence Step
# 2, ~/plans/weth-evidence.md). Blanc's ten WETH selectors are obtained from
# `scripts/weth-selectors.json` -- committed, emitted from `Blanc.wethFuncs`
# by `scripts/gen-weth-selectors.lean`, never retyped here (Fixed design
# decision 5). This gate decodes every committed fixture's transactions (and
# any caller prop's embedded calldata) and reports each selector as
# exercised or not, failing if the unexercised set exceeds the committed,
# shrink-only budget in `scripts/weth-coverage-budget.txt`.
#
# This gate needs no Lean toolchain and no frozen oracle at runtime -- it
# reads only the already-committed JSON fixtures and selector/budget files,
# with a self-contained RLP decoder -- so it runs identically here and in CI.
#
# Usage: scripts/check-weth-coverage.sh [--fixtures-dir DIR]
#
# --fixtures-dir overrides the fixture directory (default
# scripts/fixtures/weth); it exists so a negative control can point the gate
# at a fixture set missing a case without touching the committed one (see
# the Step 2 report for exactly this run).
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line, after a per-selector exercised/unexercised
# breakdown.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — weth coverage: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-weth-coverage.py" "$@"
