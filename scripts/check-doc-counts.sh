#!/usr/bin/env bash
# Documentation-count gate for Blanc: every published number is produced, not
# transcribed.
#
# The audited-theorem count and statement-pin count are computed from their
# source inventories and then checked wherever this repository publishes them.
# Prose does not recompute itself, so these counts drift silently as the
# inventories grow.
#
# This gate computes the count from scripts/AxiomCheck.lean, finds every place a
# public surface quotes it, and fails on disagreement. It is anti-vacuous: it
# knows how many quotations to expect per file and FAILS if a rewording hides
# one, so a green run never means "nothing was checked".
#
# It owns only this repository's tree. Jaune's site quotes the same number and
# no gate can see across the boundary, so a passing run prints the
# cross-repository reminder instead of pretending that surface does not exist.
#
# This gate needs no Lean toolchain, no build and no network -- it reads
# committed files only -- so it is instant, takes no report or heavy lock (it
# writes nothing), and runs identically here and in CI.
#
# Usage: scripts/check-doc-counts.sh [--root DIR]
#
# --root overrides the repository root; it exists so a negative control can
# point the gate at a mutated copy of the tree without touching the committed
# one.
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — doc-counts: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-doc-counts.py" "$@"
