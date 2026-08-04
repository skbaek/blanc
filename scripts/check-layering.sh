#!/usr/bin/env bash
# Import-hierarchy gate for Blanc: contracts must stay siblings.
#
# Enforces README.md's "Module hierarchy: contracts are siblings" -- every
# contract's program, compiled-bytes and property modules sit at the same level
# of the import hierarchy, and no contract's module imports another contract's.
# It also fails on an unclassified module, so a new contract cannot escape the
# rule by never being listed, and on a shared module importing a contract,
# which breaks the hierarchy the other way.
#
# The module classification is hardcoded in check-layering.py; adding a
# contract means adding a line there.
#
# This gate needs no Lean toolchain, no build and no network -- it reads
# committed .lean files only -- so it is instant, takes no report or heavy lock
# (it writes nothing), and runs identically here and in CI.
#
# Usage: scripts/check-layering.sh [--root DIR]
#
# --root overrides the repository root; it exists so a negative control can
# point the gate at a mutated copy of the tree without touching the committed
# one (see the gate's own negative controls).
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — layering: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-layering.py" "$@"
