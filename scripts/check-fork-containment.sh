#!/usr/bin/env bash
# Named-fork containment gate for Blanc: a generic module names no fork.
#
# Blanc's proof surface is stated over an arbitrary valid `ChainConfig`, with
# Ethereum mainnet's configured schedule published as a specialization and
# Prague retained as an audited corollary. That property is easy to state and
# easy to lose: one `pragueRules` dropped into a generic statement re-fixes the
# fork for every consumer downstream of it, and review is exactly the wrong
# instrument for catching it.
#
# This gate reads the committed `Blanc/` tree and enforces two independent
# static properties: every named-fork literal sits in a module or declaration
# that says, in this gate's own source, why naming a fork is its job; and every
# `_mainnet` specialization has its matching `_prague` corollary and vice
# versa. Both allowances carry exact counts, so a new literal inside an already
# allowed module still fails, and an allowance matching nothing fails as an
# orphan.
#
# The allowlist is a control, not a convenience. Adding a generic module to it
# to obtain green is a weakening of exactly the property the gate exists to
# keep. Every allowance opens with a category from a closed vocabulary --
# `specialization` or `compatibility` for a whole module, plus `bridge` and
# `debt` for a single declaration -- and an entry filed under any other word
# fails before the tree is read, so a third category cannot be introduced by
# prose alone.
#
# The gate catches fork *naming*, not fork *dependence*. Its population is a
# vocabulary of identifiers, so a generic module that hard-codes a
# fork-sensitive value -- `def a : Nat := 24576` -- passes, while
# `def a : Nat := pragueCodeLimits.maxCodeSize` is caught. The checker's own
# docstring records why blocklisting the value is not the fix and names the two
# live debts this blind spot leaves to review.
#
# This gate needs no Lean toolchain, no build and no network -- it reads
# committed files only -- so it is instant, takes no report or heavy lock (it
# writes nothing), and runs identically here and in CI.
#
# Usage: scripts/check-fork-containment.sh [--root DIR] [--census] [--self-test]
#
# --root overrides the repository root; it exists so a negative control can
# point the gate at a mutated copy of the tree without touching the committed
# one. --census prints what the gate sees, for authoring an allowance.
# --self-test runs the fail-closed control suite in disposable copies.
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — fork-containment: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-fork-containment.py" "$@"
