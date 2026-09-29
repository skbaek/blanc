#!/usr/bin/env bash
# End-to-end assurance-register gate for Blanc's Lido CircuitBreaker port:
# every claim the register makes is still true of the tree it describes.
#
# `LIDO_CIRCUIT_BREAKER_ASSURANCE.md` maps each assurance claim onto the exact
# declarations carrying it, their premises, their axiom dependencies, the gate
# that owns the evidence, the corroborating differential channel, and what the
# row does NOT claim. Prose does not re-derive itself, so that map drifts
# silently the moment a declaration is renamed, an axiom pin moves, a gate is
# retired, or a non-claim is edited away -- and a drifted register is worse than
# none, because it is read as authority.
#
# This gate checks five things, all fail-closed: the seven-field row structure
# with pinned per-pillar, total and gate-owned row counts; that every cited
# declaration still resolves -- fully qualified, never by last component -- to a
# public declaration in Blanc's sources; that every Axioms field is the standard
# triple the repository's ONE union axiom walk bounds every Blanc constant by,
# or, for a declaration scripts/AxiomCheck.lean explicitly claims a smaller set
# for, exactly that claim (an empty claim written `none`), with every such claim
# in turn stated by a row here or frozen by the deployment gate; that every
# named gate exists and is catalogued in scripts/GATES.md; and that every
# load-bearing non-claim phrase is still written somewhere. It is anti-vacuous:
# the counts live in the checker's own source, so a row deleted, renamed,
# reworded out of the gate's sight, or quietly converted into a gate-owned row
# FAILS rather than shrinking a green count. Every run also executes the
# in-memory mutation controls (a misspelled and an unqualified declaration, a
# wrong axiom field, a stricter claim moved away from the register, a stricter
# claim nothing states), each of which must be rejected.
#
# What it deliberately does not own: it does not elaborate Lean and re-derives
# no axiom set. Its authority over the axiom column is scripts/AxiomCheck.lean,
# which scripts/check.sh verifies against Lean by elaborating; this gate makes
# the register faithful to it and is not evidence that any theorem holds. Nor
# does it judge whether a row's prose is a fair summary, whether Premises are
# complete, or whether a differential channel names a real oracle case -- those
# are review obligations, and mechanising a pretence of them would be the
# vacuity this gate exists to prevent.
#
# It needs no Lean toolchain, no build and no network -- it reads committed
# files only -- so it is instant, takes no report or heavy lock (it writes
# nothing), and runs identically here and in CI.
#
# Usage: scripts/check-lido-circuit-breaker-assurance.sh [--root DIR]
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
  echo "REGRESSION — lido-circuit-breaker-assurance: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-lido-circuit-breaker-assurance.py" --self-test "$@"
