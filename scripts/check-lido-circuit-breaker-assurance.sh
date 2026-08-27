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
# declaration is pinned -- fully qualified, never by last component -- by the
# authority the row's OWN Gate field names; that every Axioms field equals that
# authority's expectation, order-insensitively and in both directions, with an
# empty expectation required to be written `none`; that every named gate exists
# and is catalogued in scripts/GATES.md; and that every load-bearing non-claim
# phrase is still written somewhere. It is anti-vacuous: those counts live in
# the checker's own source, so a row deleted, renamed, reworded out of the
# gate's sight, quietly converted into a gate-owned row, or quietly given a
# second gate to resolve a mis-attributed name against, FAILS rather than
# shrinking a green count. Both escape hatches are counted, in both directions.
#
# Blanc has SEVERAL axiom-expectation authorities, not one. This gate reads
# every one of their pin tables and writes none of them: scripts/check.sh's
# ROWS table over scripts/AxiomCheck.lean (which also backs
# check-lido-circuit-breaker-deployment.sh), and the access, enumeration and
# registry gates' own tables; and the history gate's uniform expectation over
# the public theorems its own probe covers, a population derived from its owner
# modules by the same rule that gate selects by. That coupling is the point --
# when a gate's pin table moves, this gate's answer moves with it. Two
# authorities that pin one name and disagree are reported as a repository
# inconsistency and resolved in neither direction, including when one row names
# both of them.
#
# What it deliberately does not own: it does not elaborate Lean and re-derives
# no axiom set. Its DEFAULT MODE IS STATIC, and its authority over the axiom
# column is exactly that of the gates whose pin tables it reads -- each of which
# verifies its own expectations against Lean by elaborating. This gate makes the
# register faithful to them; it is not evidence that any theorem holds. Nor does
# it judge whether a row's prose is a fair summary, whether Premises are
# complete, or whether a differential channel names a real oracle case -- those
# are review obligations, and mechanising a pretence of them would be the
# vacuity this gate exists to prevent.
#
# In its default mode this gate needs no Lean toolchain, no build and no
# network -- it reads committed files only -- so it is instant, takes no report
# or heavy lock (it writes nothing), and runs identically here and in CI.
#
# Usage: scripts/check-lido-circuit-breaker-assurance.sh [--root DIR] [--probe]
#
# --root overrides the repository root; it exists so a negative control can
# point the gate at a mutated copy of the tree without touching the committed
# one.
#
# --probe is an OPTIONAL NON-DEFAULT mode that closes the axiom loop directly
# rather than transitively: it regenerates a `#print axioms` file from the
# register's own citations and elaborates it with `lake env lean`. It REQUIRES
# the Lean toolchain and a built dependency graph, is not what CI or the cheap
# catalogue row runs, and must not be run beside a measurement that owns the
# host.
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

exec "$PY" "$SCRIPT_DIR/check-lido-circuit-breaker-assurance.py" "$@"
