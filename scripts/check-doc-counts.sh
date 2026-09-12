#!/usr/bin/env bash
# Published-claim gate for Blanc: every published claim is produced, not
# transcribed.
#
# Blanc publishes numbers, gate transcripts and repository references on public
# surfaces. Prose does not recompute itself, so a published claim drifts
# silently every time its producer moves -- and it did: on 2026-08-12 Jaune's
# site published 315 audited theorems against this gate's 333, and until
# 2026-09-12 the claim-pin count was published four times with nothing reading
# any of them.
#
# For each registered claim this gate computes the value from the one committed
# artifact that owns it, finds every place a public surface states it, and fails
# on disagreement. It also pins the published verbatim transcripts of
# scripts/check-claims.sh against that gate's own verdict format string, and
# PORTING.md's references into this tree. Prose judgment is out of scope: see
# the script's module docstring for what counts as a published claim and why
# scoring prose against the tree is not this gate's job.
#
# It is anti-vacuous twice over: per pattern, so a rewording that hides a
# quotation FAILS rather than passing with nothing checked; and per surface, by
# a census of standalone occurrences of each produced value, so an unregistered
# quotation cannot drift unseen. A green run never means "nothing was checked".
#
# It owns only this repository's tree. Jaune's site quotes the audited-theorem
# count and no gate can see across the boundary, so a passing run prints the
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
