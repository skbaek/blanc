#!/usr/bin/env bash
# Selective full-set gate runner for Blanc.
#
# WHY
#
# `scripts/GATES.md` lists a full ordered set that a checkpoint or merge
# candidate runs.  Until this gate existed, every row of it ran every time and
# a verdict was inherited only by exact commit identity, so correcting a
# sentence in a comment discarded the WETH, Lido, occurrence, settlement and
# fixture evidence produced minutes earlier -- none of whose inputs had moved.
#
# This runner evaluates the same ordered set, executes the rows whose declared
# mutable inputs have moved, and credits the rest from earlier successful
# executions whose fingerprints match exactly.  Reuse is by content, never by
# commit: the commit is provenance, and it is a validity input only for a gate
# that semantically consumes one (`--base main`).
#
# WHAT IT DOES NOT DO
#
# It does not make any gate weaker.  Gate bodies, verdicts, falsifiers,
# baselines and locks are untouched, every gate keeps its own direct command as
# an unambiguous fresh path, and CI keeps invoking those commands in a clean
# environment where no cache exists.  There is deliberately no `--force`:
# `--fresh` adds execution and nothing removes it.
#
# The cache lives under `.lake/`, is ignored by Git, is never hand-seeded, and
# may be deleted at any time.  Deleting it costs time; it cannot cost
# correctness, because a missing, corrupt, incomplete or drifting record causes
# execution rather than a skip.
#
# USE
#
#   scripts/check-gates.sh                # selective full set (the checkpoint)
#   scripts/check-gates.sh --fresh        # execute every row, refresh evidence
#   scripts/check-gates.sh --plan         # what would run, without running it
#   scripts/check-gates.sh --explain      # ... and which inputs moved
#   scripts/check-gates.sh --audit        # registry vs catalogue vs CI
#   scripts/check-gates.sh --self-test    # the fail-closed control suite
#   scripts/check-gates.sh --inventory    # regenerate docs/GATE_INPUTS.md
#
# Evidence is written to `.lake/gate-report.md` and `.lake/gate-manifest.json`.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — check-gates: python3 not found on PATH" >&2
  exit 2
fi

MODE=(run)
ECHO=()

while [ "$#" -gt 0 ]; do
  case "$1" in
    --fresh) MODE=(run --fresh) ;;
    --echo) ECHO=(--echo) ;;
    --plan) MODE=(plan) ;;
    --explain) MODE=(plan --explain) ;;
    --audit) MODE=(audit) ;;
    --self-test) MODE=(self-test) ;;
    --inventory) MODE=(inventory --output docs/GATE_INPUTS.md) ;;
    --force)
      echo "check-gates: there is no --force. Use --fresh, which adds execution." >&2
      exit 2
      ;;
    -h|--help)
      sed -n '2,40p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      echo "check-gates: unknown option $1" >&2
      exit 2
      ;;
  esac
  shift
done

case "${MODE[0]}" in
  run) exec python3 "$SCRIPT_DIR/gate-cache.py" "${MODE[@]}" ${ECHO[@]+"${ECHO[@]}"} ;;
  *) exec python3 "$SCRIPT_DIR/gate-cache.py" "${MODE[@]}" ;;
esac
