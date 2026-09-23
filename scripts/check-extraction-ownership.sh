#!/usr/bin/env bash
# Fail-closed ownership audit for the ExecutionSettlement extraction.
#
# The Python checker reads the sole lift manifest, checks common declarations,
# donor erasure, the exact retained-trace compatibility abbreviations, and
# Weth10HolderFlow's direct import.  A contract module consumes common
# declarations and never re-provides them, so no alias or export is approved.
#
# `--self-test` runs the nine negative controls instead of the audit alone.
# They mutate temporary copies of Blanc/ and the manifest only and show that
# each audited channel bites; under the evidence economy (scripts/GATES.md)
# they rerun when the harness changes, not on every Lean edit. This wrapper
# never writes the working tree.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ "${1:-}" = "--self-test" ]; then
  shift
  exec python3 "$SCRIPT_DIR/check-extraction-ownership.py" --negative-controls "$@"
fi
exec python3 "$SCRIPT_DIR/check-extraction-ownership.py" "$@"
