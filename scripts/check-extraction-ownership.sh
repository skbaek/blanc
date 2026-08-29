#!/usr/bin/env bash
# Fail-closed ownership audit for the ExecutionSettlement extraction.
#
# The Python checker reads the sole lift manifest, checks common declarations,
# donor erasure, the exact retained-trace compatibility abbreviations, and
# Weth10HolderFlow's direct import.  A contract module consumes common
# declarations and never re-provides them, so no alias or export is approved.
# Its built-in controls mutate temporary copies only; this wrapper never
# writes the working tree.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/check-extraction-ownership.py" --negative-controls "$@"
