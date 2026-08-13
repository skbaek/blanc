#!/usr/bin/env bash
# Fail-closed ownership audit for the ExecutionSettlement extraction.
#
# The Python checker reads the sole lift manifest, checks common declarations,
# donor erasure, and Weth10HolderFlow's direct import.  Its built-in controls
# mutate temporary copies only; this wrapper never writes the working tree.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/check-extraction-ownership.py" --negative-controls "$@"
