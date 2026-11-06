#!/usr/bin/env bash
# Fail-closed ownership audit for the ExecutionSettlement extraction.
#
# The Python checker reads the lift manifest (schema 4) and the relocation
# manifest: 14 common declarations present in Jaune with their manifest kinds,
# no exact historical donor declaration in the all-Blanc corpus (a declaration
# scan does not prove absence of every alias/export-created name),
# Blanc/ExecutionSettlement.lean directly importing Jaune.ExecSettlement, and
# 197 relocated declarations owned by Jaune only.  Product-specific
# WETH10/Lido shadow, alias/export and trace-abbreviation checks are retired.
#
# `--self-test` runs the eight negative controls instead of the audit alone.
# They mutate a disposable fixture tree and show that each audited channel
# bites, restoring exact seed bytes after each; under the evidence economy
# (scripts/GATES.md) they rerun when the harness changes, not on every Lean
# edit. This wrapper never writes the working tree.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ "${1:-}" = "--self-test" ]; then
  shift
  exec python3 "$SCRIPT_DIR/check-extraction-ownership.py" --negative-controls "$@"
fi
exec python3 "$SCRIPT_DIR/check-extraction-ownership.py" "$@"
