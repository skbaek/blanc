#!/usr/bin/env bash
# Blocking, shrink-only K1 duplication ratchet over the whole production tree.
#
# Separate from check-proof-recipes.sh on purpose: that gate is diff-scoped and
# report-only for its source findings, this one is whole-tree and blocks, so
# folding them together would make an exit code ambiguous about which part
# failed. Both modes live in the same Python file because they share one
# parser, one normalization and one substantive-declaration floor.
#
# CLI contract: exit 0 iff the gate passes; output ends with one unambiguous
# verdict line. --write-baseline is an explicit shrink-only evidence refresh,
# never an ordinary gate mode.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — proof duplication ratchet: python3 not found on PATH" >&2
  exit 2
fi

exec python3 "$SCRIPT_DIR/check-proof-recipes.py" --duplication "$@"
