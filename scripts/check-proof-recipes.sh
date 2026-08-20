#!/usr/bin/env bash
# Report-only changed-declaration recipe detector. Registry/generated-surface,
# parser, Git-diff, and exception-integrity failures remain blocking.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — proof-recipe gate: python3 not found on PATH" >&2
  exit 2
fi

exec python3 "$SCRIPT_DIR/check-proof-recipes.py" "$@"
