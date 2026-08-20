#!/usr/bin/env bash
# Report-only proof-resource debt gate. Structural/parser/baseline failures are
# still regressions; only unexcepted new or increased debt is report-only.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — proof-debt: python3 not found on PATH" >&2
  exit 2
fi

exec python3 "$SCRIPT_DIR/check-proof-debt.py" "$@"
