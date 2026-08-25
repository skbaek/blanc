#!/usr/bin/env bash
# Blocking proof-resource debt gate. Every unexcepted new or increased ceiling
# is a regression; reviewed permanent admissions use the Python writer's exact
# stable-ID path, while temporary exceptions remain bounded and expiring.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v python3 >/dev/null 2>&1; then
  echo "REGRESSION — proof-debt: python3 not found on PATH" >&2
  exit 2
fi

exec python3 "$SCRIPT_DIR/check-proof-debt.py" "$@"
