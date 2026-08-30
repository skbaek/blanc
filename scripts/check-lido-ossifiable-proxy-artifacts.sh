#!/usr/bin/env bash
# Check the generated OssifiableProxy artifact owners without Lean or network access.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ "$#" -ne 0 ]; then
  echo "REGRESSION — Blanc OssifiableProxy artifact gate: expected no arguments" >&2
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 python3 \
    "$SCRIPT_DIR/lido-ossifiable-proxy-artifacts.py" check >/dev/null; then
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 python3 \
    "$SCRIPT_DIR/test-lido-ossifiable-proxy-artifact-falsifiers.py" >/dev/null; then
  exit 1
fi

echo "OK — Blanc OssifiableProxy artifact gate: 3 pinned artifact identities; 2 evaluator rows; 20 static temp-copy falsifiers; network-free"
