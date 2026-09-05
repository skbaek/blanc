#!/usr/bin/env bash
# Offline frozen-corpus Solidity/Blanc OssifiableProxy differential through EELS Prague.

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPYCACHEPREFIX=/dev/null
EVALUATOR="$SCRIPT_DIR/eval-lido-ossifiable-proxy-artifacts.lean"
WORK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lido-ossifiable-proxy-differential.XXXXXX")"
ARTIFACTS="$WORK_DIR/blanc-artifacts.txt"
RESULT="$WORK_DIR/differential-result.json"
trap 'rm -f "$ARTIFACTS" "$RESULT"; rmdir "$WORK_DIR"' EXIT

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — OssifiableProxy differential: pinned EELS python not found at $EELS_PY"
  exit 1
fi
if [ ! -f "$EVALUATOR" ]; then
  echo "REGRESSION — OssifiableProxy differential: Blanc evaluator not found at $EVALUATOR"
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/lido_ossifiable_proxy_differential_schema.py" \
  --repo-root "$REPO_ROOT"
PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/test-lido-ossifiable-proxy-differential-falsifiers.py" \
  --repo-root "$REPO_ROOT"

(cd "$REPO_ROOT" && lake env lean \
  scripts/eval-lido-ossifiable-proxy-artifacts.lean >"$ARTIFACTS")

# The frozen campaign records this environment value. CPython -I ignores it;
# run-isolated-python.py derives and installs the executable source root from
# the clean pinned checkout before any EELS import.
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$EELS_ROOT/src" \
  "$EELS_PY" -I -s -B -X pycache_prefix=/dev/null \
  "$SCRIPT_DIR/run-isolated-python.py" "$EELS_ROOT" "run-lido-ossifiable-proxy-differential.py" \
  --repo-root "$REPO_ROOT" \
  --eels-root "$EELS_ROOT" \
  --blanc-artifacts "$ARTIFACTS" \
  --result-out "$RESULT" >/dev/null
PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/check-lido-ossifiable-proxy-differential.py" \
  --repo-root "$REPO_ROOT" \
  --require-all-matched \
  "$RESULT"
