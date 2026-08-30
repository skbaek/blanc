#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=${LIDO_OSSIFIABLE_PROXY_PERFORMANCE_ROOT:-"$SCRIPT_DIR/.."}
MANIFEST=${LIDO_OSSIFIABLE_PROXY_PERFORMANCE_MANIFEST:-"$REPO_ROOT/scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json"}
PYTHON=${PYTHON:-python3}

export PYTHONDONTWRITEBYTECODE=1

"$PYTHON" -B "$SCRIPT_DIR/lido_ossifiable_proxy_performance_schema.py" \
  --root "$REPO_ROOT" \
  --manifest "$MANIFEST"
"$PYTHON" -B "$SCRIPT_DIR/check-lido-ossifiable-proxy-performance.py" \
  --root "$REPO_ROOT" \
  --manifest "$MANIFEST"
"$PYTHON" -B "$SCRIPT_DIR/test-lido-ossifiable-proxy-performance-falsifiers.py" \
  --root "$REPO_ROOT" \
  --manifest "$MANIFEST"

echo "OK — OssifiableProxy performance static gate; no measurements run"
