#!/usr/bin/env bash
# Focused producer tests plus compiler-bound generated-output freshness.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PYTHONDONTWRITEBYTECODE=1 python3 "$SCRIPT_DIR/test-stack-certificate.py"
PYTHONDONTWRITEBYTECODE=1 python3 "$SCRIPT_DIR/gen-proxy-pair-stack-certificate.py"
echo "OK — stack-certificate producer: 6 pure controls; actual compiler bytes; generated output current"
