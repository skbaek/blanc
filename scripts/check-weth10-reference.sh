#!/usr/bin/env bash
# Network-free integrity gate for the generated deployed-WETH10 reference lock.
set -eu
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
python3 "$ROOT/scripts/weth10-reference.py" check
