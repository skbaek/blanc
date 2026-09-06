#!/usr/bin/env bash
# Data provenance and deterministic corruption controls. Lean semantic
# certification is supplied by the required built Blanc.DripStackSafety module.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
python3 -B scripts/gen-drip-stack-certificate.py
python3 -B scripts/test-drip-stack-certificate.py
echo "OK — DRIP stack certificate data: exact runtime-derived output and deterministic corruption controls passed"
