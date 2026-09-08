#!/usr/bin/env bash
# Data/proof-text provenance and deterministic corruption controls. Lean
# semantic certification is supplied by separately required production builds.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
python3 -B scripts/test-stack-certificate.py
python3 -B scripts/gen-drip-stack-certificate.py
python3 -B scripts/test-drip-stack-certificate.py
echo "OK — DRIP stack certificate data: reusable producer controls, exact runtime-derived data/proof text and deterministic corruption controls passed"
