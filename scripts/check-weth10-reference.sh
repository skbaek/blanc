#!/usr/bin/env bash
# Network-free integrity gate for the generated deployed-WETH10 reference lock.
set -eu
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
python3 "$ROOT/scripts/weth10_reference_schema.py"
python3 "$ROOT/scripts/weth10-reference.py" check >/dev/null
python3 "$ROOT/scripts/weth10-reference.py" check-drift >/dev/null
python3 "$ROOT/scripts/test-weth10-reference-falsifiers.py" >/dev/null
python3 "$ROOT/scripts/weth10-compatibility.py" check >/dev/null
echo "OK — WETH10 reference: schema v2, 27 selectors + receive, 9975 runtime bytes, 23 falsifier families, 28 compatibility endpoint keys + 12 cross-cutting keys + deployment, offline inputs verified"
