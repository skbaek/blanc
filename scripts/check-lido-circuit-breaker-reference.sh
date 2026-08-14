#!/usr/bin/env bash
set -eu
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PYTHONDONTWRITEBYTECODE=1
python3 "$ROOT/scripts/lido_circuit_breaker_reference_schema.py" >/dev/null
python3 "$ROOT/scripts/lido-circuit-breaker-reference.py" check >/dev/null
python3 "$ROOT/scripts/test-lido-circuit-breaker-reference-falsifiers.py" >/dev/null
python3 "$ROOT/scripts/lido-circuit-breaker-compatibility.py" check >/dev/null
printf '%s\n' 'OK — Lido CircuitBreaker reference: schema v2; 17 functions, 7 constructor arguments, 15 errors, 6 indexed event families; official + independent artifact worlds; 9 required falsifier categories; compatibility synchronized'
