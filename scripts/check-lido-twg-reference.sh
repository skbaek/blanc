#!/usr/bin/env bash
# Network-free closure for the TriggerableWithdrawalsGateway reference lock.
set -eu

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PYTHONDONTWRITEBYTECODE=1

python3 "$ROOT/scripts/lido_twg_reference_schema.py" >/dev/null
python3 "$ROOT/scripts/lido-twg-reference.py" check >/dev/null
python3 "$ROOT/scripts/test-lido-twg-reference-falsifiers.py" >/dev/null

printf '%s\n' 'OK — Lido TWG reference: exact 13-source closure; vendored solc 0.8.9 byte-for-byte recompilation; 24 selectors + 5-argument constructor; 6 events; 14 custom errors; 10096-byte creation + 8128-byte runtime in 2 parameter worlds; dual-provider block 25866991 runtime/role/pause snapshot; CircuitBreaker PAUSE_ROLE confirmed; 15 falsifiers'
