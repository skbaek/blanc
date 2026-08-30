#!/usr/bin/env bash
# Offline integrity gate for the pinned TriggerableWithdrawalsGateway surface.
set -eu
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PYTHONDONTWRITEBYTECODE=1
python3 "$ROOT/scripts/check-lido-twg-census.py" --self-test >/dev/null
python3 "$ROOT/scripts/check-lido-twg-census.py" >/dev/null
printf '%s\n' 'OK — Lido TWG census: pinned source 1700571; 24 selectors, 6 events, 14 custom errors, 6 role/slot hashes, and exact whenResumed surface verified offline'
