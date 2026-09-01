#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check-lido-circuit-breaker-registry.py "$@"
