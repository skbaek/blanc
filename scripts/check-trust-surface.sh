#!/usr/bin/env bash
# Transitive source-trust scan for Blanc's imported library closure.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/check-trust-surface.py" "$@"
