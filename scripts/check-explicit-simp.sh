#!/usr/bin/env bash
# Text control for the explicit-simplification discipline. Reads only sources;
# the migration's native parser/replay evidence establishes syntax coverage.
# Optional scanner arguments support disposable controls; catalogue runs use
# no arguments and therefore inspect Blanc.lean, every Blanc/**/*.lean, and every
# other Git-tracked *.lean outside .lake except explicit_simp.EXEMPT_FIXTURES.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if python3 -B "$SCRIPT_DIR/explicit_simp.py" check "$@"; then
  printf 'OK — explicit-simp: no implicit simplification calls, Aesop normalization, or simp registrations\n'
else
  verdict=$?
  printf 'REGRESSION — explicit-simp: source inventory refused or found a forbidden call/registration\n' >&2
  exit "$verdict"
fi
