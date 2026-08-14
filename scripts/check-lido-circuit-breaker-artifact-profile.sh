#!/usr/bin/env bash
# Check the immutable launch ledger and generated optimized ownership ledger.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT

MODE="--check"
if [ "$#" -gt 1 ]; then
  echo "REGRESSION — Lido artifact profile: expected at most one mode argument"
  exit 1
fi
if [ "$#" -eq 1 ]; then
  case "$1" in
    --check|--write-optimized|--print-current) MODE="$1" ;;
    *)
      echo "REGRESSION — Lido artifact profile: unknown mode $1"
      exit 1
      ;;
  esac
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-circuit-breaker-artifacts.lean >"$ARTIFACTS" 2>"$ERRORS"); then
  echo "REGRESSION — Lido artifact profile: Blanc artifact evaluation failed"
  exit 1
fi

if [ "$MODE" = "--print-current" ]; then
  PYTHONDONTWRITEBYTECODE=1 python3 \
    "$SCRIPT_DIR/profile-lido-circuit-breaker-artifacts.py" \
    --blanc-artifacts "$ARTIFACTS" "$MODE"
  exit $?
fi

if ! PYTHONDONTWRITEBYTECODE=1 python3 \
    "$SCRIPT_DIR/profile-lido-circuit-breaker-artifacts.py" \
    --blanc-artifacts "$ARTIFACTS" "$MODE" >/dev/null; then
  exit 1
fi
if ! PYTHONDONTWRITEBYTECODE=1 python3 \
    "$SCRIPT_DIR/test-lido-circuit-breaker-artifact-profile-falsifiers.py" \
    >/dev/null; then
  exit 1
fi

echo "OK — Lido artifact profiles: frozen launch and optimized/current ledgers; 10 exact artifacts; 667 partition regions; 24 falsifiers; baseline and attribution digests pinned"
