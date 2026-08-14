#!/usr/bin/env bash
# Reproduce/check the frozen Lido byte/opcode/resource ownership ledger.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BASELINE_COMMIT="fc3edee6dbfb77eaf344afee43c921d48ff8a3af"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
BASELINE_MANIFEST="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS" "$BASELINE_MANIFEST"' EXIT

MODE="--check"
if [ "$#" -gt 1 ]; then
  echo "REGRESSION — Lido artifact profile: expected at most one mode argument"
  exit 1
fi
if [ "$#" -eq 1 ]; then
  case "$1" in
    --check|--write-baseline|--print-current) MODE="$1" ;;
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

if [ "$MODE" = "--write-baseline" ]; then
  if ! git -C "$ROOT" show "$BASELINE_COMMIT:scripts/fixtures/lido-circuit-breaker/manifest.json" >"$BASELINE_MANIFEST"; then
    echo "REGRESSION — Lido artifact profile: frozen baseline manifest commit is unavailable"
    exit 1
  fi
fi

if [ "$MODE" = "--write-baseline" ]; then
  if ! PYTHONDONTWRITEBYTECODE=1 python3 "$SCRIPT_DIR/profile-lido-circuit-breaker-artifacts.py" \
    --blanc-artifacts "$ARTIFACTS" --baseline-manifest "$BASELINE_MANIFEST" "$MODE"; then
    exit 1
  fi
else
  if ! PYTHONDONTWRITEBYTECODE=1 python3 "$SCRIPT_DIR/profile-lido-circuit-breaker-artifacts.py" \
    --blanc-artifacts "$ARTIFACTS" "$MODE"; then
    exit 1
  fi
fi

if [ "$MODE" != "--print-current" ]; then
  PYTHONDONTWRITEBYTECODE=1 python3 \
    "$SCRIPT_DIR/test-lido-circuit-breaker-artifact-profile-falsifiers.py"
fi
