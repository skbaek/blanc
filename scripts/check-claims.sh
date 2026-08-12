#!/usr/bin/env bash
# Lean-checked exact statement pins for the WETH10 flagship set.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if ! (cd "$ROOT" && lake env lean scripts/ClaimCheck.lean); then
  echo "REGRESSION — WETH10 claim statements: a pinned statement changed"
  exit 1
fi

echo "OK — WETH10 claim statements: 165 definitions/statements and exact record constructors pinned by Lean"
