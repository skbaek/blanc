#!/usr/bin/env bash
# Bite controls of the derived leaf audit (`scripts/leaf_audit.py`, run by
# `scripts/check.sh`): a small fixture environment elaborated by the byte-identical
# `scripts/LeafCensus.lean` body must go red when an unused theorem is added
# without a pin, when a used theorem, an attribute-only theorem or a definition is
# pinned, when a pin is dropped, and green again on the compliant fixture. The
# production verdict is `scripts/check.sh`, not this script.
#
# Usage: scripts/check-leaf-audit.sh --self-test

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if [ "$#" -ne 1 ] || [ "$1" != "--self-test" ]; then
  echo "usage: scripts/check-leaf-audit.sh --self-test" >&2
  exit 2
fi

cd "$ROOT" || exit 1
python3 scripts/test-external-uses.py || exit $?
exec python3 scripts/leaf_audit.py self-test
