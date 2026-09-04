#!/usr/bin/env bash
# Pin the Prague differential lane's reference Python environment.
#
# The lane's Git commit pins the specification's own source and nothing else:
# the checkout declares keccak-256, secp256k1 recovery, the BN254/BLS/KZG
# precompiles, RLP encoding and U256 arithmetic as version *ranges*.  This gate
# owns the missing half — the exact semantic closure those ranges resolve to —
# for every differential that executes in that checkout.
set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PYTHONDONTWRITEBYTECODE=1

EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"

# The self-check runs on any interpreter and needs no checkout, so a broken
# validator is reported before an absent environment can mask it.
python3 "$SCRIPT_DIR/gen-eels-prague-closure.py" --self-check

if [ ! -d "$EELS_ROOT" ]; then
  echo "REGRESSION — prague closure pin: pinned EELS checkout absent at $EELS_ROOT" >&2
  exit 1
fi

python3 "$SCRIPT_DIR/gen-eels-prague-closure.py" --check --eels-root "$EELS_ROOT"
