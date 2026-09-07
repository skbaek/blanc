#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
. scripts/gate-semaphore.sh
trap gate_semaphore_release EXIT

# WHY THE COORDINATION IS HERE AND NOT IN THE DRIVER
#
# `scripts/check-execution-settlement.py` is a **frozen predecessor assurance file** of the
# transient-settlement gate, which pins its SHA-256 in
# `scripts/transient-settlement-owner-manifest.json`. Adding even a coordination
# call to it reddens that gate against a baseline nobody has any business moving
# for this reason, so the hold is taken out here instead. Do not "tidy" it into
# the driver.

gate_semaphore_acquire "the execution settlement fixtures" || exit 2

# Not `exec`: the EXIT trap that releases the hold has to survive the driver.
python3 scripts/check-execution-settlement.py
