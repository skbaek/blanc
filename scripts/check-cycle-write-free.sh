#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
. scripts/gate-semaphore.sh
trap gate_semaphore_release EXIT

# WHY THE COORDINATION IS HERE AND NOT IN THE DRIVER
#
# `scripts/check-cycle-write-free.py` is a **frozen predecessor assurance file** of the
# transient-settlement gate, which pins its SHA-256 in
# `scripts/transient-settlement-owner-manifest.json`. Adding even a coordination
# call to it reddens that gate against a baseline nobody has any business moving
# for this reason, so the hold is taken out here instead. Do not "tidy" it into
# the driver.

# `--static-only` reads committed text and asks Lean nothing, so it takes no
# hold; every other mode elaborates. This one bit of the driver's mode logic is
# restated here for that reason, and for no other.
case " $* " in
  *" --static-only "*) ;;
  *) gate_semaphore_acquire "the cycle-write-free fixtures" || exit 2 ;;
esac

# Not `exec`: the EXIT trap that releases the hold has to survive the driver.
python3 scripts/check-cycle-write-free.py "$@"
