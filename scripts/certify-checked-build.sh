#!/usr/bin/env bash
# Procedural composition of GATES.md's adjacent integrity/certification commands.
# Prerequisite: the exact authoritative build and jaune/jaune completed through
# the owned build capability. This wrapper neither builds nor repairs artifacts.
# The final certificate writer refuses unless every covered module's Lake trace
# is current for its source (scripts/GATES.md, Lake source currency), so a
# certification attempted without that build fails there, naming the module.
set -euo pipefail

if [ "$#" -ne 0 ]; then
  echo 'usage: scripts/certify-checked-build.sh' >&2
  exit 2
fi
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

# Preserve the contained broker's active cache. Do not silently select a second
# cache or accept the underlying checker's vacuous success for an empty cache.
case "${LAKE_CACHE_DIR-}" in
  /*) ;;
  *) echo 'REGRESSION — build certification: an absolute LAKE_CACHE_DIR is required' >&2; exit 2 ;;
esac
if [ ! -d "$LAKE_CACHE_DIR/artifacts" ]; then
  echo 'REGRESSION — build certification: active cache artifacts directory is absent' >&2
  exit 2
fi
shopt -s nullglob dotglob
artifacts=("$LAKE_CACHE_DIR/artifacts/"*)
if [ "${#artifacts[@]}" -eq 0 ]; then
  echo 'REGRESSION — build certification: active cache artifacts directory is empty' >&2
  exit 2
fi
for artifact in "${artifacts[@]}"; do
  if [ ! -f "$artifact" ] || [ -L "$artifact" ]; then
    echo 'REGRESSION — build certification: active cache contains a non-regular artifact' >&2
    exit 2
  fi
done
echo "build certification: ${#artifacts[@]} cache artifact entries present (not yet hash-verified)"

# Host admission, as check-claims.sh takes it: the integrity checker and the
# certificate writer's source-currency helper (about 2 GiB, which loads the Lake
# workspace) both run under this one hold.  The writer's own admission request
# is answered ALREADY_HELD for this label and proceeds under it (the
# semaphore's nested mode), so nothing waits behind this hold.  No `exec`: the
# EXIT trap must outlive the writer to release the hold.
. scripts/gate-semaphore.sh
trap gate_semaphore_release EXIT
gate_semaphore_acquire "build certification" 3 || exit 2

bash scripts/check-lake-artifact-cache.sh
bash scripts/check-gates.sh --certify-build
