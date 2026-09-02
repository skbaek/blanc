#!/usr/bin/env bash
# Recompute Lake's artifact hash instead of trusting cache names or `.hash` sidecars.
#
# Run this after an artifact-cache restore and immediately before minting a
# Blanc build certificate. The accepted residual is collision resistance of
# Lake's 64-bit non-cryptographic Hash; the trust boundary is documented in
# scripts/GATES.md.

set -euo pipefail

if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-lake-artifact-cache.sh" >&2
  exit 2
fi

printenv_path="$(command -v printenv)"
cache_dir="$(lake env "$printenv_path" LAKE_CACHE_DIR)"
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
if [ -z "$cache_dir" ]; then
  echo "REGRESSION — Lake artifact cache: LAKE_CACHE_DIR is unavailable" >&2
  exit 2
fi

if lake env lean --run "$script_dir/check-lake-artifact-cache.lean" "$cache_dir" "$PWD/.lake"; then
  :
else
  status=$?
  echo "REGRESSION — Lake artifact cache: artifact bytes do not match their recorded Lake hash" >&2
  exit "$status"
fi
