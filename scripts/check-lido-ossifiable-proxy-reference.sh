#!/usr/bin/env bash
# Network-free focused closure for the Lido OssifiableProxy reference/census.
set -eu

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PYTHONDONTWRITEBYTECODE=1

python3 "$ROOT/scripts/lido_ossifiable_proxy_reference_schema.py" >/dev/null
python3 "$ROOT/scripts/lido-ossifiable-proxy-reference.py" check >/dev/null
python3 "$ROOT/scripts/test-lido-ossifiable-proxy-reference-falsifiers.py" >/dev/null
python3 "$ROOT/scripts/lido-ossifiable-proxy-compatibility.py" check >/dev/null

printf '%s\n' 'OK — Lido OssifiableProxy reference: exact 7-source membership; vendored solc 0.8.9 byte-for-byte recompilation; nonpayable constructor + 7 value-rejecting named endpoints + payable fallback/receive; 3 reachable events (4 raw ABI declarations); 2 custom errors; exact ERC-1967 slots; dual archival RPC closure; 35 falsifier cases; compatibility synchronized'
