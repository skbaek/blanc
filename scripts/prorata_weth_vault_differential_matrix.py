#!/usr/bin/env python3
"""Fail-closed schema for the finite PRORATA vault differential matrix.

The JSON beside this module is a *coverage declaration*, not a result oracle:
it names required inputs and channels but contains no expected post-state,
return value, allowed mismatch, or measured value.  This module keeps the
required finite surface in code too, so editing the JSON cannot silently drop
a selector, channel, or case.
"""
from __future__ import annotations

import json
import hashlib
import argparse
from pathlib import Path


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "prorata-weth-vault-differential-manifest.json"

# This is the G1/G2 exact ABI surface, in the artifact gate's source order.
SELECTORS = (
    "totalAssets()", "name()", "convertToAssets(uint256)",
    "approve(address,uint256)", "previewWithdraw(uint256)", "totalSupply()",
    "transferFrom(address,address,uint256)", "decimals()", "asset()",
    "maxDeposit(address)", "previewRedeem(uint256)",
    "deposit(uint256,address)", "balanceOf(address)",
    "mint(uint256,address)", "symbol()", "transfer(address,uint256)",
    "previewMint(uint256)", "withdraw(uint256,address,address)",
    "redeem(uint256,address,address)", "maxMint(address)",
    "convertToShares(uint256)", "maxWithdraw(address)", "maxRedeem(address)",
    "allowance(address,address)", "previewDeposit(uint256)",
)

# Every selected case has an independent oracle assertion.  The two compiled
# sides are always both executed through Jaune.  The EELS leg is intentionally
# represented as a required separate producer rather than an observation of
# Jaune; callers must fail closed if they advertise it without the pinned EELS
# runner.
CASES = (
    "metadata-and-zero-views", "nonempty-and-donated-views",
    "deposit-empty", "deposit-donated", "mint-inexact", "redeem-inexact",
    "withdraw-inexact", "approve-and-transfer", "transfer-from-finite",
    "transfer-from-infinite", "allowance-underflow-rollback",
    "zero-address-rollbacks", "capacity-boundaries", "malformed-dispatch",
    "nonpayable-rollbacks", "event-order", "return-capture-controls",
    "callback-and-attack-rollbacks",
)

CHANNELS = {
    "jaune": "Jaune t8n executes each compiled side against the independent Python oracle.",
    "reference": "The locked OpenZeppelin reference is deployed and identity-checked before the Jaune leg.",
    "eels": "Pinned EELS executes an independent replay; it is never inferred from Jaune output.",
}

SOURCE_INPUTS = (
    "scripts/check-prorata-weth-vault-differential.py",
    "scripts/evm_return_capture.py",
    "scripts/prorata_weth_vault_oracle.py",
)


def source_identity() -> dict[str, str]:
    """Current non-self-referential producer inputs, hashed by content."""
    return {
        path: hashlib.sha256((HERE.parent / path).read_bytes()).hexdigest()
        for path in SOURCE_INPUTS
    }


def manifest_data() -> dict:
    """The sole deterministic coverage declaration producer.

    This carries only producer/source identity and required coverage.  Runtime
    observations stay in the runner and independent oracle; no expected bytes,
    result allowlist, deviation entry, or measurement belongs here.
    """
    return {
        "schema": 1,
        "kind": "coverage-declaration",
        "producer": {"path": "scripts/prorata_weth_vault_differential_matrix.py", "schema": 1},
        "producerSha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sourceIdentity": {"algorithm": "sha256", "files": source_identity()},
        "purpose": "Required PRORATA ERC-4626 differential cases and execution channels. This is not a golden, allowlist, deviation record, or expected-output oracle.",
        "required": {
            "selectors": list(SELECTORS),
            "cases": list(CASES),
            "channels": CHANNELS,
        },
    }


def render_manifest() -> str:
    return json.dumps(manifest_data(), indent=2, sort_keys=True) + "\n"


def validate_manifest(path: Path = MANIFEST) -> list[str]:
    """Return every schema drift; an unreadable declaration is a failure."""
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"matrix manifest is unreadable: {exc}"]
    if not isinstance(value, dict) or value.get("schema") != 1:
        return ["matrix manifest must be a schema-1 object"]
    if value != manifest_data():
        return ["matrix manifest is not the deterministic producer output; regenerate it before running"]
    return []


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="require the committed output to match")
    parser.add_argument("--print", action="store_true", help="write the deterministic JSON to stdout")
    args = parser.parse_args(argv)
    if args.print:
        print(render_manifest(), end="")
    if args.check:
        errors = validate_manifest()
        if errors:
            for error in errors:
                print(f"REGRESSION — vault differential matrix: {error}")
            return 1
        print(f"OK — vault differential matrix: {len(SELECTORS)} selectors and {len(CASES)} required cases")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(__import__("sys").argv[1:]))
