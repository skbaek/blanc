#!/usr/bin/env python3
"""Generate/check WETH10 compatibility-document row keys from the target lock."""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LOCK = Path(os.environ.get("WETH10_REFERENCE_LOCK", ROOT / "scripts" / "weth10-reference.json"))
DOCUMENT = Path(os.environ.get("WETH10_COMPATIBILITY_DOC", ROOT / "WETH10_COMPATIBILITY.md"))

CROSS_CUTTING_KEYS = [
    "receive-vs-unknown",
    "nonpayability",
    "canonical-calldata",
    "staticcall",
    "reentrancy-snapshots",
    "force-sent-eth",
    "gas-sensitive-callbacks",
    "malformed-calldata-exclusion",
    "delegatecall-exclusion",
    "cryptographic-collision-scope",
    "self-address-correspondence",
    "logical-state-projection",
]

ENDPOINT_RE = re.compile(r"^<!-- WETH10-ENDPOINT (\{.*\}) -->$")
CROSS_CUTTING_RE = re.compile(r"^<!-- WETH10-CROSSCUT ([a-z0-9-]+) -->$")
DEPLOYMENT_MARKER = "<!-- WETH10-DEPLOYMENT constructor -->"


class CompatibilityError(RuntimeError):
    pass


def load_lock() -> dict:
    try:
        value = json.loads(LOCK.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CompatibilityError(f"cannot read generated lock: {exc}") from exc
    return value


def expected_endpoints(lock: dict) -> list[dict[str, str | None]]:
    try:
        functions = lock["abi"]["functions"]
        receive = lock["abi"]["receive"]
    except (KeyError, TypeError) as exc:
        raise CompatibilityError(f"generated lock has no complete ABI inventory: {exc}") from exc
    rows = [
        {"signature": row["signature"], "selector": row["selector"]}
        for row in functions
    ]
    if receive.get("entry", {}).get("type") != "receive":
        raise CompatibilityError("generated lock receive entry has unknown shape")
    rows.append({"signature": "receive", "selector": None})
    return rows


def marker(row: dict[str, str | None]) -> str:
    return "<!-- WETH10-ENDPOINT " + json.dumps(row, separators=(",", ":")) + " -->"


def skeleton(lock: dict) -> str:
    lines = ["# WETH10 compatibility contract", "", "## Runtime endpoints", ""]
    for row in expected_endpoints(lock):
        lines.extend([
            marker(row),
            f"### `{row['signature']}`",
            "",
            "| Field | Frozen behavior |",
            "|---|---|",
            f"| Selector | `{row['selector'] or 'empty calldata'}` |",
            "| Evidence status | planned |",
            "",
        ])
    lines.extend(["## Cross-cutting behavior", ""])
    for key in CROSS_CUTTING_KEYS:
        lines.extend([f"<!-- WETH10-CROSSCUT {key} -->", f"### {key}", "", "planned", ""])
    lines.extend(["## Deployment boundary", "", DEPLOYMENT_MARKER, "", "planned", ""])
    return "\n".join(lines)


def check(lock: dict) -> None:
    try:
        lines = DOCUMENT.read_text().splitlines()
    except OSError as exc:
        raise CompatibilityError(f"cannot read {DOCUMENT.name}: {exc}") from exc

    found_endpoints: list[dict[str, str | None]] = []
    for line in lines:
        match = ENDPOINT_RE.fullmatch(line)
        if not match:
            continue
        try:
            row = json.loads(match.group(1))
        except json.JSONDecodeError as exc:
            raise CompatibilityError(f"malformed endpoint marker: {line}") from exc
        if not isinstance(row, dict) or set(row) != {"signature", "selector"}:
            raise CompatibilityError(f"endpoint marker has unknown fields: {line}")
        if not isinstance(row["signature"], str) or not (
            row["selector"] is None or isinstance(row["selector"], str)
        ):
            raise CompatibilityError(f"endpoint marker has wrong types: {line}")
        found_endpoints.append(row)

    expected = expected_endpoints(lock)
    if found_endpoints != expected:
        raise CompatibilityError(
            "endpoint markers differ from generated ABI keys/selectors\n"
            f"expected: {expected}\nfound: {found_endpoints}"
        )

    found_cross_cutting = [
        match.group(1)
        for line in lines
        if (match := CROSS_CUTTING_RE.fullmatch(line)) is not None
    ]
    if found_cross_cutting != CROSS_CUTTING_KEYS:
        raise CompatibilityError(
            "cross-cutting markers differ from the required inventory\n"
            f"expected: {CROSS_CUTTING_KEYS}\nfound: {found_cross_cutting}"
        )
    if lines.count(DEPLOYMENT_MARKER) != 1:
        raise CompatibilityError("compatibility document must contain exactly one deployment marker")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("skeleton", "check"))
    args = parser.parse_args()
    try:
        lock = load_lock()
        if args.command == "skeleton":
            sys.stdout.write(skeleton(lock))
        else:
            check(lock)
    except CompatibilityError as exc:
        print(f"REGRESSION — WETH10 compatibility: {exc}", file=sys.stderr)
        return 1
    if args.command == "check":
        print("OK — WETH10 compatibility: 28 endpoint keys, 12 cross-cutting keys, deployment boundary")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
