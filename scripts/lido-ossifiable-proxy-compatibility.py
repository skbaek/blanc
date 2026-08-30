#!/usr/bin/env python3
"""Generate/check the OssifiableProxy compatibility skeleton from its lock."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

from lido_ossifiable_proxy_reference_schema import (
    SchemaError,
    strict_json,
    validate_lock_schema,
)


ROOT = Path(__file__).resolve().parents[1]
LOCK = Path(os.environ.get(
    "LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK",
    ROOT / "scripts" / "lido-ossifiable-proxy-reference.json",
))
DOCUMENT = Path(os.environ.get(
    "LIDO_OSSIFIABLE_PROXY_COMPATIBILITY_DOC",
    ROOT / "OSSIFIABLE_PROXY_COMPATIBILITY.md",
))

CROSSCUTS = [
    "named-entry-nonpayability",
    "fallback-receive-payability",
    "selector-dispatch",
    "abi-decoding-boundaries",
    "authorization-and-ossification-precedence",
    "upgrade-and-setup-reverts",
    "event-surface",
    "error-and-string-surface",
    "erc1967-functional-slots",
    "constructor-source-order",
    "delegation-returndata",
    "inherited-abi-only-declarations",
    "interface-vs-source-accidents",
]

LOCK_RE = re.compile(r"^<!-- OSSIFIABLE-PROXY-LOCK ([0-9a-f]{64}) -->$")
CONSTRUCTOR_RE = re.compile(r"^<!-- OSSIFIABLE-PROXY-CONSTRUCTOR (\{.*\}) -->$")
ENDPOINT_RE = re.compile(r"^<!-- OSSIFIABLE-PROXY-ENDPOINT (\{.*\}) -->$")
CROSSCUT_RE = re.compile(r"^<!-- OSSIFIABLE-PROXY-CROSSCUT ([a-z0-9-]+) -->$")


class CompatibilityError(RuntimeError):
    pass


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def load_lock() -> tuple[dict[str, Any], str]:
    try:
        raw = LOCK.read_bytes()
        value = strict_json(raw, str(LOCK))
        validate_lock_schema(value, "compatibility reference lock")
    except (OSError, SchemaError) as exc:
        raise CompatibilityError(f"cannot load independently valid reference lock: {exc}") from exc
    if raw != canonical(value):
        raise CompatibilityError("reference lock is not canonical JSON")
    return value, hashlib.sha256(raw).hexdigest()


def expected_constructor(lock: dict[str, Any]) -> dict[str, Any]:
    constructor = lock["abi"]["constructor"]
    return {
        "argumentTypes": constructor["argumentTypes"],
        "payable": constructor["payable"],
        "signature": "constructor(address,address,bytes)",
    }


def expected_endpoints(lock: dict[str, Any]) -> list[dict[str, Any]]:
    rows = [{
        "acceptsValue": row["acceptsValue"],
        "selector": row["selector"],
        "signature": row["signature"],
        "stateMutability": row["entry"]["stateMutability"],
    } for row in lock["abi"]["functions"]]
    for kind in ("fallback", "receive"):
        row = lock["abi"][kind]
        rows.append({
            "acceptsValue": row["acceptsValue"],
            "selector": None,
            "signature": kind,
            "stateMutability": row["entry"]["stateMutability"],
        })
    return rows


def marker(prefix: str, row: dict[str, Any]) -> str:
    return f"<!-- {prefix} " + json.dumps(row, sort_keys=True, separators=(",", ":")) + " -->"


def endpoint_section(row: dict[str, Any]) -> list[str]:
    selector = row["selector"] or ("empty calldata" if row["signature"] == "receive" else "unmatched/short calldata")
    value = "accepted" if row["acceptsValue"] else "rejected before endpoint body behavior"
    return [
        marker("OSSIFIABLE-PROXY-ENDPOINT", row),
        f"### `{row['signature']}`",
        "",
        "| Field | Frozen Solidity boundary | Blanc port evidence |",
        "|---|---|---|",
        f"| Selector / dispatch key | `{selector}` | planned |",
        f"| State mutability | `{row['stateMutability']}` | planned |",
        f"| Nonzero call value | {value} | planned |",
        "| Classification | functional interface | planned |",
        "",
    ]


def skeleton(lock: dict[str, Any], lock_sha256: str) -> str:
    constructor = expected_constructor(lock)
    events = lock["abi"]["behavioralEvents"]
    errors = lock["abi"]["errors"]
    reasons = lock["sourceBehavior"]["reasonStrings"]
    slots = lock["sourceBehavior"]["slots"]
    lines = [
        "# OssifiableProxy compatibility contract",
        "",
        f"<!-- OSSIFIABLE-PROXY-LOCK {lock_sha256} -->",
        "",
        "This generated skeleton freezes the Solidity reference boundary before the Blanc port",
        "claim is filled in. `planned` means the reference side is locked while port evidence is",
        "still required; it is not an equivalence claim.",
        "",
        "## Constructor",
        "",
        marker("OSSIFIABLE-PROXY-CONSTRUCTOR", constructor),
        "",
        "| Field | Frozen Solidity boundary | Blanc port evidence |",
        "|---|---|---|",
        "| Signature | `constructor(address,address,bytes)` | planned |",
        "| State mutability | `nonpayable` | planned |",
        "| Nonzero creation value | rejected before constructor body behavior | planned |",
        "| Canonical empty-data suffix | 128 bytes after the 4,207-byte creation template | planned |",
        "| Classification | functional interface | planned |",
        "",
        "## Runtime endpoints",
        "",
    ]
    for row in expected_endpoints(lock):
        lines.extend(endpoint_section(row))
    lines.extend(["## Cross-cutting behavior", ""])

    crosscut_text = {
        "named-entry-nonpayability": (
            "All seven named selectors reject nonzero call value in compiler dispatch before "
            "authorization or endpoint-body behavior. The three getters are `view`; the four "
            "administrative entries are `nonpayable`."
        ),
        "fallback-receive-payability": (
            "Fallback and receive are payable and delegate to the implementation; value is "
            "observed in proxy storage context by the delegated child."
        ),
        "selector-dispatch": (
            "The seven locked selectors are pairwise distinct. Empty calldata selects receive; "
            "unmatched selectors and 0–3-byte nonempty calldata select fallback."
        ),
        "abi-decoding-boundaries": (
            "The lock records the head width, canonical minimum length, address-word, bool-word, "
            "dynamic-offset/length, and trailing-calldata boundary for every decoded endpoint."
        ),
        "authorization-and-ossification-precedence": (
            "For every administrative body, admin zero raises `ProxyIsOssified()` before caller "
            "comparison; otherwise a caller different from admin raises `NotAdmin()`."
        ),
        "upgrade-and-setup-reverts": (
            "A new implementation without code uses `ERC1967: new implementation is not a "
            "contract`; an empty failed setup uses `Address: low-level delegate call failed`; "
            "nonempty child revert data is bubbled exactly."
        ),
        "event-surface": "The three reachable event families are: " + "; ".join(
            f"`{row['signature']}` → `{row['topic0']}`" for row in events) + ".",
        "error-and-string-surface": "The custom errors are " + "; ".join(
            f"`{row['signature']}` → `{row['selector']}`" for row in errors
        ) + ". The inherited `Error(string)` messages are " + "; ".join(
            f"`{row['message']}`" for row in reasons) + ".",
        "erc1967-functional-slots": (
            "The ERC-1967 words are a functional interoperability surface, not discardable "
            "storage-layout accidents: " + "; ".join(
                f"{row['name']} `{row['value']}`" for row in slots) + "."
        ),
        "constructor-source-order": (
            "Construction validates/writes implementation and emits `Upgraded`, optionally "
            "delegatecalls setup, then reads the post-setup admin, emits `AdminChanged`, "
            "validates nonzero new admin, and writes admin."
        ),
        "delegation-returndata": (
            "Fallback and receive copy complete delegatecall returndata and return or revert with "
            "that data; execution uses the proxy account/storage context."
        ),
        "inherited-abi-only-declarations": (
            "`BeaconUpgraded(address)` is preserved in the raw compiler ABI as an inherited "
            "ABI-only declaration. It is excluded from the three-event behavioral surface "
            "because no OssifiableProxy external or constructor path calls the inherited "
            "internal beacon-upgrade emitter."
        ),
        "interface-vs-source-accidents": (
            "Selectors, mutability/value behavior, errors, reachable events, delegation "
            "observations, constructor behavior, and both ERC-1967 slots are functional. "
            "Source offsets, incidental bytecode layout, exact code hashes, and gas are "
            "reference or measurement facts rather than automatic semantic obligations."
        ),
    }
    for key in CROSSCUTS:
        lines.extend([
            f"<!-- OSSIFIABLE-PROXY-CROSSCUT {key} -->",
            f"### {key}",
            "",
            crosscut_text[key],
            "",
            "Blanc port evidence: planned.",
            "",
        ])
    return "\n".join(lines).rstrip()


def parse_json_marker(raw: str, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise CompatibilityError(f"malformed {label} marker: {exc}") from exc
    if not isinstance(value, dict):
        raise CompatibilityError(f"{label} marker is not an object")
    return value


def check(lock: dict[str, Any], lock_sha256: str) -> None:
    try:
        lines = DOCUMENT.read_text().splitlines()
    except OSError as exc:
        raise CompatibilityError(f"cannot read {DOCUMENT}: {exc}") from exc
    lock_markers = [match.group(1) for line in lines if (match := LOCK_RE.fullmatch(line))]
    if lock_markers != [lock_sha256]:
        raise CompatibilityError("document lock-digest marker differs")
    constructors = [parse_json_marker(match.group(1), "constructor")
                    for line in lines if (match := CONSTRUCTOR_RE.fullmatch(line))]
    if constructors != [expected_constructor(lock)]:
        raise CompatibilityError("constructor marker differs from locked nonpayable ABI")
    endpoints = [parse_json_marker(match.group(1), "endpoint")
                 for line in lines if (match := ENDPOINT_RE.fullmatch(line))]
    if endpoints != expected_endpoints(lock):
        raise CompatibilityError(
            f"endpoint markers differ\nexpected: {expected_endpoints(lock)}\nfound: {endpoints}")
    crosscuts = [match.group(1) for line in lines if (match := CROSSCUT_RE.fullmatch(line))]
    if crosscuts != CROSSCUTS:
        raise CompatibilityError(f"cross-cut markers differ\nexpected: {CROSSCUTS}\nfound: {crosscuts}")
    normalized = " ".join("\n".join(lines).split())
    required = [
        "constructor(address,address,bytes)", "nonpayable", "Fallback and receive are payable",
        "admin zero raises `ProxyIsOssified()` before caller comparison",
        "functional interoperability surface", "BeaconUpgraded(address)", "ABI-only declaration",
        "three-event behavioral surface", "Source offsets", "gas are reference or measurement facts",
    ]
    for phrase in required:
        if phrase not in normalized:
            raise CompatibilityError(f"required semantic phrase missing: {phrase}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("skeleton", "check"))
    arguments = parser.parse_args()
    try:
        lock, lock_sha256 = load_lock()
        if arguments.command == "skeleton":
            sys.stdout.write(skeleton(lock, lock_sha256) + "\n")
        else:
            check(lock, lock_sha256)
    except CompatibilityError as exc:
        print(f"REGRESSION — Lido OssifiableProxy compatibility: {exc}", file=sys.stderr)
        return 1
    if arguments.command == "check":
        print("OK — Lido OssifiableProxy compatibility: constructor + 9 runtime endpoints + 13 cross-cuts synchronized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
