#!/usr/bin/env python3
"""Fail-closed marker synchronization for Lido CircuitBreaker AC3 documents.

The reference lock is intentionally not created by this script.  Once AC2
lands, pass ``--lock`` (default: scripts/lido-circuit-breaker-reference.json)
and this checker requires the lock's complete ABI surface.  Until then,
``--allow-missing-lock`` performs only the self-contained document/key check.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DOCUMENT = ROOT / "LIDO_CIRCUIT_BREAKER_COMPATIBILITY.md"
DEFAULT_LOCK = ROOT / "scripts" / "lido-circuit-breaker-reference.json"

SIGNATURES = [
    "ADMIN()", "MIN_PAUSE_DURATION()", "MAX_PAUSE_DURATION()",
    "MIN_HEARTBEAT_INTERVAL()", "MAX_HEARTBEAT_INTERVAL()", "pauseDuration()",
    "heartbeatInterval()", "heartbeatExpiry(address)", "getPauser(address)",
    "getPausableCount(address)", "getPausables()", "isPauserLive(address)",
    "setPauseDuration(uint256)", "setHeartbeatInterval(uint256)",
    "registerPauser(address,address)", "heartbeat()", "pause(address)",
]
CROSSCUTS = [
    "dispatch-nonpayability", "registry-histories", "temporal-arithmetic",
    "errors-events-order", "external-return-allocation", "reentry-interference",
    "rollback", "logical-state-projection", "oracle-independence", "finite-evidence",
]
CONSTRUCTOR_ARGUMENTS = ["address", "uint256", "uint256", "uint256", "uint256", "uint256", "uint256"]
ENDPOINT_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT (\{.*\}) -->$")
CONSTRUCTOR_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-CONSTRUCTOR (\{.*\}) -->$")
CROSSCUT_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT ([a-z0-9-]+) -->$")


class CompatibilityError(RuntimeError):
    pass


def parse_marker(raw: str, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise CompatibilityError(f"malformed {label} marker: {raw}") from exc
    if not isinstance(value, dict):
        raise CompatibilityError(f"{label} marker is not an object")
    return value


def check_document() -> list[dict[str, Any]]:
    try:
        lines = DOCUMENT.read_text().splitlines()
    except OSError as exc:
        raise CompatibilityError(f"cannot read {DOCUMENT.name}: {exc}") from exc
    endpoint_markers: list[dict[str, Any]] = []
    constructors: list[dict[str, Any]] = []
    crosscuts: list[str] = []
    for line in lines:
        if match := ENDPOINT_RE.fullmatch(line):
            marker = parse_marker(match.group(1), "endpoint")
            if set(marker) != {"signature", "selector"} or not isinstance(marker["signature"], str):
                raise CompatibilityError(f"endpoint marker has wrong shape: {line}")
            if not isinstance(marker["selector"], str):
                raise CompatibilityError(f"endpoint selector must be locked: {line}")
            endpoint_markers.append(marker)
        elif match := CONSTRUCTOR_RE.fullmatch(line):
            constructors.append(parse_marker(match.group(1), "constructor"))
        elif match := CROSSCUT_RE.fullmatch(line):
            crosscuts.append(match.group(1))
    endpoint_signatures = [marker["signature"] for marker in endpoint_markers]
    if endpoint_signatures != SIGNATURES:
        raise CompatibilityError(
            f"endpoint markers differ\nexpected: {SIGNATURES}\nfound: {endpoint_signatures}")
    if constructors != [{"arguments": CONSTRUCTOR_ARGUMENTS}]:
        raise CompatibilityError("constructor marker must name exactly seven ABI argument types")
    if crosscuts != CROSSCUTS:
        raise CompatibilityError(f"cross-cut markers differ\nexpected: {CROSSCUTS}\nfound: {crosscuts}")
    return endpoint_markers


def check_lock(lock_path: Path, endpoint_markers: list[dict[str, Any]]) -> None:
    try:
        lock = json.loads(lock_path.read_text())
    except OSError as exc:
        raise CompatibilityError(f"cannot read reference lock {lock_path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise CompatibilityError(f"reference lock is invalid JSON: {exc}") from exc
    try:
        abi = lock["abi"]
        functions = abi["functions"]
        constructor = abi["constructor"]
        errors = abi["errors"]
        events = abi["events"]
    except (KeyError, TypeError) as exc:
        raise CompatibilityError("reference lock missing required abi.functions/constructor/errors/events") from exc
    if not isinstance(functions, list):
        raise CompatibilityError("reference lock abi.functions is not a list")
    locked = []
    locked_rows: dict[str, dict[str, str]] = {}
    for row in functions:
        if not isinstance(row, dict) or not isinstance(row.get("signature"), str) or not isinstance(row.get("selector"), str):
            raise CompatibilityError("reference lock has malformed function row")
        locked.append(row["signature"])
        locked_rows[row["signature"]] = {"signature": row["signature"], "selector": row["selector"]}
    if set(locked) != set(SIGNATURES) or len(locked) != len(SIGNATURES):
        raise CompatibilityError(f"reference-lock selectors differ\nexpected: {SIGNATURES}\nfound: {locked}")
    expected_markers = [locked_rows[signature] for signature in SIGNATURES]
    if endpoint_markers != expected_markers:
        raise CompatibilityError(
            f"document endpoint selectors differ from reference lock\n"
            f"expected: {expected_markers}\nfound: {endpoint_markers}")
    if not isinstance(constructor, dict) or constructor.get("argumentTypes") != CONSTRUCTOR_ARGUMENTS:
        raise CompatibilityError("reference lock constructor does not have the pinned seven ABI types")
    if not isinstance(errors, list) or len(errors) != 15:
        raise CompatibilityError("reference lock must inventory exactly 15 custom errors")
    if not isinstance(events, list) or len(events) != 6:
        raise CompatibilityError("reference lock must inventory exactly 6 event families")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("check",))
    parser.add_argument("--lock", type=Path, default=DEFAULT_LOCK)
    parser.add_argument("--allow-missing-lock", action="store_true")
    args = parser.parse_args()
    try:
        endpoint_markers = check_document()
        if args.lock.exists():
            check_lock(args.lock, endpoint_markers)
            print("OK — Lido CircuitBreaker compatibility: 17 endpoint keys, constructor, 10 cross-cutting keys, reference lock synchronized")
        elif args.allow_missing_lock:
            print("OK — Lido CircuitBreaker compatibility: 17 endpoint keys, constructor, 10 cross-cutting keys; PENDING reference lock at " + str(args.lock))
        else:
            raise CompatibilityError("reference lock is missing at " + str(args.lock) + "; use --allow-missing-lock only for pre-AC2 document checks")
    except CompatibilityError as exc:
        print("REGRESSION — Lido CircuitBreaker compatibility: " + str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
