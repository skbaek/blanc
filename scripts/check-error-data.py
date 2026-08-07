#!/usr/bin/env python3
"""Cross-derive Blanc.errorData from the frozen WETH10 reason inventory.

The lock supplies the strings.  Lean evaluates the landed definition; Python
independently reconstructs Solidity's Error(string) ABI payload with the
reference checker's in-repo Keccak implementation.  No expected payload is
stored, so this check cannot become stale by sharing an artifact with Lean.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LOCK = ROOT / "scripts" / "weth10-reference.json"
HARNESS = ROOT / "scripts" / "eval-error-data.lean"
HEX = re.compile(r"0x[0-9a-f]+\Z")


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def load_reference() -> ModuleType:
    path = ROOT / "scripts" / "weth10-reference.py"
    spec = importlib.util.spec_from_file_location("weth10_reference", path)
    require(spec is not None and spec.loader is not None,
            f"cannot load Keccak implementation from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reasons_from_lock(lock_path: Path) -> list[str]:
    try:
        lock = json.loads(lock_path.read_text(encoding="utf-8"))
        source = lock["sourceBehavior"]
        rows = source["guardOrder"]
        listed = source["reasonStrings"]
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise CheckError(f"cannot read sourceBehavior reason inventory from {lock_path}: {exc}") from exc
    require(isinstance(rows, list), "sourceBehavior.guardOrder is not a list")
    require(isinstance(listed, list), "sourceBehavior.reasonStrings is not a list")
    require(all(isinstance(s, str) for s in listed),
            "sourceBehavior.reasonStrings contains a non-string")
    require(bool(listed), "sourceBehavior.reasonStrings is empty")
    require(len(set(listed)) == len(listed),
            "sourceBehavior.reasonStrings contains a duplicate")

    observed: list[str] = []
    for row_index, row in enumerate(rows):
        require(isinstance(row, dict), f"sourceBehavior.guardOrder[{row_index}] is not an object")
        guards = row.get("guardOrder")
        require(isinstance(guards, list),
                f"sourceBehavior.guardOrder[{row_index}].guardOrder is not a list")
        for guard_index, guard in enumerate(guards):
            require(isinstance(guard, dict),
                    f"guard {row_index}/{guard_index} is not an object")
            reason = guard.get("reason")
            require(isinstance(reason, str),
                    f"guard {row_index}/{guard_index} has no string reason")
            if reason not in observed:
                observed.append(reason)
    require(bool(observed), "sourceBehavior.guardOrder has no reason strings")
    require(observed == listed,
            "sourceBehavior.reasonStrings does not exactly match the guard inventories")
    for reason in listed:
        require(reason.isascii(), f"non-ASCII Error(string) preimage: {reason!r}")
    return listed


def abi_error_data(reason: str, reference: ModuleType) -> bytes:
    data = reason.encode("ascii")
    selector = bytes.fromhex(reference.keccak256(b"Error(string)"))[:4]
    pad = (-len(data)) % 32
    return selector + (32).to_bytes(32, "big") + len(data).to_bytes(32, "big") + data + bytes(pad)


def lean_outputs(reasons: list[str], harness: Path) -> list[bytes]:
    require(harness.is_file(), f"Lean evaluation harness is missing: {harness}")
    command = ["lake", "env", "lean", "--run", str(harness), *reasons]
    try:
        completed = subprocess.run(command, cwd=ROOT, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   check=False)
    except OSError as exc:
        raise CheckError(f"cannot execute {' '.join(command[:4])}: {exc}") from exc
    require(completed.returncode == 0,
            "Lean evaluation failed:\n" + completed.stderr.rstrip())
    lines = completed.stdout.splitlines()
    require(len(lines) == len(reasons),
            f"Lean evaluation produced {len(lines)} blob(s) for {len(reasons)} lock reason(s)")
    result: list[bytes] = []
    for index, line in enumerate(lines):
        require(HEX.fullmatch(line) is not None and len(line) % 2 == 0,
                f"Lean evaluation output {index} is not lowercase 0x hex: {line!r}")
        result.append(bytes.fromhex(line[2:]))
    return result


def check(lock_path: Path, harness: Path) -> str:
    reasons = reasons_from_lock(lock_path)
    reference = load_reference()
    lean = lean_outputs(reasons, harness)
    expected = [abi_error_data(reason, reference) for reason in reasons]
    for index, (reason, actual, want) in enumerate(zip(reasons, lean, expected)):
        require(actual == want,
                f"blob mismatch for lock reason {index} {reason!r}: "
                f"Lean 0x{actual.hex()}, Python 0x{want.hex()}")
    return f"OK — error data: {len(reasons)} lock reason string(s), Lean and independent ABI derivations byte-identical"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lock", type=Path, default=LOCK,
                        help="reference lock (default: scripts/weth10-reference.json)")
    parser.add_argument("--harness", type=Path, default=HARNESS,
                        help="Lean evaluation harness")
    args = parser.parse_args()
    print(check(args.lock, args.harness))


if __name__ == "__main__":
    try:
        main()
    except CheckError as exc:
        raise SystemExit(f"REGRESSION — error data: {exc}")
