#!/usr/bin/env python3
"""Independent emitted-byte schema for Lido runtime revert auxiliaries.

The Lean evaluator is the sole Blanc artifact owner.  This checker consumes
its two parameter worlds, partitions each emitted runtime with the compiler-
derived table coordinates, and independently reconstructs the exact protected
revert entries from the reference ABI (plus the EVM-standard Panic identity).
It intentionally contains no complete runtime literal.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, NoReturn, Sequence


REPO = Path(__file__).resolve().parents[1]
REFERENCE_LOCK = REPO / "scripts" / "lido-circuit-breaker-reference.json"

WORLD_LABELS = ("official-runtime", "independent-runtime")
RUNTIME_TABLE_NAMES = (
    "main",
    "fallback",
    "error-pausable-zero",
    "error-sender-not-admin",
    "error-sender-not-pauser",
    "error-pause-below-min",
    "error-pause-above-max",
    "error-heartbeat-below-min",
    "error-heartbeat-above-max",
    "error-heartbeat-expired",
    "error-pause-failed",
    "error-reentrant-call",
    "empty-revert",
    "bubble-revert",
    "set-pauser-kernel",
    "append-target",
    "after-old-pauser",
    "remove-target",
    "finish-set-pauser",
    "register-after-set",
    "pause-after-set",
    "enumeration-loop",
    "arithmetic-panic",
)

# Table index equals the stable Func slot: entry zero is main and the remaining
# entries are the program's auxiliary list at slots 1..22.
RUNTIME_ERROR_SLOTS = (
    (2, "error-pausable-zero", "PausableZero"),
    (3, "error-sender-not-admin", "SenderNotAdmin"),
    (4, "error-sender-not-pauser", "SenderNotPauser"),
    (5, "error-pause-below-min", "PauseDurationBelowMin"),
    (6, "error-pause-above-max", "PauseDurationAboveMax"),
    (7, "error-heartbeat-below-min", "HeartbeatIntervalBelowMin"),
    (8, "error-heartbeat-above-max", "HeartbeatIntervalAboveMax"),
    (9, "error-heartbeat-expired", "HeartbeatExpired"),
    (10, "error-pause-failed", "PauseFailed"),
    (11, "error-reentrant-call", "ReentrantCall"),
)

EMPTY_REVERT_SLOT = 12
BUBBLE_REVERT_SLOT = 13
ARITHMETIC_PANIC_SLOT = 22
PANIC_SELECTOR = bytes.fromhex("4e487b71")
ARITHMETIC_PANIC_CODE = 0x11
COMPACT_SELECTOR_ENTRY_BYTES = 13

REQUIRED_ROWS = set(WORLD_LABELS) | {"runtime-table-layout"}


class RuntimeErrorSchemaError(RuntimeError):
    """A fail-closed runtime-revert-table violation."""


def die(message: str) -> NoReturn:
    raise RuntimeErrorSchemaError(message)


def parse_nat(token: str, context: str) -> int:
    if re.fullmatch(r"0|[1-9][0-9]*", token) is None:
        die(f"{context}: expected a canonical decimal natural")
    return int(token)


def parse_hex_bytes(token: str, context: str) -> bytes:
    if len(token) % 2 != 0 or re.fullmatch(r"[0-9a-f]*", token) is None:
        die(f"{context}: expected lowercase even-length hex")
    try:
        return bytes.fromhex(token)
    except ValueError as exc:  # Defensive: the regular expression is stricter.
        raise RuntimeErrorSchemaError(f"{context}: malformed hex") from exc


@dataclass(frozen=True)
class TableEntry:
    name: str
    start: int
    length: int

    @property
    def end(self) -> int:
        return self.start + self.length


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    immediate: bytes

    @property
    def end(self) -> int:
        return self.pc + 1 + len(self.immediate)


@dataclass(frozen=True)
class EvaluatorData:
    artifacts: Mapping[str, bytes]
    table: tuple[TableEntry, ...]


def parse_table(parts: Sequence[str]) -> tuple[TableEntry, ...]:
    if len(parts) != 3:
        die("runtime-table-layout: malformed evaluator row")
    count = parse_nat(parts[1], "runtime-table-layout count")
    descriptors = [] if parts[2] == "-" else parts[2].split(",")
    if len(descriptors) != count:
        die("runtime-table-layout: descriptor count mismatch")
    entries: list[TableEntry] = []
    for descriptor in descriptors:
        fields = descriptor.split("|")
        if len(fields) != 3 or re.fullmatch(r"[a-z0-9-]+", fields[0]) is None:
            die("runtime-table-layout: malformed descriptor")
        entries.append(TableEntry(
            fields[0],
            parse_nat(fields[1], f"runtime table start {fields[0]}"),
            parse_nat(fields[2], f"runtime table length {fields[0]}"),
        ))
    if len({entry.name for entry in entries}) != len(entries):
        die("runtime-table-layout: duplicate entry name")
    if len({entry.start for entry in entries}) != len(entries):
        die("runtime-table-layout: duplicate entry start")
    return tuple(entries)


def parse_evaluator(text: str) -> EvaluatorData:
    rows: dict[str, list[str]] = {}
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        if not raw_line.strip():
            continue
        if raw_line != raw_line.strip():
            die(f"evaluator line {line_number}: leading or trailing whitespace")
        parts = raw_line.split()
        if not parts:
            die(f"evaluator line {line_number}: malformed row")
        label = parts[0]
        if label in rows:
            die(f"duplicate evaluator row {label}")
        rows[label] = parts

    missing = sorted(REQUIRED_ROWS - rows.keys())
    if missing:
        die("missing evaluator row(s): " + ", ".join(missing))

    artifacts: dict[str, bytes] = {}
    for label in WORLD_LABELS:
        parts = rows[label]
        if len(parts) != 3:
            die(f"{label}: malformed evaluator byte row")
        declared = parse_nat(parts[1], f"{label} length")
        artifact = parse_hex_bytes(parts[2], label)
        if len(artifact) != declared:
            die(f"{label}: declared byte length mismatch")
        artifacts[label] = artifact

    return EvaluatorData(
        artifacts=artifacts,
        table=parse_table(rows["runtime-table-layout"]),
    )


def parse_reference_selectors(path: Path = REFERENCE_LOCK) -> Mapping[str, bytes]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeErrorSchemaError(
            f"reference lock is unavailable or malformed: {path}") from exc
    try:
        errors = value["abi"]["errors"]
    except (KeyError, TypeError) as exc:
        raise RuntimeErrorSchemaError(
            "reference lock: missing ABI error inventory") from exc
    if not isinstance(errors, list) or len(errors) != 15:
        die("reference lock: expected exactly 15 custom errors")

    selectors: dict[str, bytes] = {}
    for index, row in enumerate(errors):
        label = f"reference lock error[{index}]"
        if not isinstance(row, dict):
            die(f"{label}: expected an object")
        try:
            entry = row["entry"]
            signature = row["signature"]
            selector_token = row["selector"]
        except (KeyError, TypeError) as exc:
            raise RuntimeErrorSchemaError(f"{label}: incomplete identity") from exc
        if not isinstance(entry, dict):
            die(f"{label}: ABI entry is not an object")
        name = entry.get("name")
        if (not isinstance(name, str) or entry.get("type") != "error" or
                entry.get("inputs") != [] or signature != f"{name}()"):
            die(f"{label}: expected an exact zero-argument error identity")
        if (not isinstance(selector_token, str) or
                re.fullmatch(r"0x[0-9a-f]{8}", selector_token) is None):
            die(f"{label}: selector is not exact lowercase bytes4")
        if name in selectors:
            die(f"reference lock: duplicate error {name}")
        selectors[name] = bytes.fromhex(selector_token[2:])

    required_names = {abi_name for _, _, abi_name in RUNTIME_ERROR_SLOTS}
    missing = sorted(required_names - selectors.keys())
    if missing:
        die("reference lock: missing runtime error selector(s): " + ", ".join(missing))
    return selectors


def disassemble(code: bytes) -> tuple[Instruction, ...]:
    instructions: list[Instruction] = []
    pc = 0
    while pc < len(code):
        opcode = code[pc]
        width = opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0
        end = pc + 1 + width
        if end > len(code):
            die(f"truncated PUSH at byte {pc}")
        instructions.append(Instruction(pc, opcode, code[pc + 1:end]))
        pc = end
    return tuple(instructions)


def minimal_push(value: int) -> bytes:
    if not 0 <= value < 1 << 256:
        die("independent PUSH value lies outside the EVM word domain")
    if value == 0:
        return b"\x5f"
    width = (value.bit_length() + 7) // 8
    return bytes([0x5F + width]) + value.to_bytes(width, "big")


def selector_reverter(selector: bytes) -> bytes:
    if len(selector) != 4:
        die("independent selector reverter requires exactly four bytes")
    return b"\x5b\x63" + selector + bytes.fromhex("5f526004601cfd")


def legacy_selector_reverter(selector: bytes) -> bytes:
    """The former 40-byte table entry, retained only as a live falsifier."""
    if len(selector) != 4:
        die("legacy selector reverter requires exactly four bytes")
    word = int.from_bytes(selector + bytes(28), "big")
    return b"\x5b" + minimal_push(word) + bytes.fromhex("5f5260045ffd")


def constant_data_reverter(payload: bytes) -> bytes:
    """Independently reconstruct the existing constant-data Func layout."""
    chunks = [
        (offset, payload[offset:offset + 32].ljust(32, b"\x00"))
        for offset in range(0, len(payload), 32)
    ]
    code = bytearray(b"\x5b")
    for offset, chunk in reversed(chunks):
        code.extend(minimal_push(int.from_bytes(chunk, "big")))
        code.extend(minimal_push(offset))
        code.append(0x52)  # MSTORE
    code.extend(minimal_push(len(payload)))
    code.extend(minimal_push(0))
    code.append(0xFD)  # REVERT
    return bytes(code)


def arithmetic_panic_reverter() -> bytes:
    payload = PANIC_SELECTOR + ARITHMETIC_PANIC_CODE.to_bytes(32, "big")
    return constant_data_reverter(payload)


def validate_evaluator(
        text: str, lock_path: Path = REFERENCE_LOCK) -> Mapping[str, object]:
    data = parse_evaluator(text)
    selectors = parse_reference_selectors(lock_path)
    table = data.table
    if tuple(entry.name for entry in table) != RUNTIME_TABLE_NAMES:
        die("runtime table names/order or stable auxiliary slots drifted")

    official = data.artifacts["official-runtime"]
    independent = data.artifacts["independent-runtime"]
    if len(official) != len(independent):
        die("dual runtime worlds have different compiler lengths")
    if official == independent:
        die("dual runtime worlds collapsed to byte identity")

    cursor = 0
    for entry in table:
        if entry.start != cursor or entry.length <= 0:
            die(f"runtime table is not an exact ordered partition at {entry.name}")
        cursor = entry.end
    if cursor != len(official):
        die("runtime table does not cover both complete emitted runtimes")

    world_entries: dict[str, tuple[bytes, ...]] = {}
    for world in WORLD_LABELS:
        code = data.artifacts[world]
        instructions = disassemble(code)
        boundaries = {inst.pc for inst in instructions} | {len(code)}
        pieces: list[bytes] = []
        for entry in table:
            if entry.start not in boundaries or entry.end not in boundaries:
                die(f"{world}: table entry {entry.name} is not instruction-aligned")
            piece = code[entry.start:entry.end]
            if not piece or piece[0] != 0x5B:
                die(f"{world}: table entry {entry.name} lacks its JUMPDEST")
            pieces.append(piece)
        if b"".join(pieces) != code:
            die(f"{world}: named runtime-table reconstruction differs from emitted bytes")
        world_entries[world] = tuple(pieces)

    for slot, table_name, abi_name in RUNTIME_ERROR_SLOTS:
        entry = table[slot]
        if entry.name != table_name:
            die(f"runtime error slot {slot} changed identity")
        expected = selector_reverter(selectors[abi_name])
        if len(expected) != COMPACT_SELECTOR_ENTRY_BYTES:
            die("independent compact-selector reconstruction has the wrong length")
        for world in WORLD_LABELS:
            actual = world_entries[world][slot]
            if len(actual) != COMPACT_SELECTOR_ENTRY_BYTES or actual != expected:
                die(f"{world}: selector reverter {abi_name} changed bytes/window")

    preserved = (
        (EMPTY_REVERT_SLOT, "empty-revert", bytes.fromhex("5b5f5ffd")),
        (BUBBLE_REVERT_SLOT, "bubble-revert", bytes.fromhex("5b3d5f5f3e3d5ffd")),
        (ARITHMETIC_PANIC_SLOT, "arithmetic-panic", arithmetic_panic_reverter()),
    )
    for slot, name, expected in preserved:
        if table[slot].name != name:
            die(f"runtime preserved helper slot {slot} changed identity")
        for world in WORLD_LABELS:
            if world_entries[world][slot] != expected:
                die(f"{world}: runtime {name} helper changed bytes")

    return {
        "worlds": len(WORLD_LABELS),
        "entries": len(table),
        "compactErrors": len(RUNTIME_ERROR_SLOTS),
        "preservedHelpers": len(preserved),
        "runtimeLength": len(official),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("--reference-lock", type=Path, default=REFERENCE_LOCK)
    args = parser.parse_args(argv)
    report = validate_evaluator(
        args.artifacts.read_text(encoding="utf-8"), args.reference_lock)
    print(
        "OK — Lido runtime error byte schema: "
        f"{report['worlds']} worlds; {report['entries']} instruction-aligned entries; "
        f"{report['compactErrors']} compact selector errors; "
        f"{report['preservedHelpers']} preserved helpers"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, TypeError, ValueError, RuntimeErrorSchemaError) as exc:
        print(
            "REGRESSION — Lido runtime error byte schema: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
