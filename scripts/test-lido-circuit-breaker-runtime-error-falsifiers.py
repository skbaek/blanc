#!/usr/bin/env python3
"""Live emitted-byte mutants for the Lido runtime revert-table schema."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Callable, Sequence

from lido_circuit_breaker_runtime_error_schema import (
    REFERENCE_LOCK,
    RUNTIME_ERROR_SLOTS,
    RuntimeErrorSchemaError,
    TableEntry,
    legacy_selector_reverter,
    parse_evaluator,
    parse_reference_selectors,
    validate_evaluator,
)


WORLD_LABELS = ("official-runtime", "independent-runtime")


def lines_of(text: str) -> list[str]:
    return text.splitlines()


def find_row(lines: Sequence[str], label: str) -> int:
    matches = [
        index for index, line in enumerate(lines)
        if line.split(maxsplit=1)[0] == label
    ]
    if len(matches) != 1:
        raise RuntimeError(f"baseline evaluator row {label} is absent or duplicated")
    return matches[0]


def artifact_from_line(line: str, label: str) -> bytes:
    parts = line.split()
    if len(parts) != 3 or parts[0] != label:
        raise RuntimeError(f"baseline evaluator byte row {label} is malformed")
    artifact = bytes.fromhex(parts[2])
    if len(artifact) != int(parts[1]):
        raise RuntimeError(f"baseline evaluator byte row {label} has wrong length")
    return artifact


def replace_artifact(lines: list[str], label: str, artifact: bytes) -> None:
    index = find_row(lines, label)
    lines[index] = f"{label} {len(artifact)} {artifact.hex()}"


def replace_table(lines: list[str], entries: Sequence[TableEntry]) -> None:
    index = find_row(lines, "runtime-table-layout")
    descriptors = ",".join(
        f"{entry.name}|{entry.start}|{entry.length}" for entry in entries)
    lines[index] = f"runtime-table-layout {len(entries)} {descriptors}"


def duplicate_row(text: str, label: str) -> str:
    lines = lines_of(text)
    lines.append(lines[find_row(lines, label)])
    return "\n".join(lines) + "\n"


def remove_row(text: str, label: str) -> str:
    lines = lines_of(text)
    del lines[find_row(lines, label)]
    return "\n".join(lines) + "\n"


def corrupt_declared_length(text: str, label: str) -> str:
    lines = lines_of(text)
    index = find_row(lines, label)
    parts = lines[index].split()
    parts[1] = str(int(parts[1]) + 1)
    lines[index] = " ".join(parts)
    return "\n".join(lines) + "\n"


def replace_slot(text: str, slot: int, replacement: bytes) -> str:
    """Splice the same valid entry into both worlds and shift the table."""
    data = parse_evaluator(text)
    entry = data.table[slot]
    delta = len(replacement) - entry.length
    lines = lines_of(text)
    for world in WORLD_LABELS:
        code = data.artifacts[world]
        replace_artifact(
            lines, world, code[:entry.start] + replacement + code[entry.end:])
    shifted = []
    for index, current in enumerate(data.table):
        if index == slot:
            shifted.append(TableEntry(current.name, current.start, len(replacement)))
        elif index > slot:
            shifted.append(TableEntry(
                current.name, current.start + delta, current.length))
        else:
            shifted.append(current)
    replace_table(lines, shifted)
    return "\n".join(lines) + "\n"


def restore_all_legacy_errors(text: str, lock_path: Path) -> str:
    selectors = parse_reference_selectors(lock_path)
    mutant = text
    for slot, _, abi_name in RUNTIME_ERROR_SLOTS:
        mutant = replace_slot(
            mutant, slot, legacy_selector_reverter(selectors[abi_name]))
    return mutant


def delete_slot(text: str, slot: int) -> str:
    data = parse_evaluator(text)
    entry = data.table[slot]
    lines = lines_of(text)
    for world in WORLD_LABELS:
        code = data.artifacts[world]
        replace_artifact(lines, world, code[:entry.start] + code[entry.end:])
    shifted = []
    for index, current in enumerate(data.table):
        if index == slot:
            continue
        start = current.start - entry.length if index > slot else current.start
        shifted.append(TableEntry(current.name, start, current.length))
    replace_table(lines, shifted)
    return "\n".join(lines) + "\n"


def coherent_reorder(text: str, left: int, right: int) -> str:
    """Move names and bytes together so selector/name pairs remain coherent."""
    data = parse_evaluator(text)
    first, second = data.table[left], data.table[right]
    if right != left + 1 or first.length != second.length:
        raise RuntimeError("coherent reorder requires adjacent equal-sized entries")
    lines = lines_of(text)
    for world in WORLD_LABELS:
        code = data.artifacts[world]
        first_bytes = code[first.start:first.end]
        second_bytes = code[second.start:second.end]
        changed = code[:first.start] + second_bytes + first_bytes + code[second.end:]
        replace_artifact(lines, world, changed)
    entries = list(data.table)
    entries[left] = TableEntry(second.name, first.start, second.length)
    entries[right] = TableEntry(first.name, second.start, first.length)
    replace_table(lines, entries)
    return "\n".join(lines) + "\n"


def edit_slot_byte(
        text: str, slot: int, relative: int, transform: Callable[[int], int],
        worlds: Sequence[str] = WORLD_LABELS) -> str:
    data = parse_evaluator(text)
    entry = data.table[slot]
    if not 0 <= relative < entry.length:
        raise RuntimeError("slot-byte mutant escapes its entry")
    lines = lines_of(text)
    for world in worlds:
        changed = bytearray(data.artifacts[world])
        pc = entry.start + relative
        changed[pc] = transform(changed[pc]) & 0xFF
        replace_artifact(lines, world, bytes(changed))
    return "\n".join(lines) + "\n"


def collapse_parameter_worlds(text: str) -> str:
    data = parse_evaluator(text)
    lines = lines_of(text)
    replace_artifact(lines, "independent-runtime", data.artifacts["official-runtime"])
    return "\n".join(lines) + "\n"


def misalign_error_boundary(text: str) -> str:
    data = parse_evaluator(text)
    entries = list(data.table)
    fallback = entries[1]
    first_error = entries[2]
    # Include JUMPDEST/PUSH4 in the preceding descriptor, leaving the new
    # boundary on the selector's first immediate byte.  Coverage stays exact.
    entries[1] = TableEntry(fallback.name, fallback.start, fallback.length + 2)
    entries[2] = TableEntry(
        first_error.name, first_error.start + 2, first_error.length - 2)
    lines = lines_of(text)
    replace_table(lines, entries)
    return "\n".join(lines) + "\n"


def rejected(text: str, lock_path: Path, diagnostic: str) -> bool:
    try:
        validate_evaluator(text, lock_path)
    except (RuntimeErrorSchemaError, TypeError, ValueError) as exc:
        if diagnostic not in str(exc):
            raise RuntimeError(
                f"falsifier hit unexpected diagnostic: {exc}") from exc
        return True
    return False


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("--reference-lock", type=Path, default=REFERENCE_LOCK)
    args = parser.parse_args(argv)
    baseline = args.artifacts.read_text(encoding="utf-8")
    validate_evaluator(baseline, args.reference_lock)

    mutations = [
        ("duplicate evaluator row", "duplicate evaluator row official-runtime",
         duplicate_row(baseline, "official-runtime")),
        ("missing parameter world", "missing evaluator row(s): independent-runtime",
         remove_row(baseline, "independent-runtime")),
        ("malformed declared runtime length", "declared byte length mismatch",
         corrupt_declared_length(baseline, "official-runtime")),
        ("restore all ten legacy 40-byte errors", "selector reverter PausableZero",
         restore_all_legacy_errors(baseline, args.reference_lock)),
        ("delete one runtime error slot", "runtime table names/order",
         delete_slot(baseline, 2)),
        ("coherent error-table reorder", "runtime table names/order",
         coherent_reorder(baseline, 2, 3)),
        ("selector", "selector reverter PausableZero",
         edit_slot_byte(baseline, 2, 2, lambda value: value ^ 1)),
        ("MSTORE", "selector reverter PausableZero",
         edit_slot_byte(baseline, 2, 7, lambda _: 0x50)),
        ("length-four window", "selector reverter PausableZero",
         edit_slot_byte(baseline, 2, 9, lambda _: 5)),
        ("offset-28 window", "selector reverter PausableZero",
         edit_slot_byte(baseline, 2, 11, lambda _: 27)),
        ("REVERT", "selector reverter PausableZero",
         edit_slot_byte(baseline, 2, 12, lambda _: 0xF3)),
        ("empty revert", "runtime empty-revert helper changed bytes",
         edit_slot_byte(baseline, 12, 3, lambda _: 0xF3)),
        ("bubble revert", "runtime bubble-revert helper changed bytes",
         edit_slot_byte(baseline, 13, 4, lambda _: 0x50)),
        ("Panic payload", "runtime arithmetic-panic helper changed bytes",
         edit_slot_byte(baseline, 22, 2, lambda value: value ^ 1)),
        ("independent-world-only selector", "selector reverter PausableZero",
         edit_slot_byte(
             baseline, 2, 2, lambda value: value ^ 1,
             worlds=("independent-runtime",))),
        ("instruction boundary", "not instruction-aligned",
         misalign_error_boundary(baseline)),
        ("collapsed parameter worlds", "dual runtime worlds collapsed",
         collapse_parameter_worlds(baseline)),
    ]

    missed = [
        name for name, diagnostic, mutation in mutations
        if not rejected(mutation, args.reference_lock, diagnostic)
    ]
    if missed:
        raise RuntimeError("runtime error falsifier(s) passed: " + ", ".join(missed))
    print(
        "OK — Lido runtime error falsifiers: "
        f"{len(mutations)} row/legacy/delete/order/selector/opcode/window/"
        "helper/world/alignment controls rejected"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeErrorSchemaError, RuntimeError, TypeError, ValueError) as exc:
        print(
            "REGRESSION — Lido runtime error falsifiers: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
