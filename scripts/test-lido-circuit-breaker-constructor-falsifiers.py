#!/usr/bin/env python3
"""Live emitted-byte mutants for the Lido constructor schema."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Callable, Sequence

from lido_circuit_breaker_constructor_schema import (
    REFERENCE_LOCK,
    SchemaError,
    validate_evaluator,
    validate_fixed_push_encoding,
)


PREFIX_CARRIERS = (
    "creation-template",
    "official-create",
    "independent-create",
)


def lines_of(text: str) -> list[str]:
    return text.splitlines()


def find_row(lines: Sequence[str], label: str) -> int:
    matches = [index for index, line in enumerate(lines) if line.split(maxsplit=1)[0] == label]
    if len(matches) != 1:
        raise RuntimeError(f"baseline evaluator row {label} is absent or duplicated")
    return matches[0]


def artifact_from_line(line: str, label: str) -> bytes:
    parts = line.split()
    if len(parts) != 3 or parts[0] != label:
        raise RuntimeError(f"baseline evaluator byte row {label} is malformed")
    value = bytes.fromhex(parts[2])
    if len(value) != int(parts[1]):
        raise RuntimeError(f"baseline evaluator byte row {label} has wrong length")
    return value


def replace_artifact(lines: list[str], label: str, value: bytes) -> None:
    index = find_row(lines, label)
    lines[index] = f"{label} {len(value)} {value.hex()}"


def edit_prefix(text: str, edit: Callable[[bytes], bytes]) -> str:
    lines = lines_of(text)
    creation_line = lines[find_row(lines, "creation-template")]
    creation = artifact_from_line(creation_line, "creation-template")
    changed_prefix = edit(creation)
    for label in PREFIX_CARRIERS:
        index = find_row(lines, label)
        artifact = artifact_from_line(lines[index], label)
        if not artifact.startswith(creation):
            raise RuntimeError("baseline creation prefix carriers disagree")
        replace_artifact(lines, label, changed_prefix + artifact[len(creation):])
    return "\n".join(lines) + "\n"


def edit_prefix_byte(text: str, pc: int, transform: Callable[[int], int]) -> str:
    def edit(prefix: bytes) -> bytes:
        if not 0 <= pc < len(prefix):
            raise RuntimeError("mutant PC escapes prefix")
        changed = bytearray(prefix)
        changed[pc] = transform(changed[pc]) & 0xFF
        return bytes(changed)
    return edit_prefix(text, edit)


def swap_prefix_bytes(text: str, left: int, right: int) -> str:
    def edit(prefix: bytes) -> bytes:
        if not 0 <= left < len(prefix) or not 0 <= right < len(prefix):
            raise RuntimeError("mutant byte swap escapes prefix")
        changed = bytearray(prefix)
        changed[left], changed[right] = changed[right], changed[left]
        return bytes(changed)
    return edit_prefix(text, edit)


def swap_copy_blocks(text: str, report: dict[str, object]) -> str:
    args_start = int(report["args_copy_start"])
    args_end = int(report["args_copy_pc"]) + 1
    runtime_start = int(report["runtime_copy_start"])
    runtime_end = int(report["runtime_copy_pc"]) + 1

    def edit(prefix: bytes) -> bytes:
        if not 0 <= args_start < args_end <= runtime_start < runtime_end <= len(prefix):
            raise RuntimeError("baseline CODECOPY blocks are not ordered")
        return (
            prefix[:args_start]
            + prefix[runtime_start:runtime_end]
            + prefix[args_end:runtime_start]
            + prefix[args_start:args_end]
            + prefix[runtime_end:]
        )
    return edit_prefix(text, edit)


def insert_runtime_byte(text: str) -> str:
    """Coherently grow every runtime/template row but leave embedded lengths stale."""
    lines = lines_of(text)
    creation_index = find_row(lines, "creation-template")
    creation = artifact_from_line(lines[creation_index], "creation-template")
    for label in ("official-runtime", "independent-runtime"):
        index = find_row(lines, label)
        runtime = artifact_from_line(lines[index], label)
        replace_artifact(lines, label, runtime + b"\x00")
    replace_artifact(lines, "creation-template", creation + b"\x00")
    for label in ("official-create", "independent-create"):
        index = find_row(lines, label)
        full = artifact_from_line(lines[index], label)
        replace_artifact(lines, label, full[:len(creation)] + b"\x00" + full[len(creation):])
    sizes_index = find_row(lines, "sizes")
    size_parts = lines[sizes_index].split()
    if len(size_parts) != 9:
        raise RuntimeError("baseline evaluator sizes row is malformed")
    sizes = [int(value) for value in size_parts[1:]]
    sizes[:3] = [value + 1 for value in sizes[:3]]
    sizes[3:] = [value - 1 for value in sizes[3:]]
    lines[sizes_index] = "sizes " + " ".join(str(value) for value in sizes)
    return "\n".join(lines) + "\n"


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


def corrupt_table_length(text: str) -> str:
    lines = lines_of(text)
    index = find_row(lines, "constructor-table-layout")
    parts = lines[index].split()
    descriptors = parts[2].split(",")
    fields = descriptors[2].split("|")
    fields[2] = str(int(fields[2]) - 1)
    descriptors[2] = "|".join(fields)
    parts[2] = ",".join(descriptors)
    lines[index] = " ".join(parts)
    return "\n".join(lines) + "\n"


def rejected(text: str, lock_path: Path) -> bool:
    try:
        validate_evaluator(text, lock_path)
    except (KeyError, RuntimeError, SchemaError, TypeError, ValueError):
        return True
    return False


def rejected_push(blob: bytes, value: int) -> bool:
    try:
        validate_fixed_push_encoding(blob, value)
    except (RuntimeError, SchemaError, TypeError, ValueError):
        return True
    return False


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("--reference-lock", type=Path, default=REFERENCE_LOCK)
    args = parser.parse_args(argv)
    baseline = args.artifacts.read_text(encoding="utf-8")
    report = dict(validate_evaluator(baseline, args.reference_lock))

    guard_pc = int(report["guard_push_pc"])
    args_source_pc = int(report["args_source_push_pc"])
    runtime_base_pc = int(report["runtime_base_push_pc"])
    return_base_pc = int(report["return_base_push_pc"])
    first_patch_pc = int(tuple(report["patch_push_pcs"])[0])
    first_error_start = int(tuple(report["table"])[2].start)
    lane_bytes = set(int(value) for value in tuple(report["lane_byte_offsets"]))
    non_lane_runtime_byte = next(
        index for index in range(int(report["runtime_length"])) if index not in lane_bytes
    )

    mutations = [
        ("duplicate evaluator row", duplicate_row(baseline, "creation-template")),
        ("missing evaluator row", remove_row(baseline, "limits")),
        ("malformed evaluator length", corrupt_declared_length(baseline, "official-create")),
        ("PUSH width", edit_prefix_byte(baseline, guard_pc, lambda _: 0x60)),
        ("PUSH high-low order", swap_prefix_bytes(baseline, args_source_pc + 1, args_source_pc + 2)),
        ("runtime base", edit_prefix_byte(baseline, runtime_base_pc + 1, lambda value: value ^ 1)),
        ("CODECOPY order", swap_copy_blocks(baseline, report)),
        ("RETURN base", edit_prefix_byte(baseline, return_base_pc + 1, lambda value: value ^ 1)),
        ("selector error size window", edit_prefix_byte(baseline, first_error_start + 9, lambda _: 5)),
        ("selector error offset window", edit_prefix_byte(baseline, first_error_start + 11, lambda _: 27)),
        ("selector bytes", edit_prefix_byte(baseline, first_error_start + 2, lambda value: value ^ 1)),
        ("immutable patch destination", edit_prefix_byte(baseline, first_patch_pc + 2, lambda value: value ^ 1)),
        ("coherent embedded-template non-lane byte", edit_prefix_byte(
            baseline,
            int(report["prefix_length"]) + non_lane_runtime_byte,
            lambda value: value ^ 1,
        )),
        ("derived runtime-length mismatch", insert_runtime_byte(baseline)),
        ("constructor table size mismatch", corrupt_table_length(baseline)),
    ]

    missed = [name for name, mutation in mutations if not rejected(mutation, args.reference_lock)]

    # The good boundary encodings must be accepted before the wrap mutants are
    # meaningful.  These use the schema's real one-instruction disassembler.
    validate_fixed_push_encoding(bytes.fromhex("61ffff"), 0xFFFF)
    validate_fixed_push_encoding(b"\x7f" + (0x10000).to_bytes(32, "big"), 0x10000)
    synthetic = [
        ("synthetic 0x10000 low-16 wrap", bytes.fromhex("610000"), 0x10000),
        ("synthetic 0xffff wrong PUSH32 width", b"\x7f" + (0xFFFF).to_bytes(32, "big"), 0xFFFF),
    ]
    missed.extend(name for name, blob, value in synthetic if not rejected_push(blob, value))

    if missed:
        raise RuntimeError("constructor falsifier(s) passed: " + ", ".join(missed))
    print(
        "OK — Lido constructor falsifiers: "
        f"{len(mutations) + len(synthetic)} evaluator/byte/shape/overflow controls rejected"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(
            "REGRESSION — Lido constructor falsifiers: " + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
