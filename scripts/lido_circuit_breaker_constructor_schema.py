#!/usr/bin/env python3
"""Independent emitted-byte schema for the Lido constructor.

The authoritative Lean evaluator owns every Blanc artifact and immutable
offset consumed here.  This module does not compile a second constructor and
does not trust raw opcode searches: it disassembles the emitted prefix so PUSH
immediates can never masquerade as executable instructions.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, NoReturn, Sequence


REPO = Path(__file__).resolve().parents[1]
REFERENCE_LOCK = REPO / "scripts" / "lido-circuit-breaker-reference.json"

BYTE_LABELS = (
    "creation-template",
    "official-create",
    "official-runtime",
    "independent-create",
    "independent-runtime",
)
OFFSET_FIELDS = (
    "admin",
    "min-pause",
    "max-pause",
    "min-heartbeat",
    "max-heartbeat",
)
ARGUMENT_INDEX = {
    "admin": 0,
    "min-pause": 1,
    "max-pause": 2,
    "min-heartbeat": 3,
    "max-heartbeat": 4,
}
CONSTRUCTOR_TABLE_NAMES = (
    "main",
    "empty-revert",
    "error-admin-zero",
    "error-min-pause-zero",
    "error-min-pause-above-max",
    "error-min-heartbeat-zero",
    "error-min-heartbeat-above-max",
    "error-pause-below-min",
    "error-pause-above-max",
    "error-heartbeat-below-min",
    "error-heartbeat-above-max",
)
TABLE_ERROR_TO_LOCK_ERROR = {
    "error-admin-zero": "AdminZero",
    "error-min-pause-zero": "MinPauseDurationZero",
    "error-min-pause-above-max": "MinPauseDurationExceedsMax",
    "error-min-heartbeat-zero": "MinHeartbeatIntervalZero",
    "error-min-heartbeat-above-max": "MinHeartbeatIntervalExceedsMax",
    "error-pause-below-min": "PauseDurationBelowMin",
    "error-pause-above-max": "PauseDurationAboveMax",
    "error-heartbeat-below-min": "HeartbeatIntervalBelowMin",
    "error-heartbeat-above-max": "HeartbeatIntervalAboveMax",
}

MAIN_BYTES = 495
EMPTY_REVERT_BYTES = 4
SELECTOR_ERROR_BYTES = 13
EXPECTED_CODECOPY_PCS = (27, 137)
EXPECTED_RETURN_PC = 439
RUNTIME_BASE = 224
PUSH2_BOUND = 1 << 16
EIP3860_LIMIT = 49_152

REQUIRED_ROWS = set(BYTE_LABELS) | {
    "constructor-table-layout",
    "offset-metadata-valid",
    "patch-controls-valid",
    "limits",
    "sizes",
} | {f"offsets-{field}" for field in OFFSET_FIELDS}


class SchemaError(RuntimeError):
    """A fail-closed constructor-schema violation."""


def die(message: str) -> NoReturn:
    raise SchemaError(message)


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
        raise SchemaError(f"{context}: malformed hex") from exc


@dataclass(frozen=True)
class TableEntry:
    name: str
    start: int
    length: int


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    immediate: bytes

    @property
    def width(self) -> int:
        return len(self.immediate)

    @property
    def size(self) -> int:
        return 1 + self.width

    @property
    def end(self) -> int:
        return self.pc + self.size

    @property
    def push_value(self) -> int | None:
        if self.opcode == 0x5F:
            return 0
        if 0x60 <= self.opcode <= 0x7F:
            return int.from_bytes(self.immediate, "big")
        return None


@dataclass(frozen=True)
class EvaluatorData:
    artifacts: Mapping[str, bytes]
    table: tuple[TableEntry, ...]
    offsets: Mapping[str, tuple[int, ...]]
    offset_metadata_valid: bool
    patch_controls_valid: bool
    limits: tuple[int, int, int]
    sizes: tuple[int, ...]


@dataclass(frozen=True)
class LockData:
    argument_bytes: int
    selectors: Mapping[str, bytes]
    constructor_suffixes: Mapping[str, bytes]


def parse_table(parts: Sequence[str]) -> tuple[TableEntry, ...]:
    if len(parts) != 3:
        die("constructor-table-layout: malformed evaluator row")
    count = parse_nat(parts[1], "constructor-table-layout count")
    descriptors = [] if parts[2] == "-" else parts[2].split(",")
    if len(descriptors) != count:
        die("constructor-table-layout: descriptor count mismatch")
    entries = []
    for descriptor in descriptors:
        fields = descriptor.split("|")
        if len(fields) != 3 or not fields[0]:
            die("constructor-table-layout: malformed descriptor")
        entries.append(TableEntry(
            fields[0],
            parse_nat(fields[1], f"constructor table start {fields[0]}"),
            parse_nat(fields[2], f"constructor table length {fields[0]}"),
        ))
    if len({entry.name for entry in entries}) != len(entries):
        die("constructor-table-layout: duplicate entry name")
    if len({entry.start for entry in entries}) != len(entries):
        die("constructor-table-layout: duplicate entry start")
    return tuple(entries)


def parse_evaluator(text: str) -> EvaluatorData:
    rows: dict[str, list[str]] = {}
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        if not raw_line.strip():
            continue
        if raw_line != raw_line.strip():
            die(f"evaluator line {line_number}: leading or trailing whitespace")
        parts = raw_line.split()
        if not parts or not parts[0]:
            die(f"evaluator line {line_number}: malformed row")
        label = parts[0]
        if label in rows:
            die(f"duplicate evaluator row {label}")
        rows[label] = parts

    missing = sorted(REQUIRED_ROWS - rows.keys())
    if missing:
        die("missing evaluator row(s): " + ", ".join(missing))

    artifacts: dict[str, bytes] = {}
    for label in BYTE_LABELS:
        parts = rows[label]
        if len(parts) != 3:
            die(f"{label}: malformed evaluator byte row")
        declared = parse_nat(parts[1], f"{label} length")
        artifact = parse_hex_bytes(parts[2], label)
        if len(artifact) != declared:
            die(f"{label}: declared byte length mismatch")
        artifacts[label] = artifact

    table = parse_table(rows["constructor-table-layout"])

    offsets: dict[str, tuple[int, ...]] = {}
    for field in OFFSET_FIELDS:
        label = f"offsets-{field}"
        parts = rows[label]
        if len(parts) != 3:
            die(f"{label}: malformed evaluator offset row")
        count = parse_nat(parts[1], f"{label} count")
        values = tuple(
            parse_nat(token, f"{label} value")
            for token in ([] if parts[2] == "-" else parts[2].split(","))
        )
        if len(values) != count:
            die(f"{label}: offset count mismatch")
        if len(set(values)) != len(values):
            die(f"{label}: duplicate immutable offset")
        offsets[field] = values

    def parse_bool(label: str) -> bool:
        parts = rows[label]
        if len(parts) != 2 or parts[1] not in {"true", "false"}:
            die(f"{label}: malformed evaluator Boolean row")
        return parts[1] == "true"

    limit_parts = rows["limits"]
    if len(limit_parts) != 4:
        die("limits: malformed evaluator row")
    limits = tuple(parse_nat(value, "limits value") for value in limit_parts[1:])

    size_parts = rows["sizes"]
    if len(size_parts) != 9:
        die("sizes: malformed evaluator row")
    sizes = tuple(parse_nat(value, "sizes value") for value in size_parts[1:])

    return EvaluatorData(
        artifacts=artifacts,
        table=table,
        offsets=offsets,
        offset_metadata_valid=parse_bool("offset-metadata-valid"),
        patch_controls_valid=parse_bool("patch-controls-valid"),
        limits=(limits[0], limits[1], limits[2]),
        sizes=sizes,
    )


def parse_lock(path: Path = REFERENCE_LOCK) -> LockData:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SchemaError(f"reference lock is unavailable or malformed: {path}") from exc
    if not isinstance(value, dict):
        die("reference lock: expected a top-level object")

    try:
        constructor = value["abi"]["constructor"]
        argument_types = constructor["argumentTypes"]
        errors = value["abi"]["errors"]
        worlds = value["artifacts"]["worlds"]
    except (KeyError, TypeError) as exc:
        raise SchemaError("reference lock: missing constructor/error/world data") from exc

    expected_types = ["address"] + ["uint256"] * 6
    if argument_types != expected_types:
        die("reference lock: constructor is not the exact seven-word static ABI")
    if constructor.get("payable") is not False:
        die("reference lock: constructor unexpectedly payable")

    selectors: dict[str, bytes] = {}
    if not isinstance(errors, list):
        die("reference lock: errors must be a list")
    for row in errors:
        if not isinstance(row, dict):
            die("reference lock: malformed error row")
        try:
            name = row["entry"]["name"]
            selector_token = row["selector"]
        except (KeyError, TypeError) as exc:
            raise SchemaError("reference lock: malformed error identity") from exc
        if not isinstance(name, str) or not isinstance(selector_token, str) or not selector_token.startswith("0x"):
            die("reference lock: malformed error name or selector")
        selector = parse_hex_bytes(selector_token[2:], f"reference selector {name}")
        if len(selector) != 4:
            die(f"reference lock: selector {name} is not four bytes")
        if name in selectors:
            die(f"reference lock: duplicate error {name}")
        selectors[name] = selector

    suffixes: dict[str, bytes] = {}
    if not isinstance(worlds, list):
        die("reference lock: artifact worlds must be a list")
    for row in worlds:
        if not isinstance(row, dict):
            die("reference lock: malformed artifact world")
        name = row.get("name")
        suffix_token = row.get("constructorSuffix")
        if not isinstance(name, str) or not isinstance(suffix_token, str) or not suffix_token.startswith("0x"):
            die("reference lock: malformed constructor suffix identity")
        suffixes[name] = parse_hex_bytes(
            suffix_token[2:], f"reference constructor suffix {name}")

    expected_errors = set(TABLE_ERROR_TO_LOCK_ERROR.values())
    if not expected_errors <= selectors.keys():
        die("reference lock: constructor error selector surface incomplete")
    if set(suffixes) != {"official-mainnet", "independent-parameters"}:
        die("reference lock: constructor parameter worlds incomplete")

    argument_bytes = 32 * len(argument_types)
    if any(len(suffix) != argument_bytes for suffix in suffixes.values()):
        die("reference lock: constructor suffix is not seven words")
    return LockData(argument_bytes, selectors, suffixes)


def disassemble(code: bytes, start: int = 0, end: int | None = None) -> tuple[Instruction, ...]:
    end = len(code) if end is None else end
    if not 0 <= start <= end <= len(code):
        die("invalid disassembly interval")
    instructions: list[Instruction] = []
    pc = start
    while pc < end:
        opcode = code[pc]
        width = opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0
        next_pc = pc + 1 + width
        if next_pc > end:
            die(f"truncated PUSH at byte {pc}")
        instructions.append(Instruction(pc, opcode, code[pc + 1:next_pc]))
        pc = next_pc
    return tuple(instructions)


def require_opcode(inst: Instruction, opcode: int, context: str) -> None:
    if inst.opcode != opcode:
        die(f"{context}: expected opcode 0x{opcode:02x} at PC {inst.pc}")


def require_push(inst: Instruction, width: int, value: int, context: str) -> None:
    expected_opcode = 0x5F if width == 0 else 0x5F + width
    if inst.opcode != expected_opcode or inst.width != width or inst.push_value != value:
        die(
            f"{context}: expected PUSH{width} value {value} at PC {inst.pc}, "
            f"got opcode 0x{inst.opcode:02x} value {inst.push_value}"
        )


def fixed_push_encoding(value: int) -> bytes:
    """The audited no-wrap policy for layout coordinates.

    PUSH2 is deliberately fixed-width below its strict bound.  Larger EVM
    words use the exact 32-byte fallback; values outside the EVM word domain
    are rejected instead of being reduced modulo 2^256.
    """
    if not 0 <= value < 1 << 256:
        die("fixed push value lies outside the EVM word domain")
    if value < PUSH2_BOUND:
        return b"\x61" + value.to_bytes(2, "big")
    return b"\x7f" + value.to_bytes(32, "big")


def validate_fixed_push_encoding(blob: bytes, value: int) -> None:
    expected = fixed_push_encoding(value)
    instructions = disassemble(blob)
    if len(instructions) != 1 or instructions[0].end != len(blob):
        die("synthetic fixed push is not exactly one instruction")
    if blob != expected:
        die(f"synthetic fixed push wrapped or used the wrong width for {value}")


def find_guard(instructions: Sequence[Instruction], full_length: int) -> Instruction:
    matches = []
    for index in range(len(instructions) - 4):
        first, codesize, lt, target, jumpi = instructions[index:index + 5]
        if (first.opcode == 0x61 and first.push_value == full_length and
                codesize.opcode == 0x38 and lt.opcode == 0x10 and
                target.opcode == 0x61 and jumpi.opcode == 0x57):
            matches.append(first)
    if len(matches) != 1:
        die("constructor length guard is absent or ambiguous")
    return matches[0]


def validate_evaluator(text: str, lock_path: Path = REFERENCE_LOCK) -> Mapping[str, object]:
    data = parse_evaluator(text)
    lock = parse_lock(lock_path)
    artifacts = data.artifacts
    creation = artifacts["creation-template"]
    official_create = artifacts["official-create"]
    independent_create = artifacts["independent-create"]
    official_runtime = artifacts["official-runtime"]
    independent_runtime = artifacts["independent-runtime"]

    if len(official_runtime) != len(independent_runtime):
        die("runtime parameter worlds changed compiler length")
    if official_runtime == independent_runtime:
        die("runtime parameter worlds are byte-identical; parameter lanes are vacuous")
    runtime_length = len(official_runtime)
    if len(creation) <= runtime_length:
        die("creation template does not contain a positive constructor prefix")
    prefix_length = len(creation) - runtime_length
    runtime_template = creation[prefix_length:]
    if len(runtime_template) != runtime_length:
        die("embedded runtime template length mismatch")

    if not official_create.startswith(creation) or not independent_create.startswith(creation):
        die("full create input does not begin with the emitted creation template")
    official_suffix = official_create[len(creation):]
    independent_suffix = independent_create[len(creation):]
    if official_suffix != lock.constructor_suffixes["official-mainnet"]:
        die("official constructor suffix differs from the reference lock")
    if independent_suffix != lock.constructor_suffixes["independent-parameters"]:
        die("independent constructor suffix differs from the reference lock")
    if len(official_suffix) != lock.argument_bytes or len(independent_suffix) != lock.argument_bytes:
        die("full create input is not creation template plus seven words")

    eip170_limit, eip3860_limit, evaluator_argument_bytes = data.limits
    if eip3860_limit != EIP3860_LIMIT:
        die("evaluator EIP-3860 limit differs from the protocol limit")
    if evaluator_argument_bytes != lock.argument_bytes or evaluator_argument_bytes != RUNTIME_BASE:
        die("evaluator constructor argument size differs from the locked seven-word ABI")
    if runtime_length > eip170_limit:
        die("runtime exceeds the evaluator EIP-170 limit")
    if len(creation) > eip3860_limit or len(official_create) > eip3860_limit or len(independent_create) > eip3860_limit:
        die("creation artifact exceeds EIP-3860")

    if data.sizes != (
        runtime_length,
        len(official_runtime),
        len(independent_runtime),
        eip170_limit - len(official_runtime),
        eip170_limit - len(independent_runtime),
        eip3860_limit - len(creation),
        eip3860_limit - len(official_create),
        eip3860_limit - len(independent_create),
    ):
        die("evaluator size/headroom row disagrees with independently derived lengths")

    args_offset = prefix_length + runtime_length
    full_length = args_offset + lock.argument_bytes
    if len(official_create) != full_length or len(independent_create) != full_length:
        die("independently derived full-create length mismatch")

    if tuple(entry.name for entry in data.table) != CONSTRUCTOR_TABLE_NAMES:
        die("constructor table names or source-order error slots drifted")
    expected_table_lengths = (MAIN_BYTES, EMPTY_REVERT_BYTES) + (SELECTOR_ERROR_BYTES,) * 9
    cursor = 0
    if len(data.table) != len(expected_table_lengths):
        die("constructor table entry count drifted")
    for entry, expected_length in zip(data.table, expected_table_lengths):
        if entry.start != cursor or entry.length != expected_length:
            die(f"constructor table layout drifted at {entry.name}")
        cursor += entry.length
    if cursor != prefix_length:
        die("constructor table does not cover the independently derived prefix")

    prefix = creation[:prefix_length]
    instructions = disassemble(prefix)
    boundary_pcs = {inst.pc for inst in instructions} | {prefix_length}
    for entry in data.table:
        if entry.start not in boundary_pcs or entry.start + entry.length not in boundary_pcs:
            die(f"constructor table entry {entry.name} is not instruction-aligned")

    empty_entry = data.table[1]
    if prefix[empty_entry.start:empty_entry.start + empty_entry.length] != bytes.fromhex("5b5f5ffd"):
        die("constructor empty-revert entry changed shape")
    for entry in data.table[2:]:
        lock_name = TABLE_ERROR_TO_LOCK_ERROR[entry.name]
        selector = lock.selectors[lock_name]
        expected = b"\x5b\x63" + selector + bytes.fromhex("5f526004601cfd")
        actual = prefix[entry.start:entry.start + entry.length]
        if actual != expected:
            die(f"constructor selector reverter {lock_name} changed bytes/window")

    main_end = data.table[0].start + data.table[0].length
    main = tuple(inst for inst in instructions if inst.pc < main_end)
    if not main or main[0].pc != 0 or main[0].opcode != 0x5B:
        die("constructor main table entry lacks its JUMPDEST")
    index_by_pc = {inst.pc: index for index, inst in enumerate(main)}

    codecopies = tuple(inst for inst in main if inst.opcode == 0x39)
    if tuple(inst.pc for inst in codecopies) != EXPECTED_CODECOPY_PCS:
        die("constructor must have exactly the approved argument/runtime CODECOPY sites")
    args_copy, runtime_copy = codecopies
    args_copy_index = index_by_pc[args_copy.pc]
    runtime_copy_index = index_by_pc[runtime_copy.pc]
    if args_copy_index < 3 or runtime_copy_index < 3:
        die("constructor CODECOPY lacks three operands")

    args_operands = main[args_copy_index - 3:args_copy_index]
    require_push(args_operands[0], 1, lock.argument_bytes, "argument CODECOPY length")
    require_push(args_operands[1], 2, args_offset, "argument CODECOPY source")
    require_push(args_operands[2], 0, 0, "argument CODECOPY destination")

    runtime_operands = main[runtime_copy_index - 3:runtime_copy_index]
    require_push(runtime_operands[0], 2, runtime_length, "runtime CODECOPY length")
    require_push(runtime_operands[1], 2, prefix_length, "runtime CODECOPY source")
    require_push(runtime_operands[2], 1, RUNTIME_BASE, "runtime CODECOPY destination")

    between = main[args_copy_index + 1:runtime_copy_index]
    if sum(inst.opcode == 0x57 for inst in between) != 10:
        die("runtime CODECOPY is not after exactly ten canonical/source validation JUMPI sites")
    if sum(inst.opcode == 0x57 for inst in main) != 12:
        die("constructor main does not have outer, length, and ten validation branches")

    guard_push = find_guard(main, full_length)
    if guard_push.pc >= args_copy.pc:
        die("constructor length guard does not precede argument decoding")

    returns = tuple(inst for inst in main if inst.opcode == 0xF3)
    if tuple(inst.pc for inst in returns) != (EXPECTED_RETURN_PC,):
        die("constructor must have exactly the approved RETURN site")
    return_index = index_by_pc[returns[0].pc]
    if return_index < 2:
        die("constructor RETURN lacks size/base operands")
    require_push(main[return_index - 2], 2, runtime_length, "RETURN runtime length")
    require_push(main[return_index - 1], 1, RUNTIME_BASE, "RETURN runtime base")

    if not data.offset_metadata_valid or not data.patch_controls_valid:
        die("evaluator immutable patch controls are not green")
    all_offsets = [offset for field in OFFSET_FIELDS for offset in data.offsets[field]]
    if len(all_offsets) != 12 or len(set(all_offsets)) != 12:
        die("constructor does not have exactly twelve distinct generated immutable offsets")
    lane_bytes: set[int] = set()
    for offset in all_offsets:
        if offset + 32 > runtime_length:
            die(f"immutable offset {offset} escapes the runtime")
        span = set(range(offset, offset + 32))
        if lane_bytes & span:
            die(f"immutable word span at {offset} overlaps another parameter lane")
        lane_bytes.update(span)
        if runtime_template[offset:offset + 32] != bytes(32):
            die(f"embedded runtime template lane {offset} is not the zero-parameter word")

    def patch_template(constructor_suffix: bytes) -> bytes:
        words = [
            constructor_suffix[index:index + 32]
            for index in range(0, lock.argument_bytes, 32)
        ]
        if len(words) != 7 or any(len(word) != 32 for word in words):
            die("locked constructor suffix does not split into seven words")
        patched = bytearray(runtime_template)
        for field in OFFSET_FIELDS:
            word = words[ARGUMENT_INDEX[field]]
            for offset in data.offsets[field]:
                patched[offset:offset + 32] = word
        return bytes(patched)

    if patch_template(official_suffix) != official_runtime:
        die("embedded template plus official immutable lanes does not equal official runtime")
    if patch_template(independent_suffix) != independent_runtime:
        die("embedded template plus independent immutable lanes does not equal independent runtime")
    for index in range(runtime_length):
        if index not in lane_bytes and not (
                runtime_template[index] == official_runtime[index] == independent_runtime[index]):
            die(f"non-immutable runtime byte {index} differs across parameter worlds")

    patch_push_pcs: list[int] = []
    expected_patch_destinations: list[int] = []
    for field in OFFSET_FIELDS:
        argument_offset = 32 * ARGUMENT_INDEX[field]
        for offset in data.offsets[field]:
            destination = RUNTIME_BASE + offset
            expected_patch_destinations.append(destination)
            matches = []
            for index in range(3, len(main)):
                if main[index].opcode != 0x52:
                    continue
                load_push, mload, destination_push = main[index - 3:index]
                expected_arg_width = 0 if argument_offset == 0 else 1
                if (load_push.push_value == argument_offset and
                        load_push.width == expected_arg_width and
                        mload.opcode == 0x51 and
                        destination_push.opcode == 0x61 and
                        destination_push.push_value == destination):
                    matches.append(destination_push)
            if len(matches) != 1:
                die(f"immutable patch {field}@{offset} is absent or duplicated")
            if matches[0].pc <= runtime_copy.pc:
                die(f"immutable patch {field}@{offset} precedes runtime CODECOPY")
            patch_push_pcs.append(matches[0].pc)

    event_scratch = ((RUNTIME_BASE + runtime_length + 31) // 32) * 32
    if event_scratch % 32 != 0 or not RUNTIME_BASE + runtime_length <= event_scratch < RUNTIME_BASE + runtime_length + 32:
        die("constructor event scratch is not the first aligned word above runtime")

    mstore_destinations = []
    for index, inst in enumerate(main):
        if inst.opcode != 0x52:
            continue
        if index == 0 or main[index - 1].push_value is None:
            die(f"constructor MSTORE at PC {inst.pc} lacks a literal destination")
        mstore_destinations.append(main[index - 1].push_value)
    expected_mstores = Counter(expected_patch_destinations + [
        event_scratch, event_scratch + 32, event_scratch, event_scratch + 32,
    ])
    if Counter(mstore_destinations) != expected_mstores:
        die("constructor MSTORE destinations do not equal patches plus event scratch")

    logs = tuple(inst for inst in main if 0xA0 <= inst.opcode <= 0xA4)
    if tuple(inst.opcode for inst in logs) != (0xA2, 0xA1, 0xA1):
        die("constructor log count or order drifted")
    first_log_index = index_by_pc[logs[0].pc]
    require_push(main[first_log_index - 2], 1, 128, "initialized-event data length")
    require_push(main[first_log_index - 1], 1, 32, "initialized-event data offset")
    for log in logs[1:]:
        index = index_by_pc[log.pc]
        require_push(main[index - 2], 1, 64, "configuration-event data length")
        require_push(main[index - 1], 2, event_scratch, "configuration-event scratch offset")

    layout_values = (
        prefix_length,
        runtime_length,
        args_offset,
        full_length,
        RUNTIME_BASE,
        event_scratch,
        event_scratch + 32,
        *expected_patch_destinations,
    )
    if any(not 0 <= value < PUSH2_BOUND for value in layout_values):
        die("constructor layout coordinate exceeds strict PUSH2 range")

    # The synthetic boundary is intentionally checked by the same decoder used
    # for emitted code.  Falsifiers exercise wrong-width and low-16 wrap forms.
    validate_fixed_push_encoding(bytes.fromhex("61ffff"), 0xFFFF)
    validate_fixed_push_encoding(b"\x7f" + (0x10000).to_bytes(32, "big"), 0x10000)

    return {
        "prefix_length": prefix_length,
        "runtime_length": runtime_length,
        "creation_length": len(creation),
        "full_length": full_length,
        "args_offset": args_offset,
        "runtime_base": RUNTIME_BASE,
        "event_scratch": event_scratch,
        "guard_push_pc": guard_push.pc,
        "args_copy_start": args_operands[0].pc,
        "args_copy_pc": args_copy.pc,
        "args_source_push_pc": args_operands[1].pc,
        "runtime_copy_start": runtime_operands[0].pc,
        "runtime_copy_pc": runtime_copy.pc,
        "runtime_base_push_pc": runtime_operands[2].pc,
        "return_pc": returns[0].pc,
        "return_base_push_pc": main[return_index - 1].pc,
        "patch_push_pcs": tuple(patch_push_pcs),
        "lane_byte_offsets": tuple(sorted(lane_bytes)),
        "table": data.table,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path, help="stdout captured from the authoritative Lean artifact evaluator")
    parser.add_argument("--reference-lock", type=Path, default=REFERENCE_LOCK)
    args = parser.parse_args(argv)
    try:
        text = args.artifacts.read_text(encoding="utf-8")
    except OSError as exc:
        raise SchemaError(f"cannot read evaluator output: {args.artifacts}") from exc
    report = validate_evaluator(text, args.reference_lock)
    print(
        "OK — Lido constructor byte schema: "
        f"prefix={report['prefix_length']} runtime={report['runtime_length']} "
        f"creation={report['creation_length']} full={report['full_length']} "
        "copy=27/137 validations=10 return=439 patches=12 errors=9x13"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(
            "REGRESSION — Lido constructor byte schema: " + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
