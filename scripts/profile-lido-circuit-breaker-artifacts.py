#!/usr/bin/env python3
"""Generate/check the optimized Lido CircuitBreaker byte/opcode ownership ledger.

Blanc bytes come only from the Lean evaluator supplied with --blanc-artifacts;
Solidity bytes come only from the schema-v2 reference lock.  The committed
optimized ledger contains lengths, hashes, partitions, opcode summaries, and a
derived comparison to the separately immutable launch ledger.  Neither ledger
contains a second behavior-bearing bytecode literal.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Dict, List, Mapping, MutableSequence, NoReturn, Sequence, Tuple

from lido_circuit_breaker_artifact_profile_schema import (
    EXPECTED_OPTIMIZED_CONSTRUCTOR_TABLE, EXPECTED_OPTIMIZED_ENDPOINT_SPANS,
    EXPECTED_OPTIMIZED_ENDPOINT_TOTAL_BYTES,
    EXPECTED_OPTIMIZED_FIXED_COORDINATE_PUSHES,
    EXPECTED_OPTIMIZED_IDENTITIES, EXPECTED_OPTIMIZED_IMMUTABLE_OFFSETS,
    EXPECTED_OPTIMIZED_RUNTIME_TABLE, FROZEN_LEDGER_SHA256, OPTIMIZED_SCHEMA,
    REFERENCE_LOCK_SHA256, SCHEMA, validate_optimized_rendered,
    validate_rendered,
)


REPO = Path(__file__).resolve().parents[1]
LOCK_PATH = REPO / "scripts" / "lido-circuit-breaker-reference.json"
COMPILER_OUTPUT_PATH = REPO / "scripts" / "reference" / "lido-circuit-breaker" / "inputs" / "std-json-output.json"
FROZEN_LEDGER_PATH = REPO / "scripts" / "fixtures" / "lido-circuit-breaker" / "artifact-profile-baseline.json"
OPTIMIZED_LEDGER_PATH = REPO / "scripts" / "fixtures" / "lido-circuit-breaker" / "artifact-profile-optimized.json"


OPCODES = {
    0x00: "STOP", 0x01: "ADD", 0x02: "MUL", 0x03: "SUB", 0x04: "DIV",
    0x05: "SDIV", 0x06: "MOD", 0x07: "SMOD", 0x08: "ADDMOD",
    0x09: "MULMOD", 0x0A: "EXP", 0x0B: "SIGNEXTEND", 0x10: "LT",
    0x11: "GT", 0x12: "SLT", 0x13: "SGT", 0x14: "EQ", 0x15: "ISZERO",
    0x16: "AND", 0x17: "OR", 0x18: "XOR", 0x19: "NOT", 0x1A: "BYTE",
    0x1B: "SHL", 0x1C: "SHR", 0x1D: "SAR", 0x20: "KECCAK256",
    0x30: "ADDRESS", 0x31: "BALANCE", 0x32: "ORIGIN", 0x33: "CALLER",
    0x34: "CALLVALUE", 0x35: "CALLDATALOAD", 0x36: "CALLDATASIZE",
    0x37: "CALLDATACOPY", 0x38: "CODESIZE", 0x39: "CODECOPY",
    0x3A: "GASPRICE", 0x3B: "EXTCODESIZE", 0x3C: "EXTCODECOPY",
    0x3D: "RETURNDATASIZE", 0x3E: "RETURNDATACOPY", 0x3F: "EXTCODEHASH",
    0x40: "BLOCKHASH", 0x41: "COINBASE", 0x42: "TIMESTAMP", 0x43: "NUMBER",
    0x44: "PREVRANDAO", 0x45: "GASLIMIT", 0x46: "CHAINID",
    0x47: "SELFBALANCE", 0x48: "BASEFEE", 0x49: "BLOBHASH",
    0x4A: "BLOBBASEFEE", 0x50: "POP", 0x51: "MLOAD", 0x52: "MSTORE",
    0x53: "MSTORE8", 0x54: "SLOAD", 0x55: "SSTORE", 0x56: "JUMP",
    0x57: "JUMPI", 0x58: "PC", 0x59: "MSIZE", 0x5A: "GAS",
    0x5B: "JUMPDEST", 0x5C: "TLOAD", 0x5D: "TSTORE", 0x5E: "MCOPY",
    0x5F: "PUSH0", 0xF0: "CREATE", 0xF1: "CALL", 0xF2: "CALLCODE",
    0xF3: "RETURN", 0xF4: "DELEGATECALL", 0xF5: "CREATE2",
    0xFA: "STATICCALL", 0xFD: "REVERT", 0xFE: "INVALID",
    0xFF: "SELFDESTRUCT",
}
for _n in range(1, 33):
    OPCODES[0x5F + _n] = f"PUSH{_n}"
for _n in range(1, 17):
    OPCODES[0x7F + _n] = f"DUP{_n}"
    OPCODES[0x8F + _n] = f"SWAP{_n}"
for _n in range(5):
    OPCODES[0xA0 + _n] = f"LOG{_n}"


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identity(data: bytes) -> Mapping[str, object]:
    return {"byteLength": len(data), "sha256": sha(data)}


def parse_layout(parts: Sequence[str], label: str) -> List[Mapping[str, object]]:
    if len(parts) != 3:
        die(f"malformed evaluator layout row {label}")
    rows = [] if parts[2] == "-" else parts[2].split(",")
    result = []
    for row in rows:
        fields = row.split("|")
        if len(fields) != 3:
            die(f"malformed evaluator layout descriptor {label}")
        result.append({"name": fields[0], "start": int(fields[1]),
                       "byteLength": int(fields[2])})
    if len(result) != int(parts[1]):
        die(f"evaluator layout count mismatch for {label}")
    return result


def parse_evaluator(text: str) -> Mapping[str, object]:
    artifacts: Dict[str, bytes] = {}
    layouts: Dict[str, object] = {}
    offsets: Dict[str, List[int]] = {}
    selectors: List[str] | None = None
    seen = set()
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        label = parts[0]
        if label in seen and (label in {
                "creation-template", "official-create", "official-runtime",
                "independent-create", "independent-runtime", "runtime-table-layout",
                "runtime-endpoint-layout", "constructor-table-layout", "selectors"}
                or label.startswith("offsets-")):
            die(f"duplicate evaluator row {label}")
        seen.add(label)
        if label in {"creation-template", "official-create", "official-runtime",
                     "independent-create", "independent-runtime"}:
            if len(parts) != 3:
                die(f"malformed evaluator byte row {label}")
            raw = bytes.fromhex(parts[2])
            if len(raw) != int(parts[1]):
                die(f"evaluator byte length mismatch for {label}")
            artifacts[label] = raw
        elif label in {"runtime-table-layout", "runtime-endpoint-layout",
                       "constructor-table-layout"}:
            layouts[label] = parse_layout(parts, label)
        elif label == "selectors":
            selectors = parts[2].split(",")
            if len(selectors) != int(parts[1]):
                die("evaluator selector count mismatch")
        elif label.startswith("offsets-"):
            values = [] if parts[1] == "0" else [int(v) for v in parts[2].split(",")]
            if len(values) != int(parts[1]):
                die(f"evaluator immutable count mismatch for {label}")
            offsets[label.removeprefix("offsets-")] = values
        elif label in {"offset-metadata-valid", "patch-controls-valid"}:
            layouts[label] = parts[1] == "true"
    required_artifacts = {"creation-template", "official-create", "official-runtime",
                          "independent-create", "independent-runtime"}
    if set(artifacts) != required_artifacts:
        die(f"evaluator artifact rows incomplete: {sorted(artifacts)}")
    if set(layouts) != {"runtime-table-layout", "runtime-endpoint-layout",
                        "constructor-table-layout", "offset-metadata-valid",
                        "patch-controls-valid"}:
        die("evaluator layout/control rows incomplete")
    if selectors is None or len(selectors) != 17:
        die("evaluator selector surface is incomplete")
    if offsets != EXPECTED_OPTIMIZED_IMMUTABLE_OFFSETS:
        die("evaluator immutable offsets drifted from the optimized candidate")
    if layouts["runtime-table-layout"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_OPTIMIZED_RUNTIME_TABLE]:
        die("evaluator runtime table drifted from the optimized candidate")
    if layouts["runtime-endpoint-layout"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_OPTIMIZED_ENDPOINT_SPANS]:
        die("evaluator runtime endpoint layout drifted from the optimized candidate")
    if layouts["constructor-table-layout"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_OPTIMIZED_CONSTRUCTOR_TABLE]:
        die("evaluator constructor table drifted from the optimized candidate")
    if layouts["offset-metadata-valid"] is not True or layouts["patch-controls-valid"] is not True:
        die("evaluator immutable patch controls are not green")
    return {"artifacts": artifacts, "layouts": layouts,
            "offsets": offsets, "selectors": selectors}


def disassemble(code: bytes, start: int = 0, end: int | None = None) -> List[Mapping[str, object]]:
    end = len(code) if end is None else end
    if not 0 <= start <= end <= len(code):
        die("invalid disassembly interval")
    rows = []
    pc = start
    while pc < end:
        opcode = code[pc]
        width = opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0
        size = 1 + width
        if pc + size > end:
            die(f"truncated PUSH at byte {pc}")
        raw = code[pc:pc + size]
        rows.append({"pc": pc, "end": pc + size, "opcode": OPCODES.get(
            opcode, f"UNKNOWN_0x{opcode:02x}"), "size": size,
            "immediateBytes": width, "instructionSha256": sha(raw)})
        pc += size
    return rows


def validate_runtime_endpoint_layout(code: bytes, parsed: Mapping) -> None:
    """Fail closed unless evaluator spans are exact code-aligned leaf bodies."""
    spans = parsed["layouts"]["runtime-endpoint-layout"]
    if len(spans) != len(EXPECTED_OPTIMIZED_ENDPOINT_SPANS):
        die("evaluator runtime endpoint count drifted")
    if sum(int(span["byteLength"]) for span in spans) != EXPECTED_OPTIMIZED_ENDPOINT_TOTAL_BYTES:
        die("evaluator runtime endpoint byte coverage drifted")

    main_start = EXPECTED_OPTIMIZED_RUNTIME_TABLE[0][1]
    main_end = main_start + EXPECTED_OPTIMIZED_RUNTIME_TABLE[0][2]
    boundaries = {int(row["pc"]) for row in disassemble(code)}
    boundaries.add(len(code))
    prior_end = main_start
    for span in spans:
        start = int(span["start"])
        end = start + int(span["byteLength"])
        if not main_start <= start < end <= main_end:
            die(f"evaluator endpoint span escapes runtime main: [{start},{end})")
        if start < prior_end:
            die(f"evaluator endpoint spans overlap or are not in compiler byte order at {start}")
        if start not in boundaries or end not in boundaries:
            die(f"evaluator endpoint span is not instruction-aligned: [{start},{end})")
        prior_end = end

    for field, offsets in parsed["offsets"].items():
        for offset in offsets:
            if not any(int(span["start"]) <= offset and
                       offset + 32 <= int(span["start"]) + int(span["byteLength"])
                       for span in spans):
                die(f"immutable interval {field}@{offset} lies outside every endpoint")


def disassembly_summary(code: bytes, segments: Sequence[Tuple[str, int, int]]) -> Mapping[str, object]:
    summaries = []
    all_rows = []
    for role, start, end in segments:
        rows = disassemble(code, start, end)
        all_rows.extend(rows)
        counts = Counter(row["opcode"] for row in rows)
        summaries.append({
            "role": role, "start": start, "end": end, "byteLength": end - start,
            "instructionCount": len(rows), "opcodeHistogram": dict(sorted(counts.items())),
            "pushImmediateBytes": sum(int(row["immediateBytes"]) for row in rows),
        })
    stream = "\n".join(
        f'{row["pc"]}:{row["opcode"]}:{row["size"]}:{row["instructionSha256"]}'
        for row in all_rows).encode()
    return {
        "segments": summaries, "instructionCount": len(all_rows),
        "instructionStreamSha256": sha(stream),
        "unknownOpcodeCount": sum(str(row["opcode"]).startswith("UNKNOWN_") for row in all_rows),
    }


def metadata_start(runtime: bytes) -> int:
    if len(runtime) < 3:
        die("Solidity runtime is too short for metadata")
    cbor_length = int.from_bytes(runtime[-2:], "big")
    cbor_start = len(runtime) - 2 - cbor_length
    start = cbor_start - 1
    if start < 0 or runtime[start] != 0xFE:
        die("locked Solidity runtime has no exact CBOR metadata sentinel")
    return start


Mark = Tuple[str, str, str, str]


def blank_marks(length: int, mark: Mark) -> List[Mark]:
    return [mark] * length


def paint(marks: MutableSequence[Mark], start: int, end: int, mark: Mark) -> None:
    if not 0 <= start < end <= len(marks):
        die(f"invalid region paint [{start},{end})/{len(marks)}")
    marks[start:end] = [mark] * (end - start)


def materialize_regions(code: bytes, marks: Sequence[Mark],
                        instruction_rows: Sequence[Mapping[str, object]]) -> List[Mapping[str, object]]:
    if len(code) != len(marks):
        die("region mark length does not match artifact")
    result = []
    start = 0
    while start < len(code):
        mark = marks[start]
        end = start + 1
        while end < len(code) and marks[end] == mark:
            end += 1
        role, owner, certainty, evidence = mark
        overlapping = [row for row in instruction_rows if row["pc"] < end and row["end"] > start]
        starts_here = [row for row in overlapping if start <= row["pc"] < end]
        immediate_overlap = 0
        for row in overlapping:
            if row["immediateBytes"]:
                immediate_overlap += max(0, min(end, row["end"]) - max(start, row["pc"] + 1))
        histogram = Counter(row["opcode"] for row in starts_here)
        result.append({
            "id": f"r{len(result):04d}", "start": start, "end": end,
            "byteLength": end - start, "role": role, "owner": owner,
            "certainty": certainty, "evidence": evidence,
            "sha256": sha(code[start:end]),
            "disassembly": {
                "opcodeStarts": len(starts_here),
                "opcodeHistogram": dict(sorted(histogram.items())),
                "pushImmediateBytes": immediate_overlap,
                "uninterpretedDataBytes": (end - start) - sum(
                    max(0, min(end, row["end"]) - max(start, row["pc"]))
                    for row in overlapping),
            },
        })
        start = end
    return result


def table_role(name: str) -> Tuple[str, str, str]:
    if name == "main":
        return "main", "Lido-private", "exact"
    if name.startswith("error-") or name in {"fallback", "empty-revert", "bubble-revert", "arithmetic-panic"}:
        return "aux-error", "Lido-private", "exact"
    if name in {"set-pauser-kernel", "append-target", "after-old-pauser",
                "remove-target", "finish-set-pauser"}:
        return "shared-registry-kernel", "Lido-private", "exact"
    return "continuation", "Lido-private", "exact"


def blanc_runtime_marks(code: bytes, parsed: Mapping, signatures: Mapping[str, str]) -> List[Mark]:
    marks = blank_marks(len(code), (
        "unclassified", "Lido-private", "bounded-inference", "must be overwritten"))
    table = parsed["layouts"]["runtime-table-layout"]
    main = table[0]
    paint(marks, 0, main["byteLength"], (
        "dispatcher", "Blanc-common", "exact",
        "complement of evaluator-derived inline endpoint spans in Prog main"))
    for span in parsed["layouts"]["runtime-endpoint-layout"]:
        selector = str(span["name"])[-8:].lower()
        if selector not in signatures:
            die(f"endpoint layout selector {selector} is absent from the locked ABI")
        paint(marks, int(span["start"]), int(span["start"]) + int(span["byteLength"]), (
            "endpoint-body:" + signatures[selector], "Lido-private", "exact",
            "evaluator walk of the exact DispatchTree/Func source"))
    for field, offsets in parsed["offsets"].items():
        for offset in offsets:
            paint(marks, offset, offset + 32, (
                "immutable-lane:" + field, "Lido-private", "exact",
                "compiler-probed payload interval emitted by immutableWordOffsets"))
    for entry in table[1:]:
        role, owner, certainty = table_role(str(entry["name"]))
        start = int(entry["start"])
        end = start + int(entry["byteLength"])
        paint(marks, start, end, (role + ":" + str(entry["name"]), owner, certainty,
            "exact evaluator-emitted Prog table entry"))
    for entry in table:
        start = int(entry["start"])
        paint(marks, start, start + 1, (
            "table-framing:" + str(entry["name"]), "Blanc-common", "exact",
            "Prog.compile table-entry JUMPDEST"))
    if any(mark[0] == "unclassified" for mark in marks):
        die("Blanc runtime layout left unclassified bytes")
    return marks


def optimized_fixed_coordinate_pushes(prefix: bytes) -> List[Mapping[str, int]]:
    instructions = disassemble(prefix, 0, len(prefix))
    by_pc = {int(row["pc"]): row for row in instructions}
    result = []
    for pc, value in EXPECTED_OPTIMIZED_FIXED_COORDINATE_PUSHES:
        row = by_pc.get(pc)
        if row is None or row["opcode"] != "PUSH2" or int(row["end"]) != pc + 3:
            die(f"optimized constructor coordinate at {pc} is not an exact PUSH2")
        if int.from_bytes(prefix[pc + 1:pc + 3], "big") != value:
            die(f"optimized constructor coordinate value drifted at {pc}")
        result.append({"pc": pc, "value": int.from_bytes(
            prefix[pc + 1:pc + 3], "big")})
    return result


def blanc_constructor_marks(prefix: bytes, runtime_marks: Sequence[Mark]) -> List[Mark]:
    marks = blank_marks(len(prefix), (
        "constructor-main", "Lido-private", "exact",
        "evaluator-derived constructor Prog main"))
    for name, start, length in EXPECTED_OPTIMIZED_CONSTRUCTOR_TABLE[1:]:
        paint(marks, start, start + length, (
            "constructor-aux-error:" + name, "Lido-private", "exact",
            "evaluator-emitted constructor Prog table entry"))
    for fixed in optimized_fixed_coordinate_pushes(prefix):
        pc, end = int(fixed["pc"]), int(fixed["pc"]) + 3
        paint(marks, pc, pc + 1, (
            "constructor-fixed-coordinate-opcode", "Lido-private", "exact",
            "PUSH2 opcode from private pushFixedNat coordinate helper"))
        paint(marks, pc + 1, end, (
            "constructor-fixed-coordinate-immediate", "Lido-private", "exact",
            "sub-2^16 coordinate encoded in an exact two-byte immediate"))
    for name, start, _length in EXPECTED_OPTIMIZED_CONSTRUCTOR_TABLE:
        paint(marks, start, start + 1, (
            "table-framing:" + name, "Blanc-common", "exact",
            "Prog.compile table-entry JUMPDEST"))
    return marks + list(runtime_marks)


def parse_source_map(raw: str) -> List[Tuple[int, int, int]]:
    current = [-1, -1, -1]
    rows = []
    for item in raw.split(";"):
        fields = item.split(":")
        for index in range(min(3, len(fields))):
            if fields[index] != "":
                current[index] = int(fields[index])
        rows.append(tuple(current))
    return rows


def source_spans(source: str, source_name: str) -> List[Tuple[int, int, str]]:
    rows = []
    pattern = re.compile(r"\b(constructor|modifier|function)\s*(?:([A-Za-z_][A-Za-z0-9_]*)\s*)?\([^;{}]*\)\s*(?:[^;{}]*)\{")
    for match in pattern.finditer(source):
        kind, name = match.group(1), match.group(2)
        label = "constructor" if kind == "constructor" else (name or kind)
        brace = source.find("{", match.start(), match.end() + 1)
        depth, cursor = 0, brace
        while cursor < len(source):
            if source[cursor] == "{":
                depth += 1
            elif source[cursor] == "}":
                depth -= 1
                if depth == 0:
                    rows.append((match.start(), cursor + 1, source_name + "." + label))
                    break
            cursor += 1
        else:
            die(f"unclosed Solidity body for {source_name}.{label}")
    return rows


def source_label(source_id: int, offset: int,
                 spans_by_id: Mapping[int, Sequence[Tuple[int, int, str]]]) -> str | None:
    for start, end, label in spans_by_id.get(source_id, ()):
        if start <= offset < end:
            return label
    return None


def source_mapped_marks(code: bytes, executable_end: int, source_map: str,
                        spans_by_id: Mapping[int, Sequence[Tuple[int, int, str]]],
                        creation: bool) -> List[Mark]:
    base = ("constructor-scaffolding", "Solidity-compiler", "source-map",
            "locked solc source map") if creation else (
            "dispatcher-abi-generated", "Solidity-compiler", "source-map",
            "locked solc deployed source map")
    marks = blank_marks(len(code), base)
    instructions = disassemble(code, 0, executable_end)
    mappings = parse_source_map(source_map)
    if creation and len(mappings) + 1 == len(instructions):
        # solc omits the final constructor/runtime data-boundary instruction
        # from the source map; keep it in compiler scaffolding explicitly.
        mappings.append((-1, -1, -1))
    if len(mappings) < len(instructions):
        die(f"locked Solidity {'creation' if creation else 'runtime'} source map has "
            f"{len(mappings)} rows for {len(instructions)} executable instructions")
    for row, (offset, _length, source_id) in zip(instructions, mappings):
        label = source_label(source_id, offset, spans_by_id)
        if label:
            if creation:
                role = "constructor-body:" + label
            elif label.startswith("Registry."):
                role = "runtime-shared-registry-body:" + label
            else:
                role = "runtime-body:" + label
            mark = (role, "Lido-private", "source-map",
                    "locked compiler source-map interval")
        elif source_id >= 2:
            mark = (("constructor-decode-generated" if creation else "runtime-compiler-aux"),
                    "Solidity-compiler", "source-map", "locked generated-source id")
        else:
            mark = base
        paint(marks, int(row["pc"]), int(row["end"]), mark)
    return marks


def artifact(code: bytes, marks: Sequence[Mark],
             segments: Sequence[Tuple[str, int, int]]) -> Mapping[str, object]:
    rows = []
    for _role, start, end in segments:
        rows.extend(disassemble(code, start, end))
    return {"byteLength": len(code), "sha256": sha(code),
            "disassembly": disassembly_summary(code, segments),
            "regions": materialize_regions(code, marks, rows)}


def normalized_runtime_role(role: str) -> str:
    if role == "dispatcher":
        return "dispatcher"
    if role.startswith("endpoint-body:"):
        return "endpoint-bodies"
    if role.startswith("immutable-lane:"):
        return "immutable-lanes"
    if role.startswith("aux-error:"):
        return "aux-errors"
    if role.startswith("shared-registry-kernel:"):
        return "shared-registry-kernel"
    if role.startswith("continuation:"):
        return "continuations"
    if role.startswith("table-framing:"):
        return "table-framing"
    die(f"unclassified runtime attribution role {role}")


def normalized_constructor_role(role: str) -> str:
    if role == "constructor-main":
        return "constructor-main"
    if role.startswith("constructor-aux-error:"):
        return "constructor-aux-errors"
    if role in {"constructor-fixed-width-opcode",
                "constructor-fixed-coordinate-opcode"}:
        return "coordinate-push-opcodes"
    if role in {"constructor-fixed-width-immediate",
                "constructor-fixed-coordinate-immediate"}:
        return "coordinate-push-immediates"
    if role.startswith("table-framing:"):
        return "table-framing"
    die(f"unclassified constructor attribution role {role}")


def role_totals(regions: Sequence[Mapping[str, object]], classifier,
                end: int | None = None) -> Mapping[str, int]:
    totals: Counter[str] = Counter()
    covered = 0
    for region in regions:
        start = int(region["start"])
        stop = int(region["end"])
        if end is not None:
            if start >= end:
                continue
            if stop > end:
                die("attribution boundary cuts a generated region")
        length = int(region["byteLength"])
        totals[classifier(str(region["role"]))] += length
        covered += length
    expected = end if end is not None else sum(
        int(region["byteLength"]) for region in regions)
    if covered != expected:
        die(f"attribution covers {covered} of {expected} bytes")
    return dict(sorted(totals.items()))


def comparison_vector(before: Mapping[str, int], after: Mapping[str, int]) -> Mapping[str, object]:
    keys = sorted(set(before) | set(after))
    before_full = {key: int(before.get(key, 0)) for key in keys}
    after_full = {key: int(after.get(key, 0)) for key in keys}
    return {
        "baseline": before_full,
        "optimized": after_full,
        "delta": {key: after_full[key] - before_full[key] for key in keys},
    }


def before_after_attribution(baseline: Mapping[str, object],
                             optimized: Mapping[str, object],
                             optimized_prefix_len: int) -> Mapping[str, object]:
    baseline_blanc = baseline["artifacts"]["blanc"]
    optimized_blanc = optimized["artifacts"]["blanc"]
    baseline_prefix_len = (baseline_blanc["creationTemplate"]["byteLength"] -
                           baseline_blanc["runtime"]["byteLength"])
    artifact_names = {
        "runtime": (baseline_blanc["runtime"]["byteLength"],
                    optimized_blanc["runtime"]["byteLength"]),
        "constructorPrefix": (baseline_prefix_len, optimized_prefix_len),
        "creationTemplate": (baseline_blanc["creationTemplate"]["byteLength"],
                             optimized_blanc["creationTemplate"]["byteLength"]),
        "fullCreate": (baseline_blanc["fullCreate"]["byteLength"],
                       optimized_blanc["fullCreate"]["byteLength"]),
    }
    sizes = {
        name: {"baselineBytes": int(pair[0]), "optimizedBytes": int(pair[1]),
               "deltaBytes": int(pair[1]) - int(pair[0])}
        for name, pair in artifact_names.items()
    }
    baseline_runtime = role_totals(
        baseline_blanc["runtime"]["regions"], normalized_runtime_role)
    optimized_runtime = role_totals(
        optimized_blanc["runtime"]["regions"], normalized_runtime_role)
    baseline_constructor = role_totals(
        baseline_blanc["creationTemplate"]["regions"],
        normalized_constructor_role, baseline_prefix_len)
    optimized_constructor = role_totals(
        optimized_blanc["creationTemplate"]["regions"],
        normalized_constructor_role, optimized_prefix_len)
    baseline_owners = {
        owner: int(row["blancArtifactBytes"])
        for owner, row in baseline["ownershipSummary"].items()
    }
    optimized_owners = {
        owner: int(row["blancArtifactBytes"])
        for owner, row in optimized["ownershipSummary"].items()
    }
    return {
        "baselineLedger": {
            "path": "scripts/fixtures/lido-circuit-breaker/artifact-profile-baseline.json",
            "schema": SCHEMA, "sha256": FROZEN_LEDGER_SHA256,
        },
        "artifactSizes": sizes,
        "runtimeRoleBytes": comparison_vector(baseline_runtime, optimized_runtime),
        "constructorPrefixRoleBytes": comparison_vector(
            baseline_constructor, optimized_constructor),
        "creationTemplateOwnerBytes": comparison_vector(
            baseline_owners, optimized_owners),
        "derivation": "exact subtraction of canonical generated partitions; negative deltas are byte reductions",
    }


def build_profile(evaluator_text: str, lock_raw: bytes, compiler_raw: bytes,
                  baseline: Mapping[str, object]) -> Mapping[str, object]:
    if sha(lock_raw) != REFERENCE_LOCK_SHA256:
        die("reference-lock raw identity drifted")
    lock = json.loads(lock_raw)
    compiler_output = json.loads(compiler_raw)
    if sha(compiler_raw) != lock["compiler"]["standardOutputRawSha256"]:
        die("vendored compiler-output raw identity drifted from the reference lock")
    parsed = parse_evaluator(evaluator_text)
    blanc_bytes = parsed["artifacts"]
    sol_creation = bytes.fromhex(lock["artifacts"]["creationTemplate"]["hex"].removeprefix("0x"))
    sol_runtime_template = bytes.fromhex(lock["artifacts"]["runtimeTemplate"]["hex"].removeprefix("0x"))
    worlds = lock["artifacts"]["worlds"]
    sol_official_create = bytes.fromhex(worlds[0]["fullCreateInput"]["hex"].removeprefix("0x"))
    sol_official_runtime = bytes.fromhex(worlds[0]["returnedRuntime"]["hex"].removeprefix("0x"))
    sol_independent_create = bytes.fromhex(worlds[1]["fullCreateInput"]["hex"].removeprefix("0x"))
    sol_independent_runtime = bytes.fromhex(worlds[1]["returnedRuntime"]["hex"].removeprefix("0x"))

    actual_identities = {
        "solidity": {"creationTemplate": identity(sol_creation),
            "officialFullCreate": identity(sol_official_create),
            "officialRuntime": identity(sol_official_runtime),
            "independentFullCreate": identity(sol_independent_create),
            "independentRuntime": identity(sol_independent_runtime)},
        "blanc": {"creationTemplate": identity(blanc_bytes["creation-template"]),
            "officialFullCreate": identity(blanc_bytes["official-create"]),
            "officialRuntime": identity(blanc_bytes["official-runtime"]),
            "independentFullCreate": identity(blanc_bytes["independent-create"]),
            "independentRuntime": identity(blanc_bytes["independent-runtime"])},
    }
    for side, expected in EXPECTED_OPTIMIZED_IDENTITIES.items():
        for name, (length, digest) in expected.items():
            if actual_identities[side][name] != {"byteLength": length, "sha256": digest}:
                die(f"{side} {name} optimized identity drifted")

    contract = compiler_output["contracts"]["src/CircuitBreaker.sol"]["CircuitBreaker"]["evm"]
    if bytes.fromhex(contract["bytecode"]["object"]) != sol_creation:
        die("compiler output creation bytes differ from the locked template")
    if bytes.fromhex(contract["deployedBytecode"]["object"]) != sol_runtime_template:
        die("compiler output runtime bytes differ from the locked template")
    sol_prefix_len = len(sol_creation) - len(sol_runtime_template)
    if sol_prefix_len != 830 or sol_creation[sol_prefix_len:] != sol_runtime_template:
        die("locked Solidity creation/runtime suffix relation drifted")
    blanc_prefix_len = len(blanc_bytes["creation-template"]) - len(blanc_bytes["official-runtime"])
    if blanc_prefix_len != 616 or len(
            blanc_bytes["creation-template"][blanc_prefix_len:]) != len(blanc_bytes["official-runtime"]):
        # The evaluator owns the zero-parameter runtime template, which differs
        # from the official member only at generated immutable payloads.
        die("Blanc constructor prefix arithmetic drifted")

    abi_signatures = {row["selector"].removeprefix("0x").lower(): row["signature"]
                      for row in lock["abi"]["functions"]}
    if [selector[-8:].lower() for selector in parsed["selectors"]] != sorted(
            abi_signatures):
        die("evaluator/lock selector ordering drifted")
    blanc_runtime = blanc_bytes["official-runtime"]
    validate_runtime_endpoint_layout(blanc_runtime, parsed)
    br_marks = blanc_runtime_marks(blanc_runtime, parsed, abi_signatures)
    blanc_runtime_artifact = artifact(
        blanc_runtime, br_marks, [("deployed-runtime", 0, len(blanc_runtime))])

    blanc_prefix = blanc_bytes["creation-template"][:blanc_prefix_len]
    bc_marks = blanc_constructor_marks(blanc_prefix, br_marks)
    blanc_creation_segments = [("constructor-executable", 0, blanc_prefix_len),
                               ("embedded-runtime", blanc_prefix_len,
                                len(blanc_bytes["creation-template"]))]
    blanc_creation_artifact = artifact(
        blanc_bytes["creation-template"], bc_marks, blanc_creation_segments)
    blanc_full_marks = [("creation-template-aggregate", "Lido-private", "bounded-inference",
        "fine-grained ownership is in the creationTemplate partition")] * len(
            blanc_bytes["creation-template"])
    blanc_full_marks += [("constructor-arguments", "reference-interface-data", "exact",
        "seven-word evaluator-emitted ABI suffix")] * 224
    blanc_full_artifact = artifact(
        blanc_bytes["official-create"], blanc_full_marks, blanc_creation_segments)

    input_sources = json.loads((REPO / "scripts" / "reference" / "lido-circuit-breaker" /
                                "inputs" / "std-json-input.json").read_text())["sources"]
    spans_by_id = {}
    for path, value in input_sources.items():
        source_id = compiler_output["sources"][path]["id"]
        expected_source = next(row for row in lock["sources"] if row["path"] == path)
        raw = value["content"].encode()
        if len(raw) != expected_source["byteLength"] or sha(raw) != expected_source["sha256"]:
            die(f"compiler input source identity drifted for {path}")
        spans_by_id[source_id] = source_spans(value["content"], Path(path).stem)

    sol_meta = metadata_start(sol_official_runtime)
    sr_marks = source_mapped_marks(
        sol_official_runtime, sol_meta, contract["deployedBytecode"]["sourceMap"],
        spans_by_id, False)
    paint(sr_marks, sol_meta, len(sr_marks), (
        "solidity-cbor-metadata", "Solidity-compiler", "exact",
        "CBOR length suffix plus INVALID sentinel in locked runtime"))
    for span in lock["artifacts"]["immutableReferenceSpans"]:
        paint(sr_marks, span["start"], span["start"] + span["length"], (
            "immutable-lane:" + span["name"].lower(), "Lido-private", "exact",
            "compiler-declared immutable reference span in lock"))
    solidity_runtime_artifact = artifact(
        sol_official_runtime, sr_marks, [("runtime-executable", 0, sol_meta)])

    sc_prefix_marks = source_mapped_marks(
        sol_creation[:sol_prefix_len], sol_prefix_len, contract["bytecode"]["sourceMap"],
        spans_by_id, True)
    sc_marks = sc_prefix_marks + list(sr_marks)
    solidity_creation_artifact = artifact(
        sol_creation, sc_marks, [("constructor-executable", 0, sol_prefix_len),
            ("embedded-runtime-executable", sol_prefix_len, sol_prefix_len + sol_meta)])
    sol_full_marks = [("creation-template-aggregate", "Lido-private", "bounded-inference",
        "fine-grained provenance is in the creationTemplate partition")] * len(sol_creation)
    sol_full_marks += [("constructor-arguments", "reference-interface-data", "exact",
        "locked seven-word ABI suffix")] * 224
    solidity_full_artifact = artifact(
        sol_official_create, sol_full_marks, [("constructor-executable", 0, sol_prefix_len),
            ("embedded-runtime-executable", sol_prefix_len, sol_prefix_len + sol_meta)])

    layout = parsed["layouts"]
    profile = {
        "schema": OPTIMIZED_SCHEMA, "profile": "lido-circuit-breaker-optimized",
        "provenance": {
            "blancEvaluator": "scripts/eval-lido-circuit-breaker-artifacts.lean",
            "referenceLock": {"path": "scripts/lido-circuit-breaker-reference.json",
                              "schema": lock["schema"], "sha256": sha(lock_raw)},
            "compilerOutput": {"path": "scripts/reference/lido-circuit-breaker/inputs/std-json-output.json",
                               "sha256": sha(compiler_raw)},
            "baselineLedger": {
                "path": "scripts/fixtures/lido-circuit-breaker/artifact-profile-baseline.json",
                "schema": SCHEMA, "sha256": FROZEN_LEDGER_SHA256},
            "derivation": "no byte literal: Blanc=evaluator output; Solidity=reference-lock bytes; before/after=frozen-ledger subtraction",
        },
        "artifacts": {
            "blanc": {"identities": actual_identities["blanc"],
                "runtime": blanc_runtime_artifact,
                "creationTemplate": blanc_creation_artifact,
                "fullCreate": blanc_full_artifact,
                "layoutEvidence": {
                    "runtimeTable": layout["runtime-table-layout"],
                    "runtimeEndpoints": layout["runtime-endpoint-layout"],
                    "constructorTable": layout["constructor-table-layout"],
                    "immutableOffsets": parsed["offsets"],
                    "fixedCoordinatePushes": optimized_fixed_coordinate_pushes(
                        blanc_prefix),
                    "ownershipDecision": "Blanc CommonCore owns table/branch dispatch emission; Lido owns bodies/layout helpers and compact coordinate selection; no direct Jaune byte owner found"}},
            "solidity": {"identities": actual_identities["solidity"],
                "runtime": solidity_runtime_artifact,
                "creationTemplate": solidity_creation_artifact,
                "fullCreate": solidity_full_artifact,
                "layoutEvidence": {
                    "constructorPrefixBytes": sol_prefix_len,
                    "runtimeMetadataStart": sol_meta,
                    "runtimeMetadataBytes": len(sol_official_runtime) - sol_meta,
                    "immutableReferenceSpans": lock["artifacts"]["immutableReferenceSpans"],
                    "sourceMapOwner": "vendored locked solc standard output"}},
        },
        "sizeComparison": {
            "runtime": {"solidityBytes": 4584, "blancBytes": 4282, "deltaBytes": -302},
            "creationTemplate": {"solidityBytes": 5414, "blancBytes": 4898, "deltaBytes": -516},
            "constructorPrefix": {"solidityBytes": 830, "blancBytes": 616, "deltaBytes": -214},
            "fullCreate": {"solidityBytes": 5638, "blancBytes": 5122, "deltaBytes": -516}},
        "beforeAfter": {},
        "ownershipSummary": {},
        "limitations": [
            "Solidity regions use the locked source map; optimizer sharing can make one interval serve multiple source expressions.",
            "Blanc immutable payloads split PUSH32 instructions, so their regions contain immediate bytes but no opcode starts.",
            "The frozen ledger owns launch GAS-1…GAS-5 attribution; complete optimized gas vectors are owned by the differential manifest rather than duplicated here.",
            "Jaune defines EVM semantics/types but emitted table, branch, push-width, and dispatcher bytes are owned by Blanc CommonCore or Lido-private helpers in this optimized artifact.",
        ],
    }
    owner_counts = {owner: 0 for owner in (
        "Lido-private", "Blanc-common", "Jaune", "Solidity-compiler",
        "reference-interface-data")}
    for region in profile["artifacts"]["blanc"]["creationTemplate"]["regions"]:
        owner_counts[region["owner"]] += region["byteLength"]
    profile["ownershipSummary"] = {
        owner: {"blancArtifactBytes": count,
                "basis": "unique bytes in the Blanc creation template (constructor prefix plus embedded runtime)"}
        for owner, count in owner_counts.items()}
    profile["beforeAfter"] = before_after_attribution(
        baseline, profile, blanc_prefix_len)
    return profile


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--blanc-artifacts", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write-optimized", action="store_true")
    mode.add_argument("--print-current", action="store_true")
    args = parser.parse_args(argv)

    if not FROZEN_LEDGER_PATH.is_file():
        die("frozen launch artifact profile is missing")
    frozen_raw = FROZEN_LEDGER_PATH.read_bytes()
    if sha(frozen_raw) != FROZEN_LEDGER_SHA256:
        die("frozen launch artifact profile identity drifted; regeneration is prohibited")
    baseline = validate_rendered(frozen_raw.decode())
    profile = build_profile(Path(args.blanc_artifacts).read_text(), LOCK_PATH.read_bytes(),
                            COMPILER_OUTPUT_PATH.read_bytes(), baseline)
    rendered = json.dumps(profile, indent=2, sort_keys=True) + "\n"
    validate_optimized_rendered(rendered)
    if args.print_current:
        sys.stdout.write(rendered)
        return 0
    if args.write_optimized:
        OPTIMIZED_LEDGER_PATH.parent.mkdir(parents=True, exist_ok=True)
        OPTIMIZED_LEDGER_PATH.write_text(rendered)
        print("OK — Lido optimized artifact profile generated; frozen launch ledger unchanged")
        return 0
    if not OPTIMIZED_LEDGER_PATH.is_file():
        die("committed optimized artifact profile is missing; use --write-optimized deliberately")
    committed = OPTIMIZED_LEDGER_PATH.read_text()
    validate_optimized_rendered(committed)
    if committed != rendered:
        die("committed optimized artifact profile is stale")
    regions = sum(len(profile["artifacts"][side][artifact]["regions"])
                  for side in ("blanc", "solidity")
                  for artifact in ("runtime", "creationTemplate", "fullCreate"))
    print(f"OK — Lido artifact profiles: frozen launch digest pinned; optimized 10 exact artifacts; {regions} partition regions; before/after attribution pinned")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except Exception as exc:
        print("REGRESSION — Lido artifact profile: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
