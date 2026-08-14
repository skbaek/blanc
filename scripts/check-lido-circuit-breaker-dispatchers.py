#!/usr/bin/env python3
"""Measure and falsify the exact W3/O4 Lido dispatcher frontier."""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence


REPO = Path(__file__).resolve().parents[1]
GENERATOR = REPO / "scripts" / "gen-lido-circuit-breaker-differential.py"
LOCK = REPO / "scripts" / "lido-circuit-breaker-reference.json"
SELECTED = "shared-hybrid-5-4-4-4"
FULL_VECTOR_CANDIDATES = (
    "shared-balanced", "shared-hybrid-5-4-4-4",
)
CANDIDATE_LABELS = (
    "current-balanced",
    "wrapped-linear",
    "two-branch-shared-balanced",
    "shared-balanced",
    "shared-linear",
    "shared-hybrid-5-4-4-4",
)
IMMUTABLE_FIELDS = (
    "admin", "min-pause", "max-pause", "min-heartbeat", "max-heartbeat",
)
EXPECTED_SIZES = {
    "current-balanced": 4890,
    "wrapped-linear": 4666,
    "two-branch-shared-balanced": 4744,
    "shared-balanced": 4734,
    "shared-linear": 4510,
    "shared-hybrid-5-4-4-4": 4552,
}
EXPECTED_TOPOLOGIES = {
    "current-balanced": (
        "intrinsic-branch", "none", "leaf-local-nonpayable", "balanced",
        0, 33, 17, 0),
    "wrapped-linear": (
        "intrinsic-branch", "none", "leaf-local-nonpayable", "linear",
        0, 17, 1, 0),
    "two-branch-shared-balanced": (
        "intrinsic-branch", "two-branch", "raw-shared-guard", "balanced",
        2, 33, 17, 2),
    "shared-balanced": (
        "intrinsic-branch", "compact-or", "raw-shared-guard", "balanced",
        1, 33, 17, 0),
    "shared-linear": (
        "intrinsic-branch", "compact-or", "raw-shared-guard", "linear",
        1, 17, 1, 0),
    "shared-hybrid-5-4-4-4": (
        "intrinsic-branch", "compact-or", "raw-shared-guard",
        "hybrid-5-4-4-4", 1, 20, 4, 0),
}
AST_CENSUS_FIELDS = (
    "totalBranches", "totalCalls", "mainBranches", "mainCalls",
    "dispatchBranches", "dispatchCalls", "endpointBranches", "endpointCalls",
    "selectorBranches", "missFallbackCalls", "guardBranches",
    "guardFallbackCalls", "directLeafCalls",
)
EXPECTED_AST_CENSUS = {
    "current-balanced": (99, 60, 78, 40, 78, 40, 45, 23, 33, 17, 0, 0, 0),
    "wrapped-linear": (83, 44, 62, 24, 62, 24, 45, 23, 17, 1, 0, 0, 0),
    "two-branch-shared-balanced":
        (84, 62, 63, 42, 61, 40, 28, 23, 33, 17, 2, 2, 0),
    "shared-balanced": (83, 60, 62, 40, 61, 40, 28, 23, 33, 17, 1, 0, 0),
    "shared-linear": (67, 44, 46, 24, 45, 24, 28, 23, 17, 1, 1, 0, 0),
    "shared-hybrid-5-4-4-4":
        (70, 47, 49, 27, 48, 27, 28, 23, 20, 4, 1, 0, 0),
}
REACHABILITY_CASES = (
    "view-pause-duration",
    "view-max-pause",
    "view-admin",
    "register-fresh",
    "heartbeat-expiry-minus-one",
    "view-get-pauser",
    "view-enumeration-empty",
    "view-heartbeat-interval",
    "setter-heartbeat-authorized-equal",
    "pause-return-true",
    "view-min-pause",
    "view-max-heartbeat",
    "view-get-count",
    "view-min-heartbeat",
    "view-expiry",
    "setter-pause-authorized-equal",
    "view-live",
)


def die(message: str) -> "NoReturn":
    raise RuntimeError(message)


def load_generator(eels_root: Path):
    from ethereum.crypto.hash import keccak256

    spec = importlib.util.spec_from_file_location("lido_dispatch_generator", GENERATOR)
    if spec is None or spec.loader is None:
        die("cannot load Lido differential generator")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module._KECCAK = keccak256
    module._LOCK = json.loads(LOCK.read_text())
    module.verify_eels_pin(eels_root)
    return module


def parse_candidates(path: Path) -> tuple[
        Mapping[str, Any], Mapping[str, Any], Mapping[str, Any],
        Mapping[str, Any]]:
    candidates: dict[str, bytes] = {}
    independent: dict[str, bytes] = {}
    offsets: dict[str, dict[str, list[int]]] = {
        label: {} for label in CANDIDATE_LABELS
    }
    patch_valid: dict[str, bool] = {}
    topologies: dict[str, Any] = {}
    ast_censuses: dict[str, Any] = {}
    ast_paths: dict[str, list[Mapping[str, Any]]] = {}
    guard_saving = None
    for line in path.read_text().splitlines():
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "endpoint-guard-saving":
            if len(parts) != 2 or guard_saving is not None:
                die("malformed endpoint-guard-saving row")
            guard_saving = int(parts[1])
            continue
        if parts[0] == "topology":
            if len(parts) != 10 or parts[1] not in CANDIDATE_LABELS:
                die("malformed dispatcher topology row")
            if parts[1] in topologies:
                die(f"duplicate dispatcher topology row {parts[1]}")
            topology = (
                parts[2], parts[3], parts[4], parts[5],
                *(int(value) for value in parts[6:10]))
            if topology != EXPECTED_TOPOLOGIES[parts[1]]:
                die(f"dispatcher topology drifted for {parts[1]}: {topology}")
            topologies[parts[1]] = {
                "architecture": parts[2],
                "guardForm": parts[3],
                "endpointForm": parts[4],
                "dispatchForm": parts[5],
                "guardBranches": int(parts[6]),
                "selectorBranches": int(parts[7]),
                "missFallbackCalls": int(parts[8]),
                "guardFallbackCalls": int(parts[9]),
            }
            continue
        if parts[0] == "ast-census":
            if len(parts) != 16 or parts[1] not in CANDIDATE_LABELS or \
                    parts[1] in ast_censuses or parts[15] not in {"true", "false"}:
                die("malformed/duplicate dispatcher AST census row")
            values = tuple(int(value) for value in parts[2:15])
            if values != EXPECTED_AST_CENSUS[parts[1]] or parts[15] != "true":
                die(f"dispatcher AST census drifted for {parts[1]}: {values}")
            ast_censuses[parts[1]] = {
                **dict(zip(AST_CENSUS_FIELDS, values)),
                "auditValid": True,
            }
            continue
        if parts[0] == "ast-selector-path":
            if len(parts) != 4 or parts[1] not in CANDIDATE_LABELS:
                die("malformed dispatcher AST selector-path row")
            selector = int(parts[2])
            if selector < 0 or selector >= 2 ** 32:
                die("dispatcher AST selector escaped four bytes")
            rows = ast_paths.setdefault(parts[1], [])
            encoded_selector = f"0x{selector:08x}"
            if any(row["selector"] == encoded_selector for row in rows):
                die("duplicate dispatcher AST selector-path row")
            rows.append({
                "selector": encoded_selector,
                "tokens": parts[3].split(","),
            })
            continue
        if parts[0] == "independent":
            if len(parts) != 4 or parts[1] not in CANDIDATE_LABELS or \
                    parts[1] in independent:
                die("malformed/duplicate independent candidate row")
            code = bytes.fromhex(parts[3])
            if len(code) != int(parts[2]):
                die(f"independent candidate {parts[1]} length differs")
            independent[parts[1]] = code
            continue
        if parts[0] == "candidate-offsets":
            if len(parts) != 5 or parts[1] not in CANDIDATE_LABELS or \
                    parts[2] not in IMMUTABLE_FIELDS or \
                    parts[2] in offsets[parts[1]]:
                die("malformed/duplicate candidate immutable-offset row")
            values = [] if parts[4] == "-" else [
                int(value) for value in parts[4].split(",")
            ]
            if len(values) != int(parts[3]):
                die("candidate immutable-offset count differs")
            offsets[parts[1]][parts[2]] = values
            continue
        if parts[0] == "candidate-patch-valid":
            if len(parts) != 3 or parts[1] not in CANDIDATE_LABELS or \
                    parts[1] in patch_valid or parts[2] not in {"true", "false"}:
                die("malformed/duplicate candidate patch-valid row")
            patch_valid[parts[1]] = parts[2] == "true"
            continue
        if parts[0] not in CANDIDATE_LABELS:
            die(f"unexpected dispatcher evaluator row {parts[0]}")
        if parts[0] in candidates:
            die(f"duplicate dispatcher candidate row {parts[0]}")
        if len(parts) != 3 or parts[1] == "COMPILE-FAILED":
            die(f"dispatcher candidate {parts[0]} did not compile exactly")
        code = bytes.fromhex(parts[2])
        if len(code) != int(parts[1]):
            die(f"dispatcher candidate {parts[0]} length differs")
        candidates[parts[0]] = code
    if tuple(candidates) != CANDIDATE_LABELS:
        die("dispatcher candidate identity/order differs")
    if tuple(topologies) != CANDIDATE_LABELS or \
            tuple(ast_censuses) != CANDIDATE_LABELS or \
            tuple(ast_paths) != CANDIDATE_LABELS or \
            any(len(ast_paths[label]) != 17 for label in CANDIDATE_LABELS):
        die("dispatcher topology/AST identity, order, or coverage differs")
    if tuple(independent) != CANDIDATE_LABELS or \
            tuple(patch_valid) != CANDIDATE_LABELS or not all(patch_valid.values()):
        die("dispatcher candidate family identity/patch validity differs")
    if any(tuple(offsets[label]) != IMMUTABLE_FIELDS for label in CANDIDATE_LABELS):
        die("dispatcher candidate immutable field order/coverage differs")
    if guard_saving != 170:
        die(f"leaf-local nonpayable saving drifted: {guard_saving}")
    sizes = {label: len(code) for label, code in candidates.items()}
    if sizes != EXPECTED_SIZES:
        die(f"dispatcher candidate size frontier drifted: {sizes}")
    families: dict[str, Any] = {}
    for label in CANDIDATE_LABELS:
        if len(independent[label]) != len(candidates[label]):
            die(f"dispatcher candidate family length drifted for {label}")
        claimed: set[int] = set()
        for field in IMMUTABLE_FIELDS:
            starts = offsets[label][field]
            if not starts or starts != sorted(set(starts)):
                die(f"candidate immutable offsets malformed for {label}/{field}")
            expanded = {start + index for start in starts for index in range(32)}
            if any(start + 32 > len(candidates[label]) for start in starts) or \
                    claimed.intersection(expanded):
                die(f"candidate immutable spans overlap/escape for {label}/{field}")
            claimed.update(expanded)
        families[label] = {
            "official": candidates[label],
            "independent": independent[label],
            "offsets": offsets[label],
        }
    return families, topologies, ast_censuses, ast_paths


def semantic_snapshot(gen, result) -> Mapping[str, Any]:
    output, traces, _, writes, _ = result
    return {
        "status": gen.outcome(output),
        "returndata": "0x" + bytes(output.return_data).hex(),
        "logs": gen.normalized_logs(output.logs),
        "callTrace": traces,
        "writeTrace": writes,
    }


def candidate_parameter_words(gen, params: Mapping[str, object]) -> Mapping[str, bytes]:
    return {
        "admin": gen.address_word(str(params["admin"])),
        "min-pause": gen.h256(int(params["minPauseDuration"])),
        "max-pause": gen.h256(int(params["maxPauseDuration"])),
        "min-heartbeat": gen.h256(int(params["minHeartbeatInterval"])),
        "max-heartbeat": gen.h256(int(params["maxHeartbeatInterval"])),
    }


def patch_candidate_runtime(gen, family: Mapping[str, Any],
                            params: Mapping[str, object]) -> bytes:
    code = bytearray(family["official"])
    values = candidate_parameter_words(gen, params)
    for field in IMMUTABLE_FIELDS:
        value = values[field]
        if len(value) != 32:
            die(f"candidate immutable value is not one word: {field}")
        for offset in family["offsets"][field]:
            code[offset:offset + 32] = value
    return bytes(code)


def instruction_opcodes(code: bytes) -> list[tuple[int, int, int]]:
    instructions = []
    pc = 0
    while pc < len(code):
        opcode = code[pc]
        width = opcode - 0x5f if 0x60 <= opcode <= 0x7f else 0
        if pc + 1 + width > len(code):
            die(f"dispatcher candidate ends inside PUSH{width} immediate")
        instructions.append((pc, opcode, width))
        pc += 1 + width
    return instructions


def push_immediate_lanes(code: bytes) -> Mapping[int, tuple[int, int]]:
    lanes: dict[int, tuple[int, int]] = {}
    for pc, _, width in instruction_opcodes(code):
        if width:
            lanes[pc + 1] = (pc, width)
    return lanes


def control_flow_census(code: bytes) -> Mapping[str, int]:
    opcodes = [opcode for _, opcode, _ in instruction_opcodes(code)]
    return {
        "conditionalBranches": opcodes.count(0x57),
        "directJumps": opcodes.count(0x56),
    }


def validate_candidate_families(gen, families: Mapping[str, Any]) -> None:
    official_words = candidate_parameter_words(gen, gen.OFFICIAL)
    independent_words = candidate_parameter_words(gen, gen.INDEPENDENT)
    for label, family in families.items():
        if patch_candidate_runtime(gen, family, gen.OFFICIAL) != family["official"]:
            die(f"candidate official immutable reconstruction differs: {label}")
        if patch_candidate_runtime(gen, family, gen.INDEPENDENT) != \
                family["independent"]:
            die(f"candidate independent immutable reconstruction differs: {label}")
        official_lanes = push_immediate_lanes(family["official"])
        independent_lanes = push_immediate_lanes(family["independent"])
        if official_lanes != independent_lanes:
            die(f"candidate immutable worlds changed instruction boundaries: {label}")
        official_control = control_flow_census(family["official"])
        independent_control = control_flow_census(family["independent"])
        if official_control != independent_control:
            die(f"candidate immutable worlds changed control-flow census: {label}")
        lane_rows = []
        for field in IMMUTABLE_FIELDS:
            for offset in family["offsets"][field]:
                opcode_offset, width = official_lanes.get(offset, (-1, -1))
                official_word = family["official"][offset:offset + 32]
                independent_word = family["independent"][offset:offset + 32]
                if opcode_offset != offset - 1 or width != 32 or \
                        family["official"][opcode_offset] != 0x7f or \
                        family["independent"][opcode_offset] != 0x7f or \
                        official_word != official_words[field] or \
                        independent_word != independent_words[field]:
                    die(f"candidate immutable lane is not exact PUSH32: {label}/{field}/{offset}")
                lane_rows.append({
                    "field": field,
                    "opcode": "PUSH32",
                    "opcodeOffset": opcode_offset,
                    "payloadOffset": offset,
                    "immediateBytes": width,
                    "officialImmediate": "0x" + official_word.hex(),
                    "independentImmediate": "0x" + independent_word.hex(),
                })
        family["immutableLanes"] = lane_rows
        family["byteControlFlowCensus"] = official_control


def structural_binding(label: str, row: Mapping[str, Any]) -> str:
    payload = {
        "label": label,
        "byteLength": row["byteLength"],
        "candidateSha256": row["sha256"],
        "topology": row["topology"],
        "astCensus": row["astCensus"],
        "astSelectorPaths": row["astSelectorPaths"],
        "byteControlFlowCensus": row["byteControlFlowCensus"],
        "selectorPaths": row["selectorPaths"],
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def execute_direct(gen, code: bytes, calldata: bytes, value: int, gas: int):
    from ethereum.prague.state import State

    state = State()
    gen.install_code(state, {gen.CIRCUIT: code})
    tx = gen.Tx(gen.OTHER, calldata, value=value, gas=gas)
    result = gen.execute_tx(state, tx)
    return semantic_snapshot(gen, result), result[2]


def exact_threshold(gen, code: bytes, calldata: bytes, value: int,
                    expected: Mapping[str, Any], upper: int) -> int:
    low = -1
    high = upper
    while low + 1 < high:
        middle = (low + high) // 2
        actual, _ = execute_direct(gen, code, calldata, value, middle)
        if actual == expected:
            high = middle
        else:
            low = middle
    actual, _ = execute_direct(gen, code, calldata, value, high)
    if actual != expected:
        die("dispatch completion threshold search did not converge")
    return high


def boundary_cases(gen, lock: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    cases: list[Mapping[str, Any]] = []
    known_selectors: set[bytes] = set()
    for row in lock["abi"]["functions"]:
        signature = row["signature"]
        selector = bytes.fromhex(row["selector"].removeprefix("0x"))
        known_selectors.add(selector)
        argc = len(row["entry"]["inputs"])
        cases.append({
            "name": "nonzero-" + signature,
            "family": "known-nonzero-value",
            "calldata": selector + bytes(32 * argc),
            "value": 1,
        })
    prefix = bytes.fromhex("deadbeef")
    for size in range(4):
        cases.append({
            "name": f"short-{size}", "family": "short-calldata",
            "calldata": prefix[:size], "value": 0,
        })
    ordered = sorted(int.from_bytes(selector, "big") for selector in known_selectors)
    unknown_values = [0]
    unknown_values.extend((left + right) // 2 for left, right in zip(ordered, ordered[1:]))
    unknown_values.append(0xffffffff)
    if len(unknown_values) != 18:
        die("unknown-selector gap witness count differs")
    for index, value in enumerate(unknown_values):
        selector = value.to_bytes(4, "big")
        if selector in known_selectors:
            die(f"unknown-gap-{index:02d} benchmark selector became known")
        cases.append({
            "name": f"unknown-gap-{index:02d}", "family": "unknown-selector",
            "calldata": selector, "value": 0,
        })
    cases.append({
        "name": "unknown-middle-nonzero",
        "family": "unknown-selector-nonzero",
        "calldata": prefix,
        "value": 1,
    })
    if prefix in known_selectors:
        die("unknown-middle benchmark selector became known")
    return cases


def selector_entries(lock: Mapping[str, Any]) -> list[tuple[int, str]]:
    entries = sorted(
        (int(row["selector"].removeprefix("0x"), 16), row["signature"])
        for row in lock["abi"]["functions"])
    if len(entries) != 17 or len({selector for selector, _ in entries}) != 17:
        die("dispatcher path owner does not contain exactly 17 selectors")
    return entries


def equality_step(selector: int, candidate: tuple[int, str]) -> Mapping[str, Any]:
    word, signature = candidate
    return {
        "kind": "equality", "comparedSelector": f"0x{word:08x}",
        "comparedSignature": signature, "conditionTrue": selector == word,
    }


def balanced_selector_path(
        entries: Sequence[tuple[int, str]], selector: int) -> list[Mapping[str, Any]]:
    if len(entries) == 1:
        return [equality_step(selector, entries[0])]
    split = (len(entries) + 1) // 2
    pivot = entries[split][0]
    goes_left = selector < pivot
    step = {
        "kind": "pivot", "pivotSelector": f"0x{pivot:08x}",
        "condition": "selector<pivot", "conditionTrue": goes_left,
        "subtree": "left" if goes_left else "right",
    }
    return [step, *balanced_selector_path(
        entries[:split] if goes_left else entries[split:], selector)]


def linear_selector_path(
        entries: Sequence[tuple[int, str]], selector: int) -> list[Mapping[str, Any]]:
    steps = []
    for entry in entries:
        step = equality_step(selector, entry)
        steps.append(step)
        if step["conditionTrue"]:
            break
    return steps


def hybrid_selector_path(
        entries: Sequence[tuple[int, str]], selector: int) -> list[Mapping[str, Any]]:
    groups = (entries[:5], entries[5:9], entries[9:13], entries[13:])
    root_left = selector < entries[9][0]
    root = {
        "kind": "pivot", "pivotSelector": f"0x{entries[9][0]:08x}",
        "condition": "selector<pivot", "conditionTrue": root_left,
        "subtree": "left" if root_left else "right",
    }
    second_pivot = entries[5][0] if root_left else entries[13][0]
    second_left = selector < second_pivot
    second = {
        "kind": "pivot", "pivotSelector": f"0x{second_pivot:08x}",
        "condition": "selector<pivot", "conditionTrue": second_left,
        "subtree": "left" if second_left else "right",
    }
    group_index = (0 if second_left else 1) + (0 if root_left else 2)
    return [root, second, *linear_selector_path(groups[group_index], selector)]


def selector_path(lock: Mapping[str, Any], label: str,
                  selector: int) -> Mapping[str, Any]:
    entries = selector_entries(lock)
    if label in {"current-balanced", "two-branch-shared-balanced",
                 "shared-balanced"}:
        steps = balanced_selector_path(entries, selector)
    elif label in {"wrapped-linear", "shared-linear"}:
        steps = linear_selector_path(entries, selector)
    elif label == "shared-hybrid-5-4-4-4":
        steps = hybrid_selector_path(entries, selector)
    else:
        die(f"dispatcher path topology is not owned: {label}")
    matched = next((step for step in steps
                    if step["kind"] == "equality" and step["conditionTrue"]), None)
    return {
        "selector": f"0x{selector:08x}",
        "steps": steps,
        "branchCount": len(steps),
        "trueBranchCount": sum(step["conditionTrue"] for step in steps),
        "matchedSignature": None if matched is None else matched["comparedSignature"],
    }


def selector_path_tokens(path: Mapping[str, Any]) -> list[str]:
    tokens = []
    for step in path["steps"]:
        if step["kind"] == "pivot":
            pivot = int(step["pivotSelector"].removeprefix("0x"), 16)
            tokens.append(
                f"p:{pivot}:{'L' if step['subtree'] == 'left' else 'R'}")
        elif step["kind"] == "equality":
            selector = int(step["comparedSelector"].removeprefix("0x"), 16)
            tokens.append(
                f"e:{selector}:{'T' if step['conditionTrue'] else 'F'}")
        else:
            die(f"unknown dispatcher path step: {step['kind']}")
    return tokens


def direct_path_attribution(lock: Mapping[str, Any], label: str,
                            calldata: bytes, value: int) -> Mapping[str, Any]:
    short = len(calldata) < 4
    selector = int.from_bytes((calldata + bytes(4))[:4], "big")
    guard = []
    enters_dispatch = True
    if label.startswith("shared-"):
        rejected = value != 0 or short
        guard.append({
            "predicate": "callvalue!=0-or-calldatasize<4",
            "conditionTrue": rejected,
            "outcome": "reject" if rejected else "dispatch",
        })
        enters_dispatch = not rejected
    elif label == "two-branch-shared-balanced":
        zero_value = value == 0
        guard.append({
            "predicate": "callvalue==0", "conditionTrue": zero_value,
            "outcome": "size-check" if zero_value else "reject",
        })
        if zero_value:
            guard.append({
                "predicate": "calldatasize<4", "conditionTrue": short,
                "outcome": "reject" if short else "dispatch",
            })
        enters_dispatch = zero_value and not short
    dispatch = selector_path(lock, label, selector) if enters_dispatch else None
    leaf_nonpayable = None
    if label in {"current-balanced", "wrapped-linear"} and dispatch and \
            dispatch["matchedSignature"] is not None:
        leaf_nonpayable = {
            "predicate": "callvalue==0", "conditionTrue": value == 0,
            "outcome": "body" if value == 0 else "reject",
        }
    return {
        "architecture": "intrinsic-branch",
        "guard": guard,
        "dispatch": dispatch,
        "leafNonpayable": leaf_nonpayable,
    }


def precedence_cases(gen) -> list[Mapping[str, Any]]:
    dirty_target = (1 << 200) | int.from_bytes(gen.address_bytes(gen.TARGET_1), "big")
    register_selector = gen.selector("registerPauser(address,address)")
    prefix = bytes.fromhex("deadbeef")
    rows = [
        {
            "name": f"value-plus-short-calldata-{size}",
            "calldata": prefix[:size],
            "value": 1,
        }
        for size in range(4)
    ]
    rows.extend([
        {
            "name": "value-plus-short-register",
            "calldata": register_selector,
            "value": 1,
        },
        {
            "name": "value-plus-dirty-register",
            "calldata": register_selector + dirty_target.to_bytes(32, "big") +
                gen.address_word(gen.PAUSER_A),
            "value": 1,
        },
        {
            "name": "zero-plus-short-register",
            "calldata": register_selector,
            "value": 0,
        },
        {
            "name": "zero-plus-dirty-register",
            "calldata": register_selector + dirty_target.to_bytes(32, "big") +
                gen.address_word(gen.PAUSER_A),
            "value": 0,
        },
        {
            "name": "trailing-admin",
            "calldata": gen.calldata("ADMIN()", trailing=b"\xaa" * 13),
            "value": 0,
        },
        {
            "name": "unknown-middle-trailing",
            "calldata": prefix + b"\xbb" * 33,
            "value": 0,
        },
    ])
    return rows


def run_candidate_case(gen, case, lock, artifacts, family: Mapping[str, Any]):
    params = case.constructor_params or (
        gen.INDEPENDENT if case.world == "independent" else gen.OFFICIAL)
    candidate = patch_candidate_runtime(gen, family, params)
    original_execute_create = gen.execute_create

    def execute_create_with_runtime_override(state, target, initcode, value,
                                             timestamp=1_700_000_000,
                                             gas=gen.DEFAULT_GAS_LIMIT):
        result = original_execute_create(state, target, initcode, value,
                                         timestamp, gas)
        if gen.outcome(result[0]) == "success" and target in {gen.CIRCUIT, gen.CLONE}:
            gen.install_code(state, {target: candidate})
        return result

    gen.execute_create = execute_create_with_runtime_override
    try:
        return gen.run_side(case, "blanc", lock, artifacts)
    finally:
        gen.execute_create = original_execute_create


def reachability_evidence(gen, lock, artifacts, families) -> Mapping[str, Any]:
    all_cases = {case.name: case for case in gen.build_cases(True)}
    missing = [name for name in REACHABILITY_CASES if name not in all_cases]
    if missing:
        die(f"dispatcher reachability cases disappeared: {missing}")
    selectors = {
        row["selector"].removeprefix("0x"): row["signature"]
        for row in lock["abi"]["functions"]
    }
    expected_endpoints = {row["signature"] for row in lock["abi"]["functions"]}
    observed_endpoints = {
        gen.case_endpoint(all_cases[name], selectors) for name in REACHABILITY_CASES
    }
    if observed_endpoints != expected_endpoints or len(REACHABILITY_CASES) != 17:
        die("dispatcher reachability cases do not cover the exact 17 endpoints")

    solidity = {
        name: gen.run_side(all_cases[name], "solidity", lock, artifacts)
        for name in REACHABILITY_CASES
    }
    rows: dict[str, Any] = {}
    for label, family in families.items():
        actions = []
        for name in REACHABILITY_CASES:
            case = all_cases[name]
            result = run_candidate_case(gen, case, lock, artifacts, family)
            bad = gen.compare(case, solidity[name], result)
            if bad:
                die(f"{label}/{name}: selector reachability behavior differs: {bad}")
            solidity_gas = solidity[name]["gasUsed"][-1]
            candidate_gas = result["gasUsed"][-1]
            reference_boundaries = solidity[name]["_resourceBoundaries"]
            candidate_boundaries = result["_resourceBoundaries"]
            if len(candidate_boundaries) != len(reference_boundaries):
                die(f"{label}/{name}: resource-boundary count differs")
            descriptors = gen.resource_descriptor_rows(case)
            if len(descriptors) != len(candidate_boundaries):
                die(f"{label}/{name}: resource descriptors differ")
            resource_rows = []
            for descriptor, reference, measured in zip(
                    descriptors, reference_boundaries, candidate_boundaries):
                constructor_seed = descriptor["phase"] in {
                    "primaryConstructor", "cloneConstructor"}
                resource_rows.append({
                    "boundary": descriptor["boundary"],
                    "phase": descriptor["phase"],
                    "orderWithinPhase": descriptor["orderWithinPhase"],
                    "w3Ownership": "production-constructor-seed-control"
                        if constructor_seed else "dispatcher-candidate-runtime",
                    "gasUsed": measured["gasUsed"],
                    "solidityGasUsed": reference["gasUsed"],
                    "delta": measured["gasUsed"] - reference["gasUsed"],
                })
            actions.append({
                "case": name,
                "endpoint": gen.case_endpoint(case, selectors),
                "resourceRows": resource_rows,
                "gasUsed": candidate_gas,
                "solidityGasUsed": solidity_gas,
                "delta": candidate_gas - solidity_gas,
            })
        rows[label] = actions
    return rows


def boundary_transaction(case, phase: str, order: int):
    if phase == "cloneHistory":
        return case.clone_history[order]
    if phase == "history":
        return case.history[order]
    if phase == "action":
        if case.action is None or order != 0:
            die(f"{case.name}: malformed action topology coordinate")
        return case.action
    if phase in {"primaryConstructor", "cloneConstructor"}:
        return None
    die(f"{case.name}: unknown resource phase {phase}")


def full_vector_evidence(gen, lock, artifacts, families) -> Mapping[str, Any]:
    cases = gen.build_cases(True)
    if len(cases) != 175:
        die(f"dispatcher full-vector case count drifted: {len(cases)}")
    solidity = {
        case.name: gen.run_side(case, "solidity", lock, artifacts)
        for case in cases
    }
    evidence: dict[str, Any] = {}
    positive_failures: dict[str, list[Mapping[str, Any]]] = {}
    for label in FULL_VECTOR_CANDIDATES:
        results: dict[str, tuple[Mapping[str, Any], Mapping[str, Any]]] = {}
        for case in cases:
            candidate = run_candidate_case(
                gen, case, lock, artifacts, families[label])
            bad = gen.compare(case, solidity[case.name], candidate)
            if bad:
                die(f"{label}/{case.name}: full-vector behavior differs: {bad}")
            gen.assert_case_evidence(case, solidity[case.name], candidate)
            results[case.name] = (solidity[case.name], candidate)
        resources = gen.full_resource_boundaries(cases, results)
        if len(resources) != 464:
            die(f"{label}: full resource boundary count drifted: {len(resources)}")
        by_name = {case.name: case for case in cases}
        rows = []
        for resource in resources:
            case = by_name[resource["case"]]
            tx = boundary_transaction(
                case, resource["phase"], resource["orderWithinPhase"])
            topology = None if tx is None else direct_path_attribution(
                lock, label, tx.calldata, tx.value)
            constructor_seed = resource["phase"] in {
                "primaryConstructor", "cloneConstructor"}
            rows.append({
                **resource,
                "w3Ownership": "production-constructor-seed-control"
                    if constructor_seed else "dispatcher-candidate-runtime",
                "calldata": None if tx is None else "0x" + tx.calldata.hex(),
                "value": None if tx is None else tx.value,
                "topologyPath": topology,
            })
        runtime_rows = [
            row for row in rows
            if row["w3Ownership"] == "dispatcher-candidate-runtime"
        ]
        constructor_seeds = [
            row for row in rows
            if row["w3Ownership"] == "production-constructor-seed-control"
        ]
        adequate_runtime = [
            row for row in runtime_rows if row["adequacy"] == "adequate"
        ]
        positives = [
            row for row in adequate_runtime if row["blancMinusSolidity"] > 0
        ]
        if positives:
            positive_failures[label] = positives
        evidence[label] = {
            "caseCount": len(cases),
            "boundaryCount": len(rows),
            "runtimeBoundaryCount": len(runtime_rows),
            "constructorSeedBoundaryCount": len(constructor_seeds),
            "runtimeSummary": gen.resource_summary(runtime_rows),
            "constructorSeedSummary": gen.resource_summary(constructor_seeds),
            "worstAdequateDelta": max(
                row["blancMinusSolidity"] for row in adequate_runtime),
            "bestAdequateDelta": min(
                row["blancMinusSolidity"] for row in adequate_runtime),
            "positiveAdequateRuntimeRows": positives,
            "intrinsicBranchExceptions": [],
            "rows": rows,
        }
    candidate_rows = {
        label: {
            "byteLength": EXPECTED_SIZES[label],
            "costVector": {
                row["coordinate"]: row["blancGasUsed"]
                for row in evidence[label]["rows"]
                if row["w3Ownership"] == "dispatcher-candidate-runtime"
            },
        }
        for label in FULL_VECTOR_CANDIDATES
    }
    if positive_failures:
        detail = "; ".join(
            f"{label}[" + ", ".join(
                f"{row['coordinate']}={row['blancMinusSolidity']:+d}"
                for row in rows) + "]"
            for label, rows in positive_failures.items())
        die("positive adequate runtime boundaries require exact opcode segmentation "
            f"before admission: {detail}")
    return {
        "status": "measured-zero-runtime-positives",
        "constructorMode": "production-constructor-seed-control",
        "integrationStatus":
            "selected-production-runtime-and-constructor-matched",
        "candidateOrder": list(FULL_VECTOR_CANDIDATES),
        "paretoFrontier": pareto_labels(candidate_rows),
        "candidates": evidence,
    }


def pareto_labels(candidate_rows: Mapping[str, Mapping[str, Any]]) -> list[str]:
    labels = list(candidate_rows)
    frontier = []
    for label in labels:
        row = candidate_rows[label]
        vector = row["costVector"]
        dominated = False
        for other_label in labels:
            if other_label == label:
                continue
            other = candidate_rows[other_label]
            other_vector = other["costVector"]
            if tuple(other_vector) != tuple(vector):
                die("dispatcher Pareto vectors have different coordinates")
            weak = other["byteLength"] <= row["byteLength"] and all(
                other_vector[key] <= vector[key] for key in vector)
            strict = other["byteLength"] < row["byteLength"] or any(
                other_vector[key] < vector[key] for key in vector)
            if weak and strict:
                dominated = True
                break
        if not dominated:
            frontier.append(label)
    return frontier


def build_profile(gen, lock, artifacts, families, topologies, ast_censuses,
                  ast_paths, *, mode: str) -> Mapping[str, Any]:
    if SELECTED is not None and mode != "full-vector":
        die("selected dispatcher lifecycle requires --full-vector evidence")
    validate_candidate_families(gen, families)
    candidates = {
        label: family["official"] for label, family in families.items()
    }
    solidity_code = gen.patch_solidity_runtime(lock, gen.OFFICIAL)
    boundaries = boundary_cases(gen, lock)
    precedence = precedence_cases(gen)
    all_direct = [*boundaries, *precedence]
    reference: dict[str, Any] = {}
    for case in all_direct:
        semantic, gas_used = execute_direct(
            gen, solidity_code, case["calldata"], case["value"], 20_000_000)
        threshold = exact_threshold(
            gen, solidity_code, case["calldata"], case["value"], semantic,
            gas_used)
        reference[case["name"]] = {
            "semantic": semantic, "gasUsed": gas_used,
            "completionThreshold": threshold,
        }

    measured: dict[str, Any] = {}
    for label, code in candidates.items():
        direct_rows = []
        cost_vector: dict[str, int] = {}
        feasible = True
        for case in all_direct:
            semantic, gas_used = execute_direct(
                gen, code, case["calldata"], case["value"], 20_000_000)
            expected = reference[case["name"]]
            if semantic != expected["semantic"]:
                die(f"{label}/{case['name']}: dispatch semantics differ")
            threshold = exact_threshold(
                gen, code, case["calldata"], case["value"], semantic,
                gas_used)
            cost_vector["direct:" + case["name"] + ":gas"] = gas_used
            cost_vector["direct:" + case["name"] + ":threshold"] = threshold
            required = case in boundaries
            dominates = gas_used <= expected["gasUsed"] and \
                threshold <= expected["completionThreshold"]
            if required and not dominates:
                feasible = False
            direct_rows.append({
                "case": case["name"],
                "family": case.get("family", "precedence"),
                "calldata": "0x" + case["calldata"].hex(),
                "value": case["value"],
                "pathAttribution": direct_path_attribution(
                    lock, label, case["calldata"], case["value"]),
                "gasUsed": gas_used,
                "solidityGasUsed": expected["gasUsed"],
                "delta": gas_used - expected["gasUsed"],
                "completionThreshold": threshold,
                "solidityCompletionThreshold": expected["completionThreshold"],
                "thresholdDelta": threshold - expected["completionThreshold"],
                "requiredDominance": required,
            })
        candidate_row = {
            "byteLength": len(code),
            "officialBytecode": "0x" + code.hex(),
            "independentBytecode": "0x" + families[label]["independent"].hex(),
            "sha256": hashlib.sha256(code).hexdigest(),
            "independentSha256": hashlib.sha256(
                families[label]["independent"]).hexdigest(),
            "immutableOffsets": families[label]["offsets"],
            "immutableLanes": families[label]["immutableLanes"],
            "topology": topologies[label],
            "astCensus": ast_censuses[label],
            "astSelectorPaths": ast_paths[label],
            "byteControlFlowCensus":
                families[label]["byteControlFlowCensus"],
            "selectorPaths": [
                selector_path(lock, label, selector)
                for selector, _ in selector_entries(lock)
            ],
            "requiredDominance": feasible,
            "directRows": direct_rows,
            "costVector": cost_vector,
        }
        candidate_row["structureByteBindingSha256"] = structural_binding(
            label, candidate_row)
        measured[label] = candidate_row

    reachability = reachability_evidence(gen, lock, artifacts, families)
    for label, actions in reachability.items():
        measured[label]["reachableEndpoints"] = actions
        measured[label]["representativeDominance"] = all(
            boundary["delta"] <= 0 for row in actions
            for boundary in row["resourceRows"]
            if boundary["w3Ownership"] == "dispatcher-candidate-runtime")
        for row in actions:
            for boundary in row["resourceRows"]:
                if boundary["w3Ownership"] != "dispatcher-candidate-runtime":
                    continue
                coordinate = f"reachability:{row['case']}:" + \
                    f"{boundary['boundary']}:{boundary['phase']}:gas"
                measured[label]["costVector"][coordinate] = boundary["gasUsed"]
    frontier = pareto_labels(measured)
    production_official_runtime = artifacts["official-runtime"]
    production_independent_runtime = artifacts["independent-runtime"]
    production_official_matches = [
        label for label, family in families.items()
        if family["official"] == production_official_runtime
    ]
    production_independent_matches = [
        label for label, family in families.items()
        if family["independent"] == production_independent_runtime
    ]
    expected_production_match = \
        ["current-balanced"] if SELECTED is None else [SELECTED]
    if production_official_matches != expected_production_match or \
            production_independent_matches != expected_production_match:
        die("production runtime/candidate identity drifted: " +
            f"official={production_official_matches}, " +
            f"independent={production_independent_matches}")
    full_vector = full_vector_evidence(gen, lock, artifacts, families) \
        if mode == "full-vector" else {"status": "not-run"}
    return {
        "schema": 1,
        "mode": mode,
        "selection": {
            "status": "pending" if SELECTED is None else "selected",
            "selected": SELECTED,
        },
        "candidateOrder": list(CANDIDATE_LABELS),
        "paretoFrontier": frontier,
        "fullVector": full_vector,
        "productionOfficialRuntimeSha256": hashlib.sha256(
            production_official_runtime).hexdigest(),
        "productionIndependentRuntimeSha256": hashlib.sha256(
            production_independent_runtime).hexdigest(),
        "productionOfficialCandidateMatches": production_official_matches,
        "productionIndependentCandidateMatches": production_independent_matches,
        "referenceRuntimeSha256": hashlib.sha256(solidity_code).hexdigest(),
        "candidates": measured,
    }


def expected_topology(label: str) -> Mapping[str, Any]:
    (architecture, guard_form, endpoint_form, dispatch_form,
     guard, selector, fallback, guard_calls) = EXPECTED_TOPOLOGIES[label]
    return {
        "architecture": architecture,
        "guardForm": guard_form,
        "endpointForm": endpoint_form,
        "dispatchForm": dispatch_form,
        "guardBranches": guard,
        "selectorBranches": selector,
        "missFallbackCalls": fallback,
        "guardFallbackCalls": guard_calls,
    }


def validate_full_vector(full: Mapping[str, Any], lock: Mapping[str, Any], gen) -> None:
    if not isinstance(full, dict) or set(full) != {
            "status", "constructorMode", "integrationStatus",
            "candidateOrder", "paretoFrontier", "candidates"} or \
            full.get("status") != "measured-zero-runtime-positives" or \
            full.get("constructorMode") != "production-constructor-seed-control" or \
            full.get("integrationStatus") != \
                "selected-production-runtime-and-constructor-matched" or \
            full.get("candidateOrder") != list(FULL_VECTOR_CANDIDATES):
        die("dispatcher full-vector lifecycle/order drifted")
    candidates = full.get("candidates")
    if not isinstance(candidates, dict) or tuple(candidates) != FULL_VECTOR_CANDIDATES:
        die("dispatcher full-vector candidate identity drifted")
    cases = gen.build_cases(True)
    by_name = {case.name: case for case in cases}
    expected_descriptors = [
        (case, descriptor)
        for case in cases for descriptor in gen.resource_descriptor_rows(case)
    ]
    if len(cases) != 175 or len(expected_descriptors) != 464:
        die("dispatcher independent full-vector coordinate owner drifted")
    row_keys = {
        "ordinal", "coordinate", "case", "boundary", "label", "phase",
        "orderWithinPhase", "adequacy", "solidityStatus", "blancStatus",
        "solidityGasLimit", "blancGasLimit", "solidityGasUsed",
        "blancGasUsed", "blancMinusSolidity", "comparisonClass",
        "w3Ownership", "calldata", "value", "topologyPath",
    }
    solidity_identity = None
    constructor_seed_identity = None
    for label in FULL_VECTOR_CANDIDATES:
        evidence = candidates[label]
        if not isinstance(evidence, dict) or set(evidence) != {
                "caseCount", "boundaryCount", "runtimeBoundaryCount",
                "constructorSeedBoundaryCount", "runtimeSummary",
                "constructorSeedSummary", "worstAdequateDelta",
                "bestAdequateDelta", "positiveAdequateRuntimeRows",
                "intrinsicBranchExceptions", "rows"} or \
                evidence["caseCount"] != 175 or evidence["boundaryCount"] != 464:
            die(f"dispatcher full-vector evidence shape drifted: {label}")
        rows = evidence["rows"]
        if not isinstance(rows, list) or len(rows) != 464:
            die(f"dispatcher full-vector row count drifted: {label}")
        for ordinal, (row, (case, descriptor)) in enumerate(
                zip(rows, expected_descriptors)):
            if not isinstance(row, dict) or set(row) != row_keys:
                die(f"dispatcher full-vector row keys drifted: {label}/{ordinal}")
            coordinate = f"{case.name}#{descriptor['boundary']}:{descriptor['label']}"
            if row["ordinal"] != ordinal or row["coordinate"] != coordinate or \
                    row["case"] != case.name or \
                    any(row[field] != descriptor[field] for field in (
                        "boundary", "label", "phase", "orderWithinPhase")):
                die(f"dispatcher full-vector coordinate/order drifted: {label}/{ordinal}")
            if row["solidityGasLimit"] != descriptor["gasLimit"] or \
                    row["blancGasLimit"] != descriptor["gasLimit"] or \
                    row["solidityStatus"] != row["blancStatus"]:
                die(f"dispatcher full-vector limit/status drifted: {label}/{coordinate}")
            expected_adequacy = "oog-control" if \
                "oog-control" in case.tags and row["phase"] == "action" else "adequate"
            if row["adequacy"] != expected_adequacy or \
                    (expected_adequacy == "oog-control" and
                     row["solidityStatus"] != "exception:OutOfGasError") or \
                    (expected_adequacy == "adequate" and
                     row["solidityStatus"] == "exception:OutOfGasError"):
                die(f"dispatcher full-vector adequacy drifted: {label}/{coordinate}")
            delta = row["blancGasUsed"] - row["solidityGasUsed"]
            comparison = "blanc-cheaper" if delta < 0 else \
                "blanc-dearer" if delta > 0 else "equal"
            if row["blancMinusSolidity"] != delta or \
                    row["comparisonClass"] != comparison:
                die(f"dispatcher full-vector delta class drifted: {label}/{coordinate}")
            tx = boundary_transaction(
                by_name[row["case"]], row["phase"], row["orderWithinPhase"])
            expected_ownership = "production-constructor-seed-control" \
                if tx is None else "dispatcher-candidate-runtime"
            expected_calldata = None if tx is None else "0x" + tx.calldata.hex()
            expected_value = None if tx is None else tx.value
            expected_path = None if tx is None else direct_path_attribution(
                lock, label, tx.calldata, tx.value)
            if row["w3Ownership"] != expected_ownership or \
                    row["calldata"] != expected_calldata or row["value"] != expected_value or \
                    row["topologyPath"] != expected_path:
                die(f"dispatcher full-vector topology attribution drifted: {label}/{coordinate}")
        runtime_rows = [
            row for row in rows
            if row["w3Ownership"] == "dispatcher-candidate-runtime"
        ]
        constructor_seeds = [
            row for row in rows
            if row["w3Ownership"] == "production-constructor-seed-control"
        ]
        adequate = [row for row in runtime_rows if row["adequacy"] == "adequate"]
        positives = [row for row in adequate if row["blancMinusSolidity"] > 0]
        if evidence["runtimeBoundaryCount"] != len(runtime_rows) or \
                evidence["constructorSeedBoundaryCount"] != len(constructor_seeds) or \
                evidence["runtimeSummary"] != gen.resource_summary(runtime_rows) or \
                evidence["constructorSeedSummary"] != \
                    gen.resource_summary(constructor_seeds) or \
                evidence["positiveAdequateRuntimeRows"] != [] or positives or \
                evidence["intrinsicBranchExceptions"] != [] or \
                evidence["worstAdequateDelta"] != max(
                    row["blancMinusSolidity"] for row in adequate) or \
                evidence["bestAdequateDelta"] != min(
                    row["blancMinusSolidity"] for row in adequate):
            die(f"dispatcher full-vector extrema/positive rows drifted: {label}")
        identity = [
            (row["coordinate"], row["solidityStatus"], row["solidityGasLimit"],
             row["solidityGasUsed"]) for row in rows
        ]
        if solidity_identity is None:
            solidity_identity = identity
        elif identity != solidity_identity:
            die("dispatcher full candidates used different Solidity reference vectors")
        seeds = [
            (row["coordinate"], row["blancStatus"], row["blancGasLimit"],
             row["blancGasUsed"]) for row in constructor_seeds
        ]
        if constructor_seed_identity is None:
            constructor_seed_identity = seeds
        elif seeds != constructor_seed_identity:
            die("dispatcher candidates used different production constructor seeds")
    pareto_rows = {
        label: {
            "byteLength": EXPECTED_SIZES[label],
            "costVector": {
                row["coordinate"]: row["blancGasUsed"]
                for row in candidates[label]["rows"]
                if row["w3Ownership"] == "dispatcher-candidate-runtime"
            },
        }
        for label in FULL_VECTOR_CANDIDATES
    }
    if full["paretoFrontier"] != pareto_labels(pareto_rows):
        die("dispatcher full-vector Pareto frontier drifted")


def validate_profile(profile: Mapping[str, Any], lock: Mapping[str, Any], gen, *,
                     selected: str | None = SELECTED) -> None:
    if set(profile) != {
            "schema", "mode", "selection", "candidateOrder", "paretoFrontier",
            "fullVector", "productionOfficialRuntimeSha256",
            "productionIndependentRuntimeSha256",
            "productionOfficialCandidateMatches",
            "productionIndependentCandidateMatches",
            "referenceRuntimeSha256", "candidates"} or \
            profile.get("schema") != 1:
        die("dispatcher profile schema/top-level keys drifted")
    if profile.get("mode") not in {"focused", "full-vector"}:
        die("dispatcher profile lifecycle mode drifted")
    if profile.get("candidateOrder") != list(CANDIDATE_LABELS):
        die("dispatcher profile candidate order drifted")
    candidates = profile.get("candidates")
    if not isinstance(candidates, dict) or tuple(candidates) != CANDIDATE_LABELS:
        die("dispatcher profile candidate identity drifted")
    reference_sha = profile.get("referenceRuntimeSha256")
    if not isinstance(reference_sha, str) or len(reference_sha) != 64 or \
            any(char not in "0123456789abcdef" for char in reference_sha):
        die("dispatcher reference runtime identity is malformed")
    production_official_sha = profile.get("productionOfficialRuntimeSha256")
    production_independent_sha = profile.get(
        "productionIndependentRuntimeSha256")
    expected_production_match = \
        ["current-balanced"] if selected is None else [selected]
    if not isinstance(production_official_sha, str) or \
            len(production_official_sha) != 64 or \
            any(char not in "0123456789abcdef"
                for char in production_official_sha) or \
            not isinstance(production_independent_sha, str) or \
            len(production_independent_sha) != 64 or \
            any(char not in "0123456789abcdef"
                for char in production_independent_sha) or \
            profile.get("productionOfficialCandidateMatches") != \
                expected_production_match or \
            profile.get("productionIndependentCandidateMatches") != \
                expected_production_match or \
            production_official_sha != \
                candidates[expected_production_match[0]]["sha256"] or \
            production_independent_sha != \
                candidates[expected_production_match[0]]["independentSha256"]:
        die("dispatcher production/candidate identity evidence drifted")

    direct_identity = None
    reachability_constructor_seed_identity = None
    expected_direct_identity = [
        (case["name"], case.get("family", "precedence"),
         "0x" + case["calldata"].hex(), case["value"])
        for case in [*boundary_cases(gen, lock), *precedence_cases(gen)]
    ]
    expected_selectors = {
        f"0x{selector:08x}": signature
        for selector, signature in selector_entries(lock)
    }
    reach_case_map = {
        case.name: case for case in gen.build_cases(True)
        if case.name in REACHABILITY_CASES
    }
    for label in CANDIDATE_LABELS:
        row = candidates[label]
        if set(row) != {
                "byteLength", "officialBytecode", "independentBytecode", "sha256",
                "independentSha256", "immutableOffsets", "immutableLanes",
                "topology", "astCensus", "astSelectorPaths",
                "byteControlFlowCensus", "structureByteBindingSha256",
                "selectorPaths", "requiredDominance", "directRows",
                "costVector", "reachableEndpoints",
                "representativeDominance"}:
            die(f"dispatcher candidate profile keys drifted: {label}")
        if row["byteLength"] != EXPECTED_SIZES[label]:
            die(f"dispatcher candidate size identity drifted: {label}")
        for field in ("sha256", "independentSha256"):
            digest = row[field]
            if not isinstance(digest, str) or len(digest) != 64 or \
                    any(char not in "0123456789abcdef" for char in digest):
                die(f"dispatcher candidate digest malformed: {label}/{field}")
        if not isinstance(row["officialBytecode"], str) or \
                not isinstance(row["independentBytecode"], str) or \
                not row["officialBytecode"].startswith("0x") or \
                not row["independentBytecode"].startswith("0x"):
            die(f"dispatcher candidate bytecode encoding malformed: {label}")
        official_code = bytes.fromhex(row["officialBytecode"].removeprefix("0x"))
        independent_code = bytes.fromhex(
            row["independentBytecode"].removeprefix("0x"))
        if len(official_code) != row["byteLength"] or \
                len(independent_code) != row["byteLength"] or \
                hashlib.sha256(official_code).hexdigest() != row["sha256"] or \
                hashlib.sha256(independent_code).hexdigest() != row["independentSha256"]:
            die(f"dispatcher candidate byte identity drifted: {label}")
        if row["topology"] != expected_topology(label):
            die(f"dispatcher candidate architecture/topology drifted: {label}")
        expected_census = {
            **dict(zip(AST_CENSUS_FIELDS, EXPECTED_AST_CENSUS[label])),
            "auditValid": True,
        }
        if row["astCensus"] != expected_census or \
                row["astCensus"]["selectorBranches"] != \
                    row["topology"]["selectorBranches"] or \
                row["astCensus"]["missFallbackCalls"] != \
                    row["topology"]["missFallbackCalls"] or \
                row["astCensus"]["guardBranches"] != \
                    row["topology"]["guardBranches"] or \
                row["astCensus"]["guardFallbackCalls"] != \
                    row["topology"]["guardFallbackCalls"] or \
                row["astCensus"]["directLeafCalls"] != 0:
            die(f"dispatcher candidate AST census drifted: {label}")
        official_control = control_flow_census(official_code)
        independent_control = control_flow_census(independent_code)
        if row["byteControlFlowCensus"] != official_control or \
                independent_control != official_control or \
                official_control != {
                    "conditionalBranches": row["astCensus"]["totalBranches"],
                    "directJumps": row["astCensus"]["totalCalls"],
                }:
            die(f"dispatcher candidate AST/byte CFG census drifted: {label}")
        expected_ast_paths = [
            {
                "selector": f"0x{selector:08x}",
                "tokens": selector_path_tokens(selector_path(lock, label, selector)),
            }
            for selector, _ in selector_entries(lock)
        ]
        if row["astSelectorPaths"] != expected_ast_paths:
            die(f"dispatcher candidate plan-derived selector paths drifted: {label}")
        if row["structureByteBindingSha256"] != structural_binding(label, row):
            die(f"dispatcher topology/byte structural binding drifted: {label}")
        offsets = row["immutableOffsets"]
        if not isinstance(offsets, dict) or tuple(offsets) != IMMUTABLE_FIELDS:
            die(f"dispatcher candidate immutable ownership drifted: {label}")
        occupied: set[int] = set()
        for field in IMMUTABLE_FIELDS:
            starts = offsets[field]
            if not isinstance(starts, list) or not starts or \
                    starts != sorted(set(starts)):
                die(f"dispatcher candidate immutable offsets malformed: {label}/{field}")
            expanded = {start + index for start in starts for index in range(32)}
            if any(not isinstance(start, int) or start < 0 or
                   start + 32 > row["byteLength"] for start in starts) or \
                    occupied.intersection(expanded):
                die(f"dispatcher candidate immutable span escaped/overlapped: {label}/{field}")
            occupied.update(expanded)
        reconstructed_family = {
            "official": official_code,
            "independent": independent_code,
            "offsets": offsets,
        }
        if patch_candidate_runtime(gen, reconstructed_family, gen.OFFICIAL) != \
                official_code or \
                patch_candidate_runtime(gen, reconstructed_family, gen.INDEPENDENT) != \
                independent_code:
            die(f"dispatcher immutable reconstruction drifted: {label}")
        official_pushes = push_immediate_lanes(official_code)
        independent_pushes = push_immediate_lanes(independent_code)
        if official_pushes != independent_pushes:
            die(f"dispatcher immutable instruction boundaries drifted: {label}")
        official_words = candidate_parameter_words(gen, gen.OFFICIAL)
        independent_words = candidate_parameter_words(gen, gen.INDEPENDENT)
        expected_lanes = []
        for field in IMMUTABLE_FIELDS:
            for offset in offsets[field]:
                opcode_offset, width = official_pushes.get(offset, (-1, -1))
                if opcode_offset != offset - 1 or width != 32 or \
                        official_code[offset:offset + 32] != official_words[field] or \
                        independent_code[offset:offset + 32] != independent_words[field]:
                    die(f"dispatcher immutable lane is not exact PUSH32: {label}/{field}")
                expected_lanes.append({
                    "field": field,
                    "opcode": "PUSH32",
                    "opcodeOffset": opcode_offset,
                    "payloadOffset": offset,
                    "immediateBytes": 32,
                    "officialImmediate": "0x" + official_words[field].hex(),
                    "independentImmediate": "0x" + independent_words[field].hex(),
                })
        if row["immutableLanes"] != expected_lanes:
            die(f"dispatcher immutable PUSH32 lane evidence drifted: {label}")

        paths = row["selectorPaths"]
        if not isinstance(paths, list) or len(paths) != 17 or \
                {path.get("selector") for path in paths} != set(expected_selectors):
            die(f"dispatcher selector-path coverage drifted: {label}")
        for path in paths:
            selector = int(path["selector"].removeprefix("0x"), 16)
            if path != selector_path(lock, label, selector) or \
                    path["matchedSignature"] != expected_selectors[path["selector"]]:
                die(f"dispatcher selector-to-leaf path drifted: {label}")

        direct_rows = row["directRows"]
        if not isinstance(direct_rows, list) or len(direct_rows) != 50 or \
                len({item.get("case") for item in direct_rows}) != 50:
            die(f"dispatcher direct boundary coverage drifted: {label}")
        identity = [(item.get("case"), item.get("family"),
                     item.get("calldata"), item.get("value"))
                    for item in direct_rows]
        if direct_identity is None:
            direct_identity = identity
        elif identity != direct_identity:
            die("dispatcher candidates measured different direct boundaries")
        if identity != expected_direct_identity:
            die(f"dispatcher direct boundary identity/order drifted: {label}")
        family_counts: dict[str, int] = {}
        reconstructed_costs: dict[str, int] = {}
        required_ok = True
        for item in direct_rows:
            if set(item) != {
                    "case", "family", "calldata", "value", "pathAttribution",
                    "gasUsed", "solidityGasUsed", "delta", "completionThreshold",
                    "solidityCompletionThreshold", "thresholdDelta",
                    "requiredDominance"}:
                die(f"dispatcher direct row shape drifted: {label}/{item.get('case')}")
            family_counts[item["family"]] = family_counts.get(item["family"], 0) + 1
            calldata = bytes.fromhex(item["calldata"].removeprefix("0x"))
            if item["pathAttribution"] != direct_path_attribution(
                    lock, label, calldata, item["value"]):
                die(f"dispatcher path attribution drifted: {label}/{item['case']}")
            if item["delta"] != item["gasUsed"] - item["solidityGasUsed"] or \
                    item["thresholdDelta"] != item["completionThreshold"] - \
                    item["solidityCompletionThreshold"]:
                die(f"dispatcher direct delta arithmetic drifted: {label}/{item['case']}")
            required = item["family"] != "precedence"
            if item["requiredDominance"] is not required:
                die(f"dispatcher required-boundary classification drifted: {item['case']}")
            if required:
                required_ok &= item["delta"] <= 0 and item["thresholdDelta"] <= 0
            reconstructed_costs[f"direct:{item['case']}:gas"] = item["gasUsed"]
            reconstructed_costs[f"direct:{item['case']}:threshold"] = \
                item["completionThreshold"]
        if family_counts != {
                "known-nonzero-value": 17, "short-calldata": 4,
                "unknown-selector": 18, "unknown-selector-nonzero": 1,
                "precedence": 10}:
            die(f"dispatcher boundary family counts drifted: {family_counts}")
        if row["requiredDominance"] is not required_ok:
            die(f"dispatcher required-dominance summary drifted: {label}")

        reach = row["reachableEndpoints"]
        if not isinstance(reach, list) or [item.get("case") for item in reach] != \
                list(REACHABILITY_CASES) or \
                {item.get("endpoint") for item in reach} != set(expected_selectors.values()):
            die(f"dispatcher endpoint reachability coverage drifted: {label}")
        representative_ok = True
        for item in reach:
            if set(item) != {
                    "case", "endpoint", "resourceRows", "gasUsed",
                    "solidityGasUsed", "delta"}:
                die(f"dispatcher reachability row shape drifted: {label}/{item.get('case')}")
            descriptors = gen.resource_descriptor_rows(reach_case_map[item["case"]])
            resources = item["resourceRows"]
            if not isinstance(resources, list) or len(resources) != len(descriptors):
                die(f"dispatcher reachability resource vector drifted: {label}/{item['case']}")
            for resource, descriptor in zip(resources, descriptors):
                constructor_seed = descriptor["phase"] in {
                    "primaryConstructor", "cloneConstructor"}
                ownership = "production-constructor-seed-control" \
                    if constructor_seed else "dispatcher-candidate-runtime"
                if not isinstance(resource, dict) or set(resource) != {
                        "boundary", "phase", "orderWithinPhase", "w3Ownership",
                        "gasUsed", "solidityGasUsed", "delta"} or \
                        any(resource[field] != descriptor[field] for field in (
                            "boundary", "phase", "orderWithinPhase")) or \
                        resource["w3Ownership"] != ownership or \
                        resource["delta"] != \
                        resource["gasUsed"] - resource["solidityGasUsed"]:
                    die(f"dispatcher reachability boundary drifted: {label}/{item['case']}")
                if not constructor_seed:
                    representative_ok &= resource["delta"] <= 0
                    coordinate = f"reachability:{item['case']}:" + \
                        f"{resource['boundary']}:{resource['phase']}:gas"
                    reconstructed_costs[coordinate] = resource["gasUsed"]
            if not resources or item["gasUsed"] != resources[-1]["gasUsed"] or \
                    item["solidityGasUsed"] != resources[-1]["solidityGasUsed"] or \
                    item["delta"] != resources[-1]["delta"]:
                die(f"dispatcher reachability action summary drifted: {label}/{item['case']}")
        if row["representativeDominance"] is not representative_ok:
            die(f"dispatcher representative-dominance summary drifted: {label}")
        if row["costVector"] != reconstructed_costs:
            die(f"dispatcher Pareto cost vector drifted: {label}")
        constructor_seed_identity = [
            (item["case"], resource["boundary"], resource["phase"],
             resource["orderWithinPhase"], resource["gasUsed"],
             resource["solidityGasUsed"])
            for item in reach for resource in item["resourceRows"]
            if resource["w3Ownership"] ==
                "production-constructor-seed-control"
        ]
        if reachability_constructor_seed_identity is None:
            reachability_constructor_seed_identity = constructor_seed_identity
        elif constructor_seed_identity != reachability_constructor_seed_identity:
            die("dispatcher candidates used different focused constructor seeds")

    expected_frontier = pareto_labels(candidates)
    if profile["paretoFrontier"] != expected_frontier:
        die("dispatcher Pareto frontier is not derived from the full candidate vectors")
    if any(not candidates[label]["requiredDominance"] or
           not candidates[label]["representativeDominance"]
           for label in FULL_VECTOR_CANDIDATES):
        die("dispatcher full-vector candidates failed focused qualification")
    selection = profile["selection"]
    if selected is None:
        if selection != {"status": "pending", "selected": None}:
            die("dispatcher pending selection lifecycle drifted")
    elif profile["mode"] != "full-vector" or \
            selection != {"status": "selected", "selected": selected} or \
            selected not in expected_frontier or \
            not candidates[selected]["requiredDominance"] or \
            not candidates[selected]["representativeDominance"]:
        die("dispatcher selected lifecycle is unsupported by measured evidence")

    full_vector = profile["fullVector"]
    if full_vector == {"status": "not-run"}:
        if profile["mode"] != "focused":
            die("dispatcher full-vector mode omitted its vector")
        return
    if profile["mode"] != "full-vector":
        die("dispatcher focused mode carried a full vector")
    validate_full_vector(full_vector, lock, gen)
    if selected is not None and selected not in full_vector["paretoFrontier"]:
        die("selected dispatcher is not on the full-vector Pareto frontier")


def run_profile_falsifiers(profile: Mapping[str, Any], lock: Mapping[str, Any], gen) -> None:
    def rejects(name: str, mutate) -> None:
        mutant = copy.deepcopy(profile)
        mutate(mutant)
        try:
            validate_profile(mutant, lock, gen)
        except (KeyError, TypeError, ValueError, RuntimeError):
            return
        die(f"dispatcher live falsifier survived: {name}")

    def refresh_binding(p, label: str) -> None:
        row = p["candidates"][label]
        row["structureByteBindingSha256"] = structural_binding(label, row)

    def make_required_gas_positive(p) -> None:
        candidate = p["candidates"]["shared-hybrid-5-4-4-4"]
        row = candidate["directRows"][0]
        row["gasUsed"] = row["solidityGasUsed"] + 1
        row["delta"] = 1
        candidate["costVector"][f"direct:{row['case']}:gas"] = row["gasUsed"]
        candidate["requiredDominance"] = False

    def make_required_threshold_positive(p) -> None:
        candidate = p["candidates"]["shared-hybrid-5-4-4-4"]
        row = candidate["directRows"][0]
        row["completionThreshold"] = row["solidityCompletionThreshold"] + 1
        row["thresholdDelta"] = 1
        candidate["costVector"][f"direct:{row['case']}:threshold"] = \
            row["completionThreshold"]
        candidate["requiredDominance"] = False

    def architecture_relabel(p) -> None:
        label = "shared-hybrid-5-4-4-4"
        p["candidates"][label]["topology"]["architecture"] = "direct-jump"
        refresh_binding(p, label)

    def guard_branch_deletion(p) -> None:
        label = "shared-balanced"
        p["candidates"][label]["topology"]["guardBranches"] = 0
        refresh_binding(p, label)

    def selector_path_deletion(p) -> None:
        label = "shared-hybrid-5-4-4-4"
        p["candidates"][label]["selectorPaths"].pop()
        refresh_binding(p, label)

    def selector_leaf_swap(p) -> None:
        label = "shared-balanced"
        paths = p["candidates"][label]["selectorPaths"]
        paths[0]["matchedSignature"] = paths[1]["matchedSignature"]
        refresh_binding(p, label)

    def ast_selector_path_deletion(p) -> None:
        label = "shared-hybrid-5-4-4-4"
        p["candidates"][label]["astSelectorPaths"].pop()
        refresh_binding(p, label)

    def coherent_dispatch_branch_to_jump(p) -> None:
        label = "shared-hybrid-5-4-4-4"
        candidate = p["candidates"][label]
        guard_branches = candidate["astCensus"]["guardBranches"]
        for bytecode_field, digest_field in (
                ("officialBytecode", "sha256"),
                ("independentBytecode", "independentSha256")):
            code = bytearray(bytes.fromhex(
                candidate[bytecode_field].removeprefix("0x")))
            conditional = [
                pc for pc, opcode, _ in instruction_opcodes(bytes(code))
                if opcode == 0x57
            ]
            code[conditional[guard_branches]] = 0x56
            candidate[bytecode_field] = "0x" + code.hex()
            candidate[digest_field] = hashlib.sha256(code).hexdigest()
        census = candidate["astCensus"]
        for field in ("totalBranches", "mainBranches", "dispatchBranches",
                      "selectorBranches"):
            census[field] -= 1
        for field in ("totalCalls", "mainCalls", "dispatchCalls"):
            census[field] += 1
        census["directLeafCalls"] += 1
        candidate["topology"]["selectorBranches"] -= 1
        candidate["byteControlFlowCensus"] = control_flow_census(
            bytes.fromhex(candidate["officialBytecode"].removeprefix("0x")))
        refresh_binding(p, label)

    def coherent_immutable_lane_shift(p) -> None:
        candidate = p["candidates"]["shared-balanced"]
        candidate["immutableOffsets"]["admin"][0] += 1
        lane = candidate["immutableLanes"][0]
        lane["opcodeOffset"] += 1
        lane["payloadOffset"] += 1

    def coherent_immutable_lane_missing(p) -> None:
        candidate = p["candidates"]["shared-hybrid-5-4-4-4"]
        removed_offset = candidate["immutableOffsets"]["admin"].pop()
        lane_index = next(
            index for index, lane in enumerate(candidate["immutableLanes"])
            if lane["field"] == "admin" and
                lane["payloadOffset"] == removed_offset)
        candidate["immutableLanes"].pop(lane_index)

    def drift_focused_constructor_seed(p) -> None:
        resource = next(
            item for item in p["candidates"]["shared-balanced"]
                ["reachableEndpoints"][0]["resourceRows"]
            if item["w3Ownership"] == "production-constructor-seed-control")
        resource["gasUsed"] += 1
        resource["delta"] += 1

    rejects("direct-jump-architecture", architecture_relabel)
    rejects("coherent-dispatch-branch-to-direct-jump",
            coherent_dispatch_branch_to_jump)
    rejects("guard-branch-deletion", guard_branch_deletion)
    rejects("selector-path-deletion", selector_path_deletion)
    rejects("selector-leaf-swap", selector_leaf_swap)
    rejects("plan-derived-selector-path-deletion", ast_selector_path_deletion)
    rejects("reachability-deletion", lambda p:
            p["candidates"]["shared-hybrid-5-4-4-4"]
                ["reachableEndpoints"].pop())
    rejects("unknown-gap-deletion", lambda p:
            p["candidates"]["shared-balanced"]["directRows"].pop(21))
    rejects("required-family-relabel", lambda p:
            p["candidates"]["shared-balanced"]["directRows"][0].__setitem__(
                "family", "precedence"))
    rejects("required-gas-positive", make_required_gas_positive)
    rejects("required-threshold-positive", make_required_threshold_positive)
    rejects("pareto-forgery", lambda p: p.__setitem__("paretoFrontier", []))
    rejects("immutable-span-truncation", lambda p:
            p["candidates"]["shared-balanced"]["immutableOffsets"]
                ["admin"].__setitem__(0, p["candidates"]["shared-balanced"]
                    ["byteLength"] - 31))
    rejects("immutable-lane-shift", lambda p:
            p["candidates"]["shared-balanced"]["immutableLanes"][0]
                .__setitem__("payloadOffset", p["candidates"]["shared-balanced"]
                    ["immutableLanes"][0]["payloadOffset"] + 1))
    rejects("immutable-lane-coherent-shift", coherent_immutable_lane_shift)
    rejects("immutable-lane-missing", lambda p:
            p["candidates"]["shared-hybrid-5-4-4-4"]
                ["immutableLanes"].pop())
    rejects("immutable-lane-coherent-missing", coherent_immutable_lane_missing)
    rejects("candidate-order-swap", lambda p:
            p["candidateOrder"].__setitem__(0, p["candidateOrder"][1]))
    rejects("production-official-candidate-match", lambda p:
            p.__setitem__("productionOfficialCandidateMatches", []))
    rejects("production-independent-only-candidate-drift", lambda p:
            p.__setitem__("productionIndependentCandidateMatches", []))
    rejects("production-official-runtime-identity", lambda p:
            p.__setitem__("productionOfficialRuntimeSha256", "0" * 64))
    rejects("production-independent-only-runtime-drift", lambda p:
            p.__setitem__("productionIndependentRuntimeSha256", "0" * 64))
    rejects("constructor-seed-pareto-injection", lambda p:
            p["candidates"]["shared-balanced"]["costVector"].__setitem__(
                "reachability:view-pause-duration:0:primaryConstructor:gas",
                p["candidates"]["shared-balanced"]["reachableEndpoints"][0]
                    ["resourceRows"][0]["gasUsed"]))
    rejects("focused-constructor-seed-candidate-drift",
            drift_focused_constructor_seed)
    if profile["fullVector"] != {"status": "not-run"}:
        def coherent_full_runtime_positive(p) -> None:
            full = p["fullVector"]
            evidence = full["candidates"]["shared-hybrid-5-4-4-4"]
            row = next(item for item in evidence["rows"]
                       if item["w3Ownership"] == "dispatcher-candidate-runtime" and
                       item["adequacy"] == "adequate")
            row["blancGasUsed"] = row["solidityGasUsed"] + 1
            row["blancMinusSolidity"] = 1
            row["comparisonClass"] = "blanc-dearer"
            runtime_rows = [
                item for item in evidence["rows"]
                if item["w3Ownership"] == "dispatcher-candidate-runtime"
            ]
            adequate = [item for item in runtime_rows if item["adequacy"] == "adequate"]
            evidence["runtimeSummary"] = gen.resource_summary(runtime_rows)
            evidence["worstAdequateDelta"] = max(
                item["blancMinusSolidity"] for item in adequate)
            evidence["bestAdequateDelta"] = min(
                item["blancMinusSolidity"] for item in adequate)
            evidence["positiveAdequateRuntimeRows"] = [row]
            evidence["intrinsicBranchExceptions"] = [{
                "coordinate": row["coordinate"], "delta": 1,
                "classification": "intrinsic-branch-dispatch",
            }]
            pareto_rows = {
                label: {
                    "byteLength": EXPECTED_SIZES[label],
                    "costVector": {
                        item["coordinate"]: item["blancGasUsed"]
                        for item in full["candidates"][label]["rows"]
                        if item["w3Ownership"] == "dispatcher-candidate-runtime"
                    },
                }
                for label in FULL_VECTOR_CANDIDATES
            }
            full["paretoFrontier"] = pareto_labels(pareto_rows)

        rejects("full-vector-row-deletion", lambda p:
                p["fullVector"]["candidates"]["shared-balanced"]["rows"].pop())
        rejects("full-vector-coordinate-relabel", lambda p:
                p["fullVector"]["candidates"]["shared-hybrid-5-4-4-4"]
                    ["rows"][0].__setitem__("coordinate", "laundered#0:constructor"))
        rejects("full-vector-topology-relabel", lambda p:
                p["fullVector"]["candidates"]["shared-balanced"]["rows"][-1]
                    ["topologyPath"].__setitem__("architecture", "direct-jump"))
        rejects("full-vector-pareto-forgery", lambda p:
                p["fullVector"].__setitem__("paretoFrontier", []))
        rejects("selected-production-integration-status", lambda p:
                p["fullVector"].__setitem__(
                    "integrationStatus", "selection-pending"))
        rejects("full-vector-coherent-runtime-positive",
                coherent_full_runtime_positive)
        rejects("constructor-exception-classification", lambda p:
                p["fullVector"]["candidates"]["shared-balanced"]
                    ["intrinsicBranchExceptions"].append({
                        "coordinate": p["fullVector"]["candidates"]
                            ["shared-balanced"]["rows"][0]["coordinate"],
                        "classification": "intrinsic-branch-dispatch",
                    }))
        rejects("constructor-seed-runtime-relabel", lambda p:
                p["fullVector"]["candidates"]["shared-balanced"]["rows"][0]
                    .__setitem__("w3Ownership", "dispatcher-candidate-runtime"))

    focused_selected = copy.deepcopy(profile)
    focused_selected["mode"] = "focused"
    focused_selected["fullVector"] = {"status": "not-run"}
    focused_selected["selection"] = {
        "status": "selected", "selected": "current-balanced"}
    try:
        validate_profile(
            focused_selected, lock, gen, selected="current-balanced")
    except (KeyError, TypeError, ValueError, RuntimeError):
        pass
    else:
        die("dispatcher live falsifier survived: focused-selected-transition")


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--eels-root", required=True, type=Path)
    parser.add_argument("--blanc-artifacts", required=True, type=Path)
    parser.add_argument("--dispatcher-artifacts", required=True, type=Path)
    parser.add_argument("--mode", required=True, choices=("focused", "full-vector"))
    parser.add_argument("--selection-stage", required=True,
                        choices=("pending", "selected"))
    args = parser.parse_args(argv)
    expected_stage = "pending" if SELECTED is None else "selected"
    if args.selection_stage != expected_stage:
        die(f"dispatcher selection lifecycle mismatch: expected {expected_stage}")
    gen = load_generator(args.eels_root.expanduser().resolve())
    lock = json.loads(LOCK.read_text())
    artifacts = gen.parse_artifacts(args.blanc_artifacts.read_text())
    families, topologies, ast_censuses, ast_paths = parse_candidates(
        args.dispatcher_artifacts)
    profile = build_profile(
        gen, lock, artifacts, families, topologies, ast_censuses, ast_paths,
        mode=args.mode)
    validate_profile(profile, lock, gen)
    run_profile_falsifiers(profile, lock, gen)
    print(json.dumps(profile, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as exc:
        print("REGRESSION — Lido CircuitBreaker dispatcher: " + str(exc), file=sys.stderr)
        raise SystemExit(1)
