#!/usr/bin/env python3
"""Independent exact schema for amended AC5 successful-return resource shape."""
from __future__ import annotations

import copy
from typing import Any, Mapping, NoReturn, Sequence


CANDIDATE_SHAPE_CASES = (
    ("pause-return-empty", 0, "revert"),
    ("pause-return-one-byte", 1, "revert"),
    ("pause-return-31-bytes", 31, "revert"),
    ("pause-return-false", 32, "revert"),
    ("pause-return-noncanonical", 32, "revert"),
    ("pause-return-true", 32, "success"),
    ("pause-return-true-trailing-1", 33, "success"),
    ("pause-return-true-large-64", 64, "success"),
    ("pause-return-true-large-256", 256, "success"),
    ("pause-return-true-large-1024", 1024, "success"),
    ("pause-return-true-large-4096", 4096, "success"),
    ("pause-return-true-large-16384", 16384, "success"),
    ("pause-return-true-large-32768", 32768, "success"),
    ("pause-return-true-large-65536", 65536, "success"),
)
SIDES = ("solidity", "blanc")
CIRCUIT_ADDRESS = "0x6019cb557978296ba3c08a7b73225c0975dfb2f7"
TARGET_ADDRESS = "0x1111111111111111111111111111111111111111"
PARENT_OUTPUT_OFFSETS = {"solidity": 128, "blanc": 0}
ROW_KEYS = {
    "case", "side", "returnBytes", "status", "staticcallOutputOffset",
    "staticcallOutputSize", "staticcallReturndataBytes",
    "staticcallSource", "staticcallTarget", "successReturndatacopy",
}
COPY_KEYS = {
    "opcode", "source", "memoryOffset", "returndataOffset", "size",
}
EVIDENCE_KEYS = {
    "schema", "successfulStaticcallRows", "failureBubbleRows",
    "fullCopyMutantRejected", "failureMutantsRejected", "gasSlope",
}
FAILURE_KEYS = {
    "case", "side", "returndataBytes", "failedCall", "returndatacopy",
}
FAILED_CALL_KEYS = {
    "opcode", "source", "target", "outputOffset", "outputSize",
    "returndataBytes",
}
GAS_SLOPE_KEYS = {
    "fromReturnBytes", "toReturnBytes", "solidityGasUsedDelta",
    "blancGasUsedDelta", "frozenBlancFullCopyGasUsedDelta",
}


class Ac5ShapeError(RuntimeError):
    pass


def fail(label: str, message: str) -> NoReturn:
    raise Ac5ShapeError(f"{label}: {message}")


def exact_int(value: Any, label: str) -> int:
    if type(value) is not int:
        fail(label, "expected integer")
    return value


def exact_string(value: Any, label: str) -> str:
    if not isinstance(value, str):
        fail(label, "expected string")
    return value


def validate_candidate_parent_shape(
        rows: Sequence[Mapping[str, Any]], label: str = "AC5 candidate") -> None:
    expected = [
        (case, side, return_bytes, status)
        for case, return_bytes, status in CANDIDATE_SHAPE_CASES
        for side in SIDES
    ]
    if not isinstance(rows, list) or len(rows) != len(expected):
        fail(label, f"expected {len(expected)} exact success-shape rows")
    for index, (row, (case, side, return_bytes, status)) in enumerate(zip(rows, expected)):
        row_label = f"{label}[{index}]"
        if not isinstance(row, dict) or set(row) != ROW_KEYS:
            fail(row_label, "row keys differ")
        if exact_string(row.get("case"), row_label + ".case") != case or \
                exact_string(row.get("side"), row_label + ".side") != side:
            fail(row_label, "case/side order differs")
        if exact_int(row.get("returnBytes"), row_label + ".returnBytes") != return_bytes:
            fail(row_label, "declared return size differs")
        if exact_string(row.get("status"), row_label + ".status") != status:
            fail(row_label, "outer status differs")
        if exact_int(row.get("staticcallOutputOffset"),
                     row_label + ".staticcallOutputOffset") != \
                PARENT_OUTPUT_OFFSETS[side]:
            fail(row_label, "STATICCALL output offset differs")
        if exact_string(row.get("staticcallSource"),
                        row_label + ".staticcallSource") != CIRCUIT_ADDRESS or \
                exact_string(row.get("staticcallTarget"),
                             row_label + ".staticcallTarget") != TARGET_ADDRESS:
            fail(row_label, "STATICCALL provenance differs")
        if exact_int(row.get("staticcallOutputSize"),
                     row_label + ".staticcallOutputSize") != 32:
            fail(row_label, "STATICCALL output size is not one word")
        if exact_int(row.get("staticcallReturndataBytes"),
                     row_label + ".staticcallReturndataBytes") != return_bytes:
            fail(row_label, "observed STATICCALL returndata size differs")
        copies = row.get("successReturndatacopy")
        if not isinstance(copies, list):
            fail(row_label, "success RETURNDATACOPY evidence is not an array")
        for copy_index, copy_row in enumerate(copies):
            copy_label = f"{row_label}.successReturndatacopy[{copy_index}]"
            if not isinstance(copy_row, dict) or set(copy_row) != COPY_KEYS:
                fail(copy_label, "RETURNDATACOPY keys differ")
            if exact_string(copy_row.get("opcode"), copy_label + ".opcode") != \
                    "RETURNDATACOPY":
                fail(copy_label, "opcode differs")
            exact_string(copy_row.get("source"), copy_label + ".source")
            for field in ("memoryOffset", "returndataOffset", "size"):
                if exact_int(copy_row.get(field), copy_label + "." + field) < 0:
                    fail(copy_label, f"{field} is negative")
        if copies:
            fail(row_label, "successful-tail RETURNDATACOPY is prohibited")


def assert_captured_full_copy_mutant_rejected(
        rows: Sequence[Mapping[str, Any]],
        label: str = "AC5 captured full-copy falsifier") -> None:
    """Re-mutate an accepted captured row and require fail-closed rejection."""
    validate_candidate_parent_shape(rows, label + ".source")
    mutant = copy.deepcopy(rows)
    captured = mutant[-1]
    captured["successReturndatacopy"].append({
        "opcode": "RETURNDATACOPY",
        "source": "0x6019cb557978296ba3c08a7b73225c0975dfb2f7",
        "memoryOffset": captured["staticcallOutputOffset"],
        "returndataOffset": 0,
        "size": captured["returnBytes"],
    })
    try:
        validate_candidate_parent_shape(mutant, label + ".mutant")
    except Ac5ShapeError as exc:
        if "successful-tail RETURNDATACOPY is prohibited" not in str(exc):
            raise
        return
    fail(label, "captured full-success-tail-copy mutant was accepted")


def assert_captured_staticcall_provenance_mutant_rejected(
        rows: Sequence[Mapping[str, Any]],
        label: str = "AC5 captured provenance falsifier") -> None:
    mutant = copy.deepcopy(rows)
    mutant[0]["staticcallSource"] = TARGET_ADDRESS
    try:
        validate_candidate_parent_shape(mutant, label + ".mutant")
    except Ac5ShapeError as exc:
        if "STATICCALL provenance differs" not in str(exc):
            raise
        return
    fail(label, "captured STATICCALL provenance mutant was accepted")


def validate_failure_bubble_shape(
        failures: Sequence[Mapping[str, Any]],
        label: str = "AC5 failure bubble") -> None:
    expected_failures = [
        (case, side, size)
        for case, size in (
            ("pause-pause-target-revert", 4),
            ("pause-query-revert", 2),
            ("pause-pause-target-revert-large-256", 256),
            ("pause-query-revert-large-256", 256))
        for side in SIDES
    ]
    if not isinstance(failures, list) or len(failures) != len(expected_failures):
        fail(label, "failure-bubble row count differs")
    for index, (row, (case, side, size)) in enumerate(zip(failures, expected_failures)):
        row_label = f"{label}[{index}]"
        if not isinstance(row, dict) or set(row) != FAILURE_KEYS:
            fail(row_label, "failure row keys differ")
        if exact_string(row.get("case"), row_label + ".case") != case or \
                exact_string(row.get("side"), row_label + ".side") != side or \
                exact_int(row.get("returndataBytes"),
                          row_label + ".returndataBytes") != size:
            fail(row_label, "failure case/side/size differs")
        failed_call = row.get("failedCall")
        if not isinstance(failed_call, dict) or set(failed_call) != FAILED_CALL_KEYS:
            fail(row_label, "failed-call keys differ")
        query_failure = "query-revert" in case
        expected_opcode = "STATICCALL" if query_failure else "CALL"
        expected_output_size = 32 if query_failure else 0
        if exact_string(failed_call.get("opcode"), row_label + ".failedCall.opcode") != \
                expected_opcode or \
                exact_string(failed_call.get("source"),
                             row_label + ".failedCall.source") != CIRCUIT_ADDRESS or \
                exact_string(failed_call.get("target"),
                             row_label + ".failedCall.target") != TARGET_ADDRESS or \
                exact_int(failed_call.get("outputOffset"),
                          row_label + ".failedCall.outputOffset") != \
                PARENT_OUTPUT_OFFSETS[side] or \
                exact_int(failed_call.get("outputSize"),
                          row_label + ".failedCall.outputSize") != expected_output_size or \
                exact_int(failed_call.get("returndataBytes"),
                          row_label + ".failedCall.returndataBytes") != size:
            fail(row_label, "failed-call opcode/provenance/output geometry differs")
        copied = row.get("returndatacopy")
        if not isinstance(copied, dict) or set(copied) != COPY_KEYS:
            fail(row_label, "failure RETURNDATACOPY keys differ")
        if copied.get("opcode") != "RETURNDATACOPY" or \
                exact_string(copied.get("source"),
                             row_label + ".source") != CIRCUIT_ADDRESS or \
                exact_int(copied.get("memoryOffset"),
                          row_label + ".memoryOffset") != 0 or \
                exact_int(copied.get("returndataOffset"),
                          row_label + ".returndataOffset") != 0 or \
                exact_int(copied.get("size"), row_label + ".size") != size:
            fail(row_label, "failure RETURNDATACOPY is not exact/full/provenanced")


def assert_captured_failure_provenance_mutant_rejected(
        failures: Sequence[Mapping[str, Any]],
        label: str = "AC5 captured failure provenance falsifier") -> None:
    mutations = (
        ("opcode", lambda rows: rows[0]["failedCall"].__setitem__(
            "opcode", "STATICCALL")),
        ("target", lambda rows: rows[0]["failedCall"].__setitem__(
            "target", CIRCUIT_ADDRESS)),
        ("truncation", lambda rows: rows[4]["returndatacopy"].__setitem__(
            "size", 32)),
        ("memory-offset", lambda rows: rows[4]["returndatacopy"].__setitem__(
            "memoryOffset", 32)),
    )
    for name, mutate in mutations:
        mutant = copy.deepcopy(failures)
        mutate(mutant)
        try:
            validate_failure_bubble_shape(mutant, f"{label}.{name}")
        except Ac5ShapeError as exc:
            if not any(fragment in str(exc) for fragment in (
                    "opcode/provenance/output geometry differs",
                    "exact/full/provenanced")):
                raise
            continue
        fail(label, f"captured failure {name} mutant was accepted")


def validate_candidate_shape_evidence(
        evidence: Mapping[str, Any], label: str = "AC5 candidate evidence") -> None:
    if not isinstance(evidence, dict) or set(evidence) != EVIDENCE_KEYS:
        fail(label, "evidence keys differ")
    if exact_int(evidence.get("schema"), label + ".schema") != 1:
        fail(label, "schema differs")
    if type(evidence.get("fullCopyMutantRejected")) is not bool or \
            evidence["fullCopyMutantRejected"] is not True:
        fail(label, "full-copy mutant rejection is not true")
    if type(evidence.get("failureMutantsRejected")) is not bool or \
            evidence["failureMutantsRejected"] is not True:
        fail(label, "failure mutant rejection is not true")
    validate_candidate_parent_shape(
        evidence.get("successfulStaticcallRows"),
        label + ".successfulStaticcallRows")
    assert_captured_full_copy_mutant_rejected(
        evidence["successfulStaticcallRows"], label + ".fullCopyMutant")
    assert_captured_staticcall_provenance_mutant_rejected(
        evidence["successfulStaticcallRows"], label + ".staticcallProvenanceMutant")
    failures = evidence.get("failureBubbleRows")
    validate_failure_bubble_shape(failures, label + ".failureBubbleRows")
    assert_captured_failure_provenance_mutant_rejected(
        failures, label + ".failureProvenanceMutant")

    slope = evidence.get("gasSlope")
    if not isinstance(slope, dict) or set(slope) != GAS_SLOPE_KEYS:
        fail(label, "gas-slope keys differ")
    for key in GAS_SLOPE_KEYS:
        exact_int(slope.get(key), label + ".gasSlope." + key)
    if slope["fromReturnBytes"] != 64 or slope["toReturnBytes"] != 32768 or \
            slope["solidityGasUsedDelta"] != 13_314 or \
            slope["blancGasUsedDelta"] != 8_180 or \
            slope["frozenBlancFullCopyGasUsedDelta"] != 16_488:
        fail(label, "gas-slope range/baseline differs")
    if slope["blancGasUsedDelta"] > slope["solidityGasUsedDelta"] or \
            slope["blancGasUsedDelta"] >= slope["frozenBlancFullCopyGasUsedDelta"]:
        fail(label, "candidate gas slope remains full-copy-class")


def validate_candidate_shape_against_resource_paths(
        evidence: Mapping[str, Any], paths: Mapping[str, Any],
        label: str = "AC5 candidate resource cross-check") -> None:
    """Cross-derive the claimed slope from the independently retained rows."""
    validate_candidate_shape_evidence(evidence, label + ".shape")
    if not isinstance(paths, dict):
        fail(label, "successful large-return paths are not an object")
    first = paths.get("pause-return-true-large-64")
    last = paths.get("pause-return-true-large-32768")
    if not isinstance(first, dict) or not isinstance(last, dict):
        fail(label, "64/32768 resource rows are missing")
    derived = {
        "fromReturnBytes": 64,
        "toReturnBytes": 32768,
        "solidityGasUsedDelta":
            exact_int(last.get("solidityGasUsed"), label + ".last.solidityGasUsed") -
            exact_int(first.get("solidityGasUsed"), label + ".first.solidityGasUsed"),
        "blancGasUsedDelta":
            exact_int(last.get("blancGasUsed"), label + ".last.blancGasUsed") -
            exact_int(first.get("blancGasUsed"), label + ".first.blancGasUsed"),
        "frozenBlancFullCopyGasUsedDelta": 16_488,
    }
    if evidence.get("gasSlope") != derived:
        fail(label, "gas slope is not derived from retained resource rows")
