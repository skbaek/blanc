#!/usr/bin/env python3
"""Independent schema and digest owner for the Lido resource vector.

This module intentionally imports nothing from the differential generator.  It
derives the ordered resource coordinates from the committed case execution
descriptors and validates the separately generated measurement vector against
that derivation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

from lido_circuit_breaker_ac5_shape_schema import (
    Ac5ShapeError,
    validate_candidate_shape_against_resource_paths,
    validate_candidate_shape_evidence,
)


RESOURCE_SCHEMA = 1
EXPECTED_BOUNDARIES = {"baseline": 455, "optimized": 464}
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
REFERENCE_SOURCE_COMMIT = "6829a5a962ece56564bd9d72d01c29cabf157579"
BASELINE_BLANC_COMMIT = "fc3edee6dbfb77eaf344afee43c921d48ff8a3af"
BASELINE_MANIFEST_SHA256 = \
    "6cde638ac37977f3aea228ad877a85d37e415ac4f927e66a099be67de7d30cef"

EXPECTED_MODEL = {
    "engine": "ethereum/execution-specs",
    "fork": "Prague",
    "scope": "direct-eels-message",
    "gasUsedFormula": "message.gas - output.gas_left",
    "refundAccounting": "pre-refund",
    "transactionIntrinsicGasIncluded": False,
    "createCodeDepositGasIncluded": True,
}
EXPECTED_TRANSITIONS = {
    "baseline": {
        "adequateGasDominance": True,
        "strictSuccessfulImprovement": True,
        "independentDigestRepin": True,
    },
    "optimized": {
        "perBoundaryDominanceOrPinnedIntrinsicBranchDispatch": True,
        "strictSuccessfulImprovement": True,
        "independentCoordinateVectorAndExceptionRepin": True,
    },
}
SOLIDITY_IDENTITIES = {
    "solidityOfficialFullCreateSha256":
        "f2800888ef707680a581939c93f7975d24f25ce14641900591418e8be23400dc",
    "solidityOfficialRuntimeSha256":
        "7decb73763f1c184f5e1950c5e3449fbca507fdf40836769df2e67fccd0c8a1e",
    "solidityIndependentFullCreateSha256":
        "fa683c7c793bec9410284271ecaa7fe8ca8f12759dbca0e8a937e1dbea47da86",
    "solidityIndependentRuntimeSha256":
        "a264bca00fa7d8b264e1666e9da3bacc87b90f285583340987f6f884795f3317",
}
BASELINE_BLANC_IDENTITIES = {
    "blancCreationTemplateSha256":
        "3cbf5dec4dacbed0b0d5ee94f01fc0845b602fd67f260031ca693458e32fd28f",
    "blancOfficialFullCreateSha256":
        "3e207da94a889e623ecb92719f5782e0506c39d81a0eec2d7f41d14049e1ec2d",
    "blancOfficialRuntimeSha256":
        "fa628a48ab7544301c5a4b287315ccff998fb43ec23fc16250f4a4309d9c100a",
    "blancIndependentFullCreateSha256":
        "a7eb1fd354306a089af848b0601600b0030ff8d82102bf1cbf8cfaac45e3d8ce",
    "blancIndependentRuntimeSha256":
        "c5c98c4e99e43fa3fc61693e730b87e69dc37f6bba38f3adcdeb801c4375835f",
}

# These pins are intentionally outside the mutable generator. The baseline
# pins preserve the exact 172-case/455-boundary launch evidence. The optimized
# descriptor set adds the 65,536-byte row and two long failure-bubbling rows,
# for 175 cases/464 boundaries. Its full-vector pin is installed only after a
# complete optimized measurement through the documented manifest write path.
EXPECTED_VECTOR_PINS = {
    "baseline": {
        "orderedCoordinatesSha256":
            "5109446212e38903a851f1659fafbf0a2a307ebdcf4df978cc87dd469845bc55",
        "fullResourceVectorSha256":
            "104e373458d395c8a6ca7b02c6a7f9baefef21064e5408402df13eebc2dd8169",
    },
    "optimized": {
        "orderedCoordinatesSha256":
            "07ca7475b4af537e4866de0a8f102f043ced22c4207ef8587d7570bd9151aef2",
        "fullResourceVectorSha256":
            "98392ffe11a9eeef6407e90cc42b55739f384c154ef090473882e5d60d69a335",
    },
}

INTRINSIC_BRANCH_ARCHITECTURE = \
    "all Blanc control flow, including selector dispatch, uses Func.branch"
INTRINSIC_BRANCH_CLASSIFICATION = "intrinsic-branch-dispatch"
INTRINSIC_BRANCH_ADMISSION_REQUIRES = [
    "independent opcode traces place the entire excess before the selected leaf",
    "no later Blanc segment is costlier than the Solidity segment",
    "the selected legal tree is Pareto-justified against balanced, linear, and hybrid legal trees",
    "the exact coordinate and delta are independently pinned and mutation-tested",
]
EXPECTED_INTRINSIC_BRANCH_ROWS: list[Mapping[str, Any]] = []
EXPECTED_INTRINSIC_BRANCH_ROWS_SHA256 = \
    "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945"

COMPLETION_THRESHOLD_DEFINITION = (
    "minimum direct EELS message gas reproducing the complete adequate boundary "
    "outcome across every declared semantic channel; successful constructors also "
    "reproduce their independently owned installed-runtime identity"
)
COMPLETION_THRESHOLD_SCOPE = (
    "33 former GAS-1..GAS-5 positive-family witnesses; the two named "
    "25000-gas equal-OOG controls remain separate in resourceEvidence.oogControls"
)
COMPLETION_THRESHOLD_SEARCH = (
    "exact integer binary search over [0, 20000000] with a fresh causal world per "
    "probe; runtime seed and history messages retain adequate gas and only the final "
    "action gas varies"
)
# Exact (class, case, coordinate, Solidity threshold, Blanc threshold, delta)
# pins are populated from one complete optimized manifest-write measurement and
# are deliberately owned outside the generator.
EXPECTED_COMPLETION_THRESHOLD_PINS: tuple[
    tuple[str, str, str, int, int, int], ...
] = (
    ("GAS-1", "constructor-success-official", "constructor-success-official#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 967777, 906729, -61048),
    ("GAS-1", "constructor-success-independent", "constructor-success-independent#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 967777, 906729, -61048),
    ("GAS-1", "constructor-success-exact-lower-bounds", "constructor-success-exact-lower-bounds#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 967777, 906729, -61048),
    ("GAS-1", "constructor-success-exact-upper-bounds", "constructor-success-exact-upper-bounds#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 967777, 906729, -61048),
    ("GAS-1", "constructor-success-equal-bounds", "constructor-success-equal-bounds#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 967777, 906729, -61048),
    ("GAS-1", "constructor-trailing-arguments", "constructor-trailing-arguments#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 967783, 906729, -61054),
    ("GAS-2", "constructor-dirty-admin", "constructor-dirty-admin#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 260, 143, -117),
    ("GAS-2", "constructor-error-admin-zero", "constructor-error-admin-zero#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 481, 174, -307),
    ("GAS-2", "constructor-error-min-heartbeat-above-max", "constructor-error-min-heartbeat-above-max#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 577, 274, -303),
    ("GAS-2", "constructor-error-min-heartbeat-zero", "constructor-error-min-heartbeat-zero#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 551, 246, -305),
    ("GAS-2", "constructor-error-min-pause-above-max", "constructor-error-min-pause-above-max#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 529, 224, -305),
    ("GAS-2", "constructor-error-min-pause-zero", "constructor-error-min-pause-zero#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 503, 196, -307),
    ("GAS-2", "constructor-precedence-admin-zero-plus-min-pause-zero", "constructor-precedence-admin-zero-plus-min-pause-zero#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 481, 174, -307),
    ("GAS-2", "constructor-precedence-both-bound-inversions", "constructor-precedence-both-bound-inversions#0:primaryConstructor@0x6019cb557978296ba3c08a7b73225c0975dfb2f7", 529, 224, -305),
    ("GAS-3", "nonpayable-ADMIN", "nonpayable-ADMIN#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-MAX_HEARTBEAT_INTERVAL", "nonpayable-MAX_HEARTBEAT_INTERVAL#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-MAX_PAUSE_DURATION", "nonpayable-MAX_PAUSE_DURATION#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-MIN_HEARTBEAT_INTERVAL", "nonpayable-MIN_HEARTBEAT_INTERVAL#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-MIN_PAUSE_DURATION", "nonpayable-MIN_PAUSE_DURATION#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-getPausableCount", "nonpayable-getPausableCount#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-getPausables", "nonpayable-getPausables#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-getPauser", "nonpayable-getPauser#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-heartbeat", "nonpayable-heartbeat#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-heartbeatExpiry", "nonpayable-heartbeatExpiry#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-heartbeatInterval", "nonpayable-heartbeatInterval#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-isPauserLive", "nonpayable-isPauserLive#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-pause", "nonpayable-pause#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-pauseDuration", "nonpayable-pauseDuration#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-registerPauser", "nonpayable-registerPauser#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-setHeartbeatInterval", "nonpayable-setHeartbeatInterval#1:action", 43, 32, -11),
    ("GAS-3", "nonpayable-setPauseDuration", "nonpayable-setPauseDuration#1:action", 43, 32, -11),
    ("GAS-4", "runtime-empty-calldata", "runtime-empty-calldata#1:action", 68, 32, -36),
    ("GAS-5", "pause-return-true-large-32768", "pause-return-true-large-32768#2:action", 57317, 49873, -7444),
)
EXPECTED_COMPLETION_THRESHOLD_ROWS_SHA256 = \
    "49456665e2c6095cb1aa467231d78e45deef3d5dc9614248fcdcd756217c83fe"
EXPECTED_DISPATCHER_THRESHOLD_CASES = (
    ("GAS-3", "nonpayable-ADMIN", "nonzero-ADMIN()"),
    ("GAS-3", "nonpayable-MAX_HEARTBEAT_INTERVAL",
     "nonzero-MAX_HEARTBEAT_INTERVAL()"),
    ("GAS-3", "nonpayable-MAX_PAUSE_DURATION", "nonzero-MAX_PAUSE_DURATION()"),
    ("GAS-3", "nonpayable-MIN_HEARTBEAT_INTERVAL",
     "nonzero-MIN_HEARTBEAT_INTERVAL()"),
    ("GAS-3", "nonpayable-MIN_PAUSE_DURATION", "nonzero-MIN_PAUSE_DURATION()"),
    ("GAS-3", "nonpayable-getPausableCount", "nonzero-getPausableCount(address)"),
    ("GAS-3", "nonpayable-getPausables", "nonzero-getPausables()"),
    ("GAS-3", "nonpayable-getPauser", "nonzero-getPauser(address)"),
    ("GAS-3", "nonpayable-heartbeat", "nonzero-heartbeat()"),
    ("GAS-3", "nonpayable-heartbeatExpiry", "nonzero-heartbeatExpiry(address)"),
    ("GAS-3", "nonpayable-heartbeatInterval", "nonzero-heartbeatInterval()"),
    ("GAS-3", "nonpayable-isPauserLive", "nonzero-isPauserLive(address)"),
    ("GAS-3", "nonpayable-pause", "nonzero-pause(address)"),
    ("GAS-3", "nonpayable-pauseDuration", "nonzero-pauseDuration()"),
    ("GAS-3", "nonpayable-registerPauser",
     "nonzero-registerPauser(address,address)"),
    ("GAS-3", "nonpayable-setHeartbeatInterval",
     "nonzero-setHeartbeatInterval(uint256)"),
    ("GAS-3", "nonpayable-setPauseDuration",
     "nonzero-setPauseDuration(uint256)"),
    ("GAS-4", "runtime-empty-calldata", "short-0"),
)
EXPECTED_DISPATCHER_THRESHOLD_ROWS_SHA256 = \
    "b7b8f0ad5ca7e96de4cff76f54b4c661fce7f3faefd8e6d15526d9317db78bee"

RESOURCE_KEYS = {
    "schema", "adequateGasEnvelope", "gasModel", "lifecycle", "identities",
    "boundaries", "summary", "vectorDigests", "successfulLargeReturnPaths",
    "successfulRangeDelta", "oogControls", "representativePublicPaths",
    "shortReturnPaths", "adjudication",
}
BOUNDARY_KEYS = {
    "ordinal", "coordinate", "case", "boundary", "label", "phase",
    "orderWithinPhase", "adequacy", "solidityStatus", "blancStatus",
    "solidityGasLimit", "blancGasLimit", "solidityGasUsed", "blancGasUsed",
    "blancMinusSolidity", "comparisonClass",
}
INTRINSIC_BRANCH_KEYS = {
    "architecture", "classification", "directJumpDispatchAllowed",
    "admissionRequires", "rowCount", "orderedRows", "orderedRowsSha256",
}
INTRINSIC_BRANCH_ROW_KEYS = {
    "ordinal", "coordinate", "blancMinusSolidity",
}
COMPLETION_THRESHOLD_KEYS = {
    "schema", "definition", "scope", "search", "rowCount", "orderedRows",
    "orderedRowsSha256", "dispatcherCrossCheck",
}
COMPLETION_THRESHOLD_ROW_KEYS = {
    "ordinal", "class", "case", "coordinate", "solidityCompletionGas",
    "blancCompletionGas", "blancMinusSolidity", "comparisonClass",
    "solidityThresholdMinusOneCompletes", "blancThresholdMinusOneCompletes",
}
DISPATCHER_THRESHOLD_KEYS = {
    "owner", "selectedDispatcher", "independentDirectState",
    "productionOfficialRuntimeSha256", "rowCount", "orderedRows",
    "orderedRowsSha256",
}
DISPATCHER_THRESHOLD_ROW_KEYS = {
    "ordinal", "class", "case", "coordinate", "dispatcherCase",
    "solidityCompletionGas", "blancCompletionGas",
}
HEX256 = re.compile(r"[0-9a-f]{64}")
HEX_COMMIT = re.compile(r"[0-9a-f]{40}")
STATUS = re.compile(r"(?:success|revert|exception:[A-Za-z][A-Za-z0-9_]*)")


class ResourceSchemaError(RuntimeError):
    pass


def fail(label: str, message: str) -> NoReturn:
    raise ResourceSchemaError(f"{label}: {message}")


def exact_int(value: Any, label: str) -> int:
    if type(value) is not int:
        fail(label, "expected integer")
    return value


def exact_string(value: Any, label: str) -> str:
    if not isinstance(value, str):
        fail(label, "expected string")
    return value


def exact_bool(value: Any, label: str) -> bool:
    if type(value) is not bool:
        fail(label, "expected Boolean")
    return value


def canonical_digest(value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def require_keys(value: Any, keys: set[str], label: str) -> Mapping[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        fail(label, f"keys differ: expected {sorted(keys)}")
    return value


def tx_meta(descriptor: Any, phase: str, order: int, label: str) -> Mapping[str, Any]:
    if not isinstance(descriptor, dict):
        fail(label, "transaction descriptor is not an object")
    boundary = exact_int(descriptor.get("boundary"), label + ".boundary")
    gas = exact_int(descriptor.get("gas"), label + ".gas")
    actual_phase = exact_string(descriptor.get("phase"), label + ".phase")
    actual_order = exact_int(
        descriptor.get("orderWithinPhase"), label + ".orderWithinPhase")
    if actual_phase != phase or actual_order != order:
        fail(label, "phase/order differs from descriptor position")
    return {
        "boundary": boundary, "phase": phase, "orderWithinPhase": order,
        "gasLimit": gas,
    }


def expected_boundaries(
        manifest: Mapping[str, Any], label: str,
        expected_count: int) -> list[Mapping[str, Any]]:
    rows = manifest.get("rows")
    if not isinstance(rows, list):
        fail(label, "manifest rows are not an array")
    expected: list[Mapping[str, Any]] = []
    case_names: set[str] = set()
    for row_index, case_row in enumerate(rows):
        row_label = f"{label}.rows[{row_index}]"
        if not isinstance(case_row, dict):
            fail(row_label, "case row is not an object")
        case = exact_string(case_row.get("name"), row_label + ".name")
        if case in case_names:
            fail(row_label, "duplicate case name")
        case_names.add(case)
        tags = case_row.get("tags")
        execution = case_row.get("execution")
        if not isinstance(tags, list) or not all(isinstance(tag, str) for tag in tags):
            fail(row_label, "tags are not strings")
        if not isinstance(execution, dict):
            fail(row_label, "execution descriptor is not an object")
        boundary_order = execution.get("boundaryOrder")
        if not isinstance(boundary_order, list) or not all(
                isinstance(item, str) for item in boundary_order):
            fail(row_label, "boundaryOrder is not a string array")
        descriptors: list[Mapping[str, Any]] = []
        constructor = execution.get("constructor")
        if not isinstance(constructor, dict):
            fail(row_label, "primary constructor descriptor is missing")
        constructor_target = exact_string(
            constructor.get("target"), row_label + ".constructor.target")
        descriptors.append({
            "boundary": exact_int(
                constructor.get("boundary"), row_label + ".constructor.boundary"),
            "phase": "primaryConstructor", "orderWithinPhase": 0,
            "gasLimit": exact_int(
                constructor.get("gas"), row_label + ".constructor.gas"),
            "expectedLabel": f"primaryConstructor@{constructor_target}",
        })
        clone_constructor = execution.get("cloneConstructor")
        if clone_constructor is not None:
            if not isinstance(clone_constructor, dict):
                fail(row_label, "clone constructor descriptor is not an object")
            clone_target = exact_string(
                clone_constructor.get("target"), row_label + ".cloneConstructor.target")
            descriptors.append({
                "boundary": exact_int(
                    clone_constructor.get("boundary"),
                    row_label + ".cloneConstructor.boundary"),
                "phase": "cloneConstructor", "orderWithinPhase": 0,
                "gasLimit": exact_int(
                    clone_constructor.get("gas"), row_label + ".cloneConstructor.gas"),
                "expectedLabel": f"cloneConstructor@{clone_target}",
            })
        for phase in ("cloneHistory", "history"):
            phase_rows = execution.get(phase)
            if not isinstance(phase_rows, list):
                fail(row_label, f"{phase} is not an array")
            for order, descriptor in enumerate(phase_rows):
                item = dict(tx_meta(
                    descriptor, phase, order, f"{row_label}.{phase}[{order}]"))
                item["expectedLabel"] = f"{phase}[{order}]"
                descriptors.append(item)
        action = execution.get("action")
        if action is not None:
            item = dict(tx_meta(action, "action", 0, row_label + ".action"))
            item["expectedLabel"] = "action"
            descriptors.append(item)
        if len(boundary_order) != len(descriptors):
            fail(row_label, "boundaryOrder length differs from execution descriptors")
        if [item["boundary"] for item in descriptors] != list(range(len(descriptors))):
            fail(row_label, "descriptor boundaries are not contiguous in execution order")
        for item, actual_label in zip(descriptors, boundary_order):
            if actual_label != item["expectedLabel"]:
                fail(row_label, "boundaryOrder label differs from descriptor phase/order")
            boundary = item["boundary"]
            phase = item["phase"]
            oog_control = "oog-control" in tags and phase == "action"
            expected.append({
                "ordinal": len(expected),
                "coordinate": f"{case}#{boundary}:{actual_label}",
                "case": case, "boundary": boundary, "label": actual_label,
                "phase": phase, "orderWithinPhase": item["orderWithinPhase"],
                "gasLimit": item["gasLimit"],
                "adequacy": "oog-control" if oog_control else "adequate",
            })
    if len(expected) != expected_count:
        fail(label, "descriptor-derived boundary count is "
             f"{len(expected)}, expected {expected_count}")
    return expected


def derive_summary(boundaries: Sequence[Mapping[str, Any]]) -> Mapping[str, Any]:
    class_counts = {key: 0 for key in ("blanc-cheaper", "equal", "blanc-dearer")}
    adequacy_counts = {key: 0 for key in ("adequate", "oog-control")}
    for row in boundaries:
        comparison = row.get("comparisonClass")
        adequacy = row.get("adequacy")
        if comparison not in class_counts or adequacy not in adequacy_counts:
            raise ResourceSchemaError("summary: unknown comparison/adequacy class")
        class_counts[comparison] += 1
        adequacy_counts[adequacy] += 1
    return {
        "boundaryCount": len(boundaries),
        "adequacyCounts": adequacy_counts,
        "comparisonClassCounts": class_counts,
        "adequatePositiveDeltaCount": sum(
            row["adequacy"] == "adequate" and row["blancMinusSolidity"] > 0
            for row in boundaries),
        "successfulStrictImprovementCount": sum(
            row["adequacy"] == "adequate" and
            row["solidityStatus"] == "success" and row["blancStatus"] == "success" and
            row["blancMinusSolidity"] < 0 for row in boundaries),
        "solidityGasUsedTotal": sum(row["solidityGasUsed"] for row in boundaries),
        "blancGasUsedTotal": sum(row["blancGasUsed"] for row in boundaries),
        "blancMinusSolidityTotal": sum(
            row["blancMinusSolidity"] for row in boundaries),
    }


def validate_intrinsic_branch_dispatch(
        value: Any, boundaries: Sequence[Mapping[str, Any]],
        label: str) -> Mapping[str, Any]:
    evidence = require_keys(value, INTRINSIC_BRANCH_KEYS, label)
    architecture = exact_string(evidence.get("architecture"), label + ".architecture")
    classification = exact_string(
        evidence.get("classification"), label + ".classification")
    direct_jump = exact_bool(
        evidence.get("directJumpDispatchAllowed"),
        label + ".directJumpDispatchAllowed")
    admission = evidence.get("admissionRequires")
    if architecture != INTRINSIC_BRANCH_ARCHITECTURE or \
            classification != INTRINSIC_BRANCH_CLASSIFICATION or direct_jump is not False or \
            admission != INTRINSIC_BRANCH_ADMISSION_REQUIRES:
        fail(label, "architecture/admission rule differs from amendment 4")
    rows = evidence.get("orderedRows")
    if not isinstance(rows, list):
        fail(label, "orderedRows is not an array")
    expected_rows = [
        {
            "ordinal": row["ordinal"],
            "coordinate": row["coordinate"],
            "blancMinusSolidity": row["blancMinusSolidity"],
        }
        for row in boundaries
        if row["adequacy"] == "adequate" and row["blancMinusSolidity"] > 0
    ]
    for index, row in enumerate(rows):
        row_label = f"{label}.orderedRows[{index}]"
        require_keys(row, INTRINSIC_BRANCH_ROW_KEYS, row_label)
        exact_int(row.get("ordinal"), row_label + ".ordinal")
        exact_int(row.get("blancMinusSolidity"), row_label + ".blancMinusSolidity")
        exact_string(row.get("coordinate"), row_label + ".coordinate")
    if rows != expected_rows:
        fail(label, "ordered rows differ from all adequate positive boundaries")
    if exact_int(evidence.get("rowCount"), label + ".rowCount") != len(rows):
        fail(label, "rowCount differs from orderedRows")
    digest = exact_string(
        evidence.get("orderedRowsSha256"), label + ".orderedRowsSha256")
    if not HEX256.fullmatch(digest) or digest != canonical_digest(rows):
        fail(label, "ordered-row digest is not derived")
    if rows != EXPECTED_INTRINSIC_BRANCH_ROWS or \
            digest != EXPECTED_INTRINSIC_BRANCH_ROWS_SHA256:
        fail(label, "independent intrinsic-branch-dispatch row pin differs")
    return evidence


def validate_completion_thresholds(
        value: Any, descriptors: Sequence[Mapping[str, Any]],
        boundaries: Sequence[Mapping[str, Any]], official_runtime_sha256: str,
        label: str) -> Mapping[str, Any]:
    evidence = require_keys(value, COMPLETION_THRESHOLD_KEYS, label)
    if exact_int(evidence.get("schema"), label + ".schema") != 1 or \
            exact_string(evidence.get("definition"), label + ".definition") != \
                COMPLETION_THRESHOLD_DEFINITION or \
            exact_string(evidence.get("scope"), label + ".scope") != \
                COMPLETION_THRESHOLD_SCOPE or \
            exact_string(evidence.get("search"), label + ".search") != \
                COMPLETION_THRESHOLD_SEARCH:
        fail(label, "definition/scope/search differs from the independent threshold contract")
    if len(EXPECTED_COMPLETION_THRESHOLD_PINS) != 33 or \
            EXPECTED_COMPLETION_THRESHOLD_ROWS_SHA256.startswith("PENDING-") or \
            EXPECTED_DISPATCHER_THRESHOLD_ROWS_SHA256.startswith("PENDING-"):
        fail(label, "independent completion-threshold pins are not installed")
    expected_rows = []
    class_counts = {f"GAS-{index}": 0 for index in range(1, 6)}
    for ordinal, pin in enumerate(EXPECTED_COMPLETION_THRESHOLD_PINS):
        gas_class, case, coordinate, solidity, blanc, pinned_delta = pin
        delta = blanc - solidity
        if pinned_delta != delta:
            fail(label, f"independent threshold delta pin is not derived: {case}")
        if gas_class not in class_counts:
            fail(label, f"independent threshold class is unknown: {gas_class}")
        class_counts[gas_class] += 1
        expected_rows.append({
            "ordinal": ordinal, "class": gas_class, "case": case,
            "coordinate": coordinate,
            "solidityCompletionGas": solidity,
            "blancCompletionGas": blanc,
            "blancMinusSolidity": delta,
            "comparisonClass": "blanc-cheaper" if delta < 0 else
                "blanc-dearer" if delta > 0 else "equal",
            "solidityThresholdMinusOneCompletes": False,
            "blancThresholdMinusOneCompletes": False,
        })
    if class_counts != {
            "GAS-1": 6, "GAS-2": 8, "GAS-3": 17,
            "GAS-4": 1, "GAS-5": 1}:
        fail(label, "independent GAS-1..GAS-5 threshold roster differs")
    rows = evidence.get("orderedRows")
    if not isinstance(rows, list):
        fail(label, "orderedRows is not an array")
    for index, row in enumerate(rows):
        row_label = f"{label}.orderedRows[{index}]"
        require_keys(row, COMPLETION_THRESHOLD_ROW_KEYS, row_label)
        for field in (
                "ordinal", "solidityCompletionGas", "blancCompletionGas",
                "blancMinusSolidity"):
            exact_int(row.get(field), row_label + "." + field)
        for field in ("class", "case", "coordinate", "comparisonClass"):
            exact_string(row.get(field), row_label + "." + field)
        exact_bool(
            row.get("solidityThresholdMinusOneCompletes"),
            row_label + ".solidityThresholdMinusOneCompletes")
        exact_bool(
            row.get("blancThresholdMinusOneCompletes"),
            row_label + ".blancThresholdMinusOneCompletes")
        solidity = row["solidityCompletionGas"]
        blanc = row["blancCompletionGas"]
        delta = blanc - solidity
        comparison = "blanc-cheaper" if delta < 0 else \
            "blanc-dearer" if delta > 0 else "equal"
        if row["blancMinusSolidity"] != delta or \
                row["comparisonClass"] != comparison or \
                row["solidityThresholdMinusOneCompletes"] is not False or \
                row["blancThresholdMinusOneCompletes"] is not False:
            fail(row_label, "threshold delta/class/minimality is not derived")
        if delta > 0:
            fail(row_label, "optimized completion threshold is Blanc-dearer")
    if rows != expected_rows:
        fail(label, "ordered threshold rows differ from independent exact pins")
    if exact_int(evidence.get("rowCount"), label + ".rowCount") != 33:
        fail(label, "threshold rowCount is not exactly 33")
    digest = exact_string(
        evidence.get("orderedRowsSha256"), label + ".orderedRowsSha256")
    if not HEX256.fullmatch(digest) or digest != canonical_digest(rows) or \
            digest != EXPECTED_COMPLETION_THRESHOLD_ROWS_SHA256:
        fail(label, "threshold ordered-row digest differs from the independent pin")
    descriptor_by_case: dict[str, Mapping[str, Any]] = {}
    measured_by_coordinate = {
        row["coordinate"]: row for row in boundaries
    }
    for descriptor in descriptors:
        descriptor_by_case[descriptor["case"]] = descriptor
    for row in rows:
        descriptor = descriptor_by_case.get(row["case"])
        measured = measured_by_coordinate.get(row["coordinate"])
        if descriptor is None or row["coordinate"] != descriptor["coordinate"] or \
                measured is None or measured["adequacy"] != "adequate":
            fail(label, "threshold witness is not its case's adequate final boundary")
        if not 0 <= row["solidityCompletionGas"] <= 20_000_000 or \
                not 0 <= row["blancCompletionGas"] <= 20_000_000:
            fail(label, "completion threshold lies outside the adequate envelope")

    cross_label = label + ".dispatcherCrossCheck"
    cross = require_keys(
        evidence.get("dispatcherCrossCheck"), DISPATCHER_THRESHOLD_KEYS,
        cross_label)
    if exact_string(cross.get("owner"), cross_label + ".owner") != \
            "scripts/check-lido-circuit-breaker-dispatchers.py" or \
            exact_string(cross.get("selectedDispatcher"),
                         cross_label + ".selectedDispatcher") != \
                "shared-hybrid-5-4-4-4" or \
            exact_bool(cross.get("independentDirectState"),
                       cross_label + ".independentDirectState") is not True or \
            exact_string(cross.get("productionOfficialRuntimeSha256"),
                         cross_label + ".productionOfficialRuntimeSha256") != \
                official_runtime_sha256:
        fail(cross_label, "dispatcher owner/selection/runtime identity differs")
    completion_by_case = {row["case"]: row for row in rows}
    expected_cross_rows = []
    for ordinal, (gas_class, case, dispatcher_case) in enumerate(
            EXPECTED_DISPATCHER_THRESHOLD_CASES):
        completion = completion_by_case.get(case)
        if completion is None or completion["class"] != gas_class:
            fail(cross_label, f"dispatcher cross-check case is not a threshold row: {case}")
        expected_cross_rows.append({
            "ordinal": ordinal, "class": gas_class, "case": case,
            "coordinate": completion["coordinate"],
            "dispatcherCase": dispatcher_case,
            "solidityCompletionGas": completion["solidityCompletionGas"],
            "blancCompletionGas": completion["blancCompletionGas"],
        })
    cross_rows = cross.get("orderedRows")
    if not isinstance(cross_rows, list):
        fail(cross_label, "orderedRows is not an array")
    for index, row in enumerate(cross_rows):
        row_label = f"{cross_label}.orderedRows[{index}]"
        require_keys(row, DISPATCHER_THRESHOLD_ROW_KEYS, row_label)
        for field in (
                "ordinal", "solidityCompletionGas", "blancCompletionGas"):
            exact_int(row.get(field), row_label + "." + field)
        for field in ("class", "case", "coordinate", "dispatcherCase"):
            exact_string(row.get(field), row_label + "." + field)
    if cross_rows != expected_cross_rows or \
            exact_int(cross.get("rowCount"), cross_label + ".rowCount") != 18:
        fail(cross_label, "exact GAS-3/4 dispatcher threshold rows differ")
    cross_digest = exact_string(
        cross.get("orderedRowsSha256"), cross_label + ".orderedRowsSha256")
    if not HEX256.fullmatch(cross_digest) or \
            cross_digest != canonical_digest(cross_rows) or \
            cross_digest != EXPECTED_DISPATCHER_THRESHOLD_ROWS_SHA256:
        fail(cross_label, "dispatcher threshold digest differs from independent pin")
    return evidence


def expected_identities(manifest: Mapping[str, Any], label: str) -> Mapping[str, Any]:
    oracle = manifest.get("oracle")
    blanc = manifest.get("blanc")
    execution = manifest.get("execution")
    if not isinstance(oracle, dict) or not isinstance(blanc, dict) or \
            not isinstance(execution, dict):
        fail(label, "manifest identity owners are missing")
    if oracle.get("sourceCommit") != REFERENCE_SOURCE_COMMIT or \
            oracle.get("officialRuntimeSha256") != \
            SOLIDITY_IDENTITIES["solidityOfficialRuntimeSha256"] or \
            oracle.get("independentRuntimeSha256") != \
            SOLIDITY_IDENTITIES["solidityIndependentRuntimeSha256"] or \
            execution.get("eelsCommit") != EELS_PIN:
        fail(label, "manifest oracle/EELS identity differs")
    try:
        return {
            "eelsCommit": execution["eelsCommit"],
            "referenceSourceCommit": oracle["sourceCommit"],
            **SOLIDITY_IDENTITIES,
            "blancCreationTemplateSha256": blanc["creationTemplate"]["sha256"],
            "blancOfficialFullCreateSha256": blanc["official"]["fullCreateSha256"],
            "blancOfficialRuntimeSha256": blanc["official"]["runtimeSha256"],
            "blancIndependentFullCreateSha256": blanc["independent"]["fullCreateSha256"],
            "blancIndependentRuntimeSha256": blanc["independent"]["runtimeSha256"],
        }
    except (KeyError, TypeError) as exc:
        fail(label, f"manifest artifact identity owner is incomplete: {exc}")


def validate_resource_manifest(manifest: Mapping[str, Any], label: str = "manifest") -> Mapping[str, Any]:
    if not isinstance(manifest, dict):
        fail(label, "manifest root is not an object")
    raw_resources = manifest.get("resourceEvidence")
    if not isinstance(raw_resources, dict):
        fail(label, "resource evidence is not an object")
    raw_lifecycle = raw_resources.get("lifecycle")
    if not isinstance(raw_lifecycle, dict):
        fail(label, "resource lifecycle is not an object")
    raw_stage = raw_lifecycle.get("stage")
    if raw_stage not in EXPECTED_BOUNDARIES:
        fail(label, "resource lifecycle stage is neither baseline nor optimized")
    expected_resource_keys = set(RESOURCE_KEYS)
    if raw_stage == "optimized":
        expected_resource_keys.add("successfulReturnShape")
        expected_resource_keys.add("intrinsicBranchDispatch")
        expected_resource_keys.add("completionThresholds")
    resources = require_keys(raw_resources, expected_resource_keys,
                             label + ".resourceEvidence")
    if exact_int(resources.get("schema"), label + ".resourceEvidence.schema") != \
            RESOURCE_SCHEMA:
        fail(label, "resource schema is not 1")
    if exact_int(resources.get("adequateGasEnvelope"),
                 label + ".resourceEvidence.adequateGasEnvelope") != 20_000_000:
        fail(label, "adequate-gas envelope differs")
    model = require_keys(resources.get("gasModel"), set(EXPECTED_MODEL),
                         label + ".resourceEvidence.gasModel")
    for key, expected_value in EXPECTED_MODEL.items():
        if type(expected_value) is bool:
            actual_value = exact_bool(
                model.get(key), label + ".resourceEvidence.gasModel." + key)
        else:
            actual_value = exact_string(
                model.get(key), label + ".resourceEvidence.gasModel." + key)
        if actual_value != expected_value:
            fail(label, "gas model differs from direct pre-refund EELS Prague messages")
    lifecycle = require_keys(resources.get("lifecycle"), {
        "stage", "baselineBlancCommit", "baselineManifestSha256",
        "optimizedTransitionRequires",
    }, label + ".resourceEvidence.lifecycle")
    baseline_commit = exact_string(
        lifecycle.get("baselineBlancCommit"),
        label + ".resourceEvidence.lifecycle.baselineBlancCommit")
    baseline_manifest = exact_string(
        lifecycle.get("baselineManifestSha256"),
        label + ".resourceEvidence.lifecycle.baselineManifestSha256")
    expected_transition = EXPECTED_TRANSITIONS[raw_stage]
    transition = require_keys(
        lifecycle.get("optimizedTransitionRequires"), set(expected_transition),
        label + ".resourceEvidence.lifecycle.optimizedTransitionRequires")
    for key, expected_value in expected_transition.items():
        if exact_bool(
                transition.get(key),
                label + ".resourceEvidence.lifecycle.optimizedTransitionRequires." + key
        ) != expected_value:
            fail(label, "resource lifecycle transition lock differs")
    if not HEX_COMMIT.fullmatch(baseline_commit) or \
            not HEX256.fullmatch(baseline_manifest) or \
            baseline_commit != BASELINE_BLANC_COMMIT or \
            baseline_manifest != BASELINE_MANIFEST_SHA256:
        fail(label, "resource lifecycle baseline/transition lock differs")
    stage = exact_string(
        lifecycle.get("stage"), label + ".resourceEvidence.lifecycle.stage")
    if stage not in EXPECTED_VECTOR_PINS:
        fail(label, "resource lifecycle stage is neither baseline nor optimized")
    expected_identity = expected_identities(manifest, label)
    identities = require_keys(
        resources.get("identities"), set(expected_identity),
        label + ".resourceEvidence.identities")
    if identities != expected_identity:
        fail(label, "resource identities differ from independent manifest owners")
    for key, value in identities.items():
        pattern = HEX_COMMIT if key in {"eelsCommit", "referenceSourceCommit"} else HEX256
        if not isinstance(value, str) or not pattern.fullmatch(value):
            fail(label, "resource identity is not a lowercase SHA/commit digest")
    if identities["eelsCommit"] != EELS_PIN or \
            identities["referenceSourceCommit"] != REFERENCE_SOURCE_COMMIT:
        fail(label, "EELS/reference source identity differs")
    for key, value in SOLIDITY_IDENTITIES.items():
        if identities.get(key) != value:
            fail(label, "Solidity resource identity differs")
    baseline_blanc = {key: identities[key] for key in BASELINE_BLANC_IDENTITIES}
    if stage == "baseline" and baseline_blanc != BASELINE_BLANC_IDENTITIES:
        fail(label, "baseline lifecycle Blanc identity drifted; transition required")
    if stage == "optimized" and baseline_blanc == BASELINE_BLANC_IDENTITIES:
        fail(label, "optimized lifecycle still carries the complete baseline Blanc identity")
    if stage == "optimized":
        summary_preview = resources.get("summary")
        if not isinstance(summary_preview, dict):
            fail(label, "optimized resource summary is not an object")
        if exact_int(summary_preview.get("successfulStrictImprovementCount"),
                     label + ".resourceEvidence.summary.successfulStrictImprovementCount") < 1:
            fail(label, "optimized lifecycle has no strict successful improvement")
        candidate_shape = resources.get("successfulReturnShape")
        shape_checked = isinstance(candidate_shape, dict) and \
            "successfulStaticcallRows" in candidate_shape
        # Exercise the independent captured-row full-copy falsifier even while
        # the lifecycle is deliberately held closed on its pending vector pin.
        if shape_checked:
            try:
                validate_candidate_shape_against_resource_paths(
                    candidate_shape,
                    resources.get("successfulLargeReturnPaths"),
                    label + ".resourceEvidence.successfulReturnShape")
            except Ac5ShapeError as exc:
                fail(label, str(exc))
        pins = EXPECTED_VECTOR_PINS[stage]
        if any(value is None or value.startswith("PENDING-")
               for value in pins.values()):
            fail(label, f"{stage} independent resource-vector pin is not installed")
        if not shape_checked:
            try:
                validate_candidate_shape_evidence(
                    candidate_shape,
                    label + ".resourceEvidence.successfulReturnShape")
            except Ac5ShapeError as exc:
                fail(label, str(exc))

    expected_count = EXPECTED_BOUNDARIES[stage]
    expected = expected_boundaries(manifest, label, expected_count)
    boundaries = resources.get("boundaries")
    if not isinstance(boundaries, list) or len(boundaries) != expected_count:
        fail(label, "resource boundary deletion/count drifted")
    coordinates: set[str] = set()
    for index, (row, descriptor) in enumerate(zip(boundaries, expected)):
        row_label = f"{label}.resourceEvidence.boundaries[{index}]"
        require_keys(row, BOUNDARY_KEYS, row_label)
        for field in ("ordinal", "boundary", "orderWithinPhase", "solidityGasLimit",
                      "blancGasLimit", "solidityGasUsed", "blancGasUsed",
                      "blancMinusSolidity"):
            exact_int(row.get(field), row_label + "." + field)
        for field in ("coordinate", "case", "label", "phase", "adequacy",
                      "solidityStatus", "blancStatus", "comparisonClass"):
            exact_string(row.get(field), row_label + "." + field)
        coordinate = row["coordinate"]
        if coordinate in coordinates:
            fail(row_label, "duplicate resource coordinate")
        coordinates.add(coordinate)
        for field in ("ordinal", "coordinate", "case", "boundary", "label", "phase",
                      "orderWithinPhase", "adequacy"):
            if row[field] != descriptor[field]:
                fail(row_label, f"resource {field} does not align with boundaryOrder")
        if row["solidityGasLimit"] != descriptor["gasLimit"] or \
                row["blancGasLimit"] != descriptor["gasLimit"]:
            fail(row_label, "resource gasLimit does not align with descriptor")
        if not STATUS.fullmatch(row["solidityStatus"]) or \
                not STATUS.fullmatch(row["blancStatus"]):
            fail(row_label, "resource status has invalid syntax")
        if row["solidityStatus"] != row["blancStatus"]:
            fail(row_label, "resource statuses differ")
        if not 0 <= row["solidityGasUsed"] <= row["solidityGasLimit"] or \
                not 0 <= row["blancGasUsed"] <= row["blancGasLimit"]:
            fail(row_label, "resource gasUsed lies outside gasLimit")
        if descriptor["adequacy"] == "oog-control":
            if row["solidityStatus"] != "exception:OutOfGasError":
                fail(row_label, "named OOG control did not exhaust gas")
        elif row["solidityStatus"] == "exception:OutOfGasError":
            fail(row_label, "unlabelled adequate-gas boundary exhausted gas")
        delta = row["blancGasUsed"] - row["solidityGasUsed"]
        if row["blancMinusSolidity"] != delta:
            fail(row_label, "resource delta is not derived from side gas")
        comparison = "blanc-cheaper" if delta < 0 else "blanc-dearer" if delta > 0 else "equal"
        if row["comparisonClass"] != comparison:
            fail(row_label, "resource comparison class is not derived from delta")

    summary_claim = require_keys(resources.get("summary"), {
        "boundaryCount", "adequacyCounts", "comparisonClassCounts",
        "adequatePositiveDeltaCount", "successfulStrictImprovementCount",
        "solidityGasUsedTotal", "blancGasUsedTotal", "blancMinusSolidityTotal",
    }, label + ".resourceEvidence.summary")
    adequacy_claim = require_keys(summary_claim.get("adequacyCounts"),
                                  {"adequate", "oog-control"},
                                  label + ".resourceEvidence.summary.adequacyCounts")
    comparison_claim = require_keys(
        summary_claim.get("comparisonClassCounts"),
        {"blanc-cheaper", "equal", "blanc-dearer"},
        label + ".resourceEvidence.summary.comparisonClassCounts")
    for key in ("boundaryCount", "adequatePositiveDeltaCount",
                "successfulStrictImprovementCount", "solidityGasUsedTotal",
                "blancGasUsedTotal", "blancMinusSolidityTotal"):
        exact_int(summary_claim.get(key), label + ".resourceEvidence.summary." + key)
    for key, value in adequacy_claim.items():
        exact_int(value, label + ".resourceEvidence.summary.adequacyCounts." + key)
    for key, value in comparison_claim.items():
        exact_int(value, label + ".resourceEvidence.summary.comparisonClassCounts." + key)
    summary = derive_summary(boundaries)
    if summary_claim != summary:
        fail(label, "resource summary is not derived from the full vector")
    intrinsic_dispatch = None
    completion_thresholds = None
    if stage == "optimized":
        intrinsic_dispatch = validate_intrinsic_branch_dispatch(
            resources.get("intrinsicBranchDispatch"), boundaries,
            label + ".resourceEvidence.intrinsicBranchDispatch")
        if summary["adequatePositiveDeltaCount"] != intrinsic_dispatch["rowCount"]:
            fail(label, "optimized lifecycle has an unclassified adequate positive delta")
        if summary["successfulStrictImprovementCount"] < 1:
            fail(label, "optimized lifecycle has no strict successful improvement")
        completion_thresholds = validate_completion_thresholds(
            resources.get("completionThresholds"), expected, boundaries,
            identities["blancOfficialRuntimeSha256"],
            label + ".resourceEvidence.completionThresholds")

    coordinate_payload = ("\n".join(row["coordinate"] for row in boundaries) + "\n").encode()
    vector_payload = {
        "schema": resources["schema"], "gasModel": resources["gasModel"],
        "lifecycle": resources["lifecycle"], "identities": resources["identities"],
        "boundaries": boundaries,
    }
    if intrinsic_dispatch is not None:
        vector_payload["intrinsicBranchDispatch"] = intrinsic_dispatch
    if completion_thresholds is not None:
        vector_payload["completionThresholds"] = completion_thresholds
    actual_digests = {
        "orderedCoordinatesSha256": hashlib.sha256(coordinate_payload).hexdigest(),
        "fullResourceVectorSha256": canonical_digest(vector_payload),
    }
    digest_claim = require_keys(
        resources.get("vectorDigests"), set(actual_digests),
        label + ".resourceEvidence.vectorDigests")
    for key, value in digest_claim.items():
        if not HEX256.fullmatch(exact_string(
                value, label + ".resourceEvidence.vectorDigests." + key)):
            fail(label, "resource-vector digest is not lowercase SHA-256")
    if digest_claim != actual_digests:
        fail(label, "embedded resource-vector digests are not derived")
    pins = EXPECTED_VECTOR_PINS[stage]
    if actual_digests != pins:
        fail(label, f"{stage} independent resource-vector digest differs")
    return {
        "stage": stage, "summary": summary, "digests": actual_digests,
        "expectedBoundaryCount": expected_count,
        "completionThresholdCount": 0 if completion_thresholds is None else
            completion_thresholds["rowCount"],
    }


def reject_constant(value: str) -> NoReturn:
    raise ValueError(f"non-finite JSON constant {value}")


def reject_duplicate(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key}")
        result[key] = value
    return result


def load_manifest(path: Path) -> Mapping[str, Any]:
    raw = path.read_text()
    value = json.loads(raw, object_pairs_hook=reject_duplicate, parse_constant=reject_constant)
    if raw != json.dumps(value, indent=2, sort_keys=True) + "\n":
        raise ResourceSchemaError(f"{path}: manifest is not canonical JSON")
    return value


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args(argv)
    result = validate_resource_manifest(load_manifest(args.manifest), str(args.manifest))
    summary = result["summary"]
    print(
        "OK — Lido CircuitBreaker resource schema: "
        f"{summary['boundaryCount']}/{result['expectedBoundaryCount']} ordered boundaries; "
        f"lifecycle {result['stage']}; "
        f"{result['completionThresholdCount']} completion thresholds; "
        "coordinate/vector digests independently pinned"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (OSError, ValueError, json.JSONDecodeError, ResourceSchemaError,
            Ac5ShapeError) as exc:
        print("REGRESSION — Lido CircuitBreaker resource schema: " + str(exc),
              file=sys.stderr)
        raise SystemExit(1)
