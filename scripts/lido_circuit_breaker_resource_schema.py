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
# The optimized count is the provisional AC5 stage.  O4 threshold descriptors
# intentionally expand and repin it before the optimized lifecycle can land.
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
EXPECTED_TRANSITION = {
    "adequateGasDominance": True,
    "strictSuccessfulImprovement": True,
    "independentDigestRepin": True,
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

# These pins are intentionally outside the mutable generator.  Baseline pins
# are filled only after the complete 172-case/455-boundary baseline
# measurement.  The provisional AC5-stage optimized descriptor set adds the
# 65,536-byte row plus two long failure-bubbling rows and therefore has 175
# cases/464 boundaries.  Its coordinate pin below is intentionally not the
# final O4-expanded pin.  The transition
# remains fail-closed until O4 has repinned the descriptors and a measured
# full-vector pin replaces None in a deliberate reviewable edit.
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
        "fullResourceVectorSha256": None,
    },
}

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
    transition = require_keys(
        lifecycle.get("optimizedTransitionRequires"), set(EXPECTED_TRANSITION),
        label + ".resourceEvidence.lifecycle.optimizedTransitionRequires")
    for key, expected_value in EXPECTED_TRANSITION.items():
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
        if exact_int(summary_preview.get("adequatePositiveDeltaCount"),
                     label + ".resourceEvidence.summary.adequatePositiveDeltaCount") != 0:
            fail(label, "optimized lifecycle has a positive adequate-gas delta")
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
    if stage == "optimized":
        if summary["adequatePositiveDeltaCount"] != 0:
            fail(label, "optimized lifecycle has a positive adequate-gas delta")
        if summary["successfulStrictImprovementCount"] < 1:
            fail(label, "optimized lifecycle has no strict successful improvement")

    coordinate_payload = ("\n".join(row["coordinate"] for row in boundaries) + "\n").encode()
    vector_payload = {
        "schema": resources["schema"], "gasModel": resources["gasModel"],
        "lifecycle": resources["lifecycle"], "identities": resources["identities"],
        "boundaries": boundaries,
    }
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
        f"lifecycle {result['stage']}; coordinate/vector digests independently pinned"
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
