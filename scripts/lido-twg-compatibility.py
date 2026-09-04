#!/usr/bin/env python3
"""Fail-closed synchronization for the Lido TWG claim documents.

Ordinary use is network-free:

    python3 scripts/lido-twg-compatibility.py check
    python3 scripts/lido-twg-compatibility.py generate [--output-dir DIR]
    python3 scripts/lido-twg-compatibility.py fill

``check`` accepts only completed documents.  It rejects machine placeholders,
unresolved behavioral deviations, marker drift, and a B1/B2 evidence contract
that no longer supports the rendered identities and measurements.

``generate`` is a non-mutating preview unless ``--output-dir`` is supplied.
``fill`` replaces the two checked-in templates in place.  Both commands are
all-or-nothing: they first validate the exact placeholder inventory, the B1
lock, and the B2 ``documentFill`` contract.  No document is changed if any
required field is absent or malformed.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
import re
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CENSUS = ROOT / "scripts" / "lido-twg-census.json"
DEFAULT_LOCK = ROOT / "scripts" / "lido-twg-reference.json"
DEFAULT_MANIFEST = ROOT / "scripts" / "fixtures" / "lido-twg" / "manifest.json"
DEFAULT_COMPATIBILITY = ROOT / "LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_COMPATIBILITY.md"
DEFAULT_DEVIATIONS = ROOT / "LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_DEVIATIONS.md"

CONSTRUCTOR_ARGUMENTS = ["address", "address", "uint256", "uint256", "uint256"]
CROSSCUTS = [
    "scope-oracles",
    "dispatch-calldata",
    "pause-sentinel",
    "access-control",
    "role-enumeration",
    "exit-limit",
    "trigger-choreography",
    "events-errors-rollback",
    "logical-state-projection",
    "finite-evidence",
    "gas-boundary",
    "formal-proof-boundary",
    "deployment-boundary",
]
DEVIATION_ROWS = [
    {"id": "TWG-D01", "class": "returndata"},
    {"id": "TWG-D02", "class": "returndata"},
    {"id": "TWG-D03", "class": "returndata"},
    {"id": "TWG-D04", "class": "enumeration-order"},
    {"id": "TWG-D05", "class": "collision-refusal"},
]
IMPLEMENTATION_DIFFERENCES = [
    {"id": "TWG-I01", "class": "storage-layout"},
]
COMPATIBILITY_HEADINGS = [
    "## Evidence identities",
    "## Coverage criterion",
    "## Runtime endpoints",
    "## Constructor",
    "## Event census",
    "## Cross-cutting boundary",
    "## Strongest honest port claim",
]
DEVIATION_HEADINGS = [
    "## Behavioral deviations and dispositions",
    "## Pending behavioral deviations",
    "## Accepted low-level implementation differences",
    "## Code-size comparison",
    "## Named-path gas comparison",
    "## Explicit equivalence exclusions and nonclaims",
    "## Matched sentinel behavior is not a deviation",
]

# The order is part of the document/manifest contract.  The key names map to
# the four GAS_<KEY>_{REF,BLANC,DELTA,COORD} placeholders.
GAS_ROWS = [
    ("CONSTRUCTOR_SUCCESS", "constructor-success"),
    ("PAUSE_FOR_FINITE", "pauseFor-finite"),
    ("PAUSE_FOR_SENTINEL", "pauseFor-sentinel"),
    ("PAUSE_UNTIL_FINITE", "pauseUntil-finite"),
    ("PAUSE_UNTIL_SENTINEL", "pauseUntil-sentinel"),
    ("RESUME", "resume"),
    ("IS_PAUSED_FALSE", "isPaused-resumed"),
    ("IS_PAUSED_TRUE", "isPaused-paused"),
    ("GRANT_ROLE", "grantRole-fresh"),
    ("REVOKE_ROLE", "revokeRole-existing"),
    ("RENOUNCE_ROLE", "renounceRole-self"),
    ("GET_ROLE_MEMBER", "getRoleMember"),
    ("GET_ROLE_MEMBER_COUNT", "getRoleMemberCount"),
    ("SET_LIMIT", "setExitRequestLimit"),
    ("GET_LIMIT_SAME_FRAME", "getExitRequestLimitFullInfo-same-frame"),
    ("GET_LIMIT_REFILLED", "getExitRequestLimitFullInfo-refilled"),
    ("TRIGGER_EMPTY", "trigger-empty"),
    ("TRIGGER_SINGLE_EXACT", "trigger-single-no-refund"),
    ("TRIGGER_EXPLICIT_REFUND", "trigger-single-explicit-refund"),
    ("TRIGGER_SENDER_REFUND", "trigger-single-sender-refund"),
    ("TRIGGER_MULTIPLE", "trigger-multiple"),
    ("TRIGGER_LIMIT", "trigger-limit-exceeded"),
    ("ROLE_UNAUTHORIZED", "role-gate-unauthorized"),
    ("DEFAULT_ADMIN_ROLE_VIEW", "defaultAdminRole"),
    ("PAUSE_INFINITELY_VIEW", "pauseInfinitely"),
    ("SUPPORTS_INTERFACE", "supportsInterface"),
    ("HAS_ROLE", "hasRole"),
    ("GET_RESUME_TIMESTAMP", "getResumeSinceTimestamp"),
    ("GRANT_ROLE_DUPLICATE", "grantRole-duplicate"),
    ("REVOKE_ROLE_MISSING", "revokeRole-missing"),
    ("RENOUNCE_ROLE_WRONG_ACCOUNT", "renounceRole-wrong-account"),
    ("GET_ROLE_MEMBER_OOB", "getRoleMember-oob"),
    ("ROLE_ENUMERATION_CROSS_ROLE", "role-enumeration-cross-role-order"),
    ("ROLE_COLLISION_REFUSAL", "role-flat-key-collision-refusal"),
    ("PAUSE_FOR_WHEN_PAUSED", "pauseFor-when-paused"),
    ("PAUSE_UNTIL_WHEN_PAUSED", "pauseUntil-when-paused"),
    ("PAUSE_ZERO_DURATION", "pauseFor-zero-duration"),
    ("PAUSE_UNTIL_PAST", "pauseUntil-past"),
    ("RESUME_WHEN_RESUMED", "resume-when-resumed"),
    ("SET_LIMIT_MAX_TOO_LARGE", "setExitRequestLimit-max-too-large"),
    ("SET_LIMIT_FRAME_TOO_LARGE", "setExitRequestLimit-frame-too-large"),
    ("SET_LIMIT_EXITS_ABOVE_MAX", "setExitRequestLimit-exits-above-max"),
    ("SET_LIMIT_ZERO_FRAME", "setExitRequestLimit-zero-frame"),
    ("TRIGGER_INSUFFICIENT_FEE", "trigger-insufficient-fee"),
    ("TRIGGER_PAUSED", "trigger-paused"),
    ("TRIGGER_ZERO_VALUE", "trigger-zero-value"),
    ("TRIGGER_LOCATOR_REVERT", "trigger-locator-revert"),
    ("TRIGGER_FEE_QUERY_REVERT", "trigger-fee-query-revert"),
    ("TRIGGER_VAULT_REVERT", "trigger-vault-revert"),
    ("TRIGGER_ROUTER_REVERT", "trigger-router-revert"),
    ("TRIGGER_REFUND_REVERT", "trigger-refund-revert"),
]

BLANC_ARTIFACT_COMMIT = "df9ce992b98b1eb784ab631be312cba4550ff61b"
BLANC_PROOF_COMMIT = "35ba1e1b137529482180adccd44ae0da70417ac4"
CALLDATA_EXCLUSION_TEXT = (
    "nested malformed dynamic ABI, empty/unknown/short dispatch, trailing calldata, and "
    "recognized-selector nonpayability are untested and excluded"
)
INTERFACE_ID_EXCLUSION_TEXT = (
    "supportsInterface IDs other than 0x5a05180f are untested and excluded"
)

LOCK_TOKENS = {
    "B1_MAINNET_BLOCK",
    "B1_MAINNET_CODE_HASH",
    "B1_MAINNET_ROLE_PAUSE_SNAPSHOT_SHA256",
    "B1_REFERENCE_FULL_CREATE_BYTES",
    "B1_REFERENCE_FULL_CREATE_SHA256",
    "B1_REFERENCE_LOCK_SCHEMA",
    "B1_REFERENCE_LOCK_SHA256",
    "B1_REFERENCE_RUNTIME_BYTES",
    "B1_REFERENCE_RUNTIME_SHA256",
    "B1_SOLC_ARTIFACT_SHA256",
    "B1_SOLC_VERSION",
}
SUMMARY_TOKENS = {
    "B2_CALLDATA_SCOPE_SUMMARY",
    "B2_CODE_SIZE_HEADROOM_SUMMARY",
    "B2_CONSTRUCTOR_COVERAGE_SUMMARY",
    "B2_COVERAGE_SUMMARY",
    "B2_D01_ROW_SET",
    "B2_D01_SIZE_ATTRIBUTION",
    "B2_D02_RESOURCE_ATTRIBUTION",
    "B2_D02_ROW_SET",
    "B2_D03_RESOURCE_ATTRIBUTION",
    "B2_D03_ROW_SET",
    "B2_D04_EXPECTED_ORDERS",
    "B2_D04_ROW_SET",
    "B2_D05_PROJECTION_SHA256",
    "B2_D05_RESOURCE_ATTRIBUTION",
    "B2_D05_ROW_SET",
    "B2_DIFFERENTIAL_VERDICT",
    "B2_PER_SELECTOR_RESOURCE_COVERAGE_SUMMARY",
    "B2_PROJECTION_SCHEMA_SHA256",
}
DERIVED_MANIFEST_TOKENS = {
    "B2_BLANC_ARTIFACT_PROGRAM_COMMIT",
    "B2_BLANC_PROOF_CERTIFICATE_COMMIT",
    "B2_BLANC_CREATION_TEMPLATE_BYTES",
    "B2_BLANC_CREATION_TEMPLATE_SHA256",
    "B2_BLANC_FULL_CREATE_BYTES",
    "B2_BLANC_FULL_CREATE_SHA256",
    "B2_BLANC_RUNTIME_BYTES",
    "B2_BLANC_RUNTIME_SHA256",
    "B2_CASE_COUNT",
    "B2_FULL_CREATE_BYTE_DELTA",
    "B2_GAS_BOUNDARY_DEFINITION",
    "B2_MANIFEST_SCHEMA",
    "B2_MANIFEST_SHA256",
    "B2_NAMED_GAS_ROW_COUNT",
    "B2_POSITIVE_GAS_ROWS_TABLE",
    "B2_POSITIVE_GAS_ROW_COUNT",
    "B2_RESOURCE_BOUNDARY_COUNT",
    "B2_RUNTIME_BYTE_DELTA",
}
GAS_TOKENS = {
    f"GAS_{key}_{suffix}"
    for key, _ in GAS_ROWS
    for suffix in ("REF", "BLANC", "DELTA", "COORD")
}
EXPECTED_TOKENS = LOCK_TOKENS | SUMMARY_TOKENS | DERIVED_MANIFEST_TOKENS | GAS_TOKENS

ENDPOINT_RE = re.compile(r"^<!-- LIDO-TWG-ENDPOINT (\{.*\}) -->$")
EVENT_RE = re.compile(r"^<!-- LIDO-TWG-EVENT (\{.*\}) -->$")
CONSTRUCTOR_RE = re.compile(r"^<!-- LIDO-TWG-CONSTRUCTOR (\{.*\}) -->$")
CROSSCUT_RE = re.compile(r"^<!-- LIDO-TWG-CROSSCUT ([a-z0-9-]+) -->$")
DEVIATION_POLICY_RE = re.compile(r"^<!-- LIDO-TWG-DEVIATION-POLICY (\{.*\}) -->$")
DEVIATION_RE = re.compile(r"^<!-- LIDO-TWG-DEVIATION (\{.*\}) -->$")
IMPLEMENTATION_RE = re.compile(
    r"^<!-- LIDO-TWG-IMPLEMENTATION-DIFFERENCE (\{.*\}) -->$"
)
CODE_SIZE_RE = re.compile(r"^<!-- LIDO-TWG-CODE-SIZE (\{.*\}) -->$")
GAS_MEASUREMENT_RE = re.compile(r"^<!-- LIDO-TWG-GAS-MEASUREMENT (\{.*\}) -->$")
GAS_DEVIATION_RE = re.compile(r"^<!-- LIDO-TWG-GAS-DEVIATION (\{.*\}) -->$")
MACHINE_RE = re.compile(r"\{\{MACHINE:([A-Z0-9_]+)\}\}")
DRAFT_SENTINEL = "{{MACHINE:...}}"
SELECTOR_TABLE_RE = re.compile(
    r"^\| ([0-9]+) \| `([^`]+)` \| `(0x[0-9a-f]{8})` \|$"
)
GAS_TABLE_RE = re.compile(
    r"^\| `([^`]+)` \| .* \| `([^`]*)` \| `([^`]*)` \| `([^`]*)` \| `([^`]*)` \|$"
)


class CompatibilityError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise CompatibilityError(message)


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compact(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def strict_json(data: bytes | str, what: str) -> Any:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            expect(key not in result, f"{what}: duplicate JSON key {key!r}")
            result[key] = value
        return result

    def invalid(value: str) -> None:
        fail(f"{what}: non-finite JSON value {value}")

    try:
        return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f"{what}: invalid JSON: {exc}")


def load_json(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        fail(f"cannot read {label} at {path}: {exc}")
    value = strict_json(raw, label)
    expect(isinstance(value, dict), f"{label}: top level is not an object")
    return value, raw


def read_document(path: Path) -> tuple[str, bytes]:
    try:
        raw = path.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        fail(f"cannot read UTF-8 document {path}: {exc}")
    expect(raw.endswith(b"\n"), f"{path.name}: missing final newline")
    expect(b"\r" not in raw and b"\0" not in raw, f"{path.name}: noncanonical bytes")
    return text, raw


def parse_marker(raw: str, label: str) -> dict[str, Any]:
    value = strict_json(raw, f"{label} marker")
    expect(isinstance(value, dict), f"{label} marker is not an object")
    return value


def check_heading_inventory(text: str, expected: list[str], label: str) -> None:
    found = [line for line in text.splitlines() if line.startswith("## ")]
    expect(found == expected, f"{label} heading inventory/order differs\nexpected: {expected}\nfound: {found}")


def load_census(path: Path) -> tuple[dict[str, Any], bytes]:
    census, raw = load_json(path, "Lido TWG census")
    expect(census.get("contract") == "TriggerableWithdrawalsGateway",
           "census contract identity differs")
    expect(census.get("pinned_commit") == "17005714f151e5502c559932319a3f2f74ac2436",
           "census source commit differs")
    selectors = census.get("selectors")
    events = census.get("events")
    expect(isinstance(selectors, list) and len(selectors) == 24,
           "census must contain exactly 24 selectors")
    expect(isinstance(events, list) and len(events) == 6,
           "census must contain exactly six events")
    for index, row in enumerate(selectors):
        expect(isinstance(row, dict) and isinstance(row.get("signature"), str)
               and isinstance(row.get("selector"), str),
               f"census selector {index} is malformed")
        expect(re.fullmatch(r"0x[0-9a-f]{8}", row["selector"]) is not None,
               f"census selector {index} is not canonical")
    for index, row in enumerate(events):
        expect(isinstance(row, dict) and isinstance(row.get("signature"), str)
               and isinstance(row.get("topic0"), str)
               and isinstance(row.get("indexed"), list)
               and all(isinstance(item, str) for item in row["indexed"]),
               f"census event {index} is malformed")
        expect(re.fullmatch(r"0x[0-9a-f]{64}", row["topic0"]) is not None,
               f"census event {index} topic is not canonical")
    return census, raw


def parse_compatibility(text: str, census: dict[str, Any]) -> dict[str, Any]:
    endpoint_markers: list[dict[str, Any]] = []
    event_markers: list[dict[str, Any]] = []
    constructors: list[dict[str, Any]] = []
    crosscuts: list[str] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if match := ENDPOINT_RE.fullmatch(line):
            marker = parse_marker(match.group(1), "endpoint")
            expect(set(marker) == {"signature", "selector"}
                   and isinstance(marker["signature"], str)
                   and isinstance(marker["selector"], str),
                   f"endpoint marker line {line_number} has wrong shape")
            endpoint_markers.append(marker)
        elif match := EVENT_RE.fullmatch(line):
            marker = parse_marker(match.group(1), "event")
            expect(set(marker) == {"signature", "topic0", "indexed"}
                   and isinstance(marker["signature"], str)
                   and isinstance(marker["topic0"], str)
                   and isinstance(marker["indexed"], list)
                   and all(isinstance(item, str) for item in marker["indexed"]),
                   f"event marker line {line_number} has wrong shape")
            event_markers.append(marker)
        elif match := CONSTRUCTOR_RE.fullmatch(line):
            constructors.append(parse_marker(match.group(1), "constructor"))
        elif match := CROSSCUT_RE.fullmatch(line):
            crosscuts.append(match.group(1))
        elif line.startswith("<!-- LIDO-TWG-"):
            fail(f"compatibility document has unknown or malformed marker at line {line_number}: {line}")

    expected_endpoints = [
        {"signature": row["signature"], "selector": row["selector"]}
        for row in census["selectors"]
    ]
    expected_events = [
        {"signature": row["signature"], "topic0": row["topic0"], "indexed": row["indexed"]}
        for row in census["events"]
    ]
    expect(endpoint_markers == expected_endpoints,
           "endpoint markers differ from the exact ordered census")
    expect(event_markers == expected_events,
           "event markers differ from the exact ordered census")
    expect(constructors == [{"arguments": CONSTRUCTOR_ARGUMENTS}],
           "constructor marker must contain the exact five argument types")
    expect(crosscuts == CROSSCUTS,
           f"cross-cut marker inventory/order differs\nexpected: {CROSSCUTS}\nfound: {crosscuts}")
    visible_rows = [
        (int(match.group(1)), match.group(2), match.group(3))
        for line in text.splitlines()
        if (match := SELECTOR_TABLE_RE.fullmatch(line)) is not None
    ]
    expected_visible = [
        (index, row["signature"], row["selector"])
        for index, row in enumerate(census["selectors"], 1)
    ]
    expect(visible_rows == expected_visible,
           "visible 24-selector table differs from the exact ordered census")
    check_heading_inventory(text, COMPATIBILITY_HEADINGS, "compatibility document")
    normalized_text = " ".join(text.split())
    calldata_minimum = 1 if "{{MACHINE:B2_CALLDATA_SCOPE_SUMMARY}}" in text else 2
    expect(normalized_text.count(CALLDATA_EXCLUSION_TEXT) >= calldata_minimum,
           "compatibility document does not repeat the exact machine summary and explicit "
           "dispatch/calldata exclusion boundary")
    expect(normalized_text.count(INTERFACE_ID_EXCLUSION_TEXT) >= 2,
           "compatibility document does not repeat the exact supportsInterface coverage "
           "boundary")
    return {
        "endpoints": endpoint_markers,
        "events": event_markers,
        "constructor": constructors[0],
        "crosscuts": crosscuts,
    }


def parse_deviations(text: str) -> dict[str, Any]:
    policies: list[dict[str, Any]] = []
    deviations: list[dict[str, Any]] = []
    implementations: list[dict[str, Any]] = []
    code_sizes: list[dict[str, Any]] = []
    measurements: list[dict[str, Any]] = []
    gas_deviations: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if match := DEVIATION_POLICY_RE.fullmatch(line):
            policies.append(parse_marker(match.group(1), "deviation policy"))
        elif match := DEVIATION_RE.fullmatch(line):
            deviations.append(parse_marker(match.group(1), "deviation"))
        elif match := IMPLEMENTATION_RE.fullmatch(line):
            implementations.append(parse_marker(match.group(1), "implementation difference"))
        elif match := CODE_SIZE_RE.fullmatch(line):
            code_sizes.append(parse_marker(match.group(1), "code size"))
        elif match := GAS_MEASUREMENT_RE.fullmatch(line):
            measurements.append(parse_marker(match.group(1), "gas measurement"))
        elif match := GAS_DEVIATION_RE.fullmatch(line):
            gas_deviations.append(parse_marker(match.group(1), "gas deviation"))
        elif line.startswith("<!-- LIDO-TWG-"):
            fail(f"deviation registry has unknown or malformed marker at line {line_number}: {line}")

    policy_keys = {
        "schema", "closure", "knownBehavioralRows", "acceptedBehavioralRows",
        "repairedBehavioralRows", "pendingBehavioralRows", "positiveGasRows",
        "unknownMismatchAllowlist",
    }
    expect(len(policies) == 1 and set(policies[0]) == policy_keys,
           "deviation registry must have exactly one policy marker with the fixed fields")
    actual_rows = []
    for index, row in enumerate(deviations):
        expect(set(row) == {"id", "status", "class"}
               and row.get("status") in {"unresolved", "accepted", "repaired"},
               f"behavioral deviation marker {index} has wrong shape/status")
        actual_rows.append({"id": row.get("id"), "class": row.get("class")})
    expect(actual_rows == DEVIATION_ROWS,
           f"stable behavioral deviation inventory differs\nexpected: {DEVIATION_ROWS}\nfound: {actual_rows}")
    expect(implementations == IMPLEMENTATION_DIFFERENCES,
           "implementation-difference inventory must be exactly TWG-I01 storage-layout")
    expect(len(code_sizes) == 1 and set(code_sizes[0]) == {
        "referenceLock", "artifactProgramCommit", "proofCertificateCommit", "manifest",
    }, "code-size marker inventory/shape differs")
    template_code_size = code_sizes[0]["artifactProgramCommit"] == \
        "{{MACHINE:B2_BLANC_ARTIFACT_PROGRAM_COMMIT}}" and \
        code_sizes[0]["proofCertificateCommit"] == \
        "{{MACHINE:B2_BLANC_PROOF_CERTIFICATE_COMMIT}}"
    expect(template_code_size or
           (code_sizes[0]["artifactProgramCommit"] == BLANC_ARTIFACT_COMMIT and
            code_sizes[0]["proofCertificateCommit"] == BLANC_PROOF_COMMIT),
           "code-size marker does not bind the exact artifact-program/proof-certificate pair")
    expect(len(measurements) == 1 and set(measurements[0]) == {
        "eelsCommit", "manifest", "boundaryDefinition", "rowCount", "positiveDeltaRows",
    }, "gas-measurement marker inventory/shape differs")
    for index, row in enumerate(gas_deviations, 1):
        expect(set(row) == {"id", "gasKey", "path", "delta", "status"}
               and row.get("id") == f"TWG-G{index:02d}"
               and row.get("status") == "accepted"
               and type(row.get("delta")) is int and row["delta"] > 0,
               f"positive-gas marker {index} has wrong shape/order")
    positive_count = policies[0].get("positiveGasRows")
    expect(positive_count == "{{MACHINE:B2_POSITIVE_GAS_ROW_COUNT}}" or
           (type(positive_count) is int and positive_count == len(gas_deviations)),
           "positive-gas policy count does not match the exact marker inventory")
    check_heading_inventory(text, DEVIATION_HEADINGS, "deviation registry")
    return {
        "policy": policies[0],
        "deviations": deviations,
        "implementationDifferences": implementations,
        "codeSize": code_sizes[0],
        "gasMeasurement": measurements[0],
        "gasDeviations": gas_deviations,
    }


def machine_tokens(*texts: str) -> list[str]:
    result: list[str] = []
    for text in texts:
        sentinel_count = text.count(DRAFT_SENTINEL)
        masked = text.replace(DRAFT_SENTINEL, "")
        found = MACHINE_RE.findall(masked)
        expect(masked.count("{{MACHINE:") == len(found),
               "malformed machine placeholder syntax is present")
        result.extend(["..."] * sentinel_count)
        result.extend(found)
    return result


def completion_blockers(tokens: list[str], parsed: dict[str, Any]) -> list[str]:
    blockers: list[str] = []
    if tokens:
        blockers.append(
            f"{len(tokens)} machine placeholder occurrences remain "
            f"({len(set(tokens))} unique): {', '.join(sorted(set(tokens)))}"
        )
    unresolved = [row["id"] for row in parsed["deviations"] if row["status"] == "unresolved"]
    if unresolved:
        blockers.append("unresolved deviation markers remain: " + ", ".join(unresolved))
    if parsed["policy"].get("closure") != "complete":
        blockers.append("deviation policy closure is not 'complete'")
    return blockers


def canonical_sha(value: Any, label: str) -> str:
    expect(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
           f"{label} is not a lowercase SHA-256")
    return value


def byte_artifact(value: Any, label: str) -> dict[str, Any]:
    expect(isinstance(value, dict) and set(value) == {"byteLength", "sha256"},
           f"{label} must contain exactly byteLength/sha256")
    expect(type(value["byteLength"]) is int and value["byteLength"] > 0,
           f"{label}.byteLength must be a positive integer")
    canonical_sha(value["sha256"], f"{label}.sha256")
    return value


def locked_artifact(value: Any, label: str) -> dict[str, Any]:
    expect(isinstance(value, dict), f"{label} is not an object")
    expect(type(value.get("byteLength")) is int and value["byteLength"] > 0,
           f"{label}.byteLength must be positive")
    canonical_sha(value.get("sha256"), f"{label}.sha256")
    return value


def validate_lock(lock: dict[str, Any], raw: bytes, census: dict[str, Any],
                  reference_world: str) -> tuple[dict[str, Any], dict[str, Any]]:
    expect(lock.get("schema") == 1, "B1 reference lock schema must be 1")
    target = lock.get("target")
    expect(isinstance(target, dict)
           and target.get("contract") == "TriggerableWithdrawalsGateway"
           and target.get("releaseCommit") == census["pinned_commit"],
           "B1 reference lock target/source identity differs from census")
    abi = lock.get("abi")
    expect(isinstance(abi, dict), "B1 reference lock has no ABI inventory")
    functions = abi.get("functions")
    events = abi.get("events")
    constructor = abi.get("constructor")
    expect(isinstance(functions, list) and isinstance(events, list)
           and isinstance(constructor, dict), "B1 reference lock ABI shape differs")
    function_map = {
        row.get("signature"): row.get("selector")
        for row in functions if isinstance(row, dict)
    }
    expect(len(function_map) == len(functions) == 24,
           "B1 reference lock must have 24 unique ABI functions")
    expect([
        {"signature": row["signature"], "selector": function_map.get(row["signature"])}
        for row in census["selectors"]
    ] == [
        {"signature": row["signature"], "selector": row["selector"]}
        for row in census["selectors"]
    ], "B1 reference lock selectors differ from census")
    event_map = {}
    for row in events:
        if not isinstance(row, dict) or not isinstance(row.get("entry"), dict) \
                or not isinstance(row["entry"].get("inputs"), list):
            fail("B1 reference lock has a malformed ABI event row")
        indexed_names = [
            item.get("name")
            for item in row["entry"]["inputs"]
            if isinstance(item, dict) and item.get("indexed") is True
        ]
        event_map[row.get("signature")] = {
            "signature": row.get("signature"),
            "topic0": row.get("topic0"),
            "indexed": indexed_names,
        }
    expect(len(event_map) == len(events) == 6
           and [event_map.get(row["signature"]) for row in census["events"]] == [
               {"signature": row["signature"], "topic0": row["topic0"],
                "indexed": row["indexed"]}
               for row in census["events"]
           ], "B1 reference lock events differ from census")
    inputs = constructor.get("inputs")
    expect(isinstance(inputs, list)
           and [row.get("type") for row in inputs if isinstance(row, dict)] == CONSTRUCTOR_ARGUMENTS,
           "B1 reference lock constructor types differ")
    worlds = lock.get("artifacts", {}).get("worlds")
    expect(isinstance(worlds, list), "B1 reference lock has no artifact worlds")
    matches = [row for row in worlds if isinstance(row, dict) and row.get("name") == reference_world]
    expect(len(matches) == 1, f"B1 reference lock has no unique world {reference_world!r}")
    world = matches[0]
    full = locked_artifact(world.get("fullCreateInput"), "B1 reference full CREATE input")
    runtime = locked_artifact(world.get("returnedRuntime"), "B1 reference runtime")
    compiler = lock.get("compiler")
    snapshot = lock.get("snapshot")
    sections = lock.get("sectionDigests")
    expect(isinstance(compiler, dict) and isinstance(compiler.get("version"), str)
           and isinstance(compiler.get("binary"), dict), "B1 compiler identity differs")
    compiler_sha = canonical_sha(compiler["binary"].get("sha256"), "B1 compiler SHA-256")
    expect(isinstance(snapshot, dict) and isinstance(snapshot.get("block"), dict)
           and isinstance(snapshot.get("account"), dict), "B1 snapshot shape differs")
    block_hex = snapshot["block"].get("number")
    code_hash = snapshot["account"].get("codeHash")
    expect(isinstance(block_hex, str) and re.fullmatch(r"0x[0-9a-f]+", block_hex),
           "B1 snapshot block number is not canonical hex")
    expect(isinstance(code_hash, str) and re.fullmatch(r"0x[0-9a-f]{64}", code_hash),
           "B1 snapshot code hash is not canonical")
    expect(isinstance(sections, dict), "B1 section digest inventory is missing")
    snapshot_sha = canonical_sha(sections.get("snapshot"), "B1 snapshot section digest")
    values: dict[str, Any] = {
        "B1_REFERENCE_LOCK_SCHEMA": lock["schema"],
        "B1_REFERENCE_LOCK_SHA256": sha256(raw),
        "B1_SOLC_VERSION": compiler["version"],
        "B1_SOLC_ARTIFACT_SHA256": compiler_sha,
        "B1_REFERENCE_FULL_CREATE_BYTES": full["byteLength"],
        "B1_REFERENCE_FULL_CREATE_SHA256": full["sha256"],
        "B1_REFERENCE_RUNTIME_BYTES": runtime["byteLength"],
        "B1_REFERENCE_RUNTIME_SHA256": runtime["sha256"],
        "B1_MAINNET_BLOCK": int(block_hex, 16),
        "B1_MAINNET_CODE_HASH": code_hash,
        "B1_MAINNET_ROLE_PAUSE_SNAPSHOT_SHA256": snapshot_sha,
    }
    return values, {"fullCreateInput": full, "runtime": runtime}


def safe_text(value: Any, label: str, multiline: bool = False) -> str:
    expect(type(value) in {str, int}, f"{label} must be a string or integer")
    rendered = str(value)
    expect(rendered != "" and "\0" not in rendered and "{{MACHINE:" not in rendered,
           f"{label} is empty or contains forbidden placeholder data")
    expect("<!--" not in rendered and "-->" not in rendered,
           f"{label} may not inject an HTML marker")
    expect("`" not in rendered and "|" not in rendered,
           f"{label} may not break a machine-owned Markdown cell")
    if not multiline:
        expect("\n" not in rendered and "\r" not in rendered,
               f"{label} must be a single line")
    return rendered


def positive_gas_table(rows: list[dict[str, Any]], positives: list[dict[str, Any]]) -> str:
    vector_sha = sha256(compact(rows))
    if not positives:
        return f"None — zero measured positive public-path deltas; ordered gas vector SHA-256 `{vector_sha}`."
    by_key = {row["gasKey"]: row for row in rows}
    marker_lines = []
    table_lines = [
        "| Stable ID | Path | Delta | Defense | Evidence |",
        "|---|---|---:|---|---|",
    ]
    for item in positives:
        row = by_key[item["gasKey"]]
        marker = {
            "id": item["id"], "gasKey": item["gasKey"], "path": row["path"],
            "delta": row["delta"], "status": "accepted",
        }
        marker_lines.append(
            "<!-- LIDO-TWG-GAS-DEVIATION "
            + json.dumps(marker, separators=(",", ":")) + " -->"
        )
        table_lines.append(
            f"| `{item['id']}` | `{row['path']}` | `{row['delta']}` | "
            f"{item['defense']} | {item['evidence']} |"
        )
    return "\n".join(marker_lines + [""] + table_lines)


def validate_manifest_contract(
    manifest: dict[str, Any], raw: bytes, lock_sha: str, census_sha: str,
    compatibility_raw: bytes, deviations_raw: bytes, reference: dict[str, Any],
    verify_templates: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    fill = manifest.get("documentFill")
    if not isinstance(fill, dict):
        fail("B2 manifest is missing the required documentFill schema-1 contract; "
             "run `python3 scripts/lido-twg-compatibility.py schema` for the exact shape")
    expect(set(fill) == {
        "schema", "referenceLockSha256", "referenceWorld", "censusSha256",
        "eelsCommit", "jauneCommit", "templates", "evidence",
    } and fill.get("schema") == 1,
        "B2 documentFill top-level schema/field inventory differs")
    expect(fill["referenceWorld"] == "differential-corpus",
           "B2 documentFill referenceWorld must be 'differential-corpus'")
    expect(fill["referenceLockSha256"] == lock_sha,
           "B2 documentFill does not bind the exact B1 lock")
    expect(fill["censusSha256"] == census_sha,
           "B2 documentFill does not bind the exact census")
    expect(fill["eelsCommit"] == "4198b9c5996713b268aed602739d5aa40e277694",
           "B2 documentFill EELS commit differs")
    expect(fill["jauneCommit"] == "949cf97ee1956828a3ac0eb12a62c438656ba76e",
           "B2 documentFill Jaune commit differs")
    templates = fill["templates"]
    expect(isinstance(templates, dict) and set(templates) == {"compatibility", "deviations"},
           "B2 documentFill template inventory differs")
    for key in templates:
        canonical_sha(templates[key], f"B2 documentFill templates.{key}")
    if verify_templates:
        expect(templates == {
            "compatibility": sha256(compatibility_raw),
            "deviations": sha256(deviations_raw),
        }, "B2 documentFill template digests differ from the current placeholder documents")
    evidence = fill["evidence"]
    expect(isinstance(evidence, dict) and set(evidence) == {
        "artifactProgramCommit", "proofCertificateCommit", "artifacts", "counts",
        "summaries", "gas",
    }, "B2 documentFill evidence field inventory differs")
    artifact_commit = evidence["artifactProgramCommit"]
    proof_commit = evidence["proofCertificateCommit"]
    expect(isinstance(artifact_commit, str) and re.fullmatch(r"[0-9a-f]{40}", artifact_commit),
           "B2 Blanc artifact-program commit is not a full lowercase Git commit")
    expect(isinstance(proof_commit, str) and re.fullmatch(r"[0-9a-f]{40}", proof_commit),
           "B2 Blanc proof-certificate commit is not a full lowercase Git commit")
    expect(artifact_commit == BLANC_ARTIFACT_COMMIT,
           "B2 Blanc artifact-program commit differs from the frozen identity")
    expect(proof_commit == BLANC_PROOF_COMMIT,
           "B2 Blanc proof-certificate commit differs from the frozen identity")
    artifacts = evidence["artifacts"]
    expect(isinstance(artifacts, dict) and set(artifacts) == {
        "creationTemplate", "fullCreateInput", "runtime",
    }, "B2 documentFill artifact inventory differs")
    creation = byte_artifact(artifacts["creationTemplate"], "B2 creation template")
    full = byte_artifact(artifacts["fullCreateInput"], "B2 full CREATE input")
    runtime = byte_artifact(artifacts["runtime"], "B2 runtime")
    counts = evidence["counts"]
    expect(isinstance(counts, dict) and set(counts) == {"cases", "resourceBoundaries"}
           and type(counts["cases"]) is int and counts["cases"] > 0
           and type(counts["resourceBoundaries"]) is int and counts["resourceBoundaries"] > 0,
           "B2 documentFill counts must be positive cases/resourceBoundaries")
    summaries = evidence["summaries"]
    expect(isinstance(summaries, dict) and set(summaries) == SUMMARY_TOKENS,
           f"B2 documentFill summary inventory differs; required: {sorted(SUMMARY_TOKENS)}")
    for key, value in summaries.items():
        safe_text(value, f"B2 summaries.{key}")
    expect(str(summaries["B2_DIFFERENTIAL_VERDICT"]).upper() == "PASS",
           "B2 differential verdict must be PASS before claim-document fill")
    canonical_sha(str(summaries["B2_D05_PROJECTION_SHA256"]), "B2 D05 projection digest")
    canonical_sha(str(summaries["B2_PROJECTION_SCHEMA_SHA256"]), "B2 projection schema digest")

    gas = evidence["gas"]
    expect(isinstance(gas, dict) and set(gas) == {
        "boundaryDefinition", "rows", "positiveDeviations",
    }, "B2 documentFill gas field inventory differs")
    boundary = safe_text(gas["boundaryDefinition"], "B2 gas boundary definition")
    rows = gas["rows"]
    expect(isinstance(rows, list) and len(rows) == len(GAS_ROWS),
           f"B2 documentFill gas rows must contain exactly {len(GAS_ROWS)} entries")
    for index, (row, (key, path)) in enumerate(zip(rows, GAS_ROWS)):
        expect(isinstance(row, dict) and set(row) == {
            "gasKey", "path", "reference", "blanc", "delta", "coordinate",
        }, f"B2 gas row {index} has wrong fields")
        expect(row["gasKey"] == key and row["path"] == path,
               f"B2 gas row {index} key/path differs; expected {key}/{path}")
        expect(type(row["reference"]) is int and row["reference"] >= 0
               and type(row["blanc"]) is int and row["blanc"] >= 0
               and type(row["delta"]) is int
               and row["delta"] == row["blanc"] - row["reference"],
               f"B2 gas row {key} values/delta are not nonnegative/derived")
        safe_text(row["coordinate"], f"B2 gas row {key} coordinate")
    positives = gas["positiveDeviations"]
    expect(isinstance(positives, list), "B2 positiveDeviations is not a list")
    expect(all(row["delta"] < 0 for row in rows),
           "B2 exact 51-cell named gas ledger is not strictly dominant")
    expected_positive_keys = [row["gasKey"] for row in rows if row["delta"] > 0]
    actual_positive_keys = []
    for index, item in enumerate(positives, 1):
        expect(isinstance(item, dict) and set(item) == {"id", "gasKey", "defense", "evidence"}
               and item.get("id") == f"TWG-G{index:02d}",
               f"B2 positive gas deviation {index} has wrong fields/stable ID")
        actual_positive_keys.append(item["gasKey"])
        safe_text(item["defense"], f"positive gas deviation {index} defense")
        safe_text(item["evidence"], f"positive gas deviation {index} evidence")
    expect(actual_positive_keys == expected_positive_keys,
           "B2 positiveDeviations must cover every positive gas row exactly in gas-row order")

    values: dict[str, Any] = {
        "B2_MANIFEST_SCHEMA": manifest.get("schema"),
        "B2_MANIFEST_SHA256": sha256(raw),
        "B2_BLANC_ARTIFACT_PROGRAM_COMMIT": artifact_commit,
        "B2_BLANC_PROOF_CERTIFICATE_COMMIT": proof_commit,
        "B2_BLANC_CREATION_TEMPLATE_BYTES": creation["byteLength"],
        "B2_BLANC_CREATION_TEMPLATE_SHA256": creation["sha256"],
        "B2_BLANC_FULL_CREATE_BYTES": full["byteLength"],
        "B2_BLANC_FULL_CREATE_SHA256": full["sha256"],
        "B2_BLANC_RUNTIME_BYTES": runtime["byteLength"],
        "B2_BLANC_RUNTIME_SHA256": runtime["sha256"],
        "B2_CASE_COUNT": counts["cases"],
        "B2_RESOURCE_BOUNDARY_COUNT": counts["resourceBoundaries"],
        "B2_RUNTIME_BYTE_DELTA": runtime["byteLength"] - reference["runtime"]["byteLength"],
        "B2_FULL_CREATE_BYTE_DELTA": full["byteLength"] - reference["fullCreateInput"]["byteLength"],
        "B2_GAS_BOUNDARY_DEFINITION": boundary,
        "B2_NAMED_GAS_ROW_COUNT": len(rows),
        "B2_POSITIVE_GAS_ROW_COUNT": len(positives),
        "B2_POSITIVE_GAS_ROWS_TABLE": positive_gas_table(rows, positives),
        **summaries,
    }
    expect(type(values["B2_MANIFEST_SCHEMA"]) is int and values["B2_MANIFEST_SCHEMA"] > 0,
           "B2 manifest root schema must be a positive integer")
    for row in rows:
        prefix = f"GAS_{row['gasKey']}"
        values[f"{prefix}_REF"] = row["reference"]
        values[f"{prefix}_BLANC"] = row["blanc"]
        values[f"{prefix}_DELTA"] = row["delta"]
        values[f"{prefix}_COORD"] = row["coordinate"]
    expect(set(values) == SUMMARY_TOKENS | DERIVED_MANIFEST_TOKENS | GAS_TOKENS,
           "internal B2 fill-value inventory differs")
    return values, {"fill": fill, "gasRows": rows, "positiveDeviations": positives}


def contract_message() -> str:
    gas = ", ".join(f"{key}/{path}" for key, path in GAS_ROWS)
    return (
        "required B2 manifest contract: documentFill schema 1 with exact fields "
        "referenceLockSha256, referenceWorld='differential-corpus', censusSha256, "
        "eelsCommit, jauneCommit, templates"
        "{compatibility,deviations}, and evidence{artifactProgramCommit,proofCertificateCommit, artifacts"
        "{creationTemplate,fullCreateInput,runtime}, counts{cases,resourceBoundaries}, "
        f"summaries{{{','.join(sorted(SUMMARY_TOKENS))}}}, gas"
        "{boundaryDefinition,rows,positiveDeviations}}; ordered gas rows: " + gas
    )


def source_values(
    args: argparse.Namespace, census: dict[str, Any], census_raw: bytes,
    compatibility_raw: bytes, deviations_raw: bytes, verify_templates: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    if not args.lock.is_file():
        fail(f"B1 reference lock is missing at {args.lock}; {contract_message()}")
    if not args.manifest.is_file():
        fail(f"B2 manifest is missing at {args.manifest}; {contract_message()}")
    lock, lock_raw = load_json(args.lock, "B1 reference lock")
    manifest, manifest_raw = load_json(args.manifest, "B2 differential manifest")
    fill = manifest.get("documentFill")
    if not isinstance(fill, dict) or not isinstance(fill.get("referenceWorld"), str):
        fail("B2 manifest lacks documentFill.referenceWorld; " + contract_message())
    lock_values, reference = validate_lock(
        lock, lock_raw, census, fill["referenceWorld"],
    )
    manifest_values, evidence = validate_manifest_contract(
        manifest, manifest_raw, sha256(lock_raw), sha256(census_raw),
        compatibility_raw, deviations_raw, reference, verify_templates,
    )
    values = {**lock_values, **manifest_values}
    expect(set(values) == EXPECTED_TOKENS, "complete machine fill-value inventory differs")
    return values, evidence


def render_template(text: str, values: dict[str, Any], label: str) -> str:
    # JSON-bearing markers quote the template token so that the draft itself is
    # valid JSON.  Replace that entire JSON string first; integers then become
    # JSON numbers and strings remain correctly escaped JSON strings.
    rendered = text.replace(DRAFT_SENTINEL, "machine-owned")
    rendered = rendered.replace(
        "`{{MACHINE:B2_POSITIVE_GAS_ROWS_TABLE}}`",
        str(values["B2_POSITIVE_GAS_ROWS_TABLE"]),
    )
    for key in sorted(values):
        quoted = json.dumps("{{MACHINE:" + key + "}}")
        rendered = rendered.replace(quoted, json.dumps(values[key], separators=(",", ":")))
    for key in sorted(values):
        token = "{{MACHINE:" + key + "}}"
        value = (str(values[key]) if key == "B2_POSITIVE_GAS_ROWS_TABLE"
                 else safe_text(values[key], key))
        rendered = rendered.replace(token, value)
    expect("{{MACHINE:" not in rendered, f"{label}: machine token survived rendering")
    return rendered


def render_documents(
    compatibility: str, deviations: str, values: dict[str, Any],
    census: dict[str, Any],
) -> tuple[str, str]:
    rendered_compatibility = render_template(compatibility, values, "compatibility")
    rendered_deviations = render_template(deviations, values, "deviations")
    parse_compatibility(rendered_compatibility, census)
    parse_deviations(rendered_deviations)
    expect(not machine_tokens(rendered_compatibility, rendered_deviations),
           "rendered documents retain a machine placeholder")
    return rendered_compatibility, rendered_deviations


def require_template_tokens(compatibility: str, deviations: str) -> None:
    found = machine_tokens(compatibility, deviations)
    expect(found.count("...") == 2,
           "placeholder templates must contain the two explanatory draft sentinels")
    actual = set(found) - {"..."}
    expect(actual == EXPECTED_TOKENS,
           "placeholder template inventory differs\n"
           f"missing: {sorted(EXPECTED_TOKENS - actual)}\n"
           f"unexpected: {sorted(actual - EXPECTED_TOKENS)}")


def int_field(value: Any, label: str) -> int:
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r"-?[0-9]+", value):
        return int(value)
    fail(f"{label} must be an integer")


def check_rendered_values(
    compatibility: str, deviations: str, parsed: dict[str, Any],
    values: dict[str, Any], evidence: dict[str, Any],
) -> None:
    statuses = Counter(row["status"] for row in parsed["deviations"])
    policy = parsed["policy"]
    expect(policy.get("schema") == 1 and policy.get("closure") == "complete"
           and policy.get("knownBehavioralRows") == len(DEVIATION_ROWS)
           and policy.get("unknownMismatchAllowlist") is False,
           "completed deviation policy marker is not fail-closed")
    expect(int_field(policy.get("acceptedBehavioralRows"), "acceptedBehavioralRows")
           == statuses["accepted"]
           and int_field(policy.get("repairedBehavioralRows"), "repairedBehavioralRows")
           == statuses["repaired"]
           and int_field(policy.get("pendingBehavioralRows"), "pendingBehavioralRows") == 0,
           "deviation policy counts do not match stable row statuses")
    expect(int_field(policy.get("positiveGasRows"), "positiveGasRows")
           == len(evidence["positiveDeviations"])
           == len(parsed["gasDeviations"]),
           "positive-gas policy/manifest/marker counts differ")
    expected_gas_markers = []
    by_key = {row["gasKey"]: row for row in evidence["gasRows"]}
    for item in evidence["positiveDeviations"]:
        row = by_key[item["gasKey"]]
        expected_gas_markers.append({
            "id": item["id"], "gasKey": item["gasKey"], "path": row["path"],
            "delta": row["delta"], "status": "accepted",
        })
    expect(parsed["gasDeviations"] == expected_gas_markers,
           "positive-gas markers differ from the B2 ordered vector")
    expect(parsed["codeSize"] == {
        "referenceLock": values["B1_REFERENCE_LOCK_SHA256"],
        "artifactProgramCommit": values["B2_BLANC_ARTIFACT_PROGRAM_COMMIT"],
        "proofCertificateCommit": values["B2_BLANC_PROOF_CERTIFICATE_COMMIT"],
        "manifest": values["B2_MANIFEST_SHA256"],
    }, "code-size marker differs from B1/B2 identities")
    expect(parsed["gasMeasurement"] == {
        "eelsCommit": "4198b9c5996713b268aed602739d5aa40e277694",
        "manifest": values["B2_MANIFEST_SHA256"],
        "boundaryDefinition": values["B2_GAS_BOUNDARY_DEFINITION"],
        "rowCount": values["B2_NAMED_GAS_ROW_COUNT"],
        "positiveDeltaRows": values["B2_POSITIVE_GAS_ROW_COUNT"],
    }, "gas-measurement marker differs from the B2 vector")

    required_lines = [
        f"| Reference-lock schema | `{values['B1_REFERENCE_LOCK_SCHEMA']}` |",
        f"| Reference-lock SHA-256 | `{values['B1_REFERENCE_LOCK_SHA256']}` |",
        f"| Solidity compiler | `{values['B1_SOLC_VERSION']}`; artifact SHA-256 `{values['B1_SOLC_ARTIFACT_SHA256']}` |",
        f"| Reference creation bytes | `{values['B1_REFERENCE_FULL_CREATE_BYTES']}` bytes; SHA-256 `{values['B1_REFERENCE_FULL_CREATE_SHA256']}` |",
        f"| Reference runtime | `{values['B1_REFERENCE_RUNTIME_BYTES']}` bytes; SHA-256 `{values['B1_REFERENCE_RUNTIME_SHA256']}` |",
        f"| Blanc artifact/runtime program commit | `{values['B2_BLANC_ARTIFACT_PROGRAM_COMMIT']}` |",
        f"| Optimized-runtime theorem ladder and pinned-target certificate | `{values['B2_BLANC_PROOF_CERTIFICATE_COMMIT']}` |",
        f"| Blanc creation template | `{values['B2_BLANC_CREATION_TEMPLATE_BYTES']}` bytes; SHA-256 `{values['B2_BLANC_CREATION_TEMPLATE_SHA256']}` |",
        f"| Blanc complete CREATE input | `{values['B2_BLANC_FULL_CREATE_BYTES']}` bytes; SHA-256 `{values['B2_BLANC_FULL_CREATE_SHA256']}` |",
        f"| Blanc runtime | `{values['B2_BLANC_RUNTIME_BYTES']}` bytes; SHA-256 `{values['B2_BLANC_RUNTIME_SHA256']}` |",
        f"| Differential manifest | schema `{values['B2_MANIFEST_SCHEMA']}`; SHA-256 `{values['B2_MANIFEST_SHA256']}` |",
        f"| Differential result | `{values['B2_DIFFERENTIAL_VERDICT']}`; `{values['B2_CASE_COUNT']}` cases, `{values['B2_RESOURCE_BOUNDARY_COUNT']}` measured resource boundaries |",
        f"| Runtime | `{values['B1_REFERENCE_RUNTIME_BYTES']}` | `{values['B2_BLANC_RUNTIME_BYTES']}` | `{values['B2_RUNTIME_BYTE_DELTA']}` | reference `{values['B1_REFERENCE_RUNTIME_SHA256']}`; Blanc `{values['B2_BLANC_RUNTIME_SHA256']}` |",
        f"| Complete CREATE input for the compared parameter world | `{values['B1_REFERENCE_FULL_CREATE_BYTES']}` | `{values['B2_BLANC_FULL_CREATE_BYTES']}` | `{values['B2_FULL_CREATE_BYTE_DELTA']}` | reference `{values['B1_REFERENCE_FULL_CREATE_SHA256']}`; Blanc `{values['B2_BLANC_FULL_CREATE_SHA256']}` |",
        f"| Blanc parameterized creation template | not comparable | `{values['B2_BLANC_CREATION_TEMPLATE_BYTES']}` | not applicable | `{values['B2_BLANC_CREATION_TEMPLATE_SHA256']}` |",
    ]
    for line in required_lines:
        expect((compatibility + "\n" + deviations).count(line) == 1,
               f"machine-owned rendered row is missing or duplicated: {line}")
    found_gas = [
        (match.group(1), match.group(2), match.group(3), match.group(4), match.group(5))
        for line in deviations.splitlines()
        if (match := GAS_TABLE_RE.fullmatch(line)) is not None
    ]
    expected_gas = [
        (row["path"], str(row["reference"]), str(row["blanc"]),
         str(row["delta"]), str(row["coordinate"]))
        for row in evidence["gasRows"]
    ]
    expect(found_gas == expected_gas,
           "named-path gas table differs from the exact B2 ordered vector")
    expected_positive_table = positive_gas_table(
        evidence["gasRows"], evidence["positiveDeviations"],
    )
    expect(deviations.count(expected_positive_table) == 1,
           "positive-gas registry text differs from the exact B2 vector/dispositions")
    # Narrative summaries are deliberately free text, but each exact
    # machine-produced value must survive in one of the two documents.
    joined = compatibility + "\n" + deviations
    for key in SUMMARY_TOKENS:
        expect(safe_text(values[key], key) in joined,
               f"machine-owned narrative value {key} is absent from the documents")


def write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    mode = path.stat().st_mode & 0o777 if path.exists() else 0o644
    handle = tempfile.NamedTemporaryFile(prefix=path.name + ".", dir=path.parent, delete=False)
    temporary = Path(handle.name)
    try:
        with handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary, mode)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def fill_in_place(paths: list[tuple[Path, bytes]]) -> None:
    originals = {path: path.read_bytes() for path, _ in paths}
    written: list[Path] = []
    try:
        for path, data in paths:
            write_atomic(path, data)
            written.append(path)
    except Exception:
        for path in written:
            write_atomic(path, originals[path])
        raise


def schema_contract(args: argparse.Namespace, compatibility_raw: bytes,
                    deviations_raw: bytes, census_raw: bytes) -> dict[str, Any]:
    lock_sha = sha256(args.lock.read_bytes()) if args.lock.is_file() else "<B1 lock SHA-256>"
    artifact = {"byteLength": "<positive integer>", "sha256": "<lowercase SHA-256>"}
    return {
        "documentFill": {
            "schema": 1,
            "referenceLockSha256": lock_sha,
            "referenceWorld": "differential-corpus",
            "censusSha256": sha256(census_raw),
            "eelsCommit": "4198b9c5996713b268aed602739d5aa40e277694",
            "jauneCommit": "949cf97ee1956828a3ac0eb12a62c438656ba76e",
            "templates": {
                "compatibility": sha256(compatibility_raw),
                "deviations": sha256(deviations_raw),
            },
            "evidence": {
                "artifactProgramCommit": "<40 lowercase hex Git commit>",
                "proofCertificateCommit": "<40 lowercase hex Git commit>",
                "artifacts": {
                    "creationTemplate": artifact,
                    "fullCreateInput": artifact,
                    "runtime": artifact,
                },
                "counts": {"cases": "<positive integer>",
                           "resourceBoundaries": "<positive integer>"},
                "summaries": {key: "<nonempty single-line machine value>"
                              for key in sorted(SUMMARY_TOKENS)},
                "gas": {
                    "boundaryDefinition": "<nonempty single-line definition>",
                    "rows": [{
                        "gasKey": key,
                        "path": path,
                        "reference": "<nonnegative integer>",
                        "blanc": "<nonnegative integer>",
                        "delta": "<blanc minus reference integer>",
                        "coordinate": "<nonempty single-line manifest coordinate>",
                    } for key, path in GAS_ROWS],
                    "positiveDeviations": [{
                        "id": "TWG-G01, TWG-G02, ... in gas-row order",
                        "gasKey": "<each and only key whose delta is positive>",
                        "defense": "<nonempty single-line reviewed defense>",
                        "evidence": "<nonempty single-line evidence pointer>",
                    }],
                },
            },
        },
    }


def self_test(compatibility: str, deviations: str, census: dict[str, Any]) -> None:
    parse_compatibility(compatibility, census)
    parsed = parse_deviations(deviations)
    accepted_d01 = \
        '<!-- LIDO-TWG-DEVIATION {"id":"TWG-D01","status":"accepted","class":"returndata"} -->'
    unresolved_d01 = accepted_d01.replace('"accepted"', '"unresolved"')
    expect(accepted_d01 in deviations,
           "completed TWG-D01 marker is absent from self-test input")
    draft = deviations.replace(accepted_d01, unresolved_d01, 1)
    draft_parsed = parse_deviations(draft)
    blockers = completion_blockers(machine_tokens(compatibility, draft), draft_parsed)
    expect(blockers == ["unresolved deviation markers remain: TWG-D01"],
           f"synthetic unresolved draft did not hit the exact completion blocker: {blockers}")

    first = census["selectors"][0]["selector"]
    mutated = compatibility.replace(first, "0x00000000", 1)
    try:
        parse_compatibility(mutated, census)
    except CompatibilityError:
        pass
    else:
        fail("endpoint-marker selector falsifier did not bite")

    mutated = compatibility.replace(
        "<!-- LIDO-TWG-CROSSCUT scope-oracles -->",
        "<!-- LIDO-TWG-CROSSCUT scope-oracles -->\n<!-- LIDO-TWG-CROSSCUT scope-oracles -->",
        1,
    )
    try:
        parse_compatibility(mutated, census)
    except CompatibilityError:
        pass
    else:
        fail("cross-cut duplication falsifier did not bite")

    mutated = deviations.replace('"status":"accepted"', '"status":"unknown"', 1)
    try:
        parse_deviations(mutated)
    except CompatibilityError:
        pass
    else:
        fail("deviation-status falsifier did not bite")

    mutated = deviations.replace("<!-- LIDO-TWG-CODE-SIZE ", "<!-- LIDO-TWG-CODE_SIZE ", 1)
    try:
        parse_deviations(mutated)
    except CompatibilityError:
        pass
    else:
        fail("malformed-marker falsifier did not bite")

    mutated = deviations.replace(BLANC_ARTIFACT_COMMIT, "0" * 40, 1)
    try:
        parse_deviations(mutated)
    except CompatibilityError:
        pass
    else:
        fail("artifact-program identity falsifier did not bite")

    mutated = deviations.replace(BLANC_PROOF_COMMIT, "0" * 40, 1)
    try:
        parse_deviations(mutated)
    except CompatibilityError:
        pass
    else:
        fail("proof-certificate identity falsifier did not bite")

    mutated = deviations.replace('"positiveGasRows":0', '"positiveGasRows":1', 1)
    expect(mutated != deviations,
           "zero-positive-gas policy falsifier could not locate the completed policy")
    try:
        parse_deviations(mutated)
    except CompatibilityError:
        pass
    else:
        fail("positive-gas completeness falsifier did not bite")

    mutated = compatibility.replace(
        "empty/unknown/short dispatch", "empty/unknown dispatch", 1)
    try:
        parse_compatibility(mutated, census)
    except CompatibilityError:
        pass
    else:
        fail("dispatch/calldata exclusion falsifier did not bite")

    mutated = compatibility.replace(
        "supportsInterface IDs other than 0x5a05180f", "other supportsInterface IDs", 1)
    try:
        parse_compatibility(mutated, census)
    except CompatibilityError:
        pass
    else:
        fail("supportsInterface identifier exclusion falsifier did not bite")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("command", choices=("check", "generate", "fill", "schema", "self-test"))
    result.add_argument("--census", type=Path, default=DEFAULT_CENSUS)
    result.add_argument("--lock", type=Path, default=DEFAULT_LOCK)
    result.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    result.add_argument("--compatibility", type=Path, default=DEFAULT_COMPATIBILITY)
    result.add_argument("--deviations", type=Path, default=DEFAULT_DEVIATIONS)
    result.add_argument("--output-dir", type=Path)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        census, census_raw = load_census(args.census)
        compatibility, compatibility_raw = read_document(args.compatibility)
        deviations, deviations_raw = read_document(args.deviations)
        parse_compatibility(compatibility, census)
        parsed_deviations = parse_deviations(deviations)

        if args.command == "schema":
            print(json.dumps(
                schema_contract(args, compatibility_raw, deviations_raw, census_raw),
                indent=2, sort_keys=True,
            ))
            return 0
        if args.command == "self-test":
            self_test(compatibility, deviations, census)
            print("OK — Lido TWG compatibility parser: endpoint, cross-cut, deviation-status, identity-pair, gas-completeness, exclusion-boundary, and malformed-marker falsifiers bite")
            return 0
        if args.command == "check":
            blockers = completion_blockers(
                machine_tokens(compatibility, deviations), parsed_deviations,
            )
            if blockers:
                fail("completion blockers:\n- " + "\n- ".join(blockers))
            values, evidence = source_values(
                args, census, census_raw, compatibility_raw, deviations_raw,
                verify_templates=False,
            )
            check_rendered_values(
                compatibility, deviations, parsed_deviations, values, evidence,
            )
            print(
                "OK — Lido TWG compatibility: 24 endpoints, 6 events, constructor, "
                "13 cross-cuts, 3 accepted + 2 repaired stable deviations, exact B1/B2 identities, "
                f"{len(GAS_ROWS)} named gas rows"
            )
            return 0

        require_template_tokens(compatibility, deviations)
        values, _ = source_values(
            args, census, census_raw, compatibility_raw, deviations_raw,
            verify_templates=True,
        )
        rendered = render_documents(compatibility, deviations, values, census)
        outputs = [
            (args.compatibility, rendered[0].encode()),
            (args.deviations, rendered[1].encode()),
        ]
        if args.command == "fill":
            expect(args.output_dir is None, "fill does not accept --output-dir")
            fill_in_place(outputs)
            print("FILLED — Lido TWG compatibility documents from exact B1/B2 evidence")
        elif args.output_dir is not None:
            destinations = [(args.output_dir / path.name, data) for path, data in outputs]
            for path, data in destinations:
                write_atomic(path, data)
            print("GENERATED — Lido TWG compatibility documents at " + str(args.output_dir))
        else:
            preview = {path.name: data.decode() for path, data in outputs}
            print(json.dumps(preview, sort_keys=True, separators=(",", ":")))
        return 0
    except (CompatibilityError, OSError, ValueError, KeyError) as exc:
        print("REGRESSION — Lido TWG compatibility: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
