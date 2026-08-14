#!/usr/bin/env python3
"""Fail-closed marker synchronization for Lido CircuitBreaker AC3 documents.

The reference lock is intentionally not created by this script.  Once AC2
lands, pass ``--lock`` (default: scripts/lido-circuit-breaker-reference.json)
and this checker requires the lock's complete ABI surface.  Until then,
``--allow-missing-lock`` performs only the self-contained document/key check.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DOCUMENT = ROOT / "LIDO_CIRCUIT_BREAKER_COMPATIBILITY.md"
DEVIATIONS = ROOT / "LIDO_CIRCUIT_BREAKER_DEVIATIONS.md"
DEFAULT_LOCK = ROOT / "scripts" / "lido-circuit-breaker-reference.json"
DEFAULT_MANIFEST = ROOT / "scripts" / "fixtures" / "lido-circuit-breaker" / "manifest.json"

SIGNATURES = [
    "ADMIN()", "MIN_PAUSE_DURATION()", "MAX_PAUSE_DURATION()",
    "MIN_HEARTBEAT_INTERVAL()", "MAX_HEARTBEAT_INTERVAL()", "pauseDuration()",
    "heartbeatInterval()", "heartbeatExpiry(address)", "getPauser(address)",
    "getPausableCount(address)", "getPausables()", "isPauserLive(address)",
    "setPauseDuration(uint256)", "setHeartbeatInterval(uint256)",
    "registerPauser(address,address)", "heartbeat()", "pause(address)",
]
CROSSCUTS = [
    "dispatch-nonpayability", "registry-histories", "temporal-arithmetic",
    "errors-events-order", "external-return-allocation", "reentry-interference",
    "rollback", "logical-state-projection", "oracle-independence", "finite-evidence",
]
CONSTRUCTOR_ARGUMENTS = ["address", "uint256", "uint256", "uint256", "uint256", "uint256", "uint256"]
ENDPOINT_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-ENDPOINT (\{.*\}) -->$")
CONSTRUCTOR_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-CONSTRUCTOR (\{.*\}) -->$")
CROSSCUT_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-CROSSCUT ([a-z0-9-]+) -->$")
SEMANTIC_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-SEMANTIC ([a-z0-9-]+) -->$")
DEVIATION_POLICY_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-DEVIATION-POLICY (\{.*\}) -->$")
GAS_MEASUREMENT_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-GAS-MEASUREMENT (\{.*\}) -->$")
GAS_ROW_RE = re.compile(r"^<!-- LIDO-CIRCUIT-BREAKER-GAS (\{.*\}) -->$")
SEMANTIC_KEYS = [
    "registry-zero-zero", "registry-same-pauser", "registry-swap-pop",
    "pause-chronology", "return-data", "lock-namespace",
    "intermediate-liveness", "projection-domain", "gas-boundary",
]
SEMANTIC_REQUIREMENTS = {
    "registry-zero-zero": (
        "temporarily appends the target, writes its one-based index",
        "then removes it and clears the index",
        "emits `PauserSet` even though the boundary Registry is unchanged",
    ),
    "registry-same-pauser": (
        "decrements that pauser's count and then increments it",
        "the observable boundary count is unchanged",
        "the ordered writes and `PauserSet` remain part of compatibility",
    ),
    "registry-swap-pop": (
        "swap-and-pop, repairs the moved target's one-based index",
        "last/self-swap behavior",
        "first/middle/last/only removal",
        "moved-element follow-up",
    ),
    "pause-chronology": (
        "calldata/canonical-address checks; addressed transient-lock check/set",
        "assignment and strict-liveness checks; duration snapshot; complete unregister",
        "`EXTCODESIZE`; `pauseFor(duration)` `CALL`; `isPaused()` `STATICCALL`",
        "Boolean decode; `PauseTriggered`",
        "post-callback count and then-current heartbeat interval; and addressed unlock",
    ),
    "return-data": (
        "Child failure bubbles",
        "return shorter than 32 bytes empty-reverts",
        "first word `0` yields `PauseFailed`; `1` succeeds",
        "any other first word empty-reverts as a noncanonical Boolean",
        "trailing bytes after `0` or `1` do not change the decoded value",
        "complete successful returndata is allocated/copied before decoding",
        "First-word-only shortcuts are outside the allowed implementation freedom",
    ),
    "lock-namespace": (
        "addressed by the current CircuitBreaker account and lock key",
        "descendant `pause` on that exact instance",
        "a clone has a different storage namespace",
        "`CALLCODE`, `DELEGATECALL`, or foreign installed code",
        "An authorized admin callback may reassign Registry state while pause is yielded",
        "not an arbitrary-descendant reentry or unconditional final noninterference theorem",
    ),
    "intermediate-liveness": (
        "assignment/count zero while the old expiry still makes `isPauserLive` true",
        "caught child failure restores the child-entry world",
        "bubbled outer failure restores the outer-entry world",
        "Failed-child logs, raw internal logs, top-level output logs, and receipt logs are distinct",
    ),
    "projection-domain": (
        "duplicate-free ordered array of nonzero canonical targets and nonzero canonical pausers",
        "assignment, one-based index, array entries/length, per-pauser multiplicity, and `count[0] = 0`",
        "Tagged mapping regions quantify only canonical address payloads",
        "region/tag disjointness and length/index/count nonwrap are later, currently unproved theorem obligations",
        "No global Keccak injectivity, raw-slot equality, or storage-root equality is assumed",
    ),
    "gas-boundary": (
        "Exact gas equality and an identical OOG threshold are excluded",
        "a measured gas increase on any externally callable named path is an observable behavioral deviation",
        "adequate-gas and returndata-scaling controls do not erase that registry obligation",
    ),
}
MANDATORY_AC9_TAGS = [
    "constructor-success", "official-world", "independent-world", "lower-bound",
    "upper-bound", "equal-bound", "constructor-error", "constructor-malformed",
    "short-tail", "dirty-admin", "constructor-trailing", "constructor-nonpayability",
    "constructor-precedence", "nonpayable-before-decode", "view-getter", "setter",
    "zero-target", "no-registry-write", "zero-registration", "fresh-registration",
    "same-pauser", "distinct-pauser", "remove-first", "remove-middle", "remove-last",
    "remove-only", "idempotent-unregister", "moved-element-followup",
    "one-pauser-many-targets", "ordered-enumeration", "64-elements", "dirty-address",
    "unauthorized-plus-zero", "unauthorized-plus-dirty", "strict-expiry",
    "unregistered-versus-expired", "unauthorized-versus-expired", "interval-change",
    "checked-overflow", "runtime-nonpayability", "unknown-selector", "empty-selector",
    "short-head", "trailing-calldata", "eoa", "target-revert", "query-revert", "false",
    "short-return", "noncanonical-bool", "true", "trailing-return", "large-return",
    "adequate-gas", "oog-control", "remaining-assignment", "last-assignment",
    "duration-snapshot", "post-callback-interval", "post-callback-count",
    "mid-call-liveness", "same-target-reentry", "different-target-reentry",
    "caught-child", "bubbled-child", "clone-namespace", "heartbeat-callback",
    "config-callback", "register-callback", "authorized-admin-reassignment",
    "target-truth-not-guaranteed", "full-rollback", "outer-rollback",
    "sequential-transactions", "after-success", "after-failure", "transient-reset",
]
EXPECTED_CASE_NAMES_SHA256 = "c837157e40a74cca955c4ab266334f58044dfc1ed255cad69d64203f6776436f"
EXPECTED_ROW_SEMANTICS_SHA256 = "a0f97d667e827fcc5e808ed0f1ec66bcdef2af49454976e15989ee81acd90331"
ROW_SEMANTIC_FIELDS = (
    "name", "family", "owner", "world", "endpoint", "historyLength",
    "execution", "channels", "tags",
)
EXPECTED_PROJECTION = {
    "comparisonDomain": {
        "observedAddressesAreManifestDeclared": True,
        "orderedArray": True,
        "rawSlotEqualityExcluded": True,
        "registryLengthMaximumRead": 256,
    },
    "leanOwnedBlancProjection": {
        "blancFormula": "bitwise-or(region-times-two-pow-252,payload)",
        "domainQualifiers": {
            "array-index": "one-based",
            "canonical-address-bits": "160",
            "pausers-nonzero": "true",
            "tag-payload-upper-bound-exclusive": "2^252",
            "targets-nodup": "true",
            "targets-nonzero": "true",
            "zero-count-explicit": "true",
        },
        "regionWords": {
            "array": "0x6000000000000000000000000000000000000000000000000000000000000000",
            "assignment": "0x3000000000000000000000000000000000000000000000000000000000000000",
            "config": "0x1000000000000000000000000000000000000000000000000000000000000000",
            "count": "0x5000000000000000000000000000000000000000000000000000000000000000",
            "expiry": "0x2000000000000000000000000000000000000000000000000000000000000000",
            "index": "0x4000000000000000000000000000000000000000000000000000000000000000",
        },
        "regions": {
            "array": 6, "assignment": 3, "config": 1,
            "count": 5, "expiry": 2, "index": 4,
        },
    },
    "solidityProjection": {
        "arrayEntry": "keccak256(uint256(5)) + zero-based-index mod 2^256",
        "arrayLengthSlot": 5,
        "assignment": "keccak256(address-word || uint256(3))",
        "assignmentCount": "keccak256(address-word || uint256(6))",
        "configurationSlots": {"heartbeatInterval": 1, "pauseDuration": 0},
        "heartbeatExpiry": "keccak256(address-word || uint256(2))",
        "oneBasedIndex": "keccak256(address-word || uint256(4))",
    },
}
MANIFEST_TAGS = {
    "dispatch-nonpayability": {"runtime-nonpayability", "unknown-selector", "short-head", "trailing-calldata"},
    "registry-histories": {"fresh-registration", "same-pauser", "decrement-increment",
                           "temporary-append-remove", "idempotent-unregister", "swap-and-pop",
                           "self-swap", "moved-element-followup", "64-elements"},
    "temporal-arithmetic": {"strict-expiry", "interval-change", "checked-overflow"},
    "errors-events-order": {"constructor-error", "setter", "Panic-0x11"},
    "external-return-allocation": {"short-return", "false", "true", "noncanonical-bool",
                                   "trailing-return", "large-return", "adequate-gas",
                                   "oog-control", "duration-snapshot", "post-callback-count",
                                   "post-callback-interval"},
    "reentry-interference": {"same-target-reentry", "different-target-reentry", "caught-child",
                             "bubbled-child", "clone-namespace", "mid-call-liveness"},
    "rollback": {"full-rollback", "outer-rollback", "after-failure"},
    "logical-state-projection": {"no-registry-write", "ordered-enumeration"},
    "oracle-independence": {"official-world", "independent-world"},
    "finite-evidence": {"constructor-precedence", "target-truth-not-guaranteed"},
}

GAS_ROWS = [
    ("constructor-dirty-admin", 260, 1131, 871),
    ("constructor-error-admin-zero", 481, 1162, 681),
    ("constructor-error-min-heartbeat-above-max", 577, 1262, 685),
    ("constructor-error-min-heartbeat-zero", 551, 1234, 683),
    ("constructor-error-min-pause-above-max", 529, 1212, 683),
    ("constructor-error-min-pause-zero", 503, 1184, 681),
    ("constructor-precedence-admin-zero-plus-min-pause-zero", 481, 1162, 681),
    ("constructor-precedence-both-bound-inversions", 529, 1212, 683),
    ("constructor-success-equal-bounds", 967777, 1029868, 62091),
    ("constructor-success-exact-lower-bounds", 967777, 1029868, 62091),
    ("constructor-success-exact-upper-bounds", 967777, 1029868, 62091),
    ("constructor-success-independent", 967777, 1029868, 62091),
    ("constructor-success-official", 967777, 1029868, 62091),
    ("constructor-trailing-arguments", 967783, 1029868, 62085),
    ("nonpayable-ADMIN", 43, 145, 102),
    ("nonpayable-MAX_HEARTBEAT_INTERVAL", 43, 144, 101),
    ("nonpayable-MAX_PAUSE_DURATION", 43, 168, 125),
    ("nonpayable-MIN_HEARTBEAT_INTERVAL", 43, 144, 101),
    ("nonpayable-MIN_PAUSE_DURATION", 43, 144, 101),
    ("nonpayable-getPausableCount", 43, 143, 100),
    ("nonpayable-getPausables", 43, 144, 101),
    ("nonpayable-getPauser", 43, 145, 102),
    ("nonpayable-heartbeat", 43, 144, 101),
    ("nonpayable-heartbeatExpiry", 43, 143, 100),
    ("nonpayable-heartbeatInterval", 43, 144, 101),
    ("nonpayable-isPauserLive", 43, 142, 99),
    ("nonpayable-pause", 43, 145, 102),
    ("nonpayable-pauseDuration", 43, 169, 126),
    ("nonpayable-registerPauser", 43, 145, 102),
    ("nonpayable-setHeartbeatInterval", 43, 143, 100),
    ("nonpayable-setPauseDuration", 43, 143, 100),
    ("pause-return-true-large-32768", 57317, 58262, 945),
    ("runtime-empty-calldata", 68, 162, 94),
]
PENDING_DEVIATION_REQUIREMENTS = {
    "GAS-1": (
        "Successful Solidity construction uses 967,777 gas",
        "A factory or deployment envelope with a Solidity-calibrated fixed limit may fail",
        "the cost buys the generated, parameterized Blanc constructor/runtime family",
    ),
    "GAS-2": (
        "constructor rejection/dirty-address paths revert on both sides",
        "A tightly limited failing creation can exhaust gas before returning the same reference error",
        "the shared fail-closed constructor decoder/validation structure",
    ),
    "GAS-3": (
        "Every selector rejects nonzero runtime value before endpoint effects",
        "an exact Solidity-calibrated failure stipend may observe OOG instead of the same empty revert",
        "the uniform generated nonpayability/dispatch boundary",
    ),
    "GAS-4": (
        "Empty calldata reverts on both sides",
        "A fixed 68–161 gas execution envelope distinguishes the artifacts",
        "the small cost buys Blanc's generated dispatcher",
    ),
    "GAS-5": (
        "With a 32,768-byte successful `isPaused()` return, both sides allocate/copy the full returndata",
        "A tight Solidity-calibrated envelope can make only Blanc OOG",
        "source-compatible complete returndata handling in the Blanc runtime",
    ),
}


class CompatibilityError(RuntimeError):
    pass


def parse_marker(raw: str, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise CompatibilityError(f"malformed {label} marker: {raw}") from exc
    if not isinstance(value, dict):
        raise CompatibilityError(f"{label} marker is not an object")
    return value


def check_document() -> list[dict[str, Any]]:
    try:
        lines = DOCUMENT.read_text().splitlines()
    except OSError as exc:
        raise CompatibilityError(f"cannot read {DOCUMENT.name}: {exc}") from exc
    endpoint_markers: list[dict[str, Any]] = []
    constructors: list[dict[str, Any]] = []
    crosscuts: list[str] = []
    semantics: list[str] = []
    semantic_positions: dict[str, int] = {}
    for line_number, line in enumerate(lines):
        if match := ENDPOINT_RE.fullmatch(line):
            marker = parse_marker(match.group(1), "endpoint")
            if set(marker) != {"signature", "selector"} or not isinstance(marker["signature"], str):
                raise CompatibilityError(f"endpoint marker has wrong shape: {line}")
            if not isinstance(marker["selector"], str):
                raise CompatibilityError(f"endpoint selector must be locked: {line}")
            endpoint_markers.append(marker)
        elif match := CONSTRUCTOR_RE.fullmatch(line):
            constructors.append(parse_marker(match.group(1), "constructor"))
        elif match := CROSSCUT_RE.fullmatch(line):
            crosscuts.append(match.group(1))
        elif match := SEMANTIC_RE.fullmatch(line):
            key = match.group(1)
            semantics.append(key)
            semantic_positions[key] = line_number
    endpoint_signatures = [marker["signature"] for marker in endpoint_markers]
    if endpoint_signatures != SIGNATURES:
        raise CompatibilityError(
            f"endpoint markers differ\nexpected: {SIGNATURES}\nfound: {endpoint_signatures}")
    if constructors != [{"arguments": CONSTRUCTOR_ARGUMENTS}]:
        raise CompatibilityError("constructor marker must name exactly seven ABI argument types")
    if crosscuts != CROSSCUTS:
        raise CompatibilityError(f"cross-cut markers differ\nexpected: {CROSSCUTS}\nfound: {crosscuts}")
    if semantics != SEMANTIC_KEYS:
        raise CompatibilityError(
            f"semantic boundary markers differ\nexpected: {SEMANTIC_KEYS}\nfound: {semantics}")
    for key, phrases in SEMANTIC_REQUIREMENTS.items():
        start = semantic_positions[key] + 1
        end = next(
            (index for index in range(start, len(lines))
             if SEMANTIC_RE.fullmatch(lines[index]) or CROSSCUT_RE.fullmatch(lines[index])),
            len(lines),
        )
        section = " ".join("\n".join(lines[start:end]).split())
        for phrase in phrases:
            normalized_phrase = " ".join(phrase.split())
            if section.count(normalized_phrase) != 1:
                raise CompatibilityError(
                    f"semantic boundary {key} is missing or duplicates: {phrase}")
    normalized = " ".join("\n".join(lines).split())
    if "when landed" in normalized:
        raise CompatibilityError("compatibility contract still describes landed evidence as pending")
    return endpoint_markers


def check_lock(lock_path: Path, endpoint_markers: list[dict[str, Any]]) -> None:
    try:
        lock = json.loads(lock_path.read_text())
    except OSError as exc:
        raise CompatibilityError(f"cannot read reference lock {lock_path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise CompatibilityError(f"reference lock is invalid JSON: {exc}") from exc
    try:
        abi = lock["abi"]
        functions = abi["functions"]
        constructor = abi["constructor"]
        errors = abi["errors"]
        events = abi["events"]
    except (KeyError, TypeError) as exc:
        raise CompatibilityError("reference lock missing required abi.functions/constructor/errors/events") from exc
    if not isinstance(functions, list):
        raise CompatibilityError("reference lock abi.functions is not a list")
    locked = []
    locked_rows: dict[str, dict[str, str]] = {}
    for row in functions:
        if not isinstance(row, dict) or not isinstance(row.get("signature"), str) or not isinstance(row.get("selector"), str):
            raise CompatibilityError("reference lock has malformed function row")
        locked.append(row["signature"])
        locked_rows[row["signature"]] = {"signature": row["signature"], "selector": row["selector"]}
    if set(locked) != set(SIGNATURES) or len(locked) != len(SIGNATURES):
        raise CompatibilityError(f"reference-lock selectors differ\nexpected: {SIGNATURES}\nfound: {locked}")
    expected_markers = [locked_rows[signature] for signature in SIGNATURES]
    if endpoint_markers != expected_markers:
        raise CompatibilityError(
            f"document endpoint selectors differ from reference lock\n"
            f"expected: {expected_markers}\nfound: {endpoint_markers}")
    if not isinstance(constructor, dict) or constructor.get("argumentTypes") != CONSTRUCTOR_ARGUMENTS:
        raise CompatibilityError("reference lock constructor does not have the pinned seven ABI types")
    if not isinstance(errors, list) or len(errors) != 15:
        raise CompatibilityError("reference lock must inventory exactly 15 custom errors")
    if not isinstance(events, list) or len(events) != 6:
        raise CompatibilityError("reference lock must inventory exactly 6 event families")


def check_manifest(manifest_path: Path) -> dict[str, Any]:
    try:
        manifest = json.loads(manifest_path.read_text())
    except OSError as exc:
        raise CompatibilityError(f"cannot read differential manifest {manifest_path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise CompatibilityError(f"differential manifest is invalid JSON: {exc}") from exc
    expected_top = {
        "schema", "oracle", "blanc", "projection", "execution", "coverage",
        "counts", "resourceEvidence", "rows", "explicitLimits",
    }
    if manifest.get("schema") != 2 or set(manifest) != expected_top:
        raise CompatibilityError("differential manifest schema/top-level inventory differs")
    try:
        counts = manifest["counts"]
        coverage = manifest["coverage"]
        execution = manifest["execution"]
        rows = manifest["rows"]
    except (KeyError, TypeError) as exc:
        raise CompatibilityError("differential manifest lacks counts/coverage/execution/rows") from exc
    if counts.get("runtimeSelectors") != 17 or counts.get("constructorArguments") != 7:
        raise CompatibilityError("differential manifest does not cover the locked runtime/constructor surface")
    if counts.get("customErrors") != 15 or counts.get("events") != 6:
        raise CompatibilityError("differential manifest error/event counts differ from the compatibility boundary")
    if counts.get("rows") != len(rows) or not rows:
        raise CompatibilityError("differential manifest row count is stale or empty")
    endpoint_counts = coverage.get("endpointCounts")
    if not isinstance(endpoint_counts, dict) or any(endpoint_counts.get(signature, 0) < 1 for signature in SIGNATURES):
        raise CompatibilityError("differential manifest has an uncovered compatibility endpoint")
    if endpoint_counts.get("constructor", 0) < 1:
        raise CompatibilityError("differential manifest has no constructor row")
    required_tags = coverage.get("requiredTags", [])
    tag_counts = coverage.get("tagCounts", {})
    if required_tags != MANDATORY_AC9_TAGS:
        raise CompatibilityError(
            "differential manifest mandatory AC9 tag inventory differs\n"
            f"expected: {MANDATORY_AC9_TAGS}\nfound: {required_tags}")
    if not isinstance(tag_counts, dict) or any(tag_counts.get(tag, 0) < 1 for tag in required_tags):
        raise CompatibilityError("differential manifest mandatory AC9 tag has no credited row")
    recomputed_tags: Counter[str] = Counter()
    row_names: set[str] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or set(row) != set(ROW_SEMANTIC_FIELDS) \
                or not isinstance(row.get("name"), str) \
                or not isinstance(row.get("tags"), list) \
                or not all(isinstance(tag, str) for tag in row["tags"]):
            raise CompatibilityError(
                f"differential manifest row {index} has malformed semantic fields")
        if row["name"] in row_names:
            raise CompatibilityError(f"differential manifest has duplicate row name {row['name']}")
        row_names.add(row["name"])
        recomputed_tags.update(row["tags"])
    if dict(sorted(recomputed_tags.items())) != tag_counts:
        raise CompatibilityError("differential manifest tagCounts are not derived from exact row tags")
    case_name_payload = ("\n".join(row["name"] for row in rows) + "\n").encode()
    if hashlib.sha256(case_name_payload).hexdigest() != EXPECTED_CASE_NAMES_SHA256:
        raise CompatibilityError("differential manifest exact ordered case-name digest differs")
    row_semantics = [
        {field: row[field] for field in ROW_SEMANTIC_FIELDS}
        for row in rows
    ]
    semantic_payload = json.dumps(
        row_semantics, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode()
    if hashlib.sha256(semantic_payload).hexdigest() != EXPECTED_ROW_SEMANTICS_SHA256:
        raise CompatibilityError(
            "differential manifest exact row semantic/execution digest differs")
    if manifest.get("projection") != EXPECTED_PROJECTION:
        raise CompatibilityError(
            "differential manifest exact projection formulas/regions/qualifiers differ")
    available_tags = {tag for tag, count in tag_counts.items() if isinstance(count, int) and count > 0}
    for crosscut, required in MANIFEST_TAGS.items():
        missing = required - available_tags
        if missing:
            raise CompatibilityError(
                f"differential manifest no longer supports cross-cut {crosscut}: {sorted(missing)}")
    channels = coverage.get("channelCounts", {})
    for channel in ("status", "returndata", "state-projection", "eth", "logs", "call-trace"):
        if channels.get(channel) != len(rows):
            raise CompatibilityError(f"differential channel {channel} does not cover every manifest row")
    if execution.get("constructorCausalRuntimeHistories") is not True or \
            execution.get("projectionExcludesRawSlotEquality") is not True:
        raise CompatibilityError("differential manifest weakened causal-history or projection ownership")
    return manifest


def check_deviations(manifest: dict[str, Any]) -> None:
    try:
        text = DEVIATIONS.read_text()
    except OSError as exc:
        raise CompatibilityError(f"cannot read {DEVIATIONS.name}: {exc}") from exc
    required_headings = [
        "## Accepted behavioral deviations",
        "## Pending user adjudication — conformance blocker",
        "## Measured named-path gas deltas",
        "## Low-level implementation freedoms (not behavioral deviations)",
        "## Explicit exclusions and verification debts",
    ]
    if any(text.count(heading) != 1 for heading in required_headings):
        raise CompatibilityError("deviation registry headings are missing or duplicated")
    if "mismatch allowlist" not in text or "contains no" not in text:
        raise CompatibilityError("deviation registry no longer rejects an unknown-mismatch allowlist")
    pending = text.split(required_headings[1], 1)[1].split(required_headings[2], 1)[0]
    pending_normalized = " ".join(pending.split())
    pending_rows = re.findall(r"^\| (GAS-[0-9]+) \|", pending, flags=re.MULTILINE)
    if pending_rows != list(PENDING_DEVIATION_REQUIREMENTS):
        raise CompatibilityError(
            "pending gas-deviation row inventory differs from the five undecided classes")
    for identifier, phrases in PENDING_DEVIATION_REQUIREMENTS.items():
        if text.count(f"| {identifier} |") != 1:
            raise CompatibilityError(
                f"pending gas-deviation stance {identifier} is missing or duplicated")
        for phrase in phrases:
            if pending_normalized.count(" ".join(phrase.split())) != 1:
                raise CompatibilityError(
                    f"pending gas-deviation {identifier} rationale differs: {phrase}")
    policies = []
    measurements = []
    gas_rows = []
    for line in text.splitlines():
        if match := DEVIATION_POLICY_RE.fullmatch(line):
            policies.append(parse_marker(match.group(1), "deviation policy"))
        elif match := GAS_MEASUREMENT_RE.fullmatch(line):
            measurements.append(parse_marker(match.group(1), "gas measurement"))
        elif match := GAS_ROW_RE.fullmatch(line):
            gas_rows.append(parse_marker(match.group(1), "gas row"))
    accepted = text.split(required_headings[0], 1)[1].split(required_headings[1], 1)[0]
    accepted_normalized = " ".join(accepted.split())
    if "None." not in accepted_normalized or \
            "have not been accepted by the user" not in accepted_normalized:
        raise CompatibilityError("accepted-deviation section does not preserve the pending user decision")
    expected_policy = {
        "status": "pending-user-adjudication", "unknownMismatchAllowlist": False,
        "acceptedBehavioralRows": 0, "pendingBehavioralRows": 5, "measuredGasPaths": 33}
    if policies != [expected_policy]:
        raise CompatibilityError("deviation policy marker differs from the pending five-row/33-path boundary")
    try:
        expected_measurement = {
            "eelsCommit": manifest["execution"]["eelsCommit"],
            "solidityRuntimeSha256": manifest["oracle"]["officialRuntimeSha256"],
            "blancRuntimeSha256": manifest["blanc"]["official"]["runtimeSha256"],
            "gasModel": "EELS Prague gasUsed for final case transaction", "pathCount": len(GAS_ROWS),
        }
    except (KeyError, TypeError) as exc:
        raise CompatibilityError("differential manifest lacks gas-measurement artifact identities") from exc
    if measurements != [expected_measurement]:
        raise CompatibilityError(
            f"gas measurement identity differs from current manifest\n"
            f"expected: {expected_measurement}\nfound: {measurements}")
    expected_rows = [
        {"path": path, "solidity": solidity, "blanc": blanc, "delta": delta}
        for path, solidity, blanc, delta in GAS_ROWS]
    if gas_rows != expected_rows:
        raise CompatibilityError("measured named-path gas ledger differs from pinned exact rows")
    manifest_names = {row["name"] for row in manifest["rows"]}
    missing = [row["path"] for row in gas_rows if row["path"] not in manifest_names]
    if missing:
        raise CompatibilityError(f"gas ledger names paths absent from differential manifest: {missing}")
    if any(row["blanc"] - row["solidity"] != row["delta"] or row["delta"] <= 0
           for row in gas_rows):
        raise CompatibilityError("gas ledger has a non-derived or non-positive delta")
    if "every known increase on an externally callable named path is a behavioral deviation" not in text:
        raise CompatibilityError("low-level freedom section launders gas increases as exact-gas freedom")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("check",))
    parser.add_argument("--lock", type=Path, default=DEFAULT_LOCK)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--allow-missing-lock", action="store_true")
    args = parser.parse_args()
    try:
        endpoint_markers = check_document()
        if args.lock.exists():
            check_lock(args.lock, endpoint_markers)
            manifest = check_manifest(args.manifest)
            check_deviations(manifest)
            print("OK — Lido CircuitBreaker compatibility: 17 endpoint keys, constructor, 10 cross-cutting keys, full AC9 tags synchronized; 5 gas-deviation classes pending user adjudication")
        elif args.allow_missing_lock:
            print("OK — Lido CircuitBreaker compatibility: 17 endpoint keys, constructor, 10 cross-cutting keys; PENDING reference lock at " + str(args.lock))
        else:
            raise CompatibilityError("reference lock is missing at " + str(args.lock) + "; use --allow-missing-lock only for pre-AC2 document checks")
    except CompatibilityError as exc:
        print("REGRESSION — Lido CircuitBreaker compatibility: " + str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
