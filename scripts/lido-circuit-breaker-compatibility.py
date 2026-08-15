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
        "Child failure bubbles the complete revert data",
        "requests and captures a 32-byte `STATICCALL` output window",
        "requires `RETURNDATASIZE ≥ 32`",
        "return shorter than 32 bytes empty-reverts",
        "first word `0` yields `PauseFailed`; `1` succeeds",
        "any other first word empty-reverts as a noncanonical Boolean",
        "trailing bytes after `0` or `1` do not change the decoded value",
        "does not copy the unused successful tail",
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
        "region/tag disjointness, length/index/count nonwrap, exact chronological replay",
        "witness preservation at the post-Registry boundary",
        "does not assume those facts as extra invariant fields",
        "No global Keccak injectivity, raw-slot equality, or storage-root equality is assumed",
    ),
    "gas-boundary": (
        "Exact gas equality and an identical OOG threshold are excluded",
        "every adequate boundary in the optimized finite vector is cheaper",
        "All 33 former `GAS-1` through `GAS-5` witnesses have independently pinned minimum-completion thresholds with Blanc no greater than Solidity",
        "The independently pinned `intrinsic-branch-dispatch` set is empty",
        "does not claim universal gas dominance",
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
EXPECTED_CASE_NAMES_SHA256 = "51bc9e83f457ac7ec90295cace8860e62564de65f968ff5d3b51a19954b85430"
EXPECTED_ROW_SEMANTICS_SHA256 = "faa4f3906baf91edf3f7dd4ada850227df1966b24bfead99516aff03e3b3daa1"
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

EXPECTED_MANIFEST_SHA256 = \
    "2b0716f7d666d69d2844e2c8a01b5cd3f59cc124ba571ef16a5a02ad55cf3693"
EXPECTED_BLANC_ARTIFACTS = {
    "creationTemplate": {
        "byteLength": 4898,
        "sha256": "e899d8f2d7406f7aa6bf6ac60e25779355c6f1e3063f5edd4aed694710ba2eaa",
    },
    "official": {
        "fullCreateByteLength": 5122,
        "fullCreateSha256": "bbf5c2c548a4c56ae9079cdb63f20b607ea8c4dabf853771bd33228099e2fa64",
        "runtimeByteLength": 4282,
        "runtimeSha256": "ff8eb66d66f8e4668af9bf5b687dda082c3729f8cd5ffd24a4b14697389d1505",
    },
    "independent": {
        "fullCreateByteLength": 5122,
        "fullCreateSha256": "c33bbb06829ca1f66c536ace9d0a8a108a6f7c1a609f3aed68490afdfa50862f",
        "runtimeByteLength": 4282,
        "runtimeSha256": "ce955ede77a6343897f61bd5395731e404d9ca271fe86849359c6c9d50803796",
    },
}
EXPECTED_RESOURCE_IDENTITIES = {
    "blancCreationTemplateSha256":
        "e899d8f2d7406f7aa6bf6ac60e25779355c6f1e3063f5edd4aed694710ba2eaa",
    "blancIndependentFullCreateSha256":
        "c33bbb06829ca1f66c536ace9d0a8a108a6f7c1a609f3aed68490afdfa50862f",
    "blancIndependentRuntimeSha256":
        "ce955ede77a6343897f61bd5395731e404d9ca271fe86849359c6c9d50803796",
    "blancOfficialFullCreateSha256":
        "bbf5c2c548a4c56ae9079cdb63f20b607ea8c4dabf853771bd33228099e2fa64",
    "blancOfficialRuntimeSha256":
        "ff8eb66d66f8e4668af9bf5b687dda082c3729f8cd5ffd24a4b14697389d1505",
    "eelsCommit": "4198b9c5996713b268aed602739d5aa40e277694",
    "referenceSourceCommit": "6829a5a962ece56564bd9d72d01c29cabf157579",
    "solidityIndependentFullCreateSha256":
        "fa683c7c793bec9410284271ecaa7fe8ca8f12759dbca0e8a937e1dbea47da86",
    "solidityIndependentRuntimeSha256":
        "a264bca00fa7d8b264e1666e9da3bacc87b90f285583340987f6f884795f3317",
    "solidityOfficialFullCreateSha256":
        "f2800888ef707680a581939c93f7975d24f25ce14641900591418e8be23400dc",
    "solidityOfficialRuntimeSha256":
        "7decb73763f1c184f5e1950c5e3449fbca507fdf40836769df2e67fccd0c8a1e",
}
EXPECTED_RESOURCE_SUMMARY = {
    "adequacyCounts": {"adequate": 462, "oog-control": 2},
    "adequatePositiveDeltaCount": 0,
    "blancGasUsedTotal": 155182835,
    "blancMinusSolidityTotal": -9567434,
    "boundaryCount": 464,
    "comparisonClassCounts": {
        "blanc-cheaper": 462, "blanc-dearer": 0, "equal": 2,
    },
    "solidityGasUsedTotal": 164750269,
    "successfulStrictImprovementCount": 362,
}
EXPECTED_VECTOR_DIGESTS = {
    "fullResourceVectorSha256":
        "98392ffe11a9eeef6407e90cc42b55739f384c154ef090473882e5d60d69a335",
    "orderedCoordinatesSha256":
        "07ca7475b4af537e4866de0a8f102f043ced22c4207ef8587d7570bd9151aef2",
}
EXPECTED_COMPLETION_THRESHOLD_ROWS_SHA256 = \
    "49456665e2c6095cb1aa467231d78e45deef3d5dc9614248fcdcd756217c83fe"
EXPECTED_DISPATCHER_THRESHOLD_ROWS_SHA256 = \
    "b7b8f0ad5ca7e96de4cff76f54b4c661fce7f3faefd8e6d15526d9317db78bee"
EXPECTED_INTRINSIC_BRANCH_DISPATCH = {
    "admissionRequires": [
        "independent opcode traces place the entire excess before the selected leaf",
        "no later Blanc segment is costlier than the Solidity segment",
        "the selected legal tree is Pareto-justified against balanced, linear, and hybrid legal trees",
        "the exact coordinate and delta are independently pinned and mutation-tested",
    ],
    "architecture": "all Blanc control flow, including selector dispatch, uses Func.branch",
    "classification": "intrinsic-branch-dispatch",
    "directJumpDispatchAllowed": False,
    "orderedRows": [],
    "orderedRowsSha256":
        "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945",
    "rowCount": 0,
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
        raw = manifest_path.read_bytes()
        manifest = json.loads(raw)
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
    if hashlib.sha256(raw).hexdigest() != EXPECTED_MANIFEST_SHA256:
        raise CompatibilityError("optimized differential manifest SHA-256 differs")
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
    if counts.get("rows") != 175 or counts.get("rows") != len(rows):
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
    blanc = manifest.get("blanc")
    if not isinstance(blanc, dict) or any(
            blanc.get(key) != expected
            for key, expected in EXPECTED_BLANC_ARTIFACTS.items()):
        raise CompatibilityError("optimized Blanc artifact sizes/identities differ")
    resources = manifest.get("resourceEvidence")
    if not isinstance(resources, dict):
        raise CompatibilityError("optimized resource evidence is missing")
    lifecycle = resources.get("lifecycle")
    expected_lifecycle = {
        "stage": "optimized",
        "baselineBlancCommit": "fc3edee6dbfb77eaf344afee43c921d48ff8a3af",
        "baselineManifestSha256":
            "6cde638ac37977f3aea228ad877a85d37e415ac4f927e66a099be67de7d30cef",
        "optimizedTransitionRequires": {
            "independentCoordinateVectorAndExceptionRepin": True,
            "perBoundaryDominanceOrPinnedIntrinsicBranchDispatch": True,
            "strictSuccessfulImprovement": True,
        },
    }
    if lifecycle != expected_lifecycle:
        raise CompatibilityError("optimized lifecycle or frozen baseline identity differs")
    if resources.get("identities") != EXPECTED_RESOURCE_IDENTITIES or \
            resources.get("summary") != EXPECTED_RESOURCE_SUMMARY or \
            resources.get("vectorDigests") != EXPECTED_VECTOR_DIGESTS:
        raise CompatibilityError("optimized artifact/resource vector identity differs")
    intrinsic = resources.get("intrinsicBranchDispatch")
    if intrinsic != EXPECTED_INTRINSIC_BRANCH_DISPATCH:
        raise CompatibilityError("intrinsic-branch-dispatch evidence is not the exact empty set")
    boundaries = resources.get("boundaries")
    if not isinstance(boundaries, list) or len(boundaries) != 464:
        raise CompatibilityError("optimized resource boundary count differs")
    positives = [row for row in boundaries
                 if row.get("adequacy") == "adequate" and
                 isinstance(row.get("blancMinusSolidity"), int) and
                 row["blancMinusSolidity"] > 0]
    if positives or EXPECTED_RESOURCE_SUMMARY["adequatePositiveDeltaCount"] != 0:
        raise CompatibilityError("optimized resource vector contains an adequate positive delta")
    thresholds = resources.get("completionThresholds")
    if not isinstance(thresholds, dict) or thresholds.get("schema") != 1 or \
            thresholds.get("rowCount") != 33 or \
            thresholds.get("orderedRowsSha256") != \
                EXPECTED_COMPLETION_THRESHOLD_ROWS_SHA256:
        raise CompatibilityError("optimized completion-threshold identity/count differs")
    threshold_rows = thresholds.get("orderedRows")
    if not isinstance(threshold_rows, list) or len(threshold_rows) != 33 or \
            Counter(row.get("class") for row in threshold_rows) != Counter({
                "GAS-1": 6, "GAS-2": 8, "GAS-3": 17,
                "GAS-4": 1, "GAS-5": 1}):
        raise CompatibilityError("optimized completion-threshold GAS roster differs")
    for ordinal, row in enumerate(threshold_rows):
        solidity = row.get("solidityCompletionGas")
        blanc = row.get("blancCompletionGas")
        if row.get("ordinal") != ordinal or type(solidity) is not int or \
                type(blanc) is not int or \
                row.get("blancMinusSolidity") != blanc - solidity or \
                blanc > solidity or \
                row.get("solidityThresholdMinusOneCompletes") is not False or \
                row.get("blancThresholdMinusOneCompletes") is not False:
            raise CompatibilityError("optimized completion threshold is not minimal/derived/dominant")
    cross = thresholds.get("dispatcherCrossCheck")
    if not isinstance(cross, dict) or cross.get("selectedDispatcher") != \
            "shared-hybrid-5-4-4-4" or cross.get("rowCount") != 18 or \
            cross.get("orderedRowsSha256") != \
                EXPECTED_DISPATCHER_THRESHOLD_ROWS_SHA256 or \
            cross.get("productionOfficialRuntimeSha256") != \
                EXPECTED_RESOURCE_IDENTITIES["blancOfficialRuntimeSha256"]:
        raise CompatibilityError("selected-dispatcher threshold cross-check differs")
    return manifest


def check_deviations(manifest: dict[str, Any]) -> None:
    try:
        text = DEVIATIONS.read_text()
    except OSError as exc:
        raise CompatibilityError(f"cannot read {DEVIATIONS.name}: {exc}") from exc
    required_headings = [
        "## Accepted behavioral deviations",
        "## Pending behavioral deviations",
        "## Optimized finite resource evidence",
        "## Intrinsic `.branch` dispatch comparison rows",
        "## Low-level implementation freedoms (not behavioral deviations)",
        "## Explicit exclusions and verification debts",
    ]
    if any(text.count(heading) != 1 for heading in required_headings):
        raise CompatibilityError("deviation registry headings are missing or duplicated")
    if "mismatch allowlist" not in text or "contains no" not in text:
        raise CompatibilityError("deviation registry no longer rejects an unknown-mismatch allowlist")
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
    pending = text.split(required_headings[1], 1)[1].split(required_headings[2], 1)[0]
    intrinsic = text.split(required_headings[3], 1)[1].split(required_headings[4], 1)[0]
    accepted_normalized = " ".join(accepted.split())
    pending_normalized = " ".join(pending.split())
    intrinsic_normalized = " ".join(intrinsic.split())
    if "None." not in accepted_normalized or "zero accepted behavioral deviations" not in accepted_normalized:
        raise CompatibilityError("accepted-deviation section does not pin the empty set")
    if "None." not in pending_normalized or "zero pending behavioral deviations" not in pending_normalized:
        raise CompatibilityError("pending-deviation section does not pin the empty set")
    if "empty" not in intrinsic_normalized or "zero rows" not in intrinsic_normalized:
        raise CompatibilityError("intrinsic-branch-dispatch section does not pin the empty set")
    expected_policy = {
        "status": "optimized-no-known-deviations",
        "unknownMismatchAllowlist": False,
        "acceptedBehavioralRows": 0,
        "pendingBehavioralRows": 0,
        "adequatePositiveDeltaRows": 0,
        "intrinsicBranchDispatchRows": 0,
        "completionThresholdRows": 33,
        "dispatcherThresholdRows": 18,
        "measuredResourceBoundaries": 464,
    }
    if policies != [expected_policy]:
        raise CompatibilityError("deviation policy marker differs from the optimized empty boundary")
    expected_measurement = {
        "stage": "optimized",
        "manifestSha256": EXPECTED_MANIFEST_SHA256,
        "eelsCommit": EXPECTED_RESOURCE_IDENTITIES["eelsCommit"],
        "cases": 175,
        "boundaries": 464,
        "adequateBoundaries": 462,
        "oogControls": 2,
        "adequatePositiveDeltas": 0,
        "intrinsicBranchDispatchRows": 0,
        "completionThresholdRows": 33,
        "completionThresholdRowsSha256":
            EXPECTED_COMPLETION_THRESHOLD_ROWS_SHA256,
        "dispatcherThresholdRows": 18,
        "dispatcherThresholdRowsSha256":
            EXPECTED_DISPATCHER_THRESHOLD_ROWS_SHA256,
        "successfulStrictImprovements": 362,
        "blancCreationTemplateSha256":
            EXPECTED_RESOURCE_IDENTITIES["blancCreationTemplateSha256"],
        "blancOfficialFullCreateSha256":
            EXPECTED_RESOURCE_IDENTITIES["blancOfficialFullCreateSha256"],
        "blancOfficialRuntimeSha256":
            EXPECTED_RESOURCE_IDENTITIES["blancOfficialRuntimeSha256"],
        "blancIndependentFullCreateSha256":
            EXPECTED_RESOURCE_IDENTITIES["blancIndependentFullCreateSha256"],
        "blancIndependentRuntimeSha256":
            EXPECTED_RESOURCE_IDENTITIES["blancIndependentRuntimeSha256"],
        **EXPECTED_VECTOR_DIGESTS,
    }
    if measurements != [expected_measurement]:
        raise CompatibilityError(
            f"optimized resource measurement identity differs from current manifest\n"
            f"expected: {expected_measurement}\nfound: {measurements}")
    if gas_rows:
        raise CompatibilityError("stale positive named-path gas rows survive optimized closure")
    normalized = " ".join(text.split())
    for phrase in (
            "every adequate boundary in the finite manifest is cheaper",
            "the two explicit OOG controls are equal",
            "All 33 former GAS-family witnesses have Blanc completion thresholds no greater than Solidity",
            "does not claim universal gas dominance",
            "A future positive adequate row is not silently netted against savings"):
        if normalized.count(phrase) != 1:
            raise CompatibilityError(f"optimized finite-resource claim differs: {phrase}")


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
            print("OK — Lido CircuitBreaker compatibility: 17 endpoint keys, constructor, 10 cross-cutting keys, full AC9 tags synchronized; optimized 175-case/464-boundary vector; 33 completion thresholds; 0 accepted/pending deviations; 0 intrinsic-branch rows")
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
