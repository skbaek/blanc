#!/usr/bin/env python3
"""Independent fail-closed schema owner for the Lido TWG differential."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "scripts" / "fixtures" / "lido-twg" / "manifest.json"
LOCK = ROOT / "scripts" / "lido-twg-reference.json"
CENSUS = ROOT / "scripts" / "lido-twg-census.json"
COMPATIBILITY = ROOT / "scripts" / "lido-twg-compatibility.py"
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
JAUNE_PIN = "949cf97ee1956828a3ac0eb12a62c438656ba76e"
BLANC_ARTIFACT_COMMIT = "35a196fd50192aa269d6cb07699ea0910ad3c468"
BLANC_PROOF_COMMIT = "a0e04e7a69558b8744ced81ea4a3defdfc478d36"
EVENT_TOPICS = {
    "ExitRequestsLimitSet": "0x3119d910326e0f179e121df55f23f45b8a5022ff10c73c02aabf2b48ae36070a",
    "Paused": "0x32fb7c9891bc4f963c7de9f1186d2a7755c7d6e9f4604dabe1d8bb3027c2f49e",
    "Resumed": "0x62451d457bc659158be6e6247f56ec1df424a5c7597f71c20c2bc44e0965c8f9",
    "RoleAdminChanged": "0xbd79b86ffe0ab8e8776151514217cd7cacd52c909f66475c3af44e129f0b00ff",
    "RoleGranted": "0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d",
    "RoleRevoked": "0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b",
}
EVENT_EXPECTATIONS = {
    "constructor-success": [EVENT_TOPICS["RoleGranted"], EVENT_TOPICS["ExitRequestsLimitSet"]],
    "view-role-admin": [],
    "grant-role-fresh": [EVENT_TOPICS["RoleGranted"]],
    "revoke-role-existing": [EVENT_TOPICS["RoleRevoked"]],
    "renounce-role-self": [EVENT_TOPICS["RoleRevoked"]],
    "pause-for-finite": [EVENT_TOPICS["Paused"]],
    "pause-for-sentinel": [EVENT_TOPICS["Paused"]],
    "pause-until-finite": [EVENT_TOPICS["Paused"]],
    "pause-until-sentinel": [EVENT_TOPICS["Paused"]],
    "resume-authorized": [EVENT_TOPICS["Resumed"]],
    "set-limit-valid": [EVENT_TOPICS["ExitRequestsLimitSet"]],
}
EVENT_TAG_EXPECTATIONS = {
    "constructor-success": "events.constructor",
    "view-role-admin": "events.RoleAdminChanged-nonemission",
    "grant-role-fresh": "events.RoleGranted",
    "revoke-role-existing": "events.RoleRevoked",
    "renounce-role-self": "events.RoleRevoked",
    "pause-for-finite": "events.Paused",
    "pause-for-sentinel": "events.Paused",
    "pause-until-finite": "events.Paused",
    "pause-until-sentinel": "events.Paused",
    "resume-authorized": "events.Resumed",
    "set-limit-valid": "events.ExitRequestsLimitSet",
}
CONSTRUCTOR_RETURNDATA = {
    "constructor-admin-zero": "0x6b35b1b7",
    "constructor-max-too-large": "0xaea5046a",
    "constructor-frame-too-large": "0xbbdd2da3",
    "constructor-exits-above-max": "0x528f4863",
    "constructor-zero-frame": "0x6765a75d",
    "constructor-dirty-admin": "0x",
    "constructor-nonpayable": "0x",
}
FEE_SELECTOR = "0xc44e30dc"
VAULT_SELECTOR = "0xeb3f512a"
ROUTER_SELECTOR = "0x71416583"
REFUND = "0x5555555555555555555555555555555555555555"
ACTOR = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
REJECTOR = "0xdead00000000000000000000000000000000beef"
TRIGGER_CALL_EXPECTATIONS = {
    "trigger-single-exact-fee": ("0x1", "0x1", "0x1", 7),
    "trigger-explicit-refund": ("0x1", "0x1", "0x1", 7),
    "trigger-sender-refund": ("0x1", "0x1", "0x1", 7),
    "trigger-multiple": ("0x1", "0x1", "0x1", 14),
    "trigger-vault-revert": ("0x1", "0x0", None, 7),
    "trigger-router-revert": ("0x1", "0x1", "0x0", 7),
    "trigger-refund-revert": ("0x1", "0x1", "0x1", 7),
}
FEE_EXPECTED_KEYS = {"feeQueryCalls", "feeQuerySelector", "feeQueryCallSuccess"}
VAULT_EXPECTED_KEYS = {"vaultCalls", "vaultSelector", "vaultCallSuccess", "vaultValue"}
ROUTER_EXPECTED_KEYS = {"routerCalls", "routerSelector", "routerCallSuccess"}
EXPECTED_KEYS = {
    "constructor-success": {"constructorStatus", "eventTopics"},
    **{name: {"constructorStatus", "constructorReturndata"}
       for name in CONSTRUCTOR_RETURNDATA},
    "view-role-admin": {"eventTopics", "eventNonemissionTopic"},
    "grant-role-fresh": {"eventTopics"},
    "revoke-role-existing": {"eventTopics"},
    "renounce-role-self": {"eventTopics"},
    "pause-for-finite": {"resumeSince", "eventTopics"},
    "pause-for-sentinel": {"resumeSince", "eventTopics"},
    "pause-until-finite": {"resumeSince", "eventTopics"},
    "pause-until-sentinel": {"resumeSince", "eventTopics"},
    "pause-for-when-paused": {"actionStatus", "actionReturndata", "actionEventTopics"},
    "pause-until-when-paused": {"actionStatus", "actionReturndata", "actionEventTopics"},
    "resume-authorized": {"resumeSince", "eventTopics"},
    "resume-when-resumed": {"actionStatus", "actionReturndata", "actionEventTopics"},
    "set-limit-valid": {"eventTopics"},
    "trigger-single-exact-fee": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS |
        ROUTER_EXPECTED_KEYS | {"refund"},
    "trigger-explicit-refund": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS |
        ROUTER_EXPECTED_KEYS | {"refundTarget", "refund"},
    "trigger-sender-refund": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS |
        ROUTER_EXPECTED_KEYS | {"refundTarget", "refund"},
    "trigger-multiple": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS |
        ROUTER_EXPECTED_KEYS | {"refund"},
    "trigger-fee-query-revert": FEE_EXPECTED_KEYS,
    "trigger-vault-revert": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS,
    "trigger-router-revert": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS |
        ROUTER_EXPECTED_KEYS,
    "trigger-refund-revert": FEE_EXPECTED_KEYS | VAULT_EXPECTED_KEYS |
        ROUTER_EXPECTED_KEYS | {"refundTarget", "refund"},
}

CASE_NAMES = (
    "constructor-success", "constructor-admin-zero", "constructor-max-too-large",
    "constructor-frame-too-large", "constructor-exits-above-max",
    "constructor-zero-frame", "constructor-dirty-admin", "constructor-nonpayable",
    "view-add-full-withdrawal-request-role", "view-default-admin-role",
    "view-pause-infinitely", "view-pause-role", "view-resume-role",
    "view-twr-limit-position", "view-tw-exit-limit-manager-role", "view-version",
    "view-supports-interface", "view-role-admin", "view-has-role",
    "view-is-paused-resumed", "view-resume-timestamp", "get-limit-same-frame",
    "grant-role-fresh", "grant-role-duplicate", "revoke-role-existing",
    "revoke-role-missing", "renounce-role-self", "renounce-role-wrong-account",
    "get-role-member", "get-role-member-count", "get-role-member-oob",
    "role-enumeration-cross-role-order", "role-flat-key-collision-refusal",
    "role-negative-grant", "role-negative-revoke", "role-negative-pause-for",
    "role-negative-pause-until", "role-negative-resume", "role-negative-set-limit",
    "role-negative-trigger", "pause-for-finite", "pause-for-sentinel",
    "pause-until-finite", "pause-until-sentinel", "pause-for-when-paused",
    "pause-until-when-paused", "view-is-paused-paused", "resume-authorized",
    "pause-zero-duration", "pause-until-past",
    "resume-when-resumed", "set-limit-valid", "set-limit-max-too-large",
    "set-limit-frame-too-large", "set-limit-exits-above-max", "set-limit-zero-frame",
    "trigger-empty", "trigger-single-exact-fee", "trigger-explicit-refund",
    "trigger-sender-refund", "trigger-multiple", "trigger-insufficient-fee",
    "trigger-limit-exceeded", "get-limit-refilled", "trigger-paused",
    "trigger-zero-value", "trigger-locator-revert", "trigger-fee-query-revert",
    "trigger-vault-revert", "trigger-router-revert", "trigger-refund-revert",
)

DEVIATION_ROWS = {
    "TWG-D01": (
        "role-negative-grant", "role-negative-revoke", "role-negative-pause-for",
        "role-negative-pause-until", "role-negative-resume",
        "role-negative-set-limit", "role-negative-trigger",
    ),
    "TWG-D02": ("renounce-role-wrong-account",),
    "TWG-D03": ("get-role-member-oob",),
    "TWG-D04": ("role-enumeration-cross-role-order",),
    "TWG-D05": ("role-flat-key-collision-refusal",),
}
DEVIATION_FIELDS = {
    "TWG-D01": ("returndata",),
    "TWG-D02": ("returndata",),
    "TWG-D03": ("returndata",),
    "TWG-D04": ("returndata", "logicalState"),
    "TWG-D05": ("status", "returndata", "logicalState", "logs"),
}

GAS_ROWS = (
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
)

RETAINED_NONPOSITIVE_GAS_CASES = {
    "view-is-paused-resumed", "view-is-paused-paused", "role-negative-pause-for",
}
CALLDATA_SCOPE_SUMMARY = (
    "canonical ABI endpoint rows plus named dirty-address constructor rejection; nested "
    "malformed dynamic ABI, empty/unknown/short dispatch, trailing calldata, and "
    "recognized-selector nonpayability are untested and excluded"
)
COVERAGE_SUMMARY = (
    "71 named rows cover 24/24 selectors, constructor, five reachable emitted event kinds "
    "plus RoleAdminChanged non-emission, pause sentinel/error-polarity arms, roles, "
    "configured-limit consumption/exceeded/whole-frame refill, and trigger mocks; "
    "zero/unlimited and partial-frame limit behavior plus the excluded dispatch/calldata "
    "arms are untested"
)
COVERAGE_CRITERION = (
    "71 named rows: every census selector plus constructor; both pause sentinel arms and "
    "both exact error polarities; seven role negatives; roles/enumeration; configured-limit "
    "validation/consume/exceeded/whole-frame refill; trigger fee/value/router/refund/ETH/events; "
    "excludes zero/unlimited and partial-frame limits, nested malformed dynamic ABI, "
    "empty/unknown/short dispatch, trailing calldata, and recognized-selector nonpayability"
)

SUMMARY_KEYS = {
    "B2_CALLDATA_SCOPE_SUMMARY", "B2_CODE_SIZE_HEADROOM_SUMMARY",
    "B2_CONSTRUCTOR_COVERAGE_SUMMARY", "B2_COVERAGE_SUMMARY",
    "B2_D01_ROW_SET", "B2_D01_SIZE_ATTRIBUTION",
    "B2_D02_RESOURCE_ATTRIBUTION", "B2_D02_ROW_SET",
    "B2_D03_RESOURCE_ATTRIBUTION", "B2_D03_ROW_SET",
    "B2_D04_EXPECTED_ORDERS", "B2_D04_ROW_SET",
    "B2_D05_PROJECTION_SHA256", "B2_D05_RESOURCE_ATTRIBUTION",
    "B2_D05_ROW_SET", "B2_DIFFERENTIAL_VERDICT",
    "B2_PER_SELECTOR_RESOURCE_COVERAGE_SUMMARY", "B2_PROJECTION_SCHEMA_SHA256",
}
PLACEHOLDER_TEMPLATE_DIGESTS = {
    "compatibility": "527ffa4fa5287d020064c254ea877792f5001a20bb091e136c7aeb26bc03150a",
    "deviations": "1e17fa747d0702be780cc42462e4382b9d6fe21232ad180b941a1a898c5833b3",
}

TOP_KEYS = {
    "schema", "contract", "oracle", "artifacts", "projection", "coverage",
    "counts", "rows", "resourceEvidence", "documentFill", "sectionDigests",
}
ROW_KEYS = {
    "ordinal", "name", "family", "selector", "tags", "channels", "deviation",
    "expectedMismatchFields", "semantic", "reference", "blanc", "semanticDigest",
}
EVIDENCE_KEYS = {
    "status", "returndataSha256", "logicalStateSha256", "auxiliaryStateSha256",
    "ethSha256", "logsSha256", "callTraceSha256", "gasUsed",
}
BOUNDARY_KEYS = {
    "ordinal", "coordinate", "case", "label", "referenceStatus", "blancStatus",
    "referenceGas", "blancGas", "delta",
}
HEX64 = re.compile(r"[0-9a-f]{64}")
HEX40 = re.compile(r"[0-9a-f]{40}")
STATUS = re.compile(r"(?:success|revert|exception:[A-Za-z][A-Za-z0-9_]*)")


class SchemaError(RuntimeError):
    pass


def fail(message: str) -> NoReturn:
    raise SchemaError(message)


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def strict_json(raw: bytes | str, label: str) -> Any:
    def pairs(items):
        result = {}
        for key, value in items:
            expect(key not in result, f"{label}: duplicate key {key!r}")
            result[key] = value
        return result

    def constant(value: str) -> None:
        fail(f"{label}: non-finite number {value}")

    try:
        return json.loads(raw, object_pairs_hook=pairs, parse_constant=constant)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f"{label}: invalid JSON: {exc}")


def compact(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def digest(value: Any) -> str:
    return hashlib.sha256(compact(value)).hexdigest()


def file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_int(value: Any, label: str, minimum: int = 0) -> int:
    expect(type(value) is int and value >= minimum, f"{label}: invalid integer")
    return value


def exact_sha(value: Any, label: str) -> str:
    expect(isinstance(value, str) and HEX64.fullmatch(value) is not None,
           f"{label}: invalid SHA-256")
    return value


def safe_string(value: Any, label: str) -> str:
    expect(isinstance(value, str) and value and "\n" not in value and "\r" not in value,
           f"{label}: expected nonempty single-line string")
    return value


def compatibility_contract() -> Mapping[str, Any]:
    raw = subprocess.check_output([sys.executable, str(COMPATIBILITY), "schema"], cwd=ROOT)
    value = strict_json(raw, "compatibility schema output")
    expect(isinstance(value, dict) and set(value) == {"documentFill"},
           "compatibility schema command changed shape")
    return value["documentFill"]


def validate_artifact(value: Any, label: str) -> None:
    expect(isinstance(value, dict) and set(value) == {"byteLength", "sha256"},
           f"{label}: artifact shape differs")
    exact_int(value["byteLength"], f"{label}.byteLength", 1)
    exact_sha(value["sha256"], f"{label}.sha256")


def validate_evidence(value: Any, label: str) -> None:
    expect(isinstance(value, dict) and set(value) == EVIDENCE_KEYS,
           f"{label}: evidence keys differ")
    statuses = value["status"]
    gas = value["gasUsed"]
    expect(isinstance(statuses, list) and isinstance(gas, list) and len(statuses) == len(gas),
           f"{label}: status/gas vector differs")
    for index, status in enumerate(statuses):
        expect(isinstance(status, str) and STATUS.fullmatch(status) is not None,
               f"{label}.status[{index}] invalid")
        exact_int(gas[index], f"{label}.gasUsed[{index}]")
    for key in EVIDENCE_KEYS - {"status", "gasUsed"}:
        exact_sha(value[key], f"{label}.{key}")


def expected_gas_disposition(row: Mapping) -> tuple[str, str]:
    case = str(row["coordinate"]).split("#", 1)[0]
    if case == "constructor-success":
        return (
            "Accepted deployment cost for explicit constructor validation, tagged role/limit "
            "initialization, and runtime code deposit; no deployment-gas improvement is claimed.",
            "deployment initialization and code-deposit boundary",
        )
    if case.startswith("trigger-"):
        return (
            "Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback "
            "choreography; the corpus pins effects and no aggregate gas advantage is claimed.",
            "trigger dependency/value/rollback boundary",
        )
    if case.startswith("set-limit-") or case.startswith("get-limit-"):
        return (
            "Accepted exit-limit cost for explicit five-field projection, validation, checked "
            "consumption, or whole-frame refill; the measured behavior is independently pinned.",
            "exit-limit projection and validation boundary",
        )
    if case.startswith("pause-") or case.startswith("resume-"):
        return (
            "Accepted pause-control cost for explicit authorization, sentinel/error-polarity "
            "checks, and tagged-state update or rollback; no gas improvement is claimed.",
            "pause/resume authorization and tagged-state boundary",
        )
    if (case.startswith("grant-role") or case.startswith("revoke-role") or
            case.startswith("renounce-role") or case.startswith("get-role-member") or
            case.startswith("role-")):
        return (
            "Accepted role-state cost for full-identity collision checks and global enumeration "
            "maintenance or scanning; TWG-D02–D05 separately delimit observable differences.",
            "full-identity role lookup/enumeration boundary",
        )
    return (
        "Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged "
        "representation; exact output semantics are pinned and no gas improvement is claimed.",
        "constant, interface, role, or pause-state read boundary",
    )


def validate_document_fill(fill: Any, manifest: Mapping, contract: Mapping) -> None:
    expect(isinstance(fill, dict) and set(fill) == set(contract),
           "documentFill top-level keys differ from compatibility contract")
    for key in ("schema", "referenceWorld", "referenceLockSha256", "censusSha256",
                "eelsCommit", "jauneCommit"):
        expect(fill[key] == contract[key], f"documentFill immutable {key} differs")
    expect(fill["templates"] == PLACEHOLDER_TEMPLATE_DIGESTS,
           "documentFill source-template digests differ")
    evidence = fill["evidence"]
    expect(isinstance(evidence, dict) and set(evidence) == {
        "artifactProgramCommit", "proofCertificateCommit", "artifacts", "counts",
        "gas", "summaries"},
        "documentFill evidence fields differ")
    expect(evidence["artifactProgramCommit"] == BLANC_ARTIFACT_COMMIT,
           "documentFill Blanc artifact-program commit differs")
    expect(evidence["proofCertificateCommit"] == BLANC_PROOF_COMMIT,
           "documentFill Blanc proof-certificate commit differs")
    expect(evidence["artifacts"] == {
        "creationTemplate": manifest["artifacts"]["blanc"]["creationTemplate"],
        "fullCreateInput": manifest["artifacts"]["blanc"]["fullCreateInput"],
        "runtime": manifest["artifacts"]["blanc"]["runtime"],
    }, "documentFill artifacts do not match manifest artifacts")
    expect(evidence["counts"] == {
        "cases": manifest["counts"]["rows"],
        "resourceBoundaries": manifest["counts"]["resourceBoundaries"],
    }, "documentFill counts do not match manifest")
    summaries = evidence["summaries"]
    expect(isinstance(summaries, dict) and set(summaries) == SUMMARY_KEYS,
           "documentFill summary inventory differs")
    for key, value in summaries.items():
        safe_string(value, f"documentFill summaries.{key}")
    expect(summaries["B2_DIFFERENTIAL_VERDICT"] == "PASS",
           "documentFill verdict is not PASS")
    expect(summaries["B2_CALLDATA_SCOPE_SUMMARY"] == CALLDATA_SCOPE_SUMMARY,
           "documentFill calldata scope is not the exact narrowed 71-row boundary")
    expect(summaries["B2_COVERAGE_SUMMARY"] == COVERAGE_SUMMARY,
           "documentFill coverage summary is not the exact narrowed 71-row boundary")
    expect(summaries["B2_PROJECTION_SCHEMA_SHA256"] == digest(manifest["projection"]) and
           summaries["B2_D05_PROJECTION_SHA256"] == digest(manifest["projection"]),
           "documentFill projection digest differs")
    gas = evidence["gas"]
    expect(isinstance(gas, dict) and set(gas) == {
        "boundaryDefinition", "rows", "positiveDeviations"},
        "documentFill gas keys differ")
    expect(gas["boundaryDefinition"] == manifest["resourceEvidence"]["boundaryDefinition"],
           "documentFill gas boundary definition differs")
    expect(gas["rows"] == manifest["resourceEvidence"]["namedGasRows"],
           "documentFill named gas rows differ")
    positives = [row for row in gas["rows"] if row["delta"] > 0]
    deviations = gas["positiveDeviations"]
    expect(isinstance(deviations, list) and len(deviations) == len(positives),
           "documentFill positive gas deviations are incomplete")
    for index, (item, row) in enumerate(zip(deviations, positives), 1):
        expect(isinstance(item, dict) and set(item) == {"id", "gasKey", "defense", "evidence"},
               f"positive gas deviation {index} shape differs")
        expect(item["id"] == f"TWG-G{index:02d}" and item["gasKey"] == row["gasKey"],
               f"positive gas deviation {index} identity differs")
        safe_string(item["defense"], f"positive gas deviation {index} defense")
        safe_string(item["evidence"], f"positive gas deviation {index} evidence")
        defense, review_group = expected_gas_disposition(row)
        expect(item["defense"] == defense and item["evidence"] ==
               f"manifest resource coordinate {row['coordinate']}; {review_group}",
               f"positive gas deviation {index} lacks the exact substantive cost disposition")

    boundaries = manifest["resourceEvidence"]["boundaries"]
    public_names = [row["name"] for row in manifest["rows"] if row["family"] != "constructor"]
    expect(len(public_names) == 63 and len(set(public_names)) == 63,
           "public case inventory must contain exactly 63 unique non-constructor rows")
    final_actions = []
    for name in public_names:
        candidates = [row for row in boundaries
                      if row["case"] == name and row["label"] == "action"]
        expect(len(candidates) == 1,
               f"public case {name} must own exactly one final action boundary")
        final_actions.append(candidates[0])
    positive_coordinates = {
        row["coordinate"] for row in final_actions if row["delta"] > 0
    }
    expect(len(positive_coordinates) == 47,
           "positive public final-action inventory must contain exactly 47 rows")
    constructor = [row for row in boundaries
                   if row["case"] == "constructor-success" and row["label"] == "constructor"]
    expect(len(constructor) == 1 and constructor[0]["delta"] > 0,
           "successful constructor positive-cost boundary differs")
    positive_coordinates.add(constructor[0]["coordinate"])
    named_positive_coordinates = {
        row["coordinate"] for row in gas["rows"] if row["delta"] > 0
    }
    expect(named_positive_coordinates == positive_coordinates and
           len(named_positive_coordinates) == 48,
           "named gas rows must cover all 47 positive public actions plus constructor")
    retained_nonpositive = {
        row["coordinate"].split("#", 1)[0]
        for row in gas["rows"] if row["delta"] <= 0
    }
    expect(retained_nonpositive == RETAINED_NONPOSITIVE_GAS_CASES and
           len(gas["rows"]) == 51,
           "named gas rows must retain exactly three negative controls for 51 total rows")


def validate_manifest(manifest: Any) -> None:
    expect(isinstance(manifest, dict) and set(manifest) == TOP_KEYS,
           "manifest top-level keys differ")
    expect(manifest["schema"] == 1 and manifest["contract"] == "TriggerableWithdrawalsGateway",
           "manifest schema/contract differs")
    oracle = manifest["oracle"]
    expect(oracle == {
        "engine": "ethereum/execution-specs", "fork": "Prague",
        "eelsCommit": EELS_PIN, "jauneCommit": JAUNE_PIN,
        "referenceLockSha256": file_sha(LOCK), "censusSha256": file_sha(CENSUS),
        "referenceWorld": "differential-corpus",
        "deployment": "fresh state; each side executes its complete CREATE input",
    }, "oracle identity differs")

    lock = strict_json(LOCK.read_bytes(), "reference lock")
    artifacts = manifest["artifacts"]
    expect(isinstance(artifacts, dict) and set(artifacts) == {
        "reference", "blanc", "proof", "positiveIdentityChecks"}, "artifact keys differ")
    reference = artifacts["reference"]
    blanc = artifacts["blanc"]
    expect(isinstance(reference, dict) and set(reference) == {
        "creationTemplate", "runtimeTemplate", "fullCreateInput", "runtime"},
        "reference artifact inventory differs")
    expect(isinstance(blanc, dict) and set(blanc) == {
        "creationTemplate", "fullCreateInput", "runtime", "locatorOffsets",
        "patchControlsValid"}, "Blanc artifact inventory differs")
    for key in ("creationTemplate", "runtimeTemplate", "fullCreateInput", "runtime"):
        validate_artifact(reference[key], f"reference.{key}")
    for key in ("creationTemplate", "fullCreateInput", "runtime"):
        validate_artifact(blanc[key], f"blanc.{key}")
    world = next(item for item in lock["artifacts"]["worlds"] if item["name"] == "differential-corpus")
    expect(reference == {
        "creationTemplate": {key: lock["artifacts"]["creationTemplate"][key]
                             for key in ("byteLength", "sha256")},
        "runtimeTemplate": {key: lock["artifacts"]["runtimeTemplate"][key]
                            for key in ("byteLength", "sha256")},
        "fullCreateInput": {key: world["fullCreateInput"][key]
                            for key in ("byteLength", "sha256")},
        "runtime": {key: world["returnedRuntime"][key]
                    for key in ("byteLength", "sha256")},
    }, "reference artifacts differ from B1 lock")
    expect(blanc["patchControlsValid"] is True and isinstance(blanc["locatorOffsets"], list)
           and blanc["locatorOffsets"] and all(type(item) is int and item >= 0
                                                for item in blanc["locatorOffsets"]),
           "Blanc locator patch controls invalid")
    expect(blanc["runtime"]["byteLength"] <= 24_576 and
           blanc["fullCreateInput"]["byteLength"] <= 49_152,
           "Blanc artifacts exceed EIP limits")
    expect(artifacts["positiveIdentityChecks"] == 10,
           "positive artifact identity check count differs")
    expect(artifacts["proof"] == {
        "artifactProgramCommit": BLANC_ARTIFACT_COMMIT,
        "proofCertificateCommit": BLANC_PROOF_COMMIT,
        "certificate": "first compile-valid pinned-target certificate",
    }, "Blanc proof/program identity split differs")
    expect(subprocess.run(
        ["git", "merge-base", "--is-ancestor", BLANC_ARTIFACT_COMMIT, BLANC_PROOF_COMMIT],
        cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0,
        "Blanc artifact program is not an ancestor of the proof certificate")
    expect(subprocess.run(
        ["git", "merge-base", "--is-ancestor", BLANC_PROOF_COMMIT, "HEAD"],
        cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0,
        "Blanc proof certificate is not an ancestor of the candidate")

    projection = manifest["projection"]
    expect(isinstance(projection, dict) and set(projection) == {
        "schema", "boundary", "solidity", "blanc", "nonclaim"},
        "projection schema keys differ")
    expect(projection["schema"] == 1 and projection["boundary"] == [
        "resumeSince", "exit-limit-five-field-record",
        "per-role-admin-membership-count-and-ordered-members",
        "selected-account-ETH", "selected-mock-storage"],
        "projection boundary differs")
    expect(projection["blanc"].get("formula") ==
           "bitwise-or(region-times-two-pow-252,payload)",
           "Blanc projection formula differs")

    census = strict_json(CENSUS.read_bytes(), "census")
    rows = manifest["rows"]
    expect(isinstance(rows, list) and tuple(row.get("name") for row in rows) == CASE_NAMES,
           "exact ordered case inventory differs")
    by_name = {row["name"]: row for row in rows}
    for index, row in enumerate(rows):
        expect(isinstance(row, dict) and set(row) == ROW_KEYS and row["ordinal"] == index,
               f"row {index} shape/ordinal differs")
        expect(isinstance(row["family"], str) and isinstance(row["tags"], list)
               and row["tags"] and len(row["tags"]) == len(set(row["tags"])),
               f"row {index} tags/family invalid")
        expect(row["channels"] and all(channel in {
            "status", "returndata", "state-projection", "eth", "logs", "call-trace"
        } for channel in row["channels"]), f"row {index} channels invalid")
        deviation = row["deviation"]
        expected_fields = list(DEVIATION_FIELDS.get(deviation, ()))
        expect(row["expectedMismatchFields"] == expected_fields,
               f"row {index} deviation fields differ")
        if deviation is None:
            expect(row["name"] not in {name for names in DEVIATION_ROWS.values() for name in names},
                   f"row {index} omitted required deviation")
        else:
            expect(row["name"] in DEVIATION_ROWS.get(deviation, ()),
                   f"row {index} deviation identity differs")
        semantic = row["semantic"]
        expect(isinstance(semantic, dict) and set(semantic) == {"assertions", "expected"}
               and semantic["assertions"] == row["tags"] and isinstance(semantic["expected"], dict),
               f"row {index} semantic descriptor differs")
        expected = semantic["expected"]
        expect(set(expected) == EXPECTED_KEYS.get(row["name"], set()),
               f"row {index} semantic expected-key contract differs")
        if row["family"] == "constructor":
            wanted_status = "success" if row["name"] == "constructor-success" else "revert"
            expect(expected.get("constructorStatus") == wanted_status,
                   f"row {index} constructor outcome semantic differs")
            if row["name"] != "constructor-success":
                expect(expected.get("constructorReturndata") ==
                       CONSTRUCTOR_RETURNDATA[row["name"]],
                       f"row {index} constructor returndata semantic differs")
        expect(("eventTopics" in expected) == (row["name"] in EVENT_EXPECTATIONS),
               f"row {index} event semantic inventory differs")
        if row["name"] in EVENT_EXPECTATIONS:
            expect(expected.get("eventTopics") == EVENT_EXPECTATIONS[row["name"]],
                   f"row {index} exact event topics/order semantic differs")
        if row["name"] == "view-role-admin":
            expect(expected.get("eventNonemissionTopic") == EVENT_TOPICS["RoleAdminChanged"],
                   "RoleAdminChanged non-emission identity differs")
        if row["name"] == "trigger-fee-query-revert":
            expect(expected.get("feeQueryCalls") == 1
                   and expected.get("feeQuerySelector") == FEE_SELECTOR
                   and expected.get("feeQueryCallSuccess") == "0x0",
                   "fee-query failure semantic evidence differs")
        if row["name"] in TRIGGER_CALL_EXPECTATIONS:
            fee_success, vault_success, router_success, vault_value = \
                TRIGGER_CALL_EXPECTATIONS[row["name"]]
            expect(expected.get("feeQueryCalls") == 1
                   and expected.get("feeQuerySelector") == FEE_SELECTOR
                   and expected.get("feeQueryCallSuccess") == fee_success
                   and expected.get("vaultCalls") == 1
                   and expected.get("vaultSelector") == VAULT_SELECTOR
                   and expected.get("vaultCallSuccess") == vault_success
                   and expected.get("vaultValue") == vault_value,
                   f"row {index} fee/vault call semantic evidence differs")
            if router_success is None:
                expect("routerCalls" not in expected,
                       f"row {index} unexpectedly claims a router call")
            else:
                expect(expected.get("routerCalls") == 1
                       and expected.get("routerSelector") == ROUTER_SELECTOR
                       and expected.get("routerCallSuccess") == router_success,
                       f"row {index} router call semantic evidence differs")
        refund_expectations = {
            "trigger-single-exact-fee": (None, 0),
            "trigger-explicit-refund": (REFUND, 3),
            "trigger-sender-refund": (ACTOR, 3),
            "trigger-multiple": (None, 0),
            "trigger-refund-revert": (REJECTOR, 3),
        }
        if row["name"] in refund_expectations:
            target, amount = refund_expectations[row["name"]]
            expect(expected.get("refund") == amount
                   and (target is None or expected.get("refundTarget") == target),
                   f"row {index} refund semantic evidence differs")
        if row["name"] in {
                "trigger-single-exact-fee", "trigger-explicit-refund",
                "trigger-sender-refund", "trigger-refund-revert"}:
            expect("trigger.balance-preserved" in row["tags"],
                   f"row {index} zero gateway-balance semantic tag differs")
        if row["name"] in TRIGGER_CALL_EXPECTATIONS:
            expect("trigger.fee" in row["tags"],
                   f"row {index} fee-path semantic tag differs")
            if TRIGGER_CALL_EXPECTATIONS[row["name"]][2] is not None:
                expect("trigger.router" in row["tags"],
                       f"row {index} router semantic tag differs")
        if row["name"] in EVENT_TAG_EXPECTATIONS:
            expect(EVENT_TAG_EXPECTATIONS[row["name"]] in row["tags"],
                   f"row {index} event evidence tag differs")
        action_errors = {
            "pause-for-when-paused": ("0x14378398", "errors.ResumedExpected"),
            "pause-until-when-paused": ("0x14378398", "errors.ResumedExpected"),
            "resume-when-resumed": ("0xb047186b", "errors.PausedExpected"),
        }
        if row["name"] in action_errors:
            payload, tag = action_errors[row["name"]]
            expect(expected.get("actionStatus") == "revert"
                   and expected.get("actionReturndata") == payload
                   and expected.get("actionEventTopics") == []
                   and tag in row["tags"] and "rollback" in row["tags"],
                   f"row {index} pause-polarity error semantic differs")
        validate_evidence(row["reference"], f"row {index} reference")
        validate_evidence(row["blanc"], f"row {index} blanc")
        evidence_fields = {
            "status": "status", "returndata": "returndataSha256",
            "logicalState": "logicalStateSha256",
            "auxiliaryState": "auxiliaryStateSha256", "eth": "ethSha256",
            "logs": "logsSha256", "callTrace": "callTraceSha256",
        }
        channel_fields = {
            "status": ("status",), "returndata": ("returndata",),
            "state-projection": ("logicalState", "auxiliaryState"),
            "eth": ("eth",), "logs": ("logs",),
            "call-trace": ("callTrace",),
        }
        compared = [field for channel in row["channels"]
                    for field in channel_fields[channel]]
        actual_mismatches = {
            field for field in compared
            if row["reference"][evidence_fields[field]] !=
               row["blanc"][evidence_fields[field]]
        }
        expect(actual_mismatches == set(expected_fields),
               f"row {index} actual channel mismatches differ: {sorted(actual_mismatches)}")
        exact_sha(row["semanticDigest"], f"row {index} semanticDigest")
        expect(row["semanticDigest"] == digest({
            "assertions": row["tags"], "expected": semantic["expected"],
            "reference": row["reference"], "blanc": row["blanc"],
        }), f"row {index} semantic digest differs")
    for deviation, names in DEVIATION_ROWS.items():
        expect(tuple(row["name"] for row in rows if row["deviation"] == deviation) == names,
               f"{deviation} row set differs")
    expect(by_name["pause-for-sentinel"]["semantic"]["expected"]["resumeSince"] ==
           (1 << 256) - 1, "pauseFor sentinel semantic pin differs")
    expect(by_name["pause-until-sentinel"]["semantic"]["expected"]["resumeSince"] ==
           (1 << 256) - 1, "pauseUntil sentinel semantic pin differs")
    expect(by_name["pause-for-finite"]["semantic"]["expected"]["resumeSince"] ==
           1_700_000_010, "pauseFor finite semantic pin differs")
    expect(by_name["pause-until-finite"]["semantic"]["expected"]["resumeSince"] ==
           1_700_000_011, "pauseUntil finite semantic pin differs")
    expect(by_name["resume-authorized"]["semantic"]["expected"]["resumeSince"] ==
           1_700_000_001, "resume semantic pin differs")

    coverage = manifest["coverage"]
    expect(isinstance(coverage, dict) and set(coverage) == {
        "criterion", "selectorCount", "selectors", "requiredTags", "deviations"},
        "coverage keys differ")
    expect(coverage["selectorCount"] == 24 and coverage["selectorCount"] == len(census["selectors"]),
           "selector coverage count differs")
    expect(coverage["criterion"] == COVERAGE_CRITERION,
           "coverage criterion is not the exact narrowed 71-row boundary")
    expected_selectors = []
    for census_row in census["selectors"]:
        names = [row["name"] for row in rows if row["selector"] == census_row["signature"]]
        expect(names, f"selector {census_row['signature']} has no action row")
        expected_selectors.append({"signature": census_row["signature"],
                                   "selector": census_row["selector"], "rows": names})
    expect(coverage["selectors"] == expected_selectors,
           "selector coverage mapping differs")
    union_tags = sorted({tag for row in rows for tag in row["tags"]})
    expect(coverage["requiredTags"] == union_tags,
           "required tag inventory differs")
    for required in (
        "sentinel.pauseFor", "sentinel.pauseUntil", "roles.negative",
        "errors.PausedExpected", "errors.ResumedExpected",
        "limit.configure", "limit.consume", "limit.exceeded", "limit.frame-refill",
        "trigger.fee", "trigger.value-forward", "trigger.router",
        "trigger.refund-explicit", "trigger.refund-zero-to-sender",
        "trigger.balance-preserved", "events.RoleGranted", "events.RoleRevoked",
        "events.Paused", "events.Resumed", "events.ExitRequestsLimitSet",
        "events.RoleAdminChanged-nonemission",
        "deviation.TWG-D01", "deviation.TWG-D02", "deviation.TWG-D03",
        "deviation.TWG-D04", "deviation.TWG-D05",
    ):
        expect(required in union_tags, f"required semantic tag {required} missing")
    expect(coverage["deviations"] == [
        {"id": key, "fields": list(DEVIATION_FIELDS[key]), "rows": list(DEVIATION_ROWS[key])}
        for key in DEVIATION_FIELDS], "coverage deviation registry differs")

    counts = manifest["counts"]
    expect(isinstance(counts, dict) and set(counts) == {
        "rows", "agreementRows", "deviationRows", "selectorCount",
        "constructorRows", "resourceBoundaries", "callTraceEntries"},
        "count keys differ")
    expect(counts["rows"] == len(CASE_NAMES) and counts["agreementRows"] == 60
           and counts["deviationRows"] == 11 and counts["selectorCount"] == 24
           and counts["constructorRows"] == 8,
           "fixed case counts differ")
    exact_int(counts["callTraceEntries"], "callTraceEntries")

    resource = manifest["resourceEvidence"]
    expect(isinstance(resource, dict) and set(resource) == {
        "boundaryDefinition", "boundaries", "namedGasRows", "vectorSha256"},
        "resource evidence keys differ")
    safe_string(resource["boundaryDefinition"], "resource boundary definition")
    boundaries = resource["boundaries"]
    expect(isinstance(boundaries, list) and len(boundaries) == counts["resourceBoundaries"],
           "resource boundary count differs")
    for index, boundary in enumerate(boundaries):
        expect(isinstance(boundary, dict) and set(boundary) == BOUNDARY_KEYS
               and boundary["ordinal"] == index,
               f"resource boundary {index} shape/ordinal differs")
        expect(boundary["coordinate"] == f"{boundary['case']}#{sum(1 for prior in boundaries[:index] if prior['case'] == boundary['case'])}:{boundary['label']}",
               f"resource boundary {index} coordinate differs")
        expect(boundary["case"] in by_name, f"resource boundary {index} unknown case")
        for key in ("referenceStatus", "blancStatus"):
            expect(isinstance(boundary[key], str) and STATUS.fullmatch(boundary[key]),
                   f"resource boundary {index} status invalid")
        for key in ("referenceGas", "blancGas"):
            exact_int(boundary[key], f"resource boundary {index}.{key}")
        expect(boundary["delta"] == boundary["blancGas"] - boundary["referenceGas"],
               f"resource boundary {index} delta differs")
    expect(resource["vectorSha256"] == digest(boundaries),
           "resource vector digest differs")
    expected_boundary_count = sum(
        (1 if row["family"] == "constructor" else 1 + len(row["reference"]["gasUsed"]))
        for row in rows)
    expect(counts["resourceBoundaries"] == expected_boundary_count,
           "resource boundaries do not reconcile with case evidence")
    named = resource["namedGasRows"]
    expect(isinstance(named, list) and len(named) == len(GAS_ROWS),
           "named gas row count differs")
    for index, (row, (key, path)) in enumerate(zip(named, GAS_ROWS)):
        expect(isinstance(row, dict) and set(row) == {
            "gasKey", "path", "coordinate", "reference", "blanc", "delta"},
            f"named gas row {index} shape differs")
        expect((row["gasKey"], row["path"]) == (key, path),
               f"named gas row {index} identity differs")
        matches = [item for item in boundaries if item["coordinate"] == row["coordinate"]]
        expect(len(matches) == 1 and row["reference"] == matches[0]["referenceGas"]
               and row["blanc"] == matches[0]["blancGas"]
               and row["delta"] == row["blanc"] - row["reference"],
               f"named gas row {index} does not bind its resource coordinate")

    validate_document_fill(manifest["documentFill"], manifest, compatibility_contract())
    section_digests = manifest["sectionDigests"]
    section_names = (
        "oracle", "artifacts", "projection", "coverage", "counts", "rows",
        "resourceEvidence", "documentFill")
    expect(isinstance(section_digests, dict) and set(section_digests) == set(section_names),
           "section digest inventory differs")
    for key in section_names:
        expect(section_digests[key] == digest(manifest[key]),
               f"section digest {key} differs")


def main(argv: Sequence[str]) -> int:
    path = Path(argv[0]) if argv else DEFAULT_MANIFEST
    raw = path.read_bytes()
    expect(raw.endswith(b"\n") and b"\r" not in raw and b"\0" not in raw,
           "manifest bytes are not canonical UTF-8 newline form")
    manifest = strict_json(raw, "TWG differential manifest")
    validate_manifest(manifest)
    print("OK — Lido TWG differential schema")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except Exception as exc:
        print("REGRESSION — Lido TWG differential schema: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
