#!/usr/bin/env python3
"""Strict offline schemas for the OssifiableProxy differential campaign.

This module owns the frozen-manifest checks, symbolic fixture resolution, and
the immutable result envelope.  It deliberately has no EELS imports so its
entire negative surface can be mutation-tested without executing either
contract.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, NoReturn, Sequence


MANIFEST_FORMAT = "blanc.lido-ossifiable-proxy.differential-campaign"
MANIFEST_DIGEST = "538e9dd3c6f2e1c52a4dd559f6b48dd9f0d75eb478b11a7299170ecde904e7ab"
PERFORMANCE_FORMAT = "blanc.lido-ossifiable-proxy.performance-campaign"
PERFORMANCE_DIGEST = "d257394b6eb56b02072b68037896a863e96a42f405690423024bc6b432f34eaa"
REFERENCE_LOCK_SHA256 = "1c9f380f2475e5a54eb870e4f41ceeb09a0f9c227271ad14900fe82b0df1b688"
EELS_COMMIT = "4198b9c5996713b268aed602739d5aa40e277694"
RESULT_FORMAT = "blanc.lido-ossifiable-proxy.differential-result/v1"
CASE_COUNT = 85

MANIFEST_RELATIVE = Path("scripts/fixtures/lido-ossifiable-proxy/differential-manifest.json")
PERFORMANCE_RELATIVE = Path("scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json")
REFERENCE_RELATIVE = Path("scripts/lido-ossifiable-proxy-reference.json")
EVALUATOR_RELATIVE = Path("scripts/eval-lido-ossifiable-proxy-artifacts.lean")
RUNNER_RELATIVE = Path("scripts/run-lido-ossifiable-proxy-differential.py")
SCHEMA_RELATIVE = Path("scripts/lido_ossifiable_proxy_differential_schema.py")
LAUNCHER_RELATIVE = Path("scripts/check-lido-ossifiable-proxy-differential.sh")

EXPECTED_CASE_IDS = tuple(
    [f"K{i:02d}" for i in range(1, 19)]
    + [f"G{i:02d}" for i in range(1, 8)]
    + [f"O{i:02d}" for i in range(1, 4)]
    + [f"D{i:02d}" for i in range(1, 7)]
    + [f"U{i:02d}" for i in range(1, 8)]
    + [f"X{i:02d}" for i in range(1, 21)]
    + [f"F{i:02d}" for i in range(0, 17)]
    + [f"V{i:02d}" for i in range(1, 8)]
)

PROJECTION_CHANNELS = (
    "status", "returndata", "storage", "eth", "logs", "delegatecalls",
    "targetAccount",
)
EXPECTED_CASE_PROJECTION_KEYS = frozenset((*PROJECTION_CHANNELS, "rolledBackEffects"))
FALSIFIER_FAMILIES = frozenset({
    "reference-substitution", "selector-routing", "event-error-bytes",
    "state-projection", "rollback", "child-call-observation",
    "corpus-result-mutation",
})

SELECTORS = {
    "proxy__getAdmin()": "916f1fd7",
    "proxy__getImplementation()": "ad729a71",
    "proxy__getIsOssified()": "13351258",
    "proxy__ossify()": "adcbc237",
    "proxy__changeAdmin(address)": "773f5be8",
    "proxy__upgradeTo(address)": "3ebdd0eb",
    "proxy__upgradeToAndCall(address,bytes,bool)": "d2f6ed4d",
}

EXPECTED_EVENT_TOPICS = {
    "admin": "0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f",
    "ossified": "0x158b204828f9326d9bb3c2be9336986c14911b4a72b93d1801f207aac3c68b9f",
    "upgraded": "0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b",
    "fixture": "0x" + "aa" * 32,
}
EXPECTED_ERROR_SHA256 = {
    "NotAdmin": "ac92a971c4828f995041749977d7d057bbbd1c3174d667d01ec294313e2bd6af",
    "ProxyIsOssified": "d30f42d8327a91798a5ab12d2dac1bdd5b931e2dd11c6ba30fe92a2deaa0c33f",
    "low-level-delegate-call": "48da7bfa4e4e712bda72586b558153f64d353d661b99b24e57cfae30c3fb2b63",
    "no-code-implementation": "4052fe21e8a75f614fcd3141192048caa1281048577f9ddcc6a1d940b60ec028",
    "zero-admin": "719f8d1895b691e7eb1c7afd7ba663d553a3113b422c49b721e988ead02f8620",
    "Panic-0x41": "b63ea3d4907b780ee7bc15204003100a355d341f3727840a25471ed52f74ec48",
}
EXPECTED_REFERENCE_ARTIFACTS = {
    "creationTemplate": (4207, "9bfe890b362037666f6087ad13d90a36d62cf3a208609fa3b5d9e04797d04ac4"),
    "runtime": (2497, "6490ced9ee4f0d8815f8c24a7d40acb40cb27cd7ef0fdab57289406d7ef96abc"),
}
EXPECTED_DELEGATECALL_PROJECTIONS_SHA256 = \
    "b30f2e42bbcd7e9334c307198dc2309a115b958e61129f2834c10ff08a7c4649"

DELEGATECALL_CASE_IDS = frozenset({
    "K02", "K03", "K04", "K05", "K09", "K10", "K11", "K12",
    "X02", "X03", "X04", "X05", "X06", "X07", "X08", "X09",
    "X10", "X14", "X19",
    *[f"F{i:02d}" for i in range(0, 17)],
})
ROLLBACK_CASE_IDS = frozenset({
    "K07", "K09", "K10", "K11", "K12", "U03", "X07", "X08",
    "X09", "X10", "F09", "F10", "F11", "F12", "F15", "F16",
})

_HEX64 = re.compile(r"^[0-9a-f]{64}$")
_HEX40 = re.compile(r"^[0-9a-f]{40}$")
_EXCEPTION_STATUS = re.compile(r"^exception:[A-Za-z][A-Za-z0-9]*$")


class ValidationError(RuntimeError):
    """A deterministic schema or identity failure."""


def reject(message: str) -> NoReturn:
    raise ValidationError(message)


def load_json(path: Path) -> Dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        reject(f"cannot load JSON {path}: {exc}")
    if not isinstance(value, dict):
        reject(f"JSON root at {path} must be an object")
    return value


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    try:
        return sha256_bytes(path.read_bytes())
    except OSError as exc:
        reject(f"cannot hash {path}: {exc}")


def canonical_bytes(document: Mapping[str, Any]) -> bytes:
    return json.dumps(
        document, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")


def campaign_digest(document: Mapping[str, Any]) -> str:
    candidate = copy.deepcopy(document)
    try:
        candidate["campaign"]["digest"]["value"] = ""
    except (KeyError, TypeError):
        reject("manifest campaign digest envelope is missing")
    return sha256_bytes(canonical_bytes(candidate))


def seal_campaign_for_test(document: Dict[str, Any]) -> None:
    """Re-seal a mutated in-memory manifest for semantic falsifier tests."""
    document["campaign"]["digest"]["value"] = ""
    document["campaign"]["digest"]["value"] = campaign_digest(document)


def result_digest(document: Mapping[str, Any]) -> str:
    candidate = copy.deepcopy(document)
    try:
        candidate["identity"]["resultDigest"]["value"] = ""
    except (KeyError, TypeError):
        reject("result digest envelope is missing")
    return sha256_bytes(canonical_bytes(candidate))


def seal_result(document: Dict[str, Any]) -> str:
    document["identity"]["resultDigest"]["value"] = ""
    digest = result_digest(document)
    document["identity"]["resultDigest"]["value"] = digest
    return digest


def _exact_keys(value: Mapping[str, Any], expected: Iterable[str], owner: str) -> None:
    actual, wanted = set(value), set(expected)
    if actual != wanted:
        reject(f"{owner} keys drifted: missing={sorted(wanted-actual)}, extra={sorted(actual-wanted)}")


def _hex_bytes(value: Any, owner: str) -> bytes:
    if not isinstance(value, str) or not value.startswith("0x") or len(value) % 2:
        reject(f"{owner} must be even-length 0x hex")
    try:
        return bytes.fromhex(value[2:])
    except ValueError:
        reject(f"{owner} is not hex")


def validate_blob(blob: Mapping[str, Any], owner: str) -> bytes:
    required = {"byteLength", "description", "hex", "sha256"}
    if not required.issubset(blob):
        reject(f"{owner} blob fields are incomplete")
    raw = _hex_bytes(blob["hex"], owner)
    if blob["byteLength"] != len(raw):
        reject(f"{owner} byte length drifted")
    if blob["sha256"] != sha256_bytes(raw):
        reject(f"{owner} SHA-256 drifted")
    return raw


def pointer_get(document: Any, pointer: str, owner: str) -> Any:
    if not pointer.startswith("/"):
        reject(f"{owner} binding is not an absolute JSON pointer: {pointer}")
    value = document
    for encoded in pointer[1:].split("/"):
        token = encoded.replace("~1", "/").replace("~0", "~")
        if isinstance(value, Mapping) and token in value:
            value = value[token]
        elif isinstance(value, list) and token.isdigit() and int(token) < len(value):
            value = value[int(token)]
        else:
            reject(f"{owner} pointer does not resolve: {pointer}")
    return value


def resolve_reference(
    manifest: Mapping[str, Any], performance: Mapping[str, Any], value: Any,
    *, _seen: frozenset[str] = frozenset(),
) -> Any:
    if not isinstance(value, str) or not value.startswith(("performance:", "differential:")):
        return value
    if value in _seen:
        reject(f"cyclic symbolic fixture reference: {value}")
    if value.startswith("performance:"):
        bindings = manifest["sharedPerformanceManifest"]["sharedReferenceBindings"]
        source = performance
    else:
        bindings = manifest["fixtures"]["localReferenceBindings"]
        source = manifest
    pointer = bindings.get(value)
    if not isinstance(pointer, str):
        reject(f"unbound symbolic fixture reference: {value}")
    resolved = pointer_get(source, pointer, value)
    return resolve_reference(manifest, performance, resolved, _seen=_seen | {value})


def resolve_tree(manifest: Mapping[str, Any], performance: Mapping[str, Any], value: Any) -> Any:
    if isinstance(value, str):
        resolved = resolve_reference(manifest, performance, value)
        return resolve_tree(manifest, performance, resolved) if resolved is not value else value
    if isinstance(value, list):
        return [resolve_tree(manifest, performance, item) for item in value]
    if isinstance(value, Mapping):
        return {key: resolve_tree(manifest, performance, item) for key, item in value.items()}
    return value


def _canonical_address(value: Any, owner: str) -> str:
    raw = _hex_bytes(value, owner)
    if len(raw) != 20:
        reject(f"{owner} must be exactly 20 bytes")
    return "0x" + raw.hex()


def _word_hex(value: Any, owner: str) -> str:
    if isinstance(value, int):
        number = value
    elif isinstance(value, str) and value.isdigit():
        number = int(value)
    elif isinstance(value, str) and value.startswith("0x"):
        raw = _hex_bytes(value, owner)
        if len(raw) == 20:
            raw = bytes(12) + raw
        if len(raw) != 32:
            reject(f"{owner} cannot be normalized to one word")
        return "0x" + raw.hex()
    else:
        reject(f"{owner} is not a word/address/integer")
    if number < 0 or number >= 1 << 256:
        reject(f"{owner} integer is outside uint256")
    return "0x" + number.to_bytes(32, "big").hex()


def _fixture_addresses(
    manifest: Mapping[str, Any], performance: Mapping[str, Any]
) -> tuple[str, ...]:
    values: set[str] = set()

    def visit(value: Any) -> None:
        if isinstance(value, str) and re.fullmatch(r"0x[0-9a-fA-F]{40}", value):
            values.add(_canonical_address(value, "manifest-declared address"))
        elif isinstance(value, Mapping):
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(performance)
    visit(manifest)
    if not values:
        reject("campaign has no observed fixture addresses")
    return tuple(sorted(values))


def _proxy_state_slots(
    manifest: Mapping[str, Any], performance: Mapping[str, Any], value: Any
) -> Dict[str, str]:
    if isinstance(value, str):
        value = resolve_reference(manifest, performance, value)
    if not isinstance(value, Mapping):
        reject("proxy state did not resolve to an object")
    slots_by_name = manifest["fixtures"]["slots"]
    if "base" in value:
        slots = _proxy_state_slots(manifest, performance, value["base"])
    else:
        default = _word_hex(value.get("storageDefault", "0x" + "00" * 32), "storage default")
        slots = {slot: default for slot in slots_by_name.values()}
    for slot, raw in value.get("storageOverrides", {}).items():
        if slot in slots:
            slots[slot] = _word_hex(raw, f"storage override {slot}")
    return slots


def materialize_expected_projection(
    manifest: Mapping[str, Any], performance: Mapping[str, Any], case: Mapping[str, Any]
) -> Dict[str, Any]:
    """Resolve one frozen expected row into the exact result representation."""
    zero = "0x" + "00" * 32
    slots_by_name = manifest["fixtures"]["slots"]
    if case["world"]["kind"] == "direct-create-message":
        pre_storage = {
            "targetExists": False,
            "slots": {slot: zero for slot in slots_by_name.values()},
        }
    else:
        pre_storage = {
            "targetExists": True,
            "slots": _proxy_state_slots(
                manifest, performance, case["world"]["proxyState"]
            ),
        }

    storage_spec = case["expected"]["storage"]
    if storage_spec == "exact-prestate":
        storage = copy.deepcopy(pre_storage)
    elif storage_spec == "target-absent":
        storage = {
            "targetExists": False,
            "slots": {slot: zero for slot in slots_by_name.values()},
        }
    elif isinstance(storage_spec, Mapping):
        if "base" in storage_spec:
            slots = _proxy_state_slots(manifest, performance, storage_spec["base"])
        else:
            slots = {slot: zero for slot in slots_by_name.values()}
        for logical_name, fixture_name in (
            ("admin", "admin"),
            ("implementation", "implementation"),
            ("fixtureSlot", "fixture"),
        ):
            if logical_name in storage_spec:
                slots[slots_by_name[fixture_name]] = _word_hex(
                    resolve_reference(manifest, performance, storage_spec[logical_name]),
                    f"{case['id']} {logical_name}",
                )
        if storage_spec.get("allOtherStorage") not in (None, "differential:word:zero"):
            reject(f"{case['id']} allOtherStorage contract drifted")
        storage = {"targetExists": True, "slots": slots}
    else:
        reject(f"{case['id']} has unsupported storage expectation")

    addresses = _fixture_addresses(manifest, performance)
    eth = {address: "0" for address in addresses}
    eth_spec = case["expected"]["eth"]
    if eth_spec != "exact-prestate":
        wanted = (
            "forwarding-caller decreases by receive-value; "
            "proxy-target increases by receive-value"
        )
        if eth_spec != wanted:
            reject(f"{case['id']} has unsupported ETH expectation")
        caller = _canonical_address(
            resolve_reference(manifest, performance, "performance:forwarding-caller"),
            "forwarding caller",
        )
        target = _canonical_address(
            resolve_reference(manifest, performance, "performance:proxy-target"),
            "proxy target",
        )
        amount = int(resolve_reference(manifest, performance, "performance:receive-value"))
        eth[caller], eth[target] = str(-amount), str(amount)

    delegatecalls = []
    for declared in case["expected"]["delegatecalls"]:
        row = resolve_tree(manifest, performance, declared)
        delegatecalls.append({
            "caller": _canonical_address(row["caller"], f"{case['id']} child caller"),
            "childReturndata": "0x" + _hex_bytes(
                row["childReturndata"], f"{case['id']} child returndata"
            ).hex(),
            "childStatus": row["childStatus"],
            "codeAddress": _canonical_address(
                row["codeAddress"], f"{case['id']} child code address"
            ),
            "input": "0x" + _hex_bytes(row["input"], f"{case['id']} child input").hex(),
            "opcode": "DELEGATECALL",
            "source": _canonical_address(row["source"], f"{case['id']} child source"),
            "storageOwner": _canonical_address(
                row["storageOwner"], f"{case['id']} child storage owner"
            ),
            "value": str(int(row["value"])),
        })

    returndata = case["expected"]["returndata"]
    if returndata != "own-returned-runtime":
        resolved = resolve_reference(manifest, performance, returndata)
        returndata = "0x" + _hex_bytes(resolved, f"{case['id']} returndata").hex()
    return {
        "status": case["expected"]["status"],
        "returndata": returndata,
        "storage": storage,
        "eth": eth,
        "logs": [copy.deepcopy(manifest["fixtures"]["logAtoms"][name])
                 for name in case["expected"]["logs"]],
        "delegatecalls": delegatecalls,
        "targetAccount": case["expected"]["targetAccount"],
    }


def materialize_expected_projections(
    manifest: Mapping[str, Any], performance: Mapping[str, Any]
) -> Dict[str, Dict[str, Any]]:
    return {
        case["id"]: materialize_expected_projection(manifest, performance, case)
        for case in manifest["cases"]
    }


def _coverage(cases: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    by_family: Dict[str, Any] = {}
    by_endpoint: Dict[str, Any] = {}
    by_tag: Dict[str, list[str]] = {}
    for case in cases:
        for table, key in ((by_family, case["family"]), (by_endpoint, case["endpoint"])):
            row = table.setdefault(key, {"arms": [], "caseIds": [], "count": 0})
            row["count"] += 1
            row["caseIds"].append(case["id"])
            if case["arm"] not in row["arms"]:
                row["arms"].append(case["arm"])
        for tag in case["tags"]:
            by_tag.setdefault(tag, []).append(case["id"])
    for table in (by_family, by_endpoint):
        for row in table.values():
            row["arms"].sort()
    return {"byFamily": by_family, "byEndpoint": by_endpoint, "byTag": by_tag}


def _validate_route(
    manifest: Mapping[str, Any], performance: Mapping[str, Any], case: Mapping[str, Any]
) -> None:
    if case["endpoint"] == "constructor":
        if case["world"].get("kind") != "direct-create-message":
            reject(f"{case['id']} constructor world is not CREATE")
        return
    calldata = resolve_reference(manifest, performance, case["world"].get("calldata"))
    raw = _hex_bytes(calldata, f"{case['id']} calldata")
    if case["endpoint"] == "fallback(bytes)":
        if len(raw) >= 4 and raw[:4].hex() in SELECTORS.values():
            reject(f"{case['id']} fallback collides with a named selector")
        return
    wanted = SELECTORS.get(case["endpoint"])
    if wanted is None or len(raw) < 4 or raw[:4].hex() != wanted:
        reject(f"{case['id']} selector routing drifted for {case['endpoint']}")


def _validate_semantic_controls(cases: Mapping[str, Mapping[str, Any]]) -> None:
    k05 = cases["K05"]
    if k05["expected"]["storage"] != {
        "admin": "performance:canonical-admin",
        "allOtherStorage": "differential:word:zero",
        "fixtureSlot": "differential:word:zero",
        "implementation": "differential:post-setup-implementation",
    } or "setup-mutate-both-slots" not in k05["tags"]:
        reject("K05 both-slot constructor projection drifted")
    if cases["K11"]["expected"]["storage"] != "target-absent" or \
            cases["K11"]["expected"]["returndata"] != "differential:rollback-marker-32":
        reject("K11 constructor both-slot rollback projection drifted")
    for case_id, expected in {
        "X04": {"base": "performance:unossified", "implementation": "differential:post-setup-implementation"},
        "X05": {"base": "performance:unossified", "implementation": "performance:new-implementation", "admin": "performance:new-admin"},
        "X06": {"base": "performance:unossified", "implementation": "differential:post-setup-implementation", "admin": "performance:new-admin"},
    }.items():
        if cases[case_id]["expected"]["storage"] != expected:
            reject(f"{case_id} setup state projection drifted")
    for case_id in ROLLBACK_CASE_IDS:
        case = cases[case_id]
        wanted_storage = "target-absent" if case_id.startswith("K") else "exact-prestate"
        if case["expected"]["status"] != "revert" or case["expected"]["logs"] != [] or \
                case["expected"]["storage"] != wanted_storage:
            reject(f"{case_id} rollback projection drifted")
    actual_delegatecalls = frozenset(
        case_id for case_id, case in cases.items() if case["expected"]["delegatecalls"]
    )
    if actual_delegatecalls != DELEGATECALL_CASE_IDS:
        reject("exact DELEGATECALL case ownership drifted")
    for case_id in DELEGATECALL_CASE_IDS:
        rows = cases[case_id]["expected"]["delegatecalls"]
        if len(rows) != 1 or set(rows[0]) != {
            "caller", "childReturndata", "childStatus", "codeAddress", "input",
            "opcode", "source", "storageOwner", "value",
        } or rows[0]["opcode"] != "DELEGATECALL":
            reject(f"{case_id} exact DELEGATECALL projection drifted")
    child_rows = [
        {"id": case_id, "delegatecalls": cases[case_id]["expected"]["delegatecalls"]}
        for case_id in EXPECTED_CASE_IDS if case_id in DELEGATECALL_CASE_IDS
    ]
    if sha256_bytes(canonical_bytes(child_rows)) != EXPECTED_DELEGATECALL_PROJECTIONS_SHA256:
        reject("exact ordered DELEGATECALL projection bytes drifted")
    for case_id, fixture in (("K18", "differential:constructor:length-over-u64"),
                             ("X20", "differential:uac-length-over-u64")):
        case = cases[case_id]
        field = "constructorArguments" if case_id == "K18" else "calldata"
        if case["world"][field] != fixture or \
                case["expected"]["returndata"] != "differential:error:Panic-0x41" or \
                "dynamic-length-over-u64" not in case["tags"]:
            reject(f"{case_id} uint64 allocation panic boundary drifted")
    for case_id in ("K16", "X16"):
        if cases[case_id]["expected"]["returndata"] != "performance:empty":
            reject(f"{case_id} small length-overrun control no longer empty-reverts")


def validate_performance_manifest(performance: Mapping[str, Any]) -> None:
    campaign = performance.get("campaign", {})
    if campaign.get("format") != PERFORMANCE_FORMAT or campaign.get("formatVersion") != 2 or \
            campaign.get("digest", {}).get("value") != PERFORMANCE_DIGEST or \
            campaign_digest(performance) != PERFORMANCE_DIGEST:
        reject("frozen performance manifest identity drifted")
    binding = performance.get("fixtures", {}).get("artifactBindings", {})
    if binding.get("creationTemplate", {}).get("reference") != \
            "scripts/lido-ossifiable-proxy-reference.json#/artifacts/creationTemplate" or \
            binding.get("returnedRuntime", {}).get("reference") != \
            "scripts/lido-ossifiable-proxy-reference.json#/artifacts/runtime":
        reject("performance artifact JSON pointers drifted")
    fallback = performance.get("fixtures", {}).get("calldata", {}).get("fallback-256", {})
    expected_fallback = bytes.fromhex("feedface") + bytes(range(0xFC))
    if fallback.get("byteLength") != 256 or \
            _hex_bytes(fallback.get("hex"), "performance fallback-256") != expected_fallback:
        reject("performance fallback-256 must be exact feedface||00..fb")
    if performance.get("measurementContract", {}).get("gasAllowance") != "20000000":
        reject("shared adequate message gas allowance drifted")


def validate_reference_lock(reference: Mapping[str, Any], path: Path) -> None:
    if sha256_file(path) != REFERENCE_LOCK_SHA256:
        reject("reference lock byte identity drifted")
    for name, (length, digest) in EXPECTED_REFERENCE_ARTIFACTS.items():
        artifact = reference.get("artifacts", {}).get(name)
        if not isinstance(artifact, Mapping):
            reject(f"reference artifact missing: {name}")
        raw = _hex_bytes(artifact.get("hex"), f"reference {name}")
        if len(raw) != length or artifact.get("byteLength") != length or \
                sha256_bytes(raw) != digest or artifact.get("sha256") != digest:
            reject(f"reference artifact identity drifted: {name}")


def validate_manifest(
    manifest: Mapping[str, Any], performance: Mapping[str, Any],
    reference: Mapping[str, Any], reference_path: Path, *,
    enforce_pinned_digest: bool = True,
) -> None:
    _exact_keys(manifest, {
        "campaign", "cases", "coverage", "fixtures", "futureFalsifierObligations",
        "identities", "projectionContract", "sharedPerformanceManifest", "worldContract",
    }, "manifest")
    campaign = manifest.get("campaign", {})
    if campaign.get("format") != MANIFEST_FORMAT or campaign.get("formatVersion") != 2 or \
            campaign.get("fixedCaseCount") != CASE_COUNT or campaign.get("resultsIncluded") is not False or \
            campaign.get("runnerIncluded") is not False:
        reject("manifest campaign envelope drifted")
    calculated = campaign_digest(manifest)
    stored = campaign.get("digest", {}).get("value")
    if stored != calculated:
        reject("manifest canonical digest is stale")
    if enforce_pinned_digest and stored != MANIFEST_DIGEST:
        reject("manifest is not the admitted frozen 85-case identity")

    validate_performance_manifest(performance)
    validate_reference_lock(reference, reference_path)
    shared = manifest.get("sharedPerformanceManifest", {})
    if shared.get("campaignDigest") != PERFORMANCE_DIGEST or \
            shared.get("path") != PERFORMANCE_RELATIVE.as_posix():
        reject("shared performance binding drifted")
    identities = manifest.get("identities", {})
    execution = identities.get("execution", {})
    if execution != {
        "callEntrypoint": "ethereum.prague.vm.interpreter.process_message_call",
        "createEntrypoint": "ethereum.prague.vm.interpreter.process_create_message",
        "defaultRoot": "~/execution-specs",
        "eelsCommit": EELS_COMMIT,
        "fork": "Prague",
        "network": False,
        "python": "venv/bin/python",
        "pythonPath": "src",
        "requiredEnvironment": {
            "PYTHONDONTWRITEBYTECODE": "1", "PYTHONPATH": "${EELS_ROOT}/src"
        },
        "rootEnv": "EELS_ROOT",
    }:
        reject("EELS Prague execution identity drifted")
    ref_identity = identities.get("reference", {})
    if ref_identity.get("referenceLock") != REFERENCE_RELATIVE.as_posix() or \
            ref_identity.get("referenceLockSha256") != REFERENCE_LOCK_SHA256 or \
            ref_identity.get("artifactBinding", {}).get("returnedRuntime") != \
            "scripts/lido-ossifiable-proxy-reference.json#/artifacts/runtime":
        reject("reference substitution binding drifted")
    if identities.get("blanc", {}).get("evaluator") != EVALUATOR_RELATIVE.as_posix():
        reject("Blanc evaluator binding drifted")
    projection_contract = manifest.get("projectionContract", {})
    if projection_contract.get("channels") != list(PROJECTION_CHANNELS) or \
            projection_contract.get("delegatecalls", {}).get("exactOrderedFields") != [
                "opcode", "source", "caller", "codeAddress", "storageOwner",
                "input", "value", "childStatus", "childReturndata",
            ] or projection_contract.get("delegatecalls", {}).get(
                "missingExtraOrReordered"
            ) != "reject":
        reject("manifest projection-channel contract drifted")
    world_contract = manifest.get("worldContract", {})
    if world_contract.get("freshWorldPerCase") is not True or \
            world_contract.get("mutationCarryover") is not False:
        reject("manifest fresh-world contract drifted")

    cases = manifest.get("cases")
    if not isinstance(cases, list) or len(cases) != CASE_COUNT:
        reject("manifest case count drifted")
    ids = tuple(case.get("id") for case in cases if isinstance(case, Mapping))
    if ids != EXPECTED_CASE_IDS or tuple(campaign.get("fixedOrder", ())) != EXPECTED_CASE_IDS:
        reject("manifest fixed case order drifted")
    if [case.get("ordinal") for case in cases] != list(range(1, CASE_COUNT + 1)):
        reject("manifest ordinals drifted")
    case_map: Dict[str, Mapping[str, Any]] = {}
    for case in cases:
        _exact_keys(case, {
            "arm", "description", "endpoint", "expected", "family", "id",
            "ordinal", "tags", "world",
        }, f"case {case.get('id')}")
        if set(case["expected"]) != EXPECTED_CASE_PROJECTION_KEYS:
            reject(f"{case['id']} expected projection keys drifted")
        if case["arm"] not in {"success", "negative"} or not isinstance(case["tags"], list) or \
                case["tags"] != sorted(set(case["tags"])):
            reject(f"{case['id']} arm/tags drifted")
        resolve_tree(manifest, performance, case["world"])
        resolve_tree(manifest, performance, case["expected"])
        for log_name in case["expected"]["logs"]:
            if log_name not in manifest["fixtures"]["logAtoms"]:
                reject(f"{case['id']} has an unbound log atom: {log_name}")
        _validate_route(manifest, performance, case)
        case_map[case["id"]] = case

    fixtures = manifest.get("fixtures", {})
    for group in ("calldata", "constructorArguments", "errors", "mockImplementations"):
        for name, blob in fixtures.get(group, {}).items():
            validate_blob(blob, f"fixtures/{group}/{name}")
    if fixtures.get("eventTopics") != EXPECTED_EVENT_TOPICS:
        reject("event/log topics drifted")
    if {name: blob.get("sha256") for name, blob in fixtures.get("errors", {}).items()} != \
            EXPECTED_ERROR_SHA256:
        reject("event/error byte family drifted")
    panic = fixtures["errors"]["Panic-0x41"]["hex"]
    if panic != "0x4e487b71" + "00" * 31 + "41":
        reject("Panic(0x41) payload drifted")
    for namespace, bindings, source in (
        ("performance", shared.get("sharedReferenceBindings", {}), performance),
        ("differential", fixtures.get("localReferenceBindings", {}), manifest),
    ):
        for name, pointer in bindings.items():
            if not name.startswith(namespace + ":"):
                reject(f"{namespace} binding namespace drifted: {name}")
            pointer_get(source, pointer, name)

    calculated_coverage = _coverage(cases)
    coverage = manifest.get("coverage", {})
    if coverage.get("caseCount") != CASE_COUNT:
        reject("coverage case count drifted")
    for key, value in calculated_coverage.items():
        if coverage.get(key) != value:
            reject(f"coverage {key} drifted")
    for tag in coverage.get("requiredTags", []):
        if tag not in calculated_coverage["byTag"]:
            reject(f"required tag has no owner: {tag}")
    for endpoint, row in calculated_coverage["byEndpoint"].items():
        if set(row["arms"]) != {"negative", "success"}:
            reject(f"endpoint lacks success/negative coverage: {endpoint}")
    required_new = {
        "constructor-length-over-u64", "dynamic-length-over-u64", "panic-0x41",
        "runtime-length-over-u64", "solc-decoder-resource-boundary",
    }
    if not required_new.issubset(coverage.get("requiredTags", [])):
        reject("uint64 decoder boundary tags are incomplete")

    obligations = manifest.get("futureFalsifierObligations", {})
    if obligations.get("status") != "required-later-not-implemented-or-claimed-by-this-definition-packet" or \
            set(obligations.get("families", {})) != FALSIFIER_FAMILIES:
        reject("seven future falsifier obligations drifted")
    for family, row in obligations["families"].items():
        if not row.get("caseIds") or not set(row["caseIds"]).issubset(EXPECTED_CASE_IDS) or \
                not row.get("mutation") or not row.get("acceptanceBoundary"):
            reject(f"falsifier obligation is incomplete: {family}")
    if obligations["families"]["corpus-result-mutation"]["caseIds"] != list(EXPECTED_CASE_IDS):
        reject("corpus/result mutation obligation does not own every case")
    _validate_semantic_controls(case_map)


def manifest_order_sha256(manifest: Mapping[str, Any]) -> str:
    payload = ("\n".join(manifest["campaign"]["fixedOrder"]) + "\n").encode()
    return sha256_bytes(payload)


def projection_mismatches(
    expected: Mapping[str, Any], reference: Mapping[str, Any], blanc: Mapping[str, Any]
) -> list[str]:
    mismatches: list[str] = []
    for channel in PROJECTION_CHANNELS:
        if reference[channel] != expected[channel]:
            mismatches.append(f"reference.expected.{channel}")
        if blanc[channel] != expected[channel]:
            mismatches.append(f"blanc.expected.{channel}")
        if reference[channel] != blanc[channel]:
            mismatches.append(f"reference.blanc.{channel}")
    return mismatches


def _validate_projection(
    value: Mapping[str, Any], owner: str, expected_shape: Mapping[str, Any] | None = None
) -> None:
    if set(value) != set(PROJECTION_CHANNELS):
        reject(f"{owner} projection channels drifted")
    status = value["status"]
    if status not in {"success", "revert"} and not (
        isinstance(status, str) and _EXCEPTION_STATUS.fullmatch(status)
    ):
        reject(f"{owner} projection types drifted")
    returndata = value["returndata"]
    if returndata != "own-returned-runtime":
        _hex_bytes(returndata, f"{owner} returndata")
    storage = value["storage"]
    if not isinstance(storage, Mapping) or set(storage) != {"targetExists", "slots"} or \
            not isinstance(storage["targetExists"], bool) or not isinstance(storage["slots"], Mapping):
        reject(f"{owner} storage projection shape drifted")
    for slot, word in storage["slots"].items():
        if len(_hex_bytes(slot, f"{owner} storage slot")) != 32 or \
                len(_hex_bytes(word, f"{owner} storage word")) != 32:
            reject(f"{owner} storage slot/word width drifted")
    eth = value["eth"]
    if not isinstance(eth, Mapping):
        reject(f"{owner} ETH projection shape drifted")
    for address, delta in eth.items():
        if len(_hex_bytes(address, f"{owner} ETH address")) != 20 or \
                not isinstance(delta, str) or not re.fullmatch(r"-?(0|[1-9][0-9]*)", delta):
            reject(f"{owner} ETH row drifted")
    if expected_shape is not None and (
        set(storage["slots"]) != set(expected_shape["storage"]["slots"])
        or set(eth) != set(expected_shape["eth"])
    ):
        reject(f"{owner} omitted or added an observed storage/ETH coordinate")
    if not isinstance(value["logs"], list):
        reject(f"{owner} log projection shape drifted")
    for log in value["logs"]:
        if not isinstance(log, Mapping) or set(log) != {"address", "topics", "data"} or \
                len(_hex_bytes(log["address"], f"{owner} log address")) != 20 or \
                not isinstance(log["topics"], list):
            reject(f"{owner} log row drifted")
        _hex_bytes(log["data"], f"{owner} log data")
        if any(len(_hex_bytes(topic, f"{owner} log topic")) != 32 for topic in log["topics"]):
            reject(f"{owner} log topic width drifted")
    if not isinstance(value["delegatecalls"], list):
        reject(f"{owner} DELEGATECALL projection shape drifted")
    child_keys = {
        "caller", "childReturndata", "childStatus", "codeAddress", "input",
        "opcode", "source", "storageOwner", "value",
    }
    for row in value["delegatecalls"]:
        if not isinstance(row, Mapping) or set(row) != child_keys or row["opcode"] != "DELEGATECALL":
            reject(f"{owner} DELEGATECALL row drifted")
        for name in ("caller", "codeAddress", "source", "storageOwner"):
            if len(_hex_bytes(row[name], f"{owner} DELEGATECALL {name}")) != 20:
                reject(f"{owner} DELEGATECALL address width drifted")
        _hex_bytes(row["input"], f"{owner} DELEGATECALL input")
        _hex_bytes(row["childReturndata"], f"{owner} DELEGATECALL returndata")
        child_status = row["childStatus"]
        if child_status not in {"success", "revert"} and not (
            isinstance(child_status, str) and _EXCEPTION_STATUS.fullmatch(child_status)
        ):
            reject(f"{owner} DELEGATECALL status drifted")
        if not isinstance(row["value"], str) or not re.fullmatch(r"0|[1-9][0-9]*", row["value"]):
            reject(f"{owner} DELEGATECALL value drifted")
    if value["targetAccount"] not in {
        "absent", "exists-with-own-returned-runtime", "preexisting-proxy-account"
    }:
        reject(f"{owner} target-account projection drifted")


def validate_result(
    result: Mapping[str, Any], manifest: Mapping[str, Any], *,
    performance: Mapping[str, Any] | None = None,
    repo_root: Path | None = None,
    require_all_matched: bool = False,
) -> None:
    _exact_keys(result, {"schema", "identity", "summary", "rows"}, "result")
    if result.get("schema") != RESULT_FORMAT:
        reject("result format drifted")
    identity = result.get("identity", {})
    _exact_keys(identity, {
        "manifestDigest", "manifestPath", "manifestCaseCount", "manifestOrderSha256",
        "performanceManifestDigest", "performanceManifestSha256", "referenceLockSha256",
        "referenceArtifacts", "eels", "blanc", "implementation", "resultDigest",
    }, "result identity")
    if identity["manifestDigest"] != MANIFEST_DIGEST or \
            identity["manifestPath"] != MANIFEST_RELATIVE.as_posix() or \
            identity["manifestCaseCount"] != CASE_COUNT or \
            identity["manifestOrderSha256"] != manifest_order_sha256(manifest) or \
            identity["performanceManifestDigest"] != PERFORMANCE_DIGEST or \
            identity["referenceLockSha256"] != REFERENCE_LOCK_SHA256:
        reject("result frozen input identity drifted")
    if not _HEX64.fullmatch(identity["performanceManifestSha256"]):
        reject("result performance manifest byte identity is malformed")
    eels = identity["eels"]
    if eels != {
        "callEntrypoint": "ethereum.prague.vm.interpreter.process_message_call",
        "commit": EELS_COMMIT,
        "createEntrypoint": "ethereum.prague.vm.interpreter.process_create_message",
        "fork": "Prague",
        "network": False,
        "python": "venv/bin/python",
        "pythonPath": "src",
        "rootEnv": "EELS_ROOT",
        "requiredEnvironment": {
            "PYTHONDONTWRITEBYTECODE": "1", "PYTHONPATH": "${EELS_ROOT}/src"
        },
    }:
        reject("result EELS identity drifted")
    blanc = identity["blanc"]
    if set(blanc) != {
        "artifactEnvelopeSha256", "commit", "creationTemplate", "evaluatorPath",
        "evaluatorSha256", "repositoryClean", "returnedRuntime",
    } or not _HEX40.fullmatch(blanc.get("commit", "")) or blanc.get("repositoryClean") is not True or \
            blanc.get("evaluatorPath") != EVALUATOR_RELATIVE.as_posix():
        reject("result Blanc identity drifted")
    if not _HEX64.fullmatch(blanc.get("artifactEnvelopeSha256", "")) or \
            not _HEX64.fullmatch(blanc.get("evaluatorSha256", "")):
        reject("result Blanc byte identity is malformed")
    for owner in (blanc["creationTemplate"], blanc["returnedRuntime"],
                  *identity["referenceArtifacts"].values()):
        if set(owner) != {"byteLength", "sha256"} or not isinstance(owner["byteLength"], int) or \
                owner["byteLength"] < 0 or not _HEX64.fullmatch(owner["sha256"]):
            reject("result artifact identity is malformed")
    expected_reference = {
        name: {"byteLength": length, "sha256": digest}
        for name, (length, digest) in EXPECTED_REFERENCE_ARTIFACTS.items()
    }
    if identity["referenceArtifacts"] != expected_reference:
        reject("result reference artifact substitution detected")
    if blanc["creationTemplate"]["byteLength"] <= 0 or \
            blanc["creationTemplate"]["byteLength"] > 49_152 or \
            blanc["returnedRuntime"]["byteLength"] <= 0 or \
            blanc["returnedRuntime"]["byteLength"] > 24_576:
        reject("result Blanc artifact length is outside the admitted envelope")
    implementation = identity["implementation"]
    if set(implementation) != {
        "launcherPath", "launcherSha256", "runnerPath", "runnerSha256",
        "schemaPath", "schemaSha256",
    } or implementation.get("launcherPath") != LAUNCHER_RELATIVE.as_posix() or \
            not _HEX64.fullmatch(implementation.get("launcherSha256", "")) or \
            implementation.get("runnerPath") != RUNNER_RELATIVE.as_posix() or \
            implementation.get("schemaPath") != SCHEMA_RELATIVE.as_posix() or \
            not _HEX64.fullmatch(implementation.get("runnerSha256", "")) or \
            not _HEX64.fullmatch(implementation.get("schemaSha256", "")):
        reject("result implementation identity drifted")
    digest = identity["resultDigest"]
    if digest != {
        "algorithm": "sha256",
        "canonicalization": 'json.dumps(parsed, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")',
        "scope": "the entire parsed result with /identity/resultDigest/value replaced by the empty string",
        "value": digest.get("value"),
    } or not _HEX64.fullmatch(digest.get("value", "")) or \
            digest["value"] != result_digest(result):
        reject("result canonical digest is stale")
    if repo_root is not None:
        repo_root = repo_root.resolve()
        if identity["performanceManifestSha256"] != sha256_file(repo_root / PERFORMANCE_RELATIVE) or \
                blanc["evaluatorSha256"] != sha256_file(repo_root / EVALUATOR_RELATIVE) or \
                implementation["launcherSha256"] != sha256_file(repo_root / LAUNCHER_RELATIVE) or \
                implementation["runnerSha256"] != sha256_file(repo_root / RUNNER_RELATIVE) or \
                implementation["schemaSha256"] != sha256_file(repo_root / SCHEMA_RELATIVE):
            reject("result implementation or dependency bytes drifted from this checkout")

    rows = result.get("rows")
    if not isinstance(rows, list) or len(rows) != CASE_COUNT:
        reject("result row count drifted")
    if tuple(row.get("id") for row in rows) != EXPECTED_CASE_IDS or \
            [row.get("ordinal") for row in rows] != list(range(1, CASE_COUNT + 1)):
        reject("result rows do not exactly cover the frozen order")
    expected_by_id = None if performance is None else \
        materialize_expected_projections(manifest, performance)
    for row in rows:
        _exact_keys(row, {
            "id", "ordinal", "expected", "reference", "blanc", "matches", "mismatches"
        }, f"result row {row.get('id')}")
        _validate_projection(row["expected"], f"{row['id']}/expected")
        for side in ("reference", "blanc"):
            _validate_projection(
                row[side], f"{row['id']}/{side}", expected_shape=row["expected"]
            )
        if expected_by_id is not None and row["expected"] != expected_by_id[row["id"]]:
            reject(f"{row['id']} result expected projection drifted from the manifest")
        calculated = projection_mismatches(row["expected"], row["reference"], row["blanc"])
        if row["mismatches"] != calculated or row["matches"] is not (not calculated):
            reject(f"{row['id']} result comparison flags are inconsistent")
    mismatched = sum(not row["matches"] for row in rows)
    summary = result.get("summary", {})
    expected_summary = {
        "allCasesExecuted": True,
        "allMatched": mismatched == 0,
        "caseCount": CASE_COUNT,
        "executedCaseCount": CASE_COUNT,
        "matchedCaseCount": CASE_COUNT - mismatched,
        "mismatchCaseCount": mismatched,
        "skippedCaseCount": 0,
    }
    if summary != expected_summary:
        reject("result summary is inconsistent or permits skipped cases")
    if require_all_matched and mismatched:
        reject(f"differential result contains {mismatched} mismatched case(s)")


def default_paths(repo_root: Path) -> tuple[Path, Path, Path]:
    return (
        repo_root / MANIFEST_RELATIVE,
        repo_root / PERFORMANCE_RELATIVE,
        repo_root / REFERENCE_RELATIVE,
    )


def load_and_validate_campaign(repo_root: Path) -> tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]]:
    manifest_path, performance_path, reference_path = default_paths(repo_root)
    manifest = load_json(manifest_path)
    performance = load_json(performance_path)
    reference = load_json(reference_path)
    validate_manifest(manifest, performance, reference, reference_path)
    return manifest, performance, reference


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--result", type=Path)
    args = parser.parse_args()
    root = args.repo_root.expanduser().resolve()
    manifest, performance, _ = load_and_validate_campaign(root)
    if args.result:
        validate_result(
            load_json(args.result), manifest, performance=performance, repo_root=root
        )
    print(f"OK — OssifiableProxy differential schema: {CASE_COUNT} frozen cases; "
          f"manifest {MANIFEST_DIGEST}; result={'checked' if args.result else 'not requested'}")
