#!/usr/bin/env python3
"""Independent schema and launch pins for the Lido artifact baseline ledger."""

from __future__ import annotations

import hashlib
import json
from typing import Mapping, NoReturn, Sequence


SCHEMA = 1
BASELINE_MANIFEST_SHA256 = "6cde638ac37977f3aea228ad877a85d37e415ac4f927e66a099be67de7d30cef"
BASELINE_MANIFEST_SCHEMA = 2
EELS_COMMIT = "4198b9c5996713b268aed602739d5aa40e277694"
REFERENCE_LOCK_SHA256 = "09e1732d8226b301bb8013ffecdd89a13fc174b736bb60e382bcfa8504fff909"

EXPECTED_IDENTITIES = {
    "solidity": {
        "creationTemplate": (5414, "889ef74f28a198dc968e495e86460258c7dfb9e02132cd4b5ed7657c4570981f"),
        "officialFullCreate": (5638, "f2800888ef707680a581939c93f7975d24f25ce14641900591418e8be23400dc"),
        "officialRuntime": (4584, "7decb73763f1c184f5e1950c5e3449fbca507fdf40836769df2e67fccd0c8a1e"),
        "independentFullCreate": (5638, "fa683c7c793bec9410284271ecaa7fe8ca8f12759dbca0e8a937e1dbea47da86"),
        "independentRuntime": (4584, "a264bca00fa7d8b264e1666e9da3bacc87b90f285583340987f6f884795f3317"),
    },
    "blanc": {
        "creationTemplate": (7510, "3cbf5dec4dacbed0b0d5ee94f01fc0845b602fd67f260031ca693458e32fd28f"),
        "officialFullCreate": (7734, "3e207da94a889e623ecb92719f5782e0506c39d81a0eec2d7f41d14049e1ec2d"),
        "officialRuntime": (4897, "fa628a48ab7544301c5a4b287315ccff998fb43ec23fc16250f4a4309d9c100a"),
        "independentFullCreate": (7734, "a7eb1fd354306a089af848b0601600b0030ff8d82102bf1cbf8cfaac45e3d8ce"),
        "independentRuntime": (4897, "c5c98c4e99e43fa3fc61693e730b87e69dc37f6bba38f3adcdeb801c4375835f"),
    },
}

EXPECTED_RUNTIME_TABLE = [
    ("main", 0, 2383), ("fallback", 2383, 4),
    ("error-pausable-zero", 2387, 40), ("error-sender-not-admin", 2427, 40),
    ("error-sender-not-pauser", 2467, 40), ("error-pause-below-min", 2507, 40),
    ("error-pause-above-max", 2547, 40), ("error-heartbeat-below-min", 2587, 40),
    ("error-heartbeat-above-max", 2627, 40), ("error-heartbeat-expired", 2667, 40),
    ("error-pause-failed", 2707, 40), ("error-reentrant-call", 2747, 40),
    ("empty-revert", 2787, 4), ("bubble-revert", 2791, 8),
    ("set-pauser-kernel", 2799, 198), ("append-target", 2997, 171),
    ("after-old-pauser", 3168, 100), ("remove-target", 3268, 337),
    ("finish-set-pauser", 3605, 67), ("register-after-set", 3672, 572),
    ("pause-after-set", 4244, 503), ("enumeration-loop", 4747, 77),
    ("arithmetic-panic", 4824, 73),
]

EXPECTED_ENDPOINT_SPANS = [
    ("00000000000000000000000000000000000000000000000000000000d10ea321", 65, 86),
    ("00000000000000000000000000000000000000000000000000000000c9387332", 167, 275),
    ("00000000000000000000000000000000000000000000000000000000c427909e", 469, 84),
    ("000000000000000000000000000000000000000000000000000000008dd54ee7", 569, 49),
    ("000000000000000000000000000000000000000000000000000000008cd80ba0", 656, 84),
    ("00000000000000000000000000000000000000000000000000000000879f32f6", 756, 49),
    ("0000000000000000000000000000000000000000000000000000000076c810b5", 832, 49),
    ("0000000000000000000000000000000000000000000000000000000076a67a51", 897, 281),
    ("0000000000000000000000000000000000000000000000000000000071a99c22", 1227, 275),
    ("00000000000000000000000000000000000000000000000000000000561a4fac", 1518, 50),
    ("0000000000000000000000000000000000000000000000000000000054720ecd", 1595, 56),
    ("000000000000000000000000000000000000000000000000000000005280237a", 1667, 84),
    ("000000000000000000000000000000000000000000000000000000003defb962", 1789, 230),
    ("00000000000000000000000000000000000000000000000000000000338d93fc", 2035, 130),
    ("000000000000000000000000000000000000000000000000000000002a0acc6a", 2192, 49),
    ("000000000000000000000000000000000000000000000000000000002799657d", 2268, 49),
    ("000000000000000000000000000000000000000000000000000000000526679c", 2333, 50),
]
EXPECTED_ENDPOINT_TOTAL_BYTES = 1930

EXPECTED_CONSTRUCTOR_TABLE = [
    ("main", 0, 2249), ("empty-revert", 2249, 4),
    ("error-admin-zero", 2253, 40), ("error-min-pause-zero", 2293, 40),
    ("error-min-pause-above-max", 2333, 40),
    ("error-min-heartbeat-zero", 2373, 40),
    ("error-min-heartbeat-above-max", 2413, 40),
    ("error-pause-below-min", 2453, 40), ("error-pause-above-max", 2493, 40),
    ("error-heartbeat-below-min", 2533, 40),
    ("error-heartbeat-above-max", 2573, 40),
]

EXPECTED_IMMUTABLE_OFFSETS = {
    "admin": [187, 1247, 2081, 2203], "min-pause": [230, 843],
    "max-pause": [271, 2279], "min-heartbeat": [580, 1290],
    "max-heartbeat": [767, 1331],
}

EXPECTED_GAS_ROWS = {
    "GAS-1": [
        ("constructor-success-official", 62091),
        ("constructor-success-independent", 62091),
        ("constructor-success-exact-lower-bounds", 62091),
        ("constructor-success-exact-upper-bounds", 62091),
        ("constructor-success-equal-bounds", 62091),
        ("constructor-trailing-arguments", 62085),
    ],
    "GAS-2": [
        ("constructor-error-admin-zero", 681),
        ("constructor-error-min-pause-zero", 681),
        ("constructor-error-min-pause-above-max", 683),
        ("constructor-error-min-heartbeat-zero", 683),
        ("constructor-error-min-heartbeat-above-max", 685),
        ("constructor-dirty-admin", 871),
        ("constructor-precedence-admin-zero-plus-min-pause-zero", 681),
        ("constructor-precedence-both-bound-inversions", 683),
    ],
    "GAS-3": [
        ("ADMIN()", 102), ("MAX_HEARTBEAT_INTERVAL()", 101),
        ("MAX_PAUSE_DURATION()", 125), ("MIN_HEARTBEAT_INTERVAL()", 101),
        ("MIN_PAUSE_DURATION()", 101), ("getPausableCount(address)", 100),
        ("getPausables()", 101), ("getPauser(address)", 102),
        ("heartbeat()", 101), ("heartbeatExpiry(address)", 100),
        ("heartbeatInterval()", 101), ("isPauserLive(address)", 99),
        ("pause(address)", 102), ("pauseDuration()", 126),
        ("registerPauser(address,address)", 102),
        ("setHeartbeatInterval(uint256)", 100), ("setPauseDuration(uint256)", 100),
    ],
}


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def canonical_sha256(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _exact_keys(value: Mapping, keys: Sequence[str], where: str) -> None:
    if set(value) != set(keys):
        die(f"{where} keys drifted: {sorted(value)}")


def _partition(regions: Sequence[Mapping], length: int, where: str) -> None:
    cursor = 0
    for index, region in enumerate(regions):
        _exact_keys(region, (
            "id", "start", "end", "byteLength", "role", "owner",
            "certainty", "evidence", "sha256", "disassembly"),
            f"{where}[{index}]")
        if region["start"] != cursor or region["end"] <= region["start"]:
            die(f"{where} is not an exact ordered partition at byte {cursor}")
        if region["byteLength"] != region["end"] - region["start"]:
            die(f"{where} byte length mismatch")
        if region["owner"] not in {
                "Lido-private", "Blanc-common", "Jaune", "Solidity-compiler",
                "reference-interface-data"}:
            die(f"{where} has an unclassified owner")
        if region["certainty"] not in {"exact", "source-map", "bounded-inference"}:
            die(f"{where} has an invalid certainty label")
        _exact_keys(region["disassembly"], (
            "opcodeStarts", "opcodeHistogram", "pushImmediateBytes",
            "uninterpretedDataBytes"), f"{where}[{index}].disassembly")
        cursor = region["end"]
    if cursor != length:
        die(f"{where} covers {cursor} of {length} bytes")


def validate_profile(profile: Mapping) -> None:
    _exact_keys(profile, (
        "schema", "profile", "provenance", "artifacts", "sizeComparison",
        "gasClasses", "ownershipSummary", "limitations"), "profile")
    if profile.get("schema") != SCHEMA or profile.get("profile") != "lido-circuit-breaker-pre-optimization":
        die("artifact profile schema/profile identity drifted")

    provenance = profile["provenance"]
    _exact_keys(provenance, (
        "blancEvaluator", "referenceLock", "compilerOutput", "baselineManifest",
        "eelsCommit", "derivation"), "provenance")
    if provenance["baselineManifest"] != {
            "path": "scripts/fixtures/lido-circuit-breaker/manifest.json",
            "schema": BASELINE_MANIFEST_SCHEMA, "sha256": BASELINE_MANIFEST_SHA256}:
        die("baseline manifest identity drifted")
    if provenance["eelsCommit"] != EELS_COMMIT:
        die("baseline EELS identity drifted")

    artifacts = profile["artifacts"]
    _exact_keys(artifacts, ("blanc", "solidity"), "artifacts")
    for side in ("blanc", "solidity"):
        section = artifacts[side]
        _exact_keys(section, (
            "identities", "runtime", "creationTemplate", "fullCreate",
            "layoutEvidence"), f"artifacts.{side}")
        identities = section["identities"]
        if set(identities) != set(EXPECTED_IDENTITIES[side]):
            die(f"{side} artifact identity names drifted")
        for name, (length, digest) in EXPECTED_IDENTITIES[side].items():
            if identities[name] != {"byteLength": length, "sha256": digest}:
                die(f"{side} {name} identity drifted")
        for artifact_name in ("runtime", "creationTemplate", "fullCreate"):
            artifact = section[artifact_name]
            _exact_keys(artifact, (
                "byteLength", "sha256", "disassembly", "regions"),
                f"artifacts.{side}.{artifact_name}")
            _exact_keys(artifact["disassembly"], (
                "segments", "instructionCount", "instructionStreamSha256",
                "unknownOpcodeCount"),
                f"artifacts.{side}.{artifact_name}.disassembly")
            for index, segment in enumerate(artifact["disassembly"]["segments"]):
                _exact_keys(segment, (
                    "role", "start", "end", "byteLength", "instructionCount",
                    "opcodeHistogram", "pushImmediateBytes"),
                    f"artifacts.{side}.{artifact_name}.disassembly.segments[{index}]")
            _partition(artifact["regions"], artifact["byteLength"],
                       f"artifacts.{side}.{artifact_name}.regions")

    blanc_layout = profile["artifacts"]["blanc"]["layoutEvidence"]
    _exact_keys(blanc_layout, (
        "runtimeTable", "runtimeEndpoints", "constructorTable",
        "immutableOffsets", "ownershipDecision"),
        "artifacts.blanc.layoutEvidence")
    if blanc_layout["runtimeTable"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_RUNTIME_TABLE]:
        die("Blanc runtime table layout drifted from the independent baseline")
    expected_endpoints = [
        {"name": n, "start": s, "byteLength": z}
        for n, s, z in EXPECTED_ENDPOINT_SPANS]
    if blanc_layout["runtimeEndpoints"] != expected_endpoints:
        die("Blanc runtime endpoint layout drifted from the independent baseline")
    if sum(row["byteLength"] for row in blanc_layout["runtimeEndpoints"]) != \
            EXPECTED_ENDPOINT_TOTAL_BYTES:
        die("Blanc runtime endpoint coverage total drifted")
    for left, right in zip(blanc_layout["runtimeEndpoints"],
                           blanc_layout["runtimeEndpoints"][1:]):
        if left["start"] + left["byteLength"] > right["start"]:
            die("Blanc runtime endpoint layout overlaps")
    for offsets in EXPECTED_IMMUTABLE_OFFSETS.values():
        for offset in offsets:
            if not any(row["start"] <= offset and
                       offset + 32 <= row["start"] + row["byteLength"]
                       for row in blanc_layout["runtimeEndpoints"]):
                die("Blanc immutable interval lies outside every endpoint")
    if blanc_layout["constructorTable"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_CONSTRUCTOR_TABLE]:
        die("Blanc constructor table layout drifted from the independent baseline")
    if blanc_layout["immutableOffsets"] != EXPECTED_IMMUTABLE_OFFSETS:
        die("Blanc immutable layout drifted from the independent baseline")

    gas = profile["gasClasses"]
    if set(gas) != {"GAS-1", "GAS-2", "GAS-3", "GAS-4", "GAS-5", "representativeSavings"}:
        die("GAS class coverage drifted")
    if len(gas["GAS-1"]["rows"]) != 6 or len(gas["GAS-2"]["rows"]) != 8:
        die("constructor GAS class row coverage drifted")
    if len(gas["GAS-3"]["rows"]) != 17:
        die("nonpayable GAS-3 selector coverage drifted")
    for gas_class in ("GAS-1", "GAS-2"):
        actual = [(row["name"], row["delta"]) for row in gas[gas_class]["rows"]]
        if actual != EXPECTED_GAS_ROWS[gas_class]:
            die(f"{gas_class} exact ordered baseline rows drifted")
    gas3 = [(row["endpoint"], row["delta"]) for row in gas["GAS-3"]["rows"]]
    if gas3 != EXPECTED_GAS_ROWS["GAS-3"]:
        die("GAS-3 exact endpoint/delta vector drifted")
    if gas["GAS-4"]["rows"][0]["delta"] != 94 or gas["GAS-5"]["rows"][0]["delta"] != 945:
        die("GAS-4/GAS-5 baseline drifted")

    owners = profile["ownershipSummary"]
    if set(owners) != {"Lido-private", "Blanc-common", "Jaune", "Solidity-compiler", "reference-interface-data"}:
        die("ownership coverage is incomplete")
    if owners["Jaune"]["blancArtifactBytes"] != 0:
        die("baseline incorrectly attributes emitted Blanc bytes directly to Jaune")


def validate_rendered(rendered: str) -> Mapping:
    try:
        parsed = json.loads(rendered)
    except json.JSONDecodeError as exc:
        die(f"artifact profile is not valid JSON: {exc}")
    validate_profile(parsed)
    if rendered != json.dumps(parsed, indent=2, sort_keys=True) + "\n":
        die("artifact profile is not canonically rendered")
    return parsed
