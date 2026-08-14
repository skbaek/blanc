#!/usr/bin/env python3
"""Independent schemas and pins for the frozen and optimized Lido ledgers."""

from __future__ import annotations

import hashlib
import json
from typing import Mapping, NoReturn, Sequence


SCHEMA = 1
OPTIMIZED_SCHEMA = 2
FROZEN_LEDGER_SHA256 = "b0a59c180afac1cb1b853b747696523334c774f269001492b9109012ce6f9e7f"
BASELINE_MANIFEST_SHA256 = "6cde638ac37977f3aea228ad877a85d37e415ac4f927e66a099be67de7d30cef"
BASELINE_MANIFEST_SCHEMA = 2
EELS_COMMIT = "4198b9c5996713b268aed602739d5aa40e277694"
REFERENCE_LOCK_SHA256 = "09e1732d8226b301bb8013ffecdd89a13fc174b736bb60e382bcfa8504fff909"
COMPILER_OUTPUT_SHA256 = "9fa75ac769507931907d523b2629f081d36dd4dc7fd87d571ea5f27656d687f2"

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

EXPECTED_OPTIMIZED_IDENTITIES = {
    "solidity": EXPECTED_IDENTITIES["solidity"],
    "blanc": {
        "creationTemplate": (4898, "e899d8f2d7406f7aa6bf6ac60e25779355c6f1e3063f5edd4aed694710ba2eaa"),
        "officialFullCreate": (5122, "bbf5c2c548a4c56ae9079cdb63f20b607ea8c4dabf853771bd33228099e2fa64"),
        "officialRuntime": (4282, "ff8eb66d66f8e4668af9bf5b687dda082c3729f8cd5ffd24a4b14697389d1505"),
        "independentFullCreate": (5122, "c33bbb06829ca1f66c536ace9d0a8a108a6f7c1a609f3aed68490afdfa50862f"),
        "independentRuntime": (4282, "ce955ede77a6343897f61bd5395731e404d9ca271fe86849359c6c9d50803796"),
    },
}

EXPECTED_OPTIMIZED_RUNTIME_TABLE = [
    ("main", 0, 2045), ("fallback", 2045, 4),
    ("error-pausable-zero", 2049, 13), ("error-sender-not-admin", 2062, 13),
    ("error-sender-not-pauser", 2075, 13), ("error-pause-below-min", 2088, 13),
    ("error-pause-above-max", 2101, 13), ("error-heartbeat-below-min", 2114, 13),
    ("error-heartbeat-above-max", 2127, 13), ("error-heartbeat-expired", 2140, 13),
    ("error-pause-failed", 2153, 13), ("error-reentrant-call", 2166, 13),
    ("empty-revert", 2179, 4), ("bubble-revert", 2183, 8),
    ("set-pauser-kernel", 2191, 198), ("append-target", 2389, 171),
    ("after-old-pauser", 2560, 100), ("remove-target", 2660, 337),
    ("finish-set-pauser", 2997, 67), ("register-after-set", 3064, 572),
    ("pause-after-set", 3636, 496), ("enumeration-loop", 4132, 77),
    ("arithmetic-panic", 4209, 73),
]

EXPECTED_OPTIMIZED_ENDPOINT_SPANS = [
    ("00000000000000000000000000000000000000000000000000000000d10ea321", 86, 76),
    ("00000000000000000000000000000000000000000000000000000000c9387332", 164, 265),
    ("00000000000000000000000000000000000000000000000000000000c427909e", 431, 74),
    ("000000000000000000000000000000000000000000000000000000008dd54ee7", 507, 39),
    ("000000000000000000000000000000000000000000000000000000008cd80ba0", 595, 74),
    ("00000000000000000000000000000000000000000000000000000000879f32f6", 671, 39),
    ("0000000000000000000000000000000000000000000000000000000076c810b5", 712, 39),
    ("0000000000000000000000000000000000000000000000000000000076a67a51", 753, 271),
    ("0000000000000000000000000000000000000000000000000000000071a99c22", 1084, 265),
    ("00000000000000000000000000000000000000000000000000000000561a4fac", 1351, 40),
    ("0000000000000000000000000000000000000000000000000000000054720ecd", 1393, 46),
    ("000000000000000000000000000000000000000000000000000000005280237a", 1441, 74),
    ("000000000000000000000000000000000000000000000000000000003defb962", 1575, 220),
    ("00000000000000000000000000000000000000000000000000000000338d93fc", 1797, 120),
    ("000000000000000000000000000000000000000000000000000000002a0acc6a", 1919, 39),
    ("000000000000000000000000000000000000000000000000000000002799657d", 1960, 39),
    ("000000000000000000000000000000000000000000000000000000000526679c", 2001, 40),
]
EXPECTED_OPTIMIZED_ENDPOINT_TOTAL_BYTES = 1760

EXPECTED_OPTIMIZED_CONSTRUCTOR_TABLE = [
    ("main", 0, 495), ("empty-revert", 495, 4),
    ("error-admin-zero", 499, 13), ("error-min-pause-zero", 512, 13),
    ("error-min-pause-above-max", 525, 13),
    ("error-min-heartbeat-zero", 538, 13),
    ("error-min-heartbeat-above-max", 551, 13),
    ("error-pause-below-min", 564, 13), ("error-pause-above-max", 577, 13),
    ("error-heartbeat-below-min", 590, 13),
    ("error-heartbeat-above-max", 603, 13),
]

EXPECTED_OPTIMIZED_IMMUTABLE_OFFSETS = {
    "admin": [174, 1094, 1833, 1920], "min-pause": [217, 713],
    "max-pause": [258, 1961], "min-heartbeat": [508, 1137],
    "max-heartbeat": [672, 1178],
}

# These are precisely the source-selected `pushFixedNat` instructions in the
# final constructor, distinguished from Prog.compile's own PUSH2 table calls.
EXPECTED_OPTIMIZED_FIXED_COORDINATE_PUSHES = [
    (12, 5122), (23, 4898), (129, 4282), (132, 616),
    (140, 398), (146, 1318), (152, 2057), (158, 2144),
    (165, 441), (172, 937), (179, 482), (186, 2185),
    (193, 732), (200, 1361), (207, 896), (214, 1402),
    (259, 4512), (266, 4544), (347, 4512), (354, 4544),
    (434, 4282),
]

EXPECTED_OPTIMIZED_SIZE_COMPARISON = {
    "runtime": {"solidityBytes": 4584, "blancBytes": 4282, "deltaBytes": -302},
    "creationTemplate": {"solidityBytes": 5414, "blancBytes": 4898, "deltaBytes": -516},
    "constructorPrefix": {"solidityBytes": 830, "blancBytes": 616, "deltaBytes": -214},
    "fullCreate": {"solidityBytes": 5638, "blancBytes": 5122, "deltaBytes": -516},
}

# Filled from the canonical object only after independently checking the
# generated partitions against the exact evaluator identities above.
EXPECTED_OPTIMIZED_BEFORE_AFTER_SHA256 = "39702eb88948ac55fa4f1c9f9c94e9e8c1345ac3bd846efdf3a121e3395c2f8a"
EXPECTED_OPTIMIZED_ARTIFACTS_SHA256 = "b238899c6f08ae0a8649927ebba596bf0241a288aac3ec26eb955a624a72f238"
EXPECTED_OPTIMIZED_REGION_COUNTS = {
    "blanc": {"runtime": 104, "creationTemplate": 188, "fullCreate": 2},
    "solidity": {"runtime": 158, "creationTemplate": 213, "fullCreate": 2},
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


def validate_optimized_profile(profile: Mapping) -> None:
    _exact_keys(profile, (
        "schema", "profile", "provenance", "artifacts", "sizeComparison",
        "beforeAfter", "ownershipSummary", "limitations"), "optimized profile")
    if profile.get("schema") != OPTIMIZED_SCHEMA or \
            profile.get("profile") != "lido-circuit-breaker-optimized":
        die("optimized artifact profile schema/profile identity drifted")

    provenance = profile["provenance"]
    _exact_keys(provenance, (
        "blancEvaluator", "referenceLock", "compilerOutput", "baselineLedger",
        "derivation"), "optimized provenance")
    if provenance["baselineLedger"] != {
            "path": "scripts/fixtures/lido-circuit-breaker/artifact-profile-baseline.json",
            "schema": SCHEMA, "sha256": FROZEN_LEDGER_SHA256}:
        die("optimized profile does not name the exact frozen launch ledger")
    if provenance["referenceLock"] != {
            "path": "scripts/lido-circuit-breaker-reference.json",
            "schema": 2, "sha256": REFERENCE_LOCK_SHA256}:
        die("optimized profile reference-lock identity drifted")
    if provenance["blancEvaluator"] != \
            "scripts/eval-lido-circuit-breaker-artifacts.lean":
        die("optimized profile evaluator owner drifted")
    if provenance["compilerOutput"] != {
            "path": "scripts/reference/lido-circuit-breaker/inputs/std-json-output.json",
            "sha256": COMPILER_OUTPUT_SHA256}:
        die("optimized profile compiler-output identity drifted")
    if provenance["derivation"] != \
            "no byte literal: Blanc=evaluator output; Solidity=reference-lock bytes; before/after=frozen-ledger subtraction":
        die("optimized profile derivation claim drifted")

    artifacts = profile["artifacts"]
    _exact_keys(artifacts, ("blanc", "solidity"), "optimized artifacts")
    for side in ("blanc", "solidity"):
        section = artifacts[side]
        _exact_keys(section, (
            "identities", "runtime", "creationTemplate", "fullCreate",
            "layoutEvidence"), f"optimized artifacts.{side}")
        identities = section["identities"]
        if set(identities) != set(EXPECTED_OPTIMIZED_IDENTITIES[side]):
            die(f"optimized {side} artifact identity names drifted")
        for name, (length, digest) in EXPECTED_OPTIMIZED_IDENTITIES[side].items():
            if identities[name] != {"byteLength": length, "sha256": digest}:
                die(f"optimized {side} {name} identity drifted")
        expected_detailed = {
            "runtime": "officialRuntime",
            "creationTemplate": "creationTemplate",
            "fullCreate": "officialFullCreate",
        }
        for artifact_name, identity_name in expected_detailed.items():
            artifact = section[artifact_name]
            _exact_keys(artifact, (
                "byteLength", "sha256", "disassembly", "regions"),
                f"optimized artifacts.{side}.{artifact_name}")
            if {"byteLength": artifact["byteLength"], "sha256": artifact["sha256"]} != \
                    identities[identity_name]:
                die(f"optimized {side} {artifact_name} detail/identity mismatch")
            _exact_keys(artifact["disassembly"], (
                "segments", "instructionCount", "instructionStreamSha256",
                "unknownOpcodeCount"),
                f"optimized artifacts.{side}.{artifact_name}.disassembly")
            for index, segment in enumerate(artifact["disassembly"]["segments"]):
                _exact_keys(segment, (
                    "role", "start", "end", "byteLength", "instructionCount",
                    "opcodeHistogram", "pushImmediateBytes"),
                    f"optimized artifacts.{side}.{artifact_name}.disassembly.segments[{index}]")
            _partition(artifact["regions"], artifact["byteLength"],
                       f"optimized artifacts.{side}.{artifact_name}.regions")
            if len(artifact["regions"]) != EXPECTED_OPTIMIZED_REGION_COUNTS[side][artifact_name]:
                die(f"optimized {side} {artifact_name} region count drifted")
    if canonical_sha256(artifacts) != EXPECTED_OPTIMIZED_ARTIFACTS_SHA256:
        die("optimized exact artifact partitions/disassembly/ownership drifted")

    blanc_layout = artifacts["blanc"]["layoutEvidence"]
    _exact_keys(blanc_layout, (
        "runtimeTable", "runtimeEndpoints", "constructorTable",
        "immutableOffsets", "fixedCoordinatePushes", "ownershipDecision"),
        "optimized artifacts.blanc.layoutEvidence")
    if blanc_layout["runtimeTable"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_OPTIMIZED_RUNTIME_TABLE]:
        die("optimized Blanc runtime table layout drifted")
    expected_endpoints = [
        {"name": n, "start": s, "byteLength": z}
        for n, s, z in EXPECTED_OPTIMIZED_ENDPOINT_SPANS]
    if blanc_layout["runtimeEndpoints"] != expected_endpoints:
        die("optimized Blanc runtime endpoint layout drifted")
    if sum(row["byteLength"] for row in blanc_layout["runtimeEndpoints"]) != \
            EXPECTED_OPTIMIZED_ENDPOINT_TOTAL_BYTES:
        die("optimized Blanc runtime endpoint coverage total drifted")
    for left, right in zip(blanc_layout["runtimeEndpoints"],
                           blanc_layout["runtimeEndpoints"][1:]):
        if left["start"] + left["byteLength"] > right["start"]:
            die("optimized Blanc runtime endpoint layout overlaps")
    if blanc_layout["constructorTable"] != [
            {"name": n, "start": s, "byteLength": z}
            for n, s, z in EXPECTED_OPTIMIZED_CONSTRUCTOR_TABLE]:
        die("optimized Blanc constructor table layout drifted")
    if blanc_layout["immutableOffsets"] != EXPECTED_OPTIMIZED_IMMUTABLE_OFFSETS:
        die("optimized Blanc immutable layout drifted")
    if blanc_layout["fixedCoordinatePushes"] != [
            {"pc": pc, "value": value}
            for pc, value in EXPECTED_OPTIMIZED_FIXED_COORDINATE_PUSHES]:
        die("optimized Blanc fixed-coordinate PUSH2 layout drifted")
    for field, offsets in EXPECTED_OPTIMIZED_IMMUTABLE_OFFSETS.items():
        for offset in offsets:
            if not any(row["start"] <= offset and
                       offset + 32 <= row["start"] + row["byteLength"]
                       for row in blanc_layout["runtimeEndpoints"]):
                die(f"optimized immutable interval {field}@{offset} escapes endpoints")
            role = "immutable-lane:" + field
            if not any(region["start"] == offset and region["end"] == offset + 32 and
                       region["role"] == role
                       for region in artifacts["blanc"]["runtime"]["regions"]):
                die(f"optimized immutable interval {field}@{offset} lacks an exact region")

    if profile["sizeComparison"] != EXPECTED_OPTIMIZED_SIZE_COMPARISON:
        die("optimized size comparison drifted")
    if canonical_sha256(profile["beforeAfter"]) != EXPECTED_OPTIMIZED_BEFORE_AFTER_SHA256:
        die("optimized before/after attribution drifted")

    owners = profile["ownershipSummary"]
    owner_names = {
            "Lido-private", "Blanc-common", "Jaune", "Solidity-compiler",
            "reference-interface-data"}
    if not isinstance(owners, dict) or set(owners) != owner_names:
        die("optimized ownership coverage is incomplete")
    owner_basis = (
        "unique bytes in the Blanc creation template (constructor prefix plus "
        "embedded runtime)")
    derived_owner_bytes = {owner: 0 for owner in owner_names}
    for region in artifacts["blanc"]["creationTemplate"]["regions"]:
        owner = region["owner"]
        if owner not in derived_owner_bytes:
            die(f"optimized creation-template region has unknown owner: {owner}")
        derived_owner_bytes[owner] += region["end"] - region["start"]
    for owner, summary in owners.items():
        if not isinstance(summary, dict) or set(summary) != {
                "blancArtifactBytes", "basis"} or \
                type(summary["blancArtifactBytes"]) is not int or \
                summary["basis"] != owner_basis or \
                summary["blancArtifactBytes"] != derived_owner_bytes[owner]:
            die(f"optimized ownership summary is not derived: {owner}")
    if derived_owner_bytes["Jaune"] != 0:
        die("optimized profile incorrectly attributes emitted Blanc bytes directly to Jaune")
    if sum(derived_owner_bytes.values()) != 4898:
        die("optimized creation-template ownership does not cover every byte")


def validate_rendered(rendered: str) -> Mapping:
    try:
        parsed = json.loads(rendered)
    except json.JSONDecodeError as exc:
        die(f"artifact profile is not valid JSON: {exc}")
    validate_profile(parsed)
    if rendered != json.dumps(parsed, indent=2, sort_keys=True) + "\n":
        die("artifact profile is not canonically rendered")
    return parsed


def validate_optimized_rendered(rendered: str) -> Mapping:
    try:
        parsed = json.loads(rendered)
    except json.JSONDecodeError as exc:
        die(f"optimized artifact profile is not valid JSON: {exc}")
    validate_optimized_profile(parsed)
    if rendered != json.dumps(parsed, indent=2, sort_keys=True) + "\n":
        die("optimized artifact profile is not canonically rendered")
    return parsed
