#!/usr/bin/env python3
"""Independent schema and Ethereum Keccak for the Lido reference lock.

This module intentionally does not import the lock builder.  It pins the v2
shape, semantic surface, identities, and byte relations independently so a
coherent builder edit is not enough to move the reference target.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
LOCK = Path(os.environ.get(
    "LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK",
    ROOT / "scripts" / "lido-circuit-breaker-reference.json",
))

FUNCTIONS = {
    "ADMIN()", "MIN_PAUSE_DURATION()", "MAX_PAUSE_DURATION()",
    "MIN_HEARTBEAT_INTERVAL()", "MAX_HEARTBEAT_INTERVAL()",
    "pauseDuration()", "heartbeatInterval()", "heartbeatExpiry(address)",
    "getPauser(address)", "getPausables()", "getPausableCount(address)",
    "isPauserLive(address)", "setPauseDuration(uint256)",
    "setHeartbeatInterval(uint256)", "registerPauser(address,address)",
    "heartbeat()", "pause(address)",
}
EVENTS = {
    "CircuitBreakerInitialized(address,uint256,uint256,uint256,uint256)",
    "PauseDurationUpdated(uint256,uint256)",
    "HeartbeatIntervalUpdated(uint256,uint256)",
    "HeartbeatUpdated(address,uint256)",
    "PauseTriggered(address,address,uint256)",
    "PauserSet(address,address,address)",
}
EVENT_INDEXING = {
    "CircuitBreakerInitialized(address,uint256,uint256,uint256,uint256)": [True, False, False, False, False],
    "PauseDurationUpdated(uint256,uint256)": [False, False],
    "HeartbeatIntervalUpdated(uint256,uint256)": [False, False],
    "HeartbeatUpdated(address,uint256)": [True, False],
    "PauseTriggered(address,address,uint256)": [True, True, False],
    "PauserSet(address,address,address)": [True, True, True],
}
ERRORS = {
    "AdminZero()", "MinPauseDurationZero()", "MinPauseDurationExceedsMax()",
    "PauseDurationBelowMin()", "PauseDurationAboveMax()",
    "MinHeartbeatIntervalZero()", "MinHeartbeatIntervalExceedsMax()",
    "HeartbeatIntervalBelowMin()", "HeartbeatIntervalAboveMax()",
    "HeartbeatExpired()", "PauseFailed()", "ReentrantCall()",
    "SenderNotAdmin()", "SenderNotPauser()", "PausableZero()",
}
CONSTRUCTOR_TYPES = ["address"] + ["uint256"] * 6
IMMUTABLE_ID_NAMES = {
    "25": "ADMIN", "28": "MIN_PAUSE_DURATION", "31": "MAX_PAUSE_DURATION",
    "34": "MIN_HEARTBEAT_INTERVAL", "37": "MAX_HEARTBEAT_INTERVAL",
}
IMMUTABLE_REFERENCES = {
    "25": [{"length": 32, "start": 352}, {"length": 32, "start": 820},
           {"length": 32, "start": 1353}, {"length": 32, "start": 2260}],
    "28": [{"length": 32, "start": 544}, {"length": 32, "start": 3746}],
    "31": [{"length": 32, "start": 313}, {"length": 32, "start": 3836}],
    "34": [{"length": 32, "start": 641}, {"length": 32, "start": 3501}],
    "37": [{"length": 32, "start": 583}, {"length": 32, "start": 3591}],
}
OFFICIAL_PARAMETERS = {
    "admin": "0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c",
    "minPauseDuration": 432000, "maxPauseDuration": 5184000,
    "minHeartbeatInterval": 2592000, "maxHeartbeatInterval": 94608000,
    "initialPauseDuration": 1814400, "initialHeartbeatInterval": 31536000,
}
INDEPENDENT_PARAMETERS = {
    "admin": "0x111122223333444455556666777788889999AaAa",
    "minPauseDuration": 60, "maxPauseDuration": 86400,
    "minHeartbeatInterval": 120, "maxHeartbeatInterval": 604800,
    "initialPauseDuration": 3600, "initialHeartbeatInterval": 86400,
}


class SchemaError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SchemaError(message)


def exact_object(value: Any, label: str, keys: set[str]) -> dict[str, Any]:
    require(isinstance(value, dict), f"{label}: expected object")
    require(set(value) == keys, f"{label}: keys differ")
    return value


def exact_list(value: Any, label: str, length: int | None = None) -> list[Any]:
    require(isinstance(value, list), f"{label}: expected list")
    if length is not None:
        require(len(value) == length, f"{label}: expected {length} rows")
    return value


def integer(value: Any, label: str) -> int:
    require(type(value) is int, f"{label}: expected integer")
    return value


def boolean(value: Any, label: str) -> bool:
    require(type(value) is bool, f"{label}: expected boolean")
    return value


def string(value: Any, label: str) -> str:
    require(isinstance(value, str), f"{label}: expected string")
    return value


def digest(value: Any, label: str, prefix: bool = False) -> str:
    pattern = r"0x[0-9a-f]{64}" if prefix else r"[0-9a-f]{64}"
    require(isinstance(value, str) and re.fullmatch(pattern, value), f"{label}: invalid digest")
    return value


def section_digest(value: Any) -> str:
    encoded = json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(encoded).hexdigest()


MASK = (1 << 64) - 1
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
ROT = [
    [0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56], [27, 20, 39, 8, 14],
]


def rol(value: int, count: int) -> int:
    return ((value << count) | (value >> (64 - count))) & MASK if count else value


def keccak_f(state: list[int]) -> None:
    for rc in RC:
        columns = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
                   for x in range(5)]
        delta = [columns[(x - 1) % 5] ^ rol(columns[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= delta[x]
        rotated = [0] * 25
        for x in range(5):
            for y in range(5):
                rotated[y + 5 * ((2 * x + 3 * y) % 5)] = rol(state[x + 5 * y], ROT[x][y])
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = rotated[x + 5 * y] ^ (
                    (~rotated[(x + 1) % 5 + 5 * y]) & rotated[(x + 2) % 5 + 5 * y])
                state[x + 5 * y] &= MASK
        state[0] ^= rc


def keccak_bytes(data: bytes) -> bytes:
    rate = 136
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % rate != rate - 1:
        padded.append(0)
    padded.append(0x80)
    state = [0] * 25
    for offset in range(0, len(padded), rate):
        block = padded[offset:offset + rate]
        for lane in range(rate // 8):
            state[lane] ^= int.from_bytes(block[8 * lane:8 * lane + 8], "little")
        keccak_f(state)
    return b"".join(word.to_bytes(8, "little") for word in state)[:32]


def keccak256(data: bytes) -> str:
    return keccak_bytes(data).hex()


def validate_abi(root: dict[str, Any], label: str) -> None:
    abi = exact_object(root["abi"], f"{label}.abi", {
        "functionCount", "errorCount", "eventCount", "functions", "errors", "events", "constructor"})
    require(integer(abi["functionCount"], "functionCount") == 17
            and integer(abi["errorCount"], "errorCount") == 15
            and integer(abi["eventCount"], "eventCount") == 6,
            f"{label}.abi: wrong counts")
    functions = exact_list(abi["functions"], f"{label}.abi.functions", 17)
    signatures: list[str] = []
    for index, item in enumerate(functions):
        row = exact_object(item, f"function[{index}]", {
            "entry", "signature", "selector", "payable", "returnTypes"})
        signature = string(row["signature"], f"function[{index}].signature")
        signatures.append(signature)
        require(row["selector"] == "0x" + keccak256(signature.encode())[:8],
                f"function[{index}]: selector mismatch")
        require(boolean(row["payable"], f"function[{index}].payable") is False,
                f"function[{index}]: runtime endpoint unexpectedly payable")
        require(isinstance(row["entry"], dict) and row["entry"].get("type") == "function"
                and isinstance(row["returnTypes"], list), f"function[{index}]: malformed ABI entry")
    require(signatures == sorted(FUNCTIONS), f"{label}.abi.functions: wrong surface/order")
    errors = exact_list(abi["errors"], f"{label}.abi.errors", 15)
    error_signatures: list[str] = []
    for index, item in enumerate(errors):
        row = exact_object(item, f"error[{index}]", {"entry", "signature", "selector"})
        signature = string(row["signature"], f"error[{index}].signature")
        error_signatures.append(signature)
        require(row["selector"] == "0x" + keccak256(signature.encode())[:8]
                and row["entry"].get("type") == "error", f"error[{index}]: selector/entry mismatch")
    require(error_signatures == sorted(ERRORS), f"{label}.abi.errors: wrong surface/order")
    events = exact_list(abi["events"], f"{label}.abi.events", 6)
    event_signatures: list[str] = []
    for index, item in enumerate(events):
        row = exact_object(item, f"event[{index}]", {"entry", "signature", "topic0", "indexed"})
        signature = string(row["signature"], f"event[{index}].signature")
        event_signatures.append(signature)
        entry = row["entry"]
        require(isinstance(entry, dict) and entry.get("type") == "event"
                and row["topic0"] == "0x" + keccak256(signature.encode()),
                f"event[{index}]: topic/entry mismatch")
        require(row["indexed"] == [arg["indexed"] for arg in entry.get("inputs", [])],
                f"event[{index}]: indexing mismatch")
        require(row["indexed"] == EVENT_INDEXING[signature],
                f"event[{index}]: pinned indexing differs")
    require(event_signatures == sorted(EVENTS), f"{label}.abi.events: wrong surface/order")
    constructor = exact_object(abi["constructor"], f"{label}.abi.constructor",
                               {"entry", "argumentNames", "argumentTypes", "payable"})
    require(constructor["argumentTypes"] == CONSTRUCTOR_TYPES
            and constructor["argumentNames"] == [
                "_admin", "_minPauseDuration", "_maxPauseDuration",
                "_minHeartbeatInterval", "_maxHeartbeatInterval",
                "_initialPauseDuration", "_initialHeartbeatInterval"]
            and boolean(constructor["payable"], "constructor.payable") is False
            and constructor["entry"].get("stateMutability") == "nonpayable",
            f"{label}.abi.constructor: wrong seven-argument boundary")


def validate_lock_schema(root: Any, label: str = "lock") -> None:
    root = exact_object(root, label, {
        "_comment", "schema", "generator", "target", "provenance", "compiler", "sources",
        "abi", "inventories", "artifacts", "deployment", "sourcify", "formalReport"})
    require(root["_comment"] == "GENERATED by scripts/lido-circuit-breaker-reference.py; do not edit by hand."
            and integer(root["schema"], f"{label}.schema") == 2, f"{label}: wrong generated marker/schema")
    require(root["generator"] == {
        "implementation": "scripts/lido-circuit-breaker-reference.py",
        "name": "blanc-lido-circuit-breaker-reference", "regenerationCommand":
        "python3 scripts/lido-circuit-breaker-reference.py generate", "version": 2},
        f"{label}.generator: wrong identity")
    require(root["target"] == {
        "address": "0x6019CB557978296BA3C08a7B73225C0975DFB2F7", "chainId": 1,
        "releaseCommit": "6829a5a962ece56564bd9d72d01c29cabf157579"}, f"{label}.target: wrong target")

    provenance = exact_object(root["provenance"], f"{label}.provenance",
                              {"repository", "inputFiles", "relations"})
    require(provenance["repository"] == "https://github.com/lidofinance/circuit-breaker",
            f"{label}.provenance.repository: wrong")
    files = exact_list(provenance["inputFiles"], f"{label}.provenance.inputFiles", 13)
    paths = []
    for index, item in enumerate(files):
        row = exact_object(item, f"inputFiles[{index}]", {"path", "sha256"})
        paths.append(string(row["path"], f"inputFiles[{index}].path"))
        digest(row["sha256"], f"inputFiles[{index}].sha256")
    require(paths == sorted(paths) and len(set(paths)) == 13, f"{label}.provenance.inputFiles: order/uniqueness")
    relations = exact_object(provenance["relations"], f"{label}.provenance.relations", {
        "sourceSnapshotsEqualStandardInput", "sourcifyStandardInputExact",
        "sourcifyStandardOutputExact", "compilerAbiEqualsSourcifyAbi"})
    require(all(boolean(value, f"relation.{key}") for key, value in relations.items()),
            f"{label}.provenance.relations: false relation")

    compiler = exact_object(root["compiler"], f"{label}.compiler", {
        "longVersion", "packaging", "file", "binarySha256", "binaryKeccak256",
        "releaseManifestEntry", "standardInputRawSha256", "standardInputCanonicalSha256",
        "compilerInputRawSha256", "compilerInputDerivation", "standardOutputRawSha256",
        "standardOutputCanonicalSha256", "settings"})
    require(compiler["longVersion"] == "0.8.34+commit.80d5c536"
            and compiler["packaging"] == "emscripten-wasm32"
            and compiler["file"] == "solc-emscripten-wasm32-v0.8.34+commit.80d5c536.js"
            and compiler["binarySha256"] == "0xc8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8"
            and compiler["binaryKeccak256"] == "0xf535c144f0bce3a603161abb62e40008e4482ef8c222a40a92f8752b639b1f89",
            f"{label}.compiler: wrong compiler identity")
    require(compiler["standardInputCanonicalSha256"] == "0a82cea6a4197758d2d31ab6f11eab64bffcfa992e2c52eff42e63b6803c67ab"
            and compiler["compilerInputRawSha256"]
            == "e07808b3e0886eb34e9daca1eeba534da890f377f17859300d2c3f601c56eb91"
            and compiler["compilerInputDerivation"]
            == "canonical Sourcify Standard JSON input plus the exact outputSelection for the vendored output"
            and compiler["standardOutputCanonicalSha256"] == "5f8d65021aa9aa174bcb2bec382ece75b48ed7770a7fc7db7a7549739407e937",
            f"{label}.compiler: wrong canonical Standard JSON identities")
    settings = compiler["settings"]
    boolean(settings.get("viaIR"), f"{label}.compiler.settings.viaIR")
    optimizer = settings.get("optimizer")
    require(isinstance(optimizer, dict), f"{label}.compiler.settings.optimizer: expected object")
    boolean(optimizer.get("enabled"), f"{label}.compiler.settings.optimizer.enabled")
    integer(optimizer.get("runs"), f"{label}.compiler.settings.optimizer.runs")
    metadata_settings = settings.get("metadata")
    require(isinstance(metadata_settings, dict), f"{label}.compiler.settings.metadata: expected object")
    boolean(metadata_settings.get("appendCBOR"), f"{label}.compiler.settings.metadata.appendCBOR")
    boolean(metadata_settings.get("useLiteralContent"),
            f"{label}.compiler.settings.metadata.useLiteralContent")
    require(settings == {"evmVersion": "prague", "metadata": {"appendCBOR": True,
            "bytecodeHash": "ipfs", "useLiteralContent": False}, "optimizer": {"enabled": True,
            "runs": 10000}, "remappings": ["forge-std/=lib/forge-std/src/"], "viaIR": False},
            f"{label}.compiler.settings: wrong exact settings")
    release = compiler["releaseManifestEntry"]
    require(release == {"build": "commit.80d5c536", "keccak256": compiler["binaryKeccak256"],
            "longVersion": compiler["longVersion"], "path": compiler["file"],
            "sha256": compiler["binarySha256"],
            "urls": ["dweb:/ipfs/QmPAVftdMu79ygr6joPuJK5GDV3D9AaH3aiBFkFkHPFbLK"],
            "version": "0.8.34"}, f"{label}.compiler.releaseManifestEntry: wrong")

    sources = exact_list(root["sources"], f"{label}.sources", 2)
    source_pins = {
        "src/CircuitBreaker.sol": ("4e33eba90fd86d27c26e9a71290485f2e82da0b46a62a61851afbcc0adf3c199",
                                   "c461eab4de32893e7e362ec4d1e27c82d73538bf"),
        "src/Registry.sol": ("3841afbe8f9aff0ebf46ee219cf952dfda4810a94a6d2c17feaa780421377345",
                             "aee736c442c86554e55669c26fb665d93250aca0"),
    }
    for index, row in enumerate(sources):
        row = exact_object(row, f"source[{index}]", {"path", "sha256", "keccak256", "gitBlob", "byteLength"})
        path = string(row["path"], f"source[{index}].path")
        require(path in source_pins and (row["sha256"], row["gitBlob"]) == source_pins[path],
                f"source[{index}]: wrong source identity")
        digest(row["keccak256"], f"source[{index}].keccak256", prefix=True)
        require(integer(row["byteLength"], f"source[{index}].byteLength") > 0,
                f"source[{index}]: empty")
    require([row["path"] for row in sources] == sorted(source_pins), f"{label}.sources: wrong order")
    validate_abi(root, label)

    inventories = exact_object(root["inventories"], f"{label}.inventories", {
        "storageLayout", "transientStorageLayout", "sourceWrites", "externalCalls", "bytecodeOpcodes"})
    require(len(exact_list(inventories["sourceWrites"], "sourceWrites", 19)) == 19,
            f"{label}.inventories.sourceWrites: wrong count")
    calls = exact_list(inventories["externalCalls"], "externalCalls", 2)
    require([(row["kind"], row["signature"]) for row in calls] == [
        ("CALL", "pauseFor(uint256)"), ("STATICCALL", "isPaused()")],
        f"{label}.inventories.externalCalls: wrong surface/order")
    for index, row in enumerate(calls):
        require(set(row) == {"source", "line", "kind", "signature", "selector"}
                and row["selector"] == "0x" + keccak256(row["signature"].encode())[:8],
                f"{label}.inventories.externalCalls[{index}]: wrong selector/shape")
    require(inventories["bytecodeOpcodes"] == {
        "creationTemplateIncludingRuntime": {"CALL": 1, "SSTORE": 16, "STATICCALL": 1, "TSTORE": 3},
        "runtimeTemplate": {"CALL": 1, "SSTORE": 14, "STATICCALL": 1, "TSTORE": 3}},
        f"{label}.inventories.bytecodeOpcodes: wrong disassembly inventory")
    require(isinstance(inventories["storageLayout"], dict)
            and len(inventories["storageLayout"].get("storage", [])) == 4
            and isinstance(inventories["transientStorageLayout"], dict)
            and len(inventories["transientStorageLayout"].get("storage", [])) == 1,
            f"{label}.inventories: wrong storage layouts")

    artifacts = exact_object(root["artifacts"], f"{label}.artifacts", {
        "creationTemplate", "runtimeTemplate", "immutableReferences", "immutableReferenceSpans",
        "worlds", "derivation"})
    creation = artifacts["creationTemplate"]
    runtime = artifacts["runtimeTemplate"]
    for name, row, length, pinned in (
        ("creation", creation, 5414, "889ef74f28a198dc968e495e86460258c7dfb9e02132cd4b5ed7657c4570981f"),
        ("runtime", runtime, 4584, "3a6bf74848e735c3260584f35061368223f71680421d8db5771bd4bc04555fa5")):
        row = exact_object(row, name, {"hex", "byteLength", "sha256", "codehash"})
        raw = bytes.fromhex(string(row["hex"], f"{name}.hex")[2:])
        require(integer(row["byteLength"], f"{name}.byteLength") == len(raw) == length
                and row["sha256"] == hashlib.sha256(raw).hexdigest() == pinned
                and row["codehash"] == "0x" + keccak256(raw), f"{label}.artifacts.{name}: byte identity")
    require(artifacts["immutableReferences"] == IMMUTABLE_REFERENCES,
            f"{label}.artifacts.immutableReferences: wrong exact inventory")
    spans = exact_list(artifacts["immutableReferenceSpans"], "immutableReferenceSpans", 12)
    checked_spans = [exact_object(row, f"immutableReferenceSpans[{index}]",
                                  {"astId", "name", "start", "length"})
                     for index, row in enumerate(spans)]
    require([(row["astId"], row["name"], row["start"], row["length"]) for row in checked_spans]
            == sorted([(ast_id, IMMUTABLE_ID_NAMES[ast_id], item["start"], item["length"])
                       for ast_id, rows in IMMUTABLE_REFERENCES.items() for item in rows],
                      key=lambda item: item[2]), f"{label}.artifacts.immutableReferenceSpans: wrong")
    worlds = exact_list(artifacts["worlds"], "worlds", 2)
    expected_worlds = [("official-mainnet", OFFICIAL_PARAMETERS),
                       ("independent-parameters", INDEPENDENT_PARAMETERS)]
    for index, (world, expected) in enumerate(zip(worlds, expected_worlds)):
        name, parameters = expected
        world = exact_object(world, f"world[{index}]", {
            "name", "parameters", "constructorSuffix", "fullCreateInput", "returnedRuntime",
            "immutableValues", "relations"})
        require(world["name"] == name and world["parameters"] == parameters,
                f"world[{index}]: wrong parameter identity")
        suffix = bytes.fromhex(world["constructorSuffix"][2:])
        full = bytes.fromhex(world["fullCreateInput"]["hex"][2:])
        returned = bytes.fromhex(world["returnedRuntime"]["hex"][2:])
        admin = bytes.fromhex(parameters["admin"][2:]).rjust(32, b"\0")
        expected_suffix = b"".join([admin] + [parameters[key].to_bytes(32, "big") for key in (
            "minPauseDuration", "maxPauseDuration", "minHeartbeatInterval",
            "maxHeartbeatInterval", "initialPauseDuration", "initialHeartbeatInterval")])
        expected_values = {
            "ADMIN": "0x" + admin.hex(),
            "MIN_PAUSE_DURATION": "0x" + parameters["minPauseDuration"].to_bytes(32, "big").hex(),
            "MAX_PAUSE_DURATION": "0x" + parameters["maxPauseDuration"].to_bytes(32, "big").hex(),
            "MIN_HEARTBEAT_INTERVAL": "0x" + parameters["minHeartbeatInterval"].to_bytes(32, "big").hex(),
            "MAX_HEARTBEAT_INTERVAL": "0x" + parameters["maxHeartbeatInterval"].to_bytes(32, "big").hex(),
        }
        require(suffix == expected_suffix and world["immutableValues"] == expected_values,
                f"world[{index}]: constructor/immutable value derivation differs")
        expected_runtime = bytearray(bytes.fromhex(runtime["hex"][2:]))
        for ast_id, entries in IMMUTABLE_REFERENCES.items():
            replacement = bytes.fromhex(expected_values[IMMUTABLE_ID_NAMES[ast_id]][2:])
            for entry in entries:
                expected_runtime[entry["start"]:entry["start"] + entry["length"]] = replacement
        require(returned == bytes(expected_runtime),
                f"world[{index}]: runtime immutable substitution differs")
        require(len(suffix) == 224 and full == bytes.fromhex(creation["hex"][2:]) + suffix,
                f"world[{index}]: full CREATE derivation differs")
        require(world["fullCreateInput"]["byteLength"] == len(full) == 5638
                and world["fullCreateInput"]["sha256"] == hashlib.sha256(full).hexdigest(),
                f"world[{index}]: full CREATE identity differs")
        require(world["returnedRuntime"]["byteLength"] == len(returned) == 4584
                and world["returnedRuntime"]["sha256"] == hashlib.sha256(returned).hexdigest()
                and world["returnedRuntime"]["codehash"] == "0x" + keccak256(returned),
                f"world[{index}]: runtime identity differs")
        require(all(boolean(value, f"world[{index}].relations.{key}")
                    for key, value in world["relations"].items()), f"world[{index}]: false relation")
    require(worlds[0]["fullCreateInput"]["sha256"]
            == "f2800888ef707680a581939c93f7975d24f25ce14641900591418e8be23400dc"
            and worlds[0]["returnedRuntime"]["sha256"]
            == "7decb73763f1c184f5e1950c5e3449fbca507fdf40836769df2e67fccd0c8a1e",
            f"{label}.artifacts.worlds: wrong official identities")
    require(artifacts["derivation"] == {
        "constructorSuffix": "abi.encode(address,uint256,uint256,uint256,uint256,uint256,uint256)",
        "fullCreateInput": "creationTemplate || constructorSuffix",
        "returnedRuntime": "runtimeTemplate with each compiler immutableReference span replaced by its constructor value",
        "parameterIsolation": "the independent world changes only the constructor suffix and compiler-declared immutable substitutions"},
        f"{label}.artifacts.derivation: wrong explanation")

    deployment = exact_object(root["deployment"], f"{label}.deployment", {
        "parameters", "manifest", "broadcastTransaction", "receipt", "createAddressDerivation",
        "returnedRuntimeEqualsSourcifyOnchain", "constructorEffects"})
    require(deployment["parameters"] == OFFICIAL_PARAMETERS
            and deployment["manifest"]["circuitBreaker"].lower()
            == "0x6019cb557978296ba3c08a7b73225c0975dfb2f7"
            and deployment["broadcastTransaction"]["hash"]
            == "0x9a1328c1f63fcdfd53d611cfe9c9a5f4c284c4c3e61af9066d90acaac2d5279f",
            f"{label}.deployment: wrong parameter/transaction identity")
    create = deployment["createAddressDerivation"]
    require(create == {"formula": "last20(keccak256(rlp([sender, nonce])))", "nonce": 0,
            "sender": "0xaCf5f111399a7c613D2f5b96b70F2Ea464D3cdF3",
            "derivedAddress": "0x6019cb557978296ba3c08a7b73225c0975dfb2f7"},
            f"{label}.deployment.createAddressDerivation: wrong")
    require(boolean(deployment["returnedRuntimeEqualsSourcifyOnchain"], "runtime relation"),
            f"{label}.deployment: runtime relation false")
    effects = deployment["constructorEffects"]
    require(effects == {"externalCalls": [], "persistentWrites": ["pauseDuration", "heartbeatInterval"],
            "transientWrites": [], "eventOrder": ["CircuitBreakerInitialized", "PauseDurationUpdated",
            "HeartbeatIntervalUpdated"]}, f"{label}.deployment.constructorEffects: wrong")

    sourcify = exact_object(root["sourcify"], f"{label}.sourcify", {
        "address", "chainId", "match", "creationMatch", "runtimeMatch", "verifiedAt",
        "canonicalResponseSha256", "metadataSha256", "deployment"})
    require(sourcify["address"] == root["target"]["address"] and sourcify["chainId"] == "1"
            and sourcify["match"] == sourcify["creationMatch"] == sourcify["runtimeMatch"] == "exact_match"
            and sourcify["canonicalResponseSha256"]
            == "073f0cbc28c3c5b3944f3abedd7741ad819c9b2e7d5d92d436b6244c3ad01cda",
            f"{label}.sourcify: wrong exact-match identity")
    formal = exact_object(root["formalReport"], f"{label}.formalReport", {
        "commit", "gitBlob", "sha256", "vendoredEncoding", "decodedByteLength", "date",
        "tools", "modelFork", "properties", "unresolved", "assumptions", "unavailableEvidence",
        "scopeQualification"})
    require(formal["commit"] == "282a708cc6dbd387c7412ac67de0a11dc6b6f38e"
            and formal["gitBlob"] == "626ad7914bf9e8b946fe5d79f3749a5916413498"
            and formal["sha256"] == "09027f5f47c3a15f3f3772bddea12adb385a34f8503fbd5369de51de2579216b"
            and integer(formal["decodedByteLength"], "formalReport.decodedByteLength") == 90844
            and formal["properties"] == {"reported": 41, "verified": 38},
            f"{label}.formalReport: wrong immutable report identity/counts")
    require(formal["unresolved"] == [
        "CB-3a membershipEquivalence_registerPauser",
        "CB-6a cleanStateAfterRemoval_registerPauser",
        "CB-8a globalCountConservation_registerPauser"],
        f"{label}.formalReport.unresolved: wrong list")

    pinned_sections = {
        "provenance": "8c982cc73e89efb21736a52a52347ef77e9635f51223ada8cca06bcd601a244d",
        "compiler": "20e5aa4b6179b8fc96e1adff66d231c24480f76cf056b26ea704fb3eba93df69",
        "abi": "9a6319b0362aed02927cffe85f24c89cce4a80c6c7c384f5f4d9ad98ea4b8029",
        "deployment": "8c807c46c7902fafbdaec6e1912ae9883e7ba8dfc1cec71be926f4193b12ebef",
        "sourcify": "0a82ce4e7b2856d1263c4d29b21381dfa802e71fbd86efbfdffd3dbffba6169f",
        "formalReport": "bd1a2338af6a8d9d7fe556fc5d3d28095d90c0e07a18d1ac6f3aae58e07e1e1b",
    }
    for section, expected in pinned_sections.items():
        require(section_digest(root[section]) == expected,
                f"{label}.{section}: exact canonical section digest differs")
    inventory_sections = {
        "storageLayout": "8f258fc62f28f434a6b238094cfd4efe7d3be746e1e4108c31e1b1aa2c79c69e",
        "transientStorageLayout": "8118c83bfe9fdc91738840d0fc670615761a85df114d53f8b3b262fdc52a3c4c",
        "sourceWrites": "65fd3e730fdee6bf134550f7fc195d7dd182f73822a513d23841b7f863de4992",
        "externalCalls": "88bd7ef7fb31b1e8d66198a65d56b37eee22938cd68dc78bdd96ee8783aefdae",
    }
    for section, expected in inventory_sections.items():
        require(section_digest(inventories[section]) == expected,
                f"{label}.inventories.{section}: exact canonical section digest differs")


if __name__ == "__main__":
    try:
        validate_lock_schema(json.loads(LOCK.read_text()), "committed lock")
    except (OSError, json.JSONDecodeError, SchemaError) as exc:
        raise SystemExit(f"lido_circuit_breaker_reference_schema.py: {exc}")
    print("OK — Lido CircuitBreaker reference schema v2")
