#!/usr/bin/env python3
"""Generate/check the fail-closed offline Lido CircuitBreaker reference lock.

``generate`` and ``check`` are network-free.  ``refresh`` is the only command
that acquires inputs; it stages immutable Git/Sourcify/solc/report evidence and
will publish it only after the same pinned builder and schema accept it.
"""
from __future__ import annotations

import argparse
import base64
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

from lido_circuit_breaker_reference_schema import (
    IMMUTABLE_ID_NAMES, IMMUTABLE_REFERENCES, INDEPENDENT_PARAMETERS,
    OFFICIAL_PARAMETERS, SchemaError as LockSchemaError, keccak256,
    validate_lock_schema,
)

ROOT = Path(__file__).resolve().parents[1]
REF = Path(os.environ.get(
    "LIDO_CIRCUIT_BREAKER_REFERENCE_DIR",
    ROOT / "scripts" / "reference" / "lido-circuit-breaker",
))
INPUT = REF / "inputs"
LOCK = Path(os.environ.get(
    "LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK",
    ROOT / "scripts" / "lido-circuit-breaker-reference.json",
))

REPOSITORY = "https://github.com/lidofinance/circuit-breaker"
RELEASE_COMMIT = "6829a5a962ece56564bd9d72d01c29cabf157579"
TARGET = "0x6019CB557978296BA3C08a7B73225C0975DFB2F7"
REPORT_COMMIT = "282a708cc6dbd387c7412ac67de0a11dc6b6f38e"
REPORT_PATH = "Cyfrin CircuitBreaker Formal Verification Report 04-2026.pdf"
REPORT_FILE = "formal-report-09027f5f47c3a15f3f3772bddea12adb385a34f8503fbd5369de51de2579216b.pdf.b64"
SOLC_FILE = "solc-emscripten-wasm32-v0.8.34+commit.80d5c536.js"
SOLC_LIST_URL = "https://binaries.soliditylang.org/emscripten-wasm32/list.json"
SOURCIFY_URL = f"https://sourcify.dev/server/v2/contract/1/{TARGET}?fields=all"
GENERATOR_NAME = "blanc-lido-circuit-breaker-reference"
GENERATOR_VERSION = 2

PINNED_INPUT_SHA256 = {
    "compiler-input.json": "e07808b3e0886eb34e9daca1eeba534da890f377f17859300d2c3f601c56eb91",
    "deploy-params-mainnet.json": "9c67419bd4d8f7ca30d9762fa9abb8985147b8dfa3204b7381e0abea316f51b8",
    "deployed.mainnet.json": "663ed6e40750fc8bfdf957cf5ee8ff47bdb3ce9aca08801052caceb1f757a482",
    "foundry.toml": "122345d4fb968a449be8a769224e5029eb3b6ec927d1042c09c1fd412a96c0ab",
    REPORT_FILE: "ed4fda6616de2eeacd4198a6c5eb9fe50eb24c4771da2e49afaae4514995eecf",
    "production-broadcast-86ba620554c9202efa086459db529b061e226143.json.b64":
        "86d438d99ce5ab64ed4c2e664496cd9855170e73cbe8d47fc6d30953bb46c871",
    "production-broadcast.json": "6ec4b9780f9cdf897f9f76b2edf37e1707134ebc9ddbefdffc9f3d6c6d13e5fa",
    "solc-emscripten-wasm32-release.json": "5c02e1c3f0a65df769691d58953bd6b592b826a8849b661b5b4349e2c9ee498e",
    "source/CircuitBreaker.sol": "4e33eba90fd86d27c26e9a71290485f2e82da0b46a62a61851afbcc0adf3c199",
    "source/Registry.sol": "3841afbe8f9aff0ebf46ee219cf952dfda4810a94a6d2c17feaa780421377345",
    "sourcify-v2.json": "ba5c388caca411cdef751c1d68fa55af9e88f5b42eb7612e316cf6bb5e0fee02",
    "std-json-input.json": "c75b4db7705a67e0bf57e4c76aec8d1c05fc2e21c4d10e2555284c3322123bd2",
    "std-json-output.json": "9fa75ac769507931907d523b2629f081d36dd4dc7fd87d571ea5f27656d687f2",
}
PINNED_GIT_BLOBS = {
    "source/CircuitBreaker.sol": "c461eab4de32893e7e362ec4d1e27c82d73538bf",
    "source/Registry.sol": "aee736c442c86554e55669c26fb665d93250aca0",
    "deployed.mainnet.json": "9e1a8830123f47d22f9245276376e3bcbbc6f41b",
    "deploy-params-mainnet.json": "32eb811876a72ebc37b059509596fe4211264f99",
}


class ReferenceError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise ReferenceError(message)


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def compact(value: Any) -> bytes:
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()


def strict_json(data: bytes | str, what: str) -> Any:
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                fail(f"duplicate JSON key {key!r} in {what}")
            result[key] = value
        return result

    def invalid_constant(value: str) -> None:
        fail(f"non-finite JSON value {value} in {what}")

    try:
        return json.loads(data, object_pairs_hook=object_pairs, parse_constant=invalid_constant)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f"cannot parse JSON {what}: {exc}")


def load(path: Path) -> Any:
    try:
        return strict_json(path.read_bytes(), str(path))
    except OSError as exc:
        fail(f"cannot read {path}: {exc}")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


def hex_bytes(value: Any, what: str) -> bytes:
    expect(isinstance(value, str) and value.startswith("0x"), f"{what} is not 0x hex")
    body = value[2:]
    expect(len(body) % 2 == 0 and all(char in "0123456789abcdefABCDEF" for char in body),
           f"{what} is not even hexadecimal")
    return bytes.fromhex(body)


def byte_artifact(raw: bytes, include_hex: bool = True) -> dict[str, Any]:
    result = {
        "byteLength": len(raw), "sha256": sha256(raw),
        "codehash": "0x" + keccak256(raw),
    }
    if include_hex:
        result["hex"] = "0x" + raw.hex()
    return result


def validate_input_pins() -> list[dict[str, str]]:
    actual_paths = sorted(str(path.relative_to(INPUT)) for path in INPUT.rglob("*") if path.is_file())
    expect(actual_paths == sorted(PINNED_INPUT_SHA256),
           f"authoritative input inventory differs: {actual_paths}")
    rows = []
    for relative in actual_paths:
        data = (INPUT / relative).read_bytes()
        actual = sha256(data)
        expect(actual == PINNED_INPUT_SHA256[relative],
               f"authoritative input digest differs for {relative}: {actual}")
        if relative in PINNED_GIT_BLOBS:
            expect(git_blob(data) == PINNED_GIT_BLOBS[relative],
                   f"authoritative Git blob differs for {relative}")
        rows.append({"path": relative, "sha256": actual})
    return rows


def contract_output(output: dict[str, Any]) -> dict[str, Any]:
    try:
        return output["contracts"]["src/CircuitBreaker.sol"]["CircuitBreaker"]
    except (KeyError, TypeError) as exc:
        fail(f"compiler output lacks src/CircuitBreaker.sol:CircuitBreaker: {exc}")


def abi_inventory(abi: Any) -> dict[str, Any]:
    expect(isinstance(abi, list), "compiler ABI is not a list")
    functions: list[dict[str, Any]] = []
    errors: list[dict[str, Any]] = []
    events: list[dict[str, Any]] = []
    constructors: list[dict[str, Any]] = []
    for entry in abi:
        expect(isinstance(entry, dict) and isinstance(entry.get("type"), str),
               "ABI entry has unknown shape")
        kind = entry["type"]
        if kind == "constructor":
            constructors.append(entry)
            continue
        expect(kind in {"function", "error", "event"}, f"unsupported ABI entry {kind!r}")
        inputs = entry.get("inputs")
        expect(isinstance(inputs, list) and isinstance(entry.get("name"), str),
               f"{kind} ABI entry is malformed")
        signature = f"{entry['name']}({','.join(argument['type'] for argument in inputs)})"
        if kind == "function":
            outputs = entry.get("outputs")
            expect(isinstance(outputs, list) and entry.get("stateMutability") in {"view", "nonpayable"},
                   f"function ABI entry {signature} is malformed")
            functions.append({
                "entry": entry, "signature": signature,
                "selector": "0x" + keccak256(signature.encode())[:8],
                "payable": entry["stateMutability"] == "payable",
                "returnTypes": [argument["type"] for argument in outputs],
            })
        elif kind == "error":
            errors.append({"entry": entry, "signature": signature,
                           "selector": "0x" + keccak256(signature.encode())[:8]})
        else:
            events.append({
                "entry": entry, "signature": signature,
                "topic0": "0x" + keccak256(signature.encode()),
                "indexed": [argument["indexed"] for argument in inputs],
            })
    functions.sort(key=lambda row: row["signature"])
    errors.sort(key=lambda row: row["signature"])
    events.sort(key=lambda row: row["signature"])
    expect(len(constructors) == 1, "ABI does not have exactly one constructor")
    constructor = constructors[0]
    constructor_inputs = constructor.get("inputs", [])
    result = {
        "functionCount": len(functions), "errorCount": len(errors), "eventCount": len(events),
        "functions": functions, "errors": errors, "events": events,
        "constructor": {
            "entry": constructor,
            "argumentNames": [argument["name"] for argument in constructor_inputs],
            "argumentTypes": [argument["type"] for argument in constructor_inputs],
            "payable": constructor.get("stateMutability") == "payable",
        },
    }
    expect((len(functions), len(errors), len(events), len(constructor_inputs)) == (17, 15, 6, 7),
           "ABI counts differ from 17 functions / 15 errors / 6 events / 7 constructor arguments")
    return result


def encode_parameters(parameters: dict[str, Any]) -> bytes:
    admin = hex_bytes(parameters["admin"], "constructor admin")
    expect(len(admin) == 20, "constructor admin is not 20 bytes")
    words = [admin.rjust(32, b"\0")]
    for key in ("minPauseDuration", "maxPauseDuration", "minHeartbeatInterval",
                "maxHeartbeatInterval", "initialPauseDuration", "initialHeartbeatInterval"):
        value = parameters[key]
        expect(type(value) is int and 0 <= value < 2**256, f"invalid constructor integer {key}")
        words.append(value.to_bytes(32, "big"))
    return b"".join(words)


def immutable_values(parameters: dict[str, Any]) -> dict[str, str]:
    values = {
        "ADMIN": hex_bytes(parameters["admin"], "admin").rjust(32, b"\0"),
        "MIN_PAUSE_DURATION": parameters["minPauseDuration"].to_bytes(32, "big"),
        "MAX_PAUSE_DURATION": parameters["maxPauseDuration"].to_bytes(32, "big"),
        "MIN_HEARTBEAT_INTERVAL": parameters["minHeartbeatInterval"].to_bytes(32, "big"),
        "MAX_HEARTBEAT_INTERVAL": parameters["maxHeartbeatInterval"].to_bytes(32, "big"),
    }
    return {name: "0x" + value.hex() for name, value in values.items()}


def patch_runtime(template: bytes, values: dict[str, str]) -> bytes:
    result = bytearray(template)
    covered: set[int] = set()
    for ast_id, entries in IMMUTABLE_REFERENCES.items():
        replacement = hex_bytes(values[IMMUTABLE_ID_NAMES[ast_id]], "immutable value")
        expect(len(replacement) == 32, "immutable replacement is not one word")
        for entry in entries:
            start, length = entry["start"], entry["length"]
            cells = set(range(start, start + length))
            expect(length == 32 and start + length <= len(result) and not covered & cells,
                   "immutable reference overlaps or is out of bounds")
            covered |= cells
            result[start:start + length] = replacement
    expect(len(covered) == 12 * 32, "immutable reference coverage differs")
    return bytes(result)


def world(name: str, parameters: dict[str, Any], creation: bytes, runtime: bytes) -> dict[str, Any]:
    suffix = encode_parameters(parameters)
    values = immutable_values(parameters)
    full = creation + suffix
    returned = patch_runtime(runtime, values)
    return {
        "name": name, "parameters": parameters, "constructorSuffix": "0x" + suffix.hex(),
        "fullCreateInput": byte_artifact(full), "returnedRuntime": byte_artifact(returned),
        "immutableValues": values,
        "relations": {"sameCreationTemplate": True, "sameCompilerSettings": True,
                      "suffixIsExactAbiEncoding": True, "runtimeDiffOnlyAtImmutableSpans": True},
    }


def opcode_inventory(code: bytes) -> dict[str, int]:
    wanted = {0x55: "SSTORE", 0x5D: "TSTORE", 0xF1: "CALL", 0xFA: "STATICCALL"}
    counts = {name: 0 for name in wanted.values()}
    cursor = 0
    while cursor < len(code):
        opcode = code[cursor]
        if opcode in wanted:
            counts[wanted[opcode]] += 1
        cursor += 1 + (opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0)
    return counts


SOURCE_WRITES = [
    ("src/CircuitBreaker.sol", "constructor", "immutable", "ADMIN = _admin;"),
    ("src/CircuitBreaker.sol", "constructor", "immutable", "MIN_PAUSE_DURATION = _minPauseDuration;"),
    ("src/CircuitBreaker.sol", "constructor", "immutable", "MAX_PAUSE_DURATION = _maxPauseDuration;"),
    ("src/CircuitBreaker.sol", "constructor", "immutable", "MIN_HEARTBEAT_INTERVAL = _minHeartbeatInterval;"),
    ("src/CircuitBreaker.sol", "constructor", "immutable", "MAX_HEARTBEAT_INTERVAL = _maxHeartbeatInterval;"),
    ("src/CircuitBreaker.sol", "nonReentrant", "transient", "lock = true;"),
    ("src/CircuitBreaker.sol", "nonReentrant", "transient", "lock = false;"),
    ("src/CircuitBreaker.sol", "_setHeartbeatExpiry", "persistent", "heartbeatExpiry[_pauser] = _expiry;"),
    ("src/CircuitBreaker.sol", "_setPauseDuration", "persistent", "pauseDuration = _newPauseDuration;"),
    ("src/CircuitBreaker.sol", "_setHeartbeatInterval", "persistent", "heartbeatInterval = _newHeartbeatInterval;"),
    ("src/Registry.sol", "setPauser", "persistent", "_self.pauser[_pausable] = _newPauser;"),
    ("src/Registry.sol", "setPauser", "persistent", "--_self.pausableCount[previousPauser];"),
    ("src/Registry.sol", "setPauser", "persistent", "_self.pausables.push(_pausable);"),
    ("src/Registry.sol", "setPauser", "persistent", "_self.oneBasedIndex[_pausable] = _self.pausables.length;"),
    ("src/Registry.sol", "setPauser", "persistent", "++_self.pausableCount[_newPauser];"),
    ("src/Registry.sol", "setPauser", "persistent", "_self.pausables[removedIndex - 1] = lastPausable;"),
    ("src/Registry.sol", "setPauser", "persistent", "_self.oneBasedIndex[lastPausable] = removedIndex;"),
    ("src/Registry.sol", "setPauser", "persistent", "_self.pausables.pop();"),
    ("src/Registry.sol", "setPauser", "persistent", "delete _self.oneBasedIndex[_pausable];"),
]


def source_write_inventory(source_text: dict[str, str]) -> list[dict[str, Any]]:
    rows = []
    for path, owner, storage, statement in SOURCE_WRITES:
        text = source_text[path]
        expect(text.count(statement) == 1, f"source write statement drifted: {statement}")
        offset = text.index(statement)
        rows.append({"source": path, "owner": owner, "storage": storage,
                     "line": text[:offset].count("\n") + 1, "statement": statement})
    return rows


def create_address(sender: str, nonce: int) -> str:
    sender_bytes = hex_bytes(sender, "CREATE sender")
    expect(len(sender_bytes) == 20 and nonce == 0, "only pinned nonce-zero CREATE derivation expected")
    encoded = bytes([0xD6, 0x94]) + sender_bytes + bytes([0x80])
    return "0x" + keccak256(encoded)[-40:]


def build() -> dict[str, Any]:
    input_files = validate_input_pins()
    compiler_input_bytes = (INPUT / "compiler-input.json").read_bytes()
    standard_input_bytes = (INPUT / "std-json-input.json").read_bytes()
    standard_output_bytes = (INPUT / "std-json-output.json").read_bytes()
    sourcify_bytes = (INPUT / "sourcify-v2.json").read_bytes()
    compiler_input = strict_json(compiler_input_bytes, "effective compiler input")
    standard = strict_json(standard_input_bytes, "Standard JSON input")
    output = strict_json(standard_output_bytes, "Standard JSON output")
    sourcify = strict_json(sourcify_bytes, "Sourcify v2 response")
    deployment_manifest = load(INPUT / "deployed.mainnet.json")
    parameters = load(INPUT / "deploy-params-mainnet.json")
    broadcast = load(INPUT / "production-broadcast.json")
    broadcast_raw = base64.b64decode(
        (INPUT / "production-broadcast-86ba620554c9202efa086459db529b061e226143.json.b64").read_bytes(),
        validate=False,
    )
    expect(sha256(broadcast_raw) == "e3bf2dd480b0ee8fb33bcdb885462401a2bfd773fe743fe77613783cd649d871"
           and git_blob(broadcast_raw) == "86ba620554c9202efa086459db529b061e226143",
           "authoritative production broadcast raw bytes differ")
    expect(strict_json(broadcast_raw, "raw production broadcast") == broadcast,
           "readable production broadcast mirror differs from authoritative raw bytes")
    release = load(INPUT / "solc-emscripten-wasm32-release.json")
    reconstructed_standard = copy.deepcopy(compiler_input)
    output_selection = reconstructed_standard["settings"].pop("outputSelection")
    expect(reconstructed_standard == standard,
           "effective compiler input differs from canonical Sourcify input beyond outputSelection")
    expect(output_selection == {"src/CircuitBreaker.sol": {"CircuitBreaker": [
        "abi", "devdoc", "evm.bytecode.linkReferences", "evm.bytecode.object",
        "evm.bytecode.sourceMap", "evm.deployedBytecode.immutableReferences",
        "evm.deployedBytecode.linkReferences", "evm.deployedBytecode.object",
        "evm.deployedBytecode.sourceMap", "metadata", "storageLayout",
        "transientStorageLayout", "userdoc"]}},
        "effective compiler outputSelection differs from the exact vendored output surface")

    source_text: dict[str, str] = {}
    source_rows = []
    for source_path in ("src/CircuitBreaker.sol", "src/Registry.sol"):
        snapshot_path = INPUT / "source" / Path(source_path).name
        data = snapshot_path.read_bytes()
        text = data.decode()
        expect(standard["sources"][source_path] == {"content": text},
               f"source snapshot differs from Standard JSON input for {source_path}")
        expect(sourcify["sources"][source_path] == {"content": text},
               f"source snapshot differs from Sourcify for {source_path}")
        source_text[source_path] = text
        source_rows.append({"path": source_path, "sha256": sha256(data),
                            "keccak256": "0x" + keccak256(data), "gitBlob": git_blob(data),
                            "byteLength": len(data)})
    source_rows.sort(key=lambda row: row["path"])
    expect(sourcify["stdJsonInput"] == standard, "Sourcify Standard JSON input differs")
    expect(sourcify["stdJsonOutput"] == output, "Sourcify Standard JSON output differs")
    expect(sha256(compact(standard)) == "0a82cea6a4197758d2d31ab6f11eab64bffcfa992e2c52eff42e63b6803c67ab",
           "canonical Standard JSON input digest differs")
    expect(sha256(compact(output)) == "5f8d65021aa9aa174bcb2bec382ece75b48ed7770a7fc7db7a7549739407e937",
           "canonical Standard JSON output digest differs")
    expect(sha256(compact(sourcify)) == "073f0cbc28c3c5b3944f3abedd7741ad819c9b2e7d5d92d436b6244c3ad01cda",
           "canonical Sourcify response digest differs")

    contract = contract_output(output)
    abi = abi_inventory(contract["abi"])
    expect(contract["abi"] == sourcify["abi"], "compiler ABI differs from Sourcify ABI")
    sourcify_functions = {row["signature"]: row["signatureHash4"]
                          for row in sourcify["signatures"]["function"]}
    expect({row["signature"]: row["selector"] for row in abi["functions"]} == sourcify_functions,
           "recomputed selectors differ from Sourcify method identifiers")
    sourcify_errors = {row["signature"]: row["signatureHash4"]
                       for row in sourcify["signatures"]["error"]}
    expect({row["signature"]: row["selector"] for row in abi["errors"]} == sourcify_errors,
           "recomputed custom-error selectors differ from Sourcify identifiers")
    sourcify_events = {row["signature"]: row["signatureHash32"]
                       for row in sourcify["signatures"]["event"]}
    expect({row["signature"]: row["topic0"] for row in abi["events"]} == sourcify_events,
           "recomputed event topics differ from Sourcify identifiers")

    creation = bytes.fromhex(contract["evm"]["bytecode"]["object"])
    runtime_template = bytes.fromhex(contract["evm"]["deployedBytecode"]["object"])
    references = contract["evm"]["deployedBytecode"]["immutableReferences"]
    expect(references == IMMUTABLE_REFERENCES, "compiler immutableReferences differ from fixed inventory")
    spans = sorted([{"astId": ast_id, "name": IMMUTABLE_ID_NAMES[ast_id], **entry}
                    for ast_id, entries in references.items() for entry in entries],
                   key=lambda row: row["start"])
    official = world("official-mainnet", parameters, creation, runtime_template)
    independent = world("independent-parameters", INDEPENDENT_PARAMETERS, creation, runtime_template)

    transactions = broadcast.get("transactions")
    receipts = broadcast.get("receipts")
    expect(isinstance(transactions, list) and len(transactions) == 1
           and isinstance(receipts, list) and len(receipts) == 1, "production broadcast is not singleton")
    transaction = transactions[0]
    receipt = receipts[0]
    full_input = hex_bytes(transaction["transaction"]["input"], "broadcast CREATE input")
    expect(full_input == hex_bytes(official["fullCreateInput"]["hex"], "derived full CREATE input"),
           "broadcast CREATE input differs from compiler template plus exact constructor encoding")
    expect(hex_bytes(sourcify["creationBytecode"]["recompiledBytecode"], "Sourcify creation template") == creation,
           "Sourcify recompiled creation template differs from compiler output")
    expect(hex_bytes(sourcify["creationBytecode"]["onchainBytecode"], "Sourcify onchain creation") == full_input,
           "Sourcify onchain creation bytes differ from broadcast")
    expect(hex_bytes(sourcify["runtimeBytecode"]["recompiledBytecode"], "Sourcify runtime template")
           == runtime_template, "Sourcify recompiled runtime differs from compiler output")
    returned_runtime = hex_bytes(sourcify["runtimeBytecode"]["onchainBytecode"], "Sourcify onchain runtime")
    expect(returned_runtime == hex_bytes(official["returnedRuntime"]["hex"], "derived official runtime"),
           "immutable substitution does not reproduce returned runtime")
    expect(transaction["contractAddress"].lower() == TARGET.lower()
           and receipt["contractAddress"].lower() == TARGET.lower()
           and deployment_manifest["circuitBreaker"].lower() == TARGET.lower(),
           "deployment artifacts disagree on target address")
    sender = deployment_manifest["meta"]["deployer"]
    nonce_raw = transaction["transaction"]["nonce"]
    nonce = int(nonce_raw, 0) if isinstance(nonce_raw, str) else nonce_raw
    derived = create_address(sender, nonce)
    expect(derived.lower() == TARGET.lower(), "CREATE address derivation differs from deployed address")
    expect(parameters == OFFICIAL_PARAMETERS == deployment_manifest["constructorArgs"],
           "deployment parameter artifacts disagree")
    expect(transaction["arguments"] == [parameters["admin"]] + [str(parameters[key]) for key in (
        "minPauseDuration", "maxPauseDuration", "minHeartbeatInterval", "maxHeartbeatInterval",
        "initialPauseDuration", "initialHeartbeatInterval")], "broadcast constructor arguments differ")
    expect(receipt["status"] == "0x1" and len(receipt["logs"]) == 3,
           "deployment receipt is not successful with exactly three constructor logs")
    expected_topics = [next(row["topic0"] for row in abi["events"] if row["signature"].startswith(name + "("))
                       for name in ("CircuitBreakerInitialized", "PauseDurationUpdated",
                                    "HeartbeatIntervalUpdated")]
    expect([row["topics"][0] for row in receipt["logs"]] == expected_topics,
           "constructor receipt event order/topics differ")

    report_encoded = (INPUT / REPORT_FILE).read_bytes()
    try:
        report = base64.b64decode(report_encoded, validate=False)
    except ValueError as exc:
        fail(f"vendored formal report base64 is invalid: {exc}")
    expect(len(report) == 90844 and sha256(report)
           == "09027f5f47c3a15f3f3772bddea12adb385a34f8503fbd5369de51de2579216b",
           "vendored formal report raw bytes differ")
    expect(git_blob(report) == "626ad7914bf9e8b946fe5d79f3749a5916413498",
           "vendored formal report Git blob differs")
    expect(report.startswith(b"%PDF-"), "vendored formal report is not a PDF")

    calls = [
        {"source": "src/CircuitBreaker.sol", "line": 274, "kind": "CALL",
         "signature": "pauseFor(uint256)", "selector": "0x" + keccak256(b"pauseFor(uint256)")[:8]},
        {"source": "src/CircuitBreaker.sol", "line": 275, "kind": "STATICCALL",
         "signature": "isPaused()", "selector": "0x" + keccak256(b"isPaused()")[:8]},
    ]
    expect("target.pauseFor(duration);" in source_text["src/CircuitBreaker.sol"]
           and "target.isPaused()" in source_text["src/CircuitBreaker.sol"],
           "external-call source sites differ")
    metadata = contract["metadata"]
    metadata_object = strict_json(metadata, "compiler metadata")
    expect(metadata_object == sourcify["metadata"], "compiler metadata differs from Sourcify")
    compiler_settings = standard["settings"]
    expect(compiler_settings == sourcify["compilation"]["compilerSettings"],
           "Standard JSON and Sourcify compiler settings differ")
    expect(release == {
        "build": "commit.80d5c536", "keccak256": "0xf535c144f0bce3a603161abb62e40008e4482ef8c222a40a92f8752b639b1f89",
        "longVersion": "0.8.34+commit.80d5c536", "path": SOLC_FILE,
        "sha256": "0xc8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8",
        "urls": ["dweb:/ipfs/QmPAVftdMu79ygr6joPuJK5GDV3D9AaH3aiBFkFkHPFbLK"], "version": "0.8.34"},
        "official solc release manifest row differs")

    return {
        "_comment": "GENERATED by scripts/lido-circuit-breaker-reference.py; do not edit by hand.",
        "schema": 2,
        "generator": {"name": GENERATOR_NAME, "version": GENERATOR_VERSION,
                      "implementation": "scripts/lido-circuit-breaker-reference.py",
                      "regenerationCommand": "python3 scripts/lido-circuit-breaker-reference.py generate"},
        "target": {"address": TARGET, "chainId": 1, "releaseCommit": RELEASE_COMMIT},
        "provenance": {
            "repository": REPOSITORY, "inputFiles": input_files,
            "relations": {"sourceSnapshotsEqualStandardInput": True,
                          "sourcifyStandardInputExact": True, "sourcifyStandardOutputExact": True,
                          "compilerAbiEqualsSourcifyAbi": True},
        },
        "compiler": {
            "longVersion": "0.8.34+commit.80d5c536", "packaging": "emscripten-wasm32",
            "file": SOLC_FILE, "binarySha256": release["sha256"],
            "binaryKeccak256": release["keccak256"], "releaseManifestEntry": release,
            "standardInputRawSha256": sha256(standard_input_bytes),
            "standardInputCanonicalSha256": sha256(compact(standard)),
            "compilerInputRawSha256": sha256(compiler_input_bytes),
            "compilerInputDerivation":
                "canonical Sourcify Standard JSON input plus the exact outputSelection for the vendored output",
            "standardOutputRawSha256": sha256(standard_output_bytes),
            "standardOutputCanonicalSha256": sha256(compact(output)), "settings": compiler_settings,
        },
        "sources": source_rows,
        "abi": abi,
        "inventories": {
            "storageLayout": contract["storageLayout"],
            "transientStorageLayout": contract["transientStorageLayout"],
            "sourceWrites": source_write_inventory(source_text), "externalCalls": calls,
            "bytecodeOpcodes": {"creationTemplateIncludingRuntime": opcode_inventory(creation),
                                "runtimeTemplate": opcode_inventory(runtime_template)},
        },
        "artifacts": {
            "creationTemplate": byte_artifact(creation), "runtimeTemplate": byte_artifact(runtime_template),
            "immutableReferences": references, "immutableReferenceSpans": spans,
            "worlds": [official, independent],
            "derivation": {
                "constructorSuffix": "abi.encode(address,uint256,uint256,uint256,uint256,uint256,uint256)",
                "fullCreateInput": "creationTemplate || constructorSuffix",
                "returnedRuntime": "runtimeTemplate with each compiler immutableReference span replaced by its constructor value",
                "parameterIsolation": "the independent world changes only the constructor suffix and compiler-declared immutable substitutions",
            },
        },
        "deployment": {
            "parameters": parameters, "manifest": deployment_manifest,
            "broadcastTransaction": transaction, "receipt": receipt,
            "createAddressDerivation": {"formula": "last20(keccak256(rlp([sender, nonce])))",
                                        "sender": sender, "nonce": nonce, "derivedAddress": derived},
            "returnedRuntimeEqualsSourcifyOnchain": True,
            "constructorEffects": {"persistentWrites": ["pauseDuration", "heartbeatInterval"],
                                   "transientWrites": [], "externalCalls": [],
                                   "eventOrder": ["CircuitBreakerInitialized", "PauseDurationUpdated",
                                                  "HeartbeatIntervalUpdated"]},
        },
        "sourcify": {
            "address": sourcify["address"], "chainId": sourcify["chainId"], "match": sourcify["match"],
            "creationMatch": sourcify["creationMatch"], "runtimeMatch": sourcify["runtimeMatch"],
            "verifiedAt": sourcify["verifiedAt"], "canonicalResponseSha256": sha256(compact(sourcify)),
            "metadataSha256": sha256(compact(sourcify["metadata"])), "deployment": sourcify["deployment"],
        },
        "formalReport": {
            "commit": REPORT_COMMIT, "gitBlob": "626ad7914bf9e8b946fe5d79f3749a5916413498",
            "sha256": sha256(report), "vendoredEncoding": f"base64:{REPORT_FILE}",
            "decodedByteLength": len(report), "date": "2026-04-06",
            "tools": {"CertoraProver": "8.8.1", "Bastion": "2.3.6"}, "modelFork": "Cancun",
            "properties": {"reported": 41, "verified": 38},
            "unresolved": ["CB-3a membershipEquivalence_registerPauser",
                           "CB-6a cleanStateAfterRemoval_registerPauser",
                           "CB-8a globalCountConservation_registerPauser"],
            "assumptions": ["pauseFor(uint256) and isPaused() summarized independently and nondeterministically",
                            "optimistic_fallback enabled for unresolved calls and labelled unsafe"],
            "unavailableEvidence": ["audit repository", "CVL/harness/config", "raw campaign runs"],
            "scopeQualification": "The report is not a verification result for the deployed CircuitBreaker as a whole; CircuitBreaker.sol changed materially after mitigation.",
        },
    }


def generate(check: bool) -> None:
    built = build()
    try:
        validate_lock_schema(built, "offline-derived lock")
    except LockSchemaError as exc:
        fail(f"offline-derived lock violates independent schema: {exc}")
    expected = canonical(built)
    if check:
        try:
            actual = LOCK.read_bytes()
        except OSError as exc:
            fail(f"generated lock missing: {exc}")
        parsed = strict_json(actual, "committed generated lock")
        try:
            validate_lock_schema(parsed, "committed generated lock")
        except LockSchemaError as exc:
            fail(f"committed generated lock violates independent schema: {exc}")
        expect(actual == canonical(parsed), "generated lock is not canonical JSON")
        expect(parsed == built and actual == expected, "generated lock differs from offline-derived content")
        print("OK — Lido CircuitBreaker reference lock: schema v2, 17 selectors, 2 parameter worlds")
    else:
        LOCK.write_bytes(expected)
        print(f"wrote {LOCK}")


def download(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"user-agent": "Blanc-Lido-reference/2"})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def refresh() -> None:
    """Explicit networked reacquisition; ordinary ``check`` never calls here."""
    with tempfile.TemporaryDirectory(prefix="lido-circuit-breaker-refresh-") as temp:
        staging = Path(temp) / "reference" / "lido-circuit-breaker"
        staged_input = staging / "inputs"
        (staged_input / "source").mkdir(parents=True)
        raw_base = f"https://raw.githubusercontent.com/lidofinance/circuit-breaker/{RELEASE_COMMIT}/"
        acquisitions = {
            "source/CircuitBreaker.sol": raw_base + "src/CircuitBreaker.sol",
            "source/Registry.sol": raw_base + "src/Registry.sol",
            "foundry.toml": raw_base + "foundry.toml",
            "deployed.mainnet.json": raw_base + "deployed.mainnet.json",
            "deploy-params-mainnet.json": raw_base + "deploy-params/mainnet.json",
        }
        for relative, url in acquisitions.items():
            (staged_input / relative).write_bytes(download(url))
        broadcast_raw = download(raw_base + "broadcast/Deploy.s.sol/1/run-1777555338679.json")
        broadcast_name = "production-broadcast-86ba620554c9202efa086459db529b061e226143.json.b64"
        (staged_input / broadcast_name).write_bytes(base64.encodebytes(broadcast_raw))
        strict_json(broadcast_raw, "downloaded production broadcast")
        (staged_input / "production-broadcast.json").write_bytes(broadcast_raw + b"\n")
        sourcify_raw = download(SOURCIFY_URL)
        sourcify = strict_json(sourcify_raw, "downloaded Sourcify response")
        (staged_input / "sourcify-v2.json").write_bytes(sourcify_raw + b"\n")
        (staged_input / "std-json-input.json").write_bytes(canonical(sourcify["stdJsonInput"]))
        (staged_input / "std-json-output.json").write_bytes(canonical(sourcify["stdJsonOutput"]))
        compiler_input = copy.deepcopy(sourcify["stdJsonInput"])
        compiler_input["settings"]["outputSelection"] = {
            "src/CircuitBreaker.sol": {"CircuitBreaker": [
                "abi", "devdoc", "evm.bytecode.linkReferences", "evm.bytecode.object",
                "evm.bytecode.sourceMap", "evm.deployedBytecode.immutableReferences",
                "evm.deployedBytecode.linkReferences", "evm.deployedBytecode.object",
                "evm.deployedBytecode.sourceMap", "metadata", "storageLayout",
                "transientStorageLayout", "userdoc"]}}
        (staged_input / "compiler-input.json").write_bytes(canonical(compiler_input))
        manifest = strict_json(download(SOLC_LIST_URL), "downloaded solc manifest")
        release = next((row for row in manifest["builds"] if row.get("path") == SOLC_FILE), None)
        expect(isinstance(release, dict), "official solc manifest lacks pinned 0.8.34 build")
        (staged_input / "solc-emscripten-wasm32-release.json").write_bytes(canonical(release))
        report_url = (f"https://raw.githubusercontent.com/lidofinance/audits/{REPORT_COMMIT}/"
                      + urllib.parse.quote(REPORT_PATH))
        report = download(report_url)
        encoded = base64.encodebytes(report)
        (staged_input / REPORT_FILE).write_bytes(encoded)

        staged_lock = Path(temp) / "lido-circuit-breaker-reference.json"
        environment = dict(os.environ, LIDO_CIRCUIT_BREAKER_REFERENCE_DIR=str(staging),
                           LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK=str(staged_lock),
                           PYTHONDONTWRITEBYTECODE="1")
        subprocess.run([sys.executable, str(Path(__file__).resolve()), "generate"],
                       cwd=ROOT, env=environment, check=True)
        subprocess.run([sys.executable, str(Path(__file__).resolve()), "check"],
                       cwd=ROOT, env=environment, check=True)
        for path in sorted(staged_input.rglob("*")):
            if path.is_file():
                destination = INPUT / path.relative_to(staged_input)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, destination)
        shutil.copy2(staged_lock, LOCK)
    generate(True)
    print("refreshed and validated pinned Lido CircuitBreaker inputs")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("generate", "check", "refresh"))
    args = parser.parse_args()
    if args.command == "refresh":
        refresh()
    else:
        generate(args.command == "check")


if __name__ == "__main__":
    try:
        main()
    except (ReferenceError, LockSchemaError, OSError, KeyError, TypeError, ValueError,
            subprocess.CalledProcessError, urllib.error.URLError) as exc:
        raise SystemExit(f"lido-circuit-breaker-reference.py: {exc}")
