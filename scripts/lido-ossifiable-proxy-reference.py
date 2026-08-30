#!/usr/bin/env python3
"""Generate/check the fail-closed offline Lido OssifiableProxy reference.

`generate` and `check` are network-free.  Both validate an exact input-tree
membership contract and run the vendored solc 0.8.9 compiler over the vendored
Standard JSON input.  `refresh-rpc` is the only network command; it writes
candidate captures outside the authority tree and never admits them.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from lido_ossifiable_proxy_reference_schema import (
    SchemaError as LockSchemaError,
    keccak256,
    validate_lock_schema,
)


ROOT = Path(__file__).resolve().parents[1]
REF = Path(os.environ.get(
    "LIDO_OSSIFIABLE_PROXY_REFERENCE_DIR",
    ROOT / "scripts" / "reference" / "lido-ossifiable-proxy",
))
INPUT = REF / "inputs"
LOCK = Path(os.environ.get(
    "LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK",
    ROOT / "scripts" / "lido-ossifiable-proxy-reference.json",
))

TARGET_SOURCE = "contracts/0.8.9/proxy/OssifiableProxy.sol"
TARGET_CONTRACT = "OssifiableProxy"
TARGET_ADDRESS = "0x889edC2eDab5f40e902b864aD4d7AdE8E412F9B1"
TARGET_ADDRESS_LOWER = TARGET_ADDRESS.lower()
TARGET_TX = "0x98c2170be034f750f5006cb69ea0aeeaf0858b11f6324ee53d582fa4dd49bc1a"
TARGET_BLOCK = 17172547
TARGET_BLOCK_HEX = "0x1060843"
TARGET_BLOCK_HASH = "0x4fa4c03c69ad9b863fcd43b32cc063769d8b6a142a2aa8063a7c246feb5732a6"
TARGET_TIMESTAMP = 1683023927
IMPLEMENTATION = "0x6F6541C2203196fEeDd14CD2C09550dA1CbEDa31"
ADMIN = "0x8Ea83AD72396f1E0cD2f8E72b1461db8Eb6aF7B5"
IMPLEMENTATION_SLOT = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"
ADMIN_SLOT = "0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103"

SOLC_FILE = "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js"
SOLC_LONG_VERSION = "0.8.9+commit.e5eed63a"
SOLC_SHA256 = "5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c"
SOLC_KECCAK256 = "0xbc470ab3442e78bb4d3f16c01c39b2f160f4f34eb4373efed11c234e1c7f6ca0"
SOLC_SIZE = 26173264

PINNED_INPUT_SHA256 = {
    "git-provenance.json": "bc4d4625b001b4006b69990eade7dc412fd37e42d673670919de140a6160ec51",
    "lido/contracts/COMPILERS.md": "888504aefff340b47cd49f5b299fd3d3055c70ab56222098a961be87ef49e4b8",
    "lido/deployed-mainnet.json": "3428ba7a845ae27c69bd64d87dafda920df3fdfdc8df99da1caf3af55060fd15",
    "lido/hardhat.config.ts": "29b3e91ff197c0ea1df5b6401cc12982d3f684e7bf3e68b380096fe33e43b223",
    "lido/package.json": "5e6bd056082e23c6628aee085df5ce0743070d08d5a3e27496991e09f74b638e",
    "lido/yarn.lock": "d17f979eed36218b0bed85cf560bdc2e5d182e0c67aff6eabf2c68be8597c921",
    "rpc-blastapi.json": "bcd86c8bcd5bf2e9ddcd1ec0da9fdbb4f9041ff3f4d765b1ce1bcf6b413514dc",
    "rpc-drpc.json": "bfaca0cc02c01a3dbe93d395bebf60d166e4fcd163abd7b852f4e80108851451",
    "solc-emscripten-wasm32-list.json": "0ee86d7e0a30f0d90593ff64dfb56d192c514c8e33feebeb54446be55b12e5ad",
    SOLC_FILE: SOLC_SHA256,
    "source/@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Proxy.sol": "db6c986d393626060fa219d1072a1913eb16872224307e9261fc90c296e3770d",
    "source/@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol": "a8e55634074e89c6925a57f3274aebca184bfc99ffca39967ce967696f49dbe9",
    "source/@openzeppelin/contracts-v4.4/proxy/Proxy.sol": "f3750834a47fd89ab623ba00877c556895bb71f203e615da9987697cbabbeed6",
    "source/@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol": "6afea1d83856ed8e0495fe78109f674f925cfdc79fe2e24e854b1237e742f011",
    "source/@openzeppelin/contracts-v4.4/utils/Address.sol": "0228dd7c0a0d1342b88eab6e5a4a07ae4350818ba1650be0a374064b02218f37",
    "source/@openzeppelin/contracts-v4.4/utils/StorageSlot.sol": "b8d43f55a3afc09327fb9d802f714a8bec64e3a259ad42f5b3d877deb29aaaef",
    "source/contracts/0.8.9/proxy/OssifiableProxy.sol": "3fb48bc4a40c887dd581178d05316745c1b1c393a8e64787ef2a7075f1e7ce6d",
    "standard-json-input.json": "909192afb8f11b501e17c6f17537c7806ad3b8bb019abb668d096a97eb114803",
    "standard-json-output.json": "1fdc74b9d5f6485e82a45127114fc88d7698360372d2eb5f30ee73e722b1caa9",
}

SOURCE_INPUTS = {
    "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Proxy.sol":
        "source/@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Proxy.sol",
    "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol":
        "source/@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol",
    "@openzeppelin/contracts-v4.4/proxy/Proxy.sol":
        "source/@openzeppelin/contracts-v4.4/proxy/Proxy.sol",
    "@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol":
        "source/@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol",
    "@openzeppelin/contracts-v4.4/utils/Address.sol":
        "source/@openzeppelin/contracts-v4.4/utils/Address.sol",
    "@openzeppelin/contracts-v4.4/utils/StorageSlot.sol":
        "source/@openzeppelin/contracts-v4.4/utils/StorageSlot.sol",
    TARGET_SOURCE: "source/contracts/0.8.9/proxy/OssifiableProxy.sol",
}

PINNED_GIT_BLOBS = {
    "lido/contracts/COMPILERS.md": "4a7cc445ea7854a6f25931d213ab66ad037cb6ae",
    "lido/deployed-mainnet.json": "1aa9165e97936ef1020ac873115ba35c3b94dd28",
    "lido/hardhat.config.ts": "8156497feda3a05d0142d53cc99f9212ea3f3ee1",
    "lido/package.json": "2d9084a710482ff6957241ba4d64eb42b15bc8dc",
    "lido/yarn.lock": "b5939dc1dfac88bcdb4786c7c99344e4fb556a5e",
    "source/@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Proxy.sol": "64e9d9f6f317c3bd1135a122822965508cbdd3fa",
    "source/@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol": "036782fc7a0f288c6adf717dfde889ef416f8f68",
    "source/@openzeppelin/contracts-v4.4/proxy/Proxy.sol": "81351613004d76bdaceacbee9d02f68a0d69e4b9",
    "source/@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol": "fba3ee2ab4546832599b0498c4945c9f81d50791",
    "source/@openzeppelin/contracts-v4.4/utils/Address.sol": "9e5e887409ff86e2c0db7abf9b30ba4640e46ce1",
    "source/@openzeppelin/contracts-v4.4/utils/StorageSlot.sol": "28239dbc35a2c45a91958e1b654143a7690b2a2b",
    "source/contracts/0.8.9/proxy/OssifiableProxy.sol": "d4ccec05c453b15cc17023e3950e44341a66a4a4",
}

BUILD_FILES = {
    "lido/contracts/COMPILERS.md": "contracts/COMPILERS.md",
    "lido/deployed-mainnet.json": "deployed-mainnet.json",
    "lido/hardhat.config.ts": "hardhat.config.ts",
    "lido/package.json": "package.json",
    "lido/yarn.lock": "yarn.lock",
}

FUNCTION_ORDER = [
    "proxy__getAdmin()",
    "proxy__getImplementation()",
    "proxy__getIsOssified()",
    "proxy__ossify()",
    "proxy__changeAdmin(address)",
    "proxy__upgradeTo(address)",
    "proxy__upgradeToAndCall(address,bytes,bool)",
]

PINNED_SELECTORS = {
    "proxy__getAdmin()": "0x916f1fd7",
    "proxy__getImplementation()": "0xad729a71",
    "proxy__getIsOssified()": "0x13351258",
    "proxy__ossify()": "0xadcbc237",
    "proxy__changeAdmin(address)": "0x773f5be8",
    "proxy__upgradeTo(address)": "0x3ebdd0eb",
    "proxy__upgradeToAndCall(address,bytes,bool)": "0xd2f6ed4d",
}

BEHAVIORAL_EVENT_ORDER = [
    "Upgraded(address)", "AdminChanged(address,address)", "ProxyOssified()",
]

PINNED_TOPICS = {
    "Upgraded(address)": "0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b",
    "AdminChanged(address,address)": "0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f",
    "ProxyOssified()": "0x158b204828f9326d9bb3c2be9336986c14911b4a72b93d1801f207aac3c68b9f",
}

ERROR_ORDER = ["NotAdmin()", "ProxyIsOssified()"]
PINNED_ERRORS = {"NotAdmin()": "0x7bfa4b9f", "ProxyIsOssified()": "0xb83646a9"}

REASON_LOCATIONS = [
    ("ERC1967: new admin is the zero address",
     "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol", "_setAdmin"),
    ("ERC1967: new implementation is not a contract",
     "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol", "_setImplementation"),
    ("Address: low-level delegate call failed",
     "@openzeppelin/contracts-v4.4/utils/Address.sol", "functionDelegateCall"),
]

RPC_OPERATORS = {
    "blastapi": ("BlastAPI", "https://eth-mainnet.public.blastapi.io"),
    "drpc": ("dRPC", "https://eth.drpc.org"),
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
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


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
    expect(isinstance(value, str) and value.startswith("0x"), f"{what}: expected 0x hex")
    body = value[2:]
    expect(len(body) % 2 == 0 and all(char in "0123456789abcdefABCDEF" for char in body),
           f"{what}: malformed hexadecimal")
    return bytes.fromhex(body)


def byte_artifact(raw: bytes) -> dict[str, Any]:
    return {
        "byteLength": len(raw),
        "hex": "0x" + raw.hex(),
        "keccak256": "0x" + keccak256(raw),
        "sha256": sha256(raw),
    }


def validate_input_pins() -> list[dict[str, str]]:
    actual = sorted(str(path.relative_to(INPUT)) for path in INPUT.rglob("*") if path.is_file())
    expected = sorted(PINNED_INPUT_SHA256)
    expect(actual == expected,
           f"authoritative input inventory differs\nexpected: {expected}\nfound: {actual}")
    rows = []
    for relative in actual:
        data = (INPUT / relative).read_bytes()
        digest = sha256(data)
        expect(digest == PINNED_INPUT_SHA256[relative],
               f"authoritative input SHA-256 differs for {relative}: {digest}")
        if relative in PINNED_GIT_BLOBS:
            expect(git_blob(data) == PINNED_GIT_BLOBS[relative],
                   f"authoritative Git blob differs for {relative}")
        rows.append({"path": relative, "sha256": digest})
    return rows


def compiler_runner() -> tuple[str, str]:
    configured_jsc = os.environ.get("JSC")
    configured_node = os.environ.get("NODE")
    if configured_jsc and Path(configured_jsc).is_file() and os.access(configured_jsc, os.X_OK):
        return "jsc", configured_jsc
    if configured_node and Path(configured_node).is_file() and os.access(configured_node, os.X_OK):
        return "node", configured_node
    default_jsc = "/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc"
    if Path(default_jsc).is_file() and os.access(default_jsc, os.X_OK):
        return "jsc", default_jsc
    node = shutil.which("node")
    if node:
        return "node", node
    fail("offline recompilation requires JavaScriptCore (set JSC) or Node.js (set NODE)")


def run_vendored_solc() -> bytes:
    soljson = INPUT / SOLC_FILE
    standard_input = INPUT / "standard-json-input.json"
    kind, executable = compiler_runner()
    with tempfile.TemporaryDirectory(prefix="ossifiable-solc-") as temporary:
        driver = Path(temporary) / ("compile.js" if kind == "jsc" else "compile.cjs")
        if kind == "jsc":
            driver.write_text(
                "globalThis.console={log:print,warn:print,error:print,info:print,debug:print};"
                "globalThis.Module={print:function(){},printErr:function(){}};"
                "var argv=arguments;load(argv[0]);"
                "if(typeof drainMicrotasks===\"function\")drainMicrotasks();"
                "var c=Module.cwrap(\"solidity_compile\",\"string\","
                "[\"string\",\"number\",\"number\"]);print(c(read(argv[1]),0,0));")
            command = [executable, str(driver), "--", str(soljson), str(standard_input)]
        else:
            driver.write_text(
                "const fs=require('fs');const Module=require(process.argv[2]);"
                "const c=Module.cwrap('solidity_compile','string',['string','number','number']);"
                "process.stdout.write(c(fs.readFileSync(process.argv[3],'utf8'),0,0)+'\\n');")
            command = [executable, str(driver), str(soljson), str(standard_input)]
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    expect(result.returncode == 0,
           f"vendored solc failed with {kind} exit {result.returncode}: {result.stderr.decode(errors='replace')}")
    return result.stdout


def resolve_import(unit: str, imported: str) -> str:
    if imported.startswith("."):
        return posixpath.normpath(posixpath.join(posixpath.dirname(unit), imported))
    return posixpath.normpath(imported)


IMPORT_RE = re.compile(r'import\s+(?:[^"\']*?\s+from\s+)?["\']([^"\']+)["\']\s*;')


def derive_source_closure(source_text: dict[str, str]) -> set[str]:
    visited: set[str] = set()
    pending = [TARGET_SOURCE]
    while pending:
        unit = pending.pop()
        expect(unit in source_text, f"import closure references missing source {unit}")
        if unit in visited:
            continue
        visited.add(unit)
        for imported in IMPORT_RE.findall(source_text[unit]):
            pending.append(resolve_import(unit, imported))
    return visited


def source_inventory(standard: dict[str, Any]) -> list[dict[str, Any]]:
    expect(set(standard.get("sources", {})) == set(SOURCE_INPUTS),
           "Standard JSON source membership differs from the exact seven-source closure")
    text_by_unit: dict[str, str] = {}
    rows = []
    for source_unit, input_path in sorted(SOURCE_INPUTS.items()):
        data = (INPUT / input_path).read_bytes()
        try:
            text = data.decode()
        except UnicodeDecodeError as exc:
            fail(f"source is not UTF-8: {source_unit}: {exc}")
        expect(standard["sources"][source_unit] == {"content": text},
               f"source snapshot differs from Standard JSON content: {source_unit}")
        text_by_unit[source_unit] = text
        rows.append({
            "byteLength": len(data),
            "gitBlob": PINNED_GIT_BLOBS[input_path],
            "inputPath": input_path,
            "keccak256": "0x" + keccak256(data),
            "sha256": sha256(data),
            "sourceUnit": source_unit,
        })
    expect(derive_source_closure(text_by_unit) == set(SOURCE_INPUTS),
           "recursive import closure differs from Standard JSON source membership")
    return rows


def contract_output(output: dict[str, Any]) -> dict[str, Any]:
    try:
        return output["contracts"][TARGET_SOURCE][TARGET_CONTRACT]
    except (KeyError, TypeError) as exc:
        fail(f"compiler output lacks {TARGET_SOURCE}:{TARGET_CONTRACT}: {exc}")


def abi_signature(entry: dict[str, Any]) -> str:
    return f"{entry['name']}({','.join(argument['type'] for argument in entry.get('inputs', []))})"


def abi_inventory(raw_abi: Any) -> dict[str, Any]:
    expect(isinstance(raw_abi, list), "compiler ABI is not an array")
    constructors = [entry for entry in raw_abi if entry.get("type") == "constructor"]
    fallbacks = [entry for entry in raw_abi if entry.get("type") == "fallback"]
    receives = [entry for entry in raw_abi if entry.get("type") == "receive"]
    function_entries = {abi_signature(entry): entry for entry in raw_abi if entry.get("type") == "function"}
    error_entries = {abi_signature(entry): entry for entry in raw_abi if entry.get("type") == "error"}
    event_entries = {abi_signature(entry): entry for entry in raw_abi if entry.get("type") == "event"}
    expect(len(constructors) == len(fallbacks) == len(receives) == 1,
           "ABI must have exactly one constructor, fallback, and receive")
    expect(set(function_entries) == set(FUNCTION_ORDER), "ABI named-function inventory differs")
    expect(set(error_entries) == set(ERROR_ORDER), "ABI custom-error inventory differs")
    expect(set(event_entries) == {
        "AdminChanged(address,address)", "BeaconUpgraded(address)",
        "ProxyOssified()", "Upgraded(address)",
    }, "compiler ABI event declarations differ")

    functions = []
    for signature in FUNCTION_ORDER:
        entry = function_entries[signature]
        selector = "0x" + keccak256(signature.encode())[:8]
        expect(selector == PINNED_SELECTORS[signature], f"selector differs for {signature}")
        mutability = entry.get("stateMutability")
        expect(mutability in {"view", "nonpayable"}, f"named endpoint is unexpectedly payable: {signature}")
        functions.append({
            "acceptsValue": False,
            "classification": "functional-interface",
            "entry": entry,
            "returnTypes": [row["type"] for row in entry.get("outputs", [])],
            "selector": selector,
            "signature": signature,
        })
    expect(len({row["selector"] for row in functions}) == 7, "named selector collision")

    errors = []
    for signature in ERROR_ORDER:
        selector = "0x" + keccak256(signature.encode())[:8]
        expect(selector == PINNED_ERRORS[signature], f"custom-error selector differs for {signature}")
        errors.append({"entry": error_entries[signature], "selector": selector, "signature": signature})

    compiler_events = []
    for signature in sorted(event_entries):
        entry = event_entries[signature]
        compiler_events.append({
            "entry": entry,
            "indexed": [row["indexed"] for row in entry["inputs"]],
            "signature": signature,
            "topic0": "0x" + keccak256(signature.encode()),
        })
    by_event = {row["signature"]: row for row in compiler_events}
    behavioral_events = [by_event[signature] for signature in BEHAVIORAL_EVENT_ORDER]
    for row in behavioral_events:
        expect(row["topic0"] == PINNED_TOPICS[row["signature"]],
               f"event topic differs for {row['signature']}")

    constructor = constructors[0]
    constructor_inputs = constructor.get("inputs", [])
    expect(constructor.get("stateMutability") == "nonpayable",
           "derived constructor must be nonpayable despite payable base constructor")
    expect([row["type"] for row in constructor_inputs] == ["address", "address", "bytes"],
           "constructor ABI types differ")
    expect([row["name"] for row in constructor_inputs] == ["implementation_", "admin_", "data_"],
           "constructor ABI names differ")
    expect(fallbacks[0] == {"stateMutability": "payable", "type": "fallback"},
           "payable fallback ABI differs")
    expect(receives[0] == {"stateMutability": "payable", "type": "receive"},
           "payable receive ABI differs")

    boundaries = [{
        "abiHeadBytes": 96,
        "canonicalEmptyEncodingBytes": 128,
        "dynamicArguments": [{"headIndex": 2, "offsetBase": "constructor-suffix", "type": "bytes"}],
        "nonpayableValueRejectedBeforeBody": True,
        "signature": "constructor(address,address,bytes)",
        "wordConstraints": ["address-high-96-bits-zero", "address-high-96-bits-zero", "dynamic-offset-and-length-in-bounds"],
    }]
    for row in functions:
        signature = row["signature"]
        if signature == "proxy__upgradeToAndCall(address,bytes,bool)":
            boundary = {
                "abiHeadBytes": 96, "minimumCanonicalCalldataBytes": 132,
                "dynamicArguments": [{"headIndex": 1, "offsetBase": "after-selector", "type": "bytes"}],
                "wordConstraints": ["address-high-96-bits-zero", "dynamic-offset-and-length-in-bounds", "bool-is-zero-or-one"],
            }
        elif "(address)" in signature:
            boundary = {
                "abiHeadBytes": 32, "minimumCanonicalCalldataBytes": 36,
                "dynamicArguments": [], "wordConstraints": ["address-high-96-bits-zero"],
            }
        else:
            boundary = {
                "abiHeadBytes": 0, "minimumCanonicalCalldataBytes": 4,
                "dynamicArguments": [], "wordConstraints": [],
            }
        boundaries.append({
            **boundary,
            "nonpayableValueRejectedBeforeBody": True,
            "selectorBytes": 4,
            "signature": signature,
            "trailingCalldataAccepted": True,
        })
    boundaries.extend([
        {"acceptedCalldata": "any unmatched or short calldata", "payable": True,
         "signature": "fallback", "selectorExclusions": [PINNED_SELECTORS[key] for key in FUNCTION_ORDER]},
        {"acceptedCalldata": "empty calldata", "payable": True, "signature": "receive"},
    ])

    return {
        "abiOnlyDeclarations": [{
            "behavioralSurface": False,
            "reason": "compiler ABI reports an inherited event whose internal beacon-upgrade emitter has no OssifiableProxy external or constructor path",
            "signature": "BeaconUpgraded(address)",
        }],
        "behavioralEvents": behavioral_events,
        "compilerEvents": compiler_events,
        "constructor": {
            "argumentNames": [row["name"] for row in constructor_inputs],
            "argumentTypes": [row["type"] for row in constructor_inputs],
            "entry": constructor,
            "nonpayableValueRejected": True,
            "payable": False,
        },
        "counts": {
            "abiDeclarations": len(raw_abi), "behavioralEvents": 3, "compilerEvents": 4,
            "constructors": 1, "customErrors": 2, "fallback": 1,
            "functions": 7, "receive": 1,
        },
        "decodingBoundaries": boundaries,
        "dispatchSelectorsUnique": True,
        "errors": errors,
        "fallback": {"acceptsValue": True, "classification": "functional-interface",
                     "entry": fallbacks[0], "signature": "fallback"},
        "functions": functions,
        "raw": raw_abi,
        "rawSha256": sha256(compact(raw_abi)),
        "receive": {"acceptsValue": True, "classification": "functional-interface",
                    "entry": receives[0], "signature": "receive"},
    }


def encode_error_string(message: str) -> str:
    raw = message.encode()
    padded = raw + b"\0" * ((32 - len(raw) % 32) % 32)
    payload = (bytes.fromhex("08c379a0") + (32).to_bytes(32, "big")
               + len(raw).to_bytes(32, "big") + padded)
    return "0x" + payload.hex()


def source_behavior(source_rows: list[dict[str, Any]]) -> dict[str, Any]:
    texts = {row["sourceUnit"]: (INPUT / row["inputPath"]).read_text() for row in source_rows}
    target = texts[TARGET_SOURCE]
    expect(target.count("pragma solidity 0.8.9;") == 1, "target exact pragma differs")
    expect("constructor(\n        address implementation_,\n        address admin_,\n        bytes memory data_\n    ) ERC1967Proxy" in target,
           "derived constructor declaration or nonpayability differs")
    expect("function proxy__upgradeToAndCall(" in target and ") external onlyAdmin {" in target,
           "upgradeToAndCall declaration differs")
    expect("external payable onlyAdmin" not in target, "named endpoint unexpectedly accepts value")
    expect(target.index("if (admin == address(0))") < target.index("if (admin != msg.sender)"),
           "onlyAdmin precedence differs")
    expect(target.index("emit AdminChanged(prevAdmin, address(0));") < target.index("emit ProxyOssified();"),
           "ossification event order differs")
    upgrade = texts["@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol"]
    expect(IMPLEMENTATION_SLOT[2:] in upgrade and ADMIN_SLOT[2:] in upgrade,
           "ERC-1967 slot literals differ")
    reasons = []
    for message, unit, owner in REASON_LOCATIONS:
        expect(texts[unit].count(f'"{message}"') == 1,
               f"source reason string missing or duplicated in executable source: {message}")
        reasons.append({
            "message": message,
            "owner": owner,
            "payload": encode_error_string(message),
            "selector": "0x08c379a0",
            "sourceUnit": unit,
        })
    return {
        "authorizationOrder": [
            "admin == address(0) -> ProxyIsOssified()",
            "admin != msg.sender -> NotAdmin()",
            "authorized body",
        ],
        "constructorOrder": [
            "validate and write implementation", "emit Upgraded(address)",
            "optional setup delegatecall", "read post-setup admin",
            "emit AdminChanged(address,address)", "validate nonzero admin", "write admin",
        ],
        "reasonStrings": reasons,
        "slots": [
            {"classification": "functional-interoperability", "name": "implementation", "value": IMPLEMENTATION_SLOT},
            {"classification": "functional-interoperability", "name": "admin", "value": ADMIN_SLOT},
        ],
    }


def encode_constructor(arguments: list[str]) -> bytes:
    expect(len(arguments) == 3 and arguments[2] == "0x", "only canonical empty-data tuple expected")
    implementation = hex_bytes(arguments[0], "constructor implementation")
    admin = hex_bytes(arguments[1], "constructor admin")
    expect(len(implementation) == len(admin) == 20, "constructor addresses must be 20 bytes")
    return (implementation.rjust(32, b"\0") + admin.rjust(32, b"\0")
            + (96).to_bytes(32, "big") + (0).to_bytes(32, "big"))


def rlp_string(raw: bytes) -> bytes:
    if len(raw) == 1 and raw[0] < 0x80:
        return raw
    if len(raw) <= 55:
        return bytes([0x80 + len(raw)]) + raw
    length = len(raw).to_bytes((len(raw).bit_length() + 7) // 8, "big")
    return bytes([0xB7 + len(length)]) + length + raw


def create_address(sender: str, nonce: int) -> str:
    sender_raw = hex_bytes(sender, "CREATE sender")
    expect(len(sender_raw) == 20 and nonce >= 0, "invalid CREATE sender/nonce")
    nonce_raw = b"" if nonce == 0 else nonce.to_bytes((nonce.bit_length() + 7) // 8, "big")
    payload = rlp_string(sender_raw) + rlp_string(nonce_raw)
    encoded = bytes([0xC0 + len(payload)]) + payload
    return "0x" + keccak256(encoded)[-40:]


def expected_rpc_requests() -> list[tuple[str, dict[str, Any]]]:
    return [
        ("transaction", {"id": 1, "jsonrpc": "2.0", "method": "eth_getTransactionByHash", "params": [TARGET_TX]}),
        ("receipt", {"id": 2, "jsonrpc": "2.0", "method": "eth_getTransactionReceipt", "params": [TARGET_TX]}),
        ("block", {"id": 3, "jsonrpc": "2.0", "method": "eth_getBlockByHash", "params": [TARGET_BLOCK_HASH, False]}),
        ("code", {"id": 4, "jsonrpc": "2.0", "method": "eth_getCode", "params": [TARGET_ADDRESS_LOWER, TARGET_BLOCK_HEX]}),
    ]


def parse_rpc_record(path: Path, creation: bytes, runtime: bytes) -> dict[str, Any]:
    record_bytes = path.read_bytes()
    record = strict_json(record_bytes, str(path))
    expect(isinstance(record, dict) and set(record) == {"captureDateUtc", "captures", "operator", "schema"},
           f"{path.name}: RPC record shape differs")
    expect(record["schema"] == 1 and type(record["schema"]) is int,
           f"{path.name}: RPC schema differs")
    operator = record["operator"]
    expect(isinstance(operator, dict) and set(operator) == {"name", "url"},
           f"{path.name}: operator shape differs")
    key = path.stem.removeprefix("rpc-")
    expect(key in RPC_OPERATORS and (operator["name"], operator["url"]) == RPC_OPERATORS[key],
           f"{path.name}: operator identity differs")
    expect(re.fullmatch(r"20[0-9]{2}-[0-9]{2}-[0-9]{2}", record["captureDateUtc"] or "") is not None,
           f"{path.name}: capture date is malformed")
    captures = record["captures"]
    requests = expected_rpc_requests()
    expect(isinstance(captures, list) and len(captures) == len(requests),
           f"{path.name}: must contain four raw RPC captures")
    results: dict[str, Any] = {}
    response_hashes: dict[str, str] = {}
    for index, ((label, request), capture) in enumerate(zip(requests, captures)):
        expect(isinstance(capture, dict)
               and set(capture) == {"label", "request", "responseRaw", "responseSha256"},
               f"{path.name}: capture {index} shape differs")
        expect(capture["label"] == label and capture["request"] == request,
               f"{path.name}: {label} request differs")
        raw = capture["responseRaw"]
        expect(isinstance(raw, str)
               and sha256(raw.encode()) == capture["responseSha256"],
               f"{path.name}: {label} raw-response SHA-256 differs")
        envelope = strict_json(raw, f"{path.name} {label} raw response")
        expect(isinstance(envelope, dict) and envelope.get("jsonrpc") == "2.0"
               and envelope.get("id") == request["id"] and "error" not in envelope
               and envelope.get("result") is not None,
               f"{path.name}: {label} JSON-RPC response failed or mismatched")
        results[label] = envelope["result"]
        response_hashes[label] = capture["responseSha256"]

    transaction = results["transaction"]
    receipt = results["receipt"]
    block = results["block"]
    code = hex_bytes(results["code"], f"{path.name} code")
    tx_input = hex_bytes(transaction.get("input"), f"{path.name} transaction input")
    expect(transaction.get("hash") == TARGET_TX and transaction.get("to") is None,
           f"{path.name}: transaction is not the pinned contract creation")
    expect(transaction.get("blockHash") == TARGET_BLOCK_HASH
           and transaction.get("blockNumber") == TARGET_BLOCK_HEX,
           f"{path.name}: transaction block differs")
    expect(transaction.get("value") == "0x0", f"{path.name}: nonpayable constructor carried value")
    expect(tx_input[:len(creation)] == creation and len(tx_input) == 4335,
           f"{path.name}: transaction creation prefix/boundary differs")
    expect(receipt.get("transactionHash") == TARGET_TX and receipt.get("status") == "0x1"
           and receipt.get("contractAddress", "").lower() == TARGET_ADDRESS_LOWER,
           f"{path.name}: receipt identity/status/address differs")
    expect(receipt.get("blockHash") == TARGET_BLOCK_HASH
           and receipt.get("blockNumber") == TARGET_BLOCK_HEX
           and int(receipt.get("gasUsed", "0x0"), 16) == 669988,
           f"{path.name}: receipt block/gas differs")
    logs = receipt.get("logs")
    expect(isinstance(logs, list) and len(logs) == 2
           and logs[0].get("topics", [None])[0] == PINNED_TOPICS["Upgraded(address)"]
           and logs[1].get("topics", [None])[0] == PINNED_TOPICS["AdminChanged(address,address)"],
           f"{path.name}: constructor event sequence differs")
    expect(block.get("hash") == TARGET_BLOCK_HASH and block.get("number") == TARGET_BLOCK_HEX
           and int(block.get("timestamp", "0x0"), 16) == TARGET_TIMESTAMP,
           f"{path.name}: block header identity differs")
    transactions = block.get("transactions")
    tx_index = int(transaction.get("transactionIndex", "-1"), 16)
    expect(isinstance(transactions, list) and transactions.count(TARGET_TX) == 1
           and 0 <= tx_index < len(transactions) and transactions[tx_index] == TARGET_TX,
           f"{path.name}: full-block transaction membership/index differs")
    expect(code == runtime, f"{path.name}: pinned-block code differs from compiled runtime")
    return {
        "block": block,
        "code": code,
        "envelopeSha256": sha256(record_bytes),
        "file": path.name,
        "operator": operator["name"],
        "receipt": receipt,
        "responseSha256": response_hashes,
        "transaction": transaction,
        "url": operator["url"],
        "captureDateUtc": record["captureDateUtc"],
        "txInput": tx_input,
    }


def rpc_inventory(creation: bytes, runtime: bytes, paths: list[Path] | None = None) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    paths = paths or [INPUT / "rpc-blastapi.json", INPUT / "rpc-drpc.json"]
    parsed = [parse_rpc_record(path, creation, runtime) for path in paths]
    parsed.sort(key=lambda row: row["file"])
    first, second = parsed
    transaction_fields = ("hash", "from", "nonce", "to", "input", "value", "blockHash", "blockNumber", "transactionIndex")
    receipt_fields = ("transactionHash", "contractAddress", "from", "to", "status", "gasUsed", "blockHash", "blockNumber", "transactionIndex", "logs")
    expect({key: first["transaction"].get(key) for key in transaction_fields}
           == {key: second["transaction"].get(key) for key in transaction_fields},
           "independent RPC transactions disagree on pinned fields")
    expect({key: first["receipt"].get(key) for key in receipt_fields}
           == {key: second["receipt"].get(key) for key in receipt_fields},
           "independent RPC receipts disagree on pinned fields")
    first_header = {key: value for key, value in first["block"].items() if key != "transactions"}
    second_header = {key: value for key, value in second["block"].items() if key != "transactions"}
    expect(first_header == second_header, "independent RPC full block headers disagree")
    expect(first["block"]["transactions"] == second["block"]["transactions"],
           "independent RPC block transaction membership lists disagree")
    expect(first["code"] == second["code"] == runtime, "independent RPC code responses disagree")
    summaries = [{
        "captureDateUtc": row["captureDateUtc"],
        "envelopeSha256": row["envelopeSha256"],
        "file": row["file"],
        "operator": row["operator"],
        "responseSha256": row["responseSha256"],
        "url": row["url"],
    } for row in parsed]
    return summaries, {
        "blockHeadersEqual": True,
        "blockMembershipEqual": True,
        "codesEqual": True,
        "receiptsEqualOnPinnedFields": True,
        "transactionsEqualOnPinnedFields": True,
    }


def build() -> dict[str, Any]:
    input_files = validate_input_pins()
    provenance_input = load(INPUT / "git-provenance.json")
    expect(provenance_input.get("schema") == 1
           and provenance_input.get("lido", {}).get("commit") == "17005714f151e5502c559932319a3f2f74ac2436"
           and provenance_input.get("openzeppelin", {}).get("commit") == "6bd6b76d1156e20e45d1016f355d154141c7e5b9",
           "Git provenance commits differ")
    expect(provenance_input["openzeppelin"].get("yarnChecksum") ==
           "10c0/cbff5f130deaa17fade3de7c97a2e755dcc556a97bfc821e04db05f8698c2e5bab109563c1c239211d4fabe96603859ac15ef207f87f648d4c3f1bd3ad645078",
           "OpenZeppelin Yarn package checksum differs")

    package = load(INPUT / "lido/package.json")
    expect(package.get("dependencies", {}).get("@openzeppelin/contracts-v4.4") ==
           "npm:@openzeppelin/contracts@4.4.1", "package alias/resolution differs")
    yarn = (INPUT / "lido/yarn.lock").read_text()
    hardhat = (INPUT / "lido/hardhat.config.ts").read_text()
    compilers = (INPUT / "lido/contracts/COMPILERS.md").read_text()
    expect("10c0/cbff5f130deaa17fade3de7c97a2e755dcc556a97bfc821e04db05f8698c2e5bab109563c1c239211d4fabe96603859ac15ef207f87f648d4c3f1bd3ad645078" in yarn,
           "Yarn lock OpenZeppelin checksum differs")
    expect('version: "0.8.9"' in hardhat and 'evmVersion: "istanbul"' in hardhat
           and hardhat.count("runs: 200") >= 4, "Hardhat 0.8.9 compiler settings differ")
    expect(compilers.startswith("# Compiler Versions Used in Lido Project")
           and "yarn compile" in compilers,
           "Lido compiler-policy document identity/compilation instruction differs")

    standard_input_bytes = (INPUT / "standard-json-input.json").read_bytes()
    standard_output_bytes = (INPUT / "standard-json-output.json").read_bytes()
    standard = strict_json(standard_input_bytes, "Standard JSON input")
    vendored_output = strict_json(standard_output_bytes, "Standard JSON output")
    expect(standard.get("language") == "Solidity" and set(standard) == {"language", "settings", "sources"},
           "Standard JSON top-level shape differs")
    expected_settings = {
        "evmVersion": "istanbul",
        "optimizer": {"enabled": True, "runs": 200},
        "outputSelection": {"*": {"*": [
            "abi", "metadata", "evm.bytecode.object", "evm.deployedBytecode.object",
        ]}},
    }
    expect(standard.get("settings") == expected_settings,
           "exact Standard JSON compiler settings differ")
    source_rows = source_inventory(standard)

    compiler_bytes = (INPUT / SOLC_FILE).read_bytes()
    expect(len(compiler_bytes) == SOLC_SIZE and sha256(compiler_bytes) == SOLC_SHA256,
           "vendored solc bytes differ from the independently verified SHA-256/size pins")
    manifest = load(INPUT / "solc-emscripten-wasm32-list.json")
    release_rows = [row for row in manifest.get("builds", []) if row.get("path") == SOLC_FILE]
    expect(len(release_rows) == 1, "frozen solc manifest must have one exact 0.8.9 build row")
    release = release_rows[0]
    expect(release == {
        "build": "commit.e5eed63a",
        "keccak256": SOLC_KECCAK256,
        "longVersion": SOLC_LONG_VERSION,
        "path": SOLC_FILE,
        "sha256": "0x" + SOLC_SHA256,
        "urls": ["dweb:/ipfs/QmfFq3MvisCSUJy8N8EVsBribgPbdpTZb7tQ2eHYw7dwag"],
        "version": "0.8.9",
    }, "frozen solc manifest release row differs")

    reproduced_output_bytes = run_vendored_solc()
    expect(reproduced_output_bytes == standard_output_bytes,
           "vendored solc output differs byte-for-byte from standard-json-output.json")
    reproduced_output = strict_json(reproduced_output_bytes, "reproduced compiler output")
    expect(reproduced_output == vendored_output, "reproduced compiler JSON differs")
    contract = contract_output(vendored_output)
    metadata = strict_json(contract["metadata"], "target compiler metadata")
    expect(metadata.get("compiler", {}).get("version") == SOLC_LONG_VERSION,
           "compiler metadata version differs")
    metadata_settings = metadata.get("settings")
    expect(metadata_settings == {
        "compilationTarget": {TARGET_SOURCE: TARGET_CONTRACT},
        "evmVersion": "istanbul", "libraries": {},
        "metadata": {"bytecodeHash": "ipfs"},
        "optimizer": {"enabled": True, "runs": 200}, "remappings": [],
    }, "compiler metadata effective settings differ")

    creation = hex_bytes("0x" + contract["evm"]["bytecode"]["object"], "compiler creation bytecode")
    runtime = hex_bytes("0x" + contract["evm"]["deployedBytecode"]["object"], "compiler runtime bytecode")
    expect(len(creation) == 4207 and "0x" + keccak256(creation) ==
           "0x015bbc23707827310841f6f536b755f9c67ea516844a7684c85b97d39bdf0ffd",
           "compiled creation template identity differs")
    expect(len(runtime) == 2497 and "0x" + keccak256(runtime) ==
           "0x9bc25fa4b2f98d56db4aa4156a6dc98360ccd4ef9c7bc7f891797b0024272100",
           "compiled runtime identity differs")

    abi = abi_inventory(contract["abi"])
    behavior = source_behavior(source_rows)
    rpc_captures, rpc_agreement = rpc_inventory(creation, runtime)
    first_rpc = parse_rpc_record(INPUT / "rpc-blastapi.json", creation, runtime)
    transaction = first_rpc["transaction"]
    receipt = first_rpc["receipt"]
    tx_input = first_rpc["txInput"]

    deployed = load(INPUT / "lido/deployed-mainnet.json")
    try:
        manifest_proxy = deployed["withdrawalQueueERC721"]["proxy"]
    except (KeyError, TypeError) as exc:
        fail(f"deployment manifest lacks withdrawalQueueERC721.proxy: {exc}")
    arguments = [IMPLEMENTATION, ADMIN, "0x"]
    expect(manifest_proxy == {
        "address": TARGET_ADDRESS,
        "constructorArgs": arguments,
        "contract": TARGET_SOURCE,
        "deployTx": TARGET_TX,
    }, "canonical deployment manifest entry differs")
    suffix = encode_constructor(arguments)
    expect(len(suffix) == 128 and tx_input == creation + suffix,
           "canonical transaction is not exact creation template plus ABI suffix")
    expect("0x" + keccak256(tx_input) ==
           "0xd79529af7d327023f254f321651a98ab8f1abe14e89b735a59054bcbff10b868",
           "canonical complete creation-input Keccak-256 differs")
    sender = transaction["from"]
    nonce = int(transaction["nonce"], 16)
    derived_address = create_address(sender, nonce)
    expect(derived_address == TARGET_ADDRESS_LOWER,
           f"CREATE address derivation differs: {derived_address}")

    build_rows = []
    for input_path, upstream_path in sorted(BUILD_FILES.items()):
        data = (INPUT / input_path).read_bytes()
        build_rows.append({
            "gitBlob": PINNED_GIT_BLOBS[input_path], "inputPath": input_path,
            "sha256": sha256(data), "upstreamPath": upstream_path,
        })
    lock: dict[str, Any] = {
        "_comment": "GENERATED by scripts/lido-ossifiable-proxy-reference.py from membership-pinned offline inputs; never edit by hand",
        "schema": 1,
        "generator": {
            "name": "blanc-lido-ossifiable-proxy-reference",
            "networkFreeOrdinaryCheck": True,
            "regenerationCommand": "python3 scripts/lido-ossifiable-proxy-reference.py generate",
            "version": 1,
        },
        "target": {
            "address": TARGET_ADDRESS, "chainId": 1, "contract": TARGET_CONTRACT,
            "deploymentBlock": TARGET_BLOCK, "deploymentBlockHash": TARGET_BLOCK_HASH,
            "deploymentRole": "WithdrawalQueueERC721 proxy",
            "deploymentTransaction": TARGET_TX, "sourcePath": TARGET_SOURCE,
        },
        "provenance": {
            "buildFiles": build_rows, "closureComplete": True, "inputFiles": input_files,
            "lidoCommit": "17005714f151e5502c559932319a3f2f74ac2436", "lidoTag": "v4.0.0",
            "openzeppelinCommit": "6bd6b76d1156e20e45d1016f355d154141c7e5b9",
            "openzeppelinTag": "v4.4.1", "sourceFiles": source_rows,
        },
        "compiler": {
            "binary": {"byteLength": len(compiler_bytes), "file": SOLC_FILE,
                       "keccak256": SOLC_KECCAK256, "sha256": sha256(compiler_bytes)},
            "longVersion": SOLC_LONG_VERSION, "metadataSettings": metadata_settings,
            "packaging": "emscripten-wasm32", "releaseManifestEntry": release,
            "standardInputSha256": sha256(standard_input_bytes),
            "standardInputSettings": standard["settings"],
            "standardOutputSha256": sha256(standard_output_bytes), "version": "0.8.9",
        },
        "abi": abi,
        "sourceBehavior": behavior,
        "artifacts": {
            "compilerOutputReproducedByteForByte": True,
            "creationTemplate": byte_artifact(creation), "runtime": byte_artifact(runtime),
        },
        "deployment": {
            "block": {"hash": TARGET_BLOCK_HASH, "number": TARGET_BLOCK,
                      "timestamp": TARGET_TIMESTAMP, "timestampIso": "2023-05-02T10:38:47Z"},
            "completeInput": byte_artifact(tx_input),
            "constructor": {
                "arguments": arguments, "creationTemplateBytes": len(creation),
                "encodedSuffix": "0x" + suffix.hex(), "encodedSuffixBytes": len(suffix), "payable": False,
            },
            "createAddressDerivation": {
                "derivedAddress": TARGET_ADDRESS, "nonce": nonce, "scheme": "CREATE(rlp(sender,nonce))",
                "sender": sender,
            },
            "historicalReceipt": {
                "contractAddress": receipt["contractAddress"], "gasUsed": int(receipt["gasUsed"], 16),
                "status": int(receipt["status"], 16), "transactionIndex": int(receipt["transactionIndex"], 16),
            },
            "independentBoundaryExtraction": {
                "compilerCreationEqualsTransactionPrefix": True,
                "decodedArgumentsEqualManifest": True,
                "rpcCodeEqualsCompilerRuntime": True,
                "transactionSuffixIsExactAbiEncoding": True,
            },
            "transaction": TARGET_TX,
        },
        "rpc": {"agreement": rpc_agreement, "captures": rpc_captures},
    }
    digest_sections = [
        "abi", "artifacts", "compiler", "deployment", "provenance", "rpc", "sourceBehavior", "target",
    ]
    lock["sectionDigests"] = {name: sha256(compact(lock[name])) for name in digest_sections}
    return lock


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
        expect(parsed == built and actual == expected,
               "generated lock differs from independently rebuilt offline content")
        print("OK — Lido OssifiableProxy reference: exact 7-source closure; vendored solc recompilation; 7 named endpoints; dual archival RPC agreement")
    else:
        LOCK.write_bytes(expected)
        print(f"wrote {LOCK}")


def capture_rpc(url: str, output_path: Path, name: str) -> None:
    captures = []
    for label, request in expected_rpc_requests():
        body = json.dumps(request, separators=(",", ":"))
        raw = subprocess.check_output([
            "curl", "-sS", "--fail-with-body", "-H", "content-type: application/json",
            "--data", body, url,
        ])
        captures.append({
            "label": label, "request": request, "responseRaw": raw.decode(),
            "responseSha256": sha256(raw),
        })
    record = {
        "captureDateUtc": datetime.datetime.now(datetime.timezone.utc).date().isoformat(),
        "captures": captures, "operator": {"name": name, "url": url}, "schema": 1,
    }
    output_path.write_bytes(canonical(record))


def is_within(path: Path, parent: Path) -> bool:
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def refresh_rpc(output: Path) -> None:
    expect(not is_within(output, INPUT),
           "refresh-rpc refuses to write into the authoritative input tree")
    expect(not output.exists(), f"candidate output already exists: {output}")
    output.mkdir(parents=True)
    paths = []
    for key, (name, url) in sorted(RPC_OPERATORS.items()):
        path = output / f"rpc-{key}.json"
        capture_rpc(url, path, name)
        paths.append(path)
    compiled = contract_output(load(INPUT / "standard-json-output.json"))
    creation = hex_bytes("0x" + compiled["evm"]["bytecode"]["object"], "creation")
    runtime = hex_bytes("0x" + compiled["evm"]["deployedBytecode"]["object"], "runtime")
    rpc_inventory(creation, runtime, paths)
    for path in paths:
        print(f"candidate {path}: sha256 {sha256(path.read_bytes())}")
    print("candidate RPC records agree; they remain non-authoritative until reviewed and admitted")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("generate", "check", "refresh-rpc"))
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    try:
        if arguments.command == "refresh-rpc":
            expect(arguments.output is not None, "refresh-rpc requires --output")
            refresh_rpc(arguments.output)
        else:
            expect(arguments.output is None, "--output is only valid with refresh-rpc")
            generate(arguments.command == "check")
    except (OSError, ReferenceError, subprocess.CalledProcessError) as exc:
        print(f"REGRESSION — Lido OssifiableProxy reference: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
