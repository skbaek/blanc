#!/usr/bin/env python3
"""Build and check the fail-closed TriggerableWithdrawalsGateway reference.

`generate` and `check` are network-free.  `refresh-inputs` deliberately
vendors a clean, pinned Git source closure and compiler.  `refresh-rpc` writes
a candidate capture outside the authority tree; `admit-rpc` copies two reviewed
candidates into it.  Ordinary validation never falls back to a network call.
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
import urllib.request
from pathlib import Path, PurePosixPath
from typing import Any

from lido_twg_reference_schema import (
    SchemaError as LockSchemaError,
    keccak256,
    validate_lock_schema,
)


ROOT = Path(__file__).resolve().parents[1]
REF = Path(os.environ.get(
    "LIDO_TWG_REFERENCE_DIR", ROOT / "scripts" / "reference" / "lido-twg"
))
INPUT = REF / "inputs"
LOCK = Path(os.environ.get(
    "LIDO_TWG_REFERENCE_LOCK", ROOT / "scripts" / "lido-twg-reference.json"
))

LIDO_REPOSITORY = "https://github.com/lidofinance/core"
LIDO_COMMIT = "17005714f151e5502c559932319a3f2f74ac2436"
LIDO_TAG = "v4.0.0"
OZ_REPOSITORY = "https://github.com/OpenZeppelin/openzeppelin-contracts"
OZ_COMMIT = "6bd6b76d1156e20e45d1016f355d154141c7e5b9"
OZ_TAG = "v4.4.1"
OZ_ALIAS = "@openzeppelin/contracts-v4.4"

TARGET_SOURCE = "contracts/0.8.9/TriggerableWithdrawalsGateway.sol"
TARGET_CONTRACT = "TriggerableWithdrawalsGateway"
TARGET_ADDRESS = "0xDC00116a0D3E064427dA2600449cfD2566B3037B"
TARGET_ADDRESS_LOWER = TARGET_ADDRESS.lower()
TARGET_BLOCK = 25_866_991
TARGET_BLOCK_HEX = "0x18ab2ef"
TARGET_BLOCK_HASH = "0xe80828e439dcfe0a443115004c86072896bb1fe71ee68c4dc6ce7946b0f0603e"
TARGET_TIMESTAMP = 1_788_079_703

CIRCUIT_BREAKER = "0x6019CB557978296BA3C08a7B73225C0975DFB2F7"
OFFICIAL_PARAMETERS = {
    "admin": "0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c",
    "lidoLocator": "0xC1d0b3DE6792Bf6b4b37EccdcC24e45978Cfd2Eb",
    "maxExitRequestsLimit": 11200,
    "exitsPerFrame": 1,
    "frameDurationInSec": 48,
}
CORPUS_PARAMETERS = {
    "admin": "0x111122223333444455556666777788889999AaAa",
    "lidoLocator": "0x22223333444455556666777788889999AaAaBbBb",
    "maxExitRequestsLimit": 17,
    "exitsPerFrame": 3,
    "frameDurationInSec": 48,
}

SOLC_FILE = "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js"
SOLC_LIST = "solc-emscripten-wasm32-list.json"
SOLC_VERSION = "0.8.9"
SOLC_LONG_VERSION = "0.8.9+commit.e5eed63a"
SOLC_SHA256 = "5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c"
SOLC_KECCAK256 = "0xbc470ab3442e78bb4d3f16c01c39b2f160f4f34eb4373efed11c234e1c7f6ca0"
SOLC_SIZE = 26_173_264

BUILD_FILES = {
    "lido/contracts/COMPILERS.md": "contracts/COMPILERS.md",
    "lido/deployed-mainnet.json": "deployed-mainnet.json",
    "lido/hardhat.config.ts": "hardhat.config.ts",
    "lido/package.json": "package.json",
    "lido/yarn.lock": "yarn.lock",
}

SOURCE_INPUTS = {
    "@openzeppelin/contracts-v4.4/access/IAccessControl.sol":
        "source/@openzeppelin/contracts-v4.4/access/IAccessControl.sol",
    "@openzeppelin/contracts-v4.4/access/IAccessControlEnumerable.sol":
        "source/@openzeppelin/contracts-v4.4/access/IAccessControlEnumerable.sol",
    "@openzeppelin/contracts-v4.4/utils/Context.sol":
        "source/@openzeppelin/contracts-v4.4/utils/Context.sol",
    "@openzeppelin/contracts-v4.4/utils/Strings.sol":
        "source/@openzeppelin/contracts-v4.4/utils/Strings.sol",
    "@openzeppelin/contracts-v4.4/utils/introspection/ERC165.sol":
        "source/@openzeppelin/contracts-v4.4/utils/introspection/ERC165.sol",
    "@openzeppelin/contracts-v4.4/utils/introspection/IERC165.sol":
        "source/@openzeppelin/contracts-v4.4/utils/introspection/IERC165.sol",
    "@openzeppelin/contracts-v4.4/utils/structs/EnumerableSet.sol":
        "source/@openzeppelin/contracts-v4.4/utils/structs/EnumerableSet.sol",
    "contracts/0.8.9/TriggerableWithdrawalsGateway.sol":
        "source/contracts/0.8.9/TriggerableWithdrawalsGateway.sol",
    "contracts/0.8.9/lib/ExitLimitUtils.sol":
        "source/contracts/0.8.9/lib/ExitLimitUtils.sol",
    "contracts/0.8.9/lib/UnstructuredStorage.sol":
        "source/contracts/0.8.9/lib/UnstructuredStorage.sol",
    "contracts/0.8.9/utils/PausableUntil.sol":
        "source/contracts/0.8.9/utils/PausableUntil.sol",
    "contracts/0.8.9/utils/access/AccessControl.sol":
        "source/contracts/0.8.9/utils/access/AccessControl.sol",
    "contracts/0.8.9/utils/access/AccessControlEnumerable.sol":
        "source/contracts/0.8.9/utils/access/AccessControlEnumerable.sol",
}

ROLES = {
    "DEFAULT_ADMIN_ROLE": "0x" + "00" * 32,
    "PAUSE_ROLE": "0x139c2898040ef16910dc9f44dc697df79363da767d8bc92f2e310312b816e46d",
    "RESUME_ROLE": "0x2fc10cc8ae19568712f7a176fb4978616a610650813c9d05326c34abb62749c7",
    "ADD_FULL_WITHDRAWAL_REQUEST_ROLE":
        "0x15fac8ba7fe8dd5344b88c1915452ce66976f270d1cd793c3b0ab579cecd33c0",
    "TW_EXIT_LIMIT_MANAGER_ROLE":
        "0x03c30da9b9e4d4789ac88a294d39a63058ca4a498804c2aa823e381df59d0cf4",
}
ROLE_MEMBERS = {
    "DEFAULT_ADMIN_ROLE": ["0x3e40d73eb977dc6a537af587d48316fee66e9c8c"],
    "PAUSE_ROLE": [
        "0x7914b5a1539b97bd0bbd155757f25fd79a522d24",
        CIRCUIT_BREAKER.lower(),
    ],
    "RESUME_ROLE": ["0x7914b5a1539b97bd0bbd155757f25fd79a522d24"],
    "ADD_FULL_WITHDRAWAL_REQUEST_ROLE": [
        "0x0de4ea0184c2ad0baca7183356aea5b8d5bf5c6e",
        "0x610b517d380f287c239c93f8ef6ffbd567aa4ba5",
        "0xe181a377a2d2bde9a83f1474bc3db7a412de091e",
    ],
    "TW_EXIT_LIMIT_MANAGER_ROLE": ["0x3e40d73eb977dc6a537af587d48316fee66e9c8c"],
}

FUNCTION_SIGNATURES = {
    "ADD_FULL_WITHDRAWAL_REQUEST_ROLE()", "DEFAULT_ADMIN_ROLE()",
    "PAUSE_INFINITELY()", "PAUSE_ROLE()", "RESUME_ROLE()",
    "TWR_LIMIT_POSITION()", "TW_EXIT_LIMIT_MANAGER_ROLE()", "VERSION()",
    "getExitRequestLimitFullInfo()", "getResumeSinceTimestamp()",
    "getRoleAdmin(bytes32)", "getRoleMember(bytes32,uint256)",
    "getRoleMemberCount(bytes32)", "grantRole(bytes32,address)",
    "hasRole(bytes32,address)", "isPaused()", "pauseFor(uint256)",
    "pauseUntil(uint256)", "renounceRole(bytes32,address)", "resume()",
    "revokeRole(bytes32,address)", "setExitRequestLimit(uint256,uint256,uint256)",
    "supportsInterface(bytes4)",
    "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)",
}
EVENT_SIGNATURES = {
    "ExitRequestsLimitSet(uint256,uint256,uint256)", "Paused(uint256)",
    "Resumed()", "RoleAdminChanged(bytes32,bytes32,bytes32)",
    "RoleGranted(bytes32,address,address)", "RoleRevoked(bytes32,address,address)",
}
ERROR_SIGNATURES = {
    "AdminCannotBeZero()", "ExitRequestsLimitExceeded(uint256,uint256)",
    "FeeRefundFailed()", "InsufficientFee(uint256,uint256)",
    "LimitExceeded()", "PauseUntilMustBeInFuture()", "PausedExpected()",
    "ResumedExpected()", "TooLargeExitsPerFrame()", "TooLargeFrameDuration()",
    "TooLargeMaxExitRequestsLimit()", "ZeroArgument(string)",
    "ZeroFrameDuration()", "ZeroPauseDuration()",
}

RPC_OPERATORS = {
    "drpc": ("dRPC", "https://eth.drpc.org", "rpc-drpc.json"),
    "blastapi": ("BlastAPI", "https://eth-mainnet.public.blastapi.io", "rpc-blastapi.json"),
}

# Filled from the reviewed authority tree.  `check` refuses an unpinned tree.
PINNED_INPUT_SHA256: dict[str, str] = {
    "git-provenance.json": "1996db8d22ba5468080e4c5726492fb0f7a08fc48e140a928cc5db55000eb81f",
    "lido/contracts/COMPILERS.md": "888504aefff340b47cd49f5b299fd3d3055c70ab56222098a961be87ef49e4b8",
    "lido/deployed-mainnet.json": "3428ba7a845ae27c69bd64d87dafda920df3fdfdc8df99da1caf3af55060fd15",
    "lido/hardhat.config.ts": "29b3e91ff197c0ea1df5b6401cc12982d3f684e7bf3e68b380096fe33e43b223",
    "lido/package.json": "5e6bd056082e23c6628aee085df5ce0743070d08d5a3e27496991e09f74b638e",
    "lido/yarn.lock": "d17f979eed36218b0bed85cf560bdc2e5d182e0c67aff6eabf2c68be8597c921",
    "rpc-blastapi.json": "132df9a8b836f8e91b611a8bc5565ca8f40d6b17bfe4233f6710d0f377fc98d6",
    "rpc-drpc.json": "a1b0b809bd9ae1d0a634c3e1f6dee621db8d6b95dca58e34de624931b669c0a5",
    "solc-emscripten-wasm32-list.json": "0ee86d7e0a30f0d90593ff64dfb56d192c514c8e33feebeb54446be55b12e5ad",
    SOLC_FILE: SOLC_SHA256,
    "source/@openzeppelin/contracts-v4.4/access/IAccessControl.sol": "d03c1257f2094da6c86efa7aa09c1c07ebd33dd31046480c5097bc2542140e45",
    "source/@openzeppelin/contracts-v4.4/access/IAccessControlEnumerable.sol": "655ab8dc2a9617376734d04ca293e099cc24f8ce893997e68c29cfebc4a61d39",
    "source/@openzeppelin/contracts-v4.4/utils/Context.sol": "1458c260d010a08e4c20a4a517882259a23a4baa0b5bd9add9fb6d6a1549814a",
    "source/@openzeppelin/contracts-v4.4/utils/Strings.sol": "8597c62818dcbc6cf85c21179b90b714fb4f70a4347ca2eed23e88c87b08b8a1",
    "source/@openzeppelin/contracts-v4.4/utils/introspection/ERC165.sol": "8806a632d7b656cadb8133ff8f2acae4405b3a64d8709d93b0fa6a216a8a6154",
    "source/@openzeppelin/contracts-v4.4/utils/introspection/IERC165.sol": "701e025d13ec6be09ae892eb029cd83b3064325801d73654847a5fb11c58b1e5",
    "source/@openzeppelin/contracts-v4.4/utils/structs/EnumerableSet.sol": "42a618e7d36efd2319d1bf05fedb31f3042baf535cfb97e783128cc1fe326686",
    "source/contracts/0.8.9/TriggerableWithdrawalsGateway.sol": "22a41b19c7b44b6e6a86ead5ba942ddab36e9ca44f2586040375a82eb9dad55a",
    "source/contracts/0.8.9/lib/ExitLimitUtils.sol": "6f6bb8bec3c3eee6690d71b1b5d494c66a746d468f789dbb9883d6eefe4b927b",
    "source/contracts/0.8.9/lib/UnstructuredStorage.sol": "955bfcb0bf265db114248bdabeabebc39bddb3fbb756e2448f6aed59f1994f56",
    "source/contracts/0.8.9/utils/PausableUntil.sol": "afd11f5950050bbc8e9fad3cbea2a5bdbcc23048128c30f335a12b48084c8594",
    "source/contracts/0.8.9/utils/access/AccessControl.sol": "e399e266f9b0e8fe99708f3fb2f656a636fb432d69ca9c247f2e84f2e762f803",
    "source/contracts/0.8.9/utils/access/AccessControlEnumerable.sol": "e8fa2bc8e4c8046fd04b25ed4708be8159913cac4ca738cdc53022896e0566ce",
    "standard-json-input.json": "9f9558bcf65b2c7a326f3443a53bb0e32428176d4bb23c1761f4cc8c57962a3c",
    "standard-json-output.json": "a9e1547dd13d1915ef907e3d66aeba8c82a8ec132444d2e68b9574828b396a5e",
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
    expect(len(body) % 2 == 0 and all(c in "0123456789abcdefABCDEF" for c in body),
           f"{what}: malformed hexadecimal")
    return bytes.fromhex(body)


def byte_artifact(raw: bytes) -> dict[str, Any]:
    return {
        "byteLength": len(raw),
        "hex": "0x" + raw.hex(),
        "keccak256": "0x" + keccak256(raw),
        "sha256": sha256(raw),
    }


def git_output(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True,
    )
    expect(result.returncode == 0,
           f"git {' '.join(args)} failed in {repo}: {result.stderr.strip()}")
    return result.stdout.strip()


IMPORT_RE = re.compile(r'import\s+(?:[^"\']*?\s+from\s+)?["\']([^"\']+)["\']\s*;')


def resolve_import(unit: str, imported: str) -> str:
    if imported.startswith("."):
        return posixpath.normpath(posixpath.join(posixpath.dirname(unit), imported))
    return posixpath.normpath(imported)


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
    with tempfile.TemporaryDirectory(prefix="lido-twg-solc-") as temporary:
        driver = Path(temporary) / ("compile.js" if kind == "jsc" else "compile.cjs")
        if kind == "jsc":
            driver.write_text(
                "globalThis.console={log:print,warn:print,error:print,info:print,debug:print};"
                "globalThis.Module={print:function(){},printErr:function(){}};"
                "var argv=arguments;load(argv[0]);"
                "if(typeof drainMicrotasks===\"function\")drainMicrotasks();"
                "var c=Module.cwrap(\"solidity_compile\",\"string\","
                "[\"string\",\"number\",\"number\"]);print(c(read(argv[1]),0,0));"
            )
            command = [executable, str(driver), "--", str(soljson), str(standard_input)]
        else:
            driver.write_text(
                "const fs=require('fs');const Module=require(process.argv[2]);"
                "const c=Module.cwrap('solidity_compile','string',['string','number','number']);"
                "process.stdout.write(c(fs.readFileSync(process.argv[3],'utf8'),0,0)+'\\n');"
            )
            command = [executable, str(driver), str(soljson), str(standard_input)]
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    expect(result.returncode == 0,
           f"vendored solc failed with {kind} exit {result.returncode}: "
           f"{result.stderr.decode(errors='replace')}")
    return result.stdout


def source_path(repo_lido: Path, repo_oz: Path, unit: str) -> Path:
    if unit.startswith(OZ_ALIAS + "/"):
        return repo_oz / "contracts" / unit[len(OZ_ALIAS) + 1:]
    return repo_lido / unit


def standard_input_from_tree() -> dict[str, Any]:
    sources: dict[str, Any] = {}
    for unit, relative in sorted(SOURCE_INPUTS.items()):
        try:
            text = (INPUT / relative).read_text()
        except (OSError, UnicodeDecodeError) as exc:
            fail(f"cannot read source {relative}: {exc}")
        sources[unit] = {"content": text}
    expect(derive_source_closure({k: v["content"] for k, v in sources.items()}) == set(SOURCE_INPUTS),
           "recursive source closure differs from the exact thirteen-source set")
    return {
        "language": "Solidity",
        "sources": sources,
        "settings": {
            "evmVersion": "istanbul",
            "optimizer": {"enabled": True, "runs": 200},
            "outputSelection": {
                "*": {"*": [
                    "abi", "metadata", "evm.bytecode.object",
                    "evm.deployedBytecode.object",
                    "evm.deployedBytecode.immutableReferences",
                ]}
            },
        },
    }


def validate_input_pins() -> list[dict[str, str]]:
    expect(bool(PINNED_INPUT_SHA256), "authoritative input pins are not populated")
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
        rows.append({"path": relative, "sha256": digest})
    return rows


def release_row() -> dict[str, Any]:
    manifest = load(INPUT / SOLC_LIST)
    rows = [row for row in manifest.get("builds", []) if row.get("longVersion") == SOLC_LONG_VERSION]
    expect(len(rows) == 1, "Solidity release manifest lacks one exact 0.8.9 build")
    expected = {
        "path": SOLC_FILE, "version": SOLC_VERSION, "build": "commit.e5eed63a",
        "longVersion": SOLC_LONG_VERSION, "keccak256": SOLC_KECCAK256,
        "sha256": "0x" + SOLC_SHA256,
        "urls": ["dweb:/ipfs/QmfFq3MvisCSUJy8N8EVsBribgPbdpTZb7tQ2eHYw7dwag"],
    }
    expect(rows[0] == expected, "Solidity release manifest row differs")
    return rows[0]


def source_inventory(provenance: dict[str, Any], standard: dict[str, Any]) -> list[dict[str, Any]]:
    expect(set(standard.get("sources", {})) == set(SOURCE_INPUTS),
           "Standard JSON source membership differs")
    rows = []
    for unit, relative in sorted(SOURCE_INPUTS.items()):
        data = (INPUT / relative).read_bytes()
        expect(standard["sources"][unit] == {"content": data.decode()},
               f"Standard JSON source differs for {unit}")
        owner = "openzeppelin" if unit.startswith(OZ_ALIAS + "/") else "lido"
        upstream = ("contracts/" + unit[len(OZ_ALIAS) + 1:]
                    if owner == "openzeppelin" else unit)
        expect(provenance[owner]["files"].get(upstream) == git_blob(data),
               f"Git blob provenance differs for {unit}")
        rows.append({
            "byteLength": len(data), "gitBlob": git_blob(data),
            "inputPath": relative, "keccak256": "0x" + keccak256(data),
            "sha256": sha256(data), "sourceUnit": unit,
        })
    return rows


def contract_output(output: dict[str, Any]) -> dict[str, Any]:
    try:
        return output["contracts"][TARGET_SOURCE][TARGET_CONTRACT]
    except (KeyError, TypeError) as exc:
        fail(f"compiler output lacks {TARGET_SOURCE}:{TARGET_CONTRACT}: {exc}")


def abi_type(argument: dict[str, Any]) -> str:
    raw = argument["type"]
    if raw.startswith("tuple"):
        return "(" + ",".join(abi_type(item) for item in argument.get("components", [])) + ")" + raw[5:]
    return raw


def abi_signature(entry: dict[str, Any]) -> str:
    return f"{entry['name']}({','.join(abi_type(arg) for arg in entry.get('inputs', []))})"


def abi_inventory(raw: Any) -> dict[str, Any]:
    expect(isinstance(raw, list), "compiler ABI is not an array")
    constructors = [entry for entry in raw if entry.get("type") == "constructor"]
    functions = {abi_signature(entry): entry for entry in raw if entry.get("type") == "function"}
    events = {abi_signature(entry): entry for entry in raw if entry.get("type") == "event"}
    errors = {abi_signature(entry): entry for entry in raw if entry.get("type") == "error"}
    expect(len(constructors) == 1, "ABI must have exactly one constructor")
    expect(not [entry for entry in raw if entry.get("type") in {"fallback", "receive"}],
           "ABI unexpectedly has fallback or receive")
    expect(set(functions) == FUNCTION_SIGNATURES, "ABI function inventory differs")
    expect(set(events) == EVENT_SIGNATURES, "ABI event inventory differs")
    expect(set(errors) == ERROR_SIGNATURES, "ABI error inventory differs")
    constructor = constructors[0]
    expect([arg["name"] for arg in constructor["inputs"]] == [
        "admin", "lidoLocator", "maxExitRequestsLimit", "exitsPerFrame", "frameDurationInSec"
    ], "constructor argument names differ")
    expect([arg["type"] for arg in constructor["inputs"]] == [
        "address", "address", "uint256", "uint256", "uint256"
    ] and constructor.get("stateMutability") == "nonpayable", "constructor boundary differs")
    return {
        "constructor": constructor,
        "functions": [{
            "entry": functions[sig], "payable": functions[sig].get("stateMutability") == "payable",
            "returnTypes": [abi_type(arg) for arg in functions[sig].get("outputs", [])],
            "selector": "0x" + keccak256(sig.encode())[:8], "signature": sig,
        } for sig in sorted(functions)],
        "events": [{
            "entry": events[sig], "indexed": [arg["indexed"] for arg in events[sig]["inputs"]],
            "signature": sig, "topic0": "0x" + keccak256(sig.encode()),
        } for sig in sorted(events)],
        "errors": [{
            "entry": errors[sig], "selector": "0x" + keccak256(sig.encode())[:8],
            "signature": sig,
        } for sig in sorted(errors)],
        "functionCount": len(functions), "eventCount": len(events), "errorCount": len(errors),
    }


def address_word(value: str, what: str) -> bytes:
    raw = hex_bytes(value, what)
    expect(len(raw) == 20, f"{what}: address is not 20 bytes")
    return raw.rjust(32, b"\0")


def encode_parameters(parameters: dict[str, Any]) -> bytes:
    words = [address_word(parameters["admin"], "admin"),
             address_word(parameters["lidoLocator"], "lidoLocator")]
    for key in ("maxExitRequestsLimit", "exitsPerFrame", "frameDurationInSec"):
        value = parameters[key]
        expect(type(value) is int and 0 <= value < 2**256, f"invalid {key}")
        words.append(value.to_bytes(32, "big"))
    return b"".join(words)


def patch_runtime(template: bytes, references: dict[str, Any], locator: str) -> bytes:
    expect(set(references) == {"1089"}, "LOCATOR immutable AST id differs")
    spans = references["1089"]
    expect(spans == [{"length": 32, "start": 1500}, {"length": 32, "start": 4157}],
           "LOCATOR immutable spans differ")
    replacement = address_word(locator, "lidoLocator")
    result = bytearray(template)
    covered: set[int] = set()
    for span in spans:
        start, length = span["start"], span["length"]
        cells = set(range(start, start + length))
        expect(length == 32 and start + length <= len(result) and not covered & cells,
               "immutable span overlaps or is out of bounds")
        covered |= cells
        result[start:start + length] = replacement
    return bytes(result)


def world(name: str, parameters: dict[str, Any], creation: bytes,
          runtime: bytes, references: dict[str, Any]) -> dict[str, Any]:
    suffix = encode_parameters(parameters)
    returned = patch_runtime(runtime, references, parameters["lidoLocator"])
    return {
        "name": name, "parameters": parameters,
        "constructorSuffix": "0x" + suffix.hex(),
        "fullCreateInput": byte_artifact(creation + suffix),
        "returnedRuntime": byte_artifact(returned),
        "immutableValues": {"LOCATOR": "0x" + address_word(parameters["lidoLocator"], "locator").hex()},
        "relations": {
            "sameCreationTemplate": True, "sameCompilerSettings": True,
            "suffixIsExactAbiEncoding": True, "runtimeDiffOnlyAtImmutableSpans": True,
        },
    }


def call_data(selector: str, words: list[str] = []) -> str:
    return "0x" + selector + "".join(word.removeprefix("0x").lower() for word in words)


def rpc_requests() -> list[tuple[str, dict[str, Any]]]:
    requests: list[tuple[str, dict[str, Any]]] = []
    def add(label: str, method: str, params: list[Any]) -> None:
        requests.append((label, {"jsonrpc": "2.0", "id": len(requests) + 1,
                                 "method": method, "params": params}))
    add("chainId", "eth_chainId", [])
    add("block", "eth_getBlockByHash", [TARGET_BLOCK_HASH, False])
    add("code", "eth_getCode", [TARGET_ADDRESS_LOWER, TARGET_BLOCK_HEX])
    add("proof", "eth_getProof", [TARGET_ADDRESS_LOWER, [], TARGET_BLOCK_HEX])
    add("isPaused", "eth_call", [{"to": TARGET_ADDRESS_LOWER, "data": call_data("b187bd26")}, TARGET_BLOCK_HEX])
    add("resumeSince", "eth_call", [{"to": TARGET_ADDRESS_LOWER, "data": call_data("589ff76c")}, TARGET_BLOCK_HEX])
    pause = ROLES["PAUSE_ROLE"]
    add("hasPauseCircuitBreaker", "eth_call", [{"to": TARGET_ADDRESS_LOWER, "data": call_data(
        "91d14854", [pause, "0x" + address_word(CIRCUIT_BREAKER, "CircuitBreaker").hex()])}, TARGET_BLOCK_HEX])
    for role_name, role in ROLES.items():
        add(f"roleAdmin.{role_name}", "eth_call", [{"to": TARGET_ADDRESS_LOWER,
            "data": call_data("248a9ca3", [role])}, TARGET_BLOCK_HEX])
        add(f"roleCount.{role_name}", "eth_call", [{"to": TARGET_ADDRESS_LOWER,
            "data": call_data("ca15c873", [role])}, TARGET_BLOCK_HEX])
        for index in range(len(ROLE_MEMBERS[role_name])):
            add(f"roleMember.{role_name}.{index}", "eth_call", [{"to": TARGET_ADDRESS_LOWER,
                "data": call_data("9010d07c", [role, "0x" + index.to_bytes(32, "big").hex()])}, TARGET_BLOCK_HEX])
    return requests


def capture_map(path: Path) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    envelope = load(path)
    expect(set(envelope) == {"schema", "captureDateUtc", "operator", "captures"}
           and envelope["schema"] == 1, f"{path}: wrong RPC envelope schema")
    expected = rpc_requests()
    captures = envelope["captures"]
    expect(isinstance(captures, list) and len(captures) == len(expected),
           f"{path}: RPC capture count differs")
    results: dict[str, dict[str, Any]] = {}
    for actual, (label, request) in zip(captures, expected):
        expect(set(actual) == {"label", "request", "responseRaw", "responseSha256"},
               f"{path}: capture shape differs for {label}")
        expect(actual["label"] == label and actual["request"] == request,
               f"{path}: request differs for {label}")
        raw = actual["responseRaw"].encode()
        expect(sha256(raw) == actual["responseSha256"],
               f"{path}: response digest differs for {label}")
        response = strict_json(raw, f"{path}:{label}")
        expect(isinstance(response, dict) and response.get("id") == request["id"]
               and response.get("jsonrpc") == "2.0" and "error" not in response
               and "result" in response, f"{path}: invalid response for {label}")
        results[label] = response
    return envelope, results


def one_word(response: dict[str, Any], label: str) -> str:
    value = response["result"]
    expect(isinstance(value, str) and re.fullmatch(r"0x[0-9a-f]{64}", value),
           f"{label}: response is not one lowercase word")
    return value


def validate_rpc(runtime: bytes) -> tuple[dict[str, Any], dict[str, Any]]:
    captures = []
    selected: list[dict[str, Any]] = []
    for key in ("drpc", "blastapi"):
        operator, url, filename = RPC_OPERATORS[key]
        envelope, results = capture_map(INPUT / filename)
        expect(envelope["operator"] == {"name": operator, "url": url},
               f"{filename}: operator identity differs")
        block = results["block"]["result"]
        expect(block["number"] == TARGET_BLOCK_HEX and block["hash"] == TARGET_BLOCK_HASH
               and int(block["timestamp"], 16) == TARGET_TIMESTAMP,
               f"{filename}: block identity differs")
        code = hex_bytes(results["code"]["result"], f"{filename}:code")
        expect(code == runtime, f"{filename}: deployed code differs from compiled official runtime")
        proof = results["proof"]["result"]
        expect(proof["address"] == TARGET_ADDRESS_LOWER and proof["codeHash"] == "0x" + keccak256(runtime),
               f"{filename}: proof account/code hash differs")
        expect(one_word(results["isPaused"], "isPaused") == "0x" + "00" * 32,
               f"{filename}: target is not resumed")
        expect(one_word(results["resumeSince"], "resumeSince") == "0x" + "00" * 32,
               f"{filename}: resumeSince differs")
        expect(one_word(results["hasPauseCircuitBreaker"], "hasPauseCircuitBreaker")
               == "0x" + "00" * 31 + "01", f"{filename}: CircuitBreaker lacks PAUSE_ROLE")
        role_rows = {}
        for role_name in ROLES:
            expect(one_word(results[f"roleAdmin.{role_name}"], "role admin") == "0x" + "00" * 32,
                   f"{filename}: {role_name} admin is not DEFAULT_ADMIN_ROLE")
            expect(int(one_word(results[f"roleCount.{role_name}"], "role count"), 16)
                   == len(ROLE_MEMBERS[role_name]), f"{filename}: {role_name} count differs")
            members = []
            for index, member in enumerate(ROLE_MEMBERS[role_name]):
                word = one_word(results[f"roleMember.{role_name}.{index}"], "role member")
                actual = "0x" + word[-40:]
                expect(actual == member, f"{filename}: {role_name}[{index}] differs")
                members.append(actual)
            role_rows[role_name] = {
                "adminRole": ROLES["DEFAULT_ADMIN_ROLE"], "members": members,
            }
        chosen = {
            "chainId": results["chainId"]["result"],
            "block": {key: block[key] for key in ("number", "hash", "timestamp", "stateRoot")},
            "account": {key: proof[key] for key in ("address", "balance", "codeHash", "nonce", "storageHash")},
            "isPaused": False, "resumeSinceTimestamp": 0,
            "circuitBreaker": CIRCUIT_BREAKER,
            "circuitBreakerHasPauseRole": True, "roles": role_rows,
        }
        selected.append(chosen)
        captures.append({
            "captureDateUtc": envelope["captureDateUtc"], "file": filename,
            "operator": operator, "url": url,
            "envelopeSha256": sha256((INPUT / filename).read_bytes()),
            "responseSha256": {row["label"]: row["responseSha256"] for row in envelope["captures"]},
        })
    expect(selected[0] == selected[1], "independent RPC snapshots disagree")
    return selected[0], {
        "captures": captures,
        "agreement": {
            "blockHeaderEqual": True, "codeEqual": True, "proofFieldsEqual": True,
            "rolePauseCallsEqual": True,
        },
    }


def build_lock() -> dict[str, Any]:
    input_files = validate_input_pins()
    provenance = load(INPUT / "git-provenance.json")
    expect(provenance == {
        "schema": 1,
        "lido": {**provenance.get("lido", {})},
        "openzeppelin": {**provenance.get("openzeppelin", {})},
    }, "git provenance top-level shape differs")
    expect(provenance["lido"].get("repository") == LIDO_REPOSITORY
           and provenance["lido"].get("commit") == LIDO_COMMIT
           and provenance["lido"].get("tag") == LIDO_TAG,
           "Lido Git provenance differs")
    expect(provenance["openzeppelin"].get("repository") == OZ_REPOSITORY
           and provenance["openzeppelin"].get("commit") == OZ_COMMIT
           and provenance["openzeppelin"].get("tag") == OZ_TAG
           and provenance["openzeppelin"].get("packageAlias") == OZ_ALIAS,
           "OpenZeppelin Git provenance differs")
    standard_bytes = (INPUT / "standard-json-input.json").read_bytes()
    standard = strict_json(standard_bytes, "standard-json-input")
    expect(standard_bytes == canonical(standard), "Standard JSON input is not canonical")
    expect(standard == standard_input_from_tree(), "Standard JSON input derivation differs")
    sources = source_inventory(provenance, standard)
    compiler_bytes = (INPUT / SOLC_FILE).read_bytes()
    expect(len(compiler_bytes) == SOLC_SIZE and sha256(compiler_bytes) == SOLC_SHA256,
           "vendored solc identity differs")
    release = release_row()
    compiled_bytes = run_vendored_solc()
    frozen_output = (INPUT / "standard-json-output.json").read_bytes()
    expect(compiled_bytes == frozen_output, "vendored solc output differs byte-for-byte")
    output = strict_json(frozen_output, "standard-json-output")
    compile_errors = [row for row in output.get("errors", []) if row.get("severity") == "error"]
    expect(not compile_errors, f"compiler output has errors: {compile_errors}")
    contract = contract_output(output)
    abi = abi_inventory(contract["abi"])
    creation = bytes.fromhex(contract["evm"]["bytecode"]["object"])
    runtime = bytes.fromhex(contract["evm"]["deployedBytecode"]["object"])
    references = contract["evm"]["deployedBytecode"]["immutableReferences"]
    expect(len(creation) == 10096 and len(runtime) == 8128,
           "compiled creation/runtime size differs")
    official = world("official-mainnet-parameters", OFFICIAL_PARAMETERS, creation, runtime, references)
    corpus = world("differential-corpus", CORPUS_PARAMETERS, creation, runtime, references)
    deployed_manifest = load(INPUT / "lido/deployed-mainnet.json")
    target = deployed_manifest.get("triggerableWithdrawalsGateway")
    expect(target == {"contract": TARGET_SOURCE, "address": TARGET_ADDRESS,
                      "constructorArgs": list(OFFICIAL_PARAMETERS.values())},
           "deployed-mainnet TWG entry differs")
    snapshot, rpc = validate_rpc(hex_bytes(official["returnedRuntime"]["hex"], "official runtime"))
    root = {
        "_comment": "GENERATED by scripts/lido-twg-reference.py; do not edit by hand.",
        "schema": 1,
        "generator": {
            "name": "blanc-lido-twg-reference", "version": 1,
            "implementation": "scripts/lido-twg-reference.py",
            "regenerationCommand": "python3 scripts/lido-twg-reference.py generate",
            "networkFreeOrdinaryCheck": True,
        },
        "target": {
            "address": TARGET_ADDRESS, "chainId": 1, "contract": TARGET_CONTRACT,
            "directDeployment": True, "sourcePath": TARGET_SOURCE,
            "releaseCommit": LIDO_COMMIT, "releaseTag": LIDO_TAG,
        },
        "provenance": {
            "route": "pinned-source-compilation", "repository": LIDO_REPOSITORY,
            "lidoCommit": LIDO_COMMIT, "lidoTag": LIDO_TAG,
            "openzeppelinCommit": OZ_COMMIT, "openzeppelinTag": OZ_TAG,
            "closureComplete": True, "inputFiles": input_files,
            "sourceFiles": sources,
            "buildFiles": [{
                "inputPath": input_path, "upstreamPath": upstream,
                "gitBlob": provenance["lido"]["files"][upstream],
                "sha256": sha256((INPUT / input_path).read_bytes()),
            } for input_path, upstream in sorted(BUILD_FILES.items())],
            "claimBoundary": (
                "The source-compiled artifacts and dated on-chain equality snapshot do not "
                "verify the deployed Solidity contract or recover its deployment transaction."
            ),
        },
        "compiler": {
            "version": SOLC_VERSION, "longVersion": SOLC_LONG_VERSION,
            "packaging": "emscripten-wasm32",
            # SHA-256 is recomputed over the 26 MiB binary.  The independent
            # Keccak pin is the exact solc-bin manifest value; unlike the
            # compact contract artifacts, the compiler itself is not repeated
            # as a 52 MiB hex string in the lock.
            "binary": {
                "byteLength": len(compiler_bytes), "file": SOLC_FILE,
                "keccak256": SOLC_KECCAK256, "sha256": sha256(compiler_bytes),
            },
            "releaseManifestEntry": release,
            "settings": standard["settings"],
            "standardInputSha256": sha256(standard_bytes),
            "standardOutputSha256": sha256(frozen_output),
            "outputReproducedByteForByte": True,
        },
        "abi": abi,
        "artifacts": {
            "creationTemplate": byte_artifact(creation),
            "runtimeTemplate": byte_artifact(runtime),
            "immutableReferences": {"1089": references["1089"]},
            "immutableNames": {"1089": "LOCATOR"},
            "worlds": [official, corpus],
        },
        "snapshot": {
            "kind": "selection-time-mainnet-state", "pinnedAt": "2026-08-30",
            **snapshot,
            "relations": {
                "compiledOfficialRuntimeEqualsCode": True,
                "codeHashEqualsRuntimeKeccak": True,
                "directAccountNoProxyClaim": True,
            },
        },
        "rpc": rpc,
    }
    digest_sections = [
        "generator", "target", "provenance", "compiler", "abi", "artifacts", "snapshot", "rpc"
    ]
    root["sectionDigests"] = {key: sha256(compact(root[key])) for key in digest_sections}
    return root


def ensure_repo(repo: Path, commit: str, label: str) -> None:
    expect(repo.is_dir(), f"{label} repository not found: {repo}")
    expect(git_output(repo, "rev-parse", "HEAD") == commit, f"{label} repository HEAD differs")
    expect(git_output(repo, "status", "--porcelain") == "", f"{label} repository is dirty")


def refresh_inputs(args: argparse.Namespace) -> None:
    lido, oz = args.lido_repo.resolve(), args.openzeppelin_repo.resolve()
    ensure_repo(lido, LIDO_COMMIT, "Lido")
    ensure_repo(oz, OZ_COMMIT, "OpenZeppelin")
    expect(args.soljson.is_file() and sha256(args.soljson.read_bytes()) == SOLC_SHA256,
           "soljson SHA-256 differs")
    expect(args.soljson.stat().st_size == SOLC_SIZE, "soljson size differs")
    expect(args.solc_list.is_file(), "Solidity release list missing")
    INPUT.mkdir(parents=True, exist_ok=True)
    lido_files: dict[str, str] = {}
    oz_files: dict[str, str] = {}
    for input_path, upstream in BUILD_FILES.items():
        source = lido / upstream
        expect(source.is_file(), f"missing Lido build input {upstream}")
        destination = INPUT / input_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        lido_files[upstream] = git_output(lido, "rev-parse", f"HEAD:{upstream}")
    source_text: dict[str, str] = {}
    for unit, relative in SOURCE_INPUTS.items():
        source = source_path(lido, oz, unit)
        expect(source.is_file(), f"missing source unit {unit}")
        destination = INPUT / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        source_text[unit] = source.read_text()
        if unit.startswith(OZ_ALIAS + "/"):
            upstream = "contracts/" + unit[len(OZ_ALIAS) + 1:]
            oz_files[upstream] = git_output(oz, "rev-parse", f"HEAD:{upstream}")
        else:
            lido_files[unit] = git_output(lido, "rev-parse", f"HEAD:{unit}")
    expect(derive_source_closure(source_text) == set(SOURCE_INPUTS),
           "refreshed recursive source closure differs")
    provenance = {
        "schema": 1,
        "lido": {"repository": LIDO_REPOSITORY, "commit": LIDO_COMMIT,
                 "tag": LIDO_TAG, "files": dict(sorted(lido_files.items()))},
        "openzeppelin": {"repository": OZ_REPOSITORY, "commit": OZ_COMMIT,
                         "tag": OZ_TAG, "packageAlias": OZ_ALIAS,
                         "packageResolution": "npm:@openzeppelin/contracts@4.4.1",
                         "files": dict(sorted(oz_files.items()))},
    }
    (INPUT / "git-provenance.json").write_bytes(canonical(provenance))
    shutil.copyfile(args.soljson, INPUT / SOLC_FILE)
    shutil.copyfile(args.solc_list, INPUT / SOLC_LIST)
    standard = standard_input_from_tree()
    (INPUT / "standard-json-input.json").write_bytes(canonical(standard))
    (INPUT / "standard-json-output.json").write_bytes(run_vendored_solc())
    print("REFRESHED — Lido TWG inputs: clean pinned Git trees; exact 13-source closure; vendored solc output")


def refresh_rpc(args: argparse.Namespace) -> None:
    operator, url, _ = RPC_OPERATORS[args.operator]
    output = args.output.resolve()
    try:
        output.relative_to(REF.resolve())
    except ValueError:
        pass
    else:
        fail("refresh-rpc output must stay outside the authority tree")
    captures = []
    for label, request in rpc_requests():
        body = compact(request)
        http = urllib.request.Request(
            url, data=body,
            headers={"content-type": "application/json", "user-agent": "blanc-lido-twg-reference/1"},
        )
        try:
            with urllib.request.urlopen(http, timeout=30) as response:
                raw = response.read()
        except Exception as exc:
            fail(f"RPC refresh failed for {operator}:{label}: {exc}")
        parsed = strict_json(raw, f"RPC candidate {label}")
        expect(parsed.get("id") == request["id"] and parsed.get("jsonrpc") == "2.0"
               and "error" not in parsed and "result" in parsed,
               f"RPC candidate invalid for {label}: {parsed}")
        text = raw.decode()
        captures.append({"label": label, "request": request, "responseRaw": text,
                         "responseSha256": sha256(raw)})
    envelope = {
        "schema": 1, "captureDateUtc": datetime.datetime.now(datetime.timezone.utc).date().isoformat(),
        "operator": {"name": operator, "url": url}, "captures": captures,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(canonical(envelope))
    print(f"CANDIDATE — {operator} RPC snapshot written outside authority tree: {output}")


def admit_rpc(args: argparse.Namespace) -> None:
    for key, candidate in (("drpc", args.drpc), ("blastapi", args.blastapi)):
        operator, url, filename = RPC_OPERATORS[key]
        envelope = load(candidate)
        expect(envelope.get("operator") == {"name": operator, "url": url},
               f"{candidate}: operator differs")
        # Validate request/response syntax before admission; cross-provider and
        # semantic validation runs after both files are present.
        captures = envelope.get("captures")
        expected = rpc_requests()
        expect(isinstance(captures, list) and len(captures) == len(expected),
               f"{candidate}: capture count differs")
        for actual, (label, request) in zip(captures, expected):
            expect(actual.get("label") == label and actual.get("request") == request,
                   f"{candidate}: request differs for {label}")
            raw = actual.get("responseRaw", "").encode()
            expect(actual.get("responseSha256") == sha256(raw),
                   f"{candidate}: response digest differs for {label}")
        destination = INPUT / filename
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(candidate, destination)
    print("ADMITTED — Lido TWG dual-provider RPC candidates copied for pin review")


def print_input_pins() -> None:
    files = sorted(path for path in INPUT.rglob("*") if path.is_file())
    print("PINNED_INPUT_SHA256: dict[str, str] = {")
    for path in files:
        relative = str(path.relative_to(INPUT))
        print(f"    {relative!r}: {sha256(path.read_bytes())!r},")
    print("}")


def write_lock() -> None:
    root = build_lock()
    LOCK.write_bytes(canonical(root))
    print("GENERATED — Lido TWG reference lock")


def check_lock() -> None:
    actual = load(LOCK)
    try:
        validate_lock_schema(actual)
    except LockSchemaError as exc:
        fail(f"independent lock schema rejected lock: {exc}")
    expected = build_lock()
    expect(actual == expected, "reference lock differs from generated result")
    print("OK — Lido TWG reference lock")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("generate")
    sub.add_parser("check")
    sub.add_parser("print-input-pins")
    refresh = sub.add_parser("refresh-inputs")
    refresh.add_argument("--lido-repo", type=Path, required=True)
    refresh.add_argument("--openzeppelin-repo", type=Path, required=True)
    refresh.add_argument("--soljson", type=Path, required=True)
    refresh.add_argument("--solc-list", type=Path, required=True)
    rpc = sub.add_parser("refresh-rpc")
    rpc.add_argument("--operator", choices=sorted(RPC_OPERATORS), required=True)
    rpc.add_argument("--output", type=Path, required=True)
    admit = sub.add_parser("admit-rpc")
    admit.add_argument("--drpc", type=Path, required=True)
    admit.add_argument("--blastapi", type=Path, required=True)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "refresh-inputs":
            refresh_inputs(args)
        elif args.command == "refresh-rpc":
            refresh_rpc(args)
        elif args.command == "admit-rpc":
            admit_rpc(args)
        elif args.command == "print-input-pins":
            print_input_pins()
        elif args.command == "generate":
            write_lock()
        elif args.command == "check":
            check_lock()
        else:
            fail(f"unknown command: {args.command}")
    except (ReferenceError, LockSchemaError, OSError, ValueError, KeyError) as exc:
        print(f"REGRESSION — Lido TWG reference: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
