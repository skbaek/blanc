#!/usr/bin/env python3
"""Independent schema and semantic pins for the Lido TWG reference lock.

This module intentionally does not import the lock builder.  It owns the
closed-world lock shape, Ethereum Keccak implementation, ABI census, source
membership, compiler/artifact identities, immutable patch relation, and the
selection-time role/pause snapshot.
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
    "LIDO_TWG_REFERENCE_LOCK", ROOT / "scripts" / "lido-twg-reference.json"
))

SOURCE_UNITS = {
    "@openzeppelin/contracts-v4.4/access/IAccessControl.sol",
    "@openzeppelin/contracts-v4.4/access/IAccessControlEnumerable.sol",
    "@openzeppelin/contracts-v4.4/utils/Context.sol",
    "@openzeppelin/contracts-v4.4/utils/Strings.sol",
    "@openzeppelin/contracts-v4.4/utils/introspection/ERC165.sol",
    "@openzeppelin/contracts-v4.4/utils/introspection/IERC165.sol",
    "@openzeppelin/contracts-v4.4/utils/structs/EnumerableSet.sol",
    "contracts/0.8.9/TriggerableWithdrawalsGateway.sol",
    "contracts/0.8.9/lib/ExitLimitUtils.sol",
    "contracts/0.8.9/lib/UnstructuredStorage.sol",
    "contracts/0.8.9/utils/PausableUntil.sol",
    "contracts/0.8.9/utils/access/AccessControl.sol",
    "contracts/0.8.9/utils/access/AccessControlEnumerable.sol",
}
FUNCTIONS = {
    "ADD_FULL_WITHDRAWAL_REQUEST_ROLE()", "DEFAULT_ADMIN_ROLE()",
    "PAUSE_INFINITELY()", "PAUSE_ROLE()", "RESUME_ROLE()", "TWR_LIMIT_POSITION()",
    "TW_EXIT_LIMIT_MANAGER_ROLE()", "VERSION()", "getExitRequestLimitFullInfo()",
    "getResumeSinceTimestamp()", "getRoleAdmin(bytes32)",
    "getRoleMember(bytes32,uint256)", "getRoleMemberCount(bytes32)",
    "grantRole(bytes32,address)", "hasRole(bytes32,address)", "isPaused()",
    "pauseFor(uint256)", "pauseUntil(uint256)", "renounceRole(bytes32,address)",
    "resume()", "revokeRole(bytes32,address)",
    "setExitRequestLimit(uint256,uint256,uint256)", "supportsInterface(bytes4)",
    "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)",
}
EVENTS = {
    "ExitRequestsLimitSet(uint256,uint256,uint256)", "Paused(uint256)", "Resumed()",
    "RoleAdminChanged(bytes32,bytes32,bytes32)", "RoleGranted(bytes32,address,address)",
    "RoleRevoked(bytes32,address,address)",
}
ERRORS = {
    "AdminCannotBeZero()", "ExitRequestsLimitExceeded(uint256,uint256)",
    "FeeRefundFailed()", "InsufficientFee(uint256,uint256)", "LimitExceeded()",
    "PauseUntilMustBeInFuture()", "PausedExpected()", "ResumedExpected()",
    "TooLargeExitsPerFrame()", "TooLargeFrameDuration()",
    "TooLargeMaxExitRequestsLimit()", "ZeroArgument(string)", "ZeroFrameDuration()",
    "ZeroPauseDuration()",
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
    "PAUSE_ROLE": ["0x7914b5a1539b97bd0bbd155757f25fd79a522d24",
                   "0x6019cb557978296ba3c08a7b73225c0975dfb2f7"],
    "RESUME_ROLE": ["0x7914b5a1539b97bd0bbd155757f25fd79a522d24"],
    "ADD_FULL_WITHDRAWAL_REQUEST_ROLE": [
        "0x0de4ea0184c2ad0baca7183356aea5b8d5bf5c6e",
        "0x610b517d380f287c239c93f8ef6ffbd567aa4ba5",
        "0xe181a377a2d2bde9a83f1474bc3db7a412de091e",
    ],
    "TW_EXIT_LIMIT_MANAGER_ROLE": ["0x3e40d73eb977dc6a537af587d48316fee66e9c8c"],
}
INPUT_SHA256 = {
    "git-provenance.json": "1996db8d22ba5468080e4c5726492fb0f7a08fc48e140a928cc5db55000eb81f",
    "lido/contracts/COMPILERS.md": "888504aefff340b47cd49f5b299fd3d3055c70ab56222098a961be87ef49e4b8",
    "lido/deployed-mainnet.json": "3428ba7a845ae27c69bd64d87dafda920df3fdfdc8df99da1caf3af55060fd15",
    "lido/hardhat.config.ts": "29b3e91ff197c0ea1df5b6401cc12982d3f684e7bf3e68b380096fe33e43b223",
    "lido/package.json": "5e6bd056082e23c6628aee085df5ce0743070d08d5a3e27496991e09f74b638e",
    "lido/yarn.lock": "d17f979eed36218b0bed85cf560bdc2e5d182e0c67aff6eabf2c68be8597c921",
    "rpc-blastapi.json": "132df9a8b836f8e91b611a8bc5565ca8f40d6b17bfe4233f6710d0f377fc98d6",
    "rpc-drpc.json": "a1b0b809bd9ae1d0a634c3e1f6dee621db8d6b95dca58e34de624931b669c0a5",
    "solc-emscripten-wasm32-list.json": "0ee86d7e0a30f0d90593ff64dfb56d192c514c8e33feebeb54446be55b12e5ad",
    "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js": "5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c",
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


def string(value: Any, label: str) -> str:
    require(isinstance(value, str), f"{label}: expected string")
    return value


def integer(value: Any, label: str) -> int:
    require(type(value) is int, f"{label}: expected integer")
    return value


def boolean(value: Any, label: str) -> bool:
    require(type(value) is bool, f"{label}: expected boolean")
    return value


def digest(value: Any, label: str, prefixed: bool = False) -> str:
    pattern = r"0x[0-9a-f]{64}" if prefixed else r"[0-9a-f]{64}"
    require(isinstance(value, str) and re.fullmatch(pattern, value), f"{label}: invalid digest")
    return value


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


def section_digest(value: Any) -> str:
    encoded = json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def validate_byte_artifact(value: Any, label: str, expected_bytes: int | None = None,
                           expected_sha256: str | None = None,
                           expected_keccak: str | None = None) -> bytes:
    row = exact_object(value, label, {"byteLength", "hex", "keccak256", "sha256"})
    raw_hex = string(row["hex"], f"{label}.hex")
    require(re.fullmatch(r"0x(?:[0-9a-f]{2})*", raw_hex) is not None, f"{label}: malformed hex")
    raw = bytes.fromhex(raw_hex[2:])
    require(integer(row["byteLength"], f"{label}.byteLength") == len(raw), f"{label}: length differs")
    require(row["sha256"] == hashlib.sha256(raw).hexdigest(), f"{label}: SHA-256 differs")
    require(row["keccak256"] == "0x" + keccak256(raw), f"{label}: Keccak differs")
    if expected_bytes is not None:
        require(len(raw) == expected_bytes, f"{label}: pinned length differs")
    if expected_sha256 is not None:
        require(row["sha256"] == expected_sha256, f"{label}: pinned SHA-256 differs")
    if expected_keccak is not None:
        require(row["keccak256"] == expected_keccak, f"{label}: pinned Keccak differs")
    return raw


def selector(signature: str) -> str:
    return "0x" + keccak256(signature.encode())[:8]


def validate_abi(value: Any) -> None:
    abi = exact_object(value, "abi", {
        "constructor", "functionCount", "functions", "eventCount", "events", "errorCount", "errors"
    })
    require(integer(abi["functionCount"], "functionCount") == 24
            and integer(abi["eventCount"], "eventCount") == 6
            and integer(abi["errorCount"], "errorCount") == 14, "ABI counts differ")
    constructor = abi["constructor"]
    require(isinstance(constructor, dict)
            and [arg["name"] for arg in constructor.get("inputs", [])] == [
                "admin", "lidoLocator", "maxExitRequestsLimit", "exitsPerFrame", "frameDurationInSec"]
            and [arg["type"] for arg in constructor["inputs"]] == [
                "address", "address", "uint256", "uint256", "uint256"]
            and constructor.get("stateMutability") == "nonpayable", "constructor ABI differs")
    function_rows = exact_list(abi["functions"], "functions", 24)
    signatures = []
    for index, item in enumerate(function_rows):
        row = exact_object(item, f"function[{index}]", {
            "entry", "payable", "returnTypes", "selector", "signature"})
        sig = string(row["signature"], f"function[{index}].signature")
        signatures.append(sig)
        require(row["selector"] == selector(sig), f"function[{index}]: selector differs")
        require(boolean(row["payable"], f"function[{index}].payable")
                == (sig.startswith("triggerFullWithdrawals(")), f"function[{index}]: payability differs")
        require(isinstance(row["entry"], dict) and row["entry"].get("type") == "function"
                and isinstance(row["returnTypes"], list), f"function[{index}]: entry differs")
    require(signatures == sorted(FUNCTIONS), "function surface/order differs")
    error_rows = exact_list(abi["errors"], "errors", 14)
    signatures = []
    for index, item in enumerate(error_rows):
        row = exact_object(item, f"error[{index}]", {"entry", "selector", "signature"})
        sig = string(row["signature"], f"error[{index}].signature")
        signatures.append(sig)
        require(row["selector"] == selector(sig) and row["entry"].get("type") == "error",
                f"error[{index}]: entry/selector differs")
    require(signatures == sorted(ERRORS), "error surface/order differs")
    event_rows = exact_list(abi["events"], "events", 6)
    signatures = []
    for index, item in enumerate(event_rows):
        row = exact_object(item, f"event[{index}]", {"entry", "indexed", "signature", "topic0"})
        sig = string(row["signature"], f"event[{index}].signature")
        signatures.append(sig)
        require(row["topic0"] == "0x" + keccak256(sig.encode())
                and row["indexed"] == [arg["indexed"] for arg in row["entry"].get("inputs", [])],
                f"event[{index}]: topic/indexing differs")
    require(signatures == sorted(EVENTS), "event surface/order differs")


def address_word(value: str) -> bytes:
    require(re.fullmatch(r"0x[0-9a-fA-F]{40}", value) is not None, "invalid address")
    return bytes.fromhex(value[2:]).rjust(32, b"\0")


def encode_parameters(parameters: dict[str, Any]) -> bytes:
    result = address_word(parameters["admin"]) + address_word(parameters["lidoLocator"])
    for key in ("maxExitRequestsLimit", "exitsPerFrame", "frameDurationInSec"):
        value = integer(parameters[key], key)
        require(0 <= value < 2**256, f"{key}: out of range")
        result += value.to_bytes(32, "big")
    return result


def validate_world(value: Any, label: str, creation: bytes, template: bytes,
                   references: list[dict[str, int]], expected_parameters: dict[str, Any]) -> bytes:
    world = exact_object(value, label, {
        "name", "parameters", "constructorSuffix", "fullCreateInput", "returnedRuntime",
        "immutableValues", "relations"})
    require(world["parameters"] == expected_parameters, f"{label}: parameters differ")
    suffix = encode_parameters(expected_parameters)
    require(world["constructorSuffix"] == "0x" + suffix.hex(), f"{label}: suffix differs")
    full = validate_byte_artifact(world["fullCreateInput"], f"{label}.fullCreateInput")
    require(full == creation + suffix, f"{label}: complete CREATE input relation differs")
    returned = validate_byte_artifact(world["returnedRuntime"], f"{label}.returnedRuntime", 8128)
    patched = bytearray(template)
    replacement = address_word(expected_parameters["lidoLocator"])
    for span in references:
        patched[span["start"]:span["start"] + span["length"]] = replacement
    require(returned == bytes(patched), f"{label}: immutable patch relation differs")
    require(world["immutableValues"] == {"LOCATOR": "0x" + replacement.hex()},
            f"{label}: immutable value differs")
    require(world["relations"] == {
        "runtimeDiffOnlyAtImmutableSpans": True, "sameCompilerSettings": True,
        "sameCreationTemplate": True, "suffixIsExactAbiEncoding": True,
    }, f"{label}: relation flags differ")
    return returned


def validate_lock_schema(root: Any) -> None:
    root = exact_object(root, "lock", {
        "_comment", "schema", "generator", "target", "provenance", "compiler", "abi",
        "artifacts", "snapshot", "rpc", "sectionDigests"})
    require(root["_comment"] == "GENERATED by scripts/lido-twg-reference.py; do not edit by hand."
            and integer(root["schema"], "schema") == 1, "generated marker/schema differs")
    require(root["generator"] == {
        "implementation": "scripts/lido-twg-reference.py", "name": "blanc-lido-twg-reference",
        "networkFreeOrdinaryCheck": True,
        "regenerationCommand": "python3 scripts/lido-twg-reference.py generate", "version": 1,
    }, "generator identity differs")
    require(root["target"] == {
        "address": "0xDC00116a0D3E064427dA2600449cfD2566B3037B", "chainId": 1,
        "contract": "TriggerableWithdrawalsGateway", "directDeployment": True,
        "releaseCommit": "17005714f151e5502c559932319a3f2f74ac2436", "releaseTag": "v4.0.0",
        "sourcePath": "contracts/0.8.9/TriggerableWithdrawalsGateway.sol",
    }, "target identity differs")
    provenance = exact_object(root["provenance"], "provenance", {
        "route", "repository", "lidoCommit", "lidoTag", "openzeppelinCommit",
        "openzeppelinTag", "closureComplete", "inputFiles", "sourceFiles", "buildFiles",
        "claimBoundary"})
    require(provenance["route"] == "pinned-source-compilation"
            and provenance["repository"] == "https://github.com/lidofinance/core"
            and provenance["lidoCommit"] == "17005714f151e5502c559932319a3f2f74ac2436"
            and provenance["lidoTag"] == "v4.0.0"
            and provenance["openzeppelinCommit"] == "6bd6b76d1156e20e45d1016f355d154141c7e5b9"
            and provenance["openzeppelinTag"] == "v4.4.1"
            and boolean(provenance["closureComplete"], "closureComplete"),
            "provenance identity differs")
    inputs = exact_list(provenance["inputFiles"], "inputFiles")
    paths = []
    for index, item in enumerate(inputs):
        row = exact_object(item, f"inputFiles[{index}]", {"path", "sha256"})
        paths.append(string(row["path"], f"inputFiles[{index}].path"))
        digest(row["sha256"], f"inputFiles[{index}].sha256")
    require(paths == sorted(INPUT_SHA256), "input inventory paths differ")
    require({row["path"]: row["sha256"] for row in inputs} == INPUT_SHA256,
            "input inventory SHA-256 pins differ")
    sources = exact_list(provenance["sourceFiles"], "sourceFiles", 13)
    source_units = []
    for index, item in enumerate(sources):
        row = exact_object(item, f"sourceFiles[{index}]", {
            "byteLength", "gitBlob", "inputPath", "keccak256", "sha256", "sourceUnit"})
        source_units.append(string(row["sourceUnit"], f"sourceFiles[{index}].sourceUnit"))
        require(integer(row["byteLength"], "source byteLength") > 0
                and re.fullmatch(r"[0-9a-f]{40}", row["gitBlob"]) is not None,
                f"sourceFiles[{index}]: identity differs")
        digest(row["sha256"], "source SHA-256")
        digest(row["keccak256"], "source Keccak", True)
        require(row["sha256"] == INPUT_SHA256[row["inputPath"]],
                f"sourceFiles[{index}]: input identity differs")
    require(source_units == sorted(SOURCE_UNITS), "source membership/order differs")
    build_files = exact_list(provenance["buildFiles"], "buildFiles", 5)
    for index, row in enumerate(build_files):
        exact_object(row, f"buildFiles[{index}]", {"gitBlob", "inputPath", "sha256", "upstreamPath"})
    require([(row["inputPath"], row["upstreamPath"], row["gitBlob"], row["sha256"])
             for row in build_files] == [
        ("lido/contracts/COMPILERS.md", "contracts/COMPILERS.md", "4a7cc445ea7854a6f25931d213ab66ad037cb6ae", INPUT_SHA256["lido/contracts/COMPILERS.md"]),
        ("lido/deployed-mainnet.json", "deployed-mainnet.json", "1aa9165e97936ef1020ac873115ba35c3b94dd28", INPUT_SHA256["lido/deployed-mainnet.json"]),
        ("lido/hardhat.config.ts", "hardhat.config.ts", "8156497feda3a05d0142d53cc99f9212ea3f3ee1", INPUT_SHA256["lido/hardhat.config.ts"]),
        ("lido/package.json", "package.json", "2d9084a710482ff6957241ba4d64eb42b15bc8dc", INPUT_SHA256["lido/package.json"]),
        ("lido/yarn.lock", "yarn.lock", "b5939dc1dfac88bcdb4786c7c99344e4fb556a5e", INPUT_SHA256["lido/yarn.lock"]),
    ], "build-file provenance differs")
    require(provenance["claimBoundary"] ==
            "The source-compiled artifacts and dated on-chain equality snapshot do not verify the deployed Solidity contract or recover its deployment transaction.",
            "claim boundary differs")
    compiler = exact_object(root["compiler"], "compiler", {
        "version", "longVersion", "packaging", "binary", "releaseManifestEntry", "settings",
        "standardInputSha256", "standardOutputSha256", "outputReproducedByteForByte"})
    require(compiler["version"] == "0.8.9" and compiler["longVersion"] == "0.8.9+commit.e5eed63a"
            and compiler["packaging"] == "emscripten-wasm32"
            and boolean(compiler["outputReproducedByteForByte"], "compiler output relation"),
            "compiler identity differs")
    require(compiler["binary"] == {
        "byteLength": 26173264,
        "file": "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js",
        "keccak256": "0xbc470ab3442e78bb4d3f16c01c39b2f160f4f34eb4373efed11c234e1c7f6ca0",
        "sha256": "5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c",
    }, "compiler binary identity differs")
    require(compiler["settings"] == {
        "evmVersion": "istanbul", "optimizer": {"enabled": True, "runs": 200},
        "outputSelection": {"*": {"*": ["abi", "metadata", "evm.bytecode.object",
            "evm.deployedBytecode.object", "evm.deployedBytecode.immutableReferences"]}},
    }, "compiler settings differ")
    require(compiler["releaseManifestEntry"] == {
        "build": "commit.e5eed63a",
        "keccak256": "0xbc470ab3442e78bb4d3f16c01c39b2f160f4f34eb4373efed11c234e1c7f6ca0",
        "longVersion": "0.8.9+commit.e5eed63a",
        "path": "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js",
        "sha256": "0x5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c",
        "urls": ["dweb:/ipfs/QmfFq3MvisCSUJy8N8EVsBribgPbdpTZb7tQ2eHYw7dwag"],
        "version": "0.8.9",
    }, "compiler release manifest row differs")
    require(compiler["standardInputSha256"] == INPUT_SHA256["standard-json-input.json"]
            and compiler["standardOutputSha256"] == INPUT_SHA256["standard-json-output.json"],
            "compiler input/output digests differ")
    validate_abi(root["abi"])
    artifacts = exact_object(root["artifacts"], "artifacts", {
        "creationTemplate", "runtimeTemplate", "immutableReferences", "immutableNames", "worlds"})
    creation = validate_byte_artifact(
        artifacts["creationTemplate"], "creationTemplate", 10096,
        "7b854f9c3729427e47a102541b1f8e7403febd558f73d8e4805bc364a10488e5",
        "0x01e830efc93bc83560bc09727e093b0d285be1c6f4f0bdf7ccf27638140265d7")
    template = validate_byte_artifact(
        artifacts["runtimeTemplate"], "runtimeTemplate", 8128,
        "98c115bfba7c7bed2dd5ff53c5b72937198d580ce4109872fdb0624bd2cc56c5",
        "0xb6cf752ff72e03f927a4652cb9fe999e77a528e1a656755e1a7b7335f07635f0")
    require(artifacts["immutableReferences"] == {"1089": [
        {"length": 32, "start": 1500}, {"length": 32, "start": 4157}]}
        and artifacts["immutableNames"] == {"1089": "LOCATOR"}, "immutable map differs")
    worlds = exact_list(artifacts["worlds"], "worlds", 2)
    official_parameters = {
        "admin": "0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c",
        "lidoLocator": "0xC1d0b3DE6792Bf6b4b37EccdcC24e45978Cfd2Eb",
        "maxExitRequestsLimit": 11200, "exitsPerFrame": 1, "frameDurationInSec": 48,
    }
    corpus_parameters = {
        "admin": "0x111122223333444455556666777788889999AaAa",
        "lidoLocator": "0x22223333444455556666777788889999AaAaBbBb",
        "maxExitRequestsLimit": 17, "exitsPerFrame": 3, "frameDurationInSec": 48,
    }
    require(worlds[0]["name"] == "official-mainnet-parameters"
            and worlds[1]["name"] == "differential-corpus", "world names/order differ")
    official_runtime = validate_world(worlds[0], "worlds[0]", creation, template,
                                      artifacts["immutableReferences"]["1089"], official_parameters)
    validate_world(worlds[1], "worlds[1]", creation, template,
                   artifacts["immutableReferences"]["1089"], corpus_parameters)
    require(hashlib.sha256(official_runtime).hexdigest()
            == "f578d6b2d39783239f3d7cbfa69e5e24665afc5e77475680dc341459ea5b3e6f"
            and "0x" + keccak256(official_runtime)
            == "0xbf27dab01ae7fb4507657a02d975bd38aeea9eaba4498225da3a0ee5f815f123",
            "official runtime pin differs")
    snapshot = exact_object(root["snapshot"], "snapshot", {
        "kind", "pinnedAt", "chainId", "block", "account", "isPaused",
        "resumeSinceTimestamp", "circuitBreaker", "circuitBreakerHasPauseRole", "roles", "relations"})
    require(snapshot["kind"] == "selection-time-mainnet-state" and snapshot["pinnedAt"] == "2026-08-30"
            and snapshot["chainId"] == "0x1"
            and snapshot["block"] == {
                "number": "0x18ab2ef", "hash": "0xe80828e439dcfe0a443115004c86072896bb1fe71ee68c4dc6ce7946b0f0603e",
                "timestamp": "0x6a93ee57", "stateRoot": "0x83d83df9036b08532594fa240f7a1879e7666ec3b640789dc02a9e5c238f0010"},
            "snapshot block differs")
    require(snapshot["account"] == {
        "address": "0xdc00116a0d3e064427da2600449cfd2566b3037b",
        "balance": "0x0", "codeHash": "0xbf27dab01ae7fb4507657a02d975bd38aeea9eaba4498225da3a0ee5f815f123",
        "nonce": "0x1", "storageHash": "0x71222b148f5a50b498b51f80add628df61211d5fcae47df100e1542f6371e7b7",
    }, "snapshot account differs")
    require(boolean(snapshot["isPaused"], "isPaused") is False
            and integer(snapshot["resumeSinceTimestamp"], "resumeSinceTimestamp") == 0
            and snapshot["circuitBreaker"] == "0x6019CB557978296BA3C08a7B73225C0975DFB2F7"
            and boolean(snapshot["circuitBreakerHasPauseRole"], "hasPauseRole"),
            "snapshot pause state differs")
    require(set(snapshot["roles"]) == set(ROLES), "snapshot role set differs")
    for role_name in ROLES:
        require(snapshot["roles"][role_name] == {
            "adminRole": ROLES["DEFAULT_ADMIN_ROLE"], "members": ROLE_MEMBERS[role_name]},
            f"snapshot {role_name} differs")
    require(snapshot["relations"] == {
        "codeHashEqualsRuntimeKeccak": True, "compiledOfficialRuntimeEqualsCode": True,
        "directAccountNoProxyClaim": True,
    }, "snapshot relations differ")
    rpc = exact_object(root["rpc"], "rpc", {"captures", "agreement"})
    captures = exact_list(rpc["captures"], "rpc.captures", 2)
    require([(row["captureDateUtc"], row["operator"], row["url"], row["file"], row["envelopeSha256"])
             for row in captures] == [
        ("2026-08-30", "dRPC", "https://eth.drpc.org", "rpc-drpc.json", INPUT_SHA256["rpc-drpc.json"]),
        ("2026-08-30", "BlastAPI", "https://eth-mainnet.public.blastapi.io", "rpc-blastapi.json", INPUT_SHA256["rpc-blastapi.json"])],
        "RPC operator order/identity differs")
    for index, row in enumerate(captures):
        require(set(row) == {"captureDateUtc", "file", "operator", "url", "envelopeSha256", "responseSha256"},
                f"rpc.captures[{index}]: keys differ")
        digest(row["envelopeSha256"], "RPC envelope SHA-256")
        require(isinstance(row["responseSha256"], dict) and len(row["responseSha256"]) == 25,
                f"rpc.captures[{index}]: response inventory differs")
        for value in row["responseSha256"].values():
            digest(value, "RPC response SHA-256")
    require(rpc["agreement"] == {
        "blockHeaderEqual": True, "codeEqual": True, "proofFieldsEqual": True,
        "rolePauseCallsEqual": True,
    }, "RPC agreement differs")
    section_keys = {"generator", "target", "provenance", "compiler", "abi", "artifacts", "snapshot", "rpc"}
    section_digests = exact_object(root["sectionDigests"], "sectionDigests", section_keys)
    for key in section_keys:
        require(section_digests[key] == section_digest(root[key]), f"section digest differs: {key}")


def load_strict(path: Path) -> Any:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result
    return json.loads(path.read_bytes(), object_pairs_hook=pairs)


def main() -> int:
    try:
        validate_lock_schema(load_strict(LOCK))
    except (OSError, json.JSONDecodeError, SchemaError) as exc:
        print(f"REGRESSION — Lido TWG reference schema: {exc}")
        return 1
    print("OK — Lido TWG reference schema")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
