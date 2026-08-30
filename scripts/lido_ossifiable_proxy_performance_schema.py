#!/usr/bin/env python3
"""Independent static contract for the frozen OssifiableProxy performance campaign.

The campaign manifest intentionally contains no measurements.  This module
independently freezes its 25 primary cells, order, denominator, measurement
semantics, score threshold, fixture references, and external reference
identities.  It also defines the immutable schema used later by both the
baseline and final result ledgers.  Nothing in this module executes EVM code or
collects a performance measurement.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable


DEFAULT_ROOT = Path(os.environ.get(
    "LIDO_OSSIFIABLE_PROXY_PERFORMANCE_ROOT",
    Path(__file__).resolve().parents[1],
)).resolve()
MANIFEST_RELATIVE = Path("scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json")
REFERENCE_LOCK_RELATIVE = Path("scripts/lido-ossifiable-proxy-reference.json")
REFERENCE_INPUTS_RELATIVE = Path("scripts/reference/lido-ossifiable-proxy/inputs")

MANIFEST_FORMAT = "blanc.lido-ossifiable-proxy.performance-campaign"
RESULT_FORMAT = "blanc.lido-ossifiable-proxy.performance-result"
MANIFEST_DIGEST = "d257394b6eb56b02072b68037896a863e96a42f405690423024bc6b432f34eaa"
SUPERSEDED_MANIFEST_DIGEST = "d234fb691fdc3759cf35ee12cee60a73fbf4899d5edeaa05a956a465014cb7ca"
REFERENCE_LOCK_SHA256 = "1c9f380f2475e5a54eb870e4f41ceeb09a0f9c227271ad14900fe82b0df1b688"
EELS_COMMIT = "4198b9c5996713b268aed602739d5aa40e277694"
CAMPAIGN_BASE_COMMIT = "226bfad05b8bdd4623b600ca36fb527f003d85dc"
MINIMUM_STRICT_WINS = 13
DENOMINATOR = 25

MANIFEST_CANONICALIZATION = (
    'json.dumps(parsed, sort_keys=True, separators=(",", ":"), '
    'ensure_ascii=True).encode("utf-8")'
)
MANIFEST_DIGEST_SCOPE = (
    "the entire parsed document with /campaign/digest/value replaced by the empty string"
)
RESULT_DIGEST_SCOPE = (
    "the entire parsed document with /result/digest/value replaced by the empty string"
)

CELL_SPECS = [
    ("A1", "artifact/deployment", "returned-runtime-byte-length", "artifact"),
    ("A2", "artifact/deployment", "creation-template-byte-length", "artifact"),
    ("A3", "artifact/deployment", "direct-create-gas-used", "direct-create-message"),
    ("A4", "artifact/deployment", "direct-create-gas-used", "direct-create-message"),
    ("F1", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("F2", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("F3", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("F4", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("F5", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("F6", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("F7", "forwarding", "direct-call-gas-used", "direct-call-message"),
    ("C1", "control", "direct-call-gas-used", "direct-call-message"),
    ("C2", "control", "direct-call-gas-used", "direct-call-message"),
    ("C3", "control", "direct-call-gas-used", "direct-call-message"),
    ("C4", "control", "direct-call-gas-used", "direct-call-message"),
    ("C5", "control", "direct-call-gas-used", "direct-call-message"),
    ("C6", "control", "direct-call-gas-used", "direct-call-message"),
    ("C7", "control", "direct-call-gas-used", "direct-call-message"),
    ("C8", "control", "direct-call-gas-used", "direct-call-message"),
    ("C9", "control", "direct-call-gas-used", "direct-call-message"),
    ("N1", "negative", "direct-call-gas-used", "direct-call-message"),
    ("N2", "negative", "direct-call-gas-used", "direct-call-message"),
    ("N3", "negative", "direct-call-gas-used", "direct-call-message"),
    ("N4", "negative", "direct-call-gas-used", "direct-call-message"),
    ("N5", "negative", "direct-call-gas-used", "direct-call-message"),
]
CELL_ORDER = [row[0] for row in CELL_SPECS]
CELL_SPEC_BY_ID = {row[0]: row for row in CELL_SPECS}

MEASUREMENT_CONTRACT = {
    "artifactScalars": {
        "creation-template-byte-length": (
            "number of exact creation-template bytes before appending ABI constructor arguments"
        ),
        "returned-runtime-byte-length": (
            "number of exact runtime bytes returned by successful CREATE with canonical-empty arguments"
        ),
    },
    "callScalar": {
        "formula": "message.gas - output.gas_left",
        "name": "direct-call-gas-used",
        "refundAccounting": "pre-refund",
        "transactionIntrinsicGasIncluded": False,
    },
    "createScalar": {
        "createCodeDepositGasIncluded": True,
        "formula": "message.gas - output.gas_left",
        "initCodeExecutionIncluded": True,
        "name": "direct-create-gas-used",
        "refundAccounting": "pre-refund",
        "transactionIntrinsicGasIncluded": False,
    },
    "freshWorldPerSidePerCell": True,
    "gasAllowance": "20000000",
    "messageFlags": {
        "codeAddress": "null for direct CREATE; proxy-target for direct calls",
        "currentTarget": "proxy-target",
        "depth": "0",
        "disablePrecompiles": False,
        "isStatic": False,
        "shouldTransferValue": True,
        "target": "empty bytes for direct CREATE; proxy-target for direct calls",
    },
    "primaryFork": "Prague",
    "semanticProjection": [
        "outer status",
        "exact outer returndata",
        "proxy logical storage including ERC-1967 and fixture slots",
        "ETH balances",
        "ordered exact logs",
        (
            "DELEGATECALL code address, proxy storage owner, caller, value, calldata, "
            "status, and returndata"
        ),
        "CREATE returned runtime and installed-code identity for deployment cells",
    ],
    "sideSymmetry": (
        "within a cell, Solidity and Blanc receive the identical resolved block environment, "
        "transaction environment, caller, target, value, calldata or constructor tuple, mock "
        "accounts and bytecode, logical prestate, message access sets, and gas allowance; only "
        "the side-owned candidate artifact and representation-specific storage encoding may differ"
    ),
    "warmColdRule": (
        "forwarding-warm is forwarding-cold plus exactly canonical-implementation in "
        "accessedAddresses and (proxy-target, implementation-slot) in accessedStorageKeys; "
        "there is no other state or environment change"
    ),
}

SCORE_CONTRACT = {
    "classification": {
        "incomparable": "instrumentation failure or proved semantic mismatch; counts as a non-win",
        "loss": "Blanc named scalar is greater than the reference named scalar",
        "strict-win": "Blanc named scalar is less than the reference named scalar",
        "tie": "Blanc named scalar equals the reference named scalar; counts as a non-win",
    },
    "denominator": DENOMINATOR,
    "fixedOrder": CELL_ORDER,
    "minimumStrictWins": MINIMUM_STRICT_WINS,
    "reportAllCells": True,
    "semanticAgreementRequiredBeforeScoring": True,
    "unit": {"A1": "bytes", "A2": "bytes", "A3-N5": "gas"},
}

EXPECTED_FIXTURE_KEYS = {
    "accessSets", "accountTemplates", "addresses", "artifactBindings",
    "blockEnvironment", "calldata", "constructorTuples", "events",
    "expectedSemantics", "mockImplementations", "proxyStates", "setupFixtures",
    "transactionEnvironment", "values",
}
EXPECTED_NAMED_FIXTURES = {
    "accountTemplates": {"caller", "mock-implementation"},
    "accessSets": {
        "control-admin-cold", "control-outsider-cold", "create-entry",
        "forwarding-cold", "forwarding-warm",
    },
    "addresses": {
        "canonical-admin", "canonical-implementation", "coinbase", "control-admin",
        "creator", "forwarding-caller", "new-admin", "new-implementation",
        "no-code-implementation", "proxy-target", "proxyTargetDerivation", "zero",
    },
    "artifactBindings": {"creationTemplate", "returnedRuntime"},
    "calldata": {
        "change-admin-new", "change-admin-zero", "empty", "fallback-256",
        "fallback-32", "get-admin", "get-implementation", "get-is-ossified",
        "ossify", "setup-data-32", "upgrade-and-call-empty-false",
        "upgrade-and-call-empty-true", "upgrade-and-call-nonempty-false",
        "upgrade-new", "upgrade-no-code",
    },
    "constructorTuples": {"canonical-empty", "canonical-nonempty-setup"},
    "events": {
        "AdminChanged(address,address)", "ProxyOssified()", "Upgraded(address)",
    },
    "expectedSemantics": {
        "change-admin-success", "create-empty-success", "create-nonempty-setup-success",
        "fallback-echo-revert-256", "fallback-echo-success-256",
        "fallback-echo-success-32", "fallback-empty-revert-32", "get-admin-success",
        "get-implementation-success", "get-is-ossified-false", "no-code-string-revert",
        "not-admin-revert", "ossified-precedence-revert", "ossify-success",
        "receive-empty-success", "upgrade-child-revert-rollback",
        "upgrade-empty-false-skip", "upgrade-empty-forced-setup-success",
        "upgrade-nonempty-setup-success", "upgrade-success", "zero-admin-string-revert",
    },
    "mockImplementations": {
        "echo-revert", "echo-success", "empty-revert", "setup-empty",
        "setup-nonempty", "stop",
    },
    "proxyStates": {"ossified", "unossified"},
    "setupFixtures": {"empty", "nonempty"},
    "values": {
        "adequate-message-gas", "empty-setup-value", "fixture-slot", "receive-value",
        "setup-data-32", "zero",
    },
}

EXPECTED_IDENTITIES = {
    "blanc": {
        "campaignBaseCommit": CAMPAIGN_BASE_COMMIT,
        "candidateArtifactIdentity": (
            "not a campaign input: each immutable baseline/final result must pin the exact "
            "candidate commit and evaluator-emitted artifact digests"
        ),
    },
    "execution": {
        "defaultRoot": "~/execution-specs",
        "eelsCommit": EELS_COMMIT,
        "callEntrypoint": "ethereum.prague.vm.interpreter.process_message_call",
        "createEntrypoint": "ethereum.prague.vm.interpreter.process_create_message",
        "fork": "Prague",
        "network": False,
        "python": "venv/bin/python",
        "pythonPath": "src",
        "requiredEnvironment": {
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONPATH": "${EELS_ROOT}/src",
        },
        "rootEnv": "EELS_ROOT",
    },
    "reference": {
        "compiler": {
            "build": "commit.e5eed63a",
            "evmVersion": "istanbul",
            "keccak256": "0xbc470ab3442e78bb4d3f16c01c39b2f160f4f34eb4373efed11c234e1c7f6ca0",
            "listSha256": "0ee86d7e0a30f0d90593ff64dfb56d192c514c8e33feebeb54446be55b12e5ad",
            "longVersion": "0.8.9+commit.e5eed63a",
            "optimizerEnabled": True,
            "optimizerRuns": 200,
            "path": "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js",
            "platform": "emscripten-wasm32",
            "sha256": "0x5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c",
            "viaIR": False,
        },
        "referenceLock": str(REFERENCE_LOCK_RELATIVE),
        "release": "lidofinance/core-v4.0.0",
        "releaseCommit": "17005714f151e5502c559932319a3f2f74ac2436",
        "sourceBlob": "d4ccec05c453b15cc17023e3950e44341a66a4a4",
        "sourcePath": "contracts/0.8.9/proxy/OssifiableProxy.sol",
        "sourceSha256": "3fb48bc4a40c887dd581178d05316745c1b1c393a8e64787ef2a7075f1e7ce6d",
    },
}

EXPECTED_EXTERNAL_POINTERS = {
    "scripts/lido-ossifiable-proxy-reference.json#/artifacts/creationTemplate",
    "scripts/lido-ossifiable-proxy-reference.json#/artifacts/runtime",
}
IMPLEMENTATION_SLOT = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"
ADMIN_SLOT = "0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103"


class SchemaError(RuntimeError):
    """A static manifest or result contract violation."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SchemaError(message)


def strict_json(data: bytes, label: str) -> Any:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            require(key not in result, f"{label}: duplicate JSON key {key!r}")
            result[key] = value
        return result

    def invalid(value: str) -> None:
        raise SchemaError(f"{label}: non-finite JSON value {value}")

    try:
        return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SchemaError(f"{label}: invalid JSON: {exc}") from exc


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def compact_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode("utf-8")


def exact_object(value: Any, path: str, keys: Iterable[str]) -> dict[str, Any]:
    expected = set(keys)
    require(isinstance(value, dict), f"{path}: expected object")
    require(
        set(value) == expected,
        f"{path}: expected fields {sorted(expected)}, found {sorted(value)}",
    )
    return value


def exact_list(value: Any, path: str, length: int | None = None) -> list[Any]:
    require(isinstance(value, list), f"{path}: expected array")
    if length is not None:
        require(len(value) == length, f"{path}: expected {length} entries, found {len(value)}")
    return value


def text(value: Any, path: str, nonempty: bool = False) -> str:
    require(isinstance(value, str), f"{path}: expected string")
    if nonempty:
        require(bool(value.strip()), f"{path}: expected nonempty string")
    return value


def integer(value: Any, path: str, minimum: int | None = None) -> int:
    require(type(value) is int, f"{path}: expected integer")
    if minimum is not None:
        require(value >= minimum, f"{path}: expected integer >= {minimum}")
    return value


def boolean(value: Any, path: str) -> bool:
    require(type(value) is bool, f"{path}: expected boolean")
    return value


def fullmatch(value: Any, path: str, expression: str) -> str:
    parsed = text(value, path)
    require(re.fullmatch(expression, parsed) is not None, f"{path}: malformed value {parsed!r}")
    return parsed


def sha256_text(value: Any, path: str) -> str:
    return fullmatch(value, path, r"[0-9a-f]{64}")


def keccak_text(value: Any, path: str) -> str:
    return fullmatch(value, path, r"0x[0-9a-f]{64}")


def address_text(value: Any, path: str) -> str:
    return fullmatch(value, path, r"0x[0-9a-f]{40}")


def hex_bytes(value: Any, path: str) -> bytes:
    encoded = fullmatch(value, path, r"0x(?:[0-9a-f]{2})*")
    return bytes.fromhex(encoded[2:])


def manifest_digest(value: dict[str, Any]) -> str:
    copied = copy.deepcopy(value)
    copied["campaign"]["digest"]["value"] = ""
    return hashlib.sha256(compact_bytes(copied)).hexdigest()


def result_digest(value: dict[str, Any]) -> str:
    copied = copy.deepcopy(value)
    copied["result"]["digest"]["value"] = ""
    return hashlib.sha256(compact_bytes(copied)).hexdigest()


# Pure Keccak-256, deliberately independent of the reference-lock checker.
_MASK = (1 << 64) - 1
_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
_ROT = [
    [0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56], [27, 20, 39, 8, 14],
]


def _rol(value: int, count: int) -> int:
    if count == 0:
        return value
    return ((value << count) | (value >> (64 - count))) & _MASK


def _keccak_f(state: list[int]) -> None:
    for rc in _RC:
        columns = [
            state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
            for x in range(5)
        ]
        delta = [columns[(x - 1) % 5] ^ _rol(columns[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= delta[x]
        shuffled = [0] * 25
        for x in range(5):
            for y in range(5):
                shuffled[y + 5 * ((2 * x + 3 * y) % 5)] = _rol(
                    state[x + 5 * y], _ROT[x][y],
                )
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = shuffled[x + 5 * y] ^ (
                    (~shuffled[(x + 1) % 5 + 5 * y])
                    & shuffled[(x + 2) % 5 + 5 * y]
                )
                state[x + 5 * y] &= _MASK
        state[0] ^= rc


def keccak256(data: bytes) -> str:
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
        _keccak_f(state)
    return "".join(item.to_bytes(8, "little").hex() for item in state)[:64]


def _require_named(mapping: dict[str, Any], name: Any, path: str) -> Any:
    key = text(name, path)
    require(key in mapping, f"{path}: unresolved fixture reference {key!r}")
    return mapping[key]


def _walk_strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from _walk_strings(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from _walk_strings(item)


def _decode_pointer_token(token: str, path: str) -> str:
    require(re.search(r"~(?![01])", token) is None, f"{path}: invalid JSON Pointer escape")
    return token.replace("~1", "/").replace("~0", "~")


def resolve_json_pointer(document: Any, pointer: str, path: str) -> Any:
    require(pointer.startswith("/"), f"{path}: JSON Pointer must start with '/'")
    current = document
    for raw_token in pointer.split("/")[1:]:
        token = _decode_pointer_token(raw_token, path)
        if isinstance(current, dict):
            require(token in current, f"{path}: unresolved JSON Pointer token {token!r}")
            current = current[token]
        elif isinstance(current, list):
            require(re.fullmatch(r"0|[1-9][0-9]*", token) is not None,
                    f"{path}: invalid array index {token!r}")
            index = int(token)
            require(index < len(current), f"{path}: JSON Pointer array index out of range")
            current = current[index]
        else:
            raise SchemaError(f"{path}: JSON Pointer traverses a scalar")
    return current


def split_external_pointer(value: str, path: str) -> tuple[Path, str]:
    require(value.count("#") == 1, f"{path}: expected one JSON Pointer fragment")
    file_part, pointer = value.split("#", 1)
    require(file_part == str(REFERENCE_LOCK_RELATIVE), f"{path}: reference file identity differs")
    require(pointer.startswith("/"), f"{path}: missing absolute JSON Pointer fragment")
    return Path(file_part), pointer


def _repo_path(root: Path, relative: Path, path: str) -> Path:
    require(not relative.is_absolute(), f"{path}: absolute repository path forbidden")
    resolved = (root / relative).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError as exc:
        raise SchemaError(f"{path}: repository path escapes root") from exc
    return resolved


def _validate_artifact_row(value: Any, path: str) -> tuple[dict[str, Any], bytes]:
    row = exact_object(value, path, {"byteLength", "hex", "keccak256", "sha256"})
    raw = hex_bytes(row["hex"], f"{path}.hex")
    require(integer(row["byteLength"], f"{path}.byteLength", 0) == len(raw),
            f"{path}: byte length differs from bytes")
    require(sha256_text(row["sha256"], f"{path}.sha256") == hashlib.sha256(raw).hexdigest(),
            f"{path}: SHA-256 differs from bytes")
    require(keccak_text(row["keccak256"], f"{path}.keccak256") == "0x" + keccak256(raw),
            f"{path}: Keccak-256 differs from bytes")
    return row, raw


def _validate_artifact_identity(value: Any, path: str) -> dict[str, Any]:
    row = exact_object(value, path, {"byteLength", "keccak256", "sha256"})
    integer(row["byteLength"], f"{path}.byteLength", 0)
    keccak_text(row["keccak256"], f"{path}.keccak256")
    sha256_text(row["sha256"], f"{path}.sha256")
    return row


def _artifact_identity(row: dict[str, Any]) -> dict[str, Any]:
    return {key: row[key] for key in ("byteLength", "keccak256", "sha256")}


def _git_blob_sha1(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode()
    return hashlib.sha1(header + data).hexdigest()


def _abi_constructor_arguments(implementation: str, admin: str, data: bytes) -> bytes:
    def address_word(value: str) -> bytes:
        return bytes(12) + bytes.fromhex(value[2:])

    padded = data + bytes((-len(data)) % 32)
    return (
        address_word(implementation)
        + address_word(admin)
        + (96).to_bytes(32, "big")
        + len(data).to_bytes(32, "big")
        + padded
    )


def _validate_fixture_shapes(manifest: dict[str, Any]) -> None:
    fixtures = exact_object(manifest["fixtures"], "manifest.fixtures", EXPECTED_FIXTURE_KEYS)
    for section, expected in EXPECTED_NAMED_FIXTURES.items():
        value = fixtures[section]
        require(isinstance(value, dict), f"manifest.fixtures.{section}: expected object")
        require(set(value) == expected,
                f"manifest.fixtures.{section}: key membership drifted")

    addresses = fixtures["addresses"]
    for name, value in addresses.items():
        if name != "proxyTargetDerivation":
            address_text(value, f"manifest.fixtures.addresses.{name}")

    for name, row in fixtures["calldata"].items():
        row = exact_object(row, f"manifest.fixtures.calldata.{name}", {"byteLength", "hex"})
        raw = hex_bytes(row["hex"], f"manifest.fixtures.calldata.{name}.hex")
        require(integer(row["byteLength"], f"manifest.fixtures.calldata.{name}.byteLength", 0)
                == len(raw), f"manifest.fixtures.calldata.{name}: byte length differs")

    for name, row in fixtures["mockImplementations"].items():
        path = f"manifest.fixtures.mockImplementations.{name}"
        row = exact_object(row, path, {"byteLength", "description", "hex", "sha256"})
        raw = hex_bytes(row["hex"], f"{path}.hex")
        text(row["description"], f"{path}.description", nonempty=True)
        require(integer(row["byteLength"], f"{path}.byteLength", 0) == len(raw),
                f"{path}: byte length differs")
        require(sha256_text(row["sha256"], f"{path}.sha256") == hashlib.sha256(raw).hexdigest(),
                f"{path}: SHA-256 differs from bytes")

    for name, row in fixtures["constructorTuples"].items():
        path = f"manifest.fixtures.constructorTuples.{name}"
        row = exact_object(row, path, {
            "abiArgumentsByteLength", "abiArgumentsHex", "admin", "data",
            "implementation", "types",
        })
        implementation = address_text(row["implementation"], f"{path}.implementation")
        admin = address_text(row["admin"], f"{path}.admin")
        data = hex_bytes(row["data"], f"{path}.data")
        raw = hex_bytes(row["abiArgumentsHex"], f"{path}.abiArgumentsHex")
        require(row["types"] == ["address", "address", "bytes"], f"{path}.types: differs")
        require(integer(row["abiArgumentsByteLength"], f"{path}.abiArgumentsByteLength", 0)
                == len(raw), f"{path}: ABI byte length differs")
        require(raw == _abi_constructor_arguments(implementation, admin, data),
                f"{path}: ABI encoding differs")
        require(implementation == addresses["canonical-implementation"],
                f"{path}: implementation fixture differs")
        require(admin == addresses["canonical-admin"], f"{path}: admin fixture differs")

    setup_references: set[str] = set()
    for name, row in fixtures["setupFixtures"].items():
        path = f"manifest.fixtures.setupFixtures.{name}"
        row = exact_object(row, path, {"calldata", "implementationCode", "storageOwner", "write"})
        _require_named(fixtures["calldata"], row["calldata"], f"{path}.calldata")
        setup_references.add(row["calldata"])
        _require_named(fixtures["mockImplementations"], row["implementationCode"],
                       f"{path}.implementationCode")
        _require_named(addresses, row["storageOwner"], f"{path}.storageOwner")
        write = exact_object(row["write"], f"{path}.write", {"key", "value"})
        fullmatch(write["key"], f"{path}.write.key", r"0x[0-9a-f]{64}")
        fullmatch(write["value"], f"{path}.write.value", r"0x[0-9a-f]{64}")

    cold = fixtures["accessSets"]["forwarding-cold"]
    warm = fixtures["accessSets"]["forwarding-warm"]
    for name, row in fixtures["accessSets"].items():
        path = f"manifest.fixtures.accessSets.{name}"
        row = exact_object(row, path, {"accessedAddresses", "accessedStorageKeys"})
        values = exact_list(row["accessedAddresses"], f"{path}.accessedAddresses")
        require(len(values) == len(set(values)), f"{path}.accessedAddresses: duplicates")
        for index, value in enumerate(values):
            address_text(value, f"{path}.accessedAddresses[{index}]")
        for index, item in enumerate(exact_list(
                row["accessedStorageKeys"], f"{path}.accessedStorageKeys")):
            item = exact_object(item, f"{path}.accessedStorageKeys[{index}]", {"address", "key"})
            address_text(item["address"], f"{path}.accessedStorageKeys[{index}].address")
            fullmatch(item["key"], f"{path}.accessedStorageKeys[{index}].key", r"0x[0-9a-f]{64}")
    require(
        set(warm["accessedAddresses"]) - set(cold["accessedAddresses"])
        == {addresses["canonical-implementation"]},
        "manifest.fixtures.accessSets: warm address delta differs",
    )
    require(
        set(cold["accessedAddresses"]) - set(warm["accessedAddresses"]) == set(),
        "manifest.fixtures.accessSets: warm world removed a cold address",
    )
    require(cold["accessedStorageKeys"] == [],
            "manifest.fixtures.accessSets.forwarding-cold: storage keys must be empty")
    require(warm["accessedStorageKeys"] == [{
        "address": addresses["proxy-target"], "key": IMPLEMENTATION_SLOT,
    }], "manifest.fixtures.accessSets.forwarding-warm: storage-key delta differs")

    for state_name, state in fixtures["proxyStates"].items():
        path = f"manifest.fixtures.proxyStates.{state_name}"
        state = exact_object(state, path, {
            "accountBalance", "accountNonce", "code", "storageDefault", "storageOverrides",
        })
        require(state["code"] == "side-specific returnedRuntime artifact",
                f"{path}.code: artifact binding differs")
        overrides = state["storageOverrides"]
        require(set(overrides) == {IMPLEMENTATION_SLOT, ADMIN_SLOT},
                f"{path}.storageOverrides: ERC-1967 membership differs")
        for key, value in overrides.items():
            fullmatch(key, f"{path}.storageOverrides key", r"0x[0-9a-f]{64}")
            fullmatch(value, f"{path}.storageOverrides.{key}", r"0x[0-9a-f]{64}")


def _validate_cell_references(manifest: dict[str, Any]) -> None:
    fixtures = manifest["fixtures"]
    seen_expected: set[str] = set()
    seen_access: set[str] = set()
    seen_calldata: set[str] = set()
    seen_constructors: set[str] = set()
    seen_mock_code: set[str] = set()
    seen_states: set[str] = set()

    artifact_keys = {
        "artifactBinding", "kind", "referenceByteLength", "referenceKeccak256",
    }
    create_keys = {
        "accessSet", "caller", "callerNonce", "constructorTuple", "expected",
        "gasAllowance", "implementationAccounts", "kind", "messageData", "target",
        "targetInitiallyAbsent", "value",
    }
    call_keys = {
        "accessSet", "calldata", "caller", "expected", "gasAllowance",
        "implementationAccounts", "kind", "proxyState", "target", "value",
    }

    for index, (cell, spec) in enumerate(zip(manifest["cells"], CELL_SPECS)):
        path = f"manifest.cells[{index}]"
        cell = exact_object(cell, path, {"group", "id", "ordinal", "scalar", "world"})
        expected_id, expected_group, expected_scalar, expected_kind = spec
        require(cell["id"] == expected_id, f"{path}.id: fixed order differs")
        require(cell["ordinal"] == index + 1 and type(cell["ordinal"]) is int,
                f"{path}.ordinal: expected {index + 1}")
        require(cell["group"] == expected_group, f"{path}.group: differs")
        require(cell["scalar"] == expected_scalar, f"{path}.scalar: differs")
        world = cell["world"]
        require(isinstance(world, dict), f"{path}.world: expected object")
        require(world.get("kind") == expected_kind, f"{path}.world.kind: differs")

        if expected_kind == "artifact":
            keys = set(artifact_keys)
            if expected_id == "A1":
                keys.add("constructorTuple")
            else:
                keys.add("abiConstructorArgumentsExcluded")
            exact_object(world, f"{path}.world", keys)
            binding = _require_named(fixtures["artifactBindings"], world["artifactBinding"],
                                     f"{path}.world.artifactBinding")
            exact_object(binding, f"manifest.fixtures.artifactBindings.{world['artifactBinding']}",
                         {"blanc", "reference"})
            integer(world["referenceByteLength"], f"{path}.world.referenceByteLength", 0)
            keccak_text(world["referenceKeccak256"], f"{path}.world.referenceKeccak256")
            if expected_id == "A1":
                _require_named(fixtures["constructorTuples"], world["constructorTuple"],
                               f"{path}.world.constructorTuple")
                seen_constructors.add(world["constructorTuple"])
            else:
                require(boolean(world["abiConstructorArgumentsExcluded"],
                                f"{path}.world.abiConstructorArgumentsExcluded"),
                        f"{path}.world: ABI arguments must remain excluded")
            continue

        exact_object(
            world, f"{path}.world",
            create_keys if expected_kind == "direct-create-message"
            else call_keys | ({"absentAccounts"} if expected_id == "N4" else set()),
        )
        _require_named(fixtures["accessSets"], world["accessSet"], f"{path}.world.accessSet")
        seen_access.add(world["accessSet"])
        _require_named(fixtures["addresses"], world["caller"], f"{path}.world.caller")
        _require_named(fixtures["expectedSemantics"], world["expected"], f"{path}.world.expected")
        seen_expected.add(world["expected"])
        _require_named(fixtures["values"], world["gasAllowance"], f"{path}.world.gasAllowance")
        _require_named(fixtures["addresses"], world["target"], f"{path}.world.target")
        _require_named(fixtures["values"], world["value"], f"{path}.world.value")
        accounts = exact_list(world["implementationAccounts"],
                              f"{path}.world.implementationAccounts")
        require(1 <= len(accounts) <= 2,
                f"{path}.world.implementationAccounts: expected one or two entries")
        account_addresses: set[str] = set()
        for account_index, account in enumerate(accounts):
            account_path = f"{path}.world.implementationAccounts[{account_index}]"
            account = exact_object(account, account_path, {"address", "code"})
            _require_named(fixtures["addresses"], account["address"],
                           f"{account_path}.address")
            require(account["address"] not in account_addresses,
                    f"{account_path}.address: duplicate implementation account")
            account_addresses.add(account["address"])
            _require_named(fixtures["mockImplementations"], account["code"],
                           f"{account_path}.code")
            seen_mock_code.add(account["code"])

        if expected_kind == "direct-create-message":
            _require_named(fixtures["constructorTuples"], world["constructorTuple"],
                           f"{path}.world.constructorTuple")
            seen_constructors.add(world["constructorTuple"])
            _require_named(fixtures["calldata"], world["messageData"],
                           f"{path}.world.messageData")
            seen_calldata.add(world["messageData"])
            require(world["targetInitiallyAbsent"] is True,
                    f"{path}.world.targetInitiallyAbsent: must remain true")
        else:
            _require_named(fixtures["calldata"], world["calldata"], f"{path}.world.calldata")
            seen_calldata.add(world["calldata"])
            _require_named(fixtures["proxyStates"], world["proxyState"],
                           f"{path}.world.proxyState")
            seen_states.add(world["proxyState"])
            if expected_id == "N4":
                absent = exact_list(world["absentAccounts"], f"{path}.world.absentAccounts", 1)
                _require_named(fixtures["addresses"], absent[0], f"{path}.world.absentAccounts[0]")

    require(seen_expected == set(fixtures["expectedSemantics"]),
            "manifest.cells: expected-semantics references are not exact and total")
    require(seen_access == set(fixtures["accessSets"]),
            "manifest.cells: access-set references are not exact and total")
    require(seen_constructors == set(fixtures["constructorTuples"]),
            "manifest.cells: constructor-tuple references are not exact and total")
    require(seen_states == set(fixtures["proxyStates"]),
            "manifest.cells: proxy-state references are not exact and total")
    setup = fixtures["setupFixtures"]
    seen_calldata.update(row["calldata"] for row in setup.values())
    seen_mock_code.update(row["implementationCode"] for row in setup.values())
    require(seen_calldata == set(fixtures["calldata"]),
            "manifest: calldata references are not exact and total")
    require(seen_mock_code == set(fixtures["mockImplementations"]),
            "manifest: mock-code references are not exact and total")


def validate_manifest_schema(
    value: Any,
    *,
    root: Path | None = None,
    enforce_frozen_digest: bool = True,
    validate_external: bool = False,
) -> dict[str, Any]:
    """Validate the result-free manifest and all internal symbolic references."""
    manifest = exact_object(value, "manifest", {
        "campaign", "cells", "fixtures", "identities", "measurementContract",
        "schema", "scoreContract",
    })
    require(manifest["schema"] == 1 and type(manifest["schema"]) is int,
            "manifest.schema: expected integer 1")

    campaign = exact_object(manifest["campaign"], "manifest.campaign", {
        "authority", "digest", "format", "formatVersion", "frozenDate",
        "lifecycleStage", "measurementsIncluded", "name", "supersedes",
    })
    require(campaign["format"] == MANIFEST_FORMAT, "manifest.campaign.format: differs")
    require(campaign["formatVersion"] == 2 and type(campaign["formatVersion"]) is int,
            "manifest.campaign.formatVersion: expected corrected integer 2")
    require(campaign["measurementsIncluded"] is False,
            "manifest.campaign.measurementsIncluded: result smuggling is forbidden")
    require(campaign["lifecycleStage"] == "corrected-frozen-before-first-full-port-blanc-result",
            "manifest.campaign.lifecycleStage: differs")
    require(campaign["supersedes"] == {
        "campaignDigest": SUPERSEDED_MANIFEST_DIGEST,
        "formatVersion": 1,
        "reason": (
            "Before any measurement, independent fixture validation found fallback-256 had 511 "
            "hex nibbles. Version 2 inserts the uniquely missing e nibble, restoring the declared "
            "feedface || bytes(0x00..0xfb) 256-byte payload; no cell, world, scalar, order, "
            "denominator, or score rule changed."
        ),
        "resultsGenerated": False,
    }, "manifest.campaign.supersedes: correction lineage differs")
    digest_row = exact_object(campaign["digest"], "manifest.campaign.digest", {
        "algorithm", "canonicalization", "scope", "value",
    })
    require(digest_row == {
        "algorithm": "sha256", "canonicalization": MANIFEST_CANONICALIZATION,
        "scope": MANIFEST_DIGEST_SCOPE, "value": digest_row["value"],
    }, "manifest.campaign.digest: digest contract differs")
    recorded_digest = sha256_text(digest_row["value"], "manifest.campaign.digest.value")
    require(recorded_digest == manifest_digest(manifest),
            "manifest.campaign.digest.value: self-digest differs")
    if enforce_frozen_digest:
        require(recorded_digest == MANIFEST_DIGEST,
                "manifest.campaign.digest.value: frozen campaign identity differs")

    cells = exact_list(manifest["cells"], "manifest.cells", DENOMINATOR)
    require([row.get("id") for row in cells] == CELL_ORDER,
            "manifest.cells: denominator/order differs")
    require(len({row.get("id") for row in cells}) == DENOMINATOR,
            "manifest.cells: duplicate primary cell")
    require(manifest["measurementContract"] == MEASUREMENT_CONTRACT,
            "manifest.measurementContract: frozen measurement contract differs")
    require(manifest["scoreContract"] == SCORE_CONTRACT,
            "manifest.scoreContract: 25-cell/13-win score contract differs")
    require(manifest["identities"] == EXPECTED_IDENTITIES,
            "manifest.identities: frozen artifact/reference/execution identity differs")

    _validate_fixture_shapes(manifest)
    _validate_cell_references(manifest)
    pointers = {item for item in _walk_strings(manifest) if ".json#/" in item}
    require(pointers == EXPECTED_EXTERNAL_POINTERS,
            f"manifest: external JSON Pointer inventory differs: {sorted(pointers)}")

    if validate_external:
        validate_external_identities(manifest, (root or DEFAULT_ROOT).resolve())
    return manifest


def validate_external_identities(manifest: dict[str, Any], root: Path) -> None:
    """Resolve every external JSON Pointer and verify vendored identities."""
    lock_path = _repo_path(root, REFERENCE_LOCK_RELATIVE, "manifest.identities.reference.referenceLock")
    raw_lock = lock_path.read_bytes()
    require(hashlib.sha256(raw_lock).hexdigest() == REFERENCE_LOCK_SHA256,
            "reference lock: frozen file identity differs")
    lock = strict_json(raw_lock, str(lock_path))

    resolved: dict[str, dict[str, Any]] = {}
    for binding_name, binding in manifest["fixtures"]["artifactBindings"].items():
        pointer_value = text(binding["reference"],
                             f"manifest.fixtures.artifactBindings.{binding_name}.reference")
        relative, pointer = split_external_pointer(
            pointer_value, f"manifest.fixtures.artifactBindings.{binding_name}.reference",
        )
        require(_repo_path(root, relative, pointer_value) == lock_path,
                f"{pointer_value}: reference lock path differs")
        artifact, _ = _validate_artifact_row(
            resolve_json_pointer(lock, pointer, pointer_value), pointer_value,
        )
        resolved[binding_name] = artifact

    require(set(resolved) == {"creationTemplate", "returnedRuntime"},
            "reference artifacts: binding membership differs")
    artifact_cells = {cell["world"]["artifactBinding"]: cell for cell in manifest["cells"][:2]}
    for binding_name, artifact in resolved.items():
        world = artifact_cells[binding_name]["world"]
        require(world["referenceByteLength"] == artifact["byteLength"],
                f"manifest.cells/{binding_name}: reference byte length differs from JSON Pointer")
        require(world["referenceKeccak256"] == artifact["keccak256"],
                f"manifest.cells/{binding_name}: reference Keccak differs from JSON Pointer")

    identities = manifest["identities"]["reference"]
    compiler_identity = identities["compiler"]
    lock_compiler = lock["compiler"]
    require(lock_compiler["longVersion"] == compiler_identity["longVersion"],
            "reference compiler: long version differs from lock")
    require(lock_compiler["packaging"] == compiler_identity["platform"],
            "reference compiler: platform differs from lock")
    release_entry = lock_compiler["releaseManifestEntry"]
    for key in ("build", "keccak256", "longVersion", "path", "sha256"):
        require(release_entry[key] == compiler_identity[key],
                f"reference compiler: {key} differs from lock")
    settings = lock_compiler["standardInputSettings"]
    require(settings["evmVersion"] == compiler_identity["evmVersion"],
            "reference compiler: EVM version differs from lock")
    require(settings["optimizer"] == {
        "enabled": compiler_identity["optimizerEnabled"],
        "runs": compiler_identity["optimizerRuns"],
    }, "reference compiler: optimizer settings differ from lock")
    require(("viaIR" in settings and settings["viaIR"] is True) == compiler_identity["viaIR"],
            "reference compiler: viaIR setting differs from lock")

    inputs = _repo_path(root, REFERENCE_INPUTS_RELATIVE, "reference inputs")
    compiler_path = _repo_path(inputs, Path(compiler_identity["path"]), "reference compiler path")
    compiler_bytes = compiler_path.read_bytes()
    require(hashlib.sha256(compiler_bytes).hexdigest() == compiler_identity["sha256"][2:],
            "reference compiler: vendored SHA-256 differs")
    # The full compiler is large.  Its bytes are authenticated here by SHA-256;
    # its independently published Keccak identity is cross-checked above against
    # the frozen release-manifest entry, avoiding an expensive hash in this
    # intentionally lightweight static gate.
    list_path = _repo_path(inputs, Path("solc-emscripten-wasm32-list.json"), "solc list")
    require(hashlib.sha256(list_path.read_bytes()).hexdigest() == compiler_identity["listSha256"],
            "reference compiler: frozen release-list SHA-256 differs")

    source_relative = Path("source") / identities["sourcePath"]
    source_path = _repo_path(inputs, source_relative, "reference source path")
    source = source_path.read_bytes()
    require(hashlib.sha256(source).hexdigest() == identities["sourceSha256"],
            "reference source: SHA-256 differs")
    require(_git_blob_sha1(source) == identities["sourceBlob"],
            "reference source: Git blob differs")
    source_row = next(
        (row for row in lock["provenance"]["sourceFiles"]
         if row["sourceUnit"] == identities["sourcePath"]),
        None,
    )
    require(source_row is not None, "reference source: source-unit row missing from lock")
    require(source_row["sha256"] == identities["sourceSha256"]
            and source_row["gitBlob"] == identities["sourceBlob"],
            "reference source: manifest identity differs from lock")
    require(lock["provenance"]["lidoCommit"] == identities["releaseCommit"],
            "reference release: commit differs from lock")
    require(lock["provenance"]["lidoTag"] == "v4.0.0"
            and identities["release"] == "lidofinance/core-v4.0.0",
            "reference release: tag identity differs")

    try:
        subprocess.run(
            ["git", "-C", str(root), "cat-file", "-e", f"{CAMPAIGN_BASE_COMMIT}^{{commit}}"],
            check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise SchemaError("Blanc campaign base commit is not present in the repository") from exc


def _unit_for(cell_id: str) -> str:
    return "bytes" if cell_id in {"A1", "A2"} else "gas"


def classify_cell(cell: dict[str, Any], path: str) -> str:
    status = cell["measurementStatus"]
    agreement = cell["semanticAgreement"]
    reference_value = cell["referenceValue"]
    blanc_value = cell["blancValue"]
    if status == "instrumentation-failure":
        require(agreement is None, f"{path}.semanticAgreement: must be null on instrumentation failure")
        require(reference_value is None and blanc_value is None,
                f"{path}: instrumentation failure cannot carry score values")
        return "incomparable"
    require(status == "complete", f"{path}.measurementStatus: invalid status")
    require(type(agreement) is bool, f"{path}.semanticAgreement: expected boolean")
    reference = integer(reference_value, f"{path}.referenceValue", 0)
    blanc = integer(blanc_value, f"{path}.blancValue", 0)
    if agreement is False:
        return "incomparable"
    if blanc < reference:
        return "strict-win"
    if blanc == reference:
        return "tie"
    return "loss"


def score_for_cells(cells: list[dict[str, Any]]) -> dict[str, Any]:
    counts = Counter(cell["classification"] for cell in cells)
    strict_wins = counts["strict-win"]
    return {
        "allCellsReported": len(cells) == DENOMINATOR,
        "denominator": DENOMINATOR,
        "incomparables": counts["incomparable"],
        "losses": counts["loss"],
        "minimumStrictWins": MINIMUM_STRICT_WINS,
        "semanticAgreementCells": sum(cell["semanticAgreement"] is True for cell in cells),
        "strictWins": strict_wins,
        "thresholdMet": strict_wins >= MINIMUM_STRICT_WINS,
        "ties": counts["tie"],
        "verdict": "meets-threshold" if strict_wins >= MINIMUM_STRICT_WINS else "below-threshold",
    }


def validate_result_schema(
    value: Any,
    manifest: dict[str, Any],
    *,
    root: Path | None = None,
    enforce_self_digest: bool = True,
    validate_external: bool = True,
) -> dict[str, Any]:
    """Validate an immutable baseline or final 25-cell measurement ledger."""
    require(
        manifest["campaign"]["digest"]["value"] == MANIFEST_DIGEST,
        "performance result: validator was not given the frozen corrected campaign",
    )
    result = exact_object(value, "performance result", {
        "campaign", "cells", "diagnostics", "identities", "result", "schema", "score",
    })
    require(result["schema"] == 1 and type(result["schema"]) is int,
            "performance result.schema: expected integer 1")
    metadata = exact_object(result["result"], "performance result.result", {
        "createdAt", "digest", "format", "formatVersion", "measurementsIncluded",
        "predecessorResultSha256", "stage",
    })
    require(metadata["format"] == RESULT_FORMAT, "performance result.result.format: differs")
    require(metadata["formatVersion"] == 1 and type(metadata["formatVersion"]) is int,
            "performance result.result.formatVersion: expected integer 1")
    require(metadata["measurementsIncluded"] is True,
            "performance result.result.measurementsIncluded: expected true")
    fullmatch(metadata["createdAt"], "performance result.result.createdAt",
              r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z")
    require(metadata["stage"] in {"baseline", "final"},
            "performance result.result.stage: expected baseline or final")
    predecessor = metadata["predecessorResultSha256"]
    if metadata["stage"] == "baseline":
        require(predecessor is None,
                "performance result.result.predecessorResultSha256: baseline must be null")
    else:
        sha256_text(predecessor, "performance result.result.predecessorResultSha256")
    digest_row = exact_object(metadata["digest"], "performance result.result.digest", {
        "algorithm", "canonicalization", "scope", "value",
    })
    require(digest_row["algorithm"] == "sha256"
            and digest_row["canonicalization"] == MANIFEST_CANONICALIZATION
            and digest_row["scope"] == RESULT_DIGEST_SCOPE,
            "performance result.result.digest: digest contract differs")
    recorded = sha256_text(digest_row["value"], "performance result.result.digest.value")
    if enforce_self_digest:
        require(recorded == result_digest(result),
                "performance result.result.digest.value: self-digest differs")

    campaign = exact_object(result["campaign"], "performance result.campaign", {
        "denominator", "fixedOrder", "manifestDigest", "manifestFormatVersion",
        "manifestPath", "minimumStrictWins",
    })
    require(campaign == {
        "denominator": DENOMINATOR,
        "fixedOrder": CELL_ORDER,
        "manifestDigest": MANIFEST_DIGEST,
        "manifestFormatVersion": 2,
        "manifestPath": str(MANIFEST_RELATIVE),
        "minimumStrictWins": MINIMUM_STRICT_WINS,
    }, "performance result.campaign: frozen campaign binding differs")

    identities = exact_object(result["identities"], "performance result.identities", {
        "candidate", "execution", "reference",
    })
    candidate = exact_object(identities["candidate"], "performance result.identities.candidate", {
        "artifacts", "commit", "evaluator", "treeClean",
    })
    fullmatch(candidate["commit"], "performance result.identities.candidate.commit", r"[0-9a-f]{40}")
    require(candidate["treeClean"] is True,
            "performance result.identities.candidate.treeClean: immutable results require true")
    require(candidate["evaluator"] == "scripts/eval-lido-ossifiable-proxy-artifacts.lean",
            "performance result.identities.candidate.evaluator: differs")
    candidate_artifacts = exact_object(candidate["artifacts"],
                                       "performance result.identities.candidate.artifacts",
                                       {"creationTemplate", "returnedRuntime"})
    for name, artifact in candidate_artifacts.items():
        _validate_artifact_identity(artifact,
                                    f"performance result.identities.candidate.artifacts.{name}")
    require(candidate_artifacts["creationTemplate"] != candidate_artifacts["returnedRuntime"],
            "performance result: candidate creation/runtime identities must differ")

    execution = exact_object(identities["execution"], "performance result.identities.execution",
                             {"eelsCommit", "fork"})
    require(execution == {"eelsCommit": EELS_COMMIT, "fork": "Prague"},
            "performance result.identities.execution: differs")

    reference = exact_object(identities["reference"], "performance result.identities.reference", {
        "artifacts", "lock", "lockSha256",
    })
    require(reference["lock"] == str(REFERENCE_LOCK_RELATIVE),
            "performance result.identities.reference.lock: differs")
    sha256_text(reference["lockSha256"], "performance result.identities.reference.lockSha256")
    reference_artifacts = exact_object(reference["artifacts"],
                                       "performance result.identities.reference.artifacts",
                                       {"creationTemplate", "returnedRuntime"})
    for name, artifact in reference_artifacts.items():
        _validate_artifact_identity(artifact,
                                    f"performance result.identities.reference.artifacts.{name}")
    require(reference_artifacts["creationTemplate"] != reference_artifacts["returnedRuntime"],
            "performance result: reference creation/runtime identities must differ")

    if validate_external:
        chosen_root = (root or DEFAULT_ROOT).resolve()
        raw_lock = _repo_path(chosen_root, REFERENCE_LOCK_RELATIVE,
                              "performance result reference lock").read_bytes()
        require(reference["lockSha256"] == hashlib.sha256(raw_lock).hexdigest()
                == REFERENCE_LOCK_SHA256,
                "performance result: reference-lock identity differs")
        lock = strict_json(raw_lock, "performance result reference lock")
        for name, pointer in {
            "creationTemplate": "/artifacts/creationTemplate",
            "returnedRuntime": "/artifacts/runtime",
        }.items():
            artifact, _ = _validate_artifact_row(
                resolve_json_pointer(lock, pointer, f"reference lock#{pointer}"),
                f"reference lock#{pointer}",
            )
            require(reference_artifacts[name] == _artifact_identity(artifact),
                    f"performance result: reference {name} identity differs")
        try:
            subprocess.run(
                ["git", "-C", str(chosen_root), "cat-file", "-e",
                 f"{candidate['commit']}^{{commit}}"],
                check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
        except (OSError, subprocess.CalledProcessError) as exc:
            raise SchemaError(
                "performance result: candidate commit is not present in the repository"
            ) from exc

    cells = exact_list(result["cells"], "performance result.cells", DENOMINATOR)
    require([cell.get("id") for cell in cells] == CELL_ORDER,
            "performance result.cells: fixed denominator/order differs")
    for index, cell in enumerate(cells):
        path = f"performance result.cells[{index}]"
        cell = exact_object(cell, path, {
            "blancValue", "classification", "evidence", "group", "id",
            "incomparableReason", "measurementStatus", "ordinal", "referenceValue",
            "scalar", "semanticAgreement", "unit",
        })
        cell_id, group, scalar, _ = CELL_SPECS[index]
        require(cell["id"] == cell_id and cell["ordinal"] == index + 1
                and type(cell["ordinal"]) is int, f"{path}: fixed identity/order differs")
        require(cell["group"] == group and cell["scalar"] == scalar,
                f"{path}: group/scalar differs from manifest")
        require(cell["unit"] == _unit_for(cell_id), f"{path}.unit: differs")
        require(cell["measurementStatus"] in {"complete", "instrumentation-failure"},
                f"{path}.measurementStatus: invalid")
        derived = classify_cell(cell, path)
        require(cell["classification"] == derived,
                f"{path}.classification: expected derived {derived}")
        reason = cell["incomparableReason"]
        if derived == "incomparable":
            text(reason, f"{path}.incomparableReason", nonempty=True)
        else:
            require(reason is None, f"{path}.incomparableReason: must be null for scored cell")
        evidence = exact_object(cell["evidence"], f"{path}.evidence", {"recordSha256"})
        sha256_text(evidence["recordSha256"], f"{path}.evidence.recordSha256")

    evidence_hashes = [cell["evidence"]["recordSha256"] for cell in cells]
    require(len(evidence_hashes) == len(set(evidence_hashes)),
            "performance result.cells: each primary cell needs distinct evidence")

    require(cells[0]["referenceValue"] == reference_artifacts["returnedRuntime"]["byteLength"],
            "performance result.cells[0]: reference value differs from locked runtime")
    require(cells[1]["referenceValue"] == reference_artifacts["creationTemplate"]["byteLength"],
            "performance result.cells[1]: reference value differs from locked creation template")
    require(cells[0]["blancValue"] == candidate_artifacts["returnedRuntime"]["byteLength"],
            "performance result.cells[0]: Blanc value differs from candidate runtime identity")
    require(cells[1]["blancValue"] == candidate_artifacts["creationTemplate"]["byteLength"],
            "performance result.cells[1]: Blanc value differs from candidate creation identity")

    expected_score = score_for_cells(cells)
    exact_object(result["score"], "performance result.score", expected_score.keys())
    require(result["score"] == expected_score,
            "performance result.score: counts/13-win verdict differ from cell classifications")
    require(sum(result["score"][key] for key in ("strictWins", "ties", "losses", "incomparables"))
            == DENOMINATOR, "performance result.score: classifications do not total 25")

    diagnostics = exact_list(result["diagnostics"], "performance result.diagnostics")
    names: set[str] = set()
    for index, diagnostic in enumerate(diagnostics):
        path = f"performance result.diagnostics[{index}]"
        diagnostic = exact_object(diagnostic, path, {"name", "recordSha256"})
        name = text(diagnostic["name"], f"{path}.name", nonempty=True)
        require(name not in names, f"{path}.name: duplicate report-only diagnostic")
        names.add(name)
        sha256_text(diagnostic["recordSha256"], f"{path}.recordSha256")
    return result


def require_final_threshold(result: dict[str, Any]) -> None:
    require(result["result"]["stage"] == "final",
            "threshold closure requires a final result")
    require(result["score"]["strictWins"] >= MINIMUM_STRICT_WINS
            and result["score"]["thresholdMet"] is True,
            f"final result closes below {MINIMUM_STRICT_WINS} strict wins")


def load_json(path: Path, label: str) -> tuple[bytes, Any]:
    raw = path.read_bytes()
    value = strict_json(raw, label)
    return raw, value


def _default_manifest() -> Path:
    override = os.environ.get("LIDO_OSSIFIABLE_PROXY_PERFORMANCE_MANIFEST")
    return Path(override).resolve() if override else (DEFAULT_ROOT / MANIFEST_RELATIVE)


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate the independent performance schemas")
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--manifest", type=Path, default=_default_manifest())
    parser.add_argument("--result", type=Path)
    parser.add_argument("--require-final-threshold", action="store_true")
    args = parser.parse_args()
    try:
        _, manifest_value = load_json(args.manifest, "performance manifest")
        manifest = validate_manifest_schema(
            manifest_value, root=args.root, enforce_frozen_digest=True, validate_external=False,
        )
        if args.result is not None:
            _, result_value = load_json(args.result, "performance result")
            result = validate_result_schema(
                result_value, manifest, root=args.root, validate_external=False,
            )
            if args.require_final_threshold:
                require_final_threshold(result)
    except (OSError, SchemaError) as exc:
        print(f"REGRESSION — OssifiableProxy performance schema: {exc}", file=sys.stderr)
        return 1
    detail = "manifest + result" if args.result is not None else "result-free manifest + future result"
    print(f"OK — OssifiableProxy performance schema: {detail}; 25 cells; 13 strict wins")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
