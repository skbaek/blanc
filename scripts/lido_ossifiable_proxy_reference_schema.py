#!/usr/bin/env python3
"""Independent exact-schema contract for the OssifiableProxy reference lock.

This module intentionally does not import the lock generator.  The generator
must satisfy this separately maintained inventory before its output can be
admitted.  Exact input identities, compiler settings, external signatures,
deployment facts, event/error encodings, and ERC-1967 slots are duplicated
here on purpose: agreement between independent descriptions is the check.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LOCK = Path(os.environ.get(
    "LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK",
    ROOT / "scripts" / "lido-ossifiable-proxy-reference.json",
))

TARGET_SOURCE = "contracts/0.8.9/proxy/OssifiableProxy.sol"
TARGET_ADDRESS = "0x889edC2eDab5f40e902b864aD4d7AdE8E412F9B1"
TARGET_TX = "0x98c2170be034f750f5006cb69ea0aeeaf0858b11f6324ee53d582fa4dd49bc1a"
TARGET_BLOCK_HASH = "0x4fa4c03c69ad9b863fcd43b32cc063769d8b6a142a2aa8063a7c246feb5732a6"
IMPLEMENTATION_SLOT = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"
ADMIN_SLOT = "0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103"

EXPECTED_INPUTS = {
    "git-provenance.json": "bc4d4625b001b4006b69990eade7dc412fd37e42d673670919de140a6160ec51",
    "lido/contracts/COMPILERS.md": "888504aefff340b47cd49f5b299fd3d3055c70ab56222098a961be87ef49e4b8",
    "lido/deployed-mainnet.json": "3428ba7a845ae27c69bd64d87dafda920df3fdfdc8df99da1caf3af55060fd15",
    "lido/hardhat.config.ts": "29b3e91ff197c0ea1df5b6401cc12982d3f684e7bf3e68b380096fe33e43b223",
    "lido/package.json": "5e6bd056082e23c6628aee085df5ce0743070d08d5a3e27496991e09f74b638e",
    "lido/yarn.lock": "d17f979eed36218b0bed85cf560bdc2e5d182e0c67aff6eabf2c68be8597c921",
    "rpc-blastapi.json": "bcd86c8bcd5bf2e9ddcd1ec0da9fdbb4f9041ff3f4d765b1ce1bcf6b413514dc",
    "rpc-drpc.json": "bfaca0cc02c01a3dbe93d395bebf60d166e4fcd163abd7b852f4e80108851451",
    "solc-emscripten-wasm32-list.json": "0ee86d7e0a30f0d90593ff64dfb56d192c514c8e33feebeb54446be55b12e5ad",
    "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js": "5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c",
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

EXPECTED_SOURCE_SHA256 = {
    "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Proxy.sol": "db6c986d393626060fa219d1072a1913eb16872224307e9261fc90c296e3770d",
    "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol": "a8e55634074e89c6925a57f3274aebca184bfc99ffca39967ce967696f49dbe9",
    "@openzeppelin/contracts-v4.4/proxy/Proxy.sol": "f3750834a47fd89ab623ba00877c556895bb71f203e615da9987697cbabbeed6",
    "@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol": "6afea1d83856ed8e0495fe78109f674f925cfdc79fe2e24e854b1237e742f011",
    "@openzeppelin/contracts-v4.4/utils/Address.sol": "0228dd7c0a0d1342b88eab6e5a4a07ae4350818ba1650be0a374064b02218f37",
    "@openzeppelin/contracts-v4.4/utils/StorageSlot.sol": "b8d43f55a3afc09327fb9d802f714a8bec64e3a259ad42f5b3d877deb29aaaef",
    TARGET_SOURCE: "3fb48bc4a40c887dd581178d05316745c1b1c393a8e64787ef2a7075f1e7ce6d",
}

EXPECTED_SOURCE_BLOBS = {
    "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Proxy.sol": "64e9d9f6f317c3bd1135a122822965508cbdd3fa",
    "@openzeppelin/contracts-v4.4/proxy/ERC1967/ERC1967Upgrade.sol": "036782fc7a0f288c6adf717dfde889ef416f8f68",
    "@openzeppelin/contracts-v4.4/proxy/Proxy.sol": "81351613004d76bdaceacbee9d02f68a0d69e4b9",
    "@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol": "fba3ee2ab4546832599b0498c4945c9f81d50791",
    "@openzeppelin/contracts-v4.4/utils/Address.sol": "9e5e887409ff86e2c0db7abf9b30ba4640e46ce1",
    "@openzeppelin/contracts-v4.4/utils/StorageSlot.sol": "28239dbc35a2c45a91958e1b654143a7690b2a2b",
    TARGET_SOURCE: "d4ccec05c453b15cc17023e3950e44341a66a4a4",
}

FUNCTIONS = [
    ("proxy__getAdmin()", "0x916f1fd7", "view", ["address"]),
    ("proxy__getImplementation()", "0xad729a71", "view", ["address"]),
    ("proxy__getIsOssified()", "0x13351258", "view", ["bool"]),
    ("proxy__ossify()", "0xadcbc237", "nonpayable", []),
    ("proxy__changeAdmin(address)", "0x773f5be8", "nonpayable", []),
    ("proxy__upgradeTo(address)", "0x3ebdd0eb", "nonpayable", []),
    ("proxy__upgradeToAndCall(address,bytes,bool)", "0xd2f6ed4d", "nonpayable", []),
]

EVENTS = [
    ("Upgraded(address)", "0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b", [True]),
    ("AdminChanged(address,address)", "0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f", [False, False]),
    ("ProxyOssified()", "0x158b204828f9326d9bb3c2be9336986c14911b4a72b93d1801f207aac3c68b9f", []),
]

ERRORS = [
    ("NotAdmin()", "0x7bfa4b9f"),
    ("ProxyIsOssified()", "0xb83646a9"),
]

REASON_STRINGS = [
    "ERC1967: new admin is the zero address",
    "ERC1967: new implementation is not a contract",
    "Address: low-level delegate call failed",
]

EXPECTED_SETTINGS = {
    "evmVersion": "istanbul",
    "optimizer": {"enabled": True, "runs": 200},
    "outputSelection": {"*": {"*": [
        "abi", "metadata", "evm.bytecode.object", "evm.deployedBytecode.object",
    ]}},
}

EXPECTED_METADATA_SETTINGS = {
    "compilationTarget": {TARGET_SOURCE: "OssifiableProxy"},
    "evmVersion": "istanbul",
    "libraries": {},
    "metadata": {"bytecodeHash": "ipfs"},
    "optimizer": {"enabled": True, "runs": 200},
    "remappings": [],
}


class SchemaError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SchemaError(message)


def strict_json(data: bytes, what: str) -> Any:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            require(key not in result, f"{what}: duplicate JSON key {key!r}")
            result[key] = value
        return result

    def invalid(value: str) -> None:
        raise SchemaError(f"{what}: non-finite JSON value {value}")

    try:
        return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SchemaError(f"{what}: invalid JSON: {exc}") from exc


def exact_object(value: Any, path: str, keys: set[str]) -> dict[str, Any]:
    require(isinstance(value, dict), f"{path}: expected object")
    require(set(value) == keys,
            f"{path}: expected fields {sorted(keys)}, found {sorted(value) if isinstance(value, dict) else value}")
    return value


def exact_list(value: Any, path: str, length: int | None = None) -> list[Any]:
    require(isinstance(value, list), f"{path}: expected array")
    if length is not None:
        require(len(value) == length, f"{path}: expected {length} entries, found {len(value)}")
    return value


def string(value: Any, path: str) -> str:
    require(isinstance(value, str), f"{path}: expected string")
    return value


def integer(value: Any, path: str) -> int:
    require(type(value) is int, f"{path}: expected integer")
    return value


def boolean(value: Any, path: str) -> bool:
    require(type(value) is bool, f"{path}: expected boolean")
    return value


def same_json(value: Any, expected: Any) -> bool:
    if type(value) is not type(expected):
        return False
    if isinstance(expected, dict):
        return set(value) == set(expected) and all(
            same_json(value[key], expected[key]) for key in expected)
    if isinstance(expected, list):
        return len(value) == len(expected) and all(
            same_json(left, right) for left, right in zip(value, expected))
    return value == expected


def pattern(value: Any, path: str, regex: str) -> str:
    value = string(value, path)
    require(re.fullmatch(regex, value) is not None, f"{path}: malformed value {value!r}")
    return value


def digest(value: Any, path: str) -> str:
    return pattern(value, path, r"[0-9a-f]{64}")


def section_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


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
        shuffled = [0] * 25
        for x in range(5):
            for y in range(5):
                shuffled[y + 5 * ((2 * x + 3 * y) % 5)] = rol(state[x + 5 * y], ROT[x][y])
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = shuffled[x + 5 * y] ^ (
                    (~shuffled[(x + 1) % 5 + 5 * y]) & shuffled[(x + 2) % 5 + 5 * y])
                state[x + 5 * y] &= MASK
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
        keccak_f(state)
    return "".join(item.to_bytes(8, "little").hex() for item in state)[:64]


def validate_artifact(value: Any, path: str, expected_length: int, expected_keccak: str) -> None:
    row = exact_object(value, path, {"byteLength", "hex", "keccak256", "sha256"})
    raw_hex = pattern(row["hex"], f"{path}.hex", r"0x(?:[0-9a-f]{2})+")
    raw = bytes.fromhex(raw_hex[2:])
    require(integer(row["byteLength"], f"{path}.byteLength") == expected_length,
            f"{path}: wrong byte length")
    require(len(raw) == expected_length, f"{path}.hex: byte length differs")
    require(digest(row["sha256"], f"{path}.sha256") == hashlib.sha256(raw).hexdigest(),
            f"{path}: SHA-256 differs from bytes")
    require(pattern(row["keccak256"], f"{path}.keccak256", r"0x[0-9a-f]{64}") == expected_keccak,
            f"{path}: frozen Keccak-256 differs")
    require(row["keccak256"] == "0x" + keccak256(raw), f"{path}: Keccak-256 differs from bytes")


def validate_lock_schema(value: Any, label: str = "lock") -> None:
    lock = exact_object(value, label, {
        "_comment", "abi", "artifacts", "compiler", "deployment", "generator",
        "provenance", "rpc", "schema", "sectionDigests", "sourceBehavior", "target",
    })
    require(lock["schema"] == 1 and type(lock["schema"]) is int, f"{label}.schema: expected integer 1")
    require(isinstance(lock["_comment"], str) and "GENERATED" in lock["_comment"],
            f"{label}._comment: missing generated marker")

    generator = exact_object(lock["generator"], f"{label}.generator", {
        "name", "networkFreeOrdinaryCheck", "regenerationCommand", "version",
    })
    require(generator == {
        "name": "blanc-lido-ossifiable-proxy-reference",
        "networkFreeOrdinaryCheck": True,
        "regenerationCommand": "python3 scripts/lido-ossifiable-proxy-reference.py generate",
        "version": 1,
    }, f"{label}.generator: frozen generator contract differs")

    target = exact_object(lock["target"], f"{label}.target", {
        "address", "chainId", "contract", "deploymentBlock", "deploymentBlockHash",
        "deploymentRole", "deploymentTransaction", "sourcePath",
    })
    require(target == {
        "address": TARGET_ADDRESS,
        "chainId": 1,
        "contract": "OssifiableProxy",
        "deploymentBlock": 17172547,
        "deploymentBlockHash": TARGET_BLOCK_HASH,
        "deploymentRole": "WithdrawalQueueERC721 proxy",
        "deploymentTransaction": TARGET_TX,
        "sourcePath": TARGET_SOURCE,
    }, f"{label}.target: frozen target identity differs")

    provenance = exact_object(lock["provenance"], f"{label}.provenance", {
        "buildFiles", "closureComplete", "inputFiles", "lidoCommit", "lidoTag",
        "openzeppelinCommit", "openzeppelinTag", "sourceFiles",
    })
    require(provenance["lidoCommit"] == "17005714f151e5502c559932319a3f2f74ac2436"
            and provenance["lidoTag"] == "v4.0.0",
            f"{label}.provenance: Lido identity differs")
    require(provenance["openzeppelinCommit"] == "6bd6b76d1156e20e45d1016f355d154141c7e5b9"
            and provenance["openzeppelinTag"] == "v4.4.1",
            f"{label}.provenance: OpenZeppelin identity differs")
    require(boolean(provenance["closureComplete"], f"{label}.provenance.closureComplete"),
            f"{label}.provenance: closure must be complete")
    input_rows = exact_list(provenance["inputFiles"], f"{label}.provenance.inputFiles", len(EXPECTED_INPUTS))
    actual_inputs: dict[str, str] = {}
    for index, row_value in enumerate(input_rows):
        row = exact_object(row_value, f"{label}.provenance.inputFiles[{index}]", {"path", "sha256"})
        actual_inputs[string(row["path"], "input path")] = digest(row["sha256"], "input sha256")
    require(actual_inputs == EXPECTED_INPUTS, f"{label}.provenance.inputFiles: exact inventory differs")

    source_rows = exact_list(provenance["sourceFiles"], f"{label}.provenance.sourceFiles", 7)
    actual_sources: dict[str, tuple[str, str]] = {}
    for index, row_value in enumerate(source_rows):
        row = exact_object(row_value, f"{label}.provenance.sourceFiles[{index}]", {
            "byteLength", "gitBlob", "inputPath", "keccak256", "sha256", "sourceUnit",
        })
        source_unit = string(row["sourceUnit"], "source unit")
        integer(row["byteLength"], "source byte length")
        pattern(row["gitBlob"], "source Git blob", r"[0-9a-f]{40}")
        pattern(row["keccak256"], "source Keccak", r"0x[0-9a-f]{64}")
        string(row["inputPath"], "source input path")
        actual_sources[source_unit] = (digest(row["sha256"], "source SHA"), row["gitBlob"])
    require(actual_sources == {path: (EXPECTED_SOURCE_SHA256[path], EXPECTED_SOURCE_BLOBS[path])
                               for path in EXPECTED_SOURCE_SHA256},
            f"{label}.provenance.sourceFiles: exact source closure differs")
    exact_list(provenance["buildFiles"], f"{label}.provenance.buildFiles", 5)

    compiler = exact_object(lock["compiler"], f"{label}.compiler", {
        "binary", "longVersion", "metadataSettings", "packaging", "releaseManifestEntry",
        "standardInputSha256", "standardInputSettings", "standardOutputSha256", "version",
    })
    require(compiler["version"] == "0.8.9"
            and compiler["longVersion"] == "0.8.9+commit.e5eed63a"
            and compiler["packaging"] == "emscripten-wasm32",
            f"{label}.compiler: identity differs")
    require(same_json(compiler["standardInputSettings"], EXPECTED_SETTINGS),
            f"{label}.compiler.standardInputSettings: exact settings differ")
    require(same_json(compiler["metadataSettings"], EXPECTED_METADATA_SETTINGS),
            f"{label}.compiler.metadataSettings: effective settings differ")
    require(compiler["standardInputSha256"] == EXPECTED_INPUTS["standard-json-input.json"]
            and compiler["standardOutputSha256"] == EXPECTED_INPUTS["standard-json-output.json"],
            f"{label}.compiler: Standard JSON identities differ")
    binary = exact_object(compiler["binary"], f"{label}.compiler.binary", {
        "byteLength", "file", "keccak256", "sha256",
    })
    require(binary == {
        "byteLength": 26173264,
        "file": "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js",
        "keccak256": "0xbc470ab3442e78bb4d3f16c01c39b2f160f4f34eb4373efed11c234e1c7f6ca0",
        "sha256": "5b25f987aae32a0275fdc6c1be36cc47cf126024a04dafd8e4be39a1d1d1422c",
    }, f"{label}.compiler.binary: exact compiler bytes differ")
    release = exact_object(compiler["releaseManifestEntry"], f"{label}.compiler.releaseManifestEntry", {
        "build", "keccak256", "longVersion", "path", "sha256", "urls", "version",
    })
    require(release["path"] == binary["file"] and release["version"] == "0.8.9"
            and release["longVersion"] == compiler["longVersion"]
            and release["sha256"] == "0x" + binary["sha256"]
            and release["keccak256"] == binary["keccak256"],
            f"{label}.compiler.releaseManifestEntry: release pin differs")

    abi = exact_object(lock["abi"], f"{label}.abi", {
        "abiOnlyDeclarations", "behavioralEvents", "compilerEvents", "constructor",
        "counts", "decodingBoundaries", "dispatchSelectorsUnique", "errors", "fallback",
        "functions", "raw", "rawSha256", "receive",
    })
    require(digest(abi["rawSha256"], f"{label}.abi.rawSha256") ==
            "a58f18aae44e664111abe21ed926d9cedeae02562163945054b23ac2e53e9fc0",
            f"{label}.abi.rawSha256: frozen compiler ABI differs")
    require(abi["rawSha256"] == section_digest(abi["raw"]), f"{label}.abi.rawSha256: not derived")
    exact_list(abi["raw"], f"{label}.abi.raw", 16)
    require(abi["counts"] == {
        "abiDeclarations": 16, "behavioralEvents": 3, "compilerEvents": 4,
        "constructors": 1, "customErrors": 2, "fallback": 1, "functions": 7, "receive": 1,
    }, f"{label}.abi.counts: exact census differs")
    require(boolean(abi["dispatchSelectorsUnique"], f"{label}.abi.dispatchSelectorsUnique"),
            f"{label}.abi: selector collision")

    constructor = exact_object(abi["constructor"], f"{label}.abi.constructor", {
        "argumentNames", "argumentTypes", "entry", "nonpayableValueRejected", "payable",
    })
    require(constructor["argumentTypes"] == ["address", "address", "bytes"]
            and constructor["argumentNames"] == ["implementation_", "admin_", "data_"]
            and constructor["payable"] is False and constructor["nonpayableValueRejected"] is True,
            f"{label}.abi.constructor: constructor boundary differs")
    require(constructor["entry"].get("stateMutability") == "nonpayable",
            f"{label}.abi.constructor.entry: derived constructor must be nonpayable")

    function_rows = exact_list(abi["functions"], f"{label}.abi.functions", 7)
    observed_functions = []
    selectors = []
    for index, row_value in enumerate(function_rows):
        row = exact_object(row_value, f"{label}.abi.functions[{index}]", {
            "acceptsValue", "classification", "entry", "returnTypes", "selector", "signature",
        })
        observed_functions.append((row["signature"], row["selector"], row["entry"].get("stateMutability"), row["returnTypes"]))
        selectors.append(row["selector"])
        require(row["acceptsValue"] is False and row["classification"] == "functional-interface",
                f"{label}.abi.functions[{index}]: named endpoint value/classification differs")
    require(observed_functions == FUNCTIONS, f"{label}.abi.functions: signatures/selectors/mutability differ")
    require(len(set(selectors)) == 7, f"{label}.abi.functions: dispatch collision")

    for kind in ("fallback", "receive"):
        row = exact_object(abi[kind], f"{label}.abi.{kind}", {
            "acceptsValue", "classification", "entry", "signature",
        })
        require(row["signature"] == kind and row["entry"] == {"stateMutability": "payable", "type": kind}
                and row["acceptsValue"] is True and row["classification"] == "functional-interface",
                f"{label}.abi.{kind}: payable endpoint differs")

    errors = exact_list(abi["errors"], f"{label}.abi.errors", 2)
    require([(row.get("signature"), row.get("selector")) for row in errors] == ERRORS,
            f"{label}.abi.errors: exact custom-error census differs")
    behavioral_events = exact_list(abi["behavioralEvents"], f"{label}.abi.behavioralEvents", 3)
    require([(row.get("signature"), row.get("topic0"), row.get("indexed"))
             for row in behavioral_events] == EVENTS,
            f"{label}.abi.behavioralEvents: exact reachable event census differs")
    compiler_events = exact_list(abi["compilerEvents"], f"{label}.abi.compilerEvents", 4)
    require({row.get("signature") for row in compiler_events} == {
        "AdminChanged(address,address)", "BeaconUpgraded(address)",
        "ProxyOssified()", "Upgraded(address)",
    }, f"{label}.abi.compilerEvents: inherited ABI declarations differ")
    declarations = exact_list(abi["abiOnlyDeclarations"], f"{label}.abi.abiOnlyDeclarations", 1)
    require(declarations[0].get("signature") == "BeaconUpgraded(address)"
            and declarations[0].get("behavioralSurface") is False,
            f"{label}.abi.abiOnlyDeclarations: BeaconUpgraded classification differs")
    boundaries = exact_list(abi["decodingBoundaries"], f"{label}.abi.decodingBoundaries", 10)
    require([row.get("signature") for row in boundaries] == [
        "constructor(address,address,bytes)", *[row[0] for row in FUNCTIONS], "fallback", "receive",
    ], f"{label}.abi.decodingBoundaries: endpoint coverage/order differs")

    behavior = exact_object(lock["sourceBehavior"], f"{label}.sourceBehavior", {
        "authorizationOrder", "constructorOrder", "reasonStrings", "slots",
    })
    require(behavior["authorizationOrder"] == [
        "admin == address(0) -> ProxyIsOssified()",
        "admin != msg.sender -> NotAdmin()",
        "authorized body",
    ], f"{label}.sourceBehavior.authorizationOrder: precedence differs")
    require(behavior["constructorOrder"] == [
        "validate and write implementation", "emit Upgraded(address)",
        "optional setup delegatecall", "read post-setup admin", "emit AdminChanged(address,address)",
        "validate nonzero admin", "write admin",
    ], f"{label}.sourceBehavior.constructorOrder: source order differs")
    reasons = exact_list(behavior["reasonStrings"], f"{label}.sourceBehavior.reasonStrings", 3)
    require([row.get("message") for row in reasons] == REASON_STRINGS,
            f"{label}.sourceBehavior.reasonStrings: inherited string family differs")
    require(all(row.get("selector") == "0x08c379a0" for row in reasons),
            f"{label}.sourceBehavior.reasonStrings: Error(string) selector differs")
    slots = exact_list(behavior["slots"], f"{label}.sourceBehavior.slots", 2)
    require(slots == [
        {"classification": "functional-interoperability", "name": "implementation", "value": IMPLEMENTATION_SLOT},
        {"classification": "functional-interoperability", "name": "admin", "value": ADMIN_SLOT},
    ], f"{label}.sourceBehavior.slots: ERC-1967 functional slots differ")

    artifacts = exact_object(lock["artifacts"], f"{label}.artifacts", {
        "compilerOutputReproducedByteForByte", "creationTemplate", "runtime",
    })
    require(boolean(artifacts["compilerOutputReproducedByteForByte"], "compiler reproduction"),
            f"{label}.artifacts: ordinary compilation was not reproduced")
    validate_artifact(artifacts["creationTemplate"], f"{label}.artifacts.creationTemplate", 4207,
                      "0x015bbc23707827310841f6f536b755f9c67ea516844a7684c85b97d39bdf0ffd")
    validate_artifact(artifacts["runtime"], f"{label}.artifacts.runtime", 2497,
                      "0x9bc25fa4b2f98d56db4aa4156a6dc98360ccd4ef9c7bc7f891797b0024272100")

    deployment = exact_object(lock["deployment"], f"{label}.deployment", {
        "block", "completeInput", "constructor", "createAddressDerivation", "historicalReceipt",
        "independentBoundaryExtraction", "transaction",
    })
    require(deployment["transaction"] == TARGET_TX, f"{label}.deployment.transaction: differs")
    require(deployment["block"] == {
        "hash": TARGET_BLOCK_HASH, "number": 17172547, "timestamp": 1683023927,
        "timestampIso": "2023-05-02T10:38:47Z",
    }, f"{label}.deployment.block: frozen block differs")
    validate_artifact(deployment["completeInput"], f"{label}.deployment.completeInput", 4335,
                      "0xd79529af7d327023f254f321651a98ab8f1abe14e89b735a59054bcbff10b868")
    constructor_boundary = exact_object(deployment["constructor"], f"{label}.deployment.constructor", {
        "arguments", "creationTemplateBytes", "encodedSuffix", "encodedSuffixBytes", "payable",
    })
    require(constructor_boundary["arguments"] == [
        "0x6F6541C2203196fEeDd14CD2C09550dA1CbEDa31",
        "0x8Ea83AD72396f1E0cD2f8E72b1461db8Eb6aF7B5", "0x",
    ] and constructor_boundary["creationTemplateBytes"] == 4207
            and constructor_boundary["encodedSuffixBytes"] == 128
            and constructor_boundary["payable"] is False,
            f"{label}.deployment.constructor: exact canonical tuple/boundary differs")
    require(deployment["createAddressDerivation"].get("derivedAddress") == TARGET_ADDRESS,
            f"{label}.deployment.createAddressDerivation: derived address differs")
    require(deployment["historicalReceipt"].get("gasUsed") == 669988
            and deployment["historicalReceipt"].get("status") == 1,
            f"{label}.deployment.historicalReceipt: receipt differs")
    require(deployment["independentBoundaryExtraction"] == {
        "compilerCreationEqualsTransactionPrefix": True,
        "decodedArgumentsEqualManifest": True,
        "rpcCodeEqualsCompilerRuntime": True,
        "transactionSuffixIsExactAbiEncoding": True,
    }, f"{label}.deployment.independentBoundaryExtraction: relations differ")

    rpc = exact_object(lock["rpc"], f"{label}.rpc", {"agreement", "captures"})
    captures = exact_list(rpc["captures"], f"{label}.rpc.captures", 2)
    require([(row.get("file"), row.get("operator"), row.get("url")) for row in captures] == [
        ("rpc-blastapi.json", "BlastAPI", "https://eth-mainnet.public.blastapi.io"),
        ("rpc-drpc.json", "dRPC", "https://eth.drpc.org"),
    ], f"{label}.rpc.captures: independent operators differ")
    require(rpc["agreement"] == {
        "blockHeadersEqual": True, "blockMembershipEqual": True, "codesEqual": True,
        "receiptsEqualOnPinnedFields": True, "transactionsEqualOnPinnedFields": True,
    }, f"{label}.rpc.agreement: cross-operator agreement differs")

    section_digests = exact_object(lock["sectionDigests"], f"{label}.sectionDigests", {
        "abi", "artifacts", "compiler", "deployment", "provenance", "rpc", "sourceBehavior", "target",
    })
    for section, recorded in section_digests.items():
        require(digest(recorded, f"{label}.sectionDigests.{section}") == section_digest(lock[section]),
                f"{label}.sectionDigests.{section}: section digest differs")


def main() -> int:
    try:
        raw = LOCK.read_bytes()
        value = strict_json(raw, str(LOCK))
        validate_lock_schema(value, "reference lock")
        require(raw == (json.dumps(value, indent=2, sort_keys=True) + "\n").encode(),
                "reference lock: JSON is not canonical")
    except (OSError, SchemaError) as exc:
        print(f"REGRESSION — Lido OssifiableProxy reference schema: {exc}", file=sys.stderr)
        return 1
    print("OK — Lido OssifiableProxy independent schema: 7 named endpoints, constructor, fallback/receive, 3 reachable events, 2 errors, 2 slots")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
