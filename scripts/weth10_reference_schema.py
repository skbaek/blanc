#!/usr/bin/env python3
"""Independent exact-schema contract for the generated WETH10 target lock.

This file deliberately does not import the generator or derive its required
keys from ``build()``.  It closes the completeness gap that byte-comparing a
generated artifact with the output of the same builder cannot detect.
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
LOCK = Path(os.environ.get("WETH10_REFERENCE_LOCK", ROOT / "scripts" / "weth10-reference.json"))
TARGET = "0xf4BB2e28688e89fCcE3c0580D37d36A7672E8A9F"
SOURCE_PATH = "contracts/WETH10.sol"
FUNCTION_SIGNATURES = {
    "CALLBACK_SUCCESS()", "DOMAIN_SEPARATOR()", "PERMIT_TYPEHASH()",
    "allowance(address,address)", "approve(address,uint256)",
    "approveAndCall(address,uint256,bytes)", "balanceOf(address)", "decimals()",
    "deploymentChainId()", "deposit()", "depositTo(address)",
    "depositToAndCall(address,bytes)", "flashFee(address,uint256)",
    "flashLoan(address,address,uint256,bytes)", "flashMinted()",
    "maxFlashLoan(address)", "name()", "nonces(address)",
    "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", "symbol()",
    "totalSupply()", "transfer(address,uint256)",
    "transferAndCall(address,uint256,bytes)",
    "transferFrom(address,address,uint256)", "withdraw(uint256)",
    "withdrawFrom(address,address,uint256)", "withdrawTo(address,uint256)",
}
EVENT_SIGNATURES = {"Approval(address,address,uint256)", "Transfer(address,address,uint256)"}
PAYABLE_FUNCTIONS = {"deposit()", "depositTo(address)", "depositToAndCall(address,bytes)"}
IMMUTABLE_NAMES = {"CALLBACK_SUCCESS", "PERMIT_TYPEHASH", "deploymentChainId", "_DOMAIN_SEPARATOR"}
IMMUTABLE_ID_NAMES = {
    "44": "CALLBACK_SUCCESS", "49": "PERMIT_TYPEHASH",
    "51": "deploymentChainId", "53": "_DOMAIN_SEPARATOR",
}
IMMUTABLE_REFERENCES = {
    "44": [{"length": 32, "start": 5473}, {"length": 32, "start": 6760}],
    "49": [{"length": 32, "start": 4193}, {"length": 32, "start": 8721}],
    "51": [
        {"length": 32, "start": 4237},
        {"length": 32, "start": 8473},
        {"length": 32, "start": 8823},
    ],
    "53": [{"length": 32, "start": 4290}, {"length": 32, "start": 8876}],
}
REASON_STRINGS = [
    "WETH: flash mint only WETH10",
    "WETH: individual loan limit exceeded",
    "WETH: total loan limit exceeded",
    "WETH: flash loan failed",
    "WETH: request exceeds allowance",
    "WETH: burn amount exceeds balance",
    "WETH: Expired permit",
    "WETH: invalid permit",
    "WETH: transfer amount exceeds balance",
    "WETH: ETH transfer failed",
    "WETH: Ether transfer failed",
]
EXPECTED_INPUT_SETTINGS = {
    "optimizer": {"enabled": True, "runs": 20000},
    "outputSelection": {
        "*": {
            "*": [
                "abi", "evm.bytecode", "evm.deployedBytecode", "evm.methodIdentifiers",
                "metadata", "devdoc", "userdoc", "storageLayout", "evm.gasEstimates",
            ],
            "": ["ast"],
        }
    },
    "metadata": {"useLiteralContent": True},
}
EXPECTED_EFFECTIVE_SETTINGS = {
    "compilationTarget": {SOURCE_PATH: "WETH10"},
    "evmVersion": "istanbul",
    "libraries": {},
    "metadata": {"bytecodeHash": "ipfs", "useLiteralContent": True},
    "optimizer": {"enabled": True, "runs": 20000},
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
    missing, unknown = keys - set(value), set(value) - keys
    require(not missing, f"{path}: missing fields {sorted(missing)}")
    require(not unknown, f"{path}: unknown fields {sorted(unknown)}")
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
    """JSON equality that does not inherit Python's ``True == 1`` behavior."""
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
    require(re.fullmatch(regex, value) is not None, f"{path}: malformed value")
    return value


def digest(value: Any, path: str) -> str:
    return pattern(value, path, r"[0-9a-f]{64}")


def section_digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def word(value: Any, path: str) -> str:
    return pattern(value, path, r"0x[0-9a-f]{64}")


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
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
             for x in range(5)]
        d = [c[(x - 1) % 5] ^ rol(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= d[x]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rol(state[x + 5 * y], ROT[x][y])
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])
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


def abi_argument(value: Any, path: str, event: bool = False) -> dict[str, Any]:
    keys = {"internalType", "name", "type"} | ({"indexed"} if event else set())
    row = exact_object(value, path, keys)
    for key in ("internalType", "name", "type"):
        string(row[key], f"{path}.{key}")
    if event:
        boolean(row["indexed"], f"{path}.indexed")
    return row


def function_row(value: Any, path: str) -> dict[str, Any]:
    row = exact_object(value, path, {"entry", "signature", "selector", "payable", "returnTypes"})
    entry = exact_object(row["entry"], f"{path}.entry",
                         {"inputs", "name", "outputs", "stateMutability", "type"})
    require(entry["type"] == "function", f"{path}.entry.type: expected function")
    name = string(entry["name"], f"{path}.entry.name")
    inputs = exact_list(entry["inputs"], f"{path}.entry.inputs")
    outputs = exact_list(entry["outputs"], f"{path}.entry.outputs")
    for index, item in enumerate(inputs):
        abi_argument(item, f"{path}.entry.inputs[{index}]")
    for index, item in enumerate(outputs):
        abi_argument(item, f"{path}.entry.outputs[{index}]")
    mutability = string(entry["stateMutability"], f"{path}.entry.stateMutability")
    require(mutability in {"payable", "nonpayable", "view", "pure"},
            f"{path}.entry.stateMutability: invalid enum")
    signature = string(row["signature"], f"{path}.signature")
    require(signature == f"{name}({','.join(item['type'] for item in inputs)})",
            f"{path}.signature: differs from canonical ABI entry")
    require(pattern(row["selector"], f"{path}.selector", r"0x[0-9a-f]{8}")
            == "0x" + keccak256(signature.encode())[:8], f"{path}.selector: wrong Ethereum Keccak")
    require(boolean(row["payable"], f"{path}.payable") == (mutability == "payable"),
            f"{path}.payable: differs from stateMutability")
    returns = exact_list(row["returnTypes"], f"{path}.returnTypes")
    require(returns == [item["type"] for item in outputs], f"{path}.returnTypes: differs from outputs")
    return row


def event_row(value: Any, path: str) -> dict[str, Any]:
    row = exact_object(value, path, {"entry", "signature", "topic0"})
    entry = exact_object(row["entry"], f"{path}.entry", {"anonymous", "inputs", "name", "type"})
    require(entry["type"] == "event", f"{path}.entry.type: expected event")
    boolean(entry["anonymous"], f"{path}.entry.anonymous")
    name = string(entry["name"], f"{path}.entry.name")
    inputs = exact_list(entry["inputs"], f"{path}.entry.inputs")
    for index, item in enumerate(inputs):
        abi_argument(item, f"{path}.entry.inputs[{index}]", event=True)
    signature = string(row["signature"], f"{path}.signature")
    require(signature == f"{name}({','.join(item['type'] for item in inputs)})",
            f"{path}.signature: differs from canonical event entry")
    require(word(row["topic0"], f"{path}.topic0") == "0x" + keccak256(signature.encode()),
            f"{path}.topic0: wrong Ethereum Keccak")
    return row


def validate_lock_schema(lock: Any, label: str = "lock") -> None:
    root = exact_object(lock, label, {
        "_comment", "generator", "target", "provenance", "compiler", "runtime",
        "observation", "abi", "deployment", "sourceBehavior",
    })
    require(root["_comment"] == "GENERATED by scripts/weth10-reference.py; do not edit by hand.",
            f"{label}._comment: wrong generated marker")

    generator = exact_object(root["generator"], f"{label}.generator",
                             {"name", "version", "implementation", "regenerationCommand"})
    require(same_json(generator, {
        "name": "blanc-weth10-reference", "version": 2,
        "implementation": "scripts/weth10-reference.py",
        "regenerationCommand": "python3 scripts/weth10-reference.py generate",
    }), f"{label}.generator: wrong deterministic generator contract")

    target = exact_object(root["target"], f"{label}.target", {
        "address", "chainId", "deploymentTransaction", "deploymentBlock", "deploymentBlockHash"})
    require(target["address"] == TARGET and target["chainId"] == "0x1",
            f"{label}.target: wrong address or chain")
    require(target["deploymentTransaction"]
            == "0xef45e3478fb21e7a11916a20f32e452ea511dfef0561bce034627bf4eebbc590",
            f"{label}.target.deploymentTransaction: wrong transaction")
    require(integer(target["deploymentBlock"], f"{label}.target.deploymentBlock") == 11954957,
            f"{label}.target.deploymentBlock: wrong deployment block")
    require(target["deploymentBlockHash"]
            == "0x3a97e20c1794a8cc92ca963695f4a80b70149b8cbfe003f28f541b8b03b662f5",
            f"{label}.target.deploymentBlockHash: wrong deployment block hash")

    provenance = exact_object(root["provenance"], f"{label}.provenance", {
        "repository", "deploymentCommit", "parentSourceCommit", "deploymentArtifactPath",
        "parentSourceGitBlob",
        "deploymentArtifactGitBlob", "deploymentArtifactSha256", "solcInputPath", "solcInputHash",
        "solcInputGitBlob", "solcInputSha256", "sourcePath", "sourceGitBlob", "sourceSha256",
        "sourceTrailingLfBytes", "sourceDigests", "relations",
    })
    require(provenance["repository"] == "https://github.com/WETH10/WETH10"
            and provenance["deploymentCommit"] == "17b9cca6bd823ad1208c1cd0df4ef5a4c1003689"
            and provenance["parentSourceCommit"] == "4e7ed4085c07be94452cf64390fee36bd4d4e46e"
            and provenance["parentSourceGitBlob"] == "46de31164d7ac7a9ede0ae592e86a161a58737b2",
            f"{label}.provenance: wrong repository revisions")
    require(provenance["deploymentArtifactPath"] == "deployments/mainnet/WETH10.json"
            and provenance["deploymentArtifactGitBlob"] == "28ce831b4cf9eddcaaebaa97996caf0a4d88c801",
            f"{label}.provenance: wrong deployment artifact identity")
    require(provenance["solcInputPath"]
            == "deployments/mainnet/solcInputs/77ca555bcb549eca2b7b96e19962a69c.json"
            and provenance["solcInputHash"] == "77ca555bcb549eca2b7b96e19962a69c"
            and provenance["solcInputGitBlob"] == "b2415de923d26612ad093ebcba2d0d375b3369ad",
            f"{label}.provenance: wrong embedded standard-input identity")
    require(provenance["sourcePath"] == SOURCE_PATH
            and provenance["sourceGitBlob"] == "46de31164d7ac7a9ede0ae592e86a161a58737b2"
            and integer(provenance["sourceTrailingLfBytes"],
                        f"{label}.provenance.sourceTrailingLfBytes") == 1,
            f"{label}.provenance: wrong primary-source identity/newline shape")
    require(provenance["deploymentArtifactSha256"]
            == "79cad88e558260129b7d026ff1260aeaeab59ac41d09075b4f986251cdc781e8"
            and provenance["solcInputSha256"]
            == "885b6d0d13942f2e16b36269f39a5903765194462db141c703f897d604ac9e71"
            and provenance["sourceSha256"]
            == "2bbc258e35b4174f3e358fc0cbfa5d0e8e48946649294ba91b95cb56e534c449",
            f"{label}.provenance: wrong independently pinned artifact/input/source SHA-256")
    source_digests = exact_list(provenance["sourceDigests"], f"{label}.provenance.sourceDigests", 8)
    source_paths: list[str] = []
    for index, item in enumerate(source_digests):
        row = exact_object(item, f"{label}.provenance.sourceDigests[{index}]",
                           {"path", "sha256", "keccak256"})
        source_paths.append(string(row["path"], f"{label}.provenance.sourceDigests[{index}].path"))
        digest(row["sha256"], f"{label}.provenance.sourceDigests[{index}].sha256")
        word(row["keccak256"], f"{label}.provenance.sourceDigests[{index}].keccak256")
    require(source_paths == sorted(set(source_paths)) and SOURCE_PATH in source_paths,
            f"{label}.provenance.sourceDigests: paths are not complete/sorted/unique")
    primary_digest = next(row for row in source_digests if row["path"] == SOURCE_PATH)
    require(primary_digest["sha256"] == provenance["sourceSha256"]
            and primary_digest["keccak256"]
            == "0x3a7152d5f20b58005e91f4552908193e5528ba67842dd64ba7ca63ac469a4d1a",
            f"{label}.provenance.sourceDigests: primary-source digest relation differs")
    require(section_digest(source_digests)
            == "3e5a7c9babbe5fcc3bbb9715a12f865a383199305a4c09bff4f5373ce820106c",
            f"{label}.provenance.sourceDigests: exact inventory digest differs")
    relations = exact_object(provenance["relations"], f"{label}.provenance.relations", {
        "sourceSnapshotEqualsStandardInput", "artifactAbiEqualsCompilerOutput",
        "artifactMetadataEqualsCompilerOutput", "artifactStorageLayoutEqualsCompilerOutput"})
    require(all(boolean(value, f"{label}.provenance.relations.{key}")
                for key, value in relations.items()), f"{label}.provenance.relations: false relation")

    compiler = exact_object(root["compiler"], f"{label}.compiler", {
        "longVersion", "packaging", "file", "manifestSha256", "binarySha256",
        "binaryKeccak256", "outputSha256", "inputLanguage", "settings",
        "metadataSettings", "releaseManifestEntry"})
    require(compiler["longVersion"] == "0.7.6+commit.7338295f"
            and compiler["packaging"] == "emscripten-wasm32"
            and compiler["file"] == "solc-emscripten-wasm32-v0.7.6+commit.7338295f.js"
            and compiler["inputLanguage"] == "Solidity",
            f"{label}.compiler: wrong compiler identity")
    digest(compiler["manifestSha256"], f"{label}.compiler.manifestSha256")
    require(compiler["binarySha256"]
            == "0xb94e69dfb056b3e26080f805ab43b668afbc0ac70bf124bfb7391ecfc0172ad2"
            and compiler["binaryKeccak256"]
            == "0xc68517effed7163db0c7f4559931a4c5530fe6f2a8a20596361640d9d7eff655"
            and compiler["outputSha256"]
            == "bcf32583b407489299bae7534864ae578451615ccb6a9197458d8bfc003bec8e",
            f"{label}.compiler: wrong independently pinned digests")
    require(same_json(compiler["settings"], EXPECTED_INPUT_SETTINGS),
            f"{label}.compiler.settings: incomplete or changed standard-input settings")
    require(same_json(compiler["metadataSettings"], EXPECTED_EFFECTIVE_SETTINGS),
            f"{label}.compiler.metadataSettings: incomplete or changed effective settings")
    release = exact_object(compiler["releaseManifestEntry"], f"{label}.compiler.releaseManifestEntry",
                           {"path", "version", "build", "longVersion", "keccak256", "sha256", "urls"})
    require(same_json(release, {
        "path": compiler["file"], "version": "0.7.6", "build": "commit.7338295f",
        "longVersion": compiler["longVersion"], "keccak256": compiler["binaryKeccak256"],
        "sha256": compiler["binarySha256"],
        "urls": ["dweb:/ipfs/QmWjG6PLzF5M6kxkHujhEMg5znQCgf2m1cM1UptKA719Hy"],
    }), f"{label}.compiler.releaseManifestEntry: wrong complete release entry")

    runtime = exact_object(root["runtime"], f"{label}.runtime", {
        "installedHex", "byteLength", "installedSha256", "installedCodehash", "templateSha256",
        "templateEqualsCompilerOutput", "templateInstalledSameLength",
        "templateInstalledAgreeOutsideImmutableReferences", "templateInstalledDifferingBytes",
        "immutableReferences", "immutableReferenceSpans", "immutableValues", "constants"})
    installed_hex = pattern(runtime["installedHex"], f"{label}.runtime.installedHex", r"0x(?:[0-9a-f]{2})+")
    installed = bytes.fromhex(installed_hex[2:])
    require(integer(runtime["byteLength"], f"{label}.runtime.byteLength") == len(installed) == 9975,
            f"{label}.runtime.byteLength: differs from installed bytes")
    require(runtime["installedSha256"] == hashlib.sha256(installed).hexdigest()
            == "ca979fc12a175535a08add286497b8fc3a1805f7bcef7ae90d3dc4307ac1c25a",
            f"{label}.runtime.installedSha256: differs from installed bytes/pin")
    require(runtime["installedCodehash"] == "0x" + keccak256(installed)
            == "0x50ea9957a23e0f53e98b5651d889eb768e72027663b99addf50898bb3a1fa5d2",
            f"{label}.runtime.installedCodehash: differs from installed bytes/pin")
    require(runtime["templateSha256"]
            == "4a26bad255e787129bbb44842adfa09ccaff758715a50f3979c61e6f7f61d958"
            and integer(runtime["templateInstalledDifferingBytes"],
                        f"{label}.runtime.templateInstalledDifferingBytes") == 195,
            f"{label}.runtime: wrong pinned template relation")
    for key in ("templateEqualsCompilerOutput", "templateInstalledSameLength",
                "templateInstalledAgreeOutsideImmutableReferences"):
        require(boolean(runtime[key], f"{label}.runtime.{key}"), f"{label}.runtime.{key}: false")
    require(same_json(runtime["immutableReferences"], IMMUTABLE_REFERENCES),
            f"{label}.runtime.immutableReferences: wrong exact compiler inventory")
    spans = exact_list(runtime["immutableReferenceSpans"], f"{label}.runtime.immutableReferenceSpans", 9)
    covered: set[int] = set()
    reconstructed: dict[str, list[dict[str, int]]] = {key: [] for key in IMMUTABLE_ID_NAMES}
    prior_start = -1
    for index, item in enumerate(spans):
        row = exact_object(item, f"{label}.runtime.immutableReferenceSpans[{index}]",
                           {"astId", "name", "start", "length"})
        ast_id = string(row["astId"], f"{label}.runtime.immutableReferenceSpans[{index}].astId")
        require(ast_id in IMMUTABLE_ID_NAMES and row["name"] == IMMUTABLE_ID_NAMES[ast_id],
                f"{label}.runtime.immutableReferenceSpans[{index}]: wrong id/name relation")
        start = integer(row["start"], f"{label}.runtime.immutableReferenceSpans[{index}].start")
        length = integer(row["length"], f"{label}.runtime.immutableReferenceSpans[{index}].length")
        require(length == 32 and prior_start < start and start + length <= len(installed),
                f"{label}.runtime.immutableReferenceSpans[{index}]: invalid order/bounds/length")
        prior_start = start
        cells = set(range(start, start + length))
        require(not covered & cells, f"{label}.runtime.immutableReferenceSpans[{index}]: overlap")
        covered |= cells
        reconstructed[ast_id].append({"start": start, "length": length})
    for rows in reconstructed.values():
        rows.sort(key=lambda item: item["start"])
    require(same_json(reconstructed, IMMUTABLE_REFERENCES),
            f"{label}.runtime.immutableReferenceSpans: flattened/raw inventories differ")
    values = exact_object(runtime["immutableValues"], f"{label}.runtime.immutableValues", IMMUTABLE_NAMES)
    for name, value in values.items():
        word(value, f"{label}.runtime.immutableValues.{name}")
    for ast_id, entries in IMMUTABLE_REFERENCES.items():
        name = IMMUTABLE_ID_NAMES[ast_id]
        for entry in entries:
            start, length = entry["start"], entry["length"]
            require("0x" + installed[start:start + length].hex() == values[name],
                    f"{label}.runtime.immutableValues.{name}: differs from installed runtime span")
    constants = exact_object(runtime["constants"], f"{label}.runtime.constants", IMMUTABLE_NAMES)
    expected_preimages = {
        "CALLBACK_SUCCESS": "ERC3156FlashBorrower.onFlashLoan",
        "PERMIT_TYPEHASH": "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)",
    }
    for name in ("CALLBACK_SUCCESS", "PERMIT_TYPEHASH"):
        row = exact_object(constants[name], f"{label}.runtime.constants.{name}",
                           {"classification", "preimage", "value"})
        require(row["classification"] == "compileTimeKeccakUtf8"
                and row["preimage"] == expected_preimages[name]
                and row["value"] == values[name]
                and row["value"] == "0x" + keccak256(string(row["preimage"], f"{label}.runtime.constants.{name}.preimage").encode()),
                f"{label}.runtime.constants.{name}: preimage/value relation differs")
    chain_constant = exact_object(constants["deploymentChainId"],
                                  f"{label}.runtime.constants.deploymentChainId",
                                  {"classification", "derivation", "value"})
    require(same_json(chain_constant, {
        "classification": "deploymentDependent", "derivation": "constructor chainid()",
        "value": values["deploymentChainId"],
    }) and chain_constant["value"] == "0x" + (1).to_bytes(32, "big").hex(),
            f"{label}.runtime.constants.deploymentChainId: wrong deployment relation")
    domain = exact_object(constants["_DOMAIN_SEPARATOR"], f"{label}.runtime.constants._DOMAIN_SEPARATOR",
                          {"classification", "derivation", "inputs", "value"})
    domain_inputs = exact_object(domain["inputs"], f"{label}.runtime.constants._DOMAIN_SEPARATOR.inputs",
                                 {"domainType", "name", "version", "chainId", "verifyingContract"})
    require(domain["classification"] == "deploymentDependent"
            and domain["derivation"]
            == "keccak256(abi.encode(domainTypeHash,nameHash,versionHash,chainId,address(this)))"
            and same_json(domain_inputs, {
                "domainType": "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)",
                "name": "Wrapped Ether v10", "version": "1", "chainId": "0x1",
                "verifyingContract": TARGET,
            }),
            f"{label}.runtime.constants._DOMAIN_SEPARATOR: wrong classification/inputs")
    encoded = b"".join([
        bytes.fromhex(keccak256(string(domain_inputs["domainType"], "domainType").encode())),
        bytes.fromhex(keccak256(string(domain_inputs["name"], "domain name").encode())),
        bytes.fromhex(keccak256(string(domain_inputs["version"], "domain version").encode())),
        (1).to_bytes(32, "big"), bytes.fromhex(TARGET[2:]).rjust(32, b"\0"),
    ])
    require(domain["value"] == values["_DOMAIN_SEPARATOR"] == "0x" + keccak256(encoded),
            f"{label}.runtime.constants._DOMAIN_SEPARATOR: wrong EIP-712 value")

    observation = exact_object(root["observation"], f"{label}.observation", {"block", "captures"})
    block = exact_object(observation["block"], f"{label}.observation.block", {"number", "hash"})
    require(same_json(block, {
        "number": "0x1882d8a",
        "hash": "0x6d0d8eb1b0ac3c46a2190a1af042c8d33e1215120134283ec2ef875548c7ebeb",
    }), f"{label}.observation.block: wrong pinned observation block")
    require(int(block["number"], 16) > target["deploymentBlock"],
            f"{label}.observation.block: predates deployment")
    captures = exact_list(observation["captures"], f"{label}.observation.captures", 2)
    expected_capture = {
        "publicnode": ("https://ethereum-rpc.publicnode.com", "ethereum-rpc.publicnode.com",
                       "3f5255f0158b8f7312fc64fa408575a83e53d3375c69afb9a703b7a12f458416",
                       "ad3fc1bbe01f2821c85657d7daae14eb7e995ffce45b414be0d3833d441d8512"),
        "drpc": ("https://eth.drpc.org", "eth.drpc.org",
                 "3a3374db0729131e491aeb77b75885dbf1b9cac1b9d64031e689efe7c7c31823",
                 "601cab608d019a7f96428bdf203d921527e5fcbfe5dbf063df20285835930f5b"),
    }
    names: list[str] = []
    for index, item in enumerate(captures):
        row = exact_object(item, f"{label}.observation.captures[{index}]", {
            "name", "operator", "operatorDomain", "request", "block", "envelopeSha256",
            "responseSha256", "runtimeSha256", "runtimeCodehash"})
        name = string(row["name"], f"{label}.observation.captures[{index}].name")
        require(name in expected_capture, f"{label}.observation.captures[{index}].name: unknown")
        names.append(name)
        operator, domain_name, envelope_sha, response_sha = expected_capture[name]
        require(row["operator"] == operator and row["operatorDomain"] == domain_name
                and row["envelopeSha256"] == envelope_sha and row["responseSha256"] == response_sha,
                f"{label}.observation.captures[{index}]: wrong independent acquisition identity")
        require(same_json(row["block"], block) and row["runtimeSha256"] == runtime["installedSha256"]
                and row["runtimeCodehash"] == runtime["installedCodehash"],
                f"{label}.observation.captures[{index}]: block/runtime relation differs")
        request = exact_object(row["request"], f"{label}.observation.captures[{index}].request",
                               {"jsonrpc", "id", "method", "params"})
        require(same_json(request, {"jsonrpc": "2.0", "id": 1, "method": "eth_getCode",
                                    "params": [TARGET, block["number"]]}),
                f"{label}.observation.captures[{index}].request: wrong exact request")
    require(names == ["publicnode", "drpc"], f"{label}.observation.captures: wrong order/names")

    abi = exact_object(root["abi"], f"{label}.abi",
                       {"functionCount", "eventCount", "receiveCount", "functions", "events", "receive"})
    require(integer(abi["functionCount"], f"{label}.abi.functionCount") == 27
            and integer(abi["eventCount"], f"{label}.abi.eventCount") == 2
            and integer(abi["receiveCount"], f"{label}.abi.receiveCount") == 1,
            f"{label}.abi: wrong counts")
    functions = exact_list(abi["functions"], f"{label}.abi.functions", 27)
    function_rows = [function_row(item, f"{label}.abi.functions[{index}]")
                     for index, item in enumerate(functions)]
    signatures = [row["signature"] for row in function_rows]
    require(signatures == sorted(FUNCTION_SIGNATURES), f"{label}.abi.functions: wrong signature set/order")
    require(len({row["selector"] for row in function_rows}) == 27,
            f"{label}.abi.functions: selector collision")
    require({row["signature"] for row in function_rows if row["payable"]} == PAYABLE_FUNCTIONS,
            f"{label}.abi.functions: wrong payable surface")
    events = exact_list(abi["events"], f"{label}.abi.events", 2)
    event_rows = [event_row(item, f"{label}.abi.events[{index}]") for index, item in enumerate(events)]
    require([row["signature"] for row in event_rows] == sorted(EVENT_SIGNATURES),
            f"{label}.abi.events: wrong event set/order")
    receive = exact_object(abi["receive"], f"{label}.abi.receive", {"entry", "payable", "returnTypes"})
    require(same_json(receive, {"entry": {"stateMutability": "payable", "type": "receive"},
                                "payable": True, "returnTypes": []}),
            f"{label}.abi.receive: wrong receive boundary")
    require(section_digest(abi)
            == "6f3543bd671feb63b68339d9d9e17a9bd0b90f8e483ee7f750e964646af437dc",
            f"{label}.abi: exact canonical ABI section digest differs")

    deployment = exact_object(root["deployment"], f"{label}.deployment", {
        "constructor", "externalCalls", "logs", "stateWrites", "initialLogicalState", "initializes"})
    constructor = exact_object(deployment["constructor"], f"{label}.deployment.constructor",
                               {"entry", "arguments", "payable", "rejectsNonzeroEndowment"})
    require(same_json(constructor, {
        "entry": {"inputs": [], "stateMutability": "nonpayable", "type": "constructor"},
        "arguments": [], "payable": False, "rejectsNonzeroEndowment": True,
    }), f"{label}.deployment.constructor: wrong C3a constructor boundary")
    require(deployment["externalCalls"] == [] and deployment["logs"] == []
            and deployment["stateWrites"] == ["deploymentChainId", "_DOMAIN_SEPARATOR"],
            f"{label}.deployment: unexpected calls/logs/state writes")
    initial = exact_object(deployment["initialLogicalState"], f"{label}.deployment.initialLogicalState",
                           {"balances", "allowances", "nonces", "flashMinted"})
    require(same_json(initial, {"balances": {}, "allowances": {}, "nonces": {},
                                "flashMinted": "0x" + "00" * 32}),
            f"{label}.deployment.initialLogicalState: not empty")
    initializes = exact_object(deployment["initializes"], f"{label}.deployment.initializes",
                               {"deploymentChainId", "_DOMAIN_SEPARATOR"})
    chain_init = exact_object(initializes["deploymentChainId"],
                              f"{label}.deployment.initializes.deploymentChainId",
                              {"derivation", "installedValue"})
    domain_init = exact_object(initializes["_DOMAIN_SEPARATOR"],
                               f"{label}.deployment.initializes._DOMAIN_SEPARATOR",
                               {"derivation", "inputs", "installedValue"})
    require(same_json(chain_init, {
                "derivation": constants["deploymentChainId"]["derivation"],
                "installedValue": values["deploymentChainId"],
            }) and same_json(domain_init, {
                "derivation": constants["_DOMAIN_SEPARATOR"]["derivation"],
                "inputs": constants["_DOMAIN_SEPARATOR"]["inputs"],
                "installedValue": values["_DOMAIN_SEPARATOR"],
            }),
            f"{label}.deployment.initializes: wrong immutable initialization relation")

    behavior = exact_object(root["sourceBehavior"], f"{label}.sourceBehavior",
                            {"reasonStrings", "guardOrder", "callbacks", "events", "storageLayout"})
    require(behavior["reasonStrings"] == REASON_STRINGS,
            f"{label}.sourceBehavior.reasonStrings: wrong exact inventory/order")
    guards = exact_list(behavior["guardOrder"], f"{label}.sourceBehavior.guardOrder", 27)
    guard_signatures: list[str] = []
    guard_count = 0
    for index, item in enumerate(guards):
        row = exact_object(item, f"{label}.sourceBehavior.guardOrder[{index}]",
                           {"signature", "sourceKind", "guardOrder"})
        guard_signatures.append(string(row["signature"], f"{label}.sourceBehavior.guardOrder[{index}].signature"))
        require(row["sourceKind"] in {"explicitFunction", "compilerGeneratedGetter"},
                f"{label}.sourceBehavior.guardOrder[{index}].sourceKind: invalid enum")
        sites = exact_list(row["guardOrder"], f"{label}.sourceBehavior.guardOrder[{index}].guardOrder")
        prior = -1
        for site_index, site in enumerate(sites):
            guard = exact_object(site,
                                 f"{label}.sourceBehavior.guardOrder[{index}].guardOrder[{site_index}]",
                                 {"sourceStart", "sourceLength", "enclosingBranches", "condition", "reason"})
            start = integer(guard["sourceStart"], "guard sourceStart")
            require(start > prior and integer(guard["sourceLength"], "guard sourceLength") > 0,
                    f"{label}.sourceBehavior.guardOrder[{index}]: guard spans not ordered/positive")
            prior = start
            string(guard["condition"], "guard condition")
            require(guard["reason"] in REASON_STRINGS, "guard reason is not in exact reason inventory")
            branches = exact_list(guard["enclosingBranches"], "guard enclosingBranches")
            for branch_index, branch in enumerate(branches):
                branch_row = exact_object(branch, f"guard branch[{branch_index}]", {"condition", "branch"})
                string(branch_row["condition"], "branch condition")
                require(branch_row["branch"] in {"then", "else"}, "branch enum is invalid")
            guard_count += 1
    require(guard_signatures == sorted(FUNCTION_SIGNATURES) and guard_count == 26,
            f"{label}.sourceBehavior.guardOrder: incomplete signature/site inventory")

    callbacks = exact_list(behavior["callbacks"], f"{label}.sourceBehavior.callbacks", 3)
    callback_signatures: list[str] = []
    for index, item in enumerate(callbacks):
        row = exact_object(item, f"{label}.sourceBehavior.callbacks[{index}]", {
            "interface", "method", "sourceSignature", "abiSignature", "selector", "inputs", "outputs"})
        for key in ("interface", "method", "sourceSignature", "abiSignature"):
            string(row[key], f"{label}.sourceBehavior.callbacks[{index}].{key}")
        inputs = exact_list(row["inputs"], f"{label}.sourceBehavior.callbacks[{index}].inputs")
        outputs = exact_list(row["outputs"], f"{label}.sourceBehavior.callbacks[{index}].outputs", 1)
        for arg_index, arg in enumerate(inputs):
            arg_row = exact_object(arg, f"callback input[{arg_index}]", {"name", "type"})
            string(arg_row["name"], "callback input name"); string(arg_row["type"], "callback input type")
        for arg_index, arg in enumerate(outputs):
            arg_row = exact_object(arg, f"callback output[{arg_index}]", {"name", "type"})
            string(arg_row["name"], "callback output name"); string(arg_row["type"], "callback output type")
        signature = row["abiSignature"]
        require(signature == f"{row['method']}({','.join(arg['type'] for arg in inputs)})"
                and row["selector"] == "0x" + keccak256(signature.encode())[:8],
                f"{label}.sourceBehavior.callbacks[{index}]: ABI signature/selector differs")
        callback_signatures.append(signature)
    require(callback_signatures == [
        "onTokenTransfer(address,uint256,bytes)",
        "onTokenApproval(address,uint256,bytes)",
        "onFlashLoan(address,address,uint256,uint256,bytes)",
    ], f"{label}.sourceBehavior.callbacks: wrong callback inventory/order")

    source_events = exact_list(behavior["events"], f"{label}.sourceBehavior.events", 2)
    source_by_signature: dict[str, dict[str, Any]] = {}
    for index, item in enumerate(source_events):
        row = exact_object(item, f"{label}.sourceBehavior.events[{index}]",
                           {"name", "signature", "topic0", "anonymous", "inputs"})
        string(row["name"], "source event name"); signature = string(row["signature"], "source event signature")
        word(row["topic0"], "source event topic0"); boolean(row["anonymous"], "source event anonymous")
        inputs = exact_list(row["inputs"], "source event inputs")
        for arg_index, arg in enumerate(inputs):
            arg_row = exact_object(arg, f"source event input[{arg_index}]", {"name", "type", "indexed"})
            string(arg_row["name"], "source event input name"); string(arg_row["type"], "source event input type")
            boolean(arg_row["indexed"], "source event input indexed")
        source_by_signature[signature] = row
    require(set(source_by_signature) == EVENT_SIGNATURES, f"{label}.sourceBehavior.events: wrong event set")
    for abi_event in event_rows:
        source_event = source_by_signature[abi_event["signature"]]
        entry = abi_event["entry"]
        require(same_json(source_event, {
            "name": entry["name"], "signature": abi_event["signature"], "topic0": abi_event["topic0"],
            "anonymous": entry["anonymous"],
            "inputs": [{"name": arg["name"], "type": arg["type"], "indexed": arg["indexed"]}
                       for arg in entry["inputs"]],
        }), f"{label}.sourceBehavior.events: differs from canonical ABI events")

    layout = exact_object(behavior["storageLayout"], f"{label}.sourceBehavior.storageLayout", {"storage", "types"})
    storage = exact_list(layout["storage"], f"{label}.sourceBehavior.storageLayout.storage", 4)
    for index, item in enumerate(storage):
        row = exact_object(item, f"{label}.sourceBehavior.storageLayout.storage[{index}]",
                           {"astId", "contract", "label", "offset", "slot", "type"})
        integer(row["astId"], "storage astId"); integer(row["offset"], "storage offset")
        for key in ("contract", "label", "slot", "type"):
            string(row[key], f"storage {key}")
    types = exact_object(layout["types"], f"{label}.sourceBehavior.storageLayout.types",
                         {"t_address", "t_mapping(t_address,t_mapping(t_address,t_uint256))",
                          "t_mapping(t_address,t_uint256)", "t_uint256"})
    for type_name, item in types.items():
        require(isinstance(item, dict), f"storage type {type_name}: expected object")
        encoding = item.get("encoding")
        keys = {"encoding", "label", "numberOfBytes"} | ({"key", "value"} if encoding == "mapping" else set())
        exact_object(item, f"storage type {type_name}", keys)
        require(encoding in {"inplace", "mapping"}, f"storage type {type_name}: invalid encoding")
        for key, value in item.items():
            string(value, f"storage type {type_name}.{key}")
    require(section_digest(behavior)
            == "ec6cf354f2b02fc2220554a2ff059c76fa80ecf58e70a086600c68fcecc467e8",
            f"{label}.sourceBehavior: exact inventory digest differs")


def main() -> None:
    try:
        data = strict_json(LOCK.read_bytes(), str(LOCK))
        validate_lock_schema(data, "generated lock")
    except (OSError, SchemaError) as exc:
        raise SystemExit(f"weth10_reference_schema.py: {exc}")


if __name__ == "__main__":
    main()
