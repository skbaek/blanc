#!/usr/bin/env python3
"""Generate and verify Blanc's offline lock for the deployed WETH10 target.

The ordinary commands are deliberately network-free:

    scripts/weth10-reference.py generate
    scripts/weth10-reference.py check

``refresh`` is the only networked command.  It re-acquires the named Git,
solc-bin, and two-RPC inputs, writes them under ``scripts/reference/weth10``,
then invokes ``generate``.  CI runs only ``check``.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REF = Path(os.environ.get("WETH10_REFERENCE_DIR", ROOT / "scripts" / "reference" / "weth10"))
INPUT = REF / "inputs"
SOURCE = INPUT / "source"
LOCK = Path(os.environ.get("WETH10_REFERENCE_LOCK", ROOT / "scripts" / "weth10-reference.json"))

REPOSITORY = "https://github.com/WETH10/WETH10"
DEPLOY_COMMIT = "17b9cca6bd823ad1208c1cd0df4ef5a4c1003689"
PARENT_COMMIT = "4e7ed4085c07be94452cf64390fee36bd4d4e46e"
SIBLING_COMMIT = "34d2712876138fb3d5f769a3965f4e330bc91169"
TARGET = "0xf4BB2e28688e89fCcE3c0580D37d36A7672E8A9F"
CHAIN_ID = "0x1"
ARTIFACT_PATH = "deployments/mainnet/WETH10.json"
SOLC_INPUT_PATH = "deployments/mainnet/solcInputs/77ca555bcb549eca2b7b96e19962a69c.json"
SOURCE_PATH = "contracts/WETH10.sol"
ARTIFACT_BLOB = "28ce831b4cf9eddcaaebaa97996caf0a4d88c801"
SOLC_INPUT_BLOB = "b2415de923d26612ad093ebcba2d0d375b3369ad"
SOLC_INPUT_HASH = "77ca555bcb549eca2b7b96e19962a69c"
SOLC_LONG_VERSION = "0.7.6+commit.7338295f"
SOLC_FILE = "solc-emscripten-wasm32-v0.7.6+commit.7338295f.js"
SOLC_LIST_URL = "https://binaries.soliditylang.org/emscripten-wasm32/list.json"
SOLC_BINARY_URL = "https://binaries.soliditylang.org/emscripten-wasm32/" + SOLC_FILE
RPCS = {
    "publicnode": "https://ethereum-rpc.publicnode.com",
    "drpc": "https://eth.drpc.org",
}


class ReferenceError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise ReferenceError(message)


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def load(path: Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read JSON {path.relative_to(ROOT)}: {exc}")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


# Keccak-256 (Ethereum's pre-NIST padding), kept here so the offline checker
# does not silently depend on a host package merely to recompute ABI selectors
# and the published solc binary's keccak digest.
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
    return "".join(word.to_bytes(8, "little").hex() for word in state)[:64]


def expect(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def hex_body(value: Any, what: str) -> str:
    expect(isinstance(value, str) and value.startswith("0x"), f"{what} is not 0x hex")
    body = value[2:]
    expect(len(body) % 2 == 0 and all(c in "0123456789abcdefABCDEF" for c in body),
           f"{what} is not even hexadecimal")
    return body.lower()


def contract_output(output: dict[str, Any]) -> dict[str, Any]:
    try:
        return output["contracts"][SOURCE_PATH]["WETH10"]
    except (KeyError, TypeError) as exc:
        fail(f"compiler output has no {SOURCE_PATH}:WETH10: {exc}")


def immutable_names(output: dict[str, Any]) -> dict[str, str]:
    wanted = {"44", "49", "51", "53"}
    found: dict[str, str] = {}

    def walk(value: Any) -> None:
        if isinstance(value, dict):
            if value.get("nodeType") == "VariableDeclaration" and str(value.get("id")) in wanted:
                found[str(value["id"])] = value.get("name")
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    walk(output.get("sources", {}))
    expect(set(found) == wanted and set(found.values()) == {
        "CALLBACK_SUCCESS", "PERMIT_TYPEHASH", "deploymentChainId", "_DOMAIN_SEPARATOR"},
        f"unexpected immutable declaration inventory: {found}")
    return found


def abi_rows(abi: Any) -> tuple[list[dict[str, str]], int]:
    expect(isinstance(abi, list), "ABI is not a list")
    functions: list[dict[str, str]] = []
    receive = 0
    for item in abi:
        expect(isinstance(item, dict) and isinstance(item.get("type"), str), "ABI entry has unknown shape")
        if item["type"] == "receive":
            receive += 1
        elif item["type"] == "function":
            name, inputs = item.get("name"), item.get("inputs")
            expect(isinstance(name, str) and isinstance(inputs, list), "function ABI entry has unknown shape")
            types = []
            for arg in inputs:
                expect(isinstance(arg, dict) and isinstance(arg.get("type"), str), "ABI input has unknown shape")
                types.append(arg["type"])
            signature = f"{name}({','.join(types)})"
            functions.append({"signature": signature, "selector": "0x" + keccak256(signature.encode())[:8]})
    functions.sort(key=lambda row: row["signature"])
    selectors = [row["selector"] for row in functions]
    expect(len(functions) == 27, f"expected 27 functions, found {len(functions)}")
    expect(len(set(selectors)) == len(selectors), "duplicate/colliding ABI selectors")
    expect(receive == 1, f"expected exactly one receive entry, found {receive}")
    return functions, receive


def rpc_runtime(envelope: Any, name: str) -> tuple[str, dict[str, Any]]:
    expect(isinstance(envelope, dict), f"RPC envelope {name} has unknown shape")
    required = {"operator", "request", "block", "responseRaw"}
    expect(set(envelope) == required, f"RPC envelope {name} fields are {sorted(envelope)}")
    request, block, raw = envelope["request"], envelope["block"], envelope["responseRaw"]
    expect(isinstance(envelope["operator"], str) and envelope["operator"].startswith("https://"),
           f"RPC envelope {name} operator is invalid")
    expect(isinstance(request, dict) and request.get("method") == "eth_getCode" and isinstance(request.get("params"), list),
           f"RPC envelope {name} request is invalid")
    expect(request["params"] == [TARGET, block.get("number")], f"RPC envelope {name} request parameters differ")
    expect(isinstance(block, dict) and set(block) == {"number", "hash"} and isinstance(raw, str),
           f"RPC envelope {name} block/raw fields are invalid")
    parsed = json.loads(raw)
    runtime = hex_body(parsed.get("result"), f"RPC envelope {name} result")
    return runtime, {"operator": envelope["operator"], "request": request, "block": block,
                     "responseSha256": sha256(raw.encode()), "runtimeSha256": sha256(bytes.fromhex(runtime))}


def check_drift_inputs(deployed_source: bytes) -> None:
    """Keep Step 2's source evidence available and recognisably complete.

    These files deliberately do not feed the normative target JSON: current
    main is drift evidence, not a second source of target identity.
    """
    current = (SOURCE / "current-main-WETH10.sol").read_bytes()
    current_diff = (SOURCE / "current-main.diff").read_text()
    comment_diff = (SOURCE / "comment-only-34d2712.diff").read_text()
    expect(current and current != deployed_source and "contracts/WETH10.sol" in current_diff,
           "current-main source snapshot/diff is missing or does not show drift")
    changed = [line for line in comment_diff.splitlines()
               if line.startswith(("+", "-")) and not line.startswith(("+++", "---"))]
    expect(len(changed) == 4 and all("/// @dev" in line for line in changed),
           "34d2712 corroboration is not the exact two-comment source diff")


def normalise_source(text: str) -> str:
    """Keep source facts readable while making harmless whitespace deterministic."""
    return " ".join(text.split())


def matching_delimiter(text: str, start: int, opening: str = "(", closing: str = ")") -> int:
    expect(start < len(text) and text[start] == opening, f"expected {opening!r} in source inventory")
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return index
    fail(f"unclosed {opening!r} in source inventory")


def split_top_level(text: str) -> list[str]:
    """Split a Solidity argument list without mistaking nested calls for commas."""
    pieces: list[str] = []
    start = depth = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == "," and depth == 0:
            pieces.append(text[start:index].strip())
            start = index + 1
    pieces.append(text[start:].strip())
    return pieces


def function_bodies(source: str) -> dict[str, str]:
    """Return the deployed source bodies for explicitly written functions.

    This deliberately accepts no overloaded public function: WETH10's locked
    ABI has none, so an overload is a source-shape change that must be reviewed.
    """
    bodies: dict[str, str] = {}
    for match in re.finditer(r"\bfunction\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", source):
        name = match.group(1)
        close_parameters = matching_delimiter(source, match.end() - 1)
        body_start = source.find("{", close_parameters)
        expect(body_start >= 0, f"source function {name} has no body")
        body_end = matching_delimiter(source, body_start, "{", "}")
        expect(name not in bodies, f"overloaded or duplicate source function {name}")
        bodies[name] = source[body_start + 1:body_end]
    return bodies


def source_requires(body: str) -> list[dict[str, str]]:
    guards: list[dict[str, str]] = []
    position = 0
    while True:
        found = re.search(r"\brequire\s*\(", body[position:])
        if found is None:
            return guards
        start = position + found.end() - 1
        end = matching_delimiter(body, start)
        arguments = split_top_level(body[start + 1:end])
        expect(len(arguments) == 2, "require in deployed source has an unexpected argument shape")
        reason = arguments[1].strip()
        expect(len(reason) >= 2 and reason[0] == reason[-1] == '"',
               "require in deployed source has a non-literal reason")
        guards.append({"condition": normalise_source(arguments[0]), "reason": reason[1:-1]})
        position = end + 1


def callback_inventory(standard: dict[str, Any], deployed_source: str) -> list[dict[str, str]]:
    """Derive all three external callback declarations from vendored sources."""
    sources = standard.get("sources")
    expect(isinstance(sources, dict), "standard input has no source inventory")
    all_source = "\n".join(
        item.get("content", "") for item in sources.values()
        if isinstance(item, dict) and isinstance(item.get("content"), str))
    callbacks = [
        ("ITransferReceiver", "onTokenTransfer"),
        ("IApprovalReceiver", "onTokenApproval"),
        ("IERC3156FlashBorrower", "onFlashLoan"),
    ]
    rows: list[dict[str, str]] = []
    for interface, method in callbacks:
        interface_match = re.search(r"\binterface\s+" + re.escape(interface) + r"\s*\{(.*?)\}", all_source, re.S)
        expect(interface_match is not None, f"callback interface {interface} is absent from standard input")
        declaration = re.search(
            r"\bfunction\s+" + re.escape(method) + r"\s*\((.*?)\)\s*external\s+returns\s*\((.*?)\)\s*;",
            interface_match.group(1), re.S)
        expect(declaration is not None, f"callback declaration {interface}.{method} has an unexpected shape")
        parameters = normalise_source(declaration.group(1))
        returns = normalise_source(declaration.group(2))
        # These occurrence checks ensure the source declaration is not merely
        # imported dead text: WETH10 actually makes each callback.
        expect(re.search(r"\b" + re.escape(method) + r"\s*\(", deployed_source) is not None,
               f"deployed WETH10 source does not call {interface}.{method}")
        abi_parameters = []
        for parameter in split_top_level(parameters):
            tokens = [token for token in parameter.split() if token not in {"calldata", "memory", "storage", "payable"}]
            expect(len(tokens) >= 1, f"callback parameter {parameter!r} has an unexpected shape")
            kind = tokens[0]
            abi_parameters.append("uint256" if kind == "uint" else kind)
        return_kind = returns.split()[0]
        rows.append({
            "interface": interface,
            "method": method,
            "sourceSignature": f"{method}({parameters}) external returns ({returns})",
            "abiSignature": f"{method}({','.join(abi_parameters)})",
            "returnType": "uint256" if return_kind == "uint" else return_kind,
        })
    return rows


def source_behavior_inventory(standard: dict[str, Any], output: dict[str, Any], abi: Any) -> dict[str, Any]:
    """Generate the source-side facts Step 2 must not rediscover by prose."""
    deployed_source = standard.get("sources", {}).get(SOURCE_PATH, {}).get("content")
    expect(isinstance(deployed_source, str), "standard input has no deployed WETH10 source")
    bodies = function_bodies(deployed_source)
    functions, _ = abi_rows(abi)
    generated_getters = {
        "CALLBACK_SUCCESS", "PERMIT_TYPEHASH", "allowance", "balanceOf", "decimals",
        "deploymentChainId", "flashMinted", "name", "nonces", "symbol",
    }
    guards: list[dict[str, Any]] = []
    reasons: list[str] = []
    for row in functions:
        name = row["signature"].split("(", 1)[0]
        if name in bodies:
            ordered = source_requires(bodies[name])
            source_kind = "explicitFunction"
        else:
            expect(name in generated_getters, f"ABI function {name} is absent from source and is not a known generated getter")
            ordered = []
            source_kind = "compilerGeneratedGetter"
        guards.append({"signature": row["signature"], "sourceKind": source_kind, "guardOrder": ordered})
        for guard in ordered:
            if guard["reason"] not in reasons:
                reasons.append(guard["reason"])
    events: list[dict[str, Any]] = []
    expect(isinstance(abi, list), "ABI is not a list")
    for item in abi:
        if isinstance(item, dict) and item.get("type") == "event":
            inputs = item.get("inputs")
            expect(isinstance(item.get("name"), str) and isinstance(inputs, list), "event ABI has an unexpected shape")
            types = []
            checked_inputs: list[dict[str, Any]] = []
            for argument in inputs:
                expect(isinstance(argument, dict) and isinstance(argument.get("name"), str)
                       and isinstance(argument.get("type"), str) and isinstance(argument.get("indexed"), bool),
                       "event ABI input has an unexpected shape")
                types.append(argument["type"])
                checked_inputs.append({"name": argument["name"], "type": argument["type"], "indexed": argument["indexed"]})
            signature = f"{item['name']}({','.join(types)})"
            events.append({"name": item["name"], "signature": signature,
                           "topic0": "0x" + keccak256(signature.encode()), "anonymous": item.get("anonymous"),
                           "inputs": checked_inputs})
    events.sort(key=lambda row: row["signature"])
    storage_layout = contract_output(output).get("storageLayout")
    expect(isinstance(storage_layout, dict) and set(storage_layout) == {"storage", "types"},
           "compiler output storage layout has an unexpected shape")
    expect(isinstance(storage_layout["storage"], list) and isinstance(storage_layout["types"], dict),
           "compiler output storage layout has invalid inventories")
    return {
        "reasonStrings": reasons,
        "guardOrder": guards,
        "callbacks": callback_inventory(standard, deployed_source),
        "events": events,
        "storageLayout": storage_layout,
    }


def build() -> dict[str, Any]:
    artifact_bytes = (INPUT / "deployment-artifact.json").read_bytes()
    input_bytes = (INPUT / "solc-input.json").read_bytes()
    output_bytes = (INPUT / "solc-output.json").read_bytes()
    manifest_bytes = (INPUT / "solc-emscripten-wasm32-list.json").read_bytes()
    artifact, standard, output, manifest = map(json.loads, (artifact_bytes, input_bytes, output_bytes, manifest_bytes))
    git_provenance = load(INPUT / "git-provenance.json")
    expect(git_provenance == {
        "repository": REPOSITORY, "deploymentCommit": DEPLOY_COMMIT, "parentSourceCommit": PARENT_COMMIT,
        "commentOnlySiblingCommit": SIBLING_COMMIT, "deploymentArtifactPath": ARTIFACT_PATH,
        "deploymentArtifactGitBlob": ARTIFACT_BLOB, "solcInputPath": SOLC_INPUT_PATH,
        "solcInputGitBlob": SOLC_INPUT_BLOB, "sourcePath": SOURCE_PATH,
        "deploymentSourceGitBlob": git_blob((SOURCE / "deployed-WETH10.sol").read_bytes()),
        "currentMainCommit": git_provenance.get("currentMainCommit")},
        "Git provenance has missing, unknown, or unexpected target fields")
    expect(git_blob(artifact_bytes) == ARTIFACT_BLOB, "deployment artifact Git blob identity differs")
    expect(artifact.get("address") == TARGET and artifact.get("solcInputHash") == SOLC_INPUT_HASH,
           "deployment artifact target identity differs")
    # Hardhat's deployment artifact calls this truncated identifier
    # ``solcInputHash``; it is the source filename/record key, not a SHA-256
    # digest of the JSON bytes.  Pin both representations independently.
    expect(artifact.get("solcInputHash") == Path(SOLC_INPUT_PATH).stem == SOLC_INPUT_HASH,
           "artifact solcInputHash differs from the pinned standard-input record")
    deployed_source = (SOURCE / "deployed-WETH10.sol").read_bytes()
    embedded = standard.get("sources", {}).get(SOURCE_PATH, {}).get("content")
    expect(isinstance(embedded, str) and embedded.encode() == deployed_source,
           "vendored deployment source does not equal standard-input source")
    check_drift_inputs(deployed_source)
    c = contract_output(output)
    errors = [row for row in output.get("errors", []) if row.get("severity") == "error"]
    expect(not errors, "vendored compiler output reports errors")
    template = hex_body(artifact.get("deployedBytecode"), "artifact deployedBytecode")
    output_template = hex_body("0x" + str(c.get("evm", {}).get("deployedBytecode", {}).get("object", "")),
                               "compiler deployedBytecode")
    expect(template == output_template, "artifact deployedBytecode does not exactly equal compiler template")
    immutables = c["evm"]["deployedBytecode"].get("immutableReferences")
    expect(isinstance(immutables, dict) and immutables, "compiler output has no immutable references")
    names = immutable_names(output)
    spans: list[dict[str, Any]] = []
    for key, entries in immutables.items():
        expect(key in names and isinstance(entries, list), "unknown immutable-reference shape")
        for entry in entries:
            expect(isinstance(entry, dict) and set(entry) == {"start", "length"} and entry["length"] == 32,
                   "unknown immutable span")
            spans.append({"name": names[key], "start": entry["start"], "length": entry["length"]})
    spans.sort(key=lambda row: (row["start"], row["name"]))
    covered = {i for row in spans for i in range(row["start"], row["start"] + row["length"])}
    expect(len(covered) == sum(row["length"] for row in spans), "overlapping immutable spans")
    one_runtime, one_capture = rpc_runtime(load(INPUT / "rpc-publicnode.json"), "publicnode")
    two_runtime, two_capture = rpc_runtime(load(INPUT / "rpc-drpc.json"), "drpc")
    expect(one_runtime == two_runtime, "vendored RPC captures disagree on installed runtime")
    expect(one_capture["block"] == two_capture["block"], "vendored RPC captures disagree on observation block")
    expect(one_capture["block"]["number"] != "0x0" and len(one_capture["block"]["hash"]) == 66,
           "RPC observation block is invalid")
    expect(len(template) == len(one_runtime), "template and installed runtime lengths differ")
    differing = [i for i in range(len(template) // 2) if template[2*i:2*i+2] != one_runtime[2*i:2*i+2]]
    expect(set(differing) <= covered, "installed runtime differs outside compiler immutable spans")
    functions, receive = abi_rows(c.get("abi"))
    source_behavior = source_behavior_inventory(standard, output, c.get("abi"))
    methods = c.get("evm", {}).get("methodIdentifiers")
    expect(isinstance(methods, dict), "compiler output has no method identifiers")
    expect({row["signature"]: row["selector"][2:] for row in functions} == methods,
           "ABI-recomputed selectors differ from compiler method identifiers")
    entry = next((row for row in manifest.get("builds", []) if row.get("path") == SOLC_FILE), None)
    expect(isinstance(entry, dict) and entry.get("longVersion") == SOLC_LONG_VERSION,
           "solc release manifest lacks the pinned compiler build")
    immutable_values: dict[str, list[str]] = {}
    for row in spans:
        value = one_runtime[2*row["start"]:2*(row["start"] + row["length"])]
        immutable_values.setdefault(row["name"], []).append("0x" + value)
    for values in immutable_values.values():
        expect(len(set(values)) == 1, "one immutable has inconsistent runtime values")
    return {
        "_comment": "GENERATED by scripts/weth10-reference.py; do not edit by hand.",
        "target": {"address": TARGET, "chainId": CHAIN_ID,
                   "deploymentTransaction": artifact.get("transactionHash"),
                   "deploymentBlock": artifact.get("receipt", {}).get("blockNumber"),
                   "deploymentBlockHash": artifact.get("receipt", {}).get("blockHash")},
        "provenance": {"repository": REPOSITORY, "deploymentCommit": DEPLOY_COMMIT,
                       "parentSourceCommit": PARENT_COMMIT, "deploymentArtifactPath": ARTIFACT_PATH,
                       "deploymentArtifactGitBlob": ARTIFACT_BLOB, "solcInputPath": SOLC_INPUT_PATH,
                       "solcInputSha256": sha256(input_bytes), "deploymentArtifactSha256": sha256(artifact_bytes),
                       "sourcePath": SOURCE_PATH, "sourceSha256": sha256(deployed_source),
                       "sourceGitBlob": git_blob(deployed_source),
                       "solcInputGitBlob": SOLC_INPUT_BLOB},
        "compiler": {"longVersion": SOLC_LONG_VERSION, "packaging": "emscripten-wasm32", "file": SOLC_FILE,
                     "manifestSha256": sha256(manifest_bytes), "binarySha256": entry.get("sha256"),
                     "binaryKeccak256": entry.get("keccak256"), "outputSha256": sha256(output_bytes),
                     "settings": standard.get("settings")},
        "runtime": {"bytes": len(one_runtime) // 2, "installedSha256": sha256(bytes.fromhex(one_runtime)),
                    "templateSha256": sha256(bytes.fromhex(template)), "templateEqualsCompilerOutput": True,
                    "templateInstalledDifferingBytes": len(differing), "immutableReferences": spans,
                    "immutableValues": {name: values[0] for name, values in sorted(immutable_values.items())},
                    "constants": {"CALLBACK_SUCCESS": "compile-time immutable from its source literal",
                                  "PERMIT_TYPEHASH": "compile-time immutable from its source literal",
                                  "deploymentChainId": "deployment-dependent immutable",
                                  "_DOMAIN_SEPARATOR": "deployment-dependent immutable"}},
        "observation": {"block": one_capture["block"], "captures": [one_capture, two_capture]},
        "abi": {"functionCount": len(functions), "receiveCount": receive, "functions": functions},
        "sourceBehavior": source_behavior,
    }


def generate(check: bool) -> None:
    expected = canonical(build())
    if check:
        try:
            actual = LOCK.read_bytes()
        except OSError as exc:
            fail(f"generated lock missing: {exc}")
        expect(actual == expected, "generated lock differs from offline-derived content")
        print(f"OK — WETH10 reference: 27 selectors + receive, {build()['runtime']['bytes']} runtime bytes, offline inputs verified")
    else:
        LOCK.write_bytes(expected)
        print(f"wrote {LOCK.relative_to(ROOT)}")


def json_rpc(url: str, request: dict[str, Any]) -> str:
    data = json.dumps(request, separators=(",", ":")).encode()
    req = urllib.request.Request(url, data=data, headers={"content-type": "application/json", "user-agent": "Blanc-WETH10-reference/1"})
    with urllib.request.urlopen(req, timeout=45) as response:
        return response.read().decode()


def get_bytes(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"user-agent": "Blanc-WETH10-reference/1"})
    with urllib.request.urlopen(request, timeout=45) as response:
        return response.read()


def git_show(repo: Path, rev_path: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(repo), "show", rev_path])


def refresh() -> None:
    with tempfile.TemporaryDirectory(prefix="weth10-reference-") as temp:
        work = Path(temp) / "WETH10"
        subprocess.run(["git", "clone", "--filter=blob:none", "--no-checkout", REPOSITORY, str(work)], check=True)
        subprocess.run(["git", "-C", str(work), "fetch", "--depth=1", "origin", DEPLOY_COMMIT, SIBLING_COMMIT, "main"], check=True)
        INPUT.mkdir(parents=True, exist_ok=True)
        SOURCE.mkdir(exist_ok=True)
        (INPUT / "deployment-artifact.json").write_bytes(git_show(work, f"{DEPLOY_COMMIT}:{ARTIFACT_PATH}"))
        (INPUT / "solc-input.json").write_bytes(git_show(work, f"{DEPLOY_COMMIT}:{SOLC_INPUT_PATH}"))
        (SOURCE / "deployed-WETH10.sol").write_bytes(git_show(work, f"{DEPLOY_COMMIT}:{SOURCE_PATH}"))
        (SOURCE / "current-main-WETH10.sol").write_bytes(git_show(work, f"origin/main:{SOURCE_PATH}"))
        (SOURCE / "current-main.diff").write_bytes(subprocess.check_output(["git", "-C", str(work), "diff", "--no-ext-diff", DEPLOY_COMMIT, "origin/main", "--", SOURCE_PATH]))
        (SOURCE / "comment-only-34d2712.diff").write_bytes(subprocess.check_output(["git", "-C", str(work), "diff", "--no-ext-diff", PARENT_COMMIT, SIBLING_COMMIT, "--", SOURCE_PATH]))
        def rev(spec: str) -> str:
            return subprocess.check_output(["git", "-C", str(work), "rev-parse", spec], text=True).strip()
        provenance = {
            "repository": REPOSITORY, "deploymentCommit": DEPLOY_COMMIT, "parentSourceCommit": PARENT_COMMIT,
            "commentOnlySiblingCommit": SIBLING_COMMIT, "deploymentArtifactPath": ARTIFACT_PATH,
            "deploymentArtifactGitBlob": rev(f"{DEPLOY_COMMIT}:{ARTIFACT_PATH}"),
            "solcInputPath": SOLC_INPUT_PATH, "solcInputGitBlob": rev(f"{DEPLOY_COMMIT}:{SOLC_INPUT_PATH}"),
            "sourcePath": SOURCE_PATH, "deploymentSourceGitBlob": rev(f"{DEPLOY_COMMIT}:{SOURCE_PATH}"),
            "currentMainCommit": rev("origin/main"),
        }
        (INPUT / "git-provenance.json").write_bytes(canonical(provenance))
        manifest = get_bytes(SOLC_LIST_URL)
        (INPUT / "solc-emscripten-wasm32-list.json").write_bytes(manifest)
        compiler = get_bytes(SOLC_BINARY_URL)
        entry = next(row for row in json.loads(manifest)["builds"] if row.get("path") == SOLC_FILE)
        expect(entry.get("longVersion") == SOLC_LONG_VERSION, "official solc manifest selected an unexpected compiler build")
        expect("0x" + sha256(compiler) == entry["sha256"] and "0x" + keccak256(compiler) == entry["keccak256"],
               "downloaded solc bytes disagree with official manifest")
        compiler_path = Path(temp) / SOLC_FILE
        compiler_path.write_bytes(compiler)
        jsc = os.environ.get("JSC", "/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc")
        driver = ('globalThis.console={log:print,warn:print,error:print,info:print,debug:print};'
                  'globalThis.Module={print:function(){},printErr:function(){}};'
                  f'load({json.dumps(str(compiler_path))});'
                  'if(typeof drainMicrotasks==="function")drainMicrotasks();'
                  'var c=Module.cwrap("solidity_compile","string",["string","number","number"]);'
                  f'print(c(read({json.dumps(str(INPUT / "solc-input.json"))}),0,0));')
        output = subprocess.check_output([jsc, "-e", driver])
        (INPUT / "solc-output.json").write_bytes(output)
        blocks: dict[str, dict[str, str]] = {}
        for name, url in RPCS.items():
            raw = json_rpc(url, {"jsonrpc": "2.0", "id": 1, "method": "eth_getBlockByNumber", "params": ["finalized", False]})
            result = json.loads(raw).get("result")
            expect(isinstance(result, dict) and isinstance(result.get("number"), str) and isinstance(result.get("hash"), str),
                   f"{name} did not return a finalized block")
            blocks[name] = {"number": result["number"], "hash": result["hash"]}
        expect(len({json.dumps(v, sort_keys=True) for v in blocks.values()}) == 1, "RPC operators disagree on finalized block")
        for name, url in RPCS.items():
            request = {"jsonrpc": "2.0", "id": 1, "method": "eth_getCode", "params": [TARGET, blocks[name]["number"]]}
            raw = json_rpc(url, request)
            envelope = {"operator": url, "request": request, "block": blocks[name], "responseRaw": raw}
            (INPUT / f"rpc-{name}.json").write_bytes(canonical(envelope))
    generate(False)


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
    except (ReferenceError, OSError, subprocess.CalledProcessError, urllib.error.URLError, KeyError, StopIteration) as exc:
        raise SystemExit(f"weth10-reference.py: {exc}")
