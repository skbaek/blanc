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
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

from weth10_reference_schema import SchemaError as LockSchemaError
from weth10_reference_schema import validate_lock_schema


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
SOURCE_BLOB = "46de31164d7ac7a9ede0ae592e86a161a58737b2"
SOLC_INPUT_HASH = "77ca555bcb549eca2b7b96e19962a69c"
SOLC_LONG_VERSION = "0.7.6+commit.7338295f"
SOLC_FILE = "solc-emscripten-wasm32-v0.7.6+commit.7338295f.js"
SOLC_LIST_URL = "https://binaries.soliditylang.org/emscripten-wasm32/list.json"
SOLC_BINARY_URL = "https://binaries.soliditylang.org/emscripten-wasm32/" + SOLC_FILE
GENERATOR_NAME = "blanc-weth10-reference"
GENERATOR_VERSION = 2
GENERATOR_IMPLEMENTATION = "scripts/weth10-reference.py"
REGENERATION_COMMAND = "python3 scripts/weth10-reference.py generate"
PINNED_SOLC_BINARY_SHA256 = "0xb94e69dfb056b3e26080f805ab43b668afbc0ac70bf124bfb7391ecfc0172ad2"
PINNED_SOLC_BINARY_KECCAK256 = "0xc68517effed7163db0c7f4559931a4c5530fe6f2a8a20596361640d9d7eff655"
PINNED_ARTIFACT_SHA256 = "79cad88e558260129b7d026ff1260aeaeab59ac41d09075b4f986251cdc781e8"
PINNED_SOLC_INPUT_SHA256 = "885b6d0d13942f2e16b36269f39a5903765194462db141c703f897d604ac9e71"
PINNED_SOURCE_SHA256 = "2bbc258e35b4174f3e358fc0cbfa5d0e8e48946649294ba91b95cb56e534c449"
PINNED_SOLC_OUTPUT_SHA256 = "bcf32583b407489299bae7534864ae578451615ccb6a9197458d8bfc003bec8e"
PINNED_TEMPLATE_SHA256 = "4a26bad255e787129bbb44842adfa09ccaff758715a50f3979c61e6f7f61d958"
PINNED_RUNTIME_SHA256 = "ca979fc12a175535a08add286497b8fc3a1805f7bcef7ae90d3dc4307ac1c25a"
PINNED_RUNTIME_CODEHASH = "0x50ea9957a23e0f53e98b5651d889eb768e72027663b99addf50898bb3a1fa5d2"
PINNED_CURRENT_MAIN_COMMIT = "87ec30256dab62459a2e6d2a1741b44d345881f1"
PINNED_CURRENT_MAIN_SOURCE_SHA256 = "7071ba8cb2bc12a7fea7f96b64bf86d0cf09822c137e174a7d8e5d27843c4af2"
PINNED_CURRENT_MAIN_SOURCE_GIT_BLOB = "f96aaaf5a1872e36546ab7af3c9ced226e91d27a"
PINNED_CURRENT_MAIN_DIFF_SHA256 = "26dc99833efd9a095a1afc89e79ba17db8abd1017798bfe64257118d1d924147"
PINNED_COMMENT_DIFF_SHA256 = "7c16db2d5733f7325aa9d842b7f7576ead55ba0fe84f33e453b0eeb44b7f4a14"
PINNED_OBSERVATION_BLOCK = {
    "number": "0x1882d8a",
    "hash": "0x6d0d8eb1b0ac3c46a2190a1af042c8d33e1215120134283ec2ef875548c7ebeb",
}
PINNED_RPC_INPUTS = {
    "publicnode": {
        "envelopeSha256": "3f5255f0158b8f7312fc64fa408575a83e53d3375c69afb9a703b7a12f458416",
        "responseSha256": "ad3fc1bbe01f2821c85657d7daae14eb7e995ffce45b414be0d3833d441d8512",
    },
    "drpc": {
        "envelopeSha256": "3a3374db0729131e491aeb77b75885dbf1b9cac1b9d64031e689efe7c7c31823",
        "responseSha256": "601cab608d019a7f96428bdf203d921527e5fcbfe5dbf063df20285835930f5b",
    },
}
EXPECTED_FUNCTION_SIGNATURES = {
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
EXPECTED_EVENT_SIGNATURES = {"Approval(address,address,uint256)", "Transfer(address,address,uint256)"}
PINNED_IMMUTABLE_REFERENCES = {
    "44": [{"length": 32, "start": 5473}, {"length": 32, "start": 6760}],
    "49": [{"length": 32, "start": 4193}, {"length": 32, "start": 8721}],
    "51": [
        {"length": 32, "start": 4237},
        {"length": 32, "start": 8473},
        {"length": 32, "start": 8823},
    ],
    "53": [{"length": 32, "start": 4290}, {"length": 32, "start": 8876}],
}
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


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def load(path: Path) -> Any:
    try:
        return strict_json(path.read_bytes(), display_path(path))
    except OSError as exc:
        fail(f"cannot read JSON {display_path(path)}: {exc}")


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


def abi_inventory(abi: Any) -> dict[str, Any]:
    expect(isinstance(abi, list), "ABI is not a list")
    functions: list[dict[str, Any]] = []
    events: list[dict[str, Any]] = []
    receives: list[dict[str, Any]] = []
    constructors: list[dict[str, Any]] = []
    for item in abi:
        expect(isinstance(item, dict) and isinstance(item.get("type"), str), "ABI entry has unknown shape")
        if item["type"] == "receive":
            expect(set(item) == {"stateMutability", "type"} and item["stateMutability"] == "payable",
                   "receive ABI entry has unknown shape")
            receives.append({"entry": item, "payable": True, "returnTypes": []})
        elif item["type"] == "constructor":
            expect(set(item) == {"inputs", "stateMutability", "type"}
                   and item["stateMutability"] == "nonpayable" and item["inputs"] == [],
                   "constructor ABI entry has unknown shape")
            constructors.append(item)
        elif item["type"] == "function":
            expect(set(item) == {"inputs", "name", "outputs", "stateMutability", "type"},
                   "function ABI entry has unknown fields")
            name, inputs, outputs = item.get("name"), item.get("inputs"), item.get("outputs")
            expect(isinstance(name, str) and isinstance(inputs, list) and isinstance(outputs, list),
                   "function ABI entry has unknown shape")
            expect(item["stateMutability"] in {"payable", "nonpayable", "view", "pure"},
                   "function ABI stateMutability is invalid")
            for arg in inputs + outputs:
                expect(isinstance(arg, dict) and set(arg) == {"internalType", "name", "type"}
                       and all(isinstance(arg[key], str) for key in arg), "ABI argument has unknown shape")
            signature = f"{name}({','.join(arg['type'] for arg in inputs)})"
            functions.append({
                "entry": item,
                "signature": signature,
                "selector": "0x" + keccak256(signature.encode())[:8],
                "payable": item["stateMutability"] == "payable",
                "returnTypes": [arg["type"] for arg in outputs],
            })
        elif item["type"] == "event":
            expect(set(item) == {"anonymous", "inputs", "name", "type"}
                   and isinstance(item["anonymous"], bool) and isinstance(item["inputs"], list)
                   and isinstance(item["name"], str), "event ABI entry has unknown shape")
            for arg in item["inputs"]:
                expect(isinstance(arg, dict) and set(arg) == {"indexed", "internalType", "name", "type"}
                       and isinstance(arg["indexed"], bool)
                       and all(isinstance(arg[key], str) for key in ("internalType", "name", "type")),
                       "event ABI argument has unknown shape")
            signature = f"{item['name']}({','.join(arg['type'] for arg in item['inputs'])})"
            events.append({"entry": item, "signature": signature,
                           "topic0": "0x" + keccak256(signature.encode())})
        else:
            fail(f"unsupported ABI entry type {item['type']!r}")
    functions.sort(key=lambda row: row["signature"])
    events.sort(key=lambda row: row["signature"])
    selectors = [row["selector"] for row in functions]
    expect(len(functions) == 27, f"expected 27 functions, found {len(functions)}")
    expect({row["signature"] for row in functions} == EXPECTED_FUNCTION_SIGNATURES,
           "ABI function signatures differ from the fixed 27-function surface")
    expect(len(set(selectors)) == len(selectors), "duplicate/colliding ABI selectors")
    expect(len(events) == 2 and {row["signature"] for row in events} == EXPECTED_EVENT_SIGNATURES,
           "ABI event definitions differ from Approval and Transfer")
    expect(len(receives) == 1, f"expected exactly one receive entry, found {len(receives)}")
    expect(len(constructors) == 1, f"expected exactly one constructor entry, found {len(constructors)}")
    payable = {row["signature"] for row in functions if row["payable"]}
    expect(payable == {"deposit()", "depositTo(address)", "depositToAndCall(address,bytes)"},
           f"unexpected payable function surface: {sorted(payable)}")
    return {
        "functionCount": len(functions), "eventCount": len(events), "receiveCount": len(receives),
        "functions": functions, "events": events, "receive": receives[0],
        "constructor": constructors[0],
    }


def rpc_runtime(path: Path, name: str) -> tuple[str, dict[str, Any]]:
    envelope_bytes = path.read_bytes()
    envelope = strict_json(envelope_bytes, f"RPC envelope {name}")
    expect(isinstance(envelope, dict), f"RPC envelope {name} has unknown shape")
    required = {"operator", "request", "block", "responseRaw"}
    expect(set(envelope) == required, f"RPC envelope {name} fields are {sorted(envelope)}")
    request, block, raw = envelope["request"], envelope["block"], envelope["responseRaw"]
    expect(isinstance(envelope["operator"], str) and envelope["operator"].startswith("https://"),
           f"RPC envelope {name} operator is invalid")
    expect(isinstance(request, dict) and set(request) == {"jsonrpc", "id", "method", "params"}
           and request.get("jsonrpc") == "2.0" and request.get("id") == 1
           and request.get("method") == "eth_getCode" and isinstance(request.get("params"), list),
           f"RPC envelope {name} request is invalid")
    expect(request["params"] == [TARGET, block.get("number")], f"RPC envelope {name} request parameters differ")
    expect(isinstance(block, dict) and set(block) == {"number", "hash"} and isinstance(raw, str),
           f"RPC envelope {name} block/raw fields are invalid")
    parsed = strict_json(raw, f"RPC envelope {name} raw response")
    expect(isinstance(parsed, dict) and set(parsed) == {"jsonrpc", "id", "result"}
           and parsed.get("jsonrpc") == "2.0" and parsed.get("id") == 1,
           f"RPC envelope {name} raw response has unknown shape")
    runtime = hex_body(parsed.get("result"), f"RPC envelope {name} result")
    capture = {
        "name": name, "operator": envelope["operator"],
        "operatorDomain": urllib.parse.urlparse(envelope["operator"]).netloc,
        "request": request, "block": block,
        "envelopeSha256": sha256(envelope_bytes), "responseSha256": sha256(raw.encode()),
        "runtimeSha256": sha256(bytes.fromhex(runtime)),
        "runtimeCodehash": "0x" + keccak256(bytes.fromhex(runtime)),
    }
    expect(envelope["operator"] == RPCS[name], f"RPC envelope {name} operator differs from pinned operator")
    expect(block == PINNED_OBSERVATION_BLOCK, f"RPC envelope {name} observation block differs from pinned block")
    expect({key: capture[key] for key in ("envelopeSha256", "responseSha256")} == PINNED_RPC_INPUTS[name],
           f"RPC envelope {name} digest differs from pinned acquisition evidence")
    return runtime, capture


def check_drift_inputs(deployed_source: bytes) -> None:
    """Keep Step 2's source evidence available and recognisably complete.

    These files deliberately do not feed the normative target JSON: current
    main is drift evidence, not a second source of target identity.
    """
    current = (SOURCE / "current-main-WETH10.sol").read_bytes()
    current_diff_bytes = (SOURCE / "current-main.diff").read_bytes()
    comment_diff_bytes = (SOURCE / "comment-only-34d2712.diff").read_bytes()
    current_diff = current_diff_bytes.decode()
    comment_diff = comment_diff_bytes.decode()
    provenance = load(SOURCE / "drift-provenance.json")
    expect(provenance == {
        "currentMainCommit": PINNED_CURRENT_MAIN_COMMIT,
        "currentMainSourceGitBlob": PINNED_CURRENT_MAIN_SOURCE_GIT_BLOB,
        "currentMainSourceSha256": PINNED_CURRENT_MAIN_SOURCE_SHA256,
        "currentMainDiffSha256": PINNED_CURRENT_MAIN_DIFF_SHA256,
        "commentOnlySiblingCommit": SIBLING_COMMIT,
        "commentOnlyDiffSha256": PINNED_COMMENT_DIFF_SHA256,
    }, "drift provenance has missing, unknown, or unexpected fields")
    expect(sha256(current) == PINNED_CURRENT_MAIN_SOURCE_SHA256
           and git_blob(current) == PINNED_CURRENT_MAIN_SOURCE_GIT_BLOB
           and sha256(current_diff_bytes) == PINNED_CURRENT_MAIN_DIFF_SHA256
           and sha256(comment_diff_bytes) == PINNED_COMMENT_DIFF_SHA256,
           "drift/corroboration bytes differ from their pinned evidence")
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


def callback_inventory(standard: dict[str, Any], deployed_source: str) -> list[dict[str, Any]]:
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
        inputs: list[dict[str, str]] = []
        for parameter in split_top_level(parameters):
            tokens = [token for token in parameter.split() if token not in {"calldata", "memory", "storage", "payable"}]
            expect(len(tokens) >= 1, f"callback parameter {parameter!r} has an unexpected shape")
            kind = tokens[0]
            inputs.append({"name": tokens[1] if len(tokens) > 1 else "",
                           "type": "uint256" if kind == "uint" else kind})
        return_kind = returns.split()[0]
        outputs = [{"name": returns.split()[1] if len(returns.split()) > 1 else "",
                    "type": "uint256" if return_kind == "uint" else return_kind}]
        abi_signature = f"{method}({','.join(item['type'] for item in inputs)})"
        rows.append({
            "interface": interface,
            "method": method,
            "sourceSignature": f"{method}({parameters}) external returns ({returns})",
            "abiSignature": abi_signature,
            "selector": "0x" + keccak256(abi_signature.encode())[:8],
            "inputs": inputs,
            "outputs": outputs,
        })
    return rows


def source_slice(source: str, node: dict[str, Any], what: str) -> tuple[int, int, str]:
    src = node.get("src")
    expect(isinstance(src, str) and re.fullmatch(r"\d+:\d+:\d+", src) is not None,
           f"{what} has no exact source span")
    start, length, file_index = (int(part) for part in src.split(":"))
    expect(file_index == 0, f"{what} is not in the deployed WETH10 source")
    data = source.encode()
    expect(0 <= start <= start + length <= len(data), f"{what} source span is out of bounds")
    return start, length, data[start:start + length].decode()


def ast_guard_inventory(output: dict[str, Any], source: str) -> dict[str, list[dict[str, Any]]]:
    ast = output.get("sources", {}).get(SOURCE_PATH, {}).get("ast")
    contracts = [node for node in walk_nodes(ast)
                 if node.get("nodeType") == "ContractDefinition" and node.get("name") == "WETH10"]
    expect(len(contracts) == 1, "compiler AST does not contain exactly one WETH10 contract")
    definitions = {
        node.get("name"): node for node in contracts[0].get("nodes", [])
        if node.get("nodeType") == "FunctionDefinition" and node.get("kind") == "function"
    }

    def collect(value: Any, branches: list[dict[str, str]], sites: list[dict[str, Any]]) -> None:
        if isinstance(value, list):
            for item in value:
                collect(item, branches, sites)
            return
        if not isinstance(value, dict):
            return
        if value.get("nodeType") == "IfStatement":
            condition = value.get("condition")
            _, _, condition_source = source_slice(source, condition, "if condition")
            collect(condition, branches, sites)
            collect(value.get("trueBody"), branches + [{
                "condition": normalise_source(condition_source), "branch": "then"}], sites)
            if value.get("falseBody") is not None:
                collect(value.get("falseBody"), branches + [{
                    "condition": normalise_source(condition_source), "branch": "else"}], sites)
            return
        if value.get("nodeType") == "FunctionCall" \
                and value.get("expression", {}).get("name") == "require":
            arguments = value.get("arguments")
            expect(isinstance(arguments, list) and len(arguments) == 2,
                   "require AST node has an unexpected argument shape")
            start, length, _ = source_slice(source, value, "require call")
            _, _, condition = source_slice(source, arguments[0], "require condition")
            reason = arguments[1].get("value")
            expect(arguments[1].get("nodeType") == "Literal" and isinstance(reason, str),
                   "require reason is not an exact source literal")
            sites.append({
                "sourceStart": start, "sourceLength": length,
                "enclosingBranches": branches,
                "condition": normalise_source(condition), "reason": reason,
            })
            return
        for child in value.values():
            collect(child, branches, sites)

    result: dict[str, list[dict[str, Any]]] = {}
    for name, definition in definitions.items():
        sites: list[dict[str, Any]] = []
        collect(definition.get("body"), [], sites)
        sites.sort(key=lambda row: row["sourceStart"])
        result[name] = sites
    return result


def source_behavior_inventory(
        standard: dict[str, Any], output: dict[str, Any], abi: dict[str, Any]) -> dict[str, Any]:
    """Generate the source-side facts Step 2 must not rediscover by prose."""
    deployed_source = standard.get("sources", {}).get(SOURCE_PATH, {}).get("content")
    expect(isinstance(deployed_source, str), "standard input has no deployed WETH10 source")
    functions = abi["functions"]
    guards_by_name = ast_guard_inventory(output, deployed_source)
    generated_getters = {
        "CALLBACK_SUCCESS", "PERMIT_TYPEHASH", "allowance", "balanceOf", "decimals",
        "deploymentChainId", "flashMinted", "name", "nonces", "symbol",
    }
    guards: list[dict[str, Any]] = []
    reasons: list[str] = []
    for row in functions:
        name = row["signature"].split("(", 1)[0]
        if name in guards_by_name:
            ordered = guards_by_name[name]
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
    for row in abi["events"]:
        item = row["entry"]
        checked_inputs = [
            {"name": argument["name"], "type": argument["type"], "indexed": argument["indexed"]}
            for argument in item["inputs"]
        ]
        events.append({"name": item["name"], "signature": row["signature"],
                       "topic0": row["topic0"], "anonymous": item["anonymous"],
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


def walk_nodes(value: Any):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk_nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk_nodes(child)


def source_digest_inventory(standard: dict[str, Any], metadata: dict[str, Any]) -> list[dict[str, str]]:
    sources = standard.get("sources")
    expect(isinstance(sources, dict) and sources, "standard input has no source contents")
    rows: list[dict[str, str]] = []
    contents: dict[str, bytes] = {}
    for path, item in sorted(sources.items()):
        expect(isinstance(path, str) and isinstance(item, dict) and set(item) == {"content"}
               and isinstance(item["content"], str), f"standard-input source {path!r} has unknown shape")
        data = item["content"].encode()
        contents[path] = data
        rows.append({"path": path, "sha256": sha256(data), "keccak256": "0x" + keccak256(data)})
    metadata_sources = metadata.get("sources")
    expect(isinstance(metadata_sources, dict) and metadata_sources,
           "WETH10 compiler metadata has no source inventory")
    for path, item in metadata_sources.items():
        expect(path in contents and isinstance(item, dict) and item.get("content", "").encode() == contents[path]
               and item.get("keccak256") == "0x" + keccak256(contents[path]),
               f"compiler metadata source digest/content differs for {path}")
    return rows


def source_string_literal(source: str, pattern: str, what: str) -> str:
    matches = re.findall(pattern, source, re.S)
    expect(len(matches) == 1, f"deployed source has {len(matches)} candidates for {what}")
    try:
        value = json.loads(matches[0])
    except json.JSONDecodeError as exc:
        fail(f"deployed source {what} is not a supported UTF-8 string literal: {exc}")
    expect(isinstance(value, str), f"deployed source {what} is not a string")
    return value


def immutable_constant_inventory(source: str, immutable_values: dict[str, str]) -> dict[str, Any]:
    preimages: dict[str, str] = {}
    for name in ("CALLBACK_SUCCESS", "PERMIT_TYPEHASH"):
        preimages[name] = source_string_literal(
            source,
            rf"bytes32\s+public\s+immutable\s+{name}\s*=\s*keccak256\s*\(\s*(\"(?:\\.|[^\"])*\")\s*\)\s*;",
            f"{name} preimage",
        )
        derived = "0x" + keccak256(preimages[name].encode())
        expect(derived == immutable_values[name], f"{name} source preimage does not derive its installed immutable")

    contract_name = source_string_literal(
        source, r"string\s+public\s+constant\s+name\s*=\s*(\"(?:\\.|[^\"])*\")\s*;", "name constant")
    domain_type = source_string_literal(
        source, r"keccak256\s*\(\s*(\"EIP712Domain\((?:\\.|[^\"])*\)\")\s*\)", "domain type")
    domain_version = source_string_literal(
        source, r"keccak256\s*\(\s*bytes\s*\(\s*(\"(?:\\.|[^\"])*\")\s*\)\s*\)", "domain version")
    chain_id = int(CHAIN_ID, 16)
    address = bytes.fromhex(hex_body(TARGET, "target address"))
    expect(len(address) == 20, "target address is not 20 bytes")
    encoded_domain = b"".join([
        bytes.fromhex(keccak256(domain_type.encode())),
        bytes.fromhex(keccak256(contract_name.encode())),
        bytes.fromhex(keccak256(domain_version.encode())),
        chain_id.to_bytes(32, "big"),
        address.rjust(32, b"\0"),
    ])
    domain_separator = "0x" + keccak256(encoded_domain)
    chain_word = "0x" + chain_id.to_bytes(32, "big").hex()
    expect(immutable_values["deploymentChainId"] == chain_word,
           "installed deploymentChainId does not equal the observed deployment chain")
    expect(immutable_values["_DOMAIN_SEPARATOR"] == domain_separator,
           "installed _DOMAIN_SEPARATOR does not equal the deployed EIP-712 formula")
    return {
        "CALLBACK_SUCCESS": {
            "classification": "compileTimeKeccakUtf8", "preimage": preimages["CALLBACK_SUCCESS"],
            "value": immutable_values["CALLBACK_SUCCESS"],
        },
        "PERMIT_TYPEHASH": {
            "classification": "compileTimeKeccakUtf8", "preimage": preimages["PERMIT_TYPEHASH"],
            "value": immutable_values["PERMIT_TYPEHASH"],
        },
        "deploymentChainId": {
            "classification": "deploymentDependent", "derivation": "constructor chainid()",
            "value": immutable_values["deploymentChainId"],
        },
        "_DOMAIN_SEPARATOR": {
            "classification": "deploymentDependent",
            "derivation": "keccak256(abi.encode(domainTypeHash,nameHash,versionHash,chainId,address(this)))",
            "inputs": {
                "domainType": domain_type, "name": contract_name, "version": domain_version,
                "chainId": CHAIN_ID, "verifyingContract": TARGET,
            },
            "value": immutable_values["_DOMAIN_SEPARATOR"],
        },
    }


def lvalue_state_declarations(value: Any) -> set[int]:
    """Return state-declaration ids at the root of an assignment lvalue."""
    if not isinstance(value, dict):
        return set()
    node_type = value.get("nodeType")
    if node_type == "Identifier":
        declaration = value.get("referencedDeclaration")
        return {declaration} if isinstance(declaration, int) else set()
    if node_type in {"IndexAccess", "MemberAccess"}:
        key = "baseExpression" if node_type == "IndexAccess" else "expression"
        return lvalue_state_declarations(value.get(key))
    if node_type == "TupleExpression":
        return set().union(*(lvalue_state_declarations(item)
                             for item in value.get("components", []) if item is not None))
    return set()


def deployment_inventory(
        output: dict[str, Any], abi: dict[str, Any], artifact: dict[str, Any],
        constants: dict[str, Any]) -> dict[str, Any]:
    ast = output.get("sources", {}).get(SOURCE_PATH, {}).get("ast")
    contracts = [node for node in walk_nodes(ast)
                 if node.get("nodeType") == "ContractDefinition" and node.get("name") == "WETH10"]
    expect(len(contracts) == 1, "compiler AST does not contain exactly one WETH10 contract")
    contract = contracts[0]
    constructors = [node for node in contract.get("nodes", [])
                    if node.get("nodeType") == "FunctionDefinition" and node.get("kind") == "constructor"]
    expect(len(constructors) == 1, "compiler AST does not contain exactly one WETH10 constructor")
    constructor = constructors[0]
    parameters = constructor.get("parameters", {}).get("parameters")
    expect(constructor.get("stateMutability") == "nonpayable" and parameters == [],
           "constructor AST shape is not zero-argument nonpayable")
    body = constructor.get("body")
    constructor_nodes = list(walk_nodes(body))
    internal_calls = {
        node.get("expression", {}).get("name") for node in constructor_nodes
        if node.get("nodeType") == "FunctionCall"
        and "t_function_internal" in node.get("expression", {}).get("typeDescriptions", {}).get("typeIdentifier", "")
    }
    helpers = {
        node.get("name"): node for node in contract.get("nodes", [])
        if node.get("nodeType") == "FunctionDefinition" and node.get("kind") == "function"
    }
    expect(internal_calls == {"_calculateDomainSeparator"} and internal_calls <= set(helpers),
           f"constructor internal-call inventory differs: {sorted(internal_calls)}")
    nodes = constructor_nodes + [child for name in sorted(internal_calls)
                                 for child in walk_nodes(helpers[name].get("body"))]
    expect(sum(node.get("nodeType") == "YulFunctionCall"
               and node.get("functionName", {}).get("name") == "chainid" for node in nodes) == 1,
           "constructor does not derive deploymentChainId from one chainid() operation")
    emit_nodes = [node for node in nodes if node.get("nodeType") == "EmitStatement"]
    external_calls: list[str] = []
    for node in nodes:
        if node.get("nodeType") == "NewExpression":
            external_calls.append("contract creation")
        if node.get("nodeType") != "FunctionCall":
            continue
        expression = node.get("expression", {})
        type_identifier = expression.get("typeDescriptions", {}).get("typeIdentifier", "")
        member = expression.get("memberName")
        if "external" in type_identifier or "barecall" in type_identifier or member in {
                "call", "delegatecall", "staticcall", "send", "transfer"}:
            external_calls.append(member or type_identifier)
    state_variables = {
        node.get("id"): node.get("name") for node in contract.get("nodes", [])
        if node.get("nodeType") == "VariableDeclaration" and node.get("stateVariable") is True
    }
    logical_types = {
        "balanceOf": "t_mapping$_t_address_$_t_uint256_$",
        "nonces": "t_mapping$_t_address_$_t_uint256_$",
        "allowance": "t_mapping$_t_address_$_t_mapping$_t_address_$_t_uint256_$_$",
        "flashMinted": "t_uint256",
    }
    logical_declarations = {
        node.get("name"): node for node in contract.get("nodes", [])
        if node.get("nodeType") == "VariableDeclaration" and node.get("name") in logical_types
    }
    expect(set(logical_declarations) == set(logical_types),
           "logical state declarations are missing from the WETH10 AST")
    for name, type_identifier in logical_types.items():
        declaration = logical_declarations[name]
        expect(declaration.get("stateVariable") is True
               and declaration.get("constant") is False
               and declaration.get("mutability") == "mutable"
               and declaration.get("value") is None
               and declaration.get("typeName", {}).get("typeDescriptions", {}).get("typeIdentifier")
               == type_identifier,
               f"logical state declaration {name} is initialized or has an unexpected AST shape")
    state_writes: list[str] = []
    for node in nodes:
        declarations: set[int] = set()
        if node.get("nodeType") == "Assignment":
            declarations = lvalue_state_declarations(node.get("leftHandSide"))
        elif node.get("nodeType") == "UnaryOperation" and node.get("operator") in {"++", "--", "delete"}:
            declarations = lvalue_state_declarations(node.get("subExpression"))
        state_writes.extend(state_variables[declaration]
                            for declaration in sorted(declarations) if declaration in state_variables)
    expect(not any(node.get("nodeType") == "YulFunctionCall"
                   and node.get("functionName", {}).get("name") == "sstore" for node in nodes),
           "constructor contains an unanalyzed inline-assembly storage write")
    expect(not external_calls and not emit_nodes, "constructor unexpectedly performs an external call or emits a log")
    expect(state_writes == ["deploymentChainId", "_DOMAIN_SEPARATOR"],
           f"constructor state-write inventory differs: {state_writes}")
    expect(not set(logical_types) & set(state_writes),
           "constructor writes a logical state variable that was expected to remain initially empty")
    expect(artifact.get("args") == [], "deployment artifact has constructor arguments")
    return {
        "constructor": {
            "entry": abi["constructor"], "arguments": artifact["args"], "payable": False,
            "rejectsNonzeroEndowment": True,
        },
        "externalCalls": external_calls,
        "logs": [],
        "stateWrites": state_writes,
        "initialLogicalState": {"balances": {}, "allowances": {}, "nonces": {},
                                "flashMinted": "0x" + "00" * 32},
        "initializes": {
            "deploymentChainId": {
                "derivation": constants["deploymentChainId"]["derivation"],
                "installedValue": constants["deploymentChainId"]["value"],
            },
            "_DOMAIN_SEPARATOR": {
                "derivation": constants["_DOMAIN_SEPARATOR"]["derivation"],
                "inputs": constants["_DOMAIN_SEPARATOR"]["inputs"],
                "installedValue": constants["_DOMAIN_SEPARATOR"]["value"],
            },
        },
    }


def build() -> dict[str, Any]:
    artifact_bytes = (INPUT / "deployment-artifact.json").read_bytes()
    input_bytes = (INPUT / "solc-input.json").read_bytes()
    output_bytes = (INPUT / "solc-output.json").read_bytes()
    manifest_bytes = (INPUT / "solc-emscripten-wasm32-list.json").read_bytes()
    artifact = strict_json(artifact_bytes, "deployment artifact")
    standard = strict_json(input_bytes, "standard input")
    output = strict_json(output_bytes, "compiler output")
    manifest = strict_json(manifest_bytes, "compiler release manifest")
    git_provenance = load(INPUT / "git-provenance.json")
    expect(git_provenance == {
        "repository": REPOSITORY, "deploymentCommit": DEPLOY_COMMIT, "parentSourceCommit": PARENT_COMMIT,
        "deploymentArtifactPath": ARTIFACT_PATH,
        "deploymentArtifactGitBlob": ARTIFACT_BLOB, "solcInputPath": SOLC_INPUT_PATH,
        "solcInputGitBlob": SOLC_INPUT_BLOB, "sourcePath": SOURCE_PATH,
        "deploymentSourceGitBlob": SOURCE_BLOB, "parentSourceGitBlob": SOURCE_BLOB},
        "Git provenance has missing, unknown, or unexpected target fields")
    expect(git_blob(artifact_bytes) == ARTIFACT_BLOB, "deployment artifact Git blob identity differs")
    expect(git_blob(input_bytes) == SOLC_INPUT_BLOB, "standard-input Git blob identity differs")
    expect(sha256(artifact_bytes) == PINNED_ARTIFACT_SHA256
           and sha256(input_bytes) == PINNED_SOLC_INPUT_SHA256,
           "deployment artifact or standard input digest differs from its pin")
    expect(sha256(output_bytes) == PINNED_SOLC_OUTPUT_SHA256,
           "compiler-output digest differs from independently pinned target output")
    expect(artifact.get("address") == TARGET and artifact.get("solcInputHash") == SOLC_INPUT_HASH,
           "deployment artifact target identity differs")
    # Hardhat's deployment artifact calls this truncated identifier
    # ``solcInputHash``; it is the source filename/record key, not a SHA-256
    # digest of the JSON bytes.  Pin both representations independently.
    expect(artifact.get("solcInputHash") == Path(SOLC_INPUT_PATH).stem == SOLC_INPUT_HASH,
           "artifact solcInputHash differs from the pinned standard-input record")
    deployed_source = (SOURCE / "deployed-WETH10.sol").read_bytes()
    expect(git_blob(deployed_source) == SOURCE_BLOB and sha256(deployed_source) == PINNED_SOURCE_SHA256,
           "deployed source Git blob/SHA-256 differs from independently pinned source")
    embedded = standard.get("sources", {}).get(SOURCE_PATH, {}).get("content")
    expect(isinstance(embedded, str) and embedded.encode() == deployed_source,
           "vendored deployment source does not equal standard-input source")
    trailing_lf_bytes = len(deployed_source) - len(deployed_source.rstrip(b"\n"))
    expect(trailing_lf_bytes == 1, "deployed source terminal-newline shape differs")
    c = contract_output(output)
    errors = [row for row in output.get("errors", []) if row.get("severity") == "error"]
    expect(not errors, "vendored compiler output reports errors")
    expect(artifact.get("abi") == c.get("abi"), "deployment artifact ABI differs from exact compiler output")
    expect(artifact.get("storageLayout") == c.get("storageLayout"),
           "deployment artifact storage layout differs from exact compiler output")
    expect(artifact.get("metadata") == c.get("metadata"),
           "deployment artifact metadata differs from exact compiler output")
    metadata = strict_json(c.get("metadata"), "WETH10 compiler metadata")
    expect(metadata.get("compiler", {}).get("version") == SOLC_LONG_VERSION,
           "compiler metadata version differs from pinned compiler")
    expect(metadata.get("language") == standard.get("language") == "Solidity",
           "compiler input/metadata language differs")
    source_digests = source_digest_inventory(standard, metadata)
    template = hex_body(artifact.get("deployedBytecode"), "artifact deployedBytecode")
    output_template = hex_body("0x" + str(c.get("evm", {}).get("deployedBytecode", {}).get("object", "")),
                               "compiler deployedBytecode")
    expect(template == output_template, "artifact deployedBytecode does not exactly equal compiler template")
    template_sha256 = sha256(bytes.fromhex(template))
    expect(template_sha256 == PINNED_TEMPLATE_SHA256,
           "deployed-bytecode template digest differs from independently pinned template")
    immutables = c["evm"]["deployedBytecode"].get("immutableReferences")
    expect(immutables == PINNED_IMMUTABLE_REFERENCES,
           "compiler immutableReferences differ from the independently pinned exact inventory")
    names = immutable_names(output)
    spans: list[dict[str, Any]] = []
    for key, entries in immutables.items():
        expect(key in names and isinstance(entries, list), "unknown immutable-reference shape")
        for entry in entries:
            expect(isinstance(entry, dict) and set(entry) == {"start", "length"} and entry["length"] == 32,
                   "unknown immutable span")
            spans.append({"astId": key, "name": names[key], "start": entry["start"], "length": entry["length"]})
    spans.sort(key=lambda row: (row["start"], row["name"]))
    covered = {i for row in spans for i in range(row["start"], row["start"] + row["length"])}
    expect(len(covered) == sum(row["length"] for row in spans), "overlapping immutable spans")
    one_runtime, one_capture = rpc_runtime(INPUT / "rpc-publicnode.json", "publicnode")
    two_runtime, two_capture = rpc_runtime(INPUT / "rpc-drpc.json", "drpc")
    expect(one_runtime == two_runtime, "vendored RPC captures disagree on installed runtime")
    expect(one_capture["block"] == two_capture["block"], "vendored RPC captures disagree on observation block")
    expect(one_capture["block"]["number"] != "0x0" and len(one_capture["block"]["hash"]) == 66,
           "RPC observation block is invalid")
    expect(len(template) == len(one_runtime), "template and installed runtime lengths differ")
    differing = [i for i in range(len(template) // 2) if template[2*i:2*i+2] != one_runtime[2*i:2*i+2]]
    expect(set(differing) <= covered, "installed runtime differs outside compiler immutable spans")
    runtime_bytes = bytes.fromhex(one_runtime)
    runtime_sha256 = sha256(runtime_bytes)
    runtime_codehash = "0x" + keccak256(runtime_bytes)
    expect(runtime_sha256 == PINNED_RUNTIME_SHA256 and runtime_codehash == PINNED_RUNTIME_CODEHASH,
           "installed runtime digest/codehash differs from independently pinned deployed runtime")
    abi = abi_inventory(c.get("abi"))
    source_behavior = source_behavior_inventory(standard, output, abi)
    methods = c.get("evm", {}).get("methodIdentifiers")
    expect(isinstance(methods, dict), "compiler output has no method identifiers")
    expect({row["signature"]: row["selector"][2:] for row in abi["functions"]} == methods,
           "ABI-recomputed selectors differ from compiler method identifiers")
    entry = next((row for row in manifest.get("builds", []) if row.get("path") == SOLC_FILE), None)
    expect(isinstance(entry, dict) and entry.get("longVersion") == SOLC_LONG_VERSION,
           "solc release manifest lacks the pinned compiler build")
    expect(entry.get("sha256") == PINNED_SOLC_BINARY_SHA256
           and entry.get("keccak256") == PINNED_SOLC_BINARY_KECCAK256,
           "solc release entry differs from independently pinned compiler binary digests")
    immutable_values: dict[str, list[str]] = {}
    for row in spans:
        value = one_runtime[2*row["start"]:2*(row["start"] + row["length"])]
        immutable_values.setdefault(row["name"], []).append("0x" + value)
    for values in immutable_values.values():
        expect(len(set(values)) == 1, "one immutable has inconsistent runtime values")
    installed_immutables = {name: values[0] for name, values in sorted(immutable_values.items())}
    expect(set(installed_immutables) == {"CALLBACK_SUCCESS", "PERMIT_TYPEHASH", "deploymentChainId",
                                        "_DOMAIN_SEPARATOR"}, "installed immutable value inventory differs")
    constants = immutable_constant_inventory(embedded, installed_immutables)
    deployment = deployment_inventory(output, abi, artifact, constants)
    receipt = artifact.get("receipt")
    expect(isinstance(receipt, dict) and receipt.get("transactionHash") == artifact.get("transactionHash")
           and receipt.get("logs") == [] and receipt.get("status") == 1
           and receipt.get("contractAddress") is None
           and receipt.get("to") == "0x4e59b44847b379578588920cA78FbF26c0B4956C"
           and receipt.get("blockNumber") == 11954957
           and receipt.get("blockHash")
           == "0x3a97e20c1794a8cc92ca963695f4a80b70149b8cbfe003f28f541b8b03b662f5",
           "deployment receipt has unexpected identity/status/log shape")
    return {
        "_comment": "GENERATED by scripts/weth10-reference.py; do not edit by hand.",
        "generator": {
            "name": GENERATOR_NAME, "version": GENERATOR_VERSION,
            "implementation": GENERATOR_IMPLEMENTATION, "regenerationCommand": REGENERATION_COMMAND,
        },
        "target": {"address": TARGET, "chainId": CHAIN_ID,
                   "deploymentTransaction": artifact.get("transactionHash"),
                   "deploymentBlock": receipt["blockNumber"],
                   "deploymentBlockHash": receipt["blockHash"]},
        "provenance": {"repository": REPOSITORY, "deploymentCommit": DEPLOY_COMMIT,
                       "parentSourceCommit": PARENT_COMMIT, "parentSourceGitBlob": SOURCE_BLOB,
                       "deploymentArtifactPath": ARTIFACT_PATH,
                       "deploymentArtifactGitBlob": ARTIFACT_BLOB,
                       "solcInputPath": SOLC_INPUT_PATH, "solcInputHash": SOLC_INPUT_HASH,
                       "solcInputSha256": sha256(input_bytes), "deploymentArtifactSha256": sha256(artifact_bytes),
                       "sourcePath": SOURCE_PATH, "sourceSha256": sha256(deployed_source),
                       "sourceGitBlob": git_blob(deployed_source), "sourceTrailingLfBytes": trailing_lf_bytes,
                       "solcInputGitBlob": SOLC_INPUT_BLOB, "sourceDigests": source_digests,
                       "relations": {
                           "sourceSnapshotEqualsStandardInput": True,
                           "artifactAbiEqualsCompilerOutput": True,
                           "artifactMetadataEqualsCompilerOutput": True,
                           "artifactStorageLayoutEqualsCompilerOutput": True,
                       }},
        "compiler": {"longVersion": SOLC_LONG_VERSION, "packaging": "emscripten-wasm32", "file": SOLC_FILE,
                     "manifestSha256": sha256(manifest_bytes), "binarySha256": entry.get("sha256"),
                     "binaryKeccak256": entry.get("keccak256"), "outputSha256": sha256(output_bytes),
                     "inputLanguage": standard.get("language"), "settings": standard.get("settings"),
                     "metadataSettings": metadata.get("settings"), "releaseManifestEntry": entry},
        "runtime": {"installedHex": "0x" + one_runtime, "byteLength": len(runtime_bytes),
                    "installedSha256": runtime_sha256, "installedCodehash": runtime_codehash,
                    "templateSha256": template_sha256, "templateEqualsCompilerOutput": True,
                    "templateInstalledSameLength": True,
                    "templateInstalledAgreeOutsideImmutableReferences": True,
                    "templateInstalledDifferingBytes": len(differing),
                    "immutableReferences": immutables, "immutableReferenceSpans": spans,
                    "immutableValues": installed_immutables, "constants": constants},
        "observation": {"block": one_capture["block"], "captures": [one_capture, two_capture]},
        "abi": {key: value for key, value in abi.items() if key != "constructor"},
        "deployment": deployment,
        "sourceBehavior": source_behavior,
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
        parsed = strict_json(actual, "generated lock")
        try:
            validate_lock_schema(parsed, "committed generated lock")
        except LockSchemaError as exc:
            fail(f"committed generated lock violates independent schema: {exc}")
        expect(actual == canonical(parsed), "generated lock is not canonical JSON")
        expect(parsed == built and actual == expected, "generated lock differs from offline-derived content")
        print(f"OK — WETH10 reference: 27 selectors + receive, {built['runtime']['byteLength']} runtime bytes, offline inputs verified")
    else:
        LOCK.write_bytes(expected)
        print(f"wrote {display_path(LOCK)}")


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
    """Re-acquire into a staging tree and publish only an exactly validated lock.

    The installed-runtime observation is intentionally re-read at the pinned
    block.  Current finalized heads are used only to prove that block is final;
    advancing finality must not silently move the target lock.
    """
    with tempfile.TemporaryDirectory(prefix="weth10-reference-") as temp:
        temp_root = Path(temp)
        work = temp_root / "WETH10"
        staged_ref = temp_root / "reference" / "weth10"
        staged_input = staged_ref / "inputs"
        staged_source = staged_input / "source"
        staged_lock = temp_root / "weth10-reference.json"
        staged_source.mkdir(parents=True)
        subprocess.run(["git", "clone", "--filter=blob:none", "--no-checkout", REPOSITORY, str(work)], check=True)
        subprocess.run(["git", "-C", str(work), "fetch", "--depth=1", "origin",
                        DEPLOY_COMMIT, PARENT_COMMIT, SIBLING_COMMIT, PINNED_CURRENT_MAIN_COMMIT], check=True)
        (staged_input / "deployment-artifact.json").write_bytes(
            git_show(work, f"{DEPLOY_COMMIT}:{ARTIFACT_PATH}"))
        (staged_input / "solc-input.json").write_bytes(git_show(work, f"{DEPLOY_COMMIT}:{SOLC_INPUT_PATH}"))
        (staged_source / "deployed-WETH10.sol").write_bytes(git_show(work, f"{DEPLOY_COMMIT}:{SOURCE_PATH}"))
        (staged_source / "current-main-WETH10.sol").write_bytes(
            git_show(work, f"{PINNED_CURRENT_MAIN_COMMIT}:{SOURCE_PATH}"))
        (staged_source / "current-main.diff").write_bytes(subprocess.check_output([
            "git", "-C", str(work), "diff", "--no-ext-diff", DEPLOY_COMMIT,
            PINNED_CURRENT_MAIN_COMMIT, "--", SOURCE_PATH]))
        (staged_source / "comment-only-34d2712.diff").write_bytes(subprocess.check_output([
            "git", "-C", str(work), "diff", "--no-ext-diff", PARENT_COMMIT,
            SIBLING_COMMIT, "--", SOURCE_PATH]))
        def rev(spec: str) -> str:
            return subprocess.check_output(["git", "-C", str(work), "rev-parse", spec], text=True).strip()
        parent_source_blob = rev(f"{PARENT_COMMIT}:{SOURCE_PATH}")
        expect(parent_source_blob == rev(f"{DEPLOY_COMMIT}:{SOURCE_PATH}") == SOURCE_BLOB,
               "parent/deployment source Git blobs differ from the pinned source relation")
        provenance = {
            "repository": REPOSITORY, "deploymentCommit": DEPLOY_COMMIT, "parentSourceCommit": PARENT_COMMIT,
            "parentSourceGitBlob": parent_source_blob,
            "deploymentArtifactPath": ARTIFACT_PATH,
            "deploymentArtifactGitBlob": rev(f"{DEPLOY_COMMIT}:{ARTIFACT_PATH}"),
            "solcInputPath": SOLC_INPUT_PATH, "solcInputGitBlob": rev(f"{DEPLOY_COMMIT}:{SOLC_INPUT_PATH}"),
            "sourcePath": SOURCE_PATH, "deploymentSourceGitBlob": rev(f"{DEPLOY_COMMIT}:{SOURCE_PATH}"),
        }
        (staged_input / "git-provenance.json").write_bytes(canonical(provenance))
        current_source = (staged_source / "current-main-WETH10.sol").read_bytes()
        current_diff = (staged_source / "current-main.diff").read_bytes()
        comment_diff = (staged_source / "comment-only-34d2712.diff").read_bytes()
        drift_provenance = {
            "currentMainCommit": rev(PINNED_CURRENT_MAIN_COMMIT),
            "currentMainSourceGitBlob": git_blob(current_source),
            "currentMainSourceSha256": sha256(current_source),
            "currentMainDiffSha256": sha256(current_diff),
            "commentOnlySiblingCommit": SIBLING_COMMIT,
            "commentOnlyDiffSha256": sha256(comment_diff),
        }
        (staged_source / "drift-provenance.json").write_bytes(canonical(drift_provenance))
        manifest = get_bytes(SOLC_LIST_URL)
        (staged_input / "solc-emscripten-wasm32-list.json").write_bytes(manifest)
        compiler = get_bytes(SOLC_BINARY_URL)
        entry = next((row for row in strict_json(manifest, "downloaded compiler manifest")["builds"]
                      if row.get("path") == SOLC_FILE), None)
        expect(isinstance(entry, dict) and entry.get("longVersion") == SOLC_LONG_VERSION,
               "official solc manifest selected an unexpected compiler build")
        expect(entry.get("sha256") == PINNED_SOLC_BINARY_SHA256
               and entry.get("keccak256") == PINNED_SOLC_BINARY_KECCAK256,
               "official solc manifest selected release differs from independent compiler pins")
        expect("0x" + sha256(compiler) == PINNED_SOLC_BINARY_SHA256
               and "0x" + keccak256(compiler) == PINNED_SOLC_BINARY_KECCAK256,
               "downloaded solc bytes disagree with independent compiler pins")
        compiler_path = Path(temp) / SOLC_FILE
        compiler_path.write_bytes(compiler)
        jsc = os.environ.get("JSC", "/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc")
        driver = ('globalThis.console={log:print,warn:print,error:print,info:print,debug:print};'
                  'globalThis.Module={print:function(){},printErr:function(){}};'
                  f'load({json.dumps(str(compiler_path))});'
                  'if(typeof drainMicrotasks==="function")drainMicrotasks();'
                  'var c=Module.cwrap("solidity_compile","string",["string","number","number"]);'
                  f'print(c(read({json.dumps(str(staged_input / "solc-input.json"))}),0,0));')
        output = subprocess.check_output([jsc, "-e", driver])
        (staged_input / "solc-output.json").write_bytes(output)
        for name, url in RPCS.items():
            raw = json_rpc(url, {"jsonrpc": "2.0", "id": 1, "method": "eth_getBlockByNumber", "params": ["finalized", False]})
            result = strict_json(raw, f"{name} finalized-block response").get("result")
            expect(isinstance(result, dict) and isinstance(result.get("number"), str) and isinstance(result.get("hash"), str),
                   f"{name} did not return a finalized block")
            expect(int(result["number"], 16) >= int(PINNED_OBSERVATION_BLOCK["number"], 16),
                   f"{name} has not finalized the pinned observation block")
        for name, url in RPCS.items():
            block_raw = json_rpc(url, {"jsonrpc": "2.0", "id": 1, "method": "eth_getBlockByNumber",
                                           "params": [PINNED_OBSERVATION_BLOCK["number"], False]})
            block_result = strict_json(block_raw, f"{name} pinned-block response").get("result")
            expect(isinstance(block_result, dict)
                   and {"number": block_result.get("number"), "hash": block_result.get("hash")}
                   == PINNED_OBSERVATION_BLOCK, f"{name} returned the wrong pinned observation block")
            request = {"jsonrpc": "2.0", "id": 1, "method": "eth_getCode",
                       "params": [TARGET, PINNED_OBSERVATION_BLOCK["number"]]}
            raw = json_rpc(url, request)
            envelope = {"operator": url, "request": request,
                        "block": PINNED_OBSERVATION_BLOCK, "responseRaw": raw}
            (staged_input / f"rpc-{name}.json").write_bytes(canonical(envelope))

        staged_env = dict(os.environ, WETH10_REFERENCE_DIR=str(staged_ref),
                          WETH10_REFERENCE_LOCK=str(staged_lock), PYTHONDONTWRITEBYTECODE="1")
        subprocess.run([sys.executable, str(Path(__file__).resolve()), "generate"],
                       cwd=ROOT, env=staged_env, check=True)
        subprocess.run([sys.executable, str(Path(__file__).resolve()), "check-drift"],
                       cwd=ROOT, env=staged_env, check=True)

        for staged_path in sorted(staged_input.rglob("*")):
            if staged_path.is_file():
                destination = INPUT / staged_path.relative_to(staged_input)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(staged_path, destination)
        shutil.copy2(staged_lock, LOCK)
    generate(True)
    check_drift_inputs((SOURCE / "deployed-WETH10.sol").read_bytes())
    print("refreshed and validated pinned WETH10 reference inputs")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("generate", "check", "check-drift", "refresh"))
    args = parser.parse_args()
    if args.command == "refresh":
        refresh()
    elif args.command == "check-drift":
        check_drift_inputs((SOURCE / "deployed-WETH10.sol").read_bytes())
        print("OK — WETH10 drift/corroboration inputs: exact pinned snapshots and diffs")
    else:
        generate(args.command == "check")


if __name__ == "__main__":
    try:
        main()
    except (ReferenceError, OSError, subprocess.CalledProcessError, urllib.error.URLError, KeyError, StopIteration) as exc:
        raise SystemExit(f"weth10-reference.py: {exc}")
