#!/usr/bin/env python3
"""Execution-derived BeaconDeposit witnesses on Blanc's BPO2 lane.

This is a deliberately small complement to the exhaustive historical Prague
differential.  It owns two fresh top-level creation transactions and seven
same-input runtime transactions at the shared current-mainnet target.  The
public current-mainnet API is the sole route to t8n; there is no caller fork
parameter and this program never imports the execution-spec packages.

Normal mode is read-only and byte-compares the execution-derived document with
the committed manifest.  ``--write-manifest`` is the sole writer and is reached
only after every BPO2 execution, assertion, dominance check, registry check,
and in-process falsifier succeeds.  ``--static-self-check`` needs neither Lean
artifacts nor a t8n execution.
"""

from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Dict, List, Mapping, NoReturn, Optional, Sequence, Tuple


REPO = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO / "scripts"
REFERENCE_DIR = SCRIPT_DIR / "reference" / "beacon-deposit" / "inputs"
SOURCE = REFERENCE_DIR / "deposit_contract.sol"
ARTIFACT = REFERENCE_DIR / "deposit_contract.json"
DEPLOYED_RUNTIME = REFERENCE_DIR / "deployed-runtime.norm.hex"
EVALUATOR = SCRIPT_DIR / "eval-beacon-deposit-differential-code.lean"
PROFILE_PATH = SCRIPT_DIR / "current-mainnet-target.json"
SHARED_HELPER = SCRIPT_DIR / "current_mainnet.py"
WRAPPER = SCRIPT_DIR / "check-beacon-deposit-current-mainnet.sh"
REGISTRY = REPO / "BEACON_DEPOSIT_DEVIATIONS.md"
MANIFEST_PATH = (
    SCRIPT_DIR / "fixtures" / "beacon-deposit-current-mainnet" / "manifest.json"
)

MANIFEST_SCHEMA = 2
STATIC_INVENTORY_FALSIFIERS = 4
API_BOUNDARY_FALSIFIERS = 3
RAW_CHANNEL_FALSIFIERS = 5
MANIFEST_CHANNEL_FALSIFIERS = 5
REGISTRY_FALSIFIERS = 1
MANIFEST_FALSIFIERS = 12
CODE_DEPOSIT_GAS_PER_BYTE = 200
EIP170_LIMIT = 24_576
EIP3860_LIMIT = 49_152
TX_BASE_GAS = 21_000
TX_CREATE_GAS = 32_000
TX_DATA_TOKEN_STANDARD = 4
TX_DATA_TOKEN_FLOOR = 10
INITCODE_WORD_GAS = 2
GAS_PRICE = 10
TX_MAX_GAS_LIMIT = 16_777_216
GAS_LIMIT = TX_MAX_GAS_LIMIT
BLOCK_GAS_LIMIT = 268_435_456
MAINNET_BPO2_ACTIVATION_TIMESTAMP = 1_767_747_671
GWEI = 10**9
ETHER = 10**18
UINT256_MAX = 2**256 - 1

SOURCE_SHA256 = "2a8db249155e8502e1132f14410b8d7b2a924512723ed07a08167477d8f8c073"
ARTIFACT_SHA256 = "fbb573648e4fe96a6b731768cbf5165f5037d7bd29f43359c5316eeb9edc78e6"
DEPLOYED_RUNTIME_TEXT_SHA256 = (
    "867e261f9811c5227ff0e2ec5d7803156f1af3428e49d6ffc041102da3050432"
)
REFERENCE_RUNTIME_SHA256 = (
    "5aaa8327c5765ec883224895ca02cade2871e12dad0197bdc791efc91c7ef18d"
)
REFERENCE_CREATION_SHA256 = (
    "4ee0b7f9a82a4cc382cda436621e4253167b9475bb01d7c3ae1ac0eec44e5a47"
)
REFERENCE_RUNTIME_BYTES = 6_358
REFERENCE_CREATION_BYTES = 6_633
BLANC_RUNTIME_SHA256 = (
    "8f2474c60f85dce94e97403369d64d94d7cce4bbb44e620175bd43a5990f0c48"
)
BLANC_CREATION_SHA256 = (
    "3f3af51d0674c1afb7679dbcc60720bbd3f3d61adc9bd319da025064c0521c59"
)
BLANC_RUNTIME_BYTES = 2_891
BLANC_CREATION_BYTES = 3_037
CONSTRUCTOR_STATIC_EXPECTED = {
    "reference": {"prefixBytes": 275, "sstoreSites": [250],
                  "staticcallSites": [192], "codecopySites": [270]},
    "blanc": {"prefixBytes": 146, "sstoreSites": [137],
              "staticcallSites": [98], "codecopySites": [57]},
}

EXPECTED_SELECTORS = (
    "01ffc9a7", "22895118", "621fd130", "c5f2892f",
)
SUPPORTS_SELECTOR = bytes.fromhex("01ffc9a7")
DEPOSIT_SELECTOR = bytes.fromhex("22895118")
COUNT_SELECTOR = bytes.fromhex("621fd130")
ROOT_SELECTOR = bytes.fromhex("c5f2892f")
ERC165_ID = bytes.fromhex("01ffc9a7")
DEPOSIT_INTERFACE_ID = bytes.fromhex("85640907")
INVALID_INTERFACE_ID = bytes.fromhex("ffffffff")
DEPOSIT_EVENT_TOPIC = (
    "649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5"
)

CONTRACT = "0x00000000219ab540356cbb839cbe05303d7705fa"
SENDER = "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"
CREATE_TARGET = "0x6295ee1b4f6dd65047762f924ecd367c17eabf8f"
SECRET_KEY = (
    "0x45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8"
)
COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"
SENDER_BALANCE = 10**30
ZERO32 = bytes(32)
DEPTH = 32

PROFILE_CLAIMS = (
    "executionFork=BPO2",
    "executionModule=ethereum.forks.bpo2",
    "chainId=1",
    "reward=-1",
    "logicalCompilerFork=Osaka",
    "testingBackend=cancun",
    "externalSolcInvoked=false",
)
CURRENT_MAINNET_PUBLIC_API = (
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
)
REQUIRED_CHANNELS = (
    "status", "gas", "deposit-log", "deposit-storage", "deposit-eth",
)
CREATION_DOMINANCE_KEYS = (
    "transactionGasUsed", "netConstructorExecutionGasAfterRefund",
)
CREATION_ASSERTIONS = (
    "freshTopLevelTransaction",
    "successfulReceipt",
    "exactCreateTarget",
    "exactInstalledOwnRuntime",
    "exactOwnLayoutStorage",
    "zeroLogs",
    "exactTargetBalanceNonce",
    "eip170RuntimeLimit",
    "eip3860InitcodeLimit",
    "eip7825TransactionGasLimit",
    "refundCounterNotExposed",
    "calldataFloorNotBinding",
)
HISTORICAL_BOUNDARY = (
    "BPO2 credits status/gas on every row and exact deposit log/storage/ETH; "
    "the preserved Prague differential exclusively owns exact returndata and "
    "its broader malformed/precompile/OOG corpus"
)
DEVIATION_MARKER_VERSION = "beacon-deposit-current-mainnet-gas-v1"
MANIFEST_CLASSES = (
    "row-inventory", "credited-channel", "profile", "constructor-dominance",
    "decomposition-basis", "historical-boundary", "artifact-size",
    "cache-repository", "runtime-lock-path", "runtime-lock-digest",
    "cache-ownership", "gas-policy",
)
CACHE_REPOSITORY_FILES = (
    "scripts/current-mainnet-target.json",
    "scripts/current-mainnet-runtime-lock.json",
    "scripts/current_mainnet.py",
    "scripts/gen-current-mainnet-runtime-lock.py",
    "scripts/gen-beacon-deposit-current-mainnet.py",
    "scripts/check-beacon-deposit-current-mainnet.sh",
    "scripts/eval-beacon-deposit-differential-code.lean",
    "scripts/reference/beacon-deposit/inputs/deposit_contract.sol",
    "scripts/reference/beacon-deposit/inputs/deposit_contract.json",
    "scripts/reference/beacon-deposit/inputs/deployed-runtime.norm.hex",
    "BEACON_DEPOSIT_DEVIATIONS.md",
)
CACHE_RUNTIME_LOCK = "scripts/current-mainnet-runtime-lock.json"
CACHE_RUNTIME_PLATFORMS = ("macos-arm64", "linux-x86_64")
CACHE_OWNERSHIP = (
    "the shared runtime lock owns the reference environment's semantic "
    "closure: exact versions on every platform and exact installed bytes on "
    "each platform whose row has been generated there; the gate registry "
    "additionally fingerprints the selected exact checkout, site-packages "
    "population, and CPython 3.11.9 standard library"
)


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def q(value: int) -> str:
    if value < 0:
        die(f"negative quantity: {value}")
    return hex(value)


def parse_quantity(value: object, label: str) -> int:
    if not isinstance(value, str) \
            or re.fullmatch(r"0x(?:0|[1-9a-f][0-9a-f]*)", value) is None:
        die(f"{label}: noncanonical hex quantity: {value!r}")
    return int(value[2:], 16)


def parse_bloom(value: object, label: str) -> int:
    if not isinstance(value, str) or re.fullmatch(r"0x[0-9a-f]{512}", value) is None:
        die(f"{label}: noncanonical 256-byte bloom: {value!r}")
    return int(value[2:], 16)


def h256(value: int) -> bytes:
    if not 0 <= value <= UINT256_MAX:
        die(f"word outside uint256: {value}")
    return value.to_bytes(32, "big")


def canonical_address(value: str) -> str:
    raw = value.removeprefix("0x")
    if not re.fullmatch(r"[0-9a-fA-F]{40}", raw):
        die(f"not an address: {value!r}")
    return "0x" + raw.lower()


def address_bytes(value: str) -> bytes:
    return bytes.fromhex(canonical_address(value)[2:])


def sha256_file(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as exc:
        die(f"cannot fingerprint {path}: {exc}")


def bytes_identity(value: bytes) -> Mapping[str, object]:
    return {"byteLength": len(value), "sha256": hashlib.sha256(value).hexdigest()}


def canonical_json_sha256(value: object) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


# Small dependency-free Ethereum Keccak/RLP implementation.  It keeps the
# consumer independent of the target checkout's private Python modules while
# letting receipt logs and CREATE identity be checked from first principles.
_KECCAK_ROUNDS = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)
_KECCAK_ROTATION = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)
_MASK64 = (1 << 64) - 1


def _rotl64(value: int, amount: int) -> int:
    if amount == 0:
        return value & _MASK64
    return ((value << amount) | (value >> (64 - amount))) & _MASK64


def _keccak_f(state: List[int]) -> None:
    for constant in _KECCAK_ROUNDS:
        parity = [state[x] ^ state[x + 5] ^ state[x + 10]
                  ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        delta = [parity[(x - 1) % 5] ^ _rotl64(parity[(x + 1) % 5], 1)
                 for x in range(5)]
        for y in range(5):
            for x in range(5):
                state[x + 5 * y] ^= delta[x]
        rotated = [0] * 25
        for y in range(5):
            for x in range(5):
                rotated[y + 5 * ((2 * x + 3 * y) % 5)] = _rotl64(
                    state[x + 5 * y], _KECCAK_ROTATION[x][y])
        for y in range(5):
            for x in range(5):
                state[x + 5 * y] = rotated[x + 5 * y] ^ (
                    (~rotated[(x + 1) % 5 + 5 * y])
                    & rotated[(x + 2) % 5 + 5 * y]
                )
                state[x + 5 * y] &= _MASK64
        state[0] ^= constant


def keccak256(value: bytes) -> bytes:
    rate = 136
    padded = bytearray(value)
    padded.append(0x01)  # Ethereum's legacy Keccak domain, not SHA3's 0x06.
    padded.extend(bytes((-len(padded)) % rate))
    padded[-1] |= 0x80
    state = [0] * 25
    for offset in range(0, len(padded), rate):
        block = padded[offset:offset + rate]
        for lane in range(rate // 8):
            state[lane] ^= int.from_bytes(block[8 * lane:8 * lane + 8], "little")
        _keccak_f(state)
    return b"".join(word.to_bytes(8, "little") for word in state)[:32]


def rlp_encode(value: object) -> bytes:
    if isinstance(value, int):
        if value < 0:
            die("RLP cannot encode a negative integer")
        raw = b"" if value == 0 else value.to_bytes((value.bit_length() + 7) // 8, "big")
        return rlp_encode(raw)
    if isinstance(value, bytes):
        if len(value) == 1 and value[0] < 0x80:
            return value
        if len(value) < 56:
            return bytes([0x80 + len(value)]) + value
        size = len(value).to_bytes((len(value).bit_length() + 7) // 8, "big")
        return bytes([0xB7 + len(size)]) + size + value
    if isinstance(value, (list, tuple)):
        payload = b"".join(rlp_encode(item) for item in value)
        if len(payload) < 56:
            return bytes([0xC0 + len(payload)]) + payload
        size = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
        return bytes([0xF7 + len(size)]) + size + payload
    die(f"unsupported RLP value: {type(value).__name__}")


def create_address(sender: str, nonce: int) -> str:
    return "0x" + keccak256(rlp_encode([address_bytes(sender), nonce]))[-20:].hex()


def log_bloom(entries: Sequence[Tuple[bytes, Sequence[bytes], bytes]]) -> int:
    bloom = 0
    for address, topics, _data in entries:
        for item in (address, *topics):
            digest = keccak256(item)
            for offset in (0, 2, 4):
                bit = ((digest[offset] << 8) | digest[offset + 1]) & 2047
                bloom |= 1 << bit
    return bloom


def logs_hash(entries: Sequence[Tuple[bytes, Sequence[bytes], bytes]]) -> str:
    encoded = [[address, list(topics), data] for address, topics, data in entries]
    return "0x" + keccak256(rlp_encode(encoded)).hex()


def zero_hashes() -> Tuple[bytes, ...]:
    result = [ZERO32]
    for _ in range(1, DEPTH):
        result.append(hashlib.sha256(result[-1] + result[-1]).digest())
    return tuple(result)


ZERO_HASHES = zero_hashes()


def sha_pair(left: bytes, right: bytes) -> bytes:
    if len(left) != 32 or len(right) != 32:
        die("tree hash requires two words")
    return hashlib.sha256(left + right).digest()


def le64(value: int) -> bytes:
    if not 0 <= value < 2**64:
        die("little-endian value is not uint64")
    return value.to_bytes(8, "little")


def abi_tail(value: bytes) -> bytes:
    return h256(len(value)) + value + bytes((-len(value)) % 32)


def sample_fields(index: int) -> Tuple[bytes, bytes, bytes]:
    seed = hashlib.sha256(f"beacon-deposit-differential-{index}".encode()).digest()
    pubkey = (
        hashlib.sha256(seed + b"pubkey-0").digest()
        + hashlib.sha256(seed + b"pubkey-1").digest()
    )[:48]
    withdrawal = hashlib.sha256(seed + b"withdrawal").digest()
    signature = b"".join(
        hashlib.sha256(seed + f"signature-{part}".encode()).digest()
        for part in range(3)
    )
    return pubkey, withdrawal, signature


def deposit_node(pubkey: bytes, withdrawal: bytes,
                 signature: bytes, amount_gwei: int) -> bytes:
    pubkey_root = hashlib.sha256(pubkey + bytes(16)).digest()
    signature_root = sha_pair(
        hashlib.sha256(signature[:64]).digest(),
        hashlib.sha256(signature[64:] + ZERO32).digest(),
    )
    return sha_pair(
        sha_pair(pubkey_root, withdrawal),
        sha_pair(le64(amount_gwei) + bytes(24), signature_root),
    )


def deposit_calldata(pubkey: bytes, withdrawal: bytes,
                     signature: bytes, root: bytes) -> bytes:
    tails = (abi_tail(pubkey), abi_tail(withdrawal), abi_tail(signature))
    offsets = (128, 128 + len(tails[0]), 128 + len(tails[0]) + len(tails[1]))
    return DEPOSIT_SELECTOR + b"".join(h256(value) for value in offsets) \
        + root + b"".join(tails)


def supports_calldata(interface_id: bytes) -> bytes:
    return SUPPORTS_SELECTOR + interface_id + bytes(28)


def event_data(pubkey: bytes, withdrawal: bytes, amount: bytes,
               signature: bytes, index: bytes) -> bytes:
    fields = (pubkey, withdrawal, amount, signature, index)
    offset = 5 * 32
    heads: List[bytes] = []
    tails: List[bytes] = []
    for value in fields:
        tail = abi_tail(value)
        heads.append(h256(offset))
        tails.append(tail)
        offset += len(tail)
    result = b"".join(heads + tails)
    if len(result) != 576:
        die(f"DepositEvent ABI length differs: {len(result)}")
    return result


@dataclass(frozen=True)
class RuntimeRow:
    name: str
    endpoint: str
    calldata: bytes
    value: int
    succeeds: bool
    credited_channels: Tuple[str, ...]


def runtime_rows() -> Tuple[RuntimeRow, ...]:
    pubkey, withdrawal, signature = sample_fields(0)
    node = deposit_node(pubkey, withdrawal, signature, ETHER // GWEI)
    ordinary = ("status", "gas")
    deposit_channels = ordinary + ("deposit-log", "deposit-storage", "deposit-eth")
    return (
        RuntimeRow(
            "deposit-success", "deposit(bytes,bytes,bytes,bytes32)",
            deposit_calldata(pubkey, withdrawal, signature, node),
            ETHER, True, deposit_channels,
        ),
        RuntimeRow("get-deposit-root", "get_deposit_root()", ROOT_SELECTOR,
                   0, True, ordinary),
        RuntimeRow("get-deposit-count", "get_deposit_count()", COUNT_SELECTOR,
                   0, True, ordinary),
        RuntimeRow("supports-erc165", "supportsInterface(bytes4)",
                   supports_calldata(ERC165_ID), 0, True, ordinary),
        RuntimeRow("supports-deposit", "supportsInterface(bytes4)",
                   supports_calldata(DEPOSIT_INTERFACE_ID), 0, True, ordinary),
        RuntimeRow("supports-invalid", "supportsInterface(bytes4)",
                   supports_calldata(INVALID_INTERFACE_ID), 0, True, ordinary),
        RuntimeRow("no-match", "no-match", b"", 0, False, ordinary),
    )


REQUIRED_ROW_NAMES = tuple(row.name for row in runtime_rows())
REQUIRED_ROW_CHANNEL_MAP = tuple(
    row.name + "=" + "+".join(row.credited_channels) for row in runtime_rows()
)


def validate_runtime_inventory(rows: Sequence[RuntimeRow]) -> None:
    if tuple(row.name for row in rows) != REQUIRED_ROW_NAMES:
        die("current-mainnet runtime row order/inventory differs")
    if len({row.name for row in rows}) != len(rows):
        die("current-mainnet runtime row names are duplicated")
    if tuple(
        row.name + "=" + "+".join(row.credited_channels) for row in rows
    ) != REQUIRED_ROW_CHANNEL_MAP:
        die("current-mainnet per-row credited channels differ")
    credited = {channel for row in rows for channel in row.credited_channels}
    if credited != set(REQUIRED_CHANNELS):
        die("current-mainnet channel inventory differs")
    if any(row.name != "deposit-success" and row.credited_channels != ("status", "gas")
           for row in rows):
        die("view/support/no-match row credits more than status and gas")
    if [row.endpoint for row in rows].count("supportsInterface(bytes4)") != 3:
        die("current-mainnet ERC-165 probe count differs")
    if tuple(row.succeeds for row in rows) != (True, True, True, True, True, True, False):
        die("current-mainnet expected-status inventory differs")


def static_inventory_falsifiers(rows: Sequence[RuntimeRow]) -> int:
    mutants: List[Tuple[str, Sequence[RuntimeRow]]] = []
    mutants.append(("row-deletion", rows[1:]))
    broken = list(rows)
    broken[1] = replace(broken[1], credited_channels=("status",))
    mutants.append(("channel-deletion", broken))
    broken = list(rows)
    broken[-1] = replace(broken[-1], succeeds=True)
    mutants.append(("status-corruption", broken))
    broken = list(rows)
    broken[3] = replace(broken[3], endpoint="renamed(bytes4)")
    mutants.append(("endpoint-corruption", broken))
    for label, mutant in mutants:
        try:
            validate_runtime_inventory(mutant)
        except RuntimeError:
            continue
        die(f"static inventory falsifier survived: {label}")
    if len(mutants) != STATIC_INVENTORY_FALSIFIERS:
        die("static inventory-falsifier count differs")
    return len(mutants)


def parse_blanc_artifacts(text: str) -> Mapping[str, object]:
    lines = [line for line in text.splitlines() if line.strip()]
    labels = ("runtime", "creation", "selectors")
    if len(lines) != 3 or tuple(
            line.split()[0] if line.split() else "" for line in lines) != labels:
        die("Lean evaluator must emit exactly runtime/creation/selectors rows")
    result: Dict[str, object] = {}
    for label, line in zip(labels[:2], lines[:2]):
        parts = line.split(" ")
        if len(parts) != 3 or "" in parts or not parts[1].isdecimal() \
                or not re.fullmatch(r"[0-9a-f]+", parts[2]) \
                or len(parts[2]) % 2:
            die(f"Lean evaluator {label} row is noncanonical")
        value = bytes.fromhex(parts[2])
        if len(value) != int(parts[1]):
            die(f"Lean evaluator {label} length differs")
        result[label] = value
    parts = lines[2].split(" ")
    if len(parts) != 3 or not parts[1].isdecimal():
        die("Lean evaluator selector row is noncanonical")
    selectors = tuple(parts[2].split(","))
    if len(selectors) != int(parts[1]) or selectors != EXPECTED_SELECTORS:
        die("Lean evaluator selector inventory differs")
    result["selectors"] = selectors
    runtime = result["runtime"]
    creation = result["creation"]
    assert isinstance(runtime, bytes) and isinstance(creation, bytes)
    if bytes_identity(runtime) != {
        "byteLength": BLANC_RUNTIME_BYTES, "sha256": BLANC_RUNTIME_SHA256,
    } or bytes_identity(creation) != {
        "byteLength": BLANC_CREATION_BYTES, "sha256": BLANC_CREATION_SHA256,
    }:
        die("Blanc evaluator artifact identity differs from this witness contract")
    if not creation.endswith(runtime):
        die("Blanc creation artifact does not end in its runtime")
    return result


def load_reference() -> Mapping[str, object]:
    identities = (
        ("source", SOURCE, SOURCE_SHA256),
        ("artifact", ARTIFACT, ARTIFACT_SHA256),
        ("deployed runtime text", DEPLOYED_RUNTIME, DEPLOYED_RUNTIME_TEXT_SHA256),
    )
    for label, path, expected in identities:
        actual = sha256_file(path)
        if actual != expected:
            die(f"pinned reference {label} digest differs: {actual}")
    runtime_text = DEPLOYED_RUNTIME.read_text(encoding="ascii")
    if not re.fullmatch(r"[0-9a-f]+", runtime_text) or len(runtime_text) % 2:
        die("pinned reference runtime is not normalized lowercase hex")
    runtime = bytes.fromhex(runtime_text)
    try:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        creation_hex = artifact["bytecode"]
        abi = artifact["abi"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        die(f"pinned reference artifact is unreadable: {exc}")
    if not isinstance(creation_hex, str) or not re.fullmatch(r"0x[0-9a-f]+", creation_hex):
        die("pinned reference creation bytecode is not normalized")
    creation = bytes.fromhex(creation_hex[2:])
    if bytes_identity(runtime) != {
        "byteLength": REFERENCE_RUNTIME_BYTES, "sha256": REFERENCE_RUNTIME_SHA256,
    } or bytes_identity(creation) != {
        "byteLength": REFERENCE_CREATION_BYTES, "sha256": REFERENCE_CREATION_SHA256,
    }:
        die("pinned reference byte identity differs")
    if not creation.endswith(runtime):
        die("pinned reference runtime is not the creation artifact tail")
    signatures = []
    for row in abi:
        if row.get("type") == "function":
            inputs = ",".join(item["type"] for item in row["inputs"])
            signatures.append(f"{row['name']}({inputs})")
    selectors = tuple(sorted(keccak256(signature.encode())[:4].hex()
                             for signature in signatures))
    if selectors != EXPECTED_SELECTORS:
        die(f"pinned reference ABI selectors differ: {selectors}")
    return {"runtime": runtime, "creation": creation, "selectors": selectors}


def opcode_sites(code: bytes, opcode: int) -> List[int]:
    sites: List[int] = []
    pc = 0
    while pc < len(code):
        current = code[pc]
        if current == opcode:
            sites.append(pc)
        pc += 1 + (current - 0x5F if 0x60 <= current <= 0x7F else 0)
    return sites


def constructor_static_basis(side: str, creation: bytes, runtime: bytes) \
        -> Mapping[str, object]:
    prefix = creation[:-len(runtime)]
    expected = CONSTRUCTOR_STATIC_EXPECTED[side]
    observed = {
        "prefixBytes": len(prefix),
        "sstoreSites": opcode_sites(prefix, 0x55),
        "staticcallSites": opcode_sites(prefix, 0xFA),
        "codecopySites": opcode_sites(prefix, 0x39),
    }
    if observed != expected:
        die(f"{side} constructor source-site inventory differs: {observed}")
    forbidden = {
        "CALL": opcode_sites(prefix, 0xF1),
        "CALLCODE": opcode_sites(prefix, 0xF2),
        "DELEGATECALL": opcode_sites(prefix, 0xF4),
        "CREATE": opcode_sites(prefix, 0xF0),
        "CREATE2": opcode_sites(prefix, 0xF5),
        "SELFDESTRUCT": opcode_sites(prefix, 0xFF),
    }
    if any(forbidden.values()):
        die(f"{side} constructor gained an unowned external/create/delete site")
    return {
        **observed,
        "forbiddenExternalCreateDeleteSites": forbidden,
        "refundInferenceCredited": False,
    }


def current_mainnet_api():
    """Import exactly the five public functions, and only in execution mode."""

    from current_mainnet import (  # pylint: disable=import-outside-toplevel
        load_profile,
        resolve_root,
        run_t8n,
        target_paths,
        verify_target,
    )
    return load_profile, resolve_root, verify_target, target_paths, run_t8n


def validate_current_mainnet_api_source(source: str) -> None:
    """Fail closed if this consumer bypasses or widens the shared API."""

    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        die(f"current-mainnet consumer source is invalid Python: {exc}")
    forbidden_prefixes = ("ethereum", "ethereum_spec_tools", "execution_specs")
    for node in ast.walk(tree):
        modules: List[str] = []
        if isinstance(node, ast.Import):
            modules = [alias.name for alias in node.names]
        elif isinstance(node, ast.ImportFrom) and node.module is not None:
            modules = [node.module]
        if any(module == prefix or module.startswith(prefix + ".")
               for module in modules for prefix in forbidden_prefixes):
            die("consumer imports execution-spec internals instead of the shared API")
    api_functions = [node for node in tree.body
                     if isinstance(node, ast.FunctionDef)
                     and node.name == "current_mainnet_api"]
    if len(api_functions) != 1:
        die("consumer current_mainnet_api owner is absent or duplicated")
    owner = api_functions[0]
    imports = [node for node in ast.walk(owner)
               if isinstance(node, ast.ImportFrom)
               and node.module == "current_mainnet"]
    if len(imports) != 1 \
            or tuple(sorted(alias.name for alias in imports[0].names)) \
            != tuple(sorted(CURRENT_MAINNET_PUBLIC_API)) \
            or any(alias.asname is not None for alias in imports[0].names):
        die("consumer imports other than the exact current-mainnet public API")
    returns = [node for node in owner.body if isinstance(node, ast.Return)]
    if len(returns) != 1 or not isinstance(returns[0].value, ast.Tuple) \
            or tuple(
                element.id if isinstance(element, ast.Name) else ""
                for element in returns[0].value.elts
            ) != CURRENT_MAINNET_PUBLIC_API:
        die("consumer returns a widened or reordered current-mainnet API")
    calls = [node for node in ast.walk(tree)
             if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
             and node.func.id == "run_t8n"]
    expected_keywords = ("root", "profile", "state_test", "timeout")
    if len(calls) != 2 or any(
        tuple(keyword.arg for keyword in call.keywords) != expected_keywords
        for call in calls
    ):
        die("consumer run_t8n call count or keyword contract differs")


def current_mainnet_api_falsifiers(source: str) -> int:
    mutants = (
        ("direct-execution-spec-import",
         source + "\nfrom ethereum.forks.bpo2 import fork\n"),
        ("public-api-name",
         source.replace("        verify_target,\n", "        verify_target_alt,\n", 1)),
        ("fork-override",
         source.replace("state_test=True, timeout=120,",
                        "fork=\"Prague\", state_test=True, timeout=120,", 1)),
    )
    for label, mutant in mutants:
        if mutant == source:
            die(f"current-mainnet API falsifier did not mutate source: {label}")
        try:
            validate_current_mainnet_api_source(mutant)
        except RuntimeError:
            continue
        die(f"current-mainnet API falsifier survived: {label}")
    if len(mutants) != API_BOUNDARY_FALSIFIERS:
        die("current-mainnet API-falsifier count differs")
    return len(mutants)


def profile_claims(profile: Mapping[str, object]) -> Tuple[str, ...]:
    execution = profile.get("execution")
    compiler = profile.get("compiler")
    if not isinstance(execution, dict) or not isinstance(compiler, dict):
        die("current-mainnet profile lacks execution/compiler objects")
    return (
        f"executionFork={execution.get('fork')}",
        f"executionModule={execution.get('module')}",
        f"chainId={execution.get('chainId')}",
        f"reward={execution.get('reward')}",
        f"logicalCompilerFork={compiler.get('logicalFork')}",
        f"testingBackend={compiler.get('testingBackend')}",
        "externalSolcInvoked=" + str(compiler.get("externalSolcInvoked")).lower(),
    )


def block_environment() -> Mapping[str, object]:
    return {
        "currentCoinbase": COINBASE,
        "currentGasLimit": q(BLOCK_GAS_LIMIT),
        "currentNumber": "0x1",
        "currentTimestamp": q(MAINNET_BPO2_ACTIVATION_TIMESTAMP),
        "currentRandom": "0x" + "00" * 32,
        "currentBaseFee": "0x7",
        "currentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": "0x" + "11" * 32,
        "blockHashes": {"0x0": "0x" + "22" * 32},
        "withdrawals": [],
    }


def account(*, nonce: int, balance: int, code: bytes = b"",
            storage: Optional[Mapping[int, int]] = None) -> Mapping[str, object]:
    selected_storage = {} if storage is None else storage
    return {
        "nonce": q(nonce),
        "balance": q(balance),
        "code": "0x" + code.hex(),
        "storage": {q(key): q(value) for key, value in sorted(selected_storage.items())
                    if value != 0},
    }


def transaction(*, nonce: int, to: str, value: int,
                data: bytes) -> Mapping[str, object]:
    return {
        "type": "0x0",
        "chainId": "0x1",
        "nonce": q(nonce),
        "gasPrice": q(GAS_PRICE),
        "gas": q(GAS_LIMIT),
        "to": to,
        "value": q(value),
        "input": "0x" + data.hex(),
        "secretKey": SECRET_KEY,
    }


def find_account(alloc: object, address: str, label: str) -> Mapping[str, object]:
    if not isinstance(alloc, dict):
        die(f"{label}: t8n alloc is not an object")
    wanted = int(canonical_address(address), 16)
    matches = [value for key, value in alloc.items()
               if isinstance(key, str) and int(key, 16) == wanted]
    if len(matches) != 1 or not isinstance(matches[0], dict):
        die(f"{label}: expected one post-state account for {address}, got {len(matches)}")
    raw = matches[0]
    if set(raw) != {"nonce", "balance", "code", "storage"}:
        die(f"{label}: account fields differ: {sorted(raw)}")
    return raw


def normalize_account(raw: Mapping[str, object], label: str) -> Mapping[str, object]:
    try:
        nonce = int(str(raw["nonce"]), 16)
        balance = int(str(raw["balance"]), 16)
        code_text = str(raw["code"])
        storage_raw = raw["storage"]
    except (KeyError, TypeError, ValueError) as exc:
        die(f"{label}: malformed account: {exc}")
    if not re.fullmatch(r"0x[0-9a-f]*", code_text) or len(code_text) % 2:
        die(f"{label}: account code is not normalized hex")
    if not isinstance(storage_raw, dict):
        die(f"{label}: account storage is not an object")
    storage: Dict[int, int] = {}
    for key, value in storage_raw.items():
        try:
            slot = int(str(key), 16)
            word = int(str(value), 16)
        except ValueError as exc:
            die(f"{label}: malformed storage quantity: {exc}")
        if slot in storage:
            die(f"{label}: duplicate normalized storage slot {slot}")
        if word != 0:
            storage[slot] = word
    return {
        "nonce": nonce,
        "balance": balance,
        "code": bytes.fromhex(code_text[2:]),
        "storage": dict(sorted(storage.items())),
    }


def validate_result(result: object, transaction_count: int,
                    label: str) -> Tuple[Mapping[str, object], ...]:
    if not isinstance(result, dict):
        die(f"{label}: t8n result is not an object")
    if result.get("rejected") not in (None, []):
        die(f"{label}: t8n rejected a transaction: {result.get('rejected')!r}")
    if result.get("blockException") is not None:
        die(f"{label}: t8n block exception: {result.get('blockException')!r}")
    receipts = result.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != transaction_count \
            or any(not isinstance(receipt, dict) for receipt in receipts):
        observed = len(receipts) if isinstance(receipts, list) else type(receipts).__name__
        die(
            f"{label}: expected {transaction_count} receipts, observed {observed}; "
            f"result keys={sorted(result)}"
        )
    return tuple(receipts)


def per_transaction_gas(receipts: Sequence[Mapping[str, object]],
                        label: str) -> Tuple[int, ...]:
    cumulative: List[int] = []
    for index, receipt in enumerate(receipts):
        try:
            raw = receipt["cumulativeGasUsed"]
        except KeyError as exc:
            die(f"{label}: malformed receipt cumulative gas: {exc}")
        cumulative.append(parse_quantity(raw, f"{label}/receipt-{index}/cumulativeGasUsed"))
    if any(value <= (cumulative[index - 1] if index else 0)
           for index, value in enumerate(cumulative)):
        die(f"{label}: receipt cumulative gas is not strictly increasing")
    return tuple(value - (cumulative[index - 1] if index else 0)
                 for index, value in enumerate(cumulative))


def receipt_status(receipt: Mapping[str, object], label: str) -> bool:
    value = receipt.get("status")
    if value not in ("0x0", "0x1"):
        die(f"{label}: receipt status is not canonical hex 0/1: {value!r}")
    return value == "0x1"


def receipt_logs(receipt: Mapping[str, object], label: str) \
        -> Tuple[Tuple[bytes, Tuple[bytes, ...], bytes], ...]:
    raw_logs = receipt.get("logs")
    if not isinstance(raw_logs, list):
        die(f"{label}: receipt logs are not an array")
    result: List[Tuple[bytes, Tuple[bytes, ...], bytes]] = []
    for index, raw in enumerate(raw_logs):
        if not isinstance(raw, dict) or set(raw) != {"address", "topics", "data"}:
            die(f"{label}: receipt log {index} shape differs")
        address_text = raw["address"]
        topics_raw = raw["topics"]
        data_text = raw["data"]
        if not isinstance(address_text, str) \
                or canonical_address(address_text) != address_text \
                or not isinstance(topics_raw, list) \
                or any(not isinstance(topic, str)
                       or re.fullmatch(r"0x[0-9a-f]{64}", topic) is None
                       for topic in topics_raw) \
                or not isinstance(data_text, str) \
                or re.fullmatch(r"0x(?:[0-9a-f]{2})*", data_text) is None:
            die(f"{label}: receipt log {index} is not canonical")
        result.append((
            address_bytes(address_text),
            tuple(bytes.fromhex(topic[2:]) for topic in topics_raw),
            bytes.fromhex(data_text[2:]),
        ))
    return tuple(result)


def expected_constructor_storage(side: str) -> Mapping[int, int]:
    base = 33 if side == "reference" else 0x300
    return {base + height: int.from_bytes(ZERO_HASHES[height], "big")
            for height in range(1, DEPTH)}


def expected_runtime_initial_storage(side: str) -> Mapping[int, int]:
    return expected_constructor_storage(side)


def expected_runtime_final_storage(side: str) -> Mapping[int, int]:
    pubkey, withdrawal, signature = sample_fields(0)
    node = deposit_node(pubkey, withdrawal, signature, ETHER // GWEI)
    result = dict(expected_runtime_initial_storage(side))
    result[0 if side == "reference" else 0x100] = int.from_bytes(node, "big")
    result[32 if side == "reference" else 0x200] = 1
    return dict(sorted(result.items()))


def logical_state(side: str, storage: Mapping[int, int]) -> Mapping[str, object]:
    branch_base = 0 if side == "reference" else 0x100
    count_slot = 32 if side == "reference" else 0x200
    zero_base = 33 if side == "reference" else 0x300
    return {
        "branch": ["0x" + h256(storage.get(branch_base + height, 0)).hex()
                   for height in range(DEPTH)],
        "count": q(storage.get(count_slot, 0)),
        "zeroHashes": ["0x" + h256(storage.get(zero_base + height, 0)).hex()
                       for height in range(DEPTH)],
        "layoutQualified": True,
    }


def expected_log() -> Tuple[bytes, Sequence[bytes], bytes]:
    pubkey, withdrawal, signature = sample_fields(0)
    data = event_data(pubkey, withdrawal, le64(ETHER // GWEI), signature, le64(0))
    return address_bytes(CONTRACT), (bytes.fromhex(DEPOSIT_EVENT_TOPIC),), data


def intrinsic_components(initcode: bytes) -> Mapping[str, object]:
    zero_bytes = initcode.count(0)
    nonzero_bytes = len(initcode) - zero_bytes
    tokens = zero_bytes + 4 * nonzero_bytes
    initcode_word_cost = INITCODE_WORD_GAS * ((len(initcode) + 31) // 32)
    regular = TX_BASE_GAS + TX_CREATE_GAS + TX_DATA_TOKEN_STANDARD * tokens \
        + initcode_word_cost
    floor = TX_BASE_GAS + TX_DATA_TOKEN_FLOOR * tokens
    return {
        "zeroCalldataBytes": zero_bytes,
        "nonzeroCalldataBytes": nonzero_bytes,
        "calldataTokens": tokens,
        "baseGas": TX_BASE_GAS,
        "createSurchargeGas": TX_CREATE_GAS,
        "standardTokenGas": TX_DATA_TOKEN_STANDARD * tokens,
        "eip3860InitcodeWordGas": initcode_word_cost,
        "regularIntrinsicGas": regular,
        "calldataFloorGas": floor,
    }


def run_creation(side: str, creation: bytes, runtime: bytes,
                 *, root: Path, profile: Mapping[str, object], run_t8n) \
        -> Mapping[str, object]:
    target = create_address(SENDER, 0)
    if target != CREATE_TARGET:
        die("fresh CREATE target derivation differs from the pinned identity")
    alloc = {SENDER: account(nonce=0, balance=SENDER_BALANCE)}
    tx = transaction(nonce=0, to="", value=0, data=creation)
    outputs = run_t8n(
        alloc, block_environment(), [tx], root=root, profile=profile,
        state_test=True, timeout=120,
    )
    receipts = validate_result(outputs.result, 1, f"creation/{side}")
    receipt = receipts[0]
    if not receipt_status(receipt, f"creation/{side}"):
        die(f"creation/{side}: receipt did not succeed")
    gas_used = per_transaction_gas(receipts, f"creation/{side}")[0]
    if parse_quantity(outputs.result.get("gasUsed"),
                      f"creation/{side}/block-gas") != gas_used:
        die(f"creation/{side}: block/receipt gas differs")
    target_account = normalize_account(
        find_account(outputs.alloc, target, f"creation/{side}/target"),
        f"creation/{side}/target",
    )
    sender_account = normalize_account(
        find_account(outputs.alloc, SENDER, f"creation/{side}/sender"),
        f"creation/{side}/sender",
    )
    expected_storage = expected_constructor_storage(side)
    if target_account != {
        "nonce": 1, "balance": 0, "code": runtime,
        "storage": expected_storage,
    }:
        die(f"creation/{side}: exact target account/code/storage differs")
    expected_sender = {
        "nonce": 1,
        "balance": SENDER_BALANCE - gas_used * GAS_PRICE,
        "code": b"",
        "storage": {},
    }
    if sender_account != expected_sender:
        die(f"creation/{side}: exact sender nonce/fee state differs")
    empty_hash = logs_hash(())
    if receipt_logs(receipt, f"creation/{side}") != () \
            or outputs.result.get("logsHash") != empty_hash \
            or parse_bloom(receipt.get("bloom"), f"creation/{side}/bloom") != 0:
        die(f"creation/{side}: constructor emitted a log")
    if len(runtime) > EIP170_LIMIT or len(creation) > EIP3860_LIMIT:
        die(f"creation/{side}: EIP-170/EIP-3860 limit exceeded")
    components = intrinsic_components(creation)
    regular = int(components["regularIntrinsicGas"])
    floor = int(components["calldataFloorGas"])
    code_deposit = len(runtime) * CODE_DEPOSIT_GAS_PER_BYTE
    net_constructor = gas_used - regular - code_deposit
    if gas_used <= floor:
        die(f"creation/{side}: EIP-7623 calldata floor bound or tied the receipt")
    if net_constructor < 0 \
            or gas_used != regular + code_deposit + net_constructor:
        die(f"creation/{side}: constructor gas decomposition is impossible")
    static_basis = constructor_static_basis(side, creation, runtime)
    return {
        "side": side,
        "transaction": {
            "type": 0,
            "chainId": 1,
            "nonce": 0,
            "sender": SENDER,
            "createTarget": target,
            "value": "0x0",
            "gasLimit": GAS_LIMIT,
            "gasPrice": GAS_PRICE,
            "input": bytes_identity(creation),
        },
        "receiptSucceeded": True,
        "target": {
            "address": target,
            "nonce": 1,
            "balance": "0x0",
            "code": bytes_identity(runtime),
            "storage": {q(key): q(value) for key, value in expected_storage.items()},
        },
        "sender": {
            "address": SENDER,
            "nonce": 1,
            "balance": q(expected_sender["balance"]),
        },
        "logicalState": logical_state(side, expected_storage),
        "logs": {"count": 0, "logsHash": empty_hash, "receiptBloom": "0x0"},
        "limits": {
            "runtimeBytes": len(runtime), "eip170Limit": EIP170_LIMIT,
            "runtimeWithinLimit": True,
            "initcodeBytes": len(creation), "eip3860Limit": EIP3860_LIMIT,
            "initcodeWithinLimit": True,
            "transactionGasLimit": GAS_LIMIT,
            "eip7825TransactionGasLimitCap": TX_MAX_GAS_LIMIT,
            "transactionWithinLimit": GAS_LIMIT <= TX_MAX_GAS_LIMIT,
        },
        "gas": {
            **components,
            "calldataFloorBinding": False,
            "calldataFloorSettlementExtraGas": 0,
            "codeDepositGas": code_deposit,
            "netConstructorExecutionGasAfterRefund": net_constructor,
            "transactionGasUsed": gas_used,
            "refundCounterExposedByT8n": False,
            "constructorStaticBasis": static_basis,
            "decomposition": (
                "transactionGasUsed = regularIntrinsicGas + codeDepositGas + "
                "netConstructorExecutionGasAfterRefund; the remainder is receipt-"
                "charged constructor execution after any transaction refund because "
                "this t8n result does not expose the refund counter; calldataFloorGas "
                "is a checked alternative floor, not an additive component"
            ),
        },
    }


def project_runtime_outputs(side: str, runtime: bytes,
                            rows: Sequence[RuntimeRow], result: object,
                            post_alloc: object) -> Mapping[str, object]:
    receipts = validate_result(result, len(rows), f"runtime/{side}")
    gas_used = per_transaction_gas(receipts, f"runtime/{side}")
    statuses = tuple(receipt_status(receipt, f"runtime/{side}/{rows[index].name}")
                     for index, receipt in enumerate(receipts))
    expected_statuses = tuple(row.succeeds for row in rows)
    if statuses != expected_statuses:
        die(f"runtime/{side}: receipt status vector differs: {statuses}")
    expected_entry = expected_log()
    expected_logs_hash = logs_hash((expected_entry,))
    expected_bloom = log_bloom((expected_entry,))
    observed_blooms = tuple(
        parse_bloom(receipt.get("bloom"), f"runtime/{side}/{rows[index].name}/bloom")
        for index, receipt in enumerate(receipts)
    )
    observed_logs = tuple(
        receipt_logs(receipt, f"runtime/{side}/{rows[index].name}")
        for index, receipt in enumerate(receipts)
    )
    if observed_logs != ((expected_entry,), (), (), (), (), (), ()) \
            or not isinstance(result, dict) \
            or result.get("logsHash") != expected_logs_hash \
            or observed_blooms != (expected_bloom, 0, 0, 0, 0, 0, 0):
        die(f"runtime/{side}: exact DepositEvent log/topic/data commitment differs")
    target = normalize_account(
        find_account(post_alloc, CONTRACT, f"runtime/{side}/target"),
        f"runtime/{side}/target",
    )
    sender = normalize_account(
        find_account(post_alloc, SENDER, f"runtime/{side}/sender"),
        f"runtime/{side}/sender",
    )
    expected_storage = expected_runtime_final_storage(side)
    if target != {
        "nonce": 1, "balance": ETHER, "code": runtime,
        "storage": expected_storage,
    }:
        die(f"runtime/{side}: exact deposit target transition differs")
    total_gas = sum(gas_used)
    expected_sender_balance = SENDER_BALANCE - ETHER - total_gas * GAS_PRICE
    if sender != {
        "nonce": len(rows), "balance": expected_sender_balance,
        "code": b"", "storage": {},
    }:
        die(f"runtime/{side}: exact caller value/fee transition differs")
    block_gas = parse_quantity(result.get("gasUsed"), f"runtime/{side}/block-gas")
    if block_gas != total_gas:
        die(f"runtime/{side}: block/receipt gas differs")
    event_address, event_topics, event_bytes = expected_entry
    return {
        "side": side,
        "rows": [{
            "name": row.name,
            "receiptSucceeded": statuses[index],
            "gasUsed": gas_used[index],
            "receiptBloom": q(observed_blooms[index]),
        } for index, row in enumerate(rows)],
        "depositEvidence": {
            "logCount": 1,
            "log": {
                "address": "0x" + event_address.hex(),
                "topics": ["0x" + topic.hex() for topic in event_topics],
                "data": "0x" + event_bytes.hex(),
            },
            "logsHash": expected_logs_hash,
            "logicalState": logical_state(side, expected_storage),
            "rawStorage": {q(key): q(value) for key, value in expected_storage.items()},
            "eth": {
                "callerInitial": q(SENDER_BALANCE),
                "callerFinal": q(expected_sender_balance),
                "callerPrincipalDeltaExcludingFees": q(ETHER),
                "contractInitial": "0x0",
                "contractFinal": q(ETHER),
                "topLevelValue": q(ETHER),
                "fees": q(total_gas * GAS_PRICE),
            },
            "targetNonce": 1,
            "installedRuntime": bytes_identity(runtime),
        },
        "blockGasUsed": total_gas,
    }


def run_runtime(side: str, runtime: bytes, rows: Sequence[RuntimeRow],
                *, root: Path, profile: Mapping[str, object], run_t8n) \
        -> Mapping[str, object]:
    initial_storage = expected_runtime_initial_storage(side)
    alloc = {
        SENDER: account(nonce=0, balance=SENDER_BALANCE),
        CONTRACT: account(nonce=1, balance=0, code=runtime,
                          storage=initial_storage),
    }
    post_alloc: object = alloc
    aggregate_receipts: List[Mapping[str, object]] = []
    aggregate_logs: List[Tuple[bytes, Tuple[bytes, ...], bytes]] = []
    cumulative_gas = 0
    for index, row in enumerate(rows):
        tx = transaction(
            nonce=index, to=CONTRACT, value=row.value, data=row.calldata,
        )
        outputs = run_t8n(
            post_alloc, block_environment(), [tx], root=root, profile=profile,
            state_test=True, timeout=120,
        )
        label = f"runtime/{side}/{row.name}"
        receipt = validate_result(outputs.result, 1, label)[0]
        transaction_gas = per_transaction_gas((receipt,), label)[0]
        if parse_quantity(outputs.result.get("gasUsed"), f"{label}/block-gas") \
                != transaction_gas:
            die(f"{label}: one-transaction block/receipt gas differs")
        raw_logs = receipt_logs(receipt, label)
        if outputs.result.get("logsHash") != logs_hash(raw_logs):
            die(f"{label}: one-transaction raw logs/hash differ")
        cumulative_gas += transaction_gas
        cumulative_receipt = copy.deepcopy(receipt)
        cumulative_receipt["cumulativeGasUsed"] = q(cumulative_gas)
        aggregate_receipts.append(cumulative_receipt)
        aggregate_logs.extend(raw_logs)
        post_alloc = outputs.alloc
    aggregate_result = {
        "rejected": [],
        "blockException": None,
        "receipts": aggregate_receipts,
        "logsHash": logs_hash(tuple(aggregate_logs)),
        "gasUsed": q(cumulative_gas),
    }
    return project_runtime_outputs(
        side, runtime, rows, aggregate_result, post_alloc,
    )


def gas_registry_identity(name: str, reference_gas: int,
                          blanc_gas: int) -> Mapping[str, object]:
    delta = blanc_gas - reference_gas
    payload = {
        "row": name, "reference": reference_gas,
        "blanc": blanc_gas, "delta": delta,
    }
    registry_id = "BD-BPO2-GAS-" + canonical_json_sha256(payload)[:12].upper()
    marker = (
        f"<!-- {DEVIATION_MARKER_VERSION} id={registry_id} row={name} "
        f"reference={reference_gas} blanc={blanc_gas} delta={delta} -->"
    )
    return {"registryId": registry_id, "registryMarker": marker}


def validate_positive_gas_registry(
        increases: Sequence[Mapping[str, object]]) -> str:
    try:
        text = REGISTRY.read_text(encoding="utf-8")
    except OSError as exc:
        die(f"cannot read gas deviation registry: {exc}")
    actual = re.findall(
        rf"<!-- {re.escape(DEVIATION_MARKER_VERSION)} [^>]* -->", text
    )
    expected = [str(row["registryMarker"]) for row in increases]
    if len(actual) != len(set(actual)):
        die("current-mainnet gas registry markers are duplicated")
    if sorted(actual) != sorted(expected):
        missing = sorted(set(expected) - set(actual))
        stale = sorted(set(actual) - set(expected))
        die(f"current-mainnet gas registry markers differ: missing={missing}, stale={stale}")
    for marker in expected:
        matching = [line for line in text.splitlines() if marker in line]
        if len(matching) != 1 or not matching[0].lstrip().startswith("|") \
                or "[PENDING" in matching[0]:
            die("positive BPO2 gas delta lacks one completed deviation table row")
    return hashlib.sha256(text.encode()).hexdigest()


def cache_inputs() -> Mapping[str, object]:
    repo_files = tuple(REPO / relative for relative in CACHE_REPOSITORY_FILES)
    runtime_lock = REPO / CACHE_RUNTIME_LOCK
    runtime_digest = sha256_file(runtime_lock)
    return {
        "repositoryFiles": {
            str(path.relative_to(REPO)): sha256_file(path) for path in repo_files
        },
        "runtimeLock": {
            "relativePath": CACHE_RUNTIME_LOCK,
            "sha256": runtime_digest,
            "platforms": list(CACHE_RUNTIME_PLATFORMS),
        },
        "sharedGateOwnership": CACHE_OWNERSHIP,
    }


def artifact_document(reference: Mapping[str, object],
                      blanc: Mapping[str, object]) -> Mapping[str, object]:
    ref_runtime = bytes_identity(reference["runtime"])
    ref_creation = bytes_identity(reference["creation"])
    blanc_runtime = bytes_identity(blanc["runtime"])
    blanc_creation = bytes_identity(blanc["creation"])
    runtime_delta = int(blanc_runtime["byteLength"]) - int(ref_runtime["byteLength"])
    creation_delta = int(blanc_creation["byteLength"]) - int(ref_creation["byteLength"])
    if runtime_delta >= 0 or creation_delta >= 0:
        die("Blanc no longer strictly beats the reference artifact sizes")
    return {
        "reference": {"runtime": ref_runtime, "creation": ref_creation},
        "blanc": {"runtime": blanc_runtime, "creation": blanc_creation,
                  "selectorsAscending": list(blanc["selectors"])},
        "sizeComparison": {
            "blancMinusReferenceRuntimeBytes": runtime_delta,
            "blancMinusReferenceCreationBytes": creation_delta,
            "blancRuntimeStrictlySmaller": True,
            "blancCreationStrictlySmaller": True,
        },
    }


def compose_creation(reference: Mapping[str, object],
                     blanc: Mapping[str, object]) -> Mapping[str, object]:
    reference_gas = reference["gas"]
    blanc_gas = blanc["gas"]
    deltas = {
        key: int(blanc_gas[key]) - int(reference_gas[key])
        for key in CREATION_DOMINANCE_KEYS
    }
    dominance = {
        "requiredNonPositive": list(CREATION_DOMINANCE_KEYS),
        "transactionGasUsedNonPositive": deltas["transactionGasUsed"] <= 0,
        "netConstructorExecutionGasAfterRefundNonPositive": (
            deltas["netConstructorExecutionGasAfterRefund"] <= 0
        ),
        "satisfied": all(value <= 0 for value in deltas.values()),
    }
    if not dominance["satisfied"]:
        die(f"Blanc constructor gas dominance failed: {deltas}")
    if reference["logicalState"] != blanc["logicalState"]:
        die("constructor projected logical states differ")
    if reference["transaction"]["createTarget"] != blanc["transaction"]["createTarget"]:
        die("fresh constructor target identities differ")
    return {
        "assertions": list(CREATION_ASSERTIONS),
        "executionCount": 2,
        "freshWorldPerSide": True,
        "reference": reference,
        "blanc": blanc,
        "projection": {
            "logicalStateAgreement": True,
            "rawStorageEqualityClaim": False,
            "installedRuntimeEqualityClaim": False,
            "sameCreateTarget": True,
        },
        "deltas": deltas,
        "dominance": dominance,
    }


def compose_runtime(rows: Sequence[RuntimeRow], reference: Mapping[str, object],
                    blanc: Mapping[str, object], *, check_registry: bool = True) \
        -> Mapping[str, object]:
    reference_rows = reference["rows"]
    blanc_rows = blanc["rows"]
    if len(reference_rows) != len(rows) or len(blanc_rows) != len(rows):
        die("runtime result cardinality differs")
    descriptors = []
    increases = []
    for index, spec in enumerate(rows):
        ref = reference_rows[index]
        bla = blanc_rows[index]
        if ref["name"] != spec.name or bla["name"] != spec.name:
            die("runtime result row order differs")
        expected_status = spec.succeeds
        if ref["receiptSucceeded"] is not expected_status \
                or bla["receiptSucceeded"] is not expected_status:
            die(f"{spec.name}: reference/Blanc receipt status differs")
        reference_gas = int(ref["gasUsed"])
        blanc_gas = int(bla["gasUsed"])
        delta = blanc_gas - reference_gas
        row = {
            "name": spec.name,
            "endpoint": spec.endpoint,
            "input": {
                "calldataBytes": len(spec.calldata),
                "calldataSha256": hashlib.sha256(spec.calldata).hexdigest(),
                "value": q(spec.value),
                "sameInputBothSides": True,
            },
            "expectedReceiptSucceeded": expected_status,
            "creditedChannels": list(spec.credited_channels),
            "returndataCredited": False,
            "reference": {
                "receiptSucceeded": ref["receiptSucceeded"],
                "gasUsed": reference_gas,
            },
            "blanc": {
                "receiptSucceeded": bla["receiptSucceeded"],
                "gasUsed": blanc_gas,
            },
            "blancMinusReferenceGas": delta,
        }
        if delta > 0:
            identity = gas_registry_identity(spec.name, reference_gas, blanc_gas)
            increase = {
                "row": spec.name,
                "referenceGas": reference_gas,
                "blancGas": blanc_gas,
                "delta": delta,
                **identity,
            }
            increases.append(increase)
            row["completedDeviation"] = identity
        else:
            row["completedDeviation"] = None
        descriptors.append(row)
    registry_sha = (validate_positive_gas_registry(increases)
                    if check_registry else sha256_file(REGISTRY))
    reference_deposit = reference["depositEvidence"]
    blanc_deposit = blanc["depositEvidence"]
    if reference_deposit["log"] != blanc_deposit["log"] \
            or reference_deposit["logsHash"] != blanc_deposit["logsHash"] \
            or reference_deposit["logicalState"] != blanc_deposit["logicalState"]:
        die("runtime deposit projected log/state semantics differ")
    for side in (reference_deposit, blanc_deposit):
        eth = side["eth"]
        if eth["callerPrincipalDeltaExcludingFees"] != q(ETHER) \
                or eth["contractInitial"] != "0x0" \
                or eth["contractFinal"] != q(ETHER) \
                or eth["topLevelValue"] != q(ETHER):
            die("runtime deposit ETH/value projection differs")
    return {
        "transactionCountPerSide": len(rows),
        "sameOrderedInputs": True,
        "rows": descriptors,
        "depositProjection": {
            "exactLogTopicDataAgreement": True,
            "logicalStateAgreement": True,
            "ethValueAgreementExcludingSideSpecificFees": True,
            "rawStorageEqualityClaim": False,
            "reference": reference_deposit,
            "blanc": blanc_deposit,
        },
        "gasPolicy": {
            "allRowsRecorded": True,
            "positiveDeltas": increases,
            "deviationMarkerVersion": DEVIATION_MARKER_VERSION,
            "registryFile": "BEACON_DEPOSIT_DEVIATIONS.md",
            "registrySha256": registry_sha,
            "obligation": (
                "a positive Blanc delta fails before manifest acceptance unless one "
                "exact marker exists on a completed non-PENDING deviation table row; "
                "the generator never auto-admits or edits a deviation"
            ),
        },
        "returndataBoundary": {
            "creditedOnBpo2Rows": False,
            "owner": "scripts/check-beacon-deposit-differential.sh",
            "fork": "Prague",
            "statement": HISTORICAL_BOUNDARY,
        },
    }


def profile_document(profile: Mapping[str, object],
                     verified: Mapping[str, object]) -> Mapping[str, object]:
    if profile_claims(profile) != PROFILE_CLAIMS:
        die("shared current-mainnet profile claims differ")
    target = profile["target"]
    execution = profile["execution"]
    compiler = profile["compiler"]
    return {
        "profileFile": "scripts/current-mainnet-target.json",
        "profileSha256": sha256_file(PROFILE_PATH),
        "claims": list(PROFILE_CLAIMS),
        "execution": {
            "fork": execution["fork"],
            "module": execution["module"],
            "chainId": execution["chainId"],
            "reward": execution["reward"],
            "mainnetActivationTimestamp": MAINNET_BPO2_ACTIVATION_TIMESTAMP,
        },
        "compiler": {
            "logicalFork": compiler["logicalFork"],
            "testingBackend": compiler["testingBackend"],
            "externalSolcInvoked": compiler["externalSolcInvoked"],
            "artifactCompiler": "Blanc",
        },
        "target": {
            "repository": target["repository"],
            "rootEnv": target["rootEnv"],
            "defaultRoot": target["defaultRoot"],
            "checkoutCommit": verified["head"],
            "upstreamCommit": verified["upstream"],
            "overlayPaths": verified["overlayPaths"],
            "overlayDiffSha256": verified["overlayDiffSha256"],
            "pythonIdentity": target["pythonIdentity"],
        },
    }


def build_manifest(profile: Mapping[str, object], verified: Mapping[str, object],
                   reference_artifacts: Mapping[str, object],
                   blanc_artifacts: Mapping[str, object],
                   reference_creation: Mapping[str, object],
                   blanc_creation: Mapping[str, object],
                   reference_runtime: Mapping[str, object],
                   blanc_runtime: Mapping[str, object]) -> Mapping[str, object]:
    rows = runtime_rows()
    creation = compose_creation(reference_creation, blanc_creation)
    runtime = compose_runtime(rows, reference_runtime, blanc_runtime)
    return assemble_manifest(
        profile_document(profile, verified), cache_inputs(),
        artifact_document(reference_artifacts, blanc_artifacts), creation, runtime,
    )


def assemble_manifest(profile: Mapping[str, object], cache: Mapping[str, object],
                      artifacts: Mapping[str, object],
                      creation: Mapping[str, object],
                      runtime: Mapping[str, object]) -> Mapping[str, object]:
    rows = runtime_rows()
    return {
        "schema": MANIFEST_SCHEMA,
        "channel": "finite-bpo2-execution-witness-not-a-lean-premise",
        "profile": profile,
        "cacheInputs": cache,
        "oracle": {
            "sourceSha256": SOURCE_SHA256,
            "artifactJsonSha256": ARTIFACT_SHA256,
            "deployedRuntimeTextSha256": DEPLOYED_RUNTIME_TEXT_SHA256,
            "referenceBytecodeVerifiedCorrect": False,
        },
        "artifacts": artifacts,
        "executionBoundary": {
            "topLevelTransactions": True,
            "executionFork": "BPO2",
            "forkCallerOverrideAvailable": False,
            "constructorWorlds": "separate fresh state per side",
            "runtimeWorlds": "same ordered seven-transition BPO2 state chain per side",
            "runtimeStateTestMode": True,
            "runtimeT8nExecutionsPerSide": len(rows),
            "transactionGasLimit": GAS_LIMIT,
            "eip7825TransactionGasLimitCap": TX_MAX_GAS_LIMIT,
            "allTransactionsWithinCap": GAS_LIMIT <= TX_MAX_GAS_LIMIT,
            "historicalPragueComplement": HISTORICAL_BOUNDARY,
            "glamsterdamBaseline": False,
        },
        "counts": {
            "creationExecutions": 2,
            "runtimeTransactionsPerSide": len(rows),
            "runtimeTransactionsTotal": 2 * len(rows),
            "runtimeRows": len(rows),
            "creditedChannels": len(REQUIRED_CHANNELS),
            "staticInventoryFalsifiers": STATIC_INVENTORY_FALSIFIERS,
            "apiBoundaryFalsifiers": API_BOUNDARY_FALSIFIERS,
            "rawChannelFalsifiers": RAW_CHANNEL_FALSIFIERS,
            "manifestChannelFalsifiers": MANIFEST_CHANNEL_FALSIFIERS,
            "registryFalsifiers": REGISTRY_FALSIFIERS,
            "manifestFalsifiers": MANIFEST_FALSIFIERS,
        },
        "creation": creation,
        "runtime": runtime,
        "falsifiers": {
            "staticInventory": STATIC_INVENTORY_FALSIFIERS,
            "apiBoundary": API_BOUNDARY_FALSIFIERS,
            "rawChannelLiveness": RAW_CHANNEL_FALSIFIERS,
            "manifestChannelValidation": MANIFEST_CHANNEL_FALSIFIERS,
            "registryLiveness": REGISTRY_FALSIFIERS,
            "manifestOwnership": MANIFEST_FALSIFIERS,
            "channelClasses": list(REQUIRED_CHANNELS),
            "manifestClasses": list(MANIFEST_CLASSES),
        },
        "explicitLimits": [
            "finite BPO2 transactions, not universal equivalence or liveness",
            "reference bytecode is an executed oracle, not a verified program",
            "view/support/no-match rows credit only receipt status and charged gas",
            "exact returndata remains exclusively in the preserved Prague differential",
            "raw storage equality is excluded; each layout is projected logically",
            "constructor remainder is net receipt-charged execution after any refund; the t8n result does not expose its refund counter",
        ],
    }


def is_sha256(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def validate_cache_manifest(cache: object) -> None:
    if not isinstance(cache, dict) or set(cache) != {
        "repositoryFiles", "runtimeLock", "sharedGateOwnership",
    }:
        die("current-mainnet manifest cache input shape differs")
    repository = cache.get("repositoryFiles")
    if not isinstance(repository, dict) \
            or set(repository) != set(CACHE_REPOSITORY_FILES) \
            or any(not is_sha256(value) for value in repository.values()):
        die("current-mainnet manifest repository fingerprints differ")
    runtime_lock = cache.get("runtimeLock")
    if not isinstance(runtime_lock, dict) or set(runtime_lock) != {
        "relativePath", "sha256", "platforms",
    } or runtime_lock.get("relativePath") != CACHE_RUNTIME_LOCK \
            or not is_sha256(runtime_lock.get("sha256")) \
            or runtime_lock.get("platforms") != list(CACHE_RUNTIME_PLATFORMS):
        die("current-mainnet manifest runtime-lock binding differs")
    if repository.get(CACHE_RUNTIME_LOCK) != runtime_lock["sha256"]:
        die("current-mainnet manifest runtime-lock digest ownership differs")
    if cache.get("sharedGateOwnership") != CACHE_OWNERSHIP:
        die("current-mainnet manifest shared-gate ownership differs")


def validate_creation_side_manifest(side: object, label: str) -> None:
    if not isinstance(side, dict) or set(side) != {
        "side", "transaction", "receiptSucceeded", "target", "sender",
        "logicalState", "logs", "limits", "gas",
    } or side.get("side") != label:
        die(f"manifest creation/{label} shape differs")
    if side.get("receiptSucceeded") is not True:
        die(f"manifest creation/{label} receipt did not succeed")
    runtime_length = (REFERENCE_RUNTIME_BYTES if label == "reference"
                      else BLANC_RUNTIME_BYTES)
    runtime_sha = (REFERENCE_RUNTIME_SHA256 if label == "reference"
                   else BLANC_RUNTIME_SHA256)
    creation_length = (REFERENCE_CREATION_BYTES if label == "reference"
                       else BLANC_CREATION_BYTES)
    creation_sha = (REFERENCE_CREATION_SHA256 if label == "reference"
                    else BLANC_CREATION_SHA256)
    gas = side.get("gas")
    if not isinstance(gas, dict):
        die(f"manifest creation/{label} gas shape differs")
    required_gas = {
        "zeroCalldataBytes", "nonzeroCalldataBytes", "calldataTokens",
        "baseGas", "createSurchargeGas", "standardTokenGas",
        "eip3860InitcodeWordGas", "regularIntrinsicGas", "calldataFloorGas",
        "calldataFloorBinding", "calldataFloorSettlementExtraGas",
        "codeDepositGas", "netConstructorExecutionGasAfterRefund",
        "transactionGasUsed", "refundCounterExposedByT8n",
        "constructorStaticBasis", "decomposition",
    }
    if set(gas) != required_gas:
        die(f"manifest creation/{label} gas keys differ")
    integer_keys = required_gas - {
        "calldataFloorBinding", "refundCounterExposedByT8n",
        "constructorStaticBasis", "decomposition",
    }
    if any(type(gas.get(key)) is not int for key in integer_keys):
        die(f"manifest creation/{label} gas field is not an integer")
    if gas["calldataFloorBinding"] is not False \
            or gas["calldataFloorSettlementExtraGas"] != 0 \
            or gas["transactionGasUsed"] <= gas["calldataFloorGas"] \
            or gas["transactionGasUsed"] != (
                gas["regularIntrinsicGas"] + gas["codeDepositGas"]
                + gas["netConstructorExecutionGasAfterRefund"]
            ) or gas["netConstructorExecutionGasAfterRefund"] < 0:
        die(f"manifest creation/{label} gas decomposition/floor differs")
    if gas["zeroCalldataBytes"] + gas["nonzeroCalldataBytes"] != creation_length \
            or gas["eip3860InitcodeWordGas"] \
            != INITCODE_WORD_GAS * ((creation_length + 31) // 32) \
            or gas["codeDepositGas"] != runtime_length * CODE_DEPOSIT_GAS_PER_BYTE:
        die(f"manifest creation/{label} initcode/deposit gas basis differs")
    tokens = (gas["zeroCalldataBytes"]
              + TX_DATA_TOKEN_STANDARD * gas["nonzeroCalldataBytes"])
    if gas["baseGas"] != TX_BASE_GAS \
            or gas["createSurchargeGas"] != TX_CREATE_GAS \
            or gas["calldataTokens"] != tokens \
            or gas["standardTokenGas"] != TX_DATA_TOKEN_STANDARD * tokens \
            or gas["regularIntrinsicGas"] != (
                TX_BASE_GAS + TX_CREATE_GAS + gas["standardTokenGas"]
                + gas["eip3860InitcodeWordGas"]
            ) or gas["calldataFloorGas"] != (
                TX_BASE_GAS + TX_DATA_TOKEN_FLOOR * tokens
            ):
        die(f"manifest creation/{label} intrinsic arithmetic differs")
    if gas.get("refundCounterExposedByT8n") is not False:
        die(f"manifest creation/{label} refund boundary differs")
    static = gas.get("constructorStaticBasis")
    expected_static_doc = CONSTRUCTOR_STATIC_EXPECTED[label]
    expected_static = (
        expected_static_doc["prefixBytes"], expected_static_doc["sstoreSites"],
        expected_static_doc["staticcallSites"], expected_static_doc["codecopySites"],
    )
    if not isinstance(static, dict) or (
        static.get("prefixBytes"), static.get("sstoreSites"),
        static.get("staticcallSites"), static.get("codecopySites"),
    ) != expected_static or static.get("refundInferenceCredited") is not False:
        die(f"manifest creation/{label} constructor static basis differs")
    limits = side.get("limits")
    transaction_doc = side.get("transaction")
    target = side.get("target")
    expected_limits = {
        "runtimeBytes": runtime_length, "eip170Limit": EIP170_LIMIT,
        "runtimeWithinLimit": True,
        "initcodeBytes": creation_length, "eip3860Limit": EIP3860_LIMIT,
        "initcodeWithinLimit": True,
        "transactionGasLimit": GAS_LIMIT,
        "eip7825TransactionGasLimitCap": TX_MAX_GAS_LIMIT,
        "transactionWithinLimit": True,
    }
    expected_transaction = {
        "type": 0, "chainId": 1, "nonce": 0, "sender": SENDER,
        "createTarget": CREATE_TARGET, "value": "0x0", "gasLimit": GAS_LIMIT,
        "gasPrice": GAS_PRICE,
        "input": {"byteLength": creation_length, "sha256": creation_sha},
    }
    expected_sender = {
        "address": SENDER, "nonce": 1,
        "balance": q(SENDER_BALANCE - gas["transactionGasUsed"] * GAS_PRICE),
    }
    if limits != expected_limits \
            or transaction_doc != expected_transaction \
            or side.get("sender") != expected_sender \
            or not isinstance(target, dict) \
            or target.get("address") != CREATE_TARGET \
            or target.get("nonce") != 1 or target.get("balance") != "0x0" \
            or target.get("code") \
            != {"byteLength": runtime_length, "sha256": runtime_sha} \
            or target.get("storage") != {
                q(key): q(value)
                for key, value in expected_constructor_storage(label).items()
            } \
            or side.get("logicalState") \
            != logical_state(label, expected_constructor_storage(label)) \
            or side.get("logs") != {
                "count": 0, "logsHash": logs_hash(()), "receiptBloom": "0x0"
            }:
        die(f"manifest creation/{label} target/limit identity differs")


def validate_manifest_semantics(document: Mapping[str, object]) -> None:
    top_keys = {
        "schema", "channel", "profile", "cacheInputs", "oracle", "artifacts",
        "executionBoundary", "counts", "creation", "runtime", "falsifiers",
        "explicitLimits",
    }
    if set(document) != top_keys or document.get("schema") != MANIFEST_SCHEMA \
            or document.get("channel") \
            != "finite-bpo2-execution-witness-not-a-lean-premise":
        die("current-mainnet manifest top-level schema differs")
    profile = document.get("profile")
    if not isinstance(profile, dict) or profile.get("claims") != list(PROFILE_CLAIMS) \
            or profile.get("execution", {}).get("fork") != "BPO2" \
            or profile.get("execution", {}).get("module") != "ethereum.forks.bpo2" \
            or profile.get("compiler", {}).get("logicalFork") != "Osaka" \
            or profile.get("compiler", {}).get("externalSolcInvoked") is not False \
            or not is_sha256(profile.get("profileSha256")):
        die("current-mainnet manifest profile claims differ")
    boundary = document.get("executionBoundary")
    if not isinstance(boundary, dict) \
            or boundary.get("executionFork") != "BPO2" \
            or boundary.get("forkCallerOverrideAvailable") is not False \
            or boundary.get("constructorWorlds") != "separate fresh state per side" \
            or boundary.get("runtimeWorlds") \
            != "same ordered seven-transition BPO2 state chain per side" \
            or boundary.get("runtimeStateTestMode") is not True \
            or boundary.get("runtimeT8nExecutionsPerSide") \
            != len(REQUIRED_ROW_NAMES) \
            or boundary.get("transactionGasLimit") != GAS_LIMIT \
            or boundary.get("eip7825TransactionGasLimitCap") \
            != TX_MAX_GAS_LIMIT \
            or boundary.get("allTransactionsWithinCap") is not True \
            or boundary.get("historicalPragueComplement") != HISTORICAL_BOUNDARY \
            or boundary.get("glamsterdamBaseline") is not False:
        die("current-mainnet manifest execution boundary differs")
    artifacts = document.get("artifacts")
    expected_artifacts = expected_artifact_document()
    if artifacts != expected_artifacts:
        die("current-mainnet manifest artifact/size identity differs")
    counts = document.get("counts")
    if counts != {
        "creationExecutions": 2,
        "runtimeTransactionsPerSide": len(REQUIRED_ROW_NAMES),
        "runtimeTransactionsTotal": 2 * len(REQUIRED_ROW_NAMES),
        "runtimeRows": len(REQUIRED_ROW_NAMES),
        "creditedChannels": len(REQUIRED_CHANNELS),
        "staticInventoryFalsifiers": STATIC_INVENTORY_FALSIFIERS,
        "apiBoundaryFalsifiers": API_BOUNDARY_FALSIFIERS,
        "rawChannelFalsifiers": RAW_CHANNEL_FALSIFIERS,
        "manifestChannelFalsifiers": MANIFEST_CHANNEL_FALSIFIERS,
        "registryFalsifiers": REGISTRY_FALSIFIERS,
        "manifestFalsifiers": MANIFEST_FALSIFIERS,
    }:
        die("current-mainnet manifest counts differ")
    creation = document.get("creation")
    if not isinstance(creation, dict) or set(creation) != {
        "assertions", "executionCount", "freshWorldPerSide", "reference",
        "blanc", "projection", "deltas", "dominance",
    } or creation.get("assertions") != list(CREATION_ASSERTIONS) \
            or creation.get("executionCount") != 2 \
            or creation.get("freshWorldPerSide") is not True:
        die("current-mainnet manifest creation ownership differs")
    validate_creation_side_manifest(creation["reference"], "reference")
    validate_creation_side_manifest(creation["blanc"], "blanc")
    expected_deltas = {
        key: creation["blanc"]["gas"][key] - creation["reference"]["gas"][key]
        for key in CREATION_DOMINANCE_KEYS
    }
    expected_dominance = {
        "requiredNonPositive": list(CREATION_DOMINANCE_KEYS),
        "transactionGasUsedNonPositive": expected_deltas["transactionGasUsed"] <= 0,
        "netConstructorExecutionGasAfterRefundNonPositive": (
            expected_deltas["netConstructorExecutionGasAfterRefund"] <= 0
        ),
        "satisfied": all(delta <= 0 for delta in expected_deltas.values()),
    }
    if creation.get("deltas") != expected_deltas \
            or creation.get("dominance") != expected_dominance \
            or expected_dominance["satisfied"] is not True:
        die("current-mainnet manifest constructor dominance differs or failed")
    projection = creation.get("projection")
    if projection != {
        "logicalStateAgreement": True, "rawStorageEqualityClaim": False,
        "installedRuntimeEqualityClaim": False, "sameCreateTarget": True,
    } or creation["reference"]["logicalState"] != creation["blanc"]["logicalState"]:
        die("current-mainnet manifest constructor projection differs")
    runtime = document.get("runtime")
    if not isinstance(runtime, dict) or set(runtime) != {
        "transactionCountPerSide", "sameOrderedInputs", "rows",
        "depositProjection", "gasPolicy", "returndataBoundary",
    } or runtime.get("transactionCountPerSide") != len(REQUIRED_ROW_NAMES) \
            or runtime.get("sameOrderedInputs") is not True:
        die("current-mainnet manifest runtime ownership differs")
    manifest_rows = runtime.get("rows")
    if not isinstance(manifest_rows, list) \
            or tuple(row.get("name") for row in manifest_rows
                     if isinstance(row, dict)) != REQUIRED_ROW_NAMES:
        die("current-mainnet manifest runtime row inventory differs")
    increases = []
    for spec, row in zip(runtime_rows(), manifest_rows):
        if not isinstance(row, dict) or row.get("creditedChannels") \
                != list(spec.credited_channels) \
                or row.get("returndataCredited") is not False \
                or row.get("expectedReceiptSucceeded") is not spec.succeeds \
                or row.get("reference", {}).get("receiptSucceeded") is not spec.succeeds \
                or row.get("blanc", {}).get("receiptSucceeded") is not spec.succeeds \
                or row.get("endpoint") != spec.endpoint \
                or row.get("input") != {
                    "calldataBytes": len(spec.calldata),
                    "calldataSha256": hashlib.sha256(spec.calldata).hexdigest(),
                    "value": q(spec.value),
                    "sameInputBothSides": True,
                }:
            die(f"current-mainnet manifest row {spec.name} status/channel differs")
        reference_gas = row.get("reference", {}).get("gasUsed")
        blanc_gas = row.get("blanc", {}).get("gasUsed")
        if type(reference_gas) is not int or type(blanc_gas) is not int \
                or reference_gas <= 0 or blanc_gas <= 0 \
                or row.get("blancMinusReferenceGas") != blanc_gas - reference_gas:
            die(f"current-mainnet manifest row {spec.name} gas differs")
        if blanc_gas > reference_gas:
            identity = gas_registry_identity(spec.name, reference_gas, blanc_gas)
            if row.get("completedDeviation") != identity:
                die(f"current-mainnet manifest row {spec.name} lacks deviation identity")
            increases.append({
                "row": spec.name, "referenceGas": reference_gas,
                "blancGas": blanc_gas, "delta": blanc_gas - reference_gas,
                **identity,
            })
        elif row.get("completedDeviation") is not None:
            die(f"current-mainnet manifest row {spec.name} has stale deviation identity")
    gas_policy = runtime.get("gasPolicy")
    if not isinstance(gas_policy, dict) \
            or gas_policy.get("allRowsRecorded") is not True \
            or gas_policy.get("positiveDeltas") != increases \
            or gas_policy.get("deviationMarkerVersion") != DEVIATION_MARKER_VERSION \
            or gas_policy.get("registryFile") != "BEACON_DEPOSIT_DEVIATIONS.md" \
            or not is_sha256(gas_policy.get("registrySha256")):
        die("current-mainnet manifest runtime gas policy differs")
    returndata = runtime.get("returndataBoundary")
    if returndata != {
        "creditedOnBpo2Rows": False,
        "owner": "scripts/check-beacon-deposit-differential.sh",
        "fork": "Prague",
        "statement": HISTORICAL_BOUNDARY,
    }:
        die("current-mainnet manifest historical-Prague boundary differs")
    deposit_projection = runtime.get("depositProjection")
    expected_event = expected_log()
    expected_event_doc = {
        "address": "0x" + expected_event[0].hex(),
        "topics": ["0x" + topic.hex() for topic in expected_event[1]],
        "data": "0x" + expected_event[2].hex(),
    }
    if not isinstance(deposit_projection, dict) \
            or deposit_projection.get("exactLogTopicDataAgreement") is not True \
            or deposit_projection.get("logicalStateAgreement") is not True \
            or deposit_projection.get("ethValueAgreementExcludingSideSpecificFees") is not True \
            or deposit_projection.get("rawStorageEqualityClaim") is not False \
            or deposit_projection.get("reference", {}).get("log") \
            != deposit_projection.get("blanc", {}).get("log") \
            or deposit_projection.get("reference", {}).get("logicalState") \
            != deposit_projection.get("blanc", {}).get("logicalState") \
            or deposit_projection.get("reference", {}).get("log") != expected_event_doc:
        die("current-mainnet manifest deposit projection differs")
    for label in ("reference", "blanc"):
        evidence = deposit_projection[label]
        expected_storage = expected_runtime_final_storage(label)
        gas_total = sum(int(row[label]["gasUsed"]) for row in manifest_rows)
        expected_eth = {
            "callerInitial": q(SENDER_BALANCE),
            "callerFinal": q(SENDER_BALANCE - ETHER - gas_total * GAS_PRICE),
            "callerPrincipalDeltaExcludingFees": q(ETHER),
            "contractInitial": "0x0", "contractFinal": q(ETHER),
            "topLevelValue": q(ETHER), "fees": q(gas_total * GAS_PRICE),
        }
        runtime_identity = {
            "byteLength": (REFERENCE_RUNTIME_BYTES if label == "reference"
                           else BLANC_RUNTIME_BYTES),
            "sha256": (REFERENCE_RUNTIME_SHA256 if label == "reference"
                       else BLANC_RUNTIME_SHA256),
        }
        if evidence.get("logCount") != 1 \
                or evidence.get("log") != expected_event_doc \
                or evidence.get("logsHash") != logs_hash((expected_event,)) \
                or evidence.get("logicalState") != logical_state(label, expected_storage) \
                or evidence.get("rawStorage") != {
                    q(key): q(value) for key, value in expected_storage.items()
                } \
                or evidence.get("eth") != expected_eth \
                or evidence.get("targetNonce") != 1 \
                or evidence.get("installedRuntime") != runtime_identity:
            die(f"current-mainnet manifest deposit/{label} evidence differs")
    validate_cache_manifest(document.get("cacheInputs"))
    falsifiers = document.get("falsifiers")
    if not isinstance(falsifiers, dict) \
            or falsifiers.get("staticInventory") != STATIC_INVENTORY_FALSIFIERS \
            or falsifiers.get("apiBoundary") != API_BOUNDARY_FALSIFIERS \
            or falsifiers.get("rawChannelLiveness") != RAW_CHANNEL_FALSIFIERS \
            or falsifiers.get("manifestChannelValidation") \
            != MANIFEST_CHANNEL_FALSIFIERS \
            or falsifiers.get("registryLiveness") != REGISTRY_FALSIFIERS \
            or falsifiers.get("channelClasses") != list(REQUIRED_CHANNELS) \
            or falsifiers.get("manifestOwnership") != MANIFEST_FALSIFIERS \
            or falsifiers.get("manifestClasses") != list(MANIFEST_CLASSES):
        die("current-mainnet manifest falsifier ownership differs")


def validate_manifest(document: Mapping[str, object],
                      expected: Mapping[str, object]) -> None:
    validate_manifest_semantics(document)
    if document != expected:
        die("current-mainnet manifest differs from fresh BPO2 execution evidence")


def expected_artifact_document() -> Mapping[str, object]:
    return {
        "reference": {
            "runtime": {"byteLength": REFERENCE_RUNTIME_BYTES,
                        "sha256": REFERENCE_RUNTIME_SHA256},
            "creation": {"byteLength": REFERENCE_CREATION_BYTES,
                         "sha256": REFERENCE_CREATION_SHA256},
        },
        "blanc": {
            "runtime": {"byteLength": BLANC_RUNTIME_BYTES,
                        "sha256": BLANC_RUNTIME_SHA256},
            "creation": {"byteLength": BLANC_CREATION_BYTES,
                         "sha256": BLANC_CREATION_SHA256},
            "selectorsAscending": list(EXPECTED_SELECTORS),
        },
        "sizeComparison": {
            "blancMinusReferenceRuntimeBytes": (
                BLANC_RUNTIME_BYTES - REFERENCE_RUNTIME_BYTES),
            "blancMinusReferenceCreationBytes": (
                BLANC_CREATION_BYTES - REFERENCE_CREATION_BYTES),
            "blancRuntimeStrictlySmaller": True,
            "blancCreationStrictlySmaller": True,
        },
    }


def synthetic_creation_side(label: str, residual: int) -> Mapping[str, object]:
    runtime_length = (REFERENCE_RUNTIME_BYTES if label == "reference"
                      else BLANC_RUNTIME_BYTES)
    runtime_sha = (REFERENCE_RUNTIME_SHA256 if label == "reference"
                   else BLANC_RUNTIME_SHA256)
    creation_length = (REFERENCE_CREATION_BYTES if label == "reference"
                       else BLANC_CREATION_BYTES)
    creation_sha = (REFERENCE_CREATION_SHA256 if label == "reference"
                    else BLANC_CREATION_SHA256)
    components = intrinsic_components(bytes([1]) * creation_length)
    code_deposit = runtime_length * CODE_DEPOSIT_GAS_PER_BYTE
    total = int(components["regularIntrinsicGas"]) + code_deposit + residual
    expected_storage = expected_constructor_storage(label)
    static_expected = CONSTRUCTOR_STATIC_EXPECTED[label]
    static_basis = {
        **static_expected,
        "forbiddenExternalCreateDeleteSites": {
            "CALL": [], "CALLCODE": [], "DELEGATECALL": [],
            "CREATE": [], "CREATE2": [], "SELFDESTRUCT": [],
        },
        "refundInferenceCredited": False,
    }
    target = CREATE_TARGET
    return {
        "side": label,
        "transaction": {
            "type": 0, "chainId": 1, "nonce": 0, "sender": SENDER,
            "createTarget": target, "value": "0x0", "gasLimit": GAS_LIMIT,
            "gasPrice": GAS_PRICE,
            "input": {"byteLength": creation_length, "sha256": creation_sha},
        },
        "receiptSucceeded": True,
        "target": {
            "address": target, "nonce": 1, "balance": "0x0",
            "code": {"byteLength": runtime_length, "sha256": runtime_sha},
            "storage": {q(key): q(value) for key, value in expected_storage.items()},
        },
        "sender": {
            "address": SENDER, "nonce": 1,
            "balance": q(SENDER_BALANCE - total * GAS_PRICE),
        },
        "logicalState": logical_state(label, expected_storage),
        "logs": {"count": 0, "logsHash": logs_hash(()), "receiptBloom": "0x0"},
        "limits": {
            "runtimeBytes": runtime_length, "eip170Limit": EIP170_LIMIT,
            "runtimeWithinLimit": True,
            "initcodeBytes": creation_length, "eip3860Limit": EIP3860_LIMIT,
            "initcodeWithinLimit": True,
            "transactionGasLimit": GAS_LIMIT,
            "eip7825TransactionGasLimitCap": TX_MAX_GAS_LIMIT,
            "transactionWithinLimit": True,
        },
        "gas": {
            **components,
            "calldataFloorBinding": False,
            "calldataFloorSettlementExtraGas": 0,
            "codeDepositGas": code_deposit,
            "netConstructorExecutionGasAfterRefund": residual,
            "transactionGasUsed": total,
            "refundCounterExposedByT8n": False,
            "constructorStaticBasis": static_basis,
            "decomposition": (
                "transactionGasUsed = regularIntrinsicGas + codeDepositGas + "
                "netConstructorExecutionGasAfterRefund; the remainder is receipt-"
                "charged constructor execution after any transaction refund because "
                "this t8n result does not expose the refund counter; calldataFloorGas "
                "is a checked alternative floor, not an additive component"
            ),
        },
    }


def synthetic_runtime_side(label: str, gas: Sequence[int]) -> Mapping[str, object]:
    rows = runtime_rows()
    storage = expected_runtime_final_storage(label)
    runtime_length = (REFERENCE_RUNTIME_BYTES if label == "reference"
                      else BLANC_RUNTIME_BYTES)
    runtime_sha = (REFERENCE_RUNTIME_SHA256 if label == "reference"
                   else BLANC_RUNTIME_SHA256)
    event = expected_log()
    total = sum(gas)
    return {
        "side": label,
        "rows": [{
            "name": row.name, "receiptSucceeded": row.succeeds,
            "gasUsed": gas[index],
            "receiptBloom": q(log_bloom((event,)) if index == 0 else 0),
        } for index, row in enumerate(rows)],
        "depositEvidence": {
            "logCount": 1,
            "log": {
                "address": "0x" + event[0].hex(),
                "topics": ["0x" + topic.hex() for topic in event[1]],
                "data": "0x" + event[2].hex(),
            },
            "logsHash": logs_hash((event,)),
            "logicalState": logical_state(label, storage),
            "rawStorage": {q(key): q(value) for key, value in storage.items()},
            "eth": {
                "callerInitial": q(SENDER_BALANCE),
                "callerFinal": q(SENDER_BALANCE - ETHER - total * GAS_PRICE),
                "callerPrincipalDeltaExcludingFees": q(ETHER),
                "contractInitial": "0x0", "contractFinal": q(ETHER),
                "topLevelValue": q(ETHER), "fees": q(total * GAS_PRICE),
            },
            "targetNonce": 1,
            "installedRuntime": {"byteLength": runtime_length, "sha256": runtime_sha},
        },
        "blockGasUsed": total,
    }


def bloom_hex(value: int) -> str:
    if not 0 <= value < 2**2048:
        die("bloom value is outside 2048 bits")
    return "0x" + value.to_bytes(256, "big").hex()


def synthetic_raw_runtime(side: str, runtime: bytes,
                          gas: Sequence[int]) -> Tuple[Mapping[str, object],
                                                       Mapping[str, object]]:
    rows = runtime_rows()
    if len(gas) != len(rows):
        die("synthetic raw-runtime gas vector differs")
    entry = expected_log()
    address, topics, data = entry
    cumulative = 0
    receipts: List[Mapping[str, object]] = []
    for index, row in enumerate(rows):
        cumulative += int(gas[index])
        logs = ([{
            "address": "0x" + address.hex(),
            "topics": ["0x" + topic.hex() for topic in topics],
            "data": "0x" + data.hex(),
        }] if index == 0 else [])
        receipts.append({
            "status": "0x1" if row.succeeds else "0x0",
            "cumulativeGasUsed": q(cumulative),
            "bloom": bloom_hex(log_bloom((entry,)) if index == 0 else 0),
            "logs": logs,
        })
    expected_storage = expected_runtime_final_storage(side)
    post_alloc = {
        SENDER: account(
            nonce=len(rows),
            balance=SENDER_BALANCE - ETHER - cumulative * GAS_PRICE,
        ),
        CONTRACT: account(
            nonce=1, balance=ETHER, code=runtime, storage=expected_storage,
        ),
    }
    result = {
        "rejected": [], "blockException": None, "receipts": receipts,
        "logsHash": logs_hash((entry,)), "gasUsed": q(cumulative),
    }
    return result, post_alloc


def raw_channel_falsifiers() -> int:
    side = "blanc"
    runtime = bytes(BLANC_RUNTIME_BYTES)
    rows = runtime_rows()
    gas = (90_000, 80_000, 29_000, 24_000, 24_100, 24_200, 21_000)
    result, post_alloc = synthetic_raw_runtime(side, runtime, gas)
    baseline = project_runtime_outputs(side, runtime, rows, result, post_alloc)
    mutants: List[Tuple[str, Mapping[str, object], Mapping[str, object]]] = []
    broken_result = copy.deepcopy(result)
    broken_alloc = copy.deepcopy(post_alloc)
    broken_result["receipts"][0]["status"] = "0x0"
    mutants.append(("status", broken_result, broken_alloc))
    broken_result = copy.deepcopy(result)
    broken_alloc = copy.deepcopy(post_alloc)
    first_gas = parse_quantity(
        broken_result["receipts"][0]["cumulativeGasUsed"],
        "synthetic gas falsifier",
    )
    broken_result["receipts"][0]["cumulativeGasUsed"] = q(first_gas + 1)
    mutants.append(("gas", broken_result, broken_alloc))
    broken_result = copy.deepcopy(result)
    broken_alloc = copy.deepcopy(post_alloc)
    broken_result["receipts"][0]["logs"][0]["data"] = "0x00"
    mutants.append(("deposit-log", broken_result, broken_alloc))
    broken_result = copy.deepcopy(result)
    broken_alloc = copy.deepcopy(post_alloc)
    target = find_account(broken_alloc, CONTRACT, "synthetic storage falsifier")
    del target["storage"][next(iter(target["storage"]))]
    mutants.append(("deposit-storage", broken_result, broken_alloc))
    broken_result = copy.deepcopy(result)
    broken_alloc = copy.deepcopy(post_alloc)
    target = find_account(broken_alloc, CONTRACT, "synthetic ETH falsifier")
    target["balance"] = "0x0"
    mutants.append(("deposit-eth", broken_result, broken_alloc))
    for label, mutant_result, mutant_alloc in mutants:
        try:
            observed = project_runtime_outputs(
                side, runtime, rows, mutant_result, mutant_alloc,
            )
        except RuntimeError:
            continue
        if observed != baseline:
            continue
        die(f"raw credited-channel falsifier was invisible: {label}")
    if len(mutants) != RAW_CHANNEL_FALSIFIERS:
        die("raw credited-channel falsifier count differs")
    return len(mutants)


def synthetic_manifest() -> Mapping[str, object]:
    reference_creation = synthetic_creation_side("reference", 500_000)
    blanc_creation = synthetic_creation_side("blanc", 400_000)
    creation = compose_creation(reference_creation, blanc_creation)
    reference_runtime = synthetic_runtime_side(
        "reference", (100_000, 90_000, 30_000, 25_000, 25_100, 25_200, 22_000)
    )
    blanc_runtime = synthetic_runtime_side(
        "blanc", (90_000, 80_000, 29_000, 24_000, 24_100, 24_200, 21_000)
    )
    runtime = compose_runtime(
        runtime_rows(), reference_runtime, blanc_runtime, check_registry=False,
    )
    profile = {
        "profileFile": "scripts/current-mainnet-target.json",
        "profileSha256": "0" * 64,
        "claims": list(PROFILE_CLAIMS),
        "execution": {
            "fork": "BPO2", "module": "ethereum.forks.bpo2",
            "chainId": 1, "reward": -1,
            "mainnetActivationTimestamp": MAINNET_BPO2_ACTIVATION_TIMESTAMP,
        },
        "compiler": {
            "logicalFork": "Osaka", "testingBackend": "cancun",
            "externalSolcInvoked": False, "artifactCompiler": "Blanc",
        },
        "target": {
            "repository": "synthetic", "rootEnv": "JAUNE_T8N_TARGET",
            "defaultRoot": "~/execution-specs-t8n-amsterdam",
            "checkoutCommit": "0" * 40, "upstreamCommit": "1" * 40,
            "overlayPaths": [], "overlayDiffSha256": "2" * 64,
            "pythonIdentity": {},
        },
    }
    cache = {
        "repositoryFiles": {
            relative: str(index % 10) * 64
            for index, relative in enumerate(CACHE_REPOSITORY_FILES)
        },
        "runtimeLock": {
            "relativePath": CACHE_RUNTIME_LOCK,
            "sha256": "1" * 64,
            "platforms": list(CACHE_RUNTIME_PLATFORMS),
        },
        "sharedGateOwnership": CACHE_OWNERSHIP,
    }
    cache["repositoryFiles"][CACHE_RUNTIME_LOCK] = cache["runtimeLock"]["sha256"]
    return assemble_manifest(
        profile, cache, expected_artifact_document(), creation, runtime,
    )


def manifest_falsifiers(expected: Mapping[str, object]) -> int:
    mutants: List[Tuple[str, Mapping[str, object]]] = []
    broken = copy.deepcopy(expected)
    broken["runtime"]["rows"] = broken["runtime"]["rows"][1:]
    mutants.append(("row-inventory", broken))
    broken = copy.deepcopy(expected)
    broken["runtime"]["rows"][0]["creditedChannels"] = ["status", "gas"]
    mutants.append(("credited-channel", broken))
    broken = copy.deepcopy(expected)
    broken["profile"]["execution"]["fork"] = "Osaka"
    mutants.append(("profile", broken))
    broken = copy.deepcopy(expected)
    reference_gas = broken["creation"]["reference"]["gas"]
    blanc_gas = broken["creation"]["blanc"]["gas"]
    blanc_gas["netConstructorExecutionGasAfterRefund"] = max(
        reference_gas["netConstructorExecutionGasAfterRefund"] + 1,
        reference_gas["transactionGasUsed"] + 1
        - blanc_gas["regularIntrinsicGas"] - blanc_gas["codeDepositGas"],
    )
    blanc_gas["transactionGasUsed"] = (
        blanc_gas["regularIntrinsicGas"] + blanc_gas["codeDepositGas"]
        + blanc_gas["netConstructorExecutionGasAfterRefund"]
    )
    broken["creation"]["deltas"] = {
        key: blanc_gas[key] - reference_gas[key] for key in CREATION_DOMINANCE_KEYS
    }
    broken["creation"]["dominance"] = {
        "requiredNonPositive": list(CREATION_DOMINANCE_KEYS),
        "transactionGasUsedNonPositive": False,
        "netConstructorExecutionGasAfterRefundNonPositive": False,
        "satisfied": False,
    }
    mutants.append(("constructor-dominance", broken))
    broken = copy.deepcopy(expected)
    gas = broken["creation"]["reference"]["gas"]
    gas["standardTokenGas"] += 1
    gas["regularIntrinsicGas"] += 1
    gas["netConstructorExecutionGasAfterRefund"] -= 1
    mutants.append(("decomposition-basis", broken))
    broken = copy.deepcopy(expected)
    broken["executionBoundary"]["historicalPragueComplement"] = "weakened"
    mutants.append(("historical-boundary", broken))
    broken = copy.deepcopy(expected)
    broken["artifacts"]["sizeComparison"]["blancRuntimeStrictlySmaller"] = False
    mutants.append(("artifact-size", broken))
    broken = copy.deepcopy(expected)
    first_cache = next(iter(broken["cacheInputs"]["repositoryFiles"]))
    del broken["cacheInputs"]["repositoryFiles"][first_cache]
    mutants.append(("cache-repository", broken))
    broken = copy.deepcopy(expected)
    broken["cacheInputs"]["runtimeLock"]["relativePath"] = "weakened.json"
    mutants.append(("runtime-lock-path", broken))
    broken = copy.deepcopy(expected)
    broken["cacheInputs"]["runtimeLock"]["sha256"] = "not-a-digest"
    mutants.append(("runtime-lock-digest", broken))
    broken = copy.deepcopy(expected)
    broken["cacheInputs"]["sharedGateOwnership"] = "weakened"
    mutants.append(("cache-ownership", broken))
    broken = copy.deepcopy(expected)
    broken["runtime"]["gasPolicy"]["allRowsRecorded"] = False
    mutants.append(("gas-policy", broken))
    for label, mutant in mutants:
        try:
            validate_manifest_semantics(mutant)
        except RuntimeError:
            continue
        die(f"static manifest falsifier survived: {label}")
    if len(mutants) != MANIFEST_FALSIFIERS:
        die("manifest-falsifier count differs")
    return len(mutants)


def manifest_channel_falsifiers(expected: Mapping[str, object]) -> int:
    mutants: List[Tuple[str, Mapping[str, object]]] = []
    broken = copy.deepcopy(expected)
    broken["runtime"]["rows"][0]["reference"]["receiptSucceeded"] = False
    mutants.append(("status", broken))
    broken = copy.deepcopy(expected)
    broken["runtime"]["rows"][0]["blanc"]["gasUsed"] += 1
    mutants.append(("gas", broken))
    broken = copy.deepcopy(expected)
    broken["runtime"]["depositProjection"]["blanc"]["log"]["data"] = "0x00"
    mutants.append(("deposit-log", broken))
    broken = copy.deepcopy(expected)
    storage = broken["runtime"]["depositProjection"]["blanc"]["rawStorage"]
    del storage[next(iter(storage))]
    mutants.append(("deposit-storage", broken))
    broken = copy.deepcopy(expected)
    broken["runtime"]["depositProjection"]["blanc"]["eth"][
        "contractFinal"
    ] = "0x0"
    mutants.append(("deposit-eth", broken))
    for label, mutant in mutants:
        try:
            validate_manifest_semantics(mutant)
        except RuntimeError:
            continue
        die(f"credited-channel falsifier survived: {label}")
    if len(mutants) != MANIFEST_CHANNEL_FALSIFIERS:
        die("manifest credited-channel falsifier count differs")
    return len(mutants)


def registry_liveness_falsifier() -> int:
    reference_runtime = synthetic_runtime_side(
        "reference", (100_000, 90_000, 30_000, 25_000, 25_100, 25_200, 22_000)
    )
    blanc_runtime = synthetic_runtime_side(
        "blanc", (100_001, 80_000, 29_000, 24_000, 24_100, 24_200, 21_000)
    )
    try:
        compose_runtime(runtime_rows(), reference_runtime, blanc_runtime)
    except RuntimeError as exc:
        if "current-mainnet gas registry markers differ" not in str(exc):
            die(f"positive-gas registry control failed for the wrong reason: {exc}")
        return 1
    die("positive-gas row survived without its exact completed registry marker")


def require_manifest(expected: Mapping[str, object], write: bool) -> None:
    validate_manifest(expected, expected)
    channel_checks = manifest_channel_falsifiers(expected)
    registry_checks = registry_liveness_falsifier()
    checks = manifest_falsifiers(expected)
    rendered = json.dumps(expected, indent=2, sort_keys=True) + "\n"
    if write:
        MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST_PATH.write_text(rendered, encoding="utf-8")
        print(
            f"wrote {MANIFEST_PATH.relative_to(REPO)} after {channel_checks} "
            f"manifest-channel, {registry_checks} registry, and {checks} "
            "manifest falsifiers"
        )
        return
    if not MANIFEST_PATH.is_file():
        die(
            f"missing {MANIFEST_PATH.relative_to(REPO)}; run the complete BPO2 "
            "campaign once with --write-manifest"
        )
    try:
        committed = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        die(f"committed current-mainnet manifest is invalid JSON: {exc}")
    validate_manifest(committed, expected)
    if MANIFEST_PATH.read_text(encoding="utf-8") != rendered:
        die("committed current-mainnet manifest is not canonical")


def parse_wrapper_list(value: str) -> Tuple[str, ...]:
    result = tuple(value.split(","))
    if not value or any(not item for item in result) or len(result) != len(set(result)):
        die("wrapper-owned list is empty, malformed, or duplicated")
    return result


def validate_wrapper_contract(args: argparse.Namespace) -> None:
    if args.wrapper_schema != MANIFEST_SCHEMA:
        die("shell/Python current-mainnet schema ownership differs")
    if parse_wrapper_list(args.wrapper_rows) != REQUIRED_ROW_NAMES:
        die("shell/Python runtime-row ownership differs")
    if parse_wrapper_list(args.wrapper_channels) != REQUIRED_CHANNELS:
        die("shell/Python credited-channel ownership differs")
    if parse_wrapper_list(args.wrapper_row_channel_map) != REQUIRED_ROW_CHANNEL_MAP:
        die("shell/Python per-row channel ownership differs")
    if parse_wrapper_list(args.wrapper_profile_claims) != PROFILE_CLAIMS:
        die("shell/Python profile-claim ownership differs")
    if parse_wrapper_list(args.wrapper_dominance_keys) != CREATION_DOMINANCE_KEYS:
        die("shell/Python constructor-dominance ownership differs")
    if parse_wrapper_list(args.wrapper_creation_assertions) != CREATION_ASSERTIONS:
        die("shell/Python constructor-assertion ownership differs")
    if args.wrapper_historical_boundary != HISTORICAL_BOUNDARY:
        die("shell/Python historical-Prague boundary ownership differs")
    if args.wrapper_static_falsifiers != STATIC_INVENTORY_FALSIFIERS \
            or args.wrapper_api_falsifiers != API_BOUNDARY_FALSIFIERS \
            or args.wrapper_raw_channel_falsifiers != RAW_CHANNEL_FALSIFIERS \
            or args.wrapper_manifest_channel_falsifiers \
            != MANIFEST_CHANNEL_FALSIFIERS \
            or args.wrapper_registry_falsifiers != REGISTRY_FALSIFIERS \
            or args.wrapper_manifest_falsifiers != MANIFEST_FALSIFIERS:
        die("shell/Python falsifier-count ownership differs")
    if parse_wrapper_list(args.wrapper_manifest_classes) != MANIFEST_CLASSES:
        die("shell/Python manifest-falsifier classes differ")
    if args.wrapper_deviation_marker != DEVIATION_MARKER_VERSION:
        die("shell/Python gas-deviation marker ownership differs")
    if args.wrapper_create_target != CREATE_TARGET:
        die("shell/Python CREATE-target ownership differs")
    if args.wrapper_tx_gas_limit != TX_MAX_GAS_LIMIT:
        die("shell/Python EIP-7825 transaction-gas-limit ownership differs")
    expected_gas_constants = (
        f"txBase={TX_BASE_GAS}",
        f"txCreate={TX_CREATE_GAS}",
        f"standardToken={TX_DATA_TOKEN_STANDARD}",
        f"floorToken={TX_DATA_TOKEN_FLOOR}",
        f"initcodeWord={INITCODE_WORD_GAS}",
        f"codeDepositPerByte={CODE_DEPOSIT_GAS_PER_BYTE}",
        f"eip170Limit={EIP170_LIMIT}",
        f"eip3860Limit={EIP3860_LIMIT}",
    )
    if parse_wrapper_list(args.wrapper_gas_constants) != expected_gas_constants:
        die("shell/Python constructor gas/size constants differ")
    if parse_wrapper_list(args.wrapper_cache_repository_files) \
            != CACHE_REPOSITORY_FILES \
            or args.wrapper_cache_runtime_lock != CACHE_RUNTIME_LOCK \
            or parse_wrapper_list(args.wrapper_cache_runtime_platforms) \
            != CACHE_RUNTIME_PLATFORMS \
            or args.wrapper_cache_ownership != CACHE_OWNERSHIP:
        die("shell/Python cache-provenance ownership differs")
    expected_artifacts = (
        f"runtimeBytes={BLANC_RUNTIME_BYTES}",
        f"runtimeSha256={BLANC_RUNTIME_SHA256}",
        f"creationBytes={BLANC_CREATION_BYTES}",
        f"creationSha256={BLANC_CREATION_SHA256}",
        f"constructorPrefixBytes={CONSTRUCTOR_STATIC_EXPECTED['blanc']['prefixBytes']}",
        "constructorSstoreSites=" + "+".join(
            str(value) for value in CONSTRUCTOR_STATIC_EXPECTED["blanc"]["sstoreSites"]
        ),
        "constructorStaticcallSites=" + "+".join(
            str(value) for value in CONSTRUCTOR_STATIC_EXPECTED["blanc"]["staticcallSites"]
        ),
        "constructorCodecopySites=" + "+".join(
            str(value) for value in CONSTRUCTOR_STATIC_EXPECTED["blanc"]["codecopySites"]
        ),
    )
    if parse_wrapper_list(args.wrapper_blanc_artifacts) != expected_artifacts:
        die("shell/Python Blanc artifact/prefix ownership differs")


def crypto_self_check() -> None:
    if keccak256(b"").hex() \
            != "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470":
        die("dependency-free Ethereum Keccak empty-string vector differs")
    event_signature = b"DepositEvent(bytes,bytes,bytes,bytes,bytes)"
    if keccak256(event_signature).hex() != DEPOSIT_EVENT_TOPIC:
        die("dependency-free Ethereum Keccak DepositEvent vector differs")
    if rlp_encode([]).hex() != "c0" \
            or logs_hash(()) \
            != "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347":
        die("dependency-free RLP/empty-log vector differs")
    if not re.fullmatch(r"0x[0-9a-f]{40}", create_address(SENDER, 0)):
        die("dependency-free CREATE address derivation is malformed")
    if create_address(SENDER, 0) != CREATE_TARGET:
        die("dependency-free CREATE address vector differs")


def static_self_check() -> Tuple[int, int, int, int, int, int]:
    crypto_self_check()
    try:
        source = Path(__file__).read_text(encoding="utf-8")
    except OSError as exc:
        die(f"cannot read current-mainnet consumer source: {exc}")
    validate_current_mainnet_api_source(source)
    api_checks = current_mainnet_api_falsifiers(source)
    rows = runtime_rows()
    validate_runtime_inventory(rows)
    inventory_checks = static_inventory_falsifiers(rows)
    raw_channel_checks = raw_channel_falsifiers()
    synthetic = synthetic_manifest()
    validate_manifest(synthetic, synthetic)
    manifest_channel_checks = manifest_channel_falsifiers(synthetic)
    registry_checks = registry_liveness_falsifier()
    manifest_checks = manifest_falsifiers(synthetic)
    return (inventory_checks, api_checks, raw_channel_checks,
            manifest_channel_checks, registry_checks, manifest_checks)


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--blanc-artifacts",
                        help="output of eval-beacon-deposit-differential-code.lean")
    parser.add_argument("--root", help="explicit current-mainnet target root")
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--static-self-check", action="store_true")
    parser.add_argument("--wrapper-schema", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-rows", required=True, help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-channels", required=True, help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-row-channel-map", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-profile-claims", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-dominance-keys", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-creation-assertions", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-historical-boundary", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-static-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-api-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-raw-channel-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-manifest-channel-falsifiers", type=int,
                        required=True, help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-registry-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-manifest-falsifiers", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-manifest-classes", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-deviation-marker", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-create-target", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-tx-gas-limit", type=int, required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-gas-constants", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-cache-repository-files", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-cache-runtime-lock", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-cache-runtime-platforms", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-cache-ownership", required=True,
                        help=argparse.SUPPRESS)
    parser.add_argument("--wrapper-blanc-artifacts", required=True,
                        help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    validate_wrapper_contract(args)

    if args.static_self_check:
        if args.blanc_artifacts or args.root or args.write_manifest:
            die("static self-check refuses artifacts, target root, and manifest writes")
        (inventory_checks, api_checks, raw_channel_checks,
         manifest_channel_checks, registry_checks, manifest_checks) = \
            static_self_check()
        print(
            f"STATIC OK — beacon-deposit current-mainnet: schema {MANIFEST_SCHEMA}, "
            f"{len(REQUIRED_ROW_NAMES)} runtime rows, {len(REQUIRED_CHANNELS)} "
            f"credited channels, {inventory_checks} inventory, {api_checks} API, "
            f"{raw_channel_checks} raw-channel, {manifest_channel_checks} "
            f"manifest-channel, {registry_checks} registry, and {manifest_checks} "
            "manifest falsifiers; "
            "no Lean artifact or t8n execution"
        )
        return 0

    if not args.blanc_artifacts:
        die("normal current-mainnet mode requires --blanc-artifacts")
    load_profile, resolve_root, verify_target, target_paths, run_t8n = \
        current_mainnet_api()
    profile = load_profile()
    root = resolve_root(profile, args.root)
    verified = verify_target(root, profile)
    paths = target_paths(root, profile)
    if paths.root != root:
        die("current-mainnet public root/path resolution differs")
    reference_artifacts = load_reference()
    try:
        artifact_text = Path(args.blanc_artifacts).read_text(encoding="utf-8")
    except OSError as exc:
        die(f"cannot read Blanc evaluator output: {exc}")
    blanc_artifacts = parse_blanc_artifacts(artifact_text)
    rows = runtime_rows()
    validate_runtime_inventory(rows)

    reference_creation = run_creation(
        "reference", reference_artifacts["creation"], reference_artifacts["runtime"],
        root=root, profile=profile, run_t8n=run_t8n,
    )
    blanc_creation = run_creation(
        "blanc", blanc_artifacts["creation"], blanc_artifacts["runtime"],
        root=root, profile=profile, run_t8n=run_t8n,
    )
    reference_runtime = run_runtime(
        "reference", reference_artifacts["runtime"], rows,
        root=root, profile=profile, run_t8n=run_t8n,
    )
    blanc_runtime = run_runtime(
        "blanc", blanc_artifacts["runtime"], rows,
        root=root, profile=profile, run_t8n=run_t8n,
    )
    expected = build_manifest(
        profile, verified, reference_artifacts, blanc_artifacts,
        reference_creation, blanc_creation, reference_runtime, blanc_runtime,
    )
    require_manifest(expected, args.write_manifest)
    if args.verbose:
        for row in expected["runtime"]["rows"]:
            print(
                f"PASS {row['name']}: status/gas; "
                f"Blanc-minus-reference={row['blancMinusReferenceGas']}"
            )
    creation_delta = expected["creation"]["deltas"]
    positive = len(expected["runtime"]["gasPolicy"]["positiveDeltas"])
    print(
        f"OK — beacon-deposit current-mainnet: BPO2, 2/2 fresh creations, "
        f"{len(rows)}/{len(rows)} runtime rows; Blanc runtime/creation "
        f"{BLANC_RUNTIME_BYTES}/{BLANC_CREATION_BYTES} bytes vs reference "
        f"{REFERENCE_RUNTIME_BYTES}/{REFERENCE_CREATION_BYTES}; constructor "
        f"total/net-after-refund deltas {creation_delta['transactionGasUsed']}/"
        f"{creation_delta['netConstructorExecutionGasAfterRefund']}; "
        f"{positive} positive runtime gas deltas with completed markers"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except RuntimeError as exc:
        print(f"REGRESSION — beacon-deposit current-mainnet: {exc}", file=sys.stderr)
        raise SystemExit(1)
