#!/usr/bin/env python3
"""Generate and check WETH10's additive BPO2 current-mainnet evidence.

Run this only through ``check-weth10-current-mainnet.sh``.  The wrapper owns
the exact Lean evaluators and isolated target interpreter; this file owns all
fixture and manifest bytes.  Normal mode is read-only and byte-compares every
document.  ``--write`` is the sole writer and is reached only after the BPO2
transitions and all semantic assertions have succeeded.

The BPO2 lane deliberately credits status, receipt gas, logs, projected
storage, and fee-normalized ETH for the canonical 27-selector-plus-receive
matrix.  Exact returndata, live CALL traces, and the malformed/precompile/OOG
corpus remain exclusively in the preserved Prague differential.
"""
from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import importlib.util
import json
import re
import sys
import types
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, NoReturn, Sequence

from ethereum.crypto.hash import keccak256
from ethereum.forks.bpo2.blocks import Header
from ethereum.state import Account, Address
from ethereum.state_mpt import State, set_account, set_storage, state_root, store_code
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes8, Bytes32, Bytes256
from ethereum_types.numeric import U64, U256, Uint
from ethereum.utils.hexadecimal import hex_to_bytes
from execution_testing.forks import BPO2 as TestingBPO2
from spec256k1 import PrivateKey

from current_mainnet import (
    load_profile,
    resolve_root,
    run_t8n,
    target_paths,
    verify_target,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "scripts" / "fixtures" / "weth10-current-mainnet"
REFERENCE_LOCK = ROOT / "scripts" / "weth10-reference.json"
RUNTIME_LOCK = ROOT / "scripts" / "current-mainnet-runtime-lock.json"
DIFFERENTIAL = ROOT / "scripts" / "gen-weth10-differential.py"
MAINNET_SOURCE = ROOT / "Blanc" / "Weth10Mainnet.lean"

WETH10 = "0xf4bb2e28688e89fcce3c0580d37d36a7672e8a9f"
RECIPIENT = "0x2222222222222222222222222222222222222222"
DELEGATE = "0x000000000000000000000000000000000000d31e"
ZERO_ADDRESS = "0x" + "00" * 20
COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"

SYSTEM_ADDRESSES = (
    "0x0000f90827f1c53a10cb7a02335b175320002935",
    "0x000f3df6d732807ef1319fb7b8bb8522d0beac02",
    "0x00000961ef480eb55e80d19ad83579a64c007002",
    "0x0000bbddc7ce488642fb579f8b00f3a590007251",
    "0x00000000219ab540356cbb839cbe05303d7705fa",
)
NEUTRAL_SYSTEM_ADDRESSES = SYSTEM_ADDRESSES[:4]
EXPECTED_SYSTEM_INTS = {int(address, 16) for address in SYSTEM_ADDRESSES}

EMPTY_OMMER_HASH = (
    "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
)
EMPTY_TRIE_ROOT = (
    "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
)
EMPTY_REQUESTS_HASH = (
    "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
)
ZERO_HASH = "0x" + "00" * 32
ZERO_BLOOM = "0x" + "00" * 256

MAINNET_BPO2_ACTIVATION_TIMESTAMP = 1_767_747_671
CREATION_TIMESTAMP = MAINNET_BPO2_ACTIVATION_TIMESTAMP + 12
BLOCK_GAS_LIMIT = 30_000_000
TRANSACTION_GAS_LIMIT = 2_000_000
TRANSACTION_GAS_CAP = 1 << 24
GAS_PRICE = 10
SENDER_BALANCE = 10**24
UINT256_MAX = (1 << 256) - 1

CREATION_KEY = 29
MATRIX_KEY = 30
TYPE2_OWNER_KEY = 21
TYPE4_OWNER_KEY = 22
AUTHORITY_KEY = 23
EXPECTED_CREATION_TARGET = "0xcf024a39b81692e3c25b9ceb8474dc6203d584d7"

HISTORICAL_BOUNDARY = (
    "BPO2 credits status, receipt gas, logs, projected storage, and ETH for "
    "the canonical 27-selector-plus-receive matrix; the preserved Prague "
    "differential exclusively owns exact returndata, live CALL traces, and "
    "malformed, precompile, and OOG cases"
)
CURRENT_MAINNET_PUBLIC_API = {
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
}
EVIDENCE_BOUNDARY_FALSIFIERS = 4


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def q(value: int | str) -> str:
    number = int(value, 16) if isinstance(value, str) else int(value)
    if number < 0:
        die(f"negative JSON quantity: {number}")
    digits = format(number, "x")
    return "0x" + ("0" + digits if len(digits) % 2 else digits)


def word(value: int) -> bytes:
    return int(value).to_bytes(32, "big")


def address_bytes(address: str) -> bytes:
    raw = bytes.fromhex(address.removeprefix("0x"))
    if len(raw) != 20:
        die(f"not an address: {address}")
    return raw


def address_word(address: str) -> bytes:
    return bytes(12) + address_bytes(address)


def canonical_address(address: str) -> str:
    return "0x" + address_bytes(address).hex()


def private_key_hex(value: int) -> str:
    return "0x" + int(value).to_bytes(32, "big").hex()


def derive_address(value: int) -> str:
    public = PrivateKey(int(value).to_bytes(32, "big")).public_key.format(
        compressed=False
    )
    return "0x" + bytes(keccak256(public[1:]))[-20:].hex()


def create_address(sender: str, nonce: int) -> str:
    encoded_nonce: bytes | int = b"" if nonce == 0 else nonce
    return "0x" + bytes(
        keccak256(rlp.encode([address_bytes(sender), encoded_nonce]))
    )[-20:].hex()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def render_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def validate_current_mainnet_source(source: str) -> None:
    """Validate one source image against the closed execution boundary."""
    tree = ast.parse(source)
    legacy_env = "EELS" + "_ROOT"
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value == legacy_env:
            die("generator cross-wires the historical Prague environment")
        modules: list[str] = []
        if isinstance(node, ast.ImportFrom) and node.module is not None:
            modules = [node.module]
        elif isinstance(node, ast.Import):
            modules = [alias.name for alias in node.names]
        if any(
            module == "subprocess"
            or module.startswith("ethereum.prague")
            or module.startswith("ethereum_spec_tools")
            for module in modules
        ):
            die("generator bypasses the current-mainnet execution boundary")
    imports = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module == "current_mainnet"
    ]
    imported = {
        alias.name for node in imports for alias in node.names
        if alias.asname is None
    }
    if len(imports) != 1 or imported != CURRENT_MAINNET_PUBLIC_API or any(
        alias.asname is not None for node in imports for alias in node.names
    ):
        die("generator must import exactly the five current-mainnet API names")
    calls = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in CURRENT_MAINNET_PUBLIC_API
    ]
    counts = {name: 0 for name in CURRENT_MAINNET_PUBLIC_API}
    for call in calls:
        counts[call.func.id] += 1
    if counts != {name: 1 for name in CURRENT_MAINNET_PUBLIC_API}:
        die(f"current-mainnet public API call inventory differs: {counts}")
    transition = next(call for call in calls if call.func.id == "run_t8n")
    keywords = tuple(keyword.arg for keyword in transition.keywords)
    if len(transition.args) != 3 or keywords != (
        "root", "profile", "state_test", "timeout",
    ):
        die("run_t8n call shape differs from the closed BPO2 boundary")


def validate_current_mainnet_boundary() -> None:
    """Pin execution to the exact five-function, fork-override-free API."""
    validate_current_mainnet_source(Path(__file__).read_text(encoding="utf-8"))


def current_mainnet_boundary_falsifiers() -> int:
    source = Path(__file__).read_text(encoding="utf-8")
    call_contract = "root=root, profile=profile, state_test=state_test, timeout=120,"
    prefix, separator, suffix = source.rpartition(call_contract)
    fork_mutant = (
        prefix
        + "root=root, profile=profile, fork=\"Prague\", "
        + "state_test=state_test, timeout=120,"
        + suffix
        if separator else source
    )
    mutants = (
        (
            "public-api-name",
            source.replace("    verify_target,\n", "    verify_target_alt,\n", 1),
        ),
        ("fork-override", fork_mutant),
        ("direct-subprocess", source + "\nimport subprocess\n"),
        ("historical-root", source + "\n_LEGACY_ROOT = \"EELS_ROOT\"\n"),
    )
    for label, mutant in mutants:
        if mutant == source:
            die(f"current-mainnet boundary falsifier did not mutate source: {label}")
        try:
            validate_current_mainnet_source(mutant)
        except RuntimeError:
            continue
        die(f"current-mainnet boundary falsifier survived: {label}")
    return len(mutants)


def parse_emitted_artifacts(path: Path, expected: set[str]) -> dict[str, bytes | int]:
    found: dict[str, bytes | int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = line.strip().split()
        if len(parts) == 2 and parts[0] == "prefix-length":
            found[parts[0]] = int(parts[1])
        elif len(parts) == 3 and parts[0] in expected:
            length = int(parts[1])
            value = bytes.fromhex(parts[2])
            if len(value) != length:
                die(
                    f"{path.name}: {parts[0]} says {length} bytes, emitted "
                    f"{len(value)}"
                )
            found[parts[0]] = value
    if set(found) != expected:
        die(
            f"{path.name}: evaluator fields differ: expected={sorted(expected)}, "
            f"actual={sorted(found)}"
        )
    return found


def parse_runtime_artifacts(path: Path) -> dict[str, bytes | int | list[str]]:
    found: dict[str, bytes | int | list[str]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = line.strip().split()
        if len(parts) == 3 and parts[0] in ("mainnet", "synthetic"):
            length = int(parts[1])
            value = bytes.fromhex(parts[2])
            if len(value) != length:
                die(f"{path.name}: malformed {parts[0]} runtime length")
            found[parts[0]] = value
        elif len(parts) == 2 and parts[0] == "synthetic-domain":
            found[parts[0]] = int(parts[1])
        elif len(parts) == 3 and parts[0] == "selectors":
            count = int(parts[1])
            selectors = [item[-8:].lower() for item in parts[2].split(",")]
            if len(selectors) != count:
                die(f"{path.name}: malformed selector inventory")
            found[parts[0]] = selectors
    expected = {"mainnet", "synthetic", "synthetic-domain", "selectors"}
    if set(found) != expected:
        die(f"{path.name}: runtime evaluator fields differ: {sorted(found)}")
    return found


@dataclass(frozen=True)
class Artifacts:
    initcode: bytes
    mainnet_runtime: bytes
    transaction_runtime: bytes
    system_code: bytes
    selectors: tuple[str, ...]
    deployment_digest: str
    runtime_digest: str


def load_artifacts(deployment_path: Path, runtime_path: Path) -> Artifacts:
    deployment = parse_emitted_artifacts(
        deployment_path,
        {
            "initcode", "prefix-length", "mainnet-runtime", "synthetic-runtime",
            "transaction-runtime", "system-code",
        },
    )
    runtime = parse_runtime_artifacts(runtime_path)
    if deployment["mainnet-runtime"] != runtime["mainnet"]:
        die("deployment and differential evaluators disagree on mainnet runtime")
    if deployment["synthetic-runtime"] != runtime["synthetic"]:
        die("deployment and differential evaluators disagree on synthetic runtime")
    prefix = deployment["prefix-length"]
    if not isinstance(prefix, int) or prefix <= 0 or prefix >= len(deployment["initcode"]):
        die("deployment evaluator emitted an invalid initcode prefix length")
    system_code = deployment["system-code"]
    if system_code != b"\x5b\x00":
        die(
            "deployment system program is no longer the exact neutral "
            "JUMPDEST/STOP program"
        )
    selectors = runtime["selectors"]
    if not isinstance(selectors, list) or len(selectors) != 27 \
            or len(set(selectors)) != 27:
        die("runtime evaluator no longer emits 27 distinct selectors")
    return Artifacts(
        initcode=deployment["initcode"],
        mainnet_runtime=deployment["mainnet-runtime"],
        transaction_runtime=deployment["transaction-runtime"],
        system_code=system_code,
        selectors=tuple(selectors),
        deployment_digest=sha256_file(deployment_path),
        runtime_digest=sha256_file(runtime_path),
    )


def read_timestamp_pin() -> int:
    try:
        source = MAINNET_SOURCE.read_text(encoding="utf-8")
    except OSError as exc:
        die(f"timestamp-pin source is absent: {MAINNET_SOURCE}: {exc}")
    matches = re.findall(
        r"\bdef\s+weth10CurrentMainnetCreationTimestamp\s*:\s*Nat\s*:=\s*([0-9_]+)",
        source,
    )
    if len(matches) != 1:
        die("Weth10Mainnet must contain one literal current-mainnet creation timestamp")
    timestamp = int(matches[0].replace("_", ""))
    if timestamp != CREATION_TIMESTAMP:
        die(
            f"Lean timestamp pin differs: expected {CREATION_TIMESTAMP}, got {timestamp}"
        )
    return timestamp


def account(
    balance: int,
    code: bytes = b"",
    *,
    nonce: int | None = None,
    storage: Mapping[int, int] | None = None,
) -> dict[str, object]:
    selected_nonce = (1 if code else 0) if nonce is None else nonce
    return {
        "nonce": q(selected_nonce),
        "balance": q(balance),
        "code": "0x" + code.hex(),
        "storage": {
            q(slot): q(value) for slot, value in sorted((storage or {}).items()) if value
        },
    }


def canonical_system_alloc() -> dict[str, dict[str, object]]:
    raw = TestingBPO2.pre_allocation_blockchain()
    if set(raw) != EXPECTED_SYSTEM_INTS:
        die(
            "BPO2 system-contract population differs: "
            + repr(sorted(hex(value) for value in raw))
        )
    result: dict[str, dict[str, object]] = {}
    for address, item in sorted(raw.items()):
        code_value = item.get("code", b"")
        if isinstance(code_value, str):
            code = bytes.fromhex(code_value.removeprefix("0x"))
        elif isinstance(code_value, bytes):
            code = code_value
        else:
            die(f"BPO2 system code has unknown shape at {address:#x}")
        storage: dict[int, int] = {}
        for key, value in item.get("storage", {}).items():
            raw_value = int.from_bytes(value, "big") if isinstance(value, bytes) else int(value)
            storage[int(key)] = raw_value
        rendered = account(
            int(item.get("balance", 0)), code,
            nonce=int(item.get("nonce", 0)), storage=storage,
        )
        result["0x" + format(address, "040x")] = rendered
    return result


def neutral_system_alloc(system_code: bytes) -> dict[str, dict[str, object]]:
    result = canonical_system_alloc()
    for address in NEUTRAL_SYSTEM_ADDRESSES:
        result[address] = account(0, system_code, nonce=1)
    return result


def norm_alloc(alloc: Mapping[str, Mapping[str, object]]) -> dict[str, object]:
    return {
        canonical_address(address): {
            "nonce": q(str(item.get("nonce", "0x0"))),
            "balance": q(str(item.get("balance", "0x0"))),
            "code": str(item.get("code", "0x")).lower(),
            "storage": {
                q(str(slot)): q(str(value))
                for slot, value in sorted(
                    item.get("storage", {}).items(), key=lambda pair: int(str(pair[0]), 16)
                )
                if int(str(value), 16)
            },
        }
        for address, item in sorted(alloc.items(), key=lambda pair: int(pair[0], 16))
    }


def alloc_root(alloc: Mapping[str, Mapping[str, object]]) -> str:
    state = State()
    for address, item in alloc.items():
        code = Bytes(hex_to_bytes(str(item.get("code", "0x"))))
        target = Address(address_bytes(address))
        set_account(
            state,
            target,
            Account(
                nonce=Uint(int(str(item.get("nonce", "0x0")), 16)),
                balance=U256(int(str(item.get("balance", "0x0")), 16)),
                code_hash=store_code(state, code),
            ),
        )
        for slot, value in item.get("storage", {}).items():
            number = int(str(value), 16)
            if number:
                set_storage(
                    state, target, Bytes32(int(str(slot), 16).to_bytes(32, "big")),
                    U256(number),
                )
    return "0x" + bytes(state_root(state)).hex()


def header(document: Mapping[str, str]) -> tuple[Header, str]:
    value = Header(
        parent_hash=hex_to_bytes(document["parentHash"]),
        ommers_hash=hex_to_bytes(document["uncleHash"]),
        coinbase=Address(hex_to_bytes(document["coinbase"])),
        state_root=hex_to_bytes(document["stateRoot"]),
        transactions_root=hex_to_bytes(document["transactionsTrie"]),
        receipt_root=hex_to_bytes(document["receiptTrie"]),
        bloom=Bytes256(hex_to_bytes(document["bloom"])),
        difficulty=Uint(int(document["difficulty"], 16)),
        number=Uint(int(document["number"], 16)),
        gas_limit=Uint(int(document["gasLimit"], 16)),
        gas_used=Uint(int(document["gasUsed"], 16)),
        timestamp=U256(int(document["timestamp"], 16)),
        extra_data=Bytes(hex_to_bytes(document["extraData"])),
        prev_randao=Bytes32(hex_to_bytes(document["mixHash"])),
        nonce=Bytes8(hex_to_bytes(document["nonce"])),
        base_fee_per_gas=Uint(int(document["baseFeePerGas"], 16)),
        withdrawals_root=hex_to_bytes(document["withdrawalsRoot"]),
        blob_gas_used=U64(int(document["blobGasUsed"], 16)),
        excess_blob_gas=U64(int(document["excessBlobGas"], 16)),
        parent_beacon_block_root=hex_to_bytes(document["parentBeaconBlockRoot"]),
        requests_hash=hex_to_bytes(document["requestsHash"]),
    )
    return value, "0x" + bytes(keccak256(rlp.encode(value))).hex()


def genesis_header(alloc: Mapping[str, Mapping[str, object]]) -> dict[str, str]:
    return {
        "parentHash": ZERO_HASH,
        "uncleHash": EMPTY_OMMER_HASH,
        "coinbase": ZERO_ADDRESS,
        "stateRoot": alloc_root(alloc),
        "transactionsTrie": EMPTY_TRIE_ROOT,
        "receiptTrie": EMPTY_TRIE_ROOT,
        "bloom": ZERO_BLOOM,
        "difficulty": "0x00",
        "number": "0x00",
        "gasLimit": q(BLOCK_GAS_LIMIT),
        "gasUsed": "0x00",
        "timestamp": q(MAINNET_BPO2_ACTIVATION_TIMESTAMP),
        "extraData": "0x00",
        "mixHash": ZERO_HASH,
        "nonce": "0x0000000000000000",
        "baseFeePerGas": "0x07",
        "withdrawalsRoot": EMPTY_TRIE_ROOT,
        "blobGasUsed": "0x00",
        "excessBlobGas": "0x00",
        "parentBeaconBlockRoot": ZERO_HASH,
        "requestsHash": EMPTY_REQUESTS_HASH,
    }


def transition_environment(
    alloc: Mapping[str, Mapping[str, object]],
) -> tuple[dict[str, str], str, dict[str, object]]:
    genesis = genesis_header(alloc)
    _, genesis_hash = header(genesis)
    environment: dict[str, object] = {
        "currentCoinbase": COINBASE,
        "currentGasLimit": genesis["gasLimit"],
        "currentNumber": "0x1",
        "currentTimestamp": q(CREATION_TIMESTAMP),
        "currentRandom": ZERO_HASH,
        "parentHash": genesis_hash,
        "parentTimestamp": genesis["timestamp"],
        "parentDifficulty": "0x0",
        "parentUncleHash": EMPTY_OMMER_HASH,
        "parentGasLimit": genesis["gasLimit"],
        "parentGasUsed": "0x0",
        "parentBaseFee": genesis["baseFeePerGas"],
        "parentBlobGasUsed": "0x0",
        "parentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": genesis["parentBeaconBlockRoot"],
        "blockHashes": {"0": genesis_hash},
        "ommers": [],
        "withdrawals": [],
    }
    return genesis, genesis_hash, environment


def _run_transition(
    alloc: object,
    environment: object,
    transactions: object,
    *,
    root: Path,
    profile: Mapping[str, object],
    state_test: bool,
):
    return run_t8n(
        alloc, environment, transactions,
        root=root, profile=profile, state_test=state_test, timeout=120,
    )


def type2_transaction(
    key: int,
    nonce: int,
    to: str,
    data: bytes,
    *,
    value: int = 0,
    gas: int = TRANSACTION_GAS_LIMIT,
) -> dict[str, object]:
    if gas > TRANSACTION_GAS_CAP:
        die("authored BPO2 transaction crosses the EIP-7825 gas cap")
    return {
        "type": "0x2",
        "chainId": "0x1",
        "nonce": q(nonce),
        "maxPriorityFeePerGas": q(GAS_PRICE),
        "maxFeePerGas": q(GAS_PRICE),
        "gas": q(gas),
        "to": to,
        "value": q(value),
        "input": "0x" + data.hex(),
        "accessList": [],
        "secretKey": private_key_hex(key),
    }


def sign_authorization(key: int, delegate: str, nonce: int = 0) -> dict[str, object]:
    digest = bytes(
        keccak256(
            b"\x05"
            + rlp.encode(
                (U256(1), Address(address_bytes(delegate)), U64(nonce))
            )
        )
    )
    signature = PrivateKey(int(key).to_bytes(32, "big")).sign_recoverable(digest)
    return {
        "chainId": "0x1",
        "address": delegate,
        "nonce": q(nonce),
        "v": q(signature[64]),
        "r": q(int.from_bytes(signature[:32], "big")),
        "s": q(int.from_bytes(signature[32:64], "big")),
    }


def type4_transaction(
    key: int,
    nonce: int,
    to: str,
    data: bytes,
    authorization: Mapping[str, object],
) -> dict[str, object]:
    result = type2_transaction(key, nonce, to, data)
    result["type"] = "0x4"
    result["authorizationList"] = [dict(authorization)]
    return result


def withdraw_calldata(recipient: str, amount: int) -> bytes:
    return (
        bytes(keccak256(b"withdrawTo(address,uint256)"))[:4]
        + address_word(recipient)
        + word(amount)
    )


def balance_slot(owner: str) -> int:
    return int.from_bytes(address_word(owner), "big")


def blanc_nonce_slot(owner: str) -> int:
    return (1 << 254) | int.from_bytes(address_word(owner), "big")


def blanc_allowance_slot(owner: str, spender: str) -> int:
    low = int.from_bytes(
        bytes(keccak256(address_word(owner) + address_word(spender))), "big"
    ) & ((1 << 254) - 1)
    return (1 << 255) | low


def solidity_balance_slot(owner: str) -> int:
    return int.from_bytes(bytes(keccak256(address_word(owner) + word(0))), "big")


def solidity_nonce_slot(owner: str) -> int:
    return int.from_bytes(bytes(keccak256(address_word(owner) + word(1))), "big")


def solidity_allowance_slot(owner: str, spender: str) -> int:
    inner = bytes(keccak256(address_word(owner) + word(2)))
    return int.from_bytes(bytes(keccak256(address_word(spender) + inner)), "big")


def find_account(
    alloc: object, address: str, label: str, *, required: bool = True
) -> Mapping[str, object]:
    if not isinstance(alloc, dict):
        die(f"{label}: t8n alloc is not an object")
    wanted = int(address, 16)
    matches = [
        value for key, value in alloc.items()
        if isinstance(key, str) and int(key, 16) == wanted
    ]
    if not matches and not required:
        return {"nonce": "0x0", "balance": "0x0", "code": "0x", "storage": {}}
    if len(matches) != 1 or not isinstance(matches[0], dict):
        die(f"{label}: expected one account for {address}, got {len(matches)}")
    return matches[0]


def normalized_account(
    alloc: object, address: str, label: str, *, required: bool = True
) -> dict[str, object]:
    raw = find_account(alloc, address, label, required=required)
    try:
        storage_raw = raw.get("storage", {})
        if not isinstance(storage_raw, dict):
            raise TypeError("storage is not an object")
        storage = {
            int(str(slot), 16): int(str(value), 16)
            for slot, value in storage_raw.items()
            if int(str(value), 16)
        }
        return {
            "nonce": int(str(raw.get("nonce", "0x0")), 16),
            "balance": int(str(raw.get("balance", "0x0")), 16),
            "code": bytes.fromhex(str(raw.get("code", "0x")).removeprefix("0x")),
            "storage": dict(sorted(storage.items())),
        }
    except (TypeError, ValueError) as exc:
        die(f"{label}: malformed account: {exc}")


def storage_value(alloc: object, address: str, slot: int) -> int:
    account_value = normalized_account(
        alloc, address, f"storage/{address}", required=False
    )
    return int(account_value["storage"].get(slot, 0))


def validate_result(
    result: object, transaction_count: int, label: str
) -> tuple[Mapping[str, object], ...]:
    if not isinstance(result, dict):
        die(f"{label}: t8n result is not an object")
    if result.get("rejected") not in (None, []):
        die(f"{label}: t8n rejected a transaction: {result.get('rejected')!r}")
    if result.get("blockException") is not None:
        die(f"{label}: t8n block exception: {result.get('blockException')!r}")
    receipts = result.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != transaction_count or any(
        not isinstance(receipt, dict) for receipt in receipts
    ):
        observed = len(receipts) if isinstance(receipts, list) else type(receipts).__name__
        die(f"{label}: expected {transaction_count} receipts, observed {observed}")
    return tuple(receipts)


def receipt_status(receipt: Mapping[str, object], label: str) -> bool:
    status = receipt.get("status")
    if status not in ("0x0", "0x1"):
        die(f"{label}: receipt status is not canonical: {status!r}")
    return status == "0x1"


def per_transaction_gas(
    receipts: Sequence[Mapping[str, object]], label: str
) -> tuple[int, ...]:
    cumulative: list[int] = []
    for index, receipt in enumerate(receipts):
        value = receipt.get("cumulativeGasUsed")
        if not isinstance(value, str):
            die(f"{label}: receipt {index} lacks cumulativeGasUsed")
        cumulative.append(int(value, 16))
    if any(
        value <= (cumulative[index - 1] if index else 0)
        for index, value in enumerate(cumulative)
    ):
        die(f"{label}: cumulative receipt gas is not strictly increasing")
    return tuple(
        value - (cumulative[index - 1] if index else 0)
        for index, value in enumerate(cumulative)
    )


def receipt_logs(
    receipt: Mapping[str, object], label: str
) -> tuple[dict[str, object], ...]:
    raw_logs = receipt.get("logs")
    if not isinstance(raw_logs, list):
        die(f"{label}: receipt logs are not an array")
    result: list[dict[str, object]] = []
    for index, raw in enumerate(raw_logs):
        if not isinstance(raw, dict) or set(raw) != {"address", "topics", "data"}:
            die(f"{label}: receipt log {index} shape differs")
        address = canonical_address(str(raw["address"]))
        topics = raw["topics"]
        data = raw["data"]
        if not isinstance(topics, list) or any(
            not isinstance(topic, str)
            or re.fullmatch(r"0x[0-9a-fA-F]{64}", topic) is None
            for topic in topics
        ) or not isinstance(data, str) \
                or re.fullmatch(r"0x(?:[0-9a-fA-F]{2})*", data) is None:
            die(f"{label}: receipt log {index} is malformed")
        result.append({
            "address": address,
            "topics": [topic.lower() for topic in topics],
            "data": data.lower(),
        })
    return tuple(result)


def transfer_log(owner: str, amount: int) -> dict[str, object]:
    return {
        "address": WETH10,
        "topics": [
            "0x" + bytes(keccak256(b"Transfer(address,address,uint256)")).hex(),
            "0x" + address_word(owner).hex(),
            "0x" + address_word(ZERO_ADDRESS).hex(),
        ],
        "data": "0x" + word(amount).hex(),
    }


def profile_blob_schedule(profile: Mapping[str, object]) -> dict[str, str]:
    execution = profile.get("execution")
    if not isinstance(execution, dict) or execution.get("fork") != "BPO2" \
            or execution.get("module") != "ethereum.forks.bpo2" \
            or execution.get("chainId") != 1:
        die("verified profile no longer declares the closed BPO2/chain-1 lane")
    schedule = execution.get("blobSchedule")
    if not isinstance(schedule, dict):
        die("verified BPO2 profile has no blob schedule")
    return {
        "target": q(int(schedule["targetBlobsPerBlock"])),
        "max": q(int(schedule["maxBlobsPerBlock"])),
        "baseFeeUpdateFraction": q(int(schedule["baseFeeUpdateFraction"])),
    }


def typed_body_transactions(body: object, authored: Sequence[Mapping[str, object]]) -> list[object]:
    if not isinstance(body, str):
        die("t8n body is not a hex string")
    decoded = rlp.decode(hex_to_bytes(body))
    if not isinstance(decoded, list) or len(decoded) != len(authored):
        count = len(decoded) if isinstance(decoded, list) else type(decoded).__name__
        die(f"t8n body carries {count} transactions for {len(authored)} rows")
    transactions: list[object] = []
    for index, (raw, transaction) in enumerate(zip(decoded, authored)):
        transaction_type = int(str(transaction["type"]), 16)
        payload: object
        if isinstance(raw, list):
            payload = raw
        elif isinstance(raw, bytes):
            encoded = raw
            if transaction_type and encoded and encoded[0] == transaction_type:
                encoded = encoded[1:]
            payload = rlp.decode(encoded)
        else:
            die(f"t8n body entry {index} has unknown shape")
        if not isinstance(payload, list):
            die(f"t8n body entry {index} is not an RLP transaction payload")
        transactions.append(
            payload if transaction_type == 0
            else bytes([transaction_type]) + bytes(rlp.encode(payload))
        )
    return transactions


def block_document(
    name: str,
    alloc: Mapping[str, Mapping[str, object]],
    transactions: Sequence[Mapping[str, object]],
    *,
    root: Path,
    profile: Mapping[str, object],
    check: Callable[[object, Mapping[str, object], Sequence[Mapping[str, object]]], Mapping[str, object]],
) -> tuple[dict[str, object], Mapping[str, object]]:
    genesis, genesis_hash, environment = transition_environment(alloc)
    genesis_value, _ = header(genesis)
    outputs = _run_transition(
        alloc, environment, transactions,
        root=root, profile=profile, state_test=False,
    )
    receipts = validate_result(outputs.result, len(transactions), name)
    metadata = check(outputs.alloc, outputs.result, receipts)
    result = outputs.result
    if not isinstance(result, dict):
        die(f"{name}: malformed transition result")
    block: dict[str, str] = {
        "parentHash": genesis_hash,
        "uncleHash": EMPTY_OMMER_HASH,
        "coinbase": COINBASE,
        "stateRoot": str(result["stateRoot"]),
        "transactionsTrie": str(result["txRoot"]),
        "receiptTrie": str(result["receiptsRoot"]),
        "bloom": str(result["logsBloom"]),
        "difficulty": "0x00",
        "number": "0x01",
        "gasLimit": genesis["gasLimit"],
        "gasUsed": q(str(result["gasUsed"])),
        "timestamp": str(environment["currentTimestamp"]),
        "extraData": "0x",
        "mixHash": str(environment["currentRandom"]),
        "nonce": "0x0000000000000000",
        "baseFeePerGas": q(str(result["currentBaseFee"])),
        "withdrawalsRoot": str(result.get("withdrawalsRoot", EMPTY_TRIE_ROOT)),
        "blobGasUsed": "0x00",
        "excessBlobGas": q(str(result.get("currentExcessBlobGas", "0x0"))),
        "parentBeaconBlockRoot": str(environment["parentBeaconBlockRoot"]),
        "requestsHash": str(result["requestsHash"]),
    }
    block_value, block_hash = header(block)
    encoded_transactions = typed_body_transactions(outputs.body, transactions)
    fixture_name = f"blanc/weth10-current-mainnet::{name}[fork_BPO2-blockchain_test]"
    fixture = {
        fixture_name: {
            "network": "BPO2",
            "genesisBlockHeader": {**genesis, "hash": genesis_hash},
            "pre": norm_alloc(alloc),
            "postState": norm_alloc(outputs.alloc),
            "lastblockhash": block_hash,
            "config": {
                "network": "BPO2",
                "chainid": "0x01",
                "blobSchedule": {"BPO2": profile_blob_schedule(profile)},
            },
            "genesisRLP": "0x" + bytes(
                rlp.encode([genesis_value, [], [], []])
            ).hex(),
            "blocks": [{
                "rlp": "0x" + bytes(
                    rlp.encode([block_value, encoded_transactions, [], []])
                ).hex(),
                "blocknumber": "1",
            }],
            "sealEngine": "NoProof",
        }
    }
    return fixture, metadata


def expected_sender_balance(initial: int, gas: Sequence[int]) -> int:
    return initial - sum(gas) * GAS_PRICE


def independently_fold_holder_flow(
    initial: int,
    amounts: Sequence[int],
    statuses: Sequence[bool],
) -> dict[str, object]:
    if len(amounts) != len(statuses):
        die("holder-flow fold received mismatched amount/status vectors")
    booked = initial
    outflow = 0
    accepted = 0
    for amount, succeeded in zip(amounts, statuses):
        if succeeded:
            if amount > booked:
                die("holder-flow fold underflowed the independent booking")
            booked -= amount
            outflow += amount
            accepted += 1
    if booked + outflow != initial:
        die("holder-flow fold does not conserve the initial booking")
    return {
        "initialBooked": initial,
        "finalBooked": booked,
        "successfulOutflow": outflow,
        "successfulTransactions": accepted,
        "conservationChecked": True,
    }


def creation_case(
    artifacts: Artifacts,
    *,
    root: Path,
    profile: Mapping[str, object],
) -> tuple[dict[str, object], Mapping[str, object]]:
    sender = derive_address(CREATION_KEY)
    target = create_address(sender, 0)
    if target != EXPECTED_CREATION_TARGET:
        die(
            f"fresh CREATE target differs: expected {EXPECTED_CREATION_TARGET}, got {target}"
        )
    alloc = neutral_system_alloc(artifacts.system_code)
    alloc[sender] = account(SENDER_BALANCE)
    if target in alloc:
        die("fresh CREATE target collides with the authored pre-state")
    transaction = type2_transaction(
        CREATION_KEY, 0, "", artifacts.initcode,
    )

    def check(post: object, result: Mapping[str, object], receipts):
        statuses = tuple(
            receipt_status(receipt, f"creation/receipt-{index}")
            for index, receipt in enumerate(receipts)
        )
        gas = per_transaction_gas(receipts, "creation")
        logs = tuple(receipt_logs(receipt, "creation") for receipt in receipts)
        if statuses != (True,):
            die(
                f"creation receipt did not succeed: {statuses}; "
                f"receipt={receipts[0]!r}"
            )
        if logs != ((),):
            die("creation receipt emitted a log")
        installed = normalized_account(post, target, "creation/target")
        if installed != {
            "nonce": 1,
            "balance": 0,
            "code": artifacts.transaction_runtime,
            "storage": {},
        }:
            die("creation did not install the exact evaluated target family member")
        sender_post = normalized_account(post, sender, "creation/sender")
        if sender_post != {
            "nonce": 1,
            "balance": expected_sender_balance(SENDER_BALANCE, gas),
            "code": b"",
            "storage": {},
        }:
            die("creation sender nonce/fee transition differs")
        for address in NEUTRAL_SYSTEM_ADDRESSES:
            before = normalized_account(alloc, address, f"creation/system-pre/{address}")
            after = normalized_account(post, address, f"creation/system-post/{address}")
            if before != after or after != {
                "nonce": 1, "balance": 0, "code": artifacts.system_code, "storage": {},
            }:
                die(f"creation system program was not state-neutral at {address}")
        if int(str(result["gasUsed"]), 16) != gas[0]:
            die("creation block gas differs from its sole receipt")
        return {
            "name": "01-creation",
            "timestamp": CREATION_TIMESTAMP,
            "transactionType": 2,
            "transactionGasLimit": TRANSACTION_GAS_LIMIT,
            "transactionGasCap": TRANSACTION_GAS_CAP,
            "receiptSucceeded": True,
            "receiptGasUsed": gas[0],
            "logCount": 0,
            "sender": sender,
            "createTarget": target,
            "installedRuntime": {
                "byteLength": len(artifacts.transaction_runtime),
                "sha256": sha256_bytes(artifacts.transaction_runtime),
            },
            "storageEmpty": True,
            "neutralSystemPrograms": list(NEUTRAL_SYSTEM_ADDRESSES),
            "assertionClasses": [
                "fresh-top-level-type2",
                "BPO2-timestamp",
                "successful-receipt",
                "exact-create-target",
                "exact-evaluated-family-member",
                "empty-target-storage",
                "empty-logs",
                "exact-target-balance-nonce",
                "exact-sender-fee-nonce",
                "four-state-neutral-system-programs",
                "EIP-7825-transaction-gas-cap",
            ],
        }

    return block_document(
        "01-creation", alloc, [transaction],
        root=root, profile=profile, check=check,
    )


def type2_redemption_case(
    artifacts: Artifacts,
    *,
    root: Path,
    profile: Mapping[str, object],
) -> tuple[dict[str, object], Mapping[str, object]]:
    owner = derive_address(TYPE2_OWNER_KEY)
    amounts = (0, 3, 8)
    alloc = neutral_system_alloc(artifacts.system_code)
    alloc[WETH10] = account(
        10, artifacts.mainnet_runtime, storage={balance_slot(owner): 10}
    )
    alloc[owner] = account(10**18)
    transactions = [
        type2_transaction(
            TYPE2_OWNER_KEY, nonce, WETH10, withdraw_calldata(RECIPIENT, amount)
        )
        for nonce, amount in enumerate(amounts)
    ]

    def check(post: object, _result: Mapping[str, object], receipts):
        statuses = tuple(
            receipt_status(receipt, f"type2-redemption/receipt-{index}")
            for index, receipt in enumerate(receipts)
        )
        if statuses != (True, True, False):
            die(f"type-2 redemption status vector differs: {statuses}")
        gas = per_transaction_gas(receipts, "type2-redemption")
        logs = tuple(
            receipt_logs(receipt, f"type2-redemption/receipt-{index}")
            for index, receipt in enumerate(receipts)
        )
        expected_logs = (
            (transfer_log(owner, 0),),
            (transfer_log(owner, 3),),
            (),
        )
        if logs != expected_logs:
            die("type-2 redemption exact per-receipt burn logs differ")
        target = normalized_account(post, WETH10, "type2-redemption/WETH10")
        if target != {
            "nonce": 1,
            "balance": 7,
            "code": artifacts.mainnet_runtime,
            "storage": {balance_slot(owner): 7},
        }:
            die("type-2 redemption final WETH10 account differs")
        recipient = normalized_account(
            post, RECIPIENT, "type2-redemption/recipient", required=False
        )
        if recipient["balance"] != 3 or recipient["code"] != b"" \
                or recipient["storage"] != {}:
            die("type-2 redemption recipient ETH projection differs")
        owner_post = normalized_account(post, owner, "type2-redemption/owner")
        if owner_post != {
            "nonce": 3,
            "balance": expected_sender_balance(10**18, gas),
            "code": b"",
            "storage": {},
        }:
            die("type-2 redemption owner nonce/fee transition differs")
        flow = independently_fold_holder_flow(10, amounts, statuses)
        if flow["finalBooked"] != 7 or flow["successfulOutflow"] != 3:
            die("type-2 redemption independent holder-flow fold differs")
        return {
            "name": "02-type2-redemption",
            "timestamp": CREATION_TIMESTAMP,
            "transactionTypes": [2, 2, 2],
            "amounts": list(amounts),
            "receiptSucceeded": list(statuses),
            "receiptGasUsed": list(gas),
            "receiptLogs": [list(value) for value in logs],
            "holderFlowTotals": flow,
            "owner": owner,
            "recipient": RECIPIENT,
            "authorizationMutation": "none",
        }

    return block_document(
        "02-type2-redemption", alloc, transactions,
        root=root, profile=profile, check=check,
    )


def type4_authorization_case(
    artifacts: Artifacts,
    *,
    root: Path,
    profile: Mapping[str, object],
) -> tuple[dict[str, object], Mapping[str, object]]:
    owner = derive_address(TYPE4_OWNER_KEY)
    authority = derive_address(AUTHORITY_KEY)
    authorization = sign_authorization(AUTHORITY_KEY, DELEGATE)
    transaction = type4_transaction(
        TYPE4_OWNER_KEY,
        0,
        WETH10,
        withdraw_calldata(authority, 3),
        authorization,
    )
    alloc = neutral_system_alloc(artifacts.system_code)
    alloc[WETH10] = account(
        3, artifacts.mainnet_runtime, storage={balance_slot(owner): 3}
    )
    alloc[owner] = account(10**18)
    alloc[DELEGATE] = account(0, b"\x00", nonce=1)

    def check(post: object, _result: Mapping[str, object], receipts):
        statuses = tuple(
            receipt_status(receipt, "type4-authorization/receipt")
            for receipt in receipts
        )
        if statuses != (True,):
            die(f"type-4 authorization status differs: {statuses}")
        gas = per_transaction_gas(receipts, "type4-authorization")
        logs = receipt_logs(receipts[0], "type4-authorization/receipt")
        if logs != (transfer_log(owner, 3),):
            die("type-4 authorization exact burn log differs")
        target = normalized_account(post, WETH10, "type4-authorization/WETH10")
        if target != {
            "nonce": 1,
            "balance": 0,
            "code": artifacts.mainnet_runtime,
            "storage": {},
        }:
            die("type-4 authorization final WETH10 account differs")
        authority_post = normalized_account(
            post, authority, "type4-authorization/authority"
        )
        expected_designation = bytes.fromhex("ef0100" + DELEGATE.removeprefix("0x"))
        if authority_post != {
            "nonce": 1,
            "balance": 3,
            "code": expected_designation,
            "storage": {},
        }:
            die("type-4 authorization did not mutate recipient code+nonce exactly")
        owner_post = normalized_account(post, owner, "type4-authorization/owner")
        if owner_post != {
            "nonce": 1,
            "balance": expected_sender_balance(10**18, gas),
            "code": b"",
            "storage": {},
        }:
            die("type-4 authorization owner nonce/fee transition differs")
        flow = independently_fold_holder_flow(3, (3,), statuses)
        if flow["finalBooked"] != 0 or flow["successfulOutflow"] != 3:
            die("type-4 authorization independent holder-flow fold differs")
        return {
            "name": "03-type4-authorization",
            "timestamp": CREATION_TIMESTAMP,
            "transactionTypes": [4],
            "amounts": [3],
            "receiptSucceeded": [True],
            "receiptGasUsed": list(gas),
            "receiptLogs": list(logs),
            "holderFlowTotals": flow,
            "owner": owner,
            "recipientAuthority": authority,
            "delegate": DELEGATE,
            "authorizationMutation": "recipient code+nonce",
        }

    return block_document(
        "03-type4-authorization", alloc, [transaction],
        root=root, profile=profile, check=check,
    )


def load_differential_module(sender: str):
    name = "weth10_current_mainnet_differential_source"
    spec = importlib.util.spec_from_file_location(name, DIFFERENTIAL)
    if spec is None or spec.loader is None:
        die(f"cannot load differential scenario source {DIFFERENTIAL}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    old_alice = module.ALICE
    module._KECCAK = keccak256
    # Scenario construction uses these globals for calldata and explicit
    # permit relaying.  The dataclass's already-bound default caller is fixed
    # immediately below after construction.
    module.ALICE = sender
    module.RELAYER = sender
    if "coincurve" not in sys.modules:
        # The preserved Prague differential uses coincurve only to sign the
        # canonical permit row.  The pinned BPO2 closure intentionally ships
        # spec256k1 instead.  Provide the two-method compatibility surface and
        # keep all signing inside that pinned closure.
        compatibility = types.ModuleType("coincurve")

        class CompatiblePrivateKey:
            def __init__(self, value: bytes):
                self._key = PrivateKey(value)
                self.public_key = self._key.public_key

            def sign_recoverable(self, digest: bytes, hasher=None) -> bytes:
                if hasher is not None:
                    die("differential permit requested an unpinned hash callback")
                return self._key.sign_recoverable(digest)

        compatibility.PrivateKey = CompatiblePrivateKey
        sys.modules["coincurve"] = compatibility
    return module, old_alice


def remap_mapping_keys(mapping: Mapping[str, Any], old: str, new: str) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in mapping.items():
        selected = new if canonical_address(key) == canonical_address(old) else key
        if selected in result and result[selected] != value:
            die("scenario address remap produced conflicting values")
        result[selected] = value
    return result


def canonical_matrix_scenarios(lock: Mapping[str, object], sender: str):
    module, old_alice = load_differential_module(sender)
    scenarios = [
        scenario for scenario in module.build_scenarios(lock)
        if "selector-smoke" in scenario.tags or scenario.endpoint == "receive"
    ]
    if len(scenarios) != 28:
        die(f"ordinary matrix has {len(scenarios)} rows instead of 28")
    endpoints = {scenario.endpoint for scenario in scenarios}
    abi = lock.get("abi")
    if not isinstance(abi, dict) or not isinstance(abi.get("functions"), list):
        die("reference lock has no ABI function inventory")
    expected_endpoints = {
        str(row["signature"]) for row in abi["functions"]
        if isinstance(row, dict) and "signature" in row
    } | {"receive"}
    if endpoints != expected_endpoints or len(expected_endpoints) != 28:
        die(
            "ordinary matrix endpoint inventory differs: "
            f"missing={sorted(expected_endpoints - endpoints)}, "
            f"extra={sorted(endpoints - expected_endpoints)}"
        )
    for scenario in scenarios:
        if canonical_address(scenario.caller) == canonical_address(old_alice):
            scenario.caller = sender
        scenario.eth = remap_mapping_keys(scenario.eth, old_alice, sender)
        scenario.balances = remap_mapping_keys(scenario.balances, old_alice, sender)
        scenario.nonces = remap_mapping_keys(scenario.nonces, old_alice, sender)
        scenario.code = remap_mapping_keys(scenario.code, old_alice, sender)
        scenario.storage = remap_mapping_keys(scenario.storage, old_alice, sender)
        scenario.allowances = {
            (
                sender if canonical_address(owner) == canonical_address(old_alice) else owner,
                sender if canonical_address(spender) == canonical_address(old_alice) else spender,
            ): value
            for (owner, spender), value in scenario.allowances.items()
        }
        scenario.observe_addresses = list(dict.fromkeys(
            sender if canonical_address(value) == canonical_address(old_alice) else value
            for value in scenario.observe_addresses
        ))
        scenario.observe_pairs = list(dict.fromkeys(
            (
                sender if canonical_address(owner) == canonical_address(old_alice) else owner,
                sender if canonical_address(spender) == canonical_address(old_alice) else spender,
            )
            for owner, spender in scenario.observe_pairs
        ))
        scenario.eth.setdefault(sender, SENDER_BALANCE)
        if scenario.caller != sender:
            die(f"matrix row {scenario.name} has no known signing key")
        if scenario.world != "mainnet-chain1" or scenario.weth != WETH10:
            die(f"matrix row {scenario.name} escaped the mainnet identity world")
    return sorted(scenarios, key=lambda scenario: scenario.endpoint)


def matrix_alloc(
    scenario,
    runtime: bytes,
    artifacts: Artifacts,
    side: str,
) -> dict[str, dict[str, object]]:
    if side not in ("reference", "blanc"):
        die(f"unknown matrix side: {side}")
    addresses = {
        canonical_address(value)
        for value in (
            list(scenario.observe_addresses)
            + list(scenario.eth)
            + list(scenario.code)
            + list(scenario.storage)
            + list(scenario.balances)
            + list(scenario.nonces)
            + [scenario.weth, scenario.caller]
            + [address for pair in scenario.allowances for address in pair]
        )
    }
    storage: dict[str, dict[int, int]] = {
        canonical_address(address): {int(slot): int(value) for slot, value in slots.items()}
        for address, slots in scenario.storage.items()
    }
    weth_storage = storage.setdefault(WETH10, {})
    balance_key = solidity_balance_slot if side == "reference" else balance_slot
    nonce_key = solidity_nonce_slot if side == "reference" else blanc_nonce_slot
    allowance_key = solidity_allowance_slot if side == "reference" else blanc_allowance_slot
    for address, value in scenario.balances.items():
        weth_storage[balance_key(address)] = int(value)
    for address, value in scenario.nonces.items():
        weth_storage[nonce_key(address)] = int(value)
    for (owner, spender), value in scenario.allowances.items():
        weth_storage[allowance_key(owner, spender)] = int(value)
    if scenario.flash_minted:
        weth_storage[3 if side == "reference" else UINT256_MAX] = int(
            scenario.flash_minted
        )
    result = neutral_system_alloc(artifacts.system_code)
    for address in sorted(addresses, key=lambda value: int(value, 16)):
        code = runtime if address == WETH10 else bytes(
            scenario.code.get(address, scenario.code.get(address.lower(), b""))
        )
        balance = int(
            scenario.weth_eth if address == WETH10
            else scenario.eth.get(address, scenario.eth.get(address.lower(), 0))
        )
        result[address] = account(
            balance, code, storage=storage.get(address, {})
        )
    return result


def matrix_state_test_environment() -> dict[str, object]:
    return {
        "currentCoinbase": COINBASE,
        "currentGasLimit": q(BLOCK_GAS_LIMIT),
        "currentNumber": "0x1",
        "currentTimestamp": q(CREATION_TIMESTAMP),
        "currentRandom": ZERO_HASH,
        "currentBaseFee": "0x07",
        "currentExcessBlobGas": "0x00",
        "parentBeaconBlockRoot": ZERO_HASH,
        "blockHashes": {"0": ZERO_HASH},
        "withdrawals": [],
    }


def matrix_projection(
    scenario,
    side: str,
    pre: Mapping[str, Mapping[str, object]],
    post: object,
    result: object,
) -> dict[str, object]:
    receipts = validate_result(result, 1, f"matrix/{scenario.name}/{side}")
    status = receipt_status(receipts[0], f"matrix/{scenario.name}/{side}")
    gas = per_transaction_gas(receipts, f"matrix/{scenario.name}/{side}")[0]
    logs = receipt_logs(receipts[0], f"matrix/{scenario.name}/{side}")
    balance_key = solidity_balance_slot if side == "reference" else balance_slot
    nonce_key = solidity_nonce_slot if side == "reference" else blanc_nonce_slot
    allowance_key = solidity_allowance_slot if side == "reference" else blanc_allowance_slot
    observed_addresses = sorted(
        {canonical_address(address) for address in scenario.observe_addresses},
        key=lambda value: int(value, 16),
    )
    observed_pairs = sorted(
        {
            (canonical_address(owner), canonical_address(spender))
            for owner, spender in scenario.observe_pairs
        }
    )
    logical = {
        "balances": {
            address: q(storage_value(post, WETH10, balance_key(address)))
            for address in observed_addresses
        },
        "nonces": {
            address: q(storage_value(post, WETH10, nonce_key(address)))
            for address in observed_addresses
        },
        "allowances": {
            owner + "/" + spender: q(
                storage_value(post, WETH10, allowance_key(owner, spender))
            )
            for owner, spender in observed_pairs
        },
        "flashMinted": q(
            storage_value(post, WETH10, 3 if side == "reference" else UINT256_MAX)
        ),
    }
    auxiliary = {
        canonical_address(address): {
            q(slot): q(value)
            for slot, value in normalized_account(
                post, address, f"matrix/{scenario.name}/{side}/aux/{address}",
                required=False,
            )["storage"].items()
        }
        for address in sorted(scenario.code, key=lambda value: int(value, 16))
    }
    eth_addresses = sorted(
        set(observed_addresses)
        | {canonical_address(address) for address in scenario.code}
        | {WETH10, canonical_address(scenario.caller)},
        key=lambda value: int(value, 16),
    )
    sender = canonical_address(scenario.caller)
    fee_neutral_eth: dict[str, str] = {}
    for address in eth_addresses:
        final_balance = int(normalized_account(
            post, address, f"matrix/{scenario.name}/{side}/eth/{address}",
            required=False,
        )["balance"])
        fee_neutral_eth[address] = q(
            final_balance + (gas * GAS_PRICE if address == sender else 0)
        )
    sender_initial = int(normalized_account(
        pre, sender, f"matrix/{scenario.name}/{side}/sender-pre"
    )["balance"])
    sender_final = int(normalized_account(
        post, sender, f"matrix/{scenario.name}/{side}/sender-post"
    )["balance"])
    sender_delta_excluding_fees = sender_final - sender_initial + gas * GAS_PRICE
    return {
        "receiptSucceeded": status,
        "receiptGasUsed": gas,
        "logs": list(logs),
        "projectedStorage": logical,
        "auxiliaryStorage": auxiliary,
        "feeNeutralEth": fee_neutral_eth,
        "senderDeltaExcludingFees": sender_delta_excluding_fees,
    }


def execute_matrix_side(
    scenario,
    runtime: bytes,
    artifacts: Artifacts,
    side: str,
    *,
    root: Path,
    profile: Mapping[str, object],
) -> dict[str, object]:
    alloc = matrix_alloc(scenario, runtime, artifacts, side)
    transaction = type2_transaction(
        MATRIX_KEY, 0, WETH10, bytes(scenario.calldata), value=int(scenario.value)
    )
    outputs = _run_transition(
        alloc,
        matrix_state_test_environment(),
        [transaction],
        root=root,
        profile=profile,
        state_test=True,
    )
    return matrix_projection(scenario, side, alloc, outputs.alloc, outputs.result)


def ordinary_matrix(
    artifacts: Artifacts,
    lock: Mapping[str, object],
    installed_runtime: bytes,
    *,
    root: Path,
    profile: Mapping[str, object],
) -> dict[str, object]:
    sender = derive_address(MATRIX_KEY)
    scenarios = canonical_matrix_scenarios(lock, sender)
    rows: list[dict[str, object]] = []
    comparison_fields = (
        "receiptSucceeded", "logs", "projectedStorage", "auxiliaryStorage",
        "feeNeutralEth", "senderDeltaExcludingFees",
    )
    for scenario in scenarios:
        reference = execute_matrix_side(
            scenario, installed_runtime, artifacts, "reference",
            root=root, profile=profile,
        )
        blanc = execute_matrix_side(
            scenario, artifacts.mainnet_runtime, artifacts, "blanc",
            root=root, profile=profile,
        )
        mismatches = [
            field for field in comparison_fields if reference[field] != blanc[field]
        ]
        if mismatches:
            die(
                f"ordinary matrix row {scenario.name} differs on "
                + ", ".join(mismatches)
            )
        if reference["receiptSucceeded"] is not True:
            die(f"ordinary matrix row {scenario.name} is not a successful smoke row")
        rows.append({
            "name": scenario.name,
            "endpoint": scenario.endpoint,
            "transactionType": 2,
            "value": int(scenario.value),
            "creditedChannels": [
                "status", "receipt-gas", "logs", "projected-storage", "ETH",
            ],
            "reference": reference,
            "blanc": blanc,
            "comparison": {
                "equalFields": list(comparison_fields),
                "gasRecordedNotClaimedEqual": True,
            },
        })
    if len(rows) != 28 or len({row["endpoint"] for row in rows}) != 28:
        die("ordinary matrix lost one-to-one selector-plus-receive coverage")
    return {
        "schema": "blanc-weth10-current-mainnet-ordinary-matrix-v1",
        "network": "BPO2",
        "chainId": 1,
        "timestamp": CREATION_TIMESTAMP,
        "identityWorld": {
            "contract": WETH10,
            "caller": sender,
            "deploymentChainId": 1,
        },
        "coverage": {
            "selectors": 27,
            "receive": 1,
            "rows": 28,
            "creditedChannels": [
                "status", "receipt-gas", "logs", "projected-storage", "ETH",
            ],
            "historicalBoundary": HISTORICAL_BOUNDARY,
        },
        "runtimes": {
            "lockedDeployed": {
                "byteLength": len(installed_runtime),
                "sha256": sha256_bytes(installed_runtime),
            },
            "evaluatedBlancMainnet": {
                "byteLength": len(artifacts.mainnet_runtime),
                "sha256": sha256_bytes(artifacts.mainnet_runtime),
            },
        },
        "rows": rows,
    }


def load_reference_lock() -> tuple[dict[str, object], bytes]:
    try:
        lock = json.loads(REFERENCE_LOCK.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        die(f"cannot read WETH10 reference lock: {exc}")
    if not isinstance(lock, dict):
        die("WETH10 reference lock is not an object")
    runtime = lock.get("runtime")
    abi = lock.get("abi")
    if not isinstance(runtime, dict) or not isinstance(abi, dict):
        die("WETH10 reference lock lacks runtime/ABI objects")
    installed_hex = runtime.get("installedHex")
    installed_digest = runtime.get("installedSha256")
    if not isinstance(installed_hex, str) or re.fullmatch(
        r"0x(?:[0-9a-f]{2})+", installed_hex
    ) is None or not isinstance(installed_digest, str):
        die("WETH10 reference lock has malformed installed runtime fields")
    installed = bytes.fromhex(installed_hex[2:])
    if sha256_bytes(installed) != installed_digest:
        die("WETH10 reference lock installed runtime digest is inconsistent")
    functions = abi.get("functions")
    if abi.get("functionCount") != 27 or not isinstance(functions, list) \
            or len(functions) != 27:
        die("WETH10 reference lock does not own exactly 27 functions")
    selectors = [
        str(row.get("selector", "")).removeprefix("0x").lower()
        for row in functions if isinstance(row, dict)
    ]
    if len(selectors) != 27 or any(
        re.fullmatch(r"[0-9a-f]{8}", selector) is None for selector in selectors
    ) or len(set(selectors)) != 27:
        die("WETH10 reference lock selector inventory is malformed")
    return lock, installed


def load_runtime_lock(profile: Mapping[str, object]) -> dict[str, object]:
    try:
        lock = json.loads(RUNTIME_LOCK.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        die(f"cannot read current-mainnet runtime lock: {exc}")
    if not isinstance(lock, dict) or lock.get("schema") != 2:
        die("current-mainnet runtime lock schema differs")
    target = lock.get("target")
    platforms = lock.get("platforms")
    profile_target = profile.get("target")
    if not isinstance(target, dict) or not isinstance(platforms, dict) \
            or not isinstance(profile_target, dict):
        die("current-mainnet runtime lock shape differs")
    if target.get("checkoutCommit") != profile_target.get("checkoutCommit"):
        die("runtime lock and verified profile target commits differ")
    if set(platforms) != {"macos-arm64", "linux-x86_64"}:
        die("shared current-mainnet runtime lock is not the exact two-platform lock")
    return lock


def check_or_write(files: Mapping[str, str], *, write: bool) -> None:
    expected = set(files)
    if write:
        OUT.mkdir(parents=True, exist_ok=True)
        for name, content in sorted(files.items()):
            path = OUT / name
            temporary = path.with_name(f".{path.name}.tmp")
            temporary.write_text(content, encoding="utf-8")
            temporary.replace(path)
        for stale in OUT.glob("*.json"):
            if stale.name not in expected:
                stale.unlink()
        return
    actual = {path.name for path in OUT.glob("*.json")}
    missing = sorted(expected - actual)
    orphaned = sorted(actual - expected)
    if missing or orphaned:
        die(f"generated output population differs: missing={missing}, orphaned={orphaned}")
    for name, content in sorted(files.items()):
        path = OUT / name
        if path.read_text(encoding="utf-8") != content:
            die(f"generated output differs: {path}; run wrapper with --write")


def manifest_document(
    *,
    profile: Mapping[str, object],
    runtime_lock: Mapping[str, object],
    artifacts: Artifacts,
    installed_runtime: bytes,
    timestamp_pin: int,
    blocks: Sequence[tuple[str, str, Mapping[str, object]]],
    matrix_rendered: str,
) -> dict[str, object]:
    target = profile.get("target")
    execution = profile.get("execution")
    compiler = profile.get("compiler")
    if not isinstance(target, dict) or not isinstance(execution, dict) \
            or not isinstance(compiler, dict):
        die("verified current-mainnet profile shape differs")
    block_rows = [
        {
            "file": filename,
            "sha256": sha256_bytes(rendered.encode()),
            "metadata": metadata,
        }
        for filename, rendered, metadata in blocks
    ]
    return {
        "schema": "blanc-weth10-current-mainnet-v1",
        "claim": (
            "additive BPO2 non-vacuity for evaluated Blanc WETH10; Prague remains "
            "the historical differential owner"
        ),
        "profile": {
            "executionFork": execution.get("fork"),
            "executionModule": execution.get("module"),
            "chainId": execution.get("chainId"),
            "reward": execution.get("reward"),
            "logicalCompilerFork": compiler.get("logicalFork"),
            "testingBackend": compiler.get("testingBackend"),
            "externalSolcInvoked": compiler.get("externalSolcInvoked"),
            "targetCheckoutCommit": target.get("checkoutCommit"),
        },
        "sharedRuntimeLock": {
            "path": str(RUNTIME_LOCK.relative_to(ROOT)),
            "sha256": sha256_file(RUNTIME_LOCK),
            "schema": runtime_lock.get("schema"),
            "platforms": sorted(runtime_lock["platforms"]),
            "targetCheckoutCommit": runtime_lock["target"]["checkoutCommit"],
        },
        "referenceRuntimeLock": {
            "path": str(REFERENCE_LOCK.relative_to(ROOT)),
            "sha256": sha256_file(REFERENCE_LOCK),
            "installedRuntime": {
                "byteLength": len(installed_runtime),
                "sha256": sha256_bytes(installed_runtime),
            },
        },
        "leanEvaluators": {
            "deployment": {
                "path": "scripts/eval-weth10-deployment-code.lean",
                "outputSha256": artifacts.deployment_digest,
            },
            "differential": {
                "path": "scripts/eval-weth10-differential-code.lean",
                "outputSha256": artifacts.runtime_digest,
            },
            "evaluatedInitcode": {
                "byteLength": len(artifacts.initcode),
                "sha256": sha256_bytes(artifacts.initcode),
            },
            "evaluatedMainnetRuntime": {
                "byteLength": len(artifacts.mainnet_runtime),
                "sha256": sha256_bytes(artifacts.mainnet_runtime),
            },
            "evaluatedTransactionRuntime": {
                "byteLength": len(artifacts.transaction_runtime),
                "sha256": sha256_bytes(artifacts.transaction_runtime),
            },
            "evaluatedNeutralSystemProgram": {
                "byteLength": len(artifacts.system_code),
                "sha256": sha256_bytes(artifacts.system_code),
            },
            "evaluatedSelectorInventory": {
                "count": len(artifacts.selectors),
                "selectors": ["0x" + selector for selector in artifacts.selectors],
            },
        },
        "timestampPin": {
            "leanSource": str(MAINNET_SOURCE.relative_to(ROOT)),
            "definition": "weth10CurrentMainnetCreationTimestamp",
            "value": timestamp_pin,
            "mainnetBpo2Activation": MAINNET_BPO2_ACTIVATION_TIMESTAMP,
            "atOrAfterActivation": timestamp_pin >= MAINNET_BPO2_ACTIVATION_TIMESTAMP,
        },
        "historicalBoundary": HISTORICAL_BOUNDARY,
        "outputs": {
            "blocks": block_rows,
            "ordinaryMatrix": {
                "file": "ordinary-call-matrix.json",
                "sha256": sha256_bytes(matrix_rendered.encode()),
                "rows": 28,
                "selectors": 27,
                "receive": 1,
            },
        },
    }


def fixture_payload(
    fixture: Mapping[str, object], label: str
) -> Mapping[str, object]:
    if len(fixture) != 1:
        die(f"{label}: fixture must contain exactly one test")
    payload = next(iter(fixture.values()))
    if not isinstance(payload, dict):
        die(f"{label}: fixture payload is not an object")
    return payload


def fixture_block_timestamp(fixture: Mapping[str, object], label: str) -> int:
    payload = fixture_payload(fixture, label)
    try:
        blocks = payload["blocks"]
        if not isinstance(blocks, list) or len(blocks) != 1 \
                or not isinstance(blocks[0], dict):
            raise TypeError("fixture must contain exactly one block object")
        encoded = blocks[0]["rlp"]
        if not isinstance(encoded, str):
            raise TypeError("block RLP is not a hex string")
        decoded = rlp.decode(hex_to_bytes(encoded))
        if not isinstance(decoded, list) or not decoded \
                or not isinstance(decoded[0], list) or len(decoded[0]) <= 11:
            raise TypeError("block RLP has no canonical header timestamp")
        raw_timestamp = decoded[0][11]
        if not isinstance(raw_timestamp, bytes):
            raise TypeError("header timestamp is not an RLP byte string")
        return int.from_bytes(raw_timestamp, "big")
    except (KeyError, TypeError, ValueError) as exc:
        die(f"{label}: malformed block timestamp boundary: {exc}")


def fixture_installed_runtime(
    fixture: Mapping[str, object], address: str, label: str
) -> bytes:
    payload = fixture_payload(fixture, label)
    post = payload.get("postState")
    if not isinstance(post, dict):
        die(f"{label}: fixture postState is not an object")
    wanted = int(address, 16)
    matches = [
        account_value for account_address, account_value in post.items()
        if isinstance(account_address, str) and int(account_address, 16) == wanted
    ]
    if len(matches) != 1 or not isinstance(matches[0], dict):
        die(f"{label}: fixture has no unique installed target account")
    code = matches[0].get("code")
    if not isinstance(code, str) or re.fullmatch(r"0x(?:[0-9a-f]{2})*", code) is None:
        die(f"{label}: fixture target code is not canonical lowercase hex")
    return bytes.fromhex(code[2:])


def validate_evidence_bundle(
    *,
    artifacts: Artifacts,
    timestamp_pin: int,
    blocks: Mapping[
        str, tuple[Mapping[str, object], Mapping[str, object]]
    ],
    matrix: Mapping[str, object],
    manifest: Mapping[str, object],
) -> None:
    expected_files = (
        "01-creation-block.json",
        "02-type2-redemption-block.json",
        "03-type4-authorization-block.json",
    )
    if tuple(blocks) != expected_files:
        die("evidence block population/order differs")

    creation_fixture, creation_metadata = blocks[expected_files[0]]
    _type2_fixture, type2_metadata = blocks[expected_files[1]]
    _type4_fixture, type4_metadata = blocks[expected_files[2]]
    if fixture_installed_runtime(
        creation_fixture, EXPECTED_CREATION_TARGET, "installed-runtime"
    ) != artifacts.transaction_runtime:
        die("installed-runtime byte boundary differs")
    if creation_metadata.get("receiptSucceeded") is not True:
        die("creation receipt-status boundary differs")
    if type2_metadata.get("receiptSucceeded") != [True, True, False]:
        die("type-2 redemption receipt-status boundary differs")
    if type4_metadata.get("receiptSucceeded") != [True]:
        die("type-4 authorization receipt-status boundary differs")

    for filename, (fixture, metadata) in blocks.items():
        timestamp = fixture_block_timestamp(fixture, filename)
        if timestamp < MAINNET_BPO2_ACTIVATION_TIMESTAMP:
            die(f"{filename}: block timestamp predates BPO2")
        if timestamp != timestamp_pin or metadata.get("timestamp") != timestamp_pin:
            die(f"{filename}: block/metadata/Lean timestamp boundary differs")

    try:
        timestamp_document = manifest["timestampPin"]
        outputs = manifest["outputs"]
        if not isinstance(timestamp_document, dict) or not isinstance(outputs, dict):
            raise TypeError("manifest timestamp/outputs are not objects")
        if timestamp_document.get("value") != timestamp_pin \
                or timestamp_document.get("mainnetBpo2Activation") \
                != MAINNET_BPO2_ACTIVATION_TIMESTAMP \
                or timestamp_document.get("atOrAfterActivation") is not True:
            die("manifest timestamp pin is stale")
        block_rows = outputs["blocks"]
        if not isinstance(block_rows, list) or len(block_rows) != len(blocks):
            raise TypeError("manifest block rows differ")
        by_name = {
            row.get("file"): row for row in block_rows if isinstance(row, dict)
        }
        if set(by_name) != set(blocks) or len(by_name) != len(block_rows):
            die("manifest block population is stale")
        for filename, (fixture, metadata) in blocks.items():
            row = by_name[filename]
            if row.get("sha256") != sha256_bytes(render_json(fixture).encode()):
                die(f"manifest block digest is stale: {filename}")
            if row.get("metadata") != metadata:
                die(f"manifest block metadata is stale: {filename}")
        matrix_row = outputs["ordinaryMatrix"]
        if not isinstance(matrix_row, dict):
            raise TypeError("manifest ordinary-matrix row is not an object")
        if matrix_row.get("file") != "ordinary-call-matrix.json" \
                or matrix_row.get("sha256") \
                != sha256_bytes(render_json(matrix).encode()):
            die("ordinary-matrix digest is stale")
        if matrix_row.get("rows") != 28 or matrix_row.get("selectors") != 27 \
                or matrix_row.get("receive") != 1:
            die("ordinary-matrix manifest inventory differs")
    except (KeyError, TypeError) as exc:
        die(f"malformed evidence manifest boundary: {exc}")


def fixture_with_timestamp(
    fixture: Mapping[str, object], timestamp: int
) -> dict[str, object]:
    mutant = copy.deepcopy(fixture)
    payload = fixture_payload(mutant, "timestamp-mutant")
    blocks = payload["blocks"]
    if not isinstance(blocks, list) or len(blocks) != 1 \
            or not isinstance(blocks[0], dict):
        die("timestamp mutant cannot locate its sole block")
    decoded = rlp.decode(hex_to_bytes(str(blocks[0]["rlp"])))
    if not isinstance(decoded, list) or not decoded \
            or not isinstance(decoded[0], list) or len(decoded[0]) <= 11:
        die("timestamp mutant cannot locate the header timestamp")
    width = max(1, (timestamp.bit_length() + 7) // 8)
    decoded[0][11] = timestamp.to_bytes(width, "big")
    blocks[0]["rlp"] = "0x" + bytes(rlp.encode(decoded)).hex()
    return mutant


def evidence_boundary_falsifiers(
    *,
    artifacts: Artifacts,
    timestamp_pin: int,
    blocks: Mapping[
        str, tuple[Mapping[str, object], Mapping[str, object]]
    ],
    matrix: Mapping[str, object],
    manifest: Mapping[str, object],
) -> int:
    candidate = {
        "artifacts": artifacts,
        "timestamp_pin": timestamp_pin,
        "blocks": blocks,
        "matrix": matrix,
        "manifest": manifest,
    }
    validate_evidence_bundle(**candidate)

    runtime_blocks = copy.deepcopy(blocks)
    runtime_fixture = runtime_blocks["01-creation-block.json"][0]
    runtime_payload = fixture_payload(runtime_fixture, "installed-runtime-mutant")
    post = runtime_payload["postState"]
    if not isinstance(post, dict):
        die("installed-runtime mutant cannot locate postState")
    target = next(
        (value for key, value in post.items() if int(str(key), 16)
         == int(EXPECTED_CREATION_TARGET, 16)),
        None,
    )
    if not isinstance(target, dict) or not isinstance(target.get("code"), str):
        die("installed-runtime mutant cannot locate target code")
    original_code = target["code"]
    target["code"] = original_code[:-2] + (
        "00" if original_code[-2:] != "00" else "01"
    )

    receipt_blocks = copy.deepcopy(blocks)
    receipt_blocks["02-type2-redemption-block.json"][1][
        "receiptSucceeded"
    ] = [True, False, False]

    timestamp_blocks = copy.deepcopy(blocks)
    timestamp_blocks["01-creation-block.json"] = (
        fixture_with_timestamp(
            timestamp_blocks["01-creation-block.json"][0],
            MAINNET_BPO2_ACTIVATION_TIMESTAMP - 1,
        ),
        timestamp_blocks["01-creation-block.json"][1],
    )

    stale_manifest = copy.deepcopy(manifest)
    stale_manifest["outputs"]["ordinaryMatrix"]["sha256"] = "0" * 64

    mutants = (
        ("installed-runtime", "installed-runtime byte boundary differs",
         {**candidate, "blocks": runtime_blocks}),
        ("receipt-status", "type-2 redemption receipt-status boundary differs",
         {**candidate, "blocks": receipt_blocks}),
        ("sub-BPO2-timestamp", "block timestamp predates BPO2",
         {**candidate, "blocks": timestamp_blocks}),
        ("stale-manifest", "ordinary-matrix digest is stale",
         {**candidate, "manifest": stale_manifest}),
    )
    for label, expected_boundary, mutant in mutants:
        validate_evidence_bundle(**candidate)
        try:
            validate_evidence_bundle(**mutant)
        except RuntimeError as exc:
            if expected_boundary not in str(exc):
                die(f"{label} failed at the wrong boundary: {exc}")
        else:
            die(f"evidence-boundary falsifier survived: {label}")
        validate_evidence_bundle(**candidate)
    if len(mutants) != EVIDENCE_BOUNDARY_FALSIFIERS:
        die("evidence-boundary falsifier count differs")
    return len(mutants)


def synthetic_evidence_bundle() -> dict[str, object]:
    artifacts = Artifacts(
        initcode=b"\x60\x00",
        mainnet_runtime=b"\x60\x00",
        transaction_runtime=b"\x60\x00",
        system_code=b"\x00",
        selectors=tuple(format(index, "08x") for index in range(27)),
        deployment_digest="1" * 64,
        runtime_digest="2" * 64,
    )

    def synthetic_fixture(name: str, *, installed: bool = False) -> dict[str, object]:
        header_fields = [b""] * 12
        header_fields[11] = CREATION_TIMESTAMP.to_bytes(4, "big")
        post_state: dict[str, object] = {}
        if installed:
            post_state[EXPECTED_CREATION_TARGET] = {
                "code": "0x" + artifacts.transaction_runtime.hex()
            }
        return {
            f"synthetic::{name}": {
                "blocks": [{
                    "rlp": "0x" + bytes(
                        rlp.encode([header_fields, [], [], []])
                    ).hex()
                }],
                "postState": post_state,
            }
        }

    blocks: dict[
        str, tuple[Mapping[str, object], Mapping[str, object]]
    ] = {
        "01-creation-block.json": (
            synthetic_fixture("creation", installed=True),
            {"timestamp": CREATION_TIMESTAMP, "receiptSucceeded": True},
        ),
        "02-type2-redemption-block.json": (
            synthetic_fixture("type2"),
            {
                "timestamp": CREATION_TIMESTAMP,
                "receiptSucceeded": [True, True, False],
            },
        ),
        "03-type4-authorization-block.json": (
            synthetic_fixture("type4"),
            {"timestamp": CREATION_TIMESTAMP, "receiptSucceeded": [True]},
        ),
    }
    matrix: dict[str, object] = {"schema": "synthetic", "rows": []}
    manifest: dict[str, object] = {
        "timestampPin": {
            "value": CREATION_TIMESTAMP,
            "mainnetBpo2Activation": MAINNET_BPO2_ACTIVATION_TIMESTAMP,
            "atOrAfterActivation": True,
        },
        "outputs": {
            "blocks": [
                {
                    "file": filename,
                    "sha256": sha256_bytes(render_json(fixture).encode()),
                    "metadata": metadata,
                }
                for filename, (fixture, metadata) in blocks.items()
            ],
            "ordinaryMatrix": {
                "file": "ordinary-call-matrix.json",
                "sha256": sha256_bytes(render_json(matrix).encode()),
                "rows": 28,
                "selectors": 27,
                "receive": 1,
            },
        },
    }
    return {
        "artifacts": artifacts,
        "timestamp_pin": CREATION_TIMESTAMP,
        "blocks": blocks,
        "matrix": matrix,
        "manifest": manifest,
    }


def static_self_check(
    profile: Mapping[str, object],
    reference_lock: Mapping[str, object],
) -> None:
    runtime_lock = load_runtime_lock(profile)
    if set(runtime_lock["platforms"]) != {"macos-arm64", "linux-x86_64"}:
        die("static self-check lost the two-platform runtime-lock boundary")
    sender = derive_address(MATRIX_KEY)
    scenarios = canonical_matrix_scenarios(reference_lock, sender)
    if len(scenarios) != 28:
        die("static self-check lost the 27-selector-plus-receive matrix")
    if set(canonical_system_alloc()) != set(SYSTEM_ADDRESSES):
        die("static self-check lost the five BPO2 system addresses")
    if create_address(derive_address(CREATION_KEY), 0) != EXPECTED_CREATION_TARGET:
        die("static self-check lost the evaluator-pinned CREATE address")
    authorization = sign_authorization(AUTHORITY_KEY, DELEGATE)
    if authorization.get("address") != DELEGATE:
        die("static self-check failed to construct the EIP-7702 authorization")
    signed_by_overlay = type2_transaction(MATRIX_KEY, 0, WETH10, b"")
    if "secretKey" not in signed_by_overlay or any(
        field in signed_by_overlay for field in ("v", "r", "s")
    ):
        die("static self-check lost the current-mainnet secretKey signing shape")
    if CREATION_TIMESTAMP != MAINNET_BPO2_ACTIVATION_TIMESTAMP + 12:
        die("static self-check lost the exact post-activation timestamp")
    if current_mainnet_boundary_falsifiers() != 4:
        die("static self-check lost an API-boundary falsifier")
    if evidence_boundary_falsifiers(**synthetic_evidence_bundle()) \
            != EVIDENCE_BOUNDARY_FALSIFIERS:
        die("static self-check lost an evidence-boundary falsifier")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="explicit current-mainnet target root")
    parser.add_argument("--deployment-artifacts")
    parser.add_argument("--runtime-artifacts")
    parser.add_argument("--wrapper-historical-boundary", required=True)
    parser.add_argument("--wrapper-evidence-falsifiers", type=int, required=True)
    parser.add_argument("--write", action="store_true", help="replace generated JSON")
    parser.add_argument(
        "--static-self-check", action="store_true",
        help="check closed inventories and controls without Lean or t8n",
    )
    args = parser.parse_args(argv)

    validate_current_mainnet_boundary()
    if args.wrapper_historical_boundary != HISTORICAL_BOUNDARY:
        die("wrapper/Python historical-channel boundary differs")
    if args.wrapper_evidence_falsifiers != EVIDENCE_BOUNDARY_FALSIFIERS:
        die("wrapper/Python evidence-boundary falsifier count differs")
    if CREATION_TIMESTAMP < MAINNET_BPO2_ACTIVATION_TIMESTAMP:
        die("authored creation block predates BPO2 activation")
    if TRANSACTION_GAS_LIMIT > TRANSACTION_GAS_CAP:
        die("authored transaction gas limit crosses the BPO2 cap")

    reference_lock, installed_runtime = load_reference_lock()
    profile = load_profile()
    if args.static_self_check:
        if args.write or args.deployment_artifacts or args.runtime_artifacts:
            die("static self-check cannot write or consume evaluator output")
        static_self_check(profile, reference_lock)
        print(
            "OK — WETH10 current-mainnet static self-check: exact five-function "
            "API, 27 selectors + receive, five BPO2 system accounts, CREATE and "
            "timestamp pins, EIP-7702 signer, two-platform runtime lock, four "
            "API-boundary and four evidence-boundary falsifiers"
        )
        return 0
    if not args.root or not args.deployment_artifacts or not args.runtime_artifacts:
        die("execution mode requires --root and both evaluator artifact files")
    artifacts = load_artifacts(
        Path(args.deployment_artifacts), Path(args.runtime_artifacts)
    )
    timestamp_pin = read_timestamp_pin()

    root = resolve_root(profile, args.root)
    verify_target(root, profile)
    paths = target_paths(root, profile)
    if Path(sys.executable).resolve() != paths.python.resolve():
        die(f"generator must run under {paths.python}, got {Path(sys.executable)}")
    runtime_lock = load_runtime_lock(profile)
    lock_selectors = {
        str(row["selector"]).removeprefix("0x").lower()
        for row in reference_lock["abi"]["functions"]
    }
    if lock_selectors != set(artifacts.selectors):
        die("reference-lock and evaluated Blanc selector inventories differ")

    creation_fixture, creation_metadata = creation_case(
        artifacts, root=root, profile=profile
    )
    type2_fixture, type2_metadata = type2_redemption_case(
        artifacts, root=root, profile=profile
    )
    type4_fixture, type4_metadata = type4_authorization_case(
        artifacts, root=root, profile=profile
    )
    matrix = ordinary_matrix(
        artifacts, reference_lock, installed_runtime,
        root=root, profile=profile,
    )

    block_values = (
        ("01-creation-block.json", render_json(creation_fixture), creation_metadata),
        ("02-type2-redemption-block.json", render_json(type2_fixture), type2_metadata),
        ("03-type4-authorization-block.json", render_json(type4_fixture), type4_metadata),
    )
    matrix_rendered = render_json(matrix)
    manifest = manifest_document(
        profile=profile,
        runtime_lock=runtime_lock,
        artifacts=artifacts,
        installed_runtime=installed_runtime,
        timestamp_pin=timestamp_pin,
        blocks=block_values,
        matrix_rendered=matrix_rendered,
    )
    evidence_falsifiers = evidence_boundary_falsifiers(
        artifacts=artifacts,
        timestamp_pin=timestamp_pin,
        blocks={
            "01-creation-block.json": (creation_fixture, creation_metadata),
            "02-type2-redemption-block.json": (type2_fixture, type2_metadata),
            "03-type4-authorization-block.json": (type4_fixture, type4_metadata),
        },
        matrix=matrix,
        manifest=manifest,
    )
    files = {
        **{filename: rendered for filename, rendered, _metadata in block_values},
        "ordinary-call-matrix.json": matrix_rendered,
        "manifest.json": render_json(manifest),
    }
    check_or_write(files, write=args.write)
    verb = "wrote" if args.write else "checked"
    print(
        f"OK — {verb} WETH10 current-mainnet evidence: 3 BPO2 blocks, "
        f"28 ordinary-call rows, {evidence_falsifiers} three-control "
        f"falsifiers, timestamp {timestamp_pin}, target "
        f"{profile['target']['checkoutCommit'][:12]}"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, RuntimeError) as exc:
        print(f"REGRESSION — WETH10 current-mainnet generation: {exc}", file=sys.stderr)
        sys.exit(1)
