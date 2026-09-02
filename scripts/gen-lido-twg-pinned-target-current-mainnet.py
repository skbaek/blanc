#!/usr/bin/env python3
"""Generate/check the finite Lido CircuitBreaker × TWG BPO2 replay.

The lane executes the literal registered BPO2 target.  It consumes only the
compiler-owned runtimes emitted by the adjacent Lean evaluator and compares
the resulting transaction states and logs with an independently reconstructed
Python model of the two tagged storage layouts.  Its evidence is deliberately
outside every theorem premise.

Normal mode is read-only and byte-compares the committed result.  ``--write``
is the sole writer and is reached only after all four scenario rows agree with
their model projections.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from current_mainnet import (
    load_profile,
    resolve_root,
    run_t8n,
    target_paths,
    verify_target,
)


ROOT = Path(__file__).resolve().parents[1]
SCRIPT_PATH = ROOT / "scripts" / "gen-lido-twg-pinned-target-current-mainnet.py"
WRAPPER_PATH = ROOT / "scripts" / "check-lido-twg-pinned-target-current-mainnet.sh"
EVALUATOR_PATH = ROOT / "scripts" / "eval-lido-twg-pinned-target-current-mainnet.lean"
PROFILE_PATH = ROOT / "scripts" / "current-mainnet-target.json"
RUNTIME_LOCK_PATH = ROOT / "scripts" / "current-mainnet-runtime-lock.json"
HELPER_PATH = ROOT / "scripts" / "current_mainnet.py"
LEDGER_PATH = ROOT / "LIDO_TWG_PRAGUE_TO_OSAKA_APPLICABILITY.md"
BREAKER_MANIFEST_PATH = ROOT / "scripts" / "fixtures" / "lido-circuit-breaker" / "manifest.json"
GATEWAY_MANIFEST_PATH = ROOT / "scripts" / "fixtures" / "lido-twg" / "manifest.json"
BREAKER_REFERENCE_PATH = ROOT / "scripts" / "lido-circuit-breaker-reference.json"
GATEWAY_REFERENCE_PATH = ROOT / "scripts" / "lido-twg-reference.json"
RESULT_PATH = ROOT / "scripts" / "fixtures" / "lido-twg-current-mainnet" / "results.json"

FORMAT = "blanc.lido-twg-pinned-target.current-mainnet-replay"
SCHEMA = 2
CURRENT_MAINNET_PUBLIC_API = {
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
}
SCENARIOS = (
    "family-pause-query-finite",
    "family-pause-query-sentinel",
    "composed-public-pause-finite",
    "composed-public-pause-sentinel",
)
CHANNELS = ("status", "storage", "events", "outputs", "gas")
EXECUTION_MUTANTS = (
    "query-code-empty-return",
    "reentrant-heartbeat-noninterference",
)

UINT256_MAX = 2**256 - 1
LOW252_MASK = 2**252 - 1
ADDRESS_MASK = 2**160 - 1
FINITE_DURATION = 1_814_400
HEARTBEAT_INTERVAL = 2_592_000
BPO2_ACTIVATION_TIMESTAMP = 1_767_747_671
BPO2_TX_MAX_GAS_LIMIT = 16_777_216
BPO2_MAX_RLP_BLOCK_BYTES = 8_388_608
TX_GAS_LIMIT = 1_000_000
BLOCK_GAS_LIMIT = 60_000_000
MAX_AUTHORED_TX_DATA_BYTES = 36
BPO2_HEADER_FIELD_COUNT_UPPER_BOUND = 32
BPO2_HEADER_FIELD_BYTES_UPPER_BOUND = 256
EXPECTED_SINGLETON_RLP_BLOCK_UPPER_BOUND = 8_435
GAS_PRICE = 10
SENDER_BALANCE = 10**30

SENDER = "0x7e5f4552091a69125d5dfcb7b8c2659029395bdf"
SECRET_KEY = "0x" + format(1, "064x")
CIRCUIT_BREAKER = "0x0000000000000000000000000000000000000064"
GATEWAY = "0x0000000000000000000000000000000000000077"
COMPOSED_DRIVER = "0x0000000000000000000000000000000000000099"
ADMIN = "0x3e40d73eb977dc6a537af587d48316fee66e9c8c"
COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"

PAUSE_SELECTOR = bytes.fromhex("76a67a51")
PAUSE_FOR_SELECTOR = bytes.fromhex("f3f449c7")
IS_PAUSED_SELECTOR = bytes.fromhex("b187bd26")
SET_HEARTBEAT_INTERVAL_SELECTOR = bytes.fromhex("71a99c22")
PAUSE_ROLE = int(
    "139c2898040ef16910dc9f44dc697df79363da767d8bc92f2e310312b816e46d",
    16,
)

PAUSER_SET_TOPIC = "0xd92c3c28ed17463268f864776463c4c2154f89b18156d3edf77c0e37d0476913"
PAUSED_TOPIC = "0x32fb7c9891bc4f963c7de9f1186d2a7755c7d6e9f4604dabe1d8bb3027c2f49e"
PAUSE_TRIGGERED_TOPIC = "0x9628d25c6e4299393a2779652c1df703eb599acae5fc406c6ef98e92c9ccd93e"
HEARTBEAT_UPDATED_TOPIC = "0x4ea9e94baeeb3668b47d8d9b4cc8f5a1784d783dd263d7d76f8c10d6a10aed44"
HEARTBEAT_INTERVAL_UPDATED_TOPIC = "0xca0a37da24604276f661e36e2b0e71661bb56f8d13994a5d0f207070125b950c"
MUTANT_HEARTBEAT_INTERVAL = 31_536_000

EXPECTED_BREAKER_RUNTIME_BYTES = 4_282
EXPECTED_BREAKER_RUNTIME_SHA256 = "ff8eb66d66f8e4668af9bf5b687dda082c3729f8cd5ffd24a4b14697389d1505"
EXPECTED_GATEWAY_RUNTIME_BYTES = 15_948
EXPECTED_GATEWAY_RUNTIME_SHA256 = "3b9a9442dd0a33d8fc39471bab2f42aed7189859a2c106709631b2c16e6a22e0"
EXPECTED_GATEWAY_LOCATOR = 0x800


class ReplayError(RuntimeError):
    """The current-mainnet replay failed closed."""


def fail(message: str) -> None:
    raise ReplayError(message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def integer(value: Any, owner: str) -> int:
    try:
        if isinstance(value, str) and value.startswith("0x"):
            return int(value, 16)
        return int(value)
    except (TypeError, ValueError) as exc:
        raise ReplayError(f"{owner}: invalid integer {value!r}") from exc


def quantity(value: int) -> str:
    if value < 0:
        fail("negative quantity")
    return hex(value)


def word(value: int) -> str:
    if value < 0 or value > UINT256_MAX:
        fail(f"word outside uint256: {value}")
    return "0x" + value.to_bytes(32, "big").hex()


def word_bytes(value: int) -> bytes:
    return value.to_bytes(32, "big")


def rlp_string_size_upper_bound(payload_bytes: int) -> int:
    """Encoded size bound without depending on a payload's first byte."""
    if payload_bytes < 0:
        fail("negative RLP payload width")
    if payload_bytes == 0:
        return 1
    if payload_bytes <= 55:
        return 1 + payload_bytes
    length_bytes = (payload_bytes.bit_length() + 7) // 8
    return 1 + length_bytes + payload_bytes


def rlp_list_size_upper_bound(encoded_payload_bytes: int) -> int:
    if encoded_payload_bytes < 0:
        fail("negative RLP list payload width")
    if encoded_payload_bytes <= 55:
        return 1 + encoded_payload_bytes
    length_bytes = (encoded_payload_bytes.bit_length() + 7) // 8
    return 1 + length_bytes + encoded_payload_bytes


def singleton_rlp_block_size_upper_bound() -> int:
    """Conservative current-BPO2 block bound, independent of transaction gas.

    The header allowance covers up to 32 fields, each no wider than the
    256-byte logs bloom.  The singleton legacy transaction uses upper bounds
    for nonce, gas price, gas limit, target, value, the lane's longest calldata,
    EIP-155 v, and full-width r/s.  Ommers and withdrawals are empty lists.
    """
    header_payload = (
        BPO2_HEADER_FIELD_COUNT_UPPER_BOUND
        * rlp_string_size_upper_bound(BPO2_HEADER_FIELD_BYTES_UPPER_BOUND)
    )
    header = rlp_list_size_upper_bound(header_payload)
    transaction_payload = sum(
        rlp_string_size_upper_bound(width)
        for width in (1, 1, 3, 20, 0, MAX_AUTHORED_TX_DATA_BYTES, 1, 32, 32)
    )
    transaction = rlp_list_size_upper_bound(transaction_payload)
    transactions = rlp_list_size_upper_bound(transaction)
    empty_list = 1
    return rlp_list_size_upper_bound(
        header + transactions + empty_list + empty_list
    )


def canonical_address(value: str, owner: str) -> str:
    if not isinstance(value, str) or re.fullmatch(r"0x[0-9a-fA-F]{40}", value) is None:
        fail(f"{owner}: malformed address {value!r}")
    return value.lower()


def address_word(value: str) -> str:
    return word(int(canonical_address(value, "address word"), 16))


def slot(region: int, payload: int) -> int:
    return region * 2**252 | payload


def tagged_slot(region: int, payload: int) -> int:
    return region * 2**252 | (payload & LOW252_MASK)


def role_payload(role: int, account_address: str) -> int:
    return (role ^ (int(account_address, 16) & ADDRESS_MASK)) & LOW252_MASK


def gateway_role_storage(account_address: str) -> dict[int, int]:
    payload = role_payload(PAUSE_ROLE, account_address)
    return {
        tagged_slot(2, payload): PAUSE_ROLE,
        tagged_slot(3, payload): int(account_address, 16),
        tagged_slot(4, payload): 1,
    }


def breaker_storage(
    pauser: str, duration: int, *, target: str = GATEWAY,
) -> dict[int, int]:
    pauser_word = int(pauser, 16)
    target_word = int(target, 16)
    return {
        slot(1, 0): duration,
        slot(1, 1): HEARTBEAT_INTERVAL,
        slot(6, 0): 1,
        slot(6, 1): target_word,
        slot(3, target_word): pauser_word,
        slot(4, target_word): 1,
        slot(5, pauser_word): 1,
        slot(2, pauser_word): BPO2_ACTIVATION_TIMESTAMP + 100,
    }


def expected_breaker_storage(duration: int) -> dict[int, int]:
    return {
        slot(1, 0): duration,
        slot(1, 1): HEARTBEAT_INTERVAL,
    }


def expected_gateway_storage(caller: str, paused_until: int) -> dict[int, int]:
    result = gateway_role_storage(caller)
    result[tagged_slot(1, 0)] = paused_until
    return result


class Assembler:
    """Tiny fixed-label assembler for the two transaction-only drivers."""

    def __init__(self) -> None:
        self.code = bytearray()
        self.labels: dict[str, int] = {}
        self.fixups: list[tuple[int, str]] = []

    def op(self, opcode: int) -> None:
        self.code.append(opcode)

    def push(self, value: int) -> None:
        if value == 0:
            self.op(0x5F)
            return
        size = max(1, (value.bit_length() + 7) // 8)
        if size > 32:
            fail("assembler push wider than 32 bytes")
        self.op(0x5F + size)
        self.code.extend(value.to_bytes(size, "big"))

    def push_label(self, label: str) -> None:
        self.op(0x60)
        self.fixups.append((len(self.code), label))
        self.code.append(0)

    def label(self, name: str) -> None:
        if name in self.labels:
            fail(f"duplicate assembler label {name}")
        self.labels[name] = len(self.code)
        self.op(0x5B)

    def finish(self) -> bytes:
        for offset, label in self.fixups:
            target = self.labels.get(label)
            if target is None or target > 0xFF:
                fail(f"invalid assembler label {label}: {target}")
            self.code[offset] = target
        return bytes(self.code)


def emit_copy_calldata(asm: Assembler) -> None:
    asm.op(0x36)  # CALLDATASIZE
    asm.push(0)
    asm.push(0)
    asm.op(0x37)  # CALLDATACOPY


def emit_call(asm: Assembler, target: str) -> None:
    asm.push(0)  # output size
    asm.push(0)  # output offset
    asm.op(0x36)  # input size
    asm.push(0)  # input offset
    asm.push(0)  # value
    asm.push(int(target, 16))
    asm.op(0x5A)  # GAS
    asm.op(0xF1)  # CALL


def emit_staticcall_word(asm: Assembler, target: str) -> None:
    asm.push(32)  # output size
    asm.push(0)  # output offset
    asm.op(0x36)  # input size
    asm.push(0)  # input offset
    asm.push(int(target, 16))
    asm.op(0x5A)  # GAS
    asm.op(0xFA)  # STATICCALL


def emit_bubble_or_stop(asm: Assembler, success_label: str, fail_label: str) -> None:
    asm.push_label(success_label)
    asm.op(0x57)  # JUMPI consumes the call-success word
    asm.push_label(fail_label)
    asm.op(0x56)  # JUMP


def emit_revert_returndata(asm: Assembler) -> None:
    asm.op(0x3D)
    asm.push(0)
    asm.push(0)
    asm.op(0x3E)  # RETURNDATACOPY
    asm.op(0x3D)
    asm.push(0)
    asm.op(0xFD)  # REVERT


def composed_driver_code() -> bytes:
    asm = Assembler()
    emit_copy_calldata(asm)
    emit_call(asm, CIRCUIT_BREAKER)
    asm.op(0x3D)
    asm.push(0)
    asm.op(0x55)  # slot 0 = exact CircuitBreaker returndata size
    emit_bubble_or_stop(asm, "ok", "fail")
    asm.label("ok")
    asm.op(0x00)
    asm.label("fail")
    emit_revert_returndata(asm)
    return asm.finish()


def family_driver_code() -> bytes:
    asm = Assembler()
    asm.op(0x36)
    asm.push(4)
    asm.op(0x14)  # calldata size == four selects isPaused()
    asm.push_label("query")
    asm.op(0x57)

    emit_copy_calldata(asm)
    emit_call(asm, GATEWAY)
    asm.op(0x3D)
    asm.push(0)
    asm.op(0x55)  # slot 0 = pauseFor returndata size
    emit_bubble_or_stop(asm, "pause_ok", "fail")
    asm.label("pause_ok")
    asm.op(0x00)

    asm.label("query")
    emit_copy_calldata(asm)
    emit_staticcall_word(asm, GATEWAY)
    asm.op(0x3D)
    asm.push(1)
    asm.op(0x55)  # slot 1 = isPaused returndata size
    asm.push(0)
    asm.op(0x51)  # MLOAD
    asm.push(2)
    asm.op(0x55)  # slot 2 = isPaused returned word
    emit_bubble_or_stop(asm, "query_ok", "fail")
    asm.label("query_ok")
    asm.op(0x00)

    asm.label("fail")
    emit_revert_returndata(asm)
    return asm.finish()


def reentrant_noninterference_target_code() -> bytes:
    """A target that writes a protected parent cell through a real callback.

    The target is installed at the official admin address.  Its pause arm calls
    the production CircuitBreaker `setHeartbeatInterval(uint256)` endpoint, so
    the callback runs with the exact immutable admin as `msg.sender`.  Its query
    arm returns canonical true, allowing the outer production pause to finish
    despite the retained parent write.
    """
    asm = Assembler()
    asm.op(0x36)  # CALLDATASIZE
    asm.push(4)
    asm.op(0x14)  # EQ
    asm.push_label("query")
    asm.op(0x57)  # JUMPI

    selector_word = int.from_bytes(SET_HEARTBEAT_INTERVAL_SELECTOR, "big") << 224
    asm.push(selector_word)
    asm.push(0)
    asm.op(0x52)  # MSTORE
    asm.push(MUTANT_HEARTBEAT_INTERVAL)
    asm.push(4)
    asm.op(0x52)  # MSTORE
    asm.push(0)  # output size
    asm.push(0)  # output offset
    asm.push(36)  # input size
    asm.push(0)  # input offset
    asm.push(0)  # value
    asm.push(int(CIRCUIT_BREAKER, 16))
    asm.op(0x5A)  # GAS
    asm.op(0xF1)  # CALL
    emit_bubble_or_stop(asm, "pause_ok", "fail")
    asm.label("pause_ok")
    asm.op(0x00)  # STOP

    asm.label("query")
    asm.push(1)
    asm.push(0)
    asm.op(0x52)  # MSTORE
    asm.push(32)
    asm.push(0)
    asm.op(0xF3)  # RETURN

    asm.label("fail")
    emit_revert_returndata(asm)
    return asm.finish()


@dataclass(frozen=True)
class Artifacts:
    circuit_breaker: bytes
    gateway: bytes


def parse_artifacts(path: Path) -> Artifacts:
    rows: dict[str, bytes] = {}
    locator: int | None = None
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        parts = raw_line.split()
        if not parts:
            continue
        if parts[0] in {"circuit-breaker-runtime", "gateway-runtime"}:
            if len(parts) != 3 or parts[0] in rows:
                fail(f"malformed or duplicate artifact row: {raw_line!r}")
            code = bytes.fromhex(parts[2])
            if len(code) != integer(parts[1], parts[0]):
                fail(f"{parts[0]} evaluator byte length differs")
            rows[parts[0]] = code
        elif parts[0] == "gateway-locator":
            if len(parts) != 2 or locator is not None:
                fail(f"malformed or duplicate gateway locator: {raw_line!r}")
            locator = int(parts[1], 16)
        else:
            fail(f"unknown evaluator row: {raw_line!r}")
    if set(rows) != {"circuit-breaker-runtime", "gateway-runtime"}:
        fail(f"artifact row population differs: {sorted(rows)}")
    if locator != EXPECTED_GATEWAY_LOCATOR:
        fail(f"gateway locator differs: {locator!r}")
    breaker = rows["circuit-breaker-runtime"]
    gateway = rows["gateway-runtime"]
    if len(breaker) != EXPECTED_BREAKER_RUNTIME_BYTES \
            or sha256_bytes(breaker) != EXPECTED_BREAKER_RUNTIME_SHA256:
        fail("compiler-owned CircuitBreaker runtime identity differs")
    if len(gateway) != EXPECTED_GATEWAY_RUNTIME_BYTES \
            or sha256_bytes(gateway) != EXPECTED_GATEWAY_RUNTIME_SHA256:
        fail("compiler-owned gateway runtime identity differs")
    breaker_manifest = json.loads(BREAKER_MANIFEST_PATH.read_text(encoding="utf-8"))
    if breaker_manifest["blanc"]["official"] != {
        "fullCreateByteLength": 5122,
        "fullCreateSha256": "bbf5c2c548a4c56ae9079cdb63f20b607ea8c4dabf853771bd33228099e2fa64",
        "runtimeByteLength": EXPECTED_BREAKER_RUNTIME_BYTES,
        "runtimeSha256": EXPECTED_BREAKER_RUNTIME_SHA256,
    }:
        fail("CircuitBreaker differential manifest artifact identity differs")
    gateway_manifest = json.loads(GATEWAY_MANIFEST_PATH.read_text(encoding="utf-8"))
    if gateway_manifest["artifacts"]["blanc"]["runtime"]["byteLength"] \
            != EXPECTED_GATEWAY_RUNTIME_BYTES:
        fail("gateway differential manifest runtime width differs")
    return Artifacts(breaker, gateway)


def validate_current_mainnet_boundary() -> None:
    """Pin this consumer to the fork-override-free five-function API."""
    tree = ast.parse(SCRIPT_PATH.read_text(encoding="utf-8"))
    legacy_root_name = "EELS" + "_ROOT"
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value == legacy_root_name:
            fail("consumer cross-wires the historical Prague root environment")
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
            fail("consumer bypasses the current-mainnet execution API")
    imports = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module == "current_mainnet"
    ]
    imported = {
        alias.name for node in imports for alias in node.names if alias.asname is None
    }
    if len(imports) != 1 or imported != CURRENT_MAINNET_PUBLIC_API \
            or any(alias.asname is not None for node in imports for alias in node.names):
        fail("consumer must import exactly the five public current-mainnet API names")
    calls = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id in CURRENT_MAINNET_PUBLIC_API
    ]
    counts = {name: 0 for name in CURRENT_MAINNET_PUBLIC_API}
    for call in calls:
        counts[call.func.id] += 1
    if counts != {name: 1 for name in CURRENT_MAINNET_PUBLIC_API}:
        fail(f"current-mainnet public API call inventory differs: {counts}")
    transition = next(call for call in calls if call.func.id == "run_t8n")
    keywords = {keyword.arg: keyword.value for keyword in transition.keywords}
    if len(transition.args) != 3 or set(keywords) != {
        "root", "profile", "state_test", "timeout",
    }:
        fail("run_t8n must have three inputs and four exact keywords")
    if not isinstance(keywords["state_test"], ast.Constant) \
            or keywords["state_test"].value is not True:
        fail("consumer must use explicit state-test semantics")
    if not isinstance(keywords["timeout"], ast.Constant) \
            or keywords["timeout"].value != 120:
        fail("consumer run_t8n timeout must remain exactly 120 seconds")


def validate_wrapper_contract(args: argparse.Namespace) -> None:
    expected = {
        "wrapper_schema": str(SCHEMA),
        "wrapper_scenarios": ",".join(SCENARIOS),
        "wrapper_channels": ",".join(CHANNELS),
        "wrapper_mutants": ",".join(EXECUTION_MUTANTS),
        "wrapper_profile": "executionFork=BPO2,logicalCompilerFork=Osaka,testingBackend=cancun",
        "wrapper_tx_gas_limit": str(TX_GAS_LIMIT),
        "wrapper_rlp_block_size_cap": str(BPO2_MAX_RLP_BLOCK_BYTES),
        "wrapper_rlp_block_upper_bound": str(
            EXPECTED_SINGLETON_RLP_BLOCK_UPPER_BOUND
        ),
        "wrapper_artifacts": (
            f"circuitBreakerBytes={EXPECTED_BREAKER_RUNTIME_BYTES},"
            f"circuitBreakerSha256={EXPECTED_BREAKER_RUNTIME_SHA256},"
            f"gatewayBytes={EXPECTED_GATEWAY_RUNTIME_BYTES},"
            f"gatewaySha256={EXPECTED_GATEWAY_RUNTIME_SHA256},gatewayLocator=0x800"
        ),
        "wrapper_ledger_sha256": sha256_path(LEDGER_PATH),
        "wrapper_runtime_lock_sha256": sha256_path(RUNTIME_LOCK_PATH),
    }
    actual = {key: getattr(args, key) for key in expected}
    if actual != expected:
        fail(f"wrapper contract differs: expected={expected!r}, actual={actual!r}")


def block_environment() -> dict[str, Any]:
    return {
        "currentCoinbase": COINBASE,
        "currentGasLimit": quantity(BLOCK_GAS_LIMIT),
        "currentNumber": "0x1",
        "currentTimestamp": quantity(BPO2_ACTIVATION_TIMESTAMP),
        "currentRandom": "0x" + "00" * 32,
        "currentBaseFee": "0x7",
        "currentExcessBlobGas": "0x0",
        "parentBeaconBlockRoot": "0x" + "11" * 32,
        "blockHashes": {"0x0": "0x" + "22" * 32},
        "withdrawals": [],
    }


def account(
    *, balance: int = 0, code: bytes = b"", nonce: int = 1,
    storage: Mapping[int, int] | None = None,
) -> dict[str, Any]:
    return {
        "balance": quantity(balance),
        "code": "0x" + code.hex(),
        "nonce": quantity(nonce),
        "storage": {
            quantity(key): quantity(value)
            for key, value in sorted((storage or {}).items()) if value != 0
        },
    }


def transaction(nonce: int, to: str, data: bytes) -> dict[str, Any]:
    if len(data) > MAX_AUTHORED_TX_DATA_BYTES:
        fail(
            f"transaction calldata exceeds the RLP bound: "
            f"{len(data)} > {MAX_AUTHORED_TX_DATA_BYTES}"
        )
    return {
        "chainId": "0x1",
        "gas": quantity(TX_GAS_LIMIT),
        "gasPrice": quantity(GAS_PRICE),
        "input": "0x" + data.hex(),
        "nonce": quantity(nonce),
        "secretKey": SECRET_KEY,
        "to": to,
        "type": "0x0",
        "value": "0x0",
    }


def pause_for_calldata(duration: int) -> bytes:
    return PAUSE_FOR_SELECTOR + word_bytes(duration)


def pause_calldata(target: str = GATEWAY) -> bytes:
    return PAUSE_SELECTOR + word_bytes(int(target, 16))


def family_inputs(artifacts: Artifacts, duration: int) -> tuple[Any, Any, Any]:
    driver = family_driver_code()
    gateway_storage = gateway_role_storage(CIRCUIT_BREAKER)
    gateway_storage[tagged_slot(1, 0)] = 0
    alloc = {
        SENDER: account(balance=SENDER_BALANCE, nonce=0),
        CIRCUIT_BREAKER: account(code=driver, storage={0: 1, 1: 1}),
        GATEWAY: account(code=artifacts.gateway, storage=gateway_storage),
    }
    txs = [
        transaction(0, CIRCUIT_BREAKER, pause_for_calldata(duration)),
        transaction(1, CIRCUIT_BREAKER, IS_PAUSED_SELECTOR),
    ]
    return alloc, block_environment(), txs


def composed_inputs(artifacts: Artifacts, duration: int) -> tuple[Any, Any, Any]:
    gateway_storage = gateway_role_storage(CIRCUIT_BREAKER)
    gateway_storage[tagged_slot(1, 0)] = 0
    alloc = {
        SENDER: account(balance=SENDER_BALANCE, nonce=0),
        COMPOSED_DRIVER: account(code=composed_driver_code(), storage={0: 1}),
        CIRCUIT_BREAKER: account(
            code=artifacts.circuit_breaker,
            storage=breaker_storage(COMPOSED_DRIVER, duration),
        ),
        GATEWAY: account(code=artifacts.gateway, storage=gateway_storage),
    }
    return alloc, block_environment(), [transaction(0, COMPOSED_DRIVER, pause_calldata())]


def query_code_mutant_inputs(
    artifacts: Artifacts, duration: int,
) -> tuple[Any, Any, Any]:
    """Install clean STOP code: pause succeeds, but the query returns no word."""
    mutant_code = bytes([0x00])
    alloc = {
        SENDER: account(balance=SENDER_BALANCE, nonce=0),
        COMPOSED_DRIVER: account(code=composed_driver_code(), storage={0: 1}),
        CIRCUIT_BREAKER: account(
            code=artifacts.circuit_breaker,
            storage=breaker_storage(COMPOSED_DRIVER, duration),
        ),
        GATEWAY: account(code=mutant_code, storage=gateway_role_storage(CIRCUIT_BREAKER)),
    }
    return alloc, block_environment(), [transaction(0, COMPOSED_DRIVER, pause_calldata())]


def noninterference_mutant_inputs(
    artifacts: Artifacts, duration: int,
) -> tuple[Any, Any, Any]:
    """Install a target whose callback retains a parent heartbeat-cell write."""
    mutant_code = reentrant_noninterference_target_code()
    alloc = {
        SENDER: account(balance=SENDER_BALANCE, nonce=0),
        COMPOSED_DRIVER: account(code=composed_driver_code(), storage={0: 1}),
        CIRCUIT_BREAKER: account(
            code=artifacts.circuit_breaker,
            storage=breaker_storage(COMPOSED_DRIVER, duration, target=ADMIN),
        ),
        ADMIN: account(code=mutant_code),
    }
    return alloc, block_environment(), [transaction(0, COMPOSED_DRIVER, pause_calldata(ADMIN))]


def execute(
    alloc: Any, environment: Any, txs: Any, *, root: Path, profile: dict[str, Any],
) -> Any:
    return run_t8n(
        alloc,
        environment,
        txs,
        root=root,
        profile=profile,
        state_test=True,
        timeout=120,
    )


def find_account(post: Mapping[str, Any], wanted: str) -> Mapping[str, Any]:
    canonical = canonical_address(wanted, "wanted account")
    matches = [
        item for raw, item in post.items()
        if canonical_address(raw, "post-state address") == canonical
    ]
    if len(matches) != 1 or not isinstance(matches[0], dict):
        fail(f"post-state account {wanted} has {len(matches)} matches")
    return matches[0]


def storage_map(post_account: Mapping[str, Any], owner: str) -> dict[int, int]:
    raw = post_account.get("storage") or {}
    if not isinstance(raw, dict):
        fail(f"{owner}: post storage is not an object")
    result: dict[int, int] = {}
    for key, value in raw.items():
        parsed_key = integer(key, f"{owner} storage key")
        if parsed_key in result:
            fail(f"{owner}: duplicate normalized storage key {parsed_key:#x}")
        parsed_value = integer(value, f"{owner} storage value")
        if parsed_value:
            result[parsed_key] = parsed_value
    return result


def assert_account(
    post: Mapping[str, Any], wanted: str, *, code: bytes,
    storage: Mapping[int, int], owner: str,
) -> None:
    raw = find_account(post, wanted)
    if integer(raw.get("nonce", "0x0"), f"{owner} nonce") != 1:
        fail(f"{owner}: nonce differs")
    if integer(raw.get("balance", "0x0"), f"{owner} balance") != 0:
        fail(f"{owner}: balance differs")
    if raw.get("code", "0x").lower() != "0x" + code.hex():
        fail(f"{owner}: code identity differs")
    expected = {key: value for key, value in storage.items() if value}
    actual = storage_map(raw, owner)
    if actual != expected:
        fail(f"{owner}: exact storage differs: expected={expected!r}, actual={actual!r}")


def normalize_logs(raw_logs: Any, owner: str) -> list[dict[str, Any]]:
    if not isinstance(raw_logs, list):
        fail(f"{owner}: receipt logs are not a list")
    result: list[dict[str, Any]] = []
    for index, raw in enumerate(raw_logs):
        if not isinstance(raw, dict):
            fail(f"{owner}: log {index} is not an object")
        topics = raw.get("topics")
        if not isinstance(topics, list):
            fail(f"{owner}: log {index} topics are not a list")
        normalized_topics: list[str] = []
        for topic in topics:
            if not isinstance(topic, str) \
                    or re.fullmatch(r"0x[0-9a-fA-F]{64}", topic) is None:
                fail(f"{owner}: log {index} topic is malformed")
            normalized_topics.append(topic.lower())
        data = raw.get("data")
        if not isinstance(data, str) \
                or re.fullmatch(r"0x[0-9a-fA-F]*", data) is None:
            fail(f"{owner}: log {index} data are malformed")
        result.append({
            "address": canonical_address(raw.get("address"), f"{owner} log {index}"),
            "topics": normalized_topics,
            "data": data.lower(),
        })
    return result


def receipt_gas(receipts: Sequence[Mapping[str, Any]], owner: str) -> list[int]:
    cumulative: list[int] = []
    for index, receipt in enumerate(receipts):
        raw = receipt.get("cumulativeGasUsed", receipt.get("gasUsed"))
        cumulative.append(integer(raw, f"{owner} receipt {index} gas"))
    if cumulative != sorted(cumulative) or any(value <= 0 for value in cumulative):
        fail(f"{owner}: cumulative receipt gas is not strictly usable")
    result: list[int] = []
    previous = 0
    for value in cumulative:
        if value <= previous:
            fail(f"{owner}: receipt gas did not increase")
        result.append(value - previous)
        previous = value
    return result


def validate_result(outputs: Any, expected_receipts: int, owner: str) -> tuple[list[Any], list[int]]:
    rejected = outputs.result.get("rejected")
    if rejected not in (None, []):
        fail(f"{owner}: transaction rejected: {rejected!r}")
    if outputs.result.get("blockException") is not None:
        fail(f"{owner}: block exception: {outputs.result['blockException']!r}")
    receipts = outputs.result.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != expected_receipts:
        fail(f"{owner}: expected {expected_receipts} receipts, got {receipts!r}")
    for index, receipt in enumerate(receipts):
        if not isinstance(receipt, dict) or receipt.get("status") != "0x1":
            fail(f"{owner}: receipt {index} did not succeed: {receipt!r}")
    gas = receipt_gas(receipts, owner)
    if sum(gas) != integer(outputs.result.get("gasUsed"), f"{owner} block gas"):
        fail(f"{owner}: receipt and block gas differ")
    return receipts, gas


def validate_reverting_result(outputs: Any, owner: str) -> tuple[Mapping[str, Any], int]:
    rejected = outputs.result.get("rejected")
    if rejected not in (None, []):
        fail(f"{owner}: transaction was rejected instead of executed: {rejected!r}")
    if outputs.result.get("blockException") is not None:
        fail(f"{owner}: block exception: {outputs.result['blockException']!r}")
    receipts = outputs.result.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != 1 \
            or not isinstance(receipts[0], dict):
        fail(f"{owner}: expected one executed receipt, got {receipts!r}")
    if receipts[0].get("status") != "0x0":
        fail(f"{owner}: mutant did not drive the outer receipt to status 0")
    gas = receipt_gas(receipts, owner)
    if gas[0] != integer(outputs.result.get("gasUsed"), f"{owner} block gas"):
        fail(f"{owner}: receipt and block gas differ")
    return receipts[0], gas[0]


def paused_log(duration: int) -> dict[str, Any]:
    return {"address": GATEWAY, "topics": [PAUSED_TOPIC], "data": word(duration)}


def family_row(
    artifacts: Artifacts, duration: int, *, root: Path, profile: dict[str, Any],
) -> dict[str, Any]:
    alloc, environment, txs = family_inputs(artifacts, duration)
    pause_outputs = execute(
        alloc, environment, [txs[0]], root=root, profile=profile,
    )
    pause_receipts, pause_gas = validate_result(
        pause_outputs, 1, f"family/{duration}/pauseFor",
    )
    query_outputs = execute(
        pause_outputs.alloc, environment, [txs[1]], root=root, profile=profile,
    )
    query_receipts, query_gas = validate_result(
        query_outputs, 1, f"family/{duration}/isPaused",
    )
    pause_logs = normalize_logs(pause_receipts[0].get("logs", []), "family pause")
    query_logs = normalize_logs(query_receipts[0].get("logs", []), "family query")
    if pause_logs != [paused_log(duration)] or query_logs != []:
        fail(f"family/{duration}: exact event projection differs")
    paused_until = UINT256_MAX if duration == UINT256_MAX \
        else BPO2_ACTIVATION_TIMESTAMP + duration
    assert_account(
        query_outputs.alloc, GATEWAY, code=artifacts.gateway,
        storage=expected_gateway_storage(CIRCUIT_BREAKER, paused_until),
        owner=f"family/{duration} gateway",
    )
    driver_storage = {1: 32, 2: 1}
    assert_account(
        query_outputs.alloc, CIRCUIT_BREAKER, code=family_driver_code(),
        storage=driver_storage, owner=f"family/{duration} output driver",
    )
    return {
        "duration": word(duration),
        "expectedPauseForOutputBytes": 0,
        "expectedIsPausedOutput": word(1),
        "expectedIsPausedOutputBytes": 32,
        "expectedPausedUntil": word(paused_until),
        "gasUsed": {"pauseFor": pause_gas[0], "isPaused": query_gas[0]},
        "logs": pause_logs,
        "receiptStatuses": ["0x1", "0x1"],
        "semanticMismatches": [],
    }


def composed_logs(duration: int, *, target: str = GATEWAY) -> list[dict[str, Any]]:
    return [
        {
            "address": CIRCUIT_BREAKER,
            "topics": [
                PAUSER_SET_TOPIC,
                address_word(target),
                address_word(COMPOSED_DRIVER),
                word(0),
            ],
            "data": "0x",
        },
        paused_log(duration),
        {
            "address": CIRCUIT_BREAKER,
            "topics": [
                PAUSE_TRIGGERED_TOPIC,
                address_word(target),
                address_word(COMPOSED_DRIVER),
            ],
            "data": word(duration),
        },
        {
            "address": CIRCUIT_BREAKER,
            "topics": [HEARTBEAT_UPDATED_TOPIC, address_word(COMPOSED_DRIVER)],
            "data": word(0),
        },
    ]


def composed_row(
    artifacts: Artifacts, duration: int, *, root: Path, profile: dict[str, Any],
) -> dict[str, Any]:
    outputs = execute(*composed_inputs(artifacts, duration), root=root, profile=profile)
    receipts, gas = validate_result(outputs, 1, f"composed/{duration}")
    logs = normalize_logs(receipts[0].get("logs", []), "composed pause")
    expected_logs = composed_logs(duration)
    if logs != expected_logs:
        fail(f"composed/{duration}: exact event projection differs")
    paused_until = UINT256_MAX if duration == UINT256_MAX \
        else BPO2_ACTIVATION_TIMESTAMP + duration
    assert_account(
        outputs.alloc, CIRCUIT_BREAKER, code=artifacts.circuit_breaker,
        storage=expected_breaker_storage(duration),
        owner=f"composed/{duration} CircuitBreaker",
    )
    assert_account(
        outputs.alloc, GATEWAY, code=artifacts.gateway,
        storage=expected_gateway_storage(CIRCUIT_BREAKER, paused_until),
        owner=f"composed/{duration} gateway",
    )
    assert_account(
        outputs.alloc, COMPOSED_DRIVER, code=composed_driver_code(), storage={},
        owner=f"composed/{duration} output driver",
    )
    return {
        "duration": word(duration),
        "expectedPublicPauseOutputBytes": 0,
        "expectedPausedUntil": word(paused_until),
        "gasUsed": {"publicPauseViaDriver": gas[0]},
        "logs": logs,
        "receiptStatus": "0x1",
        "semanticMismatches": [],
    }


def heartbeat_interval_updated_log(old: int, new: int) -> dict[str, Any]:
    return {
        "address": CIRCUIT_BREAKER,
        "topics": [HEARTBEAT_INTERVAL_UPDATED_TOPIC],
        "data": "0x" + word(old)[2:] + word(new)[2:],
    }


def query_code_mutant_row(
    artifacts: Artifacts, *, root: Path, profile: dict[str, Any],
) -> dict[str, Any]:
    duration = FINITE_DURATION
    mutant_code = bytes([0x00])
    outputs = execute(
        *query_code_mutant_inputs(artifacts, duration), root=root, profile=profile,
    )
    receipt, _gas = validate_reverting_result(outputs, "mutant/query-code")
    if normalize_logs(receipt.get("logs", []), "mutant/query-code") != []:
        fail("mutant/query-code: reverted receipt retained logs")
    assert_account(
        outputs.alloc, CIRCUIT_BREAKER, code=artifacts.circuit_breaker,
        storage=breaker_storage(COMPOSED_DRIVER, duration),
        owner="mutant/query-code CircuitBreaker rollback",
    )
    assert_account(
        outputs.alloc, GATEWAY, code=mutant_code,
        storage=gateway_role_storage(CIRCUIT_BREAKER),
        owner="mutant/query-code target rollback",
    )
    assert_account(
        outputs.alloc, COMPOSED_DRIVER, code=composed_driver_code(), storage={0: 1},
        owner="mutant/query-code driver rollback",
    )
    return {
        "installedTargetCode": bytes_identity(mutant_code),
        "outerReceiptStatus": "0x0",
        "productionGatewayCodeIdentity": False,
        "queryReturnedCanonicalWord": False,
        "transactionStorageRolledBack": True,
    }


def noninterference_mutant_row(
    artifacts: Artifacts, *, root: Path, profile: dict[str, Any],
) -> dict[str, Any]:
    duration = FINITE_DURATION
    mutant_code = reentrant_noninterference_target_code()
    outputs = execute(
        *noninterference_mutant_inputs(artifacts, duration),
        root=root,
        profile=profile,
    )
    receipts, _gas = validate_result(outputs, 1, "mutant/noninterference")
    logs = normalize_logs(
        receipts[0].get("logs", []), "mutant/noninterference",
    )
    production = composed_logs(duration, target=ADMIN)
    expected_logs = [
        production[0],
        heartbeat_interval_updated_log(
            HEARTBEAT_INTERVAL, MUTANT_HEARTBEAT_INTERVAL,
        ),
        production[2],
        production[3],
    ]
    if logs != expected_logs:
        fail(
            "mutant/noninterference: retained callback log trace differs: "
            f"expected={expected_logs!r}, actual={logs!r}"
        )
    expected_storage = expected_breaker_storage(duration)
    if expected_storage[slot(1, 1)] == MUTANT_HEARTBEAT_INTERVAL:
        fail("mutant/noninterference: mutation does not change the protected cell")
    expected_storage[slot(1, 1)] = MUTANT_HEARTBEAT_INTERVAL
    assert_account(
        outputs.alloc, CIRCUIT_BREAKER, code=artifacts.circuit_breaker,
        storage=expected_storage,
        owner="mutant/noninterference CircuitBreaker",
    )
    assert_account(
        outputs.alloc, ADMIN, code=mutant_code, storage={},
        owner="mutant/noninterference target",
    )
    assert_account(
        outputs.alloc, COMPOSED_DRIVER, code=composed_driver_code(), storage={},
        owner="mutant/noninterference driver",
    )
    return {
        "callbackTarget": ADMIN,
        "outerReceiptStatus": "0x1",
        "productionEventProjectionAccepted": False,
        "productionProtectedCellProjectionAccepted": False,
        "protectedCell": word(slot(1, 1)),
        "protectedCellBefore": word(HEARTBEAT_INTERVAL),
        "protectedCellAfter": word(MUTANT_HEARTBEAT_INTERVAL),
        "retainedParentWriteObserved": True,
    }


def bytes_identity(value: bytes) -> dict[str, Any]:
    return {"byteLength": len(value), "sha256": sha256_bytes(value)}


def render_summary(
    artifacts: Artifacts, *, root: Path, profile: dict[str, Any],
) -> dict[str, Any]:
    execution_mutants = {
        "query-code-empty-return": query_code_mutant_row(
            artifacts, root=root, profile=profile,
        ),
        "reentrant-heartbeat-noninterference": noninterference_mutant_row(
            artifacts, root=root, profile=profile,
        ),
    }
    if tuple(execution_mutants) != EXECUTION_MUTANTS:
        fail("execution-mutant population or order differs")
    rows = {
        "family-pause-query-finite": family_row(
            artifacts, FINITE_DURATION, root=root, profile=profile,
        ),
        "family-pause-query-sentinel": family_row(
            artifacts, UINT256_MAX, root=root, profile=profile,
        ),
        "composed-public-pause-finite": composed_row(
            artifacts, FINITE_DURATION, root=root, profile=profile,
        ),
        "composed-public-pause-sentinel": composed_row(
            artifacts, UINT256_MAX, root=root, profile=profile,
        ),
    }
    if tuple(rows) != SCENARIOS:
        fail("scenario population or order differs")
    return {
        "artifacts": {
            "circuitBreakerOfficialRuntime": bytes_identity(artifacts.circuit_breaker),
            "gatewayControlRuntime": {
                **bytes_identity(artifacts.gateway),
                "locator": word(EXPECTED_GATEWAY_LOCATOR),
            },
        },
        "boundary": {
            "date": "2026-09-02",
            "claim": (
                "finite replay of the compiler-owned artifacts under literal BPO2 "
                "rules; model-boundary evidence only and never a theorem premise"
            ),
            "liveChainAttestation": False,
            "signedEnvelopeSubstitution": (
                "the composed row preserves the proved last-assignment shape but uses "
                "a non-precompile transaction driver as the pauser because the proof "
                "world's numeric address 0x09 cannot originate a signed transaction"
            ),
        },
        "channels": list(CHANNELS),
        "executionMutants": execution_mutants,
        "format": FORMAT,
        "network": {
            "checkoutCommit": profile["target"]["checkoutCommit"],
            "executionFork": profile["execution"]["fork"],
            "executionModule": profile["execution"]["module"],
            "logicalCompilerFork": profile["compiler"]["logicalFork"],
            "testingBackend": profile["compiler"]["testingBackend"],
            "transactionGasLimit": TX_GAS_LIMIT,
            "transactionGasLimitAtOrBelowEip7825Cap": TX_GAS_LIMIT <= BPO2_TX_MAX_GAS_LIMIT,
            "eip7934MaxRlpBlockBytes": BPO2_MAX_RLP_BLOCK_BYTES,
            "bpo2HeaderFieldCountUpperBound": BPO2_HEADER_FIELD_COUNT_UPPER_BOUND,
            "bpo2HeaderFieldBytesUpperBound": BPO2_HEADER_FIELD_BYTES_UPPER_BOUND,
            "singletonRlpBlockUpperBoundBytes": singleton_rlp_block_size_upper_bound(),
            "singletonRlpBlockUpperBoundBelowEip7934Cap": (
                singleton_rlp_block_size_upper_bound() <= BPO2_MAX_RLP_BLOCK_BYTES
            ),
            "maximumAuthoredTransactionDataBytes": MAX_AUTHORED_TX_DATA_BYTES,
            "zeroBlobInputs": True,
        },
        "provenance": {
            "breakerManifestSha256": sha256_path(BREAKER_MANIFEST_PATH),
            "breakerReferenceSha256": sha256_path(BREAKER_REFERENCE_PATH),
            "currentMainnetHelperSha256": sha256_path(HELPER_PATH),
            "evaluatorSha256": sha256_path(EVALUATOR_PATH),
            "gatewayManifestSha256": sha256_path(GATEWAY_MANIFEST_PATH),
            "gatewayReferenceSha256": sha256_path(GATEWAY_REFERENCE_PATH),
            "generatorSha256": sha256_path(SCRIPT_PATH),
            "ledgerSha256": sha256_path(LEDGER_PATH),
            "profileSha256": sha256_path(PROFILE_PATH),
            "runtimeLockSha256": sha256_path(RUNTIME_LOCK_PATH),
            "wrapperSha256": sha256_path(WRAPPER_PATH),
        },
        "rows": rows,
        "scenarioOrder": list(SCENARIOS),
        "schema": SCHEMA,
        "semanticMismatches": [],
    }


def check_or_write(content: bytes, *, write: bool) -> None:
    if write:
        RESULT_PATH.parent.mkdir(parents=True, exist_ok=True)
        temporary = RESULT_PATH.with_name("." + RESULT_PATH.name + ".tmp")
        temporary.write_bytes(content)
        temporary.replace(RESULT_PATH)
        return
    if not RESULT_PATH.is_file():
        fail(f"current-mainnet result missing: {RESULT_PATH}; run with --write")
    if RESULT_PATH.read_bytes() != content:
        fail(f"current-mainnet result differs: {RESULT_PATH}; run with --write")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--root", help="explicit current-mainnet target root")
    result.add_argument("--blanc-artifacts", type=Path)
    result.add_argument("--write", action="store_true")
    result.add_argument("--static-self-check", action="store_true")
    result.add_argument("--wrapper-schema", required=True)
    result.add_argument("--wrapper-scenarios", required=True)
    result.add_argument("--wrapper-channels", required=True)
    result.add_argument("--wrapper-mutants", required=True)
    result.add_argument("--wrapper-profile", required=True)
    result.add_argument("--wrapper-tx-gas-limit", required=True)
    result.add_argument("--wrapper-rlp-block-size-cap", required=True)
    result.add_argument("--wrapper-rlp-block-upper-bound", required=True)
    result.add_argument("--wrapper-artifacts", required=True)
    result.add_argument("--wrapper-ledger-sha256", required=True)
    result.add_argument("--wrapper-runtime-lock-sha256", required=True)
    return result


def main(argv: list[str] | None = None) -> None:
    args = parser().parse_args(argv)
    validate_current_mainnet_boundary()
    validate_wrapper_contract(args)
    if args.static_self_check:
        if args.root is not None or args.blanc_artifacts is not None or args.write:
            fail("static self-check accepts no execution or write arguments")
        if len(composed_driver_code()) == 0 or len(family_driver_code()) == 0 \
                or len(reentrant_noninterference_target_code()) == 0:
            fail("transaction driver assembly is empty")
        if singleton_rlp_block_size_upper_bound() \
                != EXPECTED_SINGLETON_RLP_BLOCK_UPPER_BOUND:
            fail("singleton RLP block upper-bound derivation differs")
        if EXPECTED_SINGLETON_RLP_BLOCK_UPPER_BOUND > BPO2_MAX_RLP_BLOCK_BYTES:
            fail("singleton RLP block upper bound exceeds EIP-7934")
        print("OK — Lido TWG pinned-target current-mainnet static boundary")
        return
    if args.blanc_artifacts is None:
        fail("--blanc-artifacts is required outside static self-check")
    profile = load_profile()
    root = resolve_root(profile, args.root)
    verify_target(root, profile)
    paths = target_paths(root, profile)
    if Path(sys.executable).resolve() != paths.python.resolve():
        fail(f"replay must run under {paths.python}, got {Path(sys.executable)}")
    artifacts = parse_artifacts(args.blanc_artifacts)
    summary = render_summary(artifacts, root=root, profile=profile)
    check_or_write(canonical_bytes(summary), write=args.write)
    verb = "wrote" if args.write else "checked"
    print(
        f"OK — {verb} Lido CircuitBreaker × TWG BPO2 replay: "
        "2 composed duration arms + 2 family pause/query arms, "
        "2 execution mutants rejected, zero semantic mismatches"
    )


if __name__ == "__main__":
    try:
        main()
    except (
        ReplayError,
        FileNotFoundError,
        ImportError,
        KeyError,
        OSError,
        TypeError,
        UnicodeError,
        ValueError,
    ) as exc:
        print(
            "REGRESSION — Lido CircuitBreaker × TWG BPO2 replay: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
