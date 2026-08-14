#!/usr/bin/env python3
"""Offline, manifest-backed Lido CircuitBreaker Solidity/Blanc differential.

Both implementations are deployed by executing their own complete CREATE
input in a fresh pinned EELS Prague state.  Runtime histories start from that
constructor-produced state.  Solidity bytes are read only from the validated
reference lock; Blanc bytes are read only from the Lean evaluator selected by
the shell gate.  The two raw storage layouts are independently projected onto
one explicit logical state before comparison.

The suite is finite evidence.  It makes no BPO2-execution, raw-slot-equality,
deployed-bytecode-verification, or universal functional-correctness claim.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Mapping, NoReturn, Sequence, Tuple

from lido_circuit_breaker_ac5_shape_schema import (
    Ac5ShapeError,
    CANDIDATE_SHAPE_CASES,
    validate_candidate_shape_against_resource_paths,
    validate_candidate_shape_evidence,
    validate_candidate_parent_shape,
)


REPO = Path(__file__).resolve().parents[1]
LOCK_PATH = REPO / "scripts" / "lido-circuit-breaker-reference.json"
MANIFEST_PATH = REPO / "scripts" / "fixtures" / "lido-circuit-breaker" / "manifest.json"
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
RESOURCE_SCHEMA = 1
RESOURCE_LIFECYCLE = "baseline"
RESOURCE_BASELINE_COMMIT = "fc3edee6dbfb77eaf344afee43c921d48ff8a3af"
RESOURCE_BASELINE_MANIFEST_SHA256 = \
    "6cde638ac37977f3aea228ad877a85d37e415ac4f927e66a099be67de7d30cef"
RESOURCE_BASELINE_BLANC_IDENTITIES = {
    "creationTemplateSha256":
        "3cbf5dec4dacbed0b0d5ee94f01fc0845b602fd67f260031ca693458e32fd28f",
    "officialFullCreateSha256":
        "3e207da94a889e623ecb92719f5782e0506c39d81a0eec2d7f41d14049e1ec2d",
    "officialRuntimeSha256":
        "fa628a48ab7544301c5a4b287315ccff998fb43ec23fc16250f4a4309d9c100a",
    "independentFullCreateSha256":
        "a7eb1fd354306a089af848b0601600b0030ff8d82102bf1cbf8cfaac45e3d8ce",
    "independentRuntimeSha256":
        "c5c98c4e99e43fa3fc61693e730b87e69dc37f6bba38f3adcdeb801c4375835f",
}
DEFAULT_GAS_LIMIT = 20_000_000

CIRCUIT = "0x6019cb557978296ba3c08a7b73225c0975dfb2f7"
CLONE = "0x9999999999999999999999999999999999999999"
CREATE_CALLER = "0x7777777777777777777777777777777777777777"
ADMIN = "0x3e40d73eb977dc6a537af587d48316fee66e9c8c"
INDEPENDENT_ADMIN = "0x111122223333444455556666777788889999aaaa"
OTHER = "0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
PAUSER_A = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
PAUSER_B = "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
PAUSER_D = "0xdddddddddddddddddddddddddddddddddddddddd"
TARGET_1 = "0x1111111111111111111111111111111111111111"
TARGET_2 = "0x2222222222222222222222222222222222222222"
TARGET_3 = "0x3333333333333333333333333333333333333333"
COINBASE = "0x6666666666666666666666666666666666666666"
ZERO = "0x" + "00" * 20
UINT256_MAX = (1 << 256) - 1

OFFICIAL = {
    "admin": ADMIN, "minPauseDuration": 432_000,
    "maxPauseDuration": 5_184_000, "minHeartbeatInterval": 2_592_000,
    "maxHeartbeatInterval": 94_608_000,
    "initialPauseDuration": 1_814_400,
    "initialHeartbeatInterval": 31_536_000,
}
INDEPENDENT = {
    "admin": INDEPENDENT_ADMIN, "minPauseDuration": 60,
    "maxPauseDuration": 86_400, "minHeartbeatInterval": 120,
    "maxHeartbeatInterval": 604_800, "initialPauseDuration": 3_600,
    "initialHeartbeatInterval": 86_400,
}

REGION_SHIFT = 252
CONFIG_REGION, EXPIRY_REGION, ASSIGNMENT_REGION = 1, 2, 3
INDEX_REGION, COUNT_REGION, ARRAY_REGION = 4, 5, 6
LOCK_KEY = 15 << REGION_SHIFT


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def address_bytes(value: str) -> bytes:
    raw = bytes.fromhex(value.removeprefix("0x"))
    if len(raw) != 20:
        die(f"not an address: {value}")
    return raw


def canonical_address(value: str) -> str:
    return "0x" + address_bytes(value).hex()


def address_word(value: str) -> bytes:
    return bytes(12) + address_bytes(value)


def h256(value: int) -> bytes:
    return value.to_bytes(32, "big")


def keccak(data: bytes) -> bytes:
    return bytes(_KECCAK(data))


def selector(signature: str) -> bytes:
    return keccak(signature.encode())[:4]


def calldata(signature: str, *words: int | str, trailing: bytes = b"") -> bytes:
    encoded = []
    for value in words:
        encoded.append(address_word(value) if isinstance(value, str) else h256(value))
    return selector(signature) + b"".join(encoded) + trailing


def constructor_suffix(params: Mapping[str, object]) -> bytes:
    return b"".join([
        address_word(str(params["admin"])), h256(int(params["minPauseDuration"])),
        h256(int(params["maxPauseDuration"])), h256(int(params["minHeartbeatInterval"])),
        h256(int(params["maxHeartbeatInterval"])), h256(int(params["initialPauseDuration"])),
        h256(int(params["initialHeartbeatInterval"])),
    ])


def push(value: int | bytes, width: int | None = None) -> bytes:
    if isinstance(value, int):
        if value < 0:
            die("negative PUSH")
        raw = value.to_bytes(width or max(1, (value.bit_length() + 7) // 8), "big")
    else:
        raw = value.rjust(width, b"\x00") if width else value
    if not 1 <= len(raw) <= 32:
        die(f"invalid PUSH width {len(raw)}")
    return bytes([0x5f + len(raw)]) + raw


def data_result(payload: bytes, revert: bool = False, base_offset: int = 0) -> bytes:
    """Constant-code response supporting return bombs without host literals."""
    op = b"\xfd" if revert else b"\xf3"
    if len(payload) <= 0xffff:
        # Preserve every frozen baseline target byte exactly.
        prefix_len = 13
        return (push(len(payload), 2) + push(base_offset + prefix_len, 2) +
                b"\x5f\x39" + push(len(payload), 2) + b"\x5f" + op + payload)
    if len(payload) > 0xffffff:
        die("target payload exceeds PUSH3 harness bound")
    prefix_len = 16
    data_offset = base_offset + prefix_len
    if data_offset > 0xffffff:
        die("target payload offset exceeds PUSH3 harness bound")
    return (push(len(payload), 3) + push(data_offset, 3) + b"\x5f\x39" +
            push(len(payload), 3) + b"\x5f" + op + payload)


def size_dispatch(pause_body: bytes, query_body: bytes) -> bytes:
    view_pc = 8 + len(pause_body)
    if view_pc > 0xffff:
        die("target dispatcher exceeds PUSH2")
    return b"\x36\x60\x04\x14\x61" + view_pc.to_bytes(2, "big") + b"\x57" + \
        pause_body + b"\x5b" + query_body


def target_code(query_payload: bytes = h256(1), *, pause_revert: bytes | None = None,
                query_revert: bool = False, pause_body: bytes | None = None) -> bytes:
    if pause_body is None:
        pause_body = b"\x00" if pause_revert is None else data_result(
            pause_revert, True, base_offset=8)
    query_offset = 9 + len(pause_body)
    return size_dispatch(pause_body, data_result(
        query_payload, query_revert, base_offset=query_offset))


def nested_call_body(contract: str, nested: bytes, *, bubble: bool,
                     recorder_slot: int = 0) -> bytes:
    """Call a runtime from pauseFor, recording or bubbling the child result."""
    out = bytearray()
    for offset in range(0, len(nested), 32):
        out += push(nested[offset:offset + 32].ljust(32, b"\x00")) + push(offset) + b"\x52"
    out += b"\x5f\x5f" + push(len(nested)) + b"\x5f\x5f"
    out += push(address_bytes(contract)) + b"\x5a\xf1"
    if bubble:
        # If success, stop.  Otherwise copy exact child bytes and revert.
        success_pc = len(out) + 12
        out += b"\x80" + push(success_pc, 2) + b"\x57"
        out += b"\x3d\x5f\x5f\x3e\x3d\x5f\xfd\x5b\x00"
    else:
        out += push(recorder_slot) + b"\x55"
        out += b"\x3d" + push(recorder_slot + 1) + b"\x55"
        out += b"\x3d\x5f\x5f\x3e\x5f\x51" + push(recorder_slot + 2) + b"\x55\x00"
    return bytes(out)


def tagged(region: int, payload: int = 0) -> int:
    return (region << REGION_SHIFT) | payload


def sol_map(address: str, base: int) -> int:
    return int.from_bytes(keccak(address_word(address) + h256(base)), "big")


def sol_array_entry(index: int) -> int:
    return (int.from_bytes(keccak(h256(5)), "big") + index) & UINT256_MAX


def runtime_error(name: str) -> bytes:
    return selector(name + "()")


@dataclass(frozen=True)
class Tx:
    caller: str
    calldata: bytes
    value: int = 0
    timestamp: int = 1_700_000_000
    gas: int = DEFAULT_GAS_LIMIT
    target: str = CIRCUIT


@dataclass
class Case:
    name: str
    family: str
    owner: str
    world: str = "official"
    constructor_params: Dict[str, object] | None = None
    constructor_suffix_override: bytes | None = None
    constructor_value: int = 0
    constructor_trailing: bytes = b""
    history: List[Tx] = field(default_factory=list)
    action: Tx | None = None
    code: Dict[str, bytes] = field(default_factory=dict)
    clone_history: List[Tx] = field(default_factory=list)
    observe_targets: List[str] = field(default_factory=list)
    observe_pausers: List[str] = field(default_factory=list)
    observe_aux_slots: Dict[str, int] = field(default_factory=dict)
    tags: Tuple[str, ...] = ()
    channels: Tuple[str, ...] = (
        "status", "returndata", "state-projection", "eth", "logs", "call-trace"
    )


def rtcase(name: str, family: str, action: Tx, **kwargs) -> Case:
    return Case(name=name, family=family, owner="AC9", action=action, **kwargs)


def ctorcase(name: str, params: Mapping[str, object], **kwargs) -> Case:
    return Case(name=name, family="constructor", owner="AC6/AC9",
                constructor_params=dict(params), **kwargs)


def parse_artifacts(text: str) -> Dict[str, object]:
    result: Dict[str, object] = {
        "offsets": {}, "source-inventories": {}, "projection": {},
    }
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        label = parts[0]
        if label in {"creation-template", "official-create", "official-runtime",
                     "independent-create", "independent-runtime"}:
            if len(parts) != 3:
                die(f"malformed evaluator row {label}")
            code = bytes.fromhex(parts[2])
            if len(code) != int(parts[1]):
                die(f"evaluator length mismatch for {label}")
            result[label] = code
        elif label == "selectors":
            values = [v[-8:].lower() for v in parts[2].split(",")]
            if len(values) != int(parts[1]):
                die("evaluator selector count mismatch")
            result[label] = values
        elif label.startswith("offsets-"):
            values = [] if parts[1] == "0" else [int(v) for v in parts[2].split(",")]
            if len(values) != int(parts[1]):
                die(f"evaluator offset count mismatch for {label}")
            result["offsets"][label.removeprefix("offsets-")] = values
        elif label == "offset-metadata-valid":
            result[label] = parts[1] == "true"
        elif label == "patch-controls-valid":
            result[label] = parts[1] == "true"
        elif label.endswith("-sites"):
            if len(parts) != 3:
                die(f"malformed evaluator source-site row {label}")
            raw_rows = [] if parts[2] == "-" else parts[2].split(",")
            split_rows = [row.split("|") for row in raw_rows]
            if any(len(row) != 3 for row in split_rows):
                die(f"malformed evaluator source-site descriptor {label}")
            values = [{"label": row[0], "offset": int(row[1]), "class": row[2]}
                      for row in split_rows]
            if len(values) != int(parts[1]):
                die(f"evaluator source-site count mismatch for {label}")
            result["source-inventories"][label] = values
        elif label in {"runtime-site-counts", "constructor-site-counts"}:
            if len(parts) != 4:
                die(f"malformed evaluator source-site counts {label}")
            result[label] = {
                "persistent": int(parts[1]), "transient": int(parts[2]),
                "external": int(parts[3]),
            }
        elif label in {"projection-regions", "projection-region-words"}:
            if len(parts) != 3:
                die(f"malformed evaluator projection row {label}")
            pairs = [row.split("|") for row in parts[2].split(",")]
            if len(pairs) != int(parts[1]) or any(len(row) != 2 for row in pairs):
                die(f"evaluator projection count mismatch for {label}")
            key = "regions" if label == "projection-regions" else "regionWords"
            result["projection"][key] = {
                name: int(value) if key == "regions" else "0x" + value
                for name, value in pairs
            }
        elif label == "projection-formula":
            result["projection"]["blancFormula"] = parts[1]
        elif label == "projection-domain":
            qualifiers = [row.split("=", 1) for row in parts[1].split(",")]
            if any(len(row) != 2 for row in qualifiers):
                die("malformed evaluator projection domain qualifiers")
            result["projection"]["domainQualifiers"] = dict(qualifiers)
        elif label == "limits":
            result[label] = tuple(map(int, parts[1:]))
        elif label == "sizes":
            if len(parts) != 9:
                die("malformed evaluator artifact sizes")
            result[label] = {
                "runtimeTemplateBytes": int(parts[1]),
                "officialRuntimeBytes": int(parts[2]),
                "independentRuntimeBytes": int(parts[3]),
                "officialRuntimeHeadroom": int(parts[4]),
                "independentRuntimeHeadroom": int(parts[5]),
                "creationTemplateInitcodeHeadroom": int(parts[6]),
                "officialFullCreateHeadroom": int(parts[7]),
                "independentFullCreateHeadroom": int(parts[8]),
            }
    required = {"creation-template", "official-create", "official-runtime",
                "independent-create", "independent-runtime", "selectors",
                "offset-metadata-valid", "patch-controls-valid", "limits",
                "sizes", "runtime-site-counts", "constructor-site-counts"}
    missing = required - result.keys()
    if missing:
        die(f"Lean evaluator omitted: {sorted(missing)}")
    if set(result["offsets"]) != {"admin", "min-pause", "max-pause",
                                     "min-heartbeat", "max-heartbeat"}:
        die("Lean evaluator immutable offset families incomplete")
    inventory_keys = {
        "runtime-persistent-sites", "runtime-transient-sites", "runtime-external-sites",
        "constructor-persistent-sites", "constructor-transient-sites",
        "constructor-external-sites",
    }
    if set(result["source-inventories"]) != inventory_keys:
        die("Lean evaluator source-site inventories incomplete")
    inventories = result["source-inventories"]
    expected_lengths = {
        "runtime-persistent-sites": 20, "runtime-transient-sites": 3,
        "runtime-external-sites": 2, "constructor-persistent-sites": 2,
        "constructor-transient-sites": 0, "constructor-external-sites": 0,
    }
    actual_lengths = {key: len(inventories[key]) for key in inventory_keys}
    if actual_lengths != expected_lengths:
        die(f"Lean evaluator source-site inventory cardinalities drifted: {actual_lengths}")
    if result["runtime-site-counts"] != {"persistent": 20, "transient": 3, "external": 2}:
        die("Lean evaluator runtime source-syntax site counts drifted")
    if result["runtime-site-counts"] != {
            "persistent": actual_lengths["runtime-persistent-sites"],
            "transient": actual_lengths["runtime-transient-sites"],
            "external": actual_lengths["runtime-external-sites"]}:
        die("Lean evaluator named runtime inventory does not reconcile with syntax counts")
    if result["constructor-site-counts"] != {
            "persistent": actual_lengths["constructor-persistent-sites"],
            "transient": actual_lengths["constructor-transient-sites"],
            "external": actual_lengths["constructor-external-sites"]}:
        die("Lean evaluator named constructor inventory counts do not reconcile")
    projection = result["projection"]
    if projection.get("regions") != {
            "config": 1, "expiry": 2, "assignment": 3,
            "index": 4, "count": 5, "array": 6}:
        die("Lean evaluator projection region ownership drifted")
    if set(projection.get("regionWords", {})) != set(projection["regions"]):
        die("Lean evaluator projection region words incomplete")
    if set(projection.get("domainQualifiers", {})) != {
            "canonical-address-bits", "tag-payload-upper-bound-exclusive",
            "array-index", "zero-count-explicit",
            "targets-nodup", "targets-nonzero", "pausers-nonzero"}:
        die("Lean evaluator projection domain qualifiers incomplete")
    return result


def patch_blanc_runtime(artifacts: Mapping, params: Mapping[str, object]) -> bytes:
    code = bytearray(artifacts["official-runtime"])
    mapping = {
        "admin": int.from_bytes(address_word(str(params["admin"])), "big"),
        "min-pause": int(params["minPauseDuration"]),
        "max-pause": int(params["maxPauseDuration"]),
        "min-heartbeat": int(params["minHeartbeatInterval"]),
        "max-heartbeat": int(params["maxHeartbeatInterval"]),
    }
    for field, value in mapping.items():
        for offset in artifacts["offsets"][field]:
            code[offset:offset + 32] = h256(value)
    return bytes(code)


def patch_solidity_runtime(lock: Mapping, params: Mapping[str, object]) -> bytes:
    code = bytearray(bytes.fromhex(lock["artifacts"]["runtimeTemplate"]["hex"].removeprefix("0x")))
    values = {
        "ADMIN": int.from_bytes(address_word(str(params["admin"])), "big"),
        "MIN_PAUSE_DURATION": int(params["minPauseDuration"]),
        "MAX_PAUSE_DURATION": int(params["maxPauseDuration"]),
        "MIN_HEARTBEAT_INTERVAL": int(params["minHeartbeatInterval"]),
        "MAX_HEARTBEAT_INTERVAL": int(params["maxHeartbeatInterval"]),
    }
    by_name: Dict[str, List[Mapping]] = {}
    for span in lock["artifacts"]["immutableReferenceSpans"]:
        by_name.setdefault(span["name"], []).append(span)
    for name, value in values.items():
        for span in by_name[name]:
            if span["length"] != 32:
                die("Solidity immutable span is not one word")
            start = span["start"]
            code[start:start + 32] = h256(value)
    return bytes(code)


def verify_eels_pin(root: Path) -> None:
    head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(root), "status", "--porcelain"], text=True).strip()
    if head != EELS_PIN or dirty:
        die(f"pinned EELS must be clean at {EELS_PIN}; found {head}, dirty={bool(dirty)}")


def environments(state, timestamp: int, gas: int):
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, TransactionEnvironment
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    block = BlockEnvironment(
        chain_id=U64(1), state=state, block_gas_limit=Uint(30_000_000),
        block_hashes=[Hash32(bytes(32))], coinbase=Address(address_bytes(COINBASE)),
        number=Uint(20_000_000), base_fee_per_gas=Uint(0), time=U256(timestamp),
        prev_randao=Bytes32(bytes(32)), excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(bytes(32)))
    tx = TransactionEnvironment(
        origin=Address(address_bytes(CREATE_CALLER)), gas_price=Uint(0), gas=Uint(gas),
        access_list_addresses=set(), access_list_storage_keys=set(),
        transient_storage=TransientStorage(), blob_versioned_hashes=(),
        authorizations=(), index_in_block=None, tx_hash=None, traces=[])
    return block, tx


def outcome(output) -> str:
    if output.error is None:
        return "success"
    name = type(output.error).__name__
    return "revert" if name == "Revert" else "exception:" + name


def normalized_logs(logs) -> List[Mapping]:
    return [{
        "address": "0x" + bytes(log.address).hex(),
        "topics": ["0x" + bytes(topic).hex() for topic in log.topics],
        "data": "0x" + bytes(log.data).hex(),
    } for log in logs]


def execute_create(state, target: str, initcode: bytes, value: int,
                   timestamp: int = 1_700_000_000, gas: int = DEFAULT_GAS_LIMIT):
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import get_account, set_account
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_message_call
    from ethereum_types.bytes import Bytes, Bytes0
    from ethereum_types.numeric import U256, Uint

    caller = Address(address_bytes(CREATE_CALLER))
    target_address = Address(address_bytes(target))
    set_account(state, caller, Account(Uint(0), U256(10**24), Bytes(b"")))
    block, tx = environments(state, timestamp, gas)
    message = Message(
        block_env=block, tx_env=tx, caller=caller, target=Bytes0(b""),
        current_target=target_address, gas=Uint(gas), value=U256(value),
        data=Bytes(b""), code_address=None, code=Bytes(initcode), depth=Uint(0),
        should_transfer_value=True, is_static=False,
        accessed_addresses={caller, target_address}, accessed_storage_keys=set(),
        disable_precompiles=False, parent_evm=None)
    output = process_message_call(message)
    return output, bytes(get_account(state, target_address).code), gas - int(output.gas_left)


def execute_tx(state, txspec: Tx):
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import get_account, set_account
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_message_call
    from ethereum.trace import OpEnd, OpStart, set_evm_trace
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import U256, Uint

    caller = Address(address_bytes(txspec.caller))
    target = Address(address_bytes(txspec.target))
    caller_account = get_account(state, caller)
    if int(caller_account.balance) < txspec.value:
        set_account(state, caller, Account(caller_account.nonce, U256(10**24), caller_account.code))
    block, txenv = environments(state, txspec.timestamp, txspec.gas)
    txenv.origin = caller
    code = get_account(state, target).code
    message = Message(
        block_env=block, tx_env=txenv, caller=caller, target=target,
        current_target=target, gas=Uint(txspec.gas), value=U256(txspec.value),
        data=Bytes(txspec.calldata), code_address=target, code=code, depth=Uint(0),
        should_transfer_value=True, is_static=False,
        accessed_addresses={caller, target}, accessed_storage_keys=set(),
        disable_precompiles=False, parent_evm=None)
    traces: List[Dict[str, object]] = []
    writes: List[Dict[str, object]] = []
    resource_ops: List[Dict[str, object]] = []
    pending: Dict[int, List[int]] = {}

    def memread(memory: bytearray, start: int, size: int) -> bytes:
        if size > 1_000_000:
            die(f"refusing traced input of {size} bytes")
        raw = bytes(memory[start:start + size])
        return raw + bytes(size - len(raw))

    def tracer(evm, event, /, **_kw) -> None:
        if isinstance(event, OpStart) and event.op.name == "SSTORE":
            if len(evm.stack) < 2:
                die("traced SSTORE stack underflow")
            writes.append({
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "key": hex(int(evm.stack[-1])), "value": hex(int(evm.stack[-2])),
            })
            return
        if isinstance(event, OpStart) and event.op.name in ("CALL", "STATICCALL"):
            opcode = event.op.name
            need = 7 if opcode == "CALL" else 6
            if len(evm.stack) < need:
                die(f"traced {opcode} stack underflow")
            target_word = int(evm.stack[-2])
            called = target_word.to_bytes(32, "big")[-20:]
            if opcode == "CALL":
                value = int(evm.stack[-3]); offset = int(evm.stack[-4]); size = int(evm.stack[-5])
                output_offset = int(evm.stack[-6]); output_size = int(evm.stack[-7])
            else:
                value = 0; offset = int(evm.stack[-3]); size = int(evm.stack[-4])
                output_offset = int(evm.stack[-5]); output_size = int(evm.stack[-6])
            resource_ops.append({
                "opcode": opcode,
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "outputOffset": output_offset,
                "outputSize": output_size,
            })
            traces.append({
                "opcode": opcode,
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "target": "0x" + called.hex(), "value": hex(value),
                "input": "0x" + memread(evm.memory, offset, size).hex(),
            })
            pending.setdefault(id(evm), []).append(len(traces) - 1)
        elif isinstance(event, OpStart) and event.op.name == "RETURNDATACOPY":
            if len(evm.stack) < 3:
                die("traced RETURNDATACOPY stack underflow")
            resource_ops.append({
                "opcode": "RETURNDATACOPY",
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "memoryOffset": int(evm.stack[-1]),
                "returndataOffset": int(evm.stack[-2]),
                "size": int(evm.stack[-3]),
            })
        elif isinstance(event, OpEnd):
            indices = pending.get(id(evm), [])
            if indices:
                record = traces[indices.pop()]
                record["success"] = hex(int(evm.stack[-1]))
                record["returndata"] = "0x" + bytes(evm.return_data).hex()

    previous = set_evm_trace(tracer)
    try:
        output = process_message_call(message)
    finally:
        set_evm_trace(previous)
    if any(pending.values()):
        die("call trace contains unmatched opcode start")
    return output, traces, txspec.gas - int(output.gas_left), writes, resource_ops


def install_code(state, mapping: Mapping[str, bytes]) -> None:
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import get_account, set_account
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import Uint

    for address, code in mapping.items():
        a = Address(address_bytes(address))
        old = get_account(state, a)
        set_account(state, a, Account(Uint(max(1, int(old.nonce))), old.balance, Bytes(code)))


def project_state(case: Case, state, side: str) -> Mapping:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account, get_storage
    from ethereum_types.bytes import Bytes32

    circuit = Address(address_bytes(CIRCUIT))
    targets = sorted(set(case.observe_targets), key=canonical_address)
    pausers = sorted(set(case.observe_pausers), key=canonical_address)

    def read(address: str, key: int) -> int:
        return int(get_storage(state, Address(address_bytes(address)), Bytes32(h256(key))))

    if side == "solidity":
        pause_slot, interval_slot, length_slot = 0, 1, 5
        expiry = lambda a: sol_map(a, 2)
        assignment = lambda a: sol_map(a, 3)
        index = lambda a: sol_map(a, 4)
        count = lambda a: sol_map(a, 6)
        entry = sol_array_entry
    else:
        pause_slot, interval_slot, length_slot = tagged(1), tagged(1, 1), tagged(6)
        expiry = lambda a: tagged(2, int.from_bytes(address_bytes(a), "big"))
        assignment = lambda a: tagged(3, int.from_bytes(address_bytes(a), "big"))
        index = lambda a: tagged(4, int.from_bytes(address_bytes(a), "big"))
        count = lambda a: tagged(5, int.from_bytes(address_bytes(a), "big"))
        entry = lambda i: tagged(6, i + 1)
    def contract_projection(owner: str) -> Mapping:
        length = read(owner, length_slot)
        if length > 256:
            die(f"projection refuses implausible registry length {length}")
        return {
            "pauseDuration": hex(read(owner, pause_slot)),
            "heartbeatInterval": hex(read(owner, interval_slot)),
            "assignments": {canonical_address(a): hex(read(owner, assignment(a))) for a in targets},
            "indices": {canonical_address(a): hex(read(owner, index(a))) for a in targets},
            "counts": {canonical_address(a): hex(read(owner, count(a))) for a in pausers},
            "expiries": {canonical_address(a): hex(read(owner, expiry(a))) for a in pausers},
            "array": [hex(read(owner, entry(i))) for i in range(length)],
        }

    logical = dict(contract_projection(CIRCUIT))
    if case.clone_history:
        logical["clone"] = contract_projection(CLONE)
    addresses = {CIRCUIT, CREATE_CALLER, *(tx.caller for tx in case.history), *(case.code.keys())}
    if case.action:
        addresses.add(case.action.caller)
    eth = {canonical_address(a): hex(int(get_account(state, Address(address_bytes(a))).balance))
           for a in sorted(addresses, key=canonical_address)}
    aux = {
        canonical_address(a): [hex(read(a, slot)) for slot in range(count_slots)]
        for a, count_slots in sorted(case.observe_aux_slots.items(), key=lambda row: canonical_address(row[0]))
    }
    return {"logicalState": logical, "eth": eth, "auxiliaryState": aux,
            "_rawSlotZero": hex(read(CIRCUIT, 0))}


CHANNEL_FIELDS = {
    "status": ("status",), "returndata": ("returndata",),
    "state-projection": ("logicalState", "auxiliaryState"), "eth": ("eth",),
    "logs": ("logs",), "call-trace": ("callTrace",),
}


def normalize_runtime(case: Case, state,
                      outputs: Sequence[Tuple[
                          object, Sequence[Mapping], int, Sequence[Mapping],
                          Sequence[Mapping]]],
                      side: str, resource_boundaries: Sequence[Mapping]) -> Mapping:
    rows = [{
        "status": outcome(output), "returndata": "0x" + bytes(output.return_data).hex(),
        "logs": normalized_logs(output.logs), "callTrace": list(trace), "gasUsed": gas_used,
        "writeTrace": list(writes),
        "resourceOps": list(resource_ops),
    } for output, trace, gas_used, writes, resource_ops in outputs]
    projected = project_state(case, state, side)
    return {
        "status": [row["status"] for row in rows],
        "returndata": [row["returndata"] for row in rows],
        "logs": [row["logs"] for row in rows],
        "callTrace": [row["callTrace"] for row in rows],
        "gasUsed": [row["gasUsed"] for row in rows],
        "writeTrace": [row["writeTrace"] for row in rows],
        "_resourceOps": [row["resourceOps"] for row in rows],
        "_resourceBoundaries": list(resource_boundaries),
        **projected,
    }


def resource_boundary(output, gas_limit: int, gas_used: int) -> Mapping:
    return {
        "status": outcome(output), "gasLimit": gas_limit, "gasUsed": gas_used,
    }


def compare(case: Case, solidity: Mapping, blanc: Mapping) -> List[str]:
    fields: List[str] = []
    for channel in case.channels:
        fields.extend(CHANNEL_FIELDS[channel])
    return [field for field in dict.fromkeys(fields) if solidity[field] != blanc[field]]


def side_artifacts(side: str, params: Mapping[str, object], lock: Mapping,
                   artifacts: Mapping) -> Tuple[bytes, bytes, bytes]:
    suffix = constructor_suffix(params)
    if side == "solidity":
        template = bytes.fromhex(lock["artifacts"]["creationTemplate"]["hex"].removeprefix("0x"))
        runtime = patch_solidity_runtime(lock, params)
    else:
        template = artifacts["creation-template"]
        runtime = patch_blanc_runtime(artifacts, params)
    return template, template + suffix, runtime


def run_side(case: Case, side: str, lock: Mapping, artifacts: Mapping) -> Mapping:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import State, get_account_optional

    params = case.constructor_params or (INDEPENDENT if case.world == "independent" else OFFICIAL)
    template, ordinary_create, expected_runtime = side_artifacts(side, params, lock, artifacts)
    suffix = case.constructor_suffix_override
    create_input = ordinary_create if suffix is None else template + suffix
    create_input += case.constructor_trailing
    state = State()
    created, installed, create_gas = execute_create(
        state, CIRCUIT, create_input, case.constructor_value)
    created_status = outcome(created)
    created_return = bytes(created.return_data)
    account_exists = get_account_optional(state, Address(address_bytes(CIRCUIT))) is not None

    if created_status == "success":
        if installed != expected_runtime or created_return != expected_runtime:
            die(f"{case.name}/{side}: constructor did not install/return its independently owned runtime")
        if len(installed) > 24_576 or len(create_input) > 49_152:
            die(f"{case.name}/{side}: EIP-170/EIP-3860 limit exceeded")
    elif account_exists:
        die(f"{case.name}/{side}: failed constructor left an account")

    if case.family == "constructor":
        projection = project_state(case, state, side)
        return {
            "status": [created_status],
            # Successful runtime bytes intentionally differ across toolchains;
            # each was checked above against its independent owner.
            "returndata": ["own-runtime" if created_status == "success" else "0x" + created_return.hex()],
            "logicalState": projection["logicalState"],
            "auxiliaryState": projection["auxiliaryState"],
            "_rawSlotZero": projection["_rawSlotZero"],
            "eth": projection["eth"], "logs": [normalized_logs(created.logs)],
            "callTrace": [[]], "gasUsed": [create_gas],
            "_resourceBoundaries": [
                resource_boundary(created, DEFAULT_GAS_LIMIT, create_gas)
            ],
            "runtimeIdentity": hashlib.sha256(installed).hexdigest() if installed else None,
            "createInputIdentity": hashlib.sha256(create_input).hexdigest(),
        }

    if created_status != "success":
        die(f"{case.name}/{side}: causal constructor seed failed: {created_status} {created_return.hex()}")
    resource_boundaries = [
        resource_boundary(created, DEFAULT_GAS_LIMIT, create_gas)
    ]
    install_code(state, case.code)
    if case.clone_history:
        clone_created, clone_installed, clone_gas = execute_create(
            state, CLONE, ordinary_create, 0)
        if outcome(clone_created) != "success" or clone_installed != expected_runtime:
            die(f"{case.name}/{side}: causal clone constructor seed failed")
        resource_boundaries.append(
            resource_boundary(clone_created, DEFAULT_GAS_LIMIT, clone_gas))
    outputs: List[Tuple[
        object, Sequence[Mapping], int, Sequence[Mapping], Sequence[Mapping]]] = []
    for transaction in [*case.clone_history, *case.history, case.action]:
        if transaction is None:
            continue
        result = execute_tx(state, transaction)
        outputs.append(result)
        resource_boundaries.append(
            resource_boundary(result[0], transaction.gas, result[2]))
    return normalize_runtime(case, state, outputs, side, resource_boundaries)


def build_constructor_cases() -> List[Case]:
    cases: List[Case] = [
        ctorcase("constructor-success-official", OFFICIAL, tags=("constructor-success", "official-world")),
        ctorcase("constructor-success-independent", INDEPENDENT, world="independent",
                 tags=("constructor-success", "independent-world")),
    ]
    lower = {**OFFICIAL, "initialPauseDuration": OFFICIAL["minPauseDuration"],
             "initialHeartbeatInterval": OFFICIAL["minHeartbeatInterval"]}
    upper = {**OFFICIAL, "initialPauseDuration": OFFICIAL["maxPauseDuration"],
             "initialHeartbeatInterval": OFFICIAL["maxHeartbeatInterval"]}
    equal = {**OFFICIAL, "minPauseDuration": 7, "maxPauseDuration": 7,
             "initialPauseDuration": 7, "minHeartbeatInterval": 11,
             "maxHeartbeatInterval": 11, "initialHeartbeatInterval": 11}
    cases += [
        ctorcase("constructor-success-exact-lower-bounds", lower, tags=("constructor-success", "lower-bound")),
        ctorcase("constructor-success-exact-upper-bounds", upper, tags=("constructor-success", "upper-bound")),
        ctorcase("constructor-success-equal-bounds", equal, tags=("constructor-success", "equal-bound")),
    ]
    invalid = [
        ("admin-zero", {**OFFICIAL, "admin": ZERO}, "AdminZero"),
        ("min-pause-zero", {**OFFICIAL, "minPauseDuration": 0}, "MinPauseDurationZero"),
        ("min-pause-above-max", {**OFFICIAL, "minPauseDuration": 10, "maxPauseDuration": 9,
                                  "initialPauseDuration": 10}, "MinPauseDurationExceedsMax"),
        ("min-heartbeat-zero", {**OFFICIAL, "minHeartbeatInterval": 0}, "MinHeartbeatIntervalZero"),
        ("min-heartbeat-above-max", {**OFFICIAL, "minHeartbeatInterval": 10,
                                      "maxHeartbeatInterval": 9,
                                      "initialHeartbeatInterval": 10}, "MinHeartbeatIntervalExceedsMax"),
        ("pause-below-min", {**OFFICIAL, "initialPauseDuration": OFFICIAL["minPauseDuration"] - 1},
         "PauseDurationBelowMin"),
        ("pause-above-max", {**OFFICIAL, "initialPauseDuration": OFFICIAL["maxPauseDuration"] + 1},
         "PauseDurationAboveMax"),
        ("heartbeat-below-min", {**OFFICIAL,
                                  "initialHeartbeatInterval": OFFICIAL["minHeartbeatInterval"] - 1},
         "HeartbeatIntervalBelowMin"),
        ("heartbeat-above-max", {**OFFICIAL,
                                  "initialHeartbeatInterval": OFFICIAL["maxHeartbeatInterval"] + 1},
         "HeartbeatIntervalAboveMax"),
    ]
    for name, params, error in invalid:
        cases.append(ctorcase("constructor-error-" + name, params,
                              tags=("constructor-error", error)))
    suffix = constructor_suffix(OFFICIAL)
    for amount in (0, 1, 31, 32, 33, 63, 64, 127, 191, 223):
        cases.append(ctorcase(f"constructor-short-tail-{amount}", OFFICIAL,
                              constructor_suffix_override=suffix[:amount],
                              tags=("constructor-malformed", "short-tail")))
    dirty = bytearray(suffix); dirty[0] = 1
    cases += [
        ctorcase("constructor-dirty-admin", OFFICIAL, constructor_suffix_override=bytes(dirty),
                 tags=("constructor-malformed", "dirty-admin")),
        ctorcase("constructor-trailing-arguments", OFFICIAL, constructor_trailing=b"\xaa" * 37,
                 tags=("constructor-trailing", "constructor-success")),
        ctorcase("constructor-nonzero-value", OFFICIAL, constructor_value=1,
                 tags=("constructor-nonpayability", "wrapper-precedence")),
        ctorcase("constructor-precedence-admin-zero-plus-min-pause-zero",
                 {**OFFICIAL, "admin": ZERO, "minPauseDuration": 0},
                 tags=("constructor-precedence", "AdminZero")),
        ctorcase("constructor-precedence-both-bound-inversions",
                 {**OFFICIAL, "minPauseDuration": 10, "maxPauseDuration": 9,
                  "minHeartbeatInterval": 10, "maxHeartbeatInterval": 9,
                  "initialPauseDuration": 10, "initialHeartbeatInterval": 10},
                 tags=("constructor-precedence", "MinPauseDurationExceedsMax")),
        ctorcase("constructor-precedence-both-invalid-initials",
                 {**OFFICIAL, "initialPauseDuration": OFFICIAL["minPauseDuration"] - 1,
                  "initialHeartbeatInterval": OFFICIAL["minHeartbeatInterval"] - 1},
                 tags=("constructor-precedence", "PauseDurationBelowMin")),
        ctorcase("constructor-precedence-value-plus-malformed", OFFICIAL,
                 constructor_suffix_override=suffix[:1], constructor_value=1,
                 tags=("constructor-precedence", "nonpayable-before-decode")),
    ]
    return cases


def reg(target: str, pauser: str, *, caller: str = ADMIN,
        timestamp: int = 1_700_000_000, trailing: bytes = b"") -> Tx:
    return Tx(caller, calldata("registerPauser(address,address)", target, pauser,
                               trailing=trailing), timestamp=timestamp)


def pause(target: str, *, caller: str = PAUSER_A, timestamp: int = 1_700_000_001,
          gas: int = 20_000_000, trailing: bytes = b"") -> Tx:
    return Tx(caller, calldata("pause(address)", target, trailing=trailing),
              timestamp=timestamp, gas=gas)


def runtime_surface_cases() -> List[Case]:
    cases: List[Case] = []
    views = [
        ("pauseDuration()", (), "view-pause-duration"),
        ("heartbeatInterval()", (), "view-heartbeat-interval"),
        ("ADMIN()", (), "view-admin"),
        ("MIN_PAUSE_DURATION()", (), "view-min-pause"),
        ("MAX_PAUSE_DURATION()", (), "view-max-pause"),
        ("MIN_HEARTBEAT_INTERVAL()", (), "view-min-heartbeat"),
        ("MAX_HEARTBEAT_INTERVAL()", (), "view-max-heartbeat"),
        ("getPauser(address)", (TARGET_1,), "view-get-pauser"),
        ("getPausableCount(address)", (PAUSER_A,), "view-get-count"),
        ("heartbeatExpiry(address)", (PAUSER_A,), "view-expiry"),
        ("isPauserLive(address)", (PAUSER_A,), "view-live"),
        ("getPausables()", (), "view-enumeration-empty"),
    ]
    for signature, words, name in views:
        cases.append(rtcase(name, "views", Tx(OTHER, calldata(signature, *words)),
                            observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
                            tags=("selector-surface", "view-getter")))
    # The five immutable getters are also paired in the independent world.
    for signature in ("ADMIN()", "MIN_PAUSE_DURATION()", "MAX_PAUSE_DURATION()",
                      "MIN_HEARTBEAT_INTERVAL()", "MAX_HEARTBEAT_INTERVAL()"):
        cases.append(rtcase("independent-" + signature.split("(")[0].lower(), "views",
                            Tx(OTHER, calldata(signature)), world="independent",
                            tags=("selector-surface", "independent-world", "view-getter")))

    for endpoint, signature, low, high, initial in [
        ("pause", "setPauseDuration(uint256)", OFFICIAL["minPauseDuration"],
         OFFICIAL["maxPauseDuration"], OFFICIAL["initialPauseDuration"]),
        ("heartbeat", "setHeartbeatInterval(uint256)", OFFICIAL["minHeartbeatInterval"],
         OFFICIAL["maxHeartbeatInterval"], OFFICIAL["initialHeartbeatInterval"]),
    ]:
        for label, caller, value in [
            ("authorized-equal", ADMIN, initial), ("authorized-lower", ADMIN, low),
            ("authorized-upper", ADMIN, high), ("below", ADMIN, low - 1),
            ("above", ADMIN, high + 1), ("unauthorized", OTHER, initial),
        ]:
            error_tag: Tuple[str, ...] = ()
            if label == "below":
                error_tag = (("PauseDurationBelowMin" if endpoint == "pause"
                              else "HeartbeatIntervalBelowMin"),)
            elif label == "above":
                error_tag = (("PauseDurationAboveMax" if endpoint == "pause"
                              else "HeartbeatIntervalAboveMax"),)
            elif label == "unauthorized":
                error_tag = ("SenderNotAdmin",)
            cases.append(rtcase(f"setter-{endpoint}-{label}", "setters",
                                Tx(caller, calldata(signature, value)),
                                tags=("selector-surface", "setter", label, *error_tag)))
    cases.append(rtcase("heartbeat-unregistered", "heartbeat",
                        Tx(PAUSER_A, calldata("heartbeat()")),
                        observe_pausers=[PAUSER_A],
                        tags=("selector-surface", "unregistered", "SenderNotPauser")))
    return cases


def registry_cases() -> List[Case]:
    cases = [
        rtcase("register-zero-target-before-write", "registry", reg(ZERO, PAUSER_A),
               observe_targets=[ZERO], observe_pausers=[PAUSER_A],
               tags=("zero-target", "no-registry-write", "PausableZero")),
        rtcase("register-absent-to-zero", "registry", reg(TARGET_1, ZERO),
               observe_targets=[TARGET_1], observe_pausers=[ZERO],
               tags=("zero-registration", "temporary-append-remove", "PauserSet")),
        rtcase("register-fresh", "registry", reg(TARGET_1, PAUSER_A),
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A], tags=("fresh-registration",)),
        rtcase("register-same-pauser", "registry", reg(TARGET_1, PAUSER_A),
               history=[reg(TARGET_1, PAUSER_A)], observe_targets=[TARGET_1],
               observe_pausers=[PAUSER_A], tags=("same-pauser", "decrement-increment")),
        rtcase("register-distinct-pauser", "registry", reg(TARGET_1, PAUSER_B),
               history=[reg(TARGET_1, PAUSER_A)], observe_targets=[TARGET_1],
               observe_pausers=[PAUSER_A, PAUSER_B], tags=("distinct-pauser",)),
        rtcase("remove-only", "registry", reg(TARGET_1, ZERO),
               history=[reg(TARGET_1, PAUSER_A)], observe_targets=[TARGET_1],
               observe_pausers=[PAUSER_A], tags=("remove-only", "last-assignment")),
        rtcase("remove-first", "registry", reg(TARGET_1, ZERO),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A), reg(TARGET_3, PAUSER_A)],
               observe_targets=[TARGET_1, TARGET_2, TARGET_3], observe_pausers=[PAUSER_A],
               tags=("remove-first", "swap-and-pop")),
        rtcase("remove-middle", "registry", reg(TARGET_2, ZERO),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A), reg(TARGET_3, PAUSER_A)],
               observe_targets=[TARGET_1, TARGET_2, TARGET_3], observe_pausers=[PAUSER_A],
               tags=("remove-middle", "swap-and-pop")),
        rtcase("remove-last", "registry", reg(TARGET_3, ZERO),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A), reg(TARGET_3, PAUSER_A)],
               observe_targets=[TARGET_1, TARGET_2, TARGET_3], observe_pausers=[PAUSER_A],
               tags=("remove-last", "self-swap")),
        rtcase("idempotent-unregister", "registry", reg(TARGET_1, ZERO),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_1, ZERO)],
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A, ZERO],
               tags=("idempotent-unregister", "temporary-append-remove")),
        rtcase("moved-element-followup-replace", "registry", reg(TARGET_3, PAUSER_B),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A),
                        reg(TARGET_3, PAUSER_A), reg(TARGET_2, ZERO)],
               observe_targets=[TARGET_1, TARGET_2, TARGET_3],
               observe_pausers=[PAUSER_A, PAUSER_B], tags=("moved-element-followup", "replace")),
        rtcase("moved-element-followup-remove", "registry", reg(TARGET_3, ZERO),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A),
                        reg(TARGET_3, PAUSER_A), reg(TARGET_2, ZERO)],
               observe_targets=[TARGET_1, TARGET_2, TARGET_3], observe_pausers=[PAUSER_A],
               tags=("moved-element-followup", "remove")),
    ]
    many_targets = [f"0x{value:040x}" for value in range(0x100, 0x140)]
    history = [reg(target, PAUSER_A) for target in many_targets]
    cases += [
        rtcase("enumeration-singleton", "enumeration", Tx(OTHER, calldata("getPausables()")),
               history=[reg(TARGET_1, PAUSER_A)], observe_targets=[TARGET_1],
               observe_pausers=[PAUSER_A], tags=("ordered-enumeration", "singleton")),
        rtcase("enumeration-64-targets", "enumeration", Tx(OTHER, calldata("getPausables()")),
               history=history, observe_targets=many_targets, observe_pausers=[PAUSER_A],
               tags=("ordered-enumeration", "64-elements", "one-pauser-many-targets")),
    ]
    return cases


def abi_boundary_cases() -> List[Case]:
    cases = [
        rtcase("runtime-empty-calldata", "dispatch", Tx(OTHER, b""), tags=("empty-selector",)),
        rtcase("runtime-unknown-selector", "dispatch", Tx(OTHER, bytes.fromhex("deadbeef")),
               tags=("unknown-selector",)),
    ]
    signatures = [
        ("getPauser(address)", [TARGET_1]), ("getPausableCount(address)", [PAUSER_A]),
        ("heartbeatExpiry(address)", [PAUSER_A]), ("isPauserLive(address)", [PAUSER_A]),
        ("pause(address)", [TARGET_1]),
        ("registerPauser(address,address)", [TARGET_1, PAUSER_A]),
        ("setPauseDuration(uint256)", [OFFICIAL["initialPauseDuration"]]),
        ("setHeartbeatInterval(uint256)", [OFFICIAL["initialHeartbeatInterval"]]),
    ]
    for signature, words in signatures:
        full = calldata(signature, *words)
        for cut in (4, len(full) - 1):
            cases.append(rtcase(f"short-head-{signature.split('(')[0]}-{cut}", "abi-boundary",
                                Tx(ADMIN, full[:cut]), tags=("short-head", signature)))
        cases.append(rtcase("trailing-calldata-" + signature.split("(")[0], "abi-boundary",
                            Tx(ADMIN, full + b"\xaa" * 13), tags=("trailing-calldata", signature)))
    address_positions = [
        ("getPauser", "getPauser(address)", [TARGET_1], 0),
        ("getCount", "getPausableCount(address)", [PAUSER_A], 0),
        ("expiry", "heartbeatExpiry(address)", [PAUSER_A], 0),
        ("live", "isPauserLive(address)", [PAUSER_A], 0),
        ("pause", "pause(address)", [TARGET_1], 0),
        ("register-target", "registerPauser(address,address)", [TARGET_1, PAUSER_A], 0),
        ("register-pauser", "registerPauser(address,address)", [TARGET_1, PAUSER_A], 1),
    ]
    for label, signature, words, position in address_positions:
        encoded = bytearray(calldata(signature, *words))
        encoded[4 + 32 * position] = 1
        cases.append(rtcase("dirty-address-" + label, "abi-boundary", Tx(OTHER, bytes(encoded)),
                            tags=("dirty-address", f"arg-{position}")))
    # Every runtime selector is nonpayable, not merely a representative.
    lock = json.loads(LOCK_PATH.read_text())
    for row in lock["abi"]["functions"]:
        signature = row["signature"]
        argc = len(row["entry"]["inputs"])
        words = [0] * argc
        cases.append(rtcase("nonpayable-" + signature.split("(")[0], "nonpayability",
                            Tx(OTHER, calldata(signature, *words), value=1),
                            tags=("runtime-nonpayability", signature)))
    cases += [
        rtcase("precedence-unauthorized-register-zero", "precedence", reg(ZERO, PAUSER_A, caller=OTHER),
               observe_targets=[ZERO], observe_pausers=[PAUSER_A],
               tags=("unauthorized-plus-zero", "SenderNotAdmin", "admin-before-kernel")),
        rtcase("precedence-unauthorized-register-dirty", "precedence",
               Tx(OTHER, selector("registerPauser(address,address)") +
                  ((1 << 200) | int.from_bytes(address_bytes(TARGET_1), "big")).to_bytes(32, "big") +
                  address_word(PAUSER_A)), tags=("unauthorized-plus-dirty", "decoder-before-admin")),
    ]
    return cases


def temporal_cases() -> List[Case]:
    base = 1_700_000_000
    expiry = base + OFFICIAL["initialHeartbeatInterval"]
    cases = []
    for delta, label in [(-1, "minus-one"), (0, "equal"), (1, "plus-one")]:
        timestamp = expiry + delta
        cases += [
            rtcase("liveness-expiry-" + label, "time", Tx(OTHER,
                   calldata("isPauserLive(address)", PAUSER_A), timestamp=timestamp),
                   history=[reg(TARGET_1, PAUSER_A, timestamp=base)],
                   observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
                   tags=("strict-expiry", label)),
            rtcase("heartbeat-expiry-" + label, "time", Tx(PAUSER_A,
                   calldata("heartbeat()"), timestamp=timestamp),
                   history=[reg(TARGET_1, PAUSER_A, timestamp=base)],
                   observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
                   tags=("strict-expiry", "heartbeat", label,
                         *(("HeartbeatExpired",) if delta >= 0 else ()))),
        ]
    cases += [
        rtcase("heartbeat-unregistered-versus-expired", "precedence",
               Tx(PAUSER_A, calldata("heartbeat()"), timestamp=UINT256_MAX),
               observe_pausers=[PAUSER_A], tags=("unregistered-versus-expired", "SenderNotPauser")),
        rtcase("pause-unauthorized-versus-expired", "precedence",
               pause(TARGET_1, caller=OTHER, timestamp=expiry),
               history=[reg(TARGET_1, PAUSER_A, timestamp=base)], code={TARGET_1: target_code()},
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               tags=("unauthorized-versus-expired", "SenderNotPauser")),
        rtcase("interval-change-does-not-retroactively-change-expiry", "time",
               Tx(OTHER, calldata("heartbeatExpiry(address)", PAUSER_A), timestamp=base + 2),
               history=[reg(TARGET_1, PAUSER_A, timestamp=base),
                        Tx(ADMIN, calldata("setHeartbeatInterval(uint256)",
                                           OFFICIAL["minHeartbeatInterval"]), timestamp=base + 1)],
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               tags=("interval-change", "existing-expiry-stable")),
    ]
    # Checked addition in register and heartbeat.  The registration setup for
    # heartbeat lands exactly on max, remains live one tick later, then its
    # next expiry addition overflows.
    near = UINT256_MAX - OFFICIAL["initialHeartbeatInterval"]
    cases += [
        rtcase("overflow-register-expiry", "overflow", reg(TARGET_1, PAUSER_A,
               timestamp=near + 1), observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               tags=("checked-overflow", "register", "Panic-0x11")),
        rtcase("overflow-heartbeat-expiry", "overflow",
               Tx(PAUSER_A, calldata("heartbeat()"), timestamp=near + 1),
               history=[reg(TARGET_1, PAUSER_A, timestamp=near)],
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               tags=("checked-overflow", "heartbeat", "Panic-0x11")),
    ]
    return cases


def pause_result_cases(include_candidate_resource_cases: bool = False) -> List[Case]:
    cases: List[Case] = []
    variants = [
        ("eoa", b"", ("eoa", "extcodesize")),
        ("pause-target-revert", target_code(pause_revert=b"\xde\xad\xbe\xef"),
         ("target-revert", "bubble")),
        ("query-revert", target_code(query_payload=b"\xca\xfe", query_revert=True),
         ("query-revert", "bubble")),
        ("return-empty", target_code(b""), ("short-return", "size-0")),
        ("return-one-byte", target_code(b"\x01"), ("short-return", "size-1")),
        ("return-31-bytes", target_code(bytes(31)), ("short-return", "size-31")),
        ("return-false", target_code(h256(0)), ("false", "PauseFailed")),
        ("return-noncanonical", target_code(h256(2)), ("noncanonical-bool", "empty-revert")),
        ("return-true", target_code(h256(1)), ("true", "target-truth-not-guaranteed")),
        ("return-true-trailing-1", target_code(h256(1) + b"\xaa"),
         ("trailing-return", "size-33")),
    ]
    for name, code, tags in variants:
        mapping = {} if not code else {TARGET_1: code}
        cases.append(rtcase("pause-" + name, "pause-results", pause(TARGET_1),
                            history=[reg(TARGET_1, PAUSER_A)], code=mapping,
                            observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
                            tags=("pause-outcome", "full-rollback", *tags)))
    successful_sizes = [64, 256, 1024, 4096, 16384, 32768]
    if include_candidate_resource_cases:
        successful_sizes.append(65536)
    for size in successful_sizes:
        payload = h256(1) + bytes((i * 17 + 3) & 0xff for i in range(size - 32))
        cases.append(rtcase(f"pause-return-true-large-{size}", "return-data-resource",
                            pause(TARGET_1), history=[reg(TARGET_1, PAUSER_A)],
                            code={TARGET_1: target_code(payload)}, observe_targets=[TARGET_1],
                            observe_pausers=[PAUSER_A],
                            tags=("large-return", f"return-size-{size}", "adequate-gas")))
    if include_candidate_resource_cases:
        large_revert = bytes((i * 29 + 7) & 0xff for i in range(256))
        cases.append(rtcase(
            "pause-pause-target-revert-large-256", "return-data-resource",
            pause(TARGET_1), history=[reg(TARGET_1, PAUSER_A)],
            code={TARGET_1: target_code(pause_revert=large_revert)},
            observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
            tags=("target-revert", "bubble", "return-size-256")))
        cases.append(rtcase(
            "pause-query-revert-large-256", "return-data-resource",
            pause(TARGET_1), history=[reg(TARGET_1, PAUSER_A)],
            code={TARGET_1: target_code(
                query_payload=large_revert, query_revert=True)},
            observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
            tags=("query-revert", "bubble", "return-size-256")))
    # Explicit low-gas controls are calibrated far below any successful pause;
    # both sides must exhaust exceptional execution while the high-gas rows
    # above provide source-compatible return-data resource evidence.
    for size in (4096, 32768):
        payload = h256(1) + bytes(size - 32)
        cases.append(rtcase(f"pause-return-large-{size}-oog-control", "return-data-resource",
                            pause(TARGET_1, gas=25_000), history=[reg(TARGET_1, PAUSER_A)],
                            code={TARGET_1: target_code(payload)}, observe_targets=[TARGET_1],
                            observe_pausers=[PAUSER_A],
                            tags=("large-return", f"return-size-{size}", "oog-control")))
    return cases


def callback_and_history_cases() -> List[Case]:
    same_nested = calldata("pause(address)", TARGET_1)
    diff_nested = calldata("pause(address)", TARGET_2)
    same_catch = target_code(pause_body=nested_call_body(CIRCUIT, same_nested, bubble=False))
    same_bubble = target_code(pause_body=nested_call_body(CIRCUIT, same_nested, bubble=True))
    diff_catch = target_code(pause_body=nested_call_body(CIRCUIT, diff_nested, bubble=False))
    diff_bubble = target_code(pause_body=nested_call_body(CIRCUIT, diff_nested, bubble=True))
    clone_nested = target_code(pause_body=nested_call_body(CLONE, diff_nested, bubble=False))

    cases = [
        rtcase("reentry-same-target-caught", "reentry", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A)], code={TARGET_1: same_catch},
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               observe_aux_slots={TARGET_1: 3}, tags=("same-target-reentry", "caught-child")),
        rtcase("reentry-same-target-bubbled", "reentry", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A)], code={TARGET_1: same_bubble},
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               tags=("same-target-reentry", "bubbled-child", "outer-rollback", "ReentrantCall")),
        rtcase("reentry-different-target-caught", "reentry", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A)],
               code={TARGET_1: diff_catch, TARGET_2: target_code()},
               observe_targets=[TARGET_1, TARGET_2], observe_pausers=[PAUSER_A],
               observe_aux_slots={TARGET_1: 3}, tags=("different-target-reentry", "caught-child")),
        rtcase("reentry-different-target-bubbled", "reentry", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A)],
               code={TARGET_1: diff_bubble, TARGET_2: target_code()},
               observe_targets=[TARGET_1, TARGET_2], observe_pausers=[PAUSER_A],
               tags=("different-target-reentry", "bubbled-child", "outer-rollback", "ReentrantCall")),
        rtcase("reentry-clone-namespace", "reentry", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A)],
               clone_history=[Tx(ADMIN, calldata("registerPauser(address,address)", TARGET_2,
                                                TARGET_1), target=CLONE)],
               code={TARGET_1: clone_nested, TARGET_2: target_code()},
               observe_targets=[TARGET_1, TARGET_2], observe_pausers=[PAUSER_A, TARGET_1],
               observe_aux_slots={TARGET_1: 3}, tags=("clone-namespace", "distinct-lock-owner")),
    ]

    heartbeat_callback = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("heartbeat()"), bubble=False))
    mid_liveness = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("isPauserLive(address)", PAUSER_A), bubble=False))
    set_duration = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("setPauseDuration(uint256)", OFFICIAL["minPauseDuration"]),
        bubble=False))
    set_interval = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("setHeartbeatInterval(uint256)", OFFICIAL["minHeartbeatInterval"]),
        bubble=False))
    register_other = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("registerPauser(address,address)", ADMIN, PAUSER_B), bubble=False))
    register_same = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("registerPauser(address,address)", ADMIN, PAUSER_A), bubble=False))
    cases += [
        rtcase("callback-heartbeat", "callback-interference", pause(PAUSER_A),
               history=[reg(PAUSER_A, PAUSER_A), reg(TARGET_2, PAUSER_A)],
               code={PAUSER_A: heartbeat_callback}, observe_targets=[PAUSER_A, TARGET_2],
               observe_pausers=[PAUSER_A], observe_aux_slots={PAUSER_A: 3},
               tags=("heartbeat-callback", "post-unregister-count")),
        rtcase("callback-midcall-liveness", "callback-interference", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A)], code={TARGET_1: mid_liveness},
               observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               observe_aux_slots={TARGET_1: 3}, tags=("mid-call-liveness", "old-expiry-visible")),
        rtcase("callback-admin-set-duration-snapshot", "callback-interference", pause(ADMIN),
               history=[reg(ADMIN, PAUSER_A)], code={ADMIN: set_duration},
               observe_targets=[ADMIN], observe_pausers=[PAUSER_A],
               observe_aux_slots={ADMIN: 3}, tags=("config-callback", "duration-snapshot")),
        rtcase("callback-admin-set-interval-post-expiry", "callback-interference", pause(ADMIN),
               history=[reg(ADMIN, PAUSER_A), reg(TARGET_2, PAUSER_A)], code={ADMIN: set_interval},
               observe_targets=[ADMIN, TARGET_2], observe_pausers=[PAUSER_A],
               observe_aux_slots={ADMIN: 3}, tags=("config-callback", "post-callback-interval")),
        rtcase("callback-admin-reassign-distinct", "callback-interference", pause(ADMIN),
               history=[reg(ADMIN, PAUSER_A)], code={ADMIN: register_other},
               observe_targets=[ADMIN], observe_pausers=[PAUSER_A, PAUSER_B],
               observe_aux_slots={ADMIN: 3}, tags=("register-callback", "authorized-admin-reassignment")),
        rtcase("callback-admin-reassign-same-post-count", "callback-interference", pause(ADMIN),
               history=[reg(ADMIN, PAUSER_A)], code={ADMIN: register_same},
               observe_targets=[ADMIN], observe_pausers=[PAUSER_A],
               observe_aux_slots={ADMIN: 3}, tags=("register-callback", "post-callback-count")),
    ]

    cases += [
        rtcase("next-transaction-after-success", "transaction-reset", pause(TARGET_2),
               history=[reg(TARGET_1, PAUSER_A), reg(TARGET_2, PAUSER_A), pause(TARGET_1)],
               code={TARGET_1: target_code(), TARGET_2: target_code()},
               observe_targets=[TARGET_1, TARGET_2], observe_pausers=[PAUSER_A],
               tags=("sequential-transactions", "after-success", "transient-reset")),
        rtcase("next-transaction-after-failure", "transaction-reset", pause(TARGET_1),
               history=[reg(TARGET_1, PAUSER_A), pause(TARGET_1)],
               code={TARGET_1: target_code(h256(0))}, observe_targets=[TARGET_1],
               observe_pausers=[PAUSER_A],
               tags=("sequential-transactions", "after-failure", "transient-reset")),
    ]
    return cases


def overflow_pause_cases() -> List[Case]:
    # One remaining assignment takes the checked-add branch after callback.
    near = UINT256_MAX - OFFICIAL["initialHeartbeatInterval"]
    normal = target_code()
    callback_setup = UINT256_MAX - OFFICIAL["initialHeartbeatInterval"] - 1
    callback_action = UINT256_MAX - 2
    set_max_interval = target_code(pause_body=nested_call_body(
        CIRCUIT, calldata("setHeartbeatInterval(uint256)",
                          OFFICIAL["maxHeartbeatInterval"]), bubble=False))
    return [
        rtcase("overflow-pause-post-callback-count-positive", "overflow", pause(
               TARGET_1, timestamp=near + 1),
               history=[reg(TARGET_1, PAUSER_A, timestamp=near),
                        reg(TARGET_2, PAUSER_A, timestamp=near)],
               code={TARGET_1: normal}, observe_targets=[TARGET_1, TARGET_2],
               observe_pausers=[PAUSER_A],
               tags=("checked-overflow", "pause", "remaining-assignment", "Panic-0x11")),
        rtcase("pause-last-assignment-zero-expiry-no-add", "overflow", pause(
               TARGET_1, timestamp=near + 1),
               history=[reg(TARGET_1, PAUSER_A, timestamp=near)],
               code={TARGET_1: normal}, observe_targets=[TARGET_1], observe_pausers=[PAUSER_A],
               tags=("pause", "last-assignment", "zero-expiry-branch")),
        rtcase("overflow-pause-post-callback-interval-change", "overflow", pause(
               ADMIN, timestamp=callback_action),
               history=[reg(ADMIN, PAUSER_A, timestamp=callback_setup),
                        reg(TARGET_2, PAUSER_A, timestamp=callback_setup)],
               code={ADMIN: set_max_interval}, observe_targets=[ADMIN, TARGET_2],
               observe_pausers=[PAUSER_A], observe_aux_slots={ADMIN: 3},
               tags=("checked-overflow", "pause", "post-callback-interval",
                     "remaining-assignment", "config-callback", "Panic-0x11")),
    ]


def build_cases(include_candidate_resource_cases: bool = False) -> List[Case]:
    cases = (build_constructor_cases() + runtime_surface_cases() + registry_cases() +
             abi_boundary_cases() + temporal_cases() + pause_result_cases(
                 include_candidate_resource_cases) +
             callback_and_history_cases() + overflow_pause_cases())
    names = [case.name for case in cases]
    if len(names) != len(set(names)):
        die("duplicate differential case name")
    return cases


REQUIRED_TAGS = [
    "constructor-success", "official-world", "independent-world", "lower-bound",
    "upper-bound", "equal-bound", "constructor-error", "constructor-malformed",
    "short-tail", "dirty-admin", "constructor-trailing", "constructor-nonpayability",
    "constructor-precedence", "nonpayable-before-decode", "view-getter", "setter",
    "zero-target", "no-registry-write", "zero-registration", "fresh-registration",
    "same-pauser", "distinct-pauser", "remove-first", "remove-middle", "remove-last",
    "remove-only", "idempotent-unregister", "moved-element-followup",
    "one-pauser-many-targets", "ordered-enumeration", "64-elements", "dirty-address",
    "unauthorized-plus-zero", "unauthorized-plus-dirty", "strict-expiry",
    "unregistered-versus-expired", "unauthorized-versus-expired", "interval-change",
    "checked-overflow", "runtime-nonpayability", "unknown-selector", "empty-selector",
    "short-head", "trailing-calldata", "eoa", "target-revert", "query-revert",
    "false", "short-return", "noncanonical-bool", "true", "trailing-return",
    "large-return", "adequate-gas", "oog-control", "remaining-assignment",
    "last-assignment", "duration-snapshot", "post-callback-interval",
    "post-callback-count", "mid-call-liveness", "same-target-reentry",
    "different-target-reentry", "caught-child", "bubbled-child", "clone-namespace",
    "heartbeat-callback", "config-callback", "register-callback",
    "authorized-admin-reassignment", "target-truth-not-guaranteed", "full-rollback",
    "outer-rollback", "sequential-transactions", "after-success", "after-failure",
    "transient-reset",
]


def case_endpoint(case: Case, selector_to_signature: Mapping[str, str]) -> str:
    if case.family == "constructor":
        return "constructor"
    if case.action is None or len(case.action.calldata) < 4:
        return "empty-calldata"
    return selector_to_signature.get(case.action.calldata[:4].hex(), "unknown-selector")


def byte_descriptor(payload: bytes) -> Mapping:
    """Freeze exact bytes; SHA-256 is derived here from evaluator/case bytes."""
    return {
        "byteLength": len(payload), "hex": "0x" + payload.hex(),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def code_descriptor(payload: bytes) -> Mapping:
    return {
        "byteLength": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def params_descriptor(params: Mapping[str, object]) -> Mapping:
    return {
        key: canonical_address(str(value)) if key == "admin" else int(value)
        for key, value in params.items()
    }


def tx_descriptor(tx: Tx, boundary: int, phase: str, order: int) -> Mapping:
    return {
        "boundary": boundary, "phase": phase, "orderWithinPhase": order,
        "caller": canonical_address(tx.caller), "target": canonical_address(tx.target),
        "value": tx.value, "timestamp": tx.timestamp, "gas": tx.gas,
        "calldata": byte_descriptor(tx.calldata),
    }


def case_execution_descriptor(case: Case) -> Mapping:
    params = case.constructor_params or (
        INDEPENDENT if case.world == "independent" else OFFICIAL)
    ordinary_suffix = constructor_suffix(params)
    suffix = case.constructor_suffix_override
    actual_suffix = ordinary_suffix if suffix is None else suffix
    dirty_admin = len(actual_suffix) >= 32 and any(actual_suffix[:12])
    malformed_kind = "none"
    if len(actual_suffix) < 224:
        malformed_kind = "short-tail"
    elif dirty_admin:
        malformed_kind = "dirty-admin"
    elif len(actual_suffix) != 224:
        malformed_kind = "noncanonical-length"

    boundary = 0
    boundary_order = [f"primaryConstructor@{canonical_address(CIRCUIT)}"]
    boundary += 1
    if case.clone_history:
        boundary_order.append(f"cloneConstructor@{canonical_address(CLONE)}")
        boundary += 1
    clone_rows = []
    for order, tx in enumerate(case.clone_history):
        clone_rows.append(tx_descriptor(tx, boundary, "cloneHistory", order))
        boundary_order.append(f"cloneHistory[{order}]")
        boundary += 1
    history_rows = []
    for order, tx in enumerate(case.history):
        history_rows.append(tx_descriptor(tx, boundary, "history", order))
        boundary_order.append(f"history[{order}]")
        boundary += 1
    action = None
    if case.action is not None:
        action = tx_descriptor(case.action, boundary, "action", 0)
        boundary_order.append("action")

    return {
        "constructor": {
            "boundary": 0, "target": canonical_address(CIRCUIT),
            "caller": canonical_address(CREATE_CALLER), "value": case.constructor_value,
            "timestamp": 1_700_000_000, "gas": DEFAULT_GAS_LIMIT,
            "parameters": params_descriptor(params),
            "argumentSuffixSource": "derived" if suffix is None else "override",
            "argumentSuffix": byte_descriptor(actual_suffix),
            "ordinaryArgumentSuffix": byte_descriptor(ordinary_suffix),
            "trailing": byte_descriptor(case.constructor_trailing),
            "malformed": {
                "kind": malformed_kind, "expectedArgumentBytes": 224,
                "actualArgumentBytes": len(actual_suffix),
                "missingArgumentBytes": max(0, 224 - len(actual_suffix)),
                "dirtyAdminHighBits": dirty_admin,
            },
        },
        "cloneConstructor": None if not case.clone_history else {
            "boundary": 1, "target": canonical_address(CLONE),
            "caller": canonical_address(CREATE_CALLER), "value": 0,
            "timestamp": 1_700_000_000, "gas": DEFAULT_GAS_LIMIT,
            "parameters": params_descriptor(params),
            "argumentSuffix": byte_descriptor(ordinary_suffix),
        },
        "cloneHistory": clone_rows, "history": history_rows, "action": action,
        "boundaryOrder": boundary_order,
        "targetCode": {
            canonical_address(address): code_descriptor(code)
            for address, code in sorted(
                case.code.items(), key=lambda row: canonical_address(row[0]))
        },
        "observeTargets": [canonical_address(value) for value in case.observe_targets],
        "observePausers": [canonical_address(value) for value in case.observe_pausers],
        "observeAuxSlots": {
            canonical_address(address): count for address, count in sorted(
                case.observe_aux_slots.items(), key=lambda row: canonical_address(row[0]))
        },
    }


def validate_identities(lock: Mapping, artifacts: Mapping) -> Tuple[int, int]:
    positive_checks = 0
    functions = lock["abi"]["functions"]
    reference_selectors = sorted(row["selector"].removeprefix("0x").lower() for row in functions)
    if artifacts["selectors"] != reference_selectors or len(reference_selectors) != 17:
        die("Lean dispatcher and reference ABI selectors are not the same exact 17")
    positive_checks += 1
    if not artifacts["patch-controls-valid"] or not artifacts["offset-metadata-valid"]:
        die("Lean immutable patch control evaluator reports false")
    positive_checks += 1
    runtime_limit, init_limit, arg_bytes = artifacts["limits"]
    if (runtime_limit, init_limit, arg_bytes) != (24_576, 49_152, 224):
        die("Lean evaluator size limits or constructor boundary drifted")
    expected_sizes = {
        "runtimeTemplateBytes": len(artifacts["official-runtime"]),
        "officialRuntimeBytes": len(artifacts["official-runtime"]),
        "independentRuntimeBytes": len(artifacts["independent-runtime"]),
        "officialRuntimeHeadroom": runtime_limit - len(artifacts["official-runtime"]),
        "independentRuntimeHeadroom": runtime_limit - len(artifacts["independent-runtime"]),
        "creationTemplateInitcodeHeadroom": init_limit - len(artifacts["creation-template"]),
        "officialFullCreateHeadroom": init_limit - len(artifacts["official-create"]),
        "independentFullCreateHeadroom": init_limit - len(artifacts["independent-create"]),
    }
    if artifacts["sizes"] != expected_sizes:
        die("Lean evaluator artifact size/headroom metadata does not match emitted bytes")
    positive_checks += 1
    worlds = {world["name"]: world for world in lock["artifacts"]["worlds"]}
    for label, params, lean_label, lock_label in [
        ("official", OFFICIAL, "official", "official-mainnet"),
        ("independent", INDEPENDENT, "independent", "independent-parameters"),
    ]:
        world = worlds[lock_label]
        template, sol_create, sol_runtime = side_artifacts("solidity", params, lock, artifacts)
        if sol_create != bytes.fromhex(world["fullCreateInput"]["hex"].removeprefix("0x")):
            die(f"{label} Solidity full CREATE derivation differs from lock")
        if sol_runtime != bytes.fromhex(world["returnedRuntime"]["hex"].removeprefix("0x")):
            die(f"{label} Solidity returned runtime derivation differs from lock")
        _, blanc_create, blanc_runtime = side_artifacts("blanc", params, lock, artifacts)
        if blanc_create != artifacts[f"{lean_label}-create"] or blanc_runtime != artifacts[f"{lean_label}-runtime"]:
            die(f"{label} Python Blanc parameter derivation differs from Lean evaluator")
        if len(sol_runtime) > runtime_limit or len(blanc_runtime) > runtime_limit:
            die(f"{label} returned runtime violates EIP-170")
        if len(sol_create) > init_limit or len(blanc_create) > init_limit:
            die(f"{label} full CREATE input violates EIP-3860")
        positive_checks += 6
    # Live runtime identity falsifier: one-bit corruption must fail the same
    # digest predicate used above.
    broken = bytearray(artifacts["official-runtime"]); broken[0] ^= 1
    if bytes(broken) == artifacts["official-runtime"] or \
            hashlib.sha256(broken).digest() == hashlib.sha256(artifacts["official-runtime"]).digest():
        die("runtime identity falsifier was not detected")
    if positive_checks != 15:
        die(f"artifact positive-check accounting drifted: {positive_checks}")
    return positive_checks, 1


def build_manifest(cases: Sequence[Case], lock: Mapping, artifacts: Mapping,
                   resource_metrics: Mapping) -> Mapping:
    selectors = {row["selector"].removeprefix("0x").lower(): row["signature"]
                 for row in lock["abi"]["functions"]}
    tag_counts: Dict[str, int] = {}
    endpoint_counts: Dict[str, int] = {}
    family_counts: Dict[str, int] = {}
    channel_counts: Dict[str, int] = {}
    rows = []
    for case in cases:
        endpoint = case_endpoint(case, selectors)
        endpoint_counts[endpoint] = endpoint_counts.get(endpoint, 0) + 1
        family_counts[case.family] = family_counts.get(case.family, 0) + 1
        for tag in case.tags:
            tag_counts[tag] = tag_counts.get(tag, 0) + 1
        for channel in case.channels:
            channel_counts[channel] = channel_counts.get(channel, 0) + 1
        execution = case_execution_descriptor(case)
        rows.append({
            "name": case.name, "family": case.family, "owner": case.owner,
            "world": case.world, "endpoint": endpoint,
            "historyLength": len(case.clone_history) + len(case.history),
            "execution": execution,
            "channels": list(case.channels), "tags": list(case.tags),
        })
    missing_endpoints = [row["signature"] for row in lock["abi"]["functions"]
                         if endpoint_counts.get(row["signature"], 0) == 0]
    if missing_endpoints:
        die(f"manifest has no action row for endpoint(s): {missing_endpoints}")
    missing_tags = [tag for tag in REQUIRED_TAGS if tag_counts.get(tag, 0) == 0]
    if missing_tags:
        die(f"manifest required AC9 tags missing: {missing_tags}")
    return {
        "schema": 2,
        "oracle": {
            "sourceCommit": lock["target"]["releaseCommit"],
            "officialRuntimeSha256": lock["artifacts"]["worlds"][0]["returnedRuntime"]["sha256"],
            "independentRuntimeSha256": lock["artifacts"]["worlds"][1]["returnedRuntime"]["sha256"],
            "ordinaryInput": "scripts/lido-circuit-breaker-reference.json",
        },
        "blanc": {
            "evaluator": "scripts/eval-lido-circuit-breaker-artifacts.lean",
            "digestDerivation": "Python SHA-256 over exact bytes emitted by the Lean evaluator",
            "creationTemplate": {"byteLength": len(artifacts["creation-template"]),
                                 "sha256": hashlib.sha256(artifacts["creation-template"]).hexdigest()},
            "official": {"fullCreateByteLength": len(artifacts["official-create"]),
                         "fullCreateSha256": hashlib.sha256(artifacts["official-create"]).hexdigest(),
                         "runtimeByteLength": len(artifacts["official-runtime"]),
                         "runtimeSha256": hashlib.sha256(artifacts["official-runtime"]).hexdigest()},
            "independent": {"fullCreateByteLength": len(artifacts["independent-create"]),
                            "fullCreateSha256": hashlib.sha256(artifacts["independent-create"]).hexdigest(),
                            "runtimeByteLength": len(artifacts["independent-runtime"]),
                            "runtimeSha256": hashlib.sha256(artifacts["independent-runtime"]).hexdigest()},
            "immutableOffsets": artifacts["offsets"],
            "patchControlsValid": artifacts["patch-controls-valid"],
            "sizesAndHeadroom": artifacts["sizes"],
            "sourceInventories": artifacts["source-inventories"],
            "runtimeSyntaxSiteCounts": artifacts["runtime-site-counts"],
            "constructorInventoryCounts": artifacts["constructor-site-counts"],
        },
        "projection": {
            "leanOwnedBlancProjection": artifacts["projection"],
            "solidityProjection": {
                "configurationSlots": {"pauseDuration": 0, "heartbeatInterval": 1},
                "heartbeatExpiry": "keccak256(address-word || uint256(2))",
                "assignment": "keccak256(address-word || uint256(3))",
                "oneBasedIndex": "keccak256(address-word || uint256(4))",
                "arrayLengthSlot": 5,
                "arrayEntry": "keccak256(uint256(5)) + zero-based-index mod 2^256",
                "assignmentCount": "keccak256(address-word || uint256(6))",
            },
            "comparisonDomain": {
                "registryLengthMaximumRead": 256,
                "rawSlotEqualityExcluded": True,
                "orderedArray": True,
                "observedAddressesAreManifestDeclared": True,
            },
        },
        "execution": {
            "eelsCommit": EELS_PIN, "fork": "Prague", "network": False,
            "solidityCodegenTarget": "Prague",
            "bpo2ExecutionClaim": False,
            "reportModelFork": lock["formalReport"]["modelFork"],
            "constructorCausalRuntimeHistories": True,
            "projectionExcludesRawSlotEquality": True,
        },
        "coverage": {
            "requiredTags": REQUIRED_TAGS, "tagCounts": tag_counts,
            "endpointCounts": endpoint_counts, "familyCounts": family_counts,
            "channelCounts": channel_counts,
        },
        "counts": {"rows": len(cases), "runtimeSelectors": 17,
                   "constructorArguments": 7, "customErrors": 15, "events": 6},
        "resourceEvidence": resource_metrics,
        "rows": rows,
        "explicitLimits": [
            "finite differential evidence, not universal correctness",
            "no raw storage or storage-root equality claim",
            "no BPO2 execution claim; EELS execution and Solidity code generation are Prague",
            "no target-truth guarantee from a successful isPaused() observation",
            "exact gas equality and identical OOG thresholds are excluded",
        ],
    }


def require_manifest(expected: Mapping, write: bool) -> None:
    validate_manifest_schema(expected)
    rendered = json.dumps(expected, indent=2, sort_keys=True) + "\n"
    if write:
        MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST_PATH.write_text(rendered)
        return
    if not MANIFEST_PATH.is_file():
        die("committed Lido differential manifest is missing")
    committed_text = MANIFEST_PATH.read_text()
    validate_manifest_schema(json.loads(committed_text))
    if committed_text != rendered:
        die("committed Lido differential manifest is stale; regenerate deliberately with --write-manifest")
    # Live case-manifest falsifier through the same schema/count validator.
    broken = json.loads(rendered); broken["rows"] = broken["rows"][1:]
    try:
        validate_manifest_schema(broken)
    except RuntimeError:
        pass
    else:
        die("case-manifest deletion falsifier was not detected")


def assert_case_evidence(case: Case, solidity: Mapping, blanc: Mapping) -> None:
    statuses = solidity["status"]
    returns = solidity["returndata"]
    if case.family == "constructor":
        final = statuses[-1]
        if "constructor-success" in case.tags:
            if final != "success":
                die(f"{case.name}: expected constructor success, got {final}")
            topics = [row["topics"][0] for row in solidity["logs"][-1]]
            expected = [
                "0x" + keccak(b"CircuitBreakerInitialized(address,uint256,uint256,uint256,uint256)").hex(),
                "0x" + keccak(b"PauseDurationUpdated(uint256,uint256)").hex(),
                "0x" + keccak(b"HeartbeatIntervalUpdated(uint256,uint256)").hex(),
            ]
            if topics != expected:
                die(f"{case.name}: constructor event order differs from source: {topics}")
        else:
            if final == "success":
                die(f"{case.name}: expected constructor rejection")
            expected_errors = {row["signature"].removesuffix("()"):
                               bytes.fromhex(row["selector"].removeprefix("0x"))
                               for row in _LOCK["abi"]["errors"]}
            tagged_error = next((name for name in expected_errors if name in case.tags), None)
            if tagged_error is not None and returns[-1] != "0x" + expected_errors[tagged_error].hex():
                die(f"{case.name}: expected winning error {tagged_error}, got {returns[-1]}")
            if tagged_error is None and returns[-1] != "0x":
                die(f"{case.name}: malformed/nonpayable constructor must empty-revert")
            if solidity["logs"][-1] or blanc["logs"][-1]:
                die(f"{case.name}: failed constructor retained logs")
        if case.name == "constructor-success-official":
            if solidity["_rawSlotZero"] == blanc["_rawSlotZero"]:
                die("raw-layout control is vacuous: official constructor slot zero agrees")
            if solidity["logicalState"] != blanc["logicalState"]:
                die("raw-layout control did not preserve projected equality")
        return

    expected_errors = {row["signature"].removesuffix("()"):
                       bytes.fromhex(row["selector"].removeprefix("0x"))
                       for row in _LOCK["abi"]["errors"]}
    tagged_error = next((name for name in expected_errors if name in case.tags), None)
    if tagged_error is not None and returns[-1] != "0x" + expected_errors[tagged_error].hex():
        die(f"{case.name}: expected winning runtime error {tagged_error}, got {returns[-1]}")
    if "Panic-0x11" in case.tags:
        expected_panic = "0x" + (keccak(b"Panic(uint256)")[:4] + h256(0x11)).hex()
        if returns[-1] != expected_panic:
            die(f"{case.name}: expected checked-add Panic(0x11), got {returns[-1]}")

    if "oog-control" in case.tags:
        if not statuses[-1].startswith("exception:"):
            die(f"{case.name}: low-gas control did not exhaust execution")
    if "adequate-gas" in case.tags and statuses[-1] != "success":
        die(f"{case.name}: adequate-gas large-return row did not succeed")
    if "short-return" in case.tags:
        expected_size = {
            "pause-return-empty": 0,
            "pause-return-one-byte": 1,
            "pause-return-31-bytes": 31,
        }[case.name]
        for side, result in (("Solidity", solidity), ("Blanc", blanc)):
            trace = result["callTrace"][-1]
            if result["status"][-1] != "revert" or result["returndata"][-1] != "0x" or \
                    len(trace) != 2 or trace[-1].get("opcode") != "STATICCALL" or \
                    len(bytes.fromhex(trace[-1].get("returndata", "0x").removeprefix("0x"))) != expected_size:
                die(f"{case.name}: {side} short-return chronology evidence is incomplete")
    if case.family in {"pause-results", "return-data-resource", "reentry",
                       "callback-interference", "transaction-reset", "overflow"}:
        traces = solidity["callTrace"][-1]
        if statuses[-1] == "success" and "zero-expiry-branch" not in case.tags and \
                case.action and case.action.calldata[:4] == selector("pause(address)") and not traces:
            die(f"{case.name}: successful pause row has no external-call trace")
    if "target-truth-not-guaranteed" in case.tags and statuses[-1] != "success":
        die(f"{case.name}: lying-true target did not witness the declared truth boundary: "
            f"{statuses[-1]} {returns[-1]}")
    if case.name == "pause-return-true":
        topics = [row["topics"][0] for row in solidity["logs"][-1]]
        expected = [
            "0x" + keccak(b"PauserSet(address,address,address)").hex(),
            "0x" + keccak(b"PauseTriggered(address,address,uint256)").hex(),
            "0x" + keccak(b"HeartbeatUpdated(address,uint256)").hex(),
        ]
        if topics != expected:
            die(f"{case.name}: pause event order differs from source: {topics}")
    if case.name == "pause-pause-target-revert":
        trace = solidity["callTrace"][-1]
        if len(trace) != 1 or trace[0].get("success") != "0x0" or \
                trace[0].get("returndata") != "0xdeadbeef" or solidity["logs"][-1]:
            die("target-revert outer rollback trace/log evidence is incomplete")
        if solidity["logicalState"]["assignments"][canonical_address(TARGET_1)] != \
                hex(int.from_bytes(address_bytes(PAUSER_A), "big")):
            die("target-revert outer rollback did not restore assignment")
    if case.name == "pause-query-revert":
        trace = solidity["callTrace"][-1]
        if len(trace) != 2 or trace[-1].get("opcode") != "STATICCALL" or \
                trace[-1].get("success") != "0x0" or trace[-1].get("returndata") != "0xcafe":
            die("query-revert rollback trace did not retain exact STATICCALL failure")
    if case.name == "register-zero-target-before-write":
        if solidity["writeTrace"][-1] or blanc["writeTrace"][-1]:
            die("zero target reached a Registry SSTORE before rejection")
    if case.name == "callback-midcall-liveness":
        expected = ["0x1", "0x20", "0x1"]
        for result in (solidity, blanc):
            actual = result["auxiliaryState"][canonical_address(TARGET_1)]
            if actual != expected:
                die(f"mid-call liveness callback did not observe true: {actual}")
    if case.name == "reentry-clone-namespace":
        for result in (solidity, blanc):
            if result["auxiliaryState"][canonical_address(TARGET_1)][0] != "0x1":
                die("clone namespace nested pause did not succeed")
            clone = result["logicalState"].get("clone")
            if clone is None or clone["assignments"][canonical_address(TARGET_2)] != "0x0":
                die("clone namespace projection did not retain successful nested removal")
    if case.name == "callback-admin-set-duration-snapshot":
        call = solidity["callTrace"][-1][0]
        if call["input"] != "0x" + calldata(
                "pauseFor(uint256)", OFFICIAL["initialPauseDuration"]).hex():
            die("pause callback did not receive the pre-callback duration snapshot")
    if case.name == "callback-admin-set-interval-post-expiry":
        expected_expiry = case.action.timestamp + OFFICIAL["minHeartbeatInterval"]
        if int(solidity["logicalState"]["expiries"][canonical_address(PAUSER_A)], 16) != expected_expiry:
            die("pause expiry did not use post-callback heartbeat interval")
    if case.name == "next-transaction-after-success" and statuses[-1] != "success":
        die("next transaction after successful pause retained a transient lock")
    if case.name == "next-transaction-after-failure":
        expected = "0x" + expected_errors["PauseFailed"].hex()
        if returns[-1] != expected:
            die("next transaction after failed pause retained a transient lock")
    if "sequential-transactions" in case.tags and len(statuses) < 3:
        die(f"{case.name}: sequential reset evidence has too few transactions")


def channel_falsifiers(sample: Case, solidity: Mapping, blanc: Mapping) -> int:
    checks = 0
    for channel, fields in CHANNEL_FIELDS.items():
        broken = copy.deepcopy(blanc)
        field = fields[0]
        if isinstance(broken[field], list):
            broken[field].append({"corrupt": True})
        elif isinstance(broken[field], dict):
            broken[field]["__corrupt__"] = True
        else:
            broken[field] = str(broken[field]) + "-corrupt"
        probe = copy.copy(sample); probe.channels = (channel,)
        if not compare(probe, solidity, broken):
            die(f"live {channel} channel falsifier was not detected")
        checks += 1
    return checks


def projection_falsifiers(sample: Case, solidity: Mapping, blanc: Mapping) -> int:
    checks = 0
    mutations = [
        ("pauseDuration", lambda logical: logical.__setitem__("pauseDuration", "0xdead")),
        ("heartbeatInterval", lambda logical: logical.__setitem__("heartbeatInterval", "0xdead")),
        ("assignment", lambda logical: logical["assignments"].__setitem__(
            canonical_address(TARGET_1), "0xdead")),
        ("index", lambda logical: logical["indices"].__setitem__(
            canonical_address(TARGET_1), "0xdead")),
        ("count", lambda logical: logical["counts"].__setitem__(
            canonical_address(PAUSER_A), "0xdead")),
        ("expiry", lambda logical: logical["expiries"].__setitem__(
            canonical_address(PAUSER_A), "0xdead")),
        ("array-entry", lambda logical: logical["array"].__setitem__(0, "0xdead")),
        ("array-order", lambda logical: logical["array"].reverse()),
    ]
    for name, mutate in mutations:
        broken = copy.deepcopy(blanc)
        mutate(broken["logicalState"])
        probe = copy.copy(sample); probe.channels = ("state-projection",)
        if not compare(probe, solidity, broken):
            die(f"live projection {name} falsifier was not detected")
        checks += 1
    return checks


def candidate_ac5_shape_evidence(
        results: Mapping[str, Tuple[Mapping, Mapping]]) -> Mapping:
    rows: List[Mapping] = []
    parent = canonical_address(CIRCUIT)
    for case_name, return_bytes, _ in CANDIDATE_SHAPE_CASES:
        for side_index, side in ((0, "solidity"), (1, "blanc")):
            result = results[case_name][side_index]
            operations = result["_resourceOps"][-1]
            staticcalls = [
                row for row in operations
                if row["opcode"] == "STATICCALL" and row["source"] == parent
            ]
            trace_staticcalls = [
                row for row in result["callTrace"][-1]
                if row["opcode"] == "STATICCALL" and row["source"] == parent
            ]
            if len(staticcalls) != 1 or len(trace_staticcalls) != 1:
                die(f"{case_name}/{side}: exact parent STATICCALL evidence differs")
            copied = [
                row for row in operations
                if row["opcode"] == "RETURNDATACOPY" and row["source"] == parent
            ]
            observed_return_bytes = len(bytes.fromhex(
                trace_staticcalls[0]["returndata"].removeprefix("0x")))
            rows.append({
                "case": case_name,
                "side": side,
                "returnBytes": return_bytes,
                "status": result["status"][-1],
                "staticcallSource": staticcalls[0]["source"],
                "staticcallTarget": trace_staticcalls[0]["target"],
                "staticcallOutputOffset": staticcalls[0]["outputOffset"],
                "staticcallOutputSize": staticcalls[0]["outputSize"],
                "staticcallReturndataBytes": observed_return_bytes,
                "successReturndatacopy": copied,
            })
    validate_candidate_parent_shape(rows)

    # Mutate an actually captured 65,536-byte candidate row, not a toy shape.
    # A complete successful-tail copy must be rejected by the same independent
    # validator that accepts the measured trace rows above.
    mutant = copy.deepcopy(rows)
    mutant[-1]["successReturndatacopy"].append({
        "opcode": "RETURNDATACOPY", "source": parent,
        "memoryOffset": 1024, "returndataOffset": 0,
        "size": mutant[-1]["returnBytes"],
    })
    try:
        validate_candidate_parent_shape(mutant, "AC5 full-copy mutant")
    except Ac5ShapeError as exc:
        if "successful-tail RETURNDATACOPY is prohibited" not in str(exc):
            raise
    else:
        die("AC5 full-success-tail-copy mutant escaped independent shape validation")

    failure_rows: List[Mapping] = []
    for case_name, expected_bytes in (
            ("pause-pause-target-revert", 4),
            ("pause-query-revert", 2),
            ("pause-pause-target-revert-large-256", 256),
            ("pause-query-revert-large-256", 256)):
        for side_index, side in ((0, "solidity"), (1, "blanc")):
            result = results[case_name][side_index]
            calls = [
                row for row in result["_resourceOps"][-1]
                if row["opcode"] in ("CALL", "STATICCALL") and
                row["source"] == parent
            ]
            failed_traces = [
                row for row in result["callTrace"][-1]
                if row["source"] == parent and row["target"] == TARGET_1 and
                row.get("success") == "0x0"
            ]
            if len(failed_traces) != 1:
                die(f"{case_name}/{side}: exact failed parent call differs")
            failed_trace = failed_traces[0]
            call_shapes = [row for row in calls if row["opcode"] == failed_trace["opcode"]]
            if len(call_shapes) != 1:
                die(f"{case_name}/{side}: failed parent call geometry differs")
            failed_call = call_shapes[0]
            observed_failure_bytes = len(bytes.fromhex(
                failed_trace["returndata"].removeprefix("0x")))
            copies = [
                row for row in result["_resourceOps"][-1]
                if row["opcode"] == "RETURNDATACOPY" and row["source"] == parent
            ]
            if len(copies) != 1 or copies[0]["returndataOffset"] != 0 or \
                    copies[0]["size"] != expected_bytes:
                die(f"{case_name}/{side}: full failure-returndata copy evidence differs")
            failure_rows.append({
                "case": case_name, "side": side,
                "returndataBytes": expected_bytes,
                "failedCall": {
                    "opcode": failed_trace["opcode"],
                    "source": failed_trace["source"],
                    "target": failed_trace["target"],
                    "outputOffset": failed_call["outputOffset"],
                    "outputSize": failed_call["outputSize"],
                    "returndataBytes": observed_failure_bytes,
                },
                "returndatacopy": copies[0],
            })
    return {
        "schema": 1,
        "successfulStaticcallRows": rows,
        "failureBubbleRows": failure_rows,
        "fullCopyMutantRejected": True,
        "failureMutantsRejected": True,
    }


def resource_evidence(
        results: Mapping[str, Tuple[Mapping, Mapping]], *,
        candidate_shape: bool = False) -> Mapping | None:
    sizes = (64, 256, 1024, 4096, 16384, 32768)
    for side_index, side in [(0, "solidity"), (1, "blanc")]:
        gas = [results[f"pause-return-true-large-{size}"][side_index]["gasUsed"][-1]
               for size in sizes]
        if any(a >= b for a, b in zip(gas, gas[1:])):
            die(f"{side} successful-return gas is not strictly increasing: {gas}")
        if gas[-1] - gas[0] < 3_000:
            die(f"{side} large-return execution scaling is unexpectedly small")
    sol_delta = (results["pause-return-true-large-32768"][0]["gasUsed"][-1] -
                 results["pause-return-true-large-64"][0]["gasUsed"][-1])
    blanc_delta = (results["pause-return-true-large-32768"][1]["gasUsed"][-1] -
                   results["pause-return-true-large-64"][1]["gasUsed"][-1])
    if not candidate_shape:
        # Frozen fc3edee compatibility: the old Blanc implementation copied
        # the complete successful tail, so its slope stayed close to Solidity.
        if abs(sol_delta - blanc_delta) > max(1_500, sol_delta // 4):
            die(f"large-return parent allocation slopes diverge: Solidity {sol_delta}, Blanc {blanc_delta}")
        return None

    extended_sizes = (*sizes, 65536)
    for side_index, side in ((0, "solidity"), (1, "blanc")):
        gas = [results[f"pause-return-true-large-{size}"][side_index]["gasUsed"][-1]
               for size in extended_sizes]
        if any(a >= b for a, b in zip(gas, gas[1:])):
            die(f"{side} amended successful-return gas is not strictly increasing: {gas}")
    # The pinned full-copy Blanc slope was 16,488 gas over 64→32,768 bytes.
    # The amended candidate must exhibit the materially smaller no-tail-copy
    # class as well as the direct opcode-shape evidence below.
    if blanc_delta > sol_delta or blanc_delta >= 16_488:
        die("amended Blanc successful-return slope remains full-copy-class: "
            f"Solidity {sol_delta}, Blanc {blanc_delta}")
    shape = dict(candidate_ac5_shape_evidence(results))
    shape["gasSlope"] = {
        "fromReturnBytes": 64,
        "toReturnBytes": 32768,
        "solidityGasUsedDelta": sol_delta,
        "blancGasUsedDelta": blanc_delta,
        "frozenBlancFullCopyGasUsedDelta": 16_488,
    }
    validate_candidate_shape_evidence(shape)
    return shape


def canonical_digest(value: object) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def resource_identities(lock: Mapping, artifacts: Mapping) -> Mapping:
    worlds = {world["name"]: world for world in lock["artifacts"]["worlds"]}
    official = worlds["official-mainnet"]
    independent = worlds["independent-parameters"]
    return {
        "eelsCommit": EELS_PIN,
        "referenceSourceCommit": lock["target"]["releaseCommit"],
        "solidityOfficialFullCreateSha256": official["fullCreateInput"]["sha256"],
        "solidityOfficialRuntimeSha256": official["returnedRuntime"]["sha256"],
        "solidityIndependentFullCreateSha256": independent["fullCreateInput"]["sha256"],
        "solidityIndependentRuntimeSha256": independent["returnedRuntime"]["sha256"],
        "blancCreationTemplateSha256": hashlib.sha256(
            artifacts["creation-template"]).hexdigest(),
        "blancOfficialFullCreateSha256": hashlib.sha256(
            artifacts["official-create"]).hexdigest(),
        "blancOfficialRuntimeSha256": hashlib.sha256(
            artifacts["official-runtime"]).hexdigest(),
        "blancIndependentFullCreateSha256": hashlib.sha256(
            artifacts["independent-create"]).hexdigest(),
        "blancIndependentRuntimeSha256": hashlib.sha256(
            artifacts["independent-runtime"]).hexdigest(),
    }


def resource_model() -> Mapping:
    return {
        "engine": "ethereum/execution-specs",
        "fork": "Prague",
        "scope": "direct-eels-message",
        "gasUsedFormula": "message.gas - output.gas_left",
        "refundAccounting": "pre-refund",
        "transactionIntrinsicGasIncluded": False,
        "createCodeDepositGasIncluded": True,
    }


def resource_lifecycle() -> Mapping:
    return {
        "stage": RESOURCE_LIFECYCLE,
        "baselineBlancCommit": RESOURCE_BASELINE_COMMIT,
        "baselineManifestSha256": RESOURCE_BASELINE_MANIFEST_SHA256,
        "optimizedTransitionRequires": {
            "adequateGasDominance": True,
            "strictSuccessfulImprovement": True,
            "independentDigestRepin": True,
        },
    }


def enforce_resource_lifecycle(
        blanc_identities: Mapping, summary: Mapping, *,
        read_only_experiment: bool, lifecycle: str = RESOURCE_LIFECYCLE) -> None:
    if lifecycle not in {"baseline", "optimized"}:
        die(f"unknown resource lifecycle {lifecycle}")
    # Experiments still execute and compare every behavior/resource boundary.
    # They skip only the acceptance decision so a candidate artifact can be
    # measured before its reviewed lifecycle transition and independent pins.
    if read_only_experiment:
        return
    if lifecycle == "baseline":
        if blanc_identities != RESOURCE_BASELINE_BLANC_IDENTITIES:
            die("baseline resource lifecycle artifact identity drifted; transition deliberately")
        return
    if summary["adequatePositiveDeltaCount"] != 0:
        die("optimized resource lifecycle has a positive adequate-gas boundary")
    if summary["successfulStrictImprovementCount"] < 1:
        die("optimized resource lifecycle lacks a strict successful improvement")


def experiment_summary_payload(metrics: Mapping) -> Mapping:
    adequate_positive = [
        {"coordinate": row["coordinate"], "delta": row["blancMinusSolidity"]}
        for row in metrics["boundaries"]
        if row["adequacy"] == "adequate" and row["blancMinusSolidity"] > 0
    ]
    payload = {
        "mode": "read-only-experiment",
        "lifecycleAcceptance": "skipped-read-only-experiment",
        "lifecycle": metrics["lifecycle"],
        "identities": metrics["identities"],
        "summary": metrics["summary"],
        "vectorDigests": metrics["vectorDigests"],
        "worstAdequatePositive": sorted(
            adequate_positive, key=lambda row: row["delta"], reverse=True)[:20],
    }
    if "successfulReturnShape" in metrics:
        payload["successfulReturnShape"] = metrics["successfulReturnShape"]
    return payload


def resource_experiment_escape_self_check() -> None:
    drifted = dict(RESOURCE_BASELINE_BLANC_IDENTITIES)
    drifted["creationTemplateSha256"] = "0" * 64
    synthetic_summary = {
        "adequatePositiveDeltaCount": 1,
        "successfulStrictImprovementCount": 0,
    }
    enforce_resource_lifecycle(
        drifted, synthetic_summary, read_only_experiment=True,
        lifecycle="baseline")
    enforce_resource_lifecycle(
        drifted, synthetic_summary, read_only_experiment=True,
        lifecycle="optimized")
    synthetic_payload = experiment_summary_payload({
        "boundaries": [], "lifecycle": {"stage": "baseline"},
        "identities": {"blancCreationTemplateSha256":
                       drifted["creationTemplateSha256"]},
        "summary": synthetic_summary, "vectorDigests": {},
    })
    if synthetic_payload["identities"]["blancCreationTemplateSha256"] != "0" * 64:
        die("read-only experiment omitted synthetic artifact identity drift")
    try:
        enforce_resource_lifecycle(
            drifted, synthetic_summary, read_only_experiment=False,
            lifecycle="baseline")
    except RuntimeError as exc:
        if str(exc) != \
                "baseline resource lifecycle artifact identity drifted; transition deliberately":
            raise
    else:
        die("ordinary baseline lifecycle accepted synthetic artifact identity drift")
    try:
        enforce_resource_lifecycle(
            drifted, synthetic_summary, read_only_experiment=False,
            lifecycle="optimized")
    except RuntimeError as exc:
        if str(exc) != \
                "optimized resource lifecycle has a positive adequate-gas boundary":
            raise
    else:
        die("ordinary optimized lifecycle accepted a synthetic positive gas delta")
    no_strict_improvement = {
        "adequatePositiveDeltaCount": 0,
        "successfulStrictImprovementCount": 0,
    }
    try:
        enforce_resource_lifecycle(
            drifted, no_strict_improvement, read_only_experiment=False,
            lifecycle="optimized")
    except RuntimeError as exc:
        if str(exc) != \
                "optimized resource lifecycle lacks a strict successful improvement":
            raise
    else:
        die("ordinary optimized lifecycle accepted no strict successful improvement")


def resource_descriptor_rows(case: Case) -> List[Mapping]:
    execution = case_execution_descriptor(case)
    rows: List[Mapping] = [{
        "boundary": execution["constructor"]["boundary"],
        "label": execution["boundaryOrder"][0],
        "phase": "primaryConstructor", "orderWithinPhase": 0,
        "gasLimit": execution["constructor"]["gas"],
    }]
    offset = 1
    clone_constructor = execution["cloneConstructor"]
    if clone_constructor is not None:
        rows.append({
            "boundary": clone_constructor["boundary"],
            "label": execution["boundaryOrder"][offset],
            "phase": "cloneConstructor", "orderWithinPhase": 0,
            "gasLimit": clone_constructor["gas"],
        })
        offset += 1
    for phase in ("cloneHistory", "history"):
        for descriptor in execution[phase]:
            rows.append({
                "boundary": descriptor["boundary"],
                "label": execution["boundaryOrder"][offset],
                "phase": phase,
                "orderWithinPhase": descriptor["orderWithinPhase"],
                "gasLimit": descriptor["gas"],
            })
            offset += 1
    action = execution["action"]
    if action is not None:
        rows.append({
            "boundary": action["boundary"],
            "label": execution["boundaryOrder"][offset],
            "phase": "action", "orderWithinPhase": action["orderWithinPhase"],
            "gasLimit": action["gas"],
        })
        offset += 1
    if offset != len(execution["boundaryOrder"]):
        die(f"{case.name}: resource descriptors do not consume boundaryOrder")
    if [row["boundary"] for row in rows] != list(range(len(rows))):
        die(f"{case.name}: resource descriptor boundaries are not contiguous")
    return rows


def full_resource_boundaries(
        cases: Sequence[Case], results: Mapping[str, Tuple[Mapping, Mapping]]) -> List[Mapping]:
    boundaries: List[Mapping] = []
    expected_boundary_count = 0
    for case in cases:
        descriptors = resource_descriptor_rows(case)
        expected_boundary_count += len(descriptors)
        solidity = results[case.name][0]["_resourceBoundaries"]
        blanc = results[case.name][1]["_resourceBoundaries"]
        if len(solidity) != len(descriptors) or len(blanc) != len(descriptors):
            die(f"{case.name}: measured resources do not align with boundaryOrder")
        for descriptor, sol, bla in zip(descriptors, solidity, blanc):
            if sol["gasLimit"] != descriptor["gasLimit"] or \
                    bla["gasLimit"] != descriptor["gasLimit"]:
                die(f"{case.name}: measured gas limit differs from descriptor")
            if sol["status"] != bla["status"]:
                die(f"{case.name}: resource status differs across implementations")
            phase = descriptor["phase"]
            oog_control = "oog-control" in case.tags and phase == "action"
            if oog_control:
                expected_oog = "exception:OutOfGasError"
                if sol["status"] != expected_oog:
                    die(f"{case.name}: named OOG resource control did not exhaust gas")
                adequacy = "oog-control"
            else:
                if sol["status"] == "exception:OutOfGasError":
                    die(f"{case.name}: unlabelled resource boundary exhausted gas")
                adequacy = "adequate"
            delta = bla["gasUsed"] - sol["gasUsed"]
            comparison = (
                "blanc-cheaper" if delta < 0 else
                "blanc-dearer" if delta > 0 else "equal")
            boundary = descriptor["boundary"]
            label = descriptor["label"]
            boundaries.append({
                "ordinal": len(boundaries),
                "coordinate": f"{case.name}#{boundary}:{label}",
                "case": case.name, "boundary": boundary,
                "label": label, "phase": phase,
                "orderWithinPhase": descriptor["orderWithinPhase"],
                "adequacy": adequacy,
                "solidityStatus": sol["status"], "blancStatus": bla["status"],
                "solidityGasLimit": sol["gasLimit"],
                "blancGasLimit": bla["gasLimit"],
                "solidityGasUsed": sol["gasUsed"],
                "blancGasUsed": bla["gasUsed"],
                "blancMinusSolidity": delta,
                "comparisonClass": comparison,
            })
    if len(boundaries) != expected_boundary_count:
        die("full resource-vector boundary count differs from execution descriptors: "
            f"{len(boundaries)} != {expected_boundary_count}")
    return boundaries


def resource_summary(boundaries: Sequence[Mapping]) -> Mapping:
    class_counts = {key: 0 for key in ("blanc-cheaper", "equal", "blanc-dearer")}
    adequacy_counts = {key: 0 for key in ("adequate", "oog-control")}
    for row in boundaries:
        class_counts[row["comparisonClass"]] += 1
        adequacy_counts[row["adequacy"]] += 1
    return {
        "boundaryCount": len(boundaries),
        "adequacyCounts": adequacy_counts,
        "comparisonClassCounts": class_counts,
        "adequatePositiveDeltaCount": sum(
            row["adequacy"] == "adequate" and row["blancMinusSolidity"] > 0
            for row in boundaries),
        "successfulStrictImprovementCount": sum(
            row["adequacy"] == "adequate" and
            row["solidityStatus"] == "success" and
            row["blancStatus"] == "success" and
            row["blancMinusSolidity"] < 0
            for row in boundaries),
        "solidityGasUsedTotal": sum(row["solidityGasUsed"] for row in boundaries),
        "blancGasUsedTotal": sum(row["blancGasUsed"] for row in boundaries),
        "blancMinusSolidityTotal": sum(
            row["blancMinusSolidity"] for row in boundaries),
    }


def resource_metrics(cases: Sequence[Case], results: Mapping[str, Tuple[Mapping, Mapping]],
                     lock: Mapping, artifacts: Mapping, *,
                     read_only_experiment: bool = False,
                     ac5_shape_evidence: Mapping | None = None) -> Mapping:
    sizes = [64, 256, 1024, 4096, 16384, 32768]
    if ac5_shape_evidence is not None:
        sizes.append(65536)
    rows = {}
    for size in sizes:
        name = f"pause-return-true-large-{size}"
        solidity = results[name][0]["gasUsed"][-1]
        blanc = results[name][1]["gasUsed"][-1]
        rows[name] = {
            "returnBytes": size, "solidityGasUsed": solidity,
            "blancGasUsed": blanc, "blancMinusSolidity": blanc - solidity,
        }
    controls = {}
    for size in (4096, 32768):
        name = f"pause-return-large-{size}-oog-control"
        controls[name] = {
            "returnBytes": size,
            "gasLimit": 25_000,
            "solidityGasUsed": results[name][0]["gasUsed"][-1],
            "blancGasUsed": results[name][1]["gasUsed"][-1],
            "solidityStatus": results[name][0]["status"][-1],
            "blancStatus": results[name][1]["status"][-1],
        }
    first, last = rows["pause-return-true-large-64"], rows[
        f"pause-return-true-large-{sizes[-1]}"]
    representative_names = (
        "constructor-success-official", "view-pause-duration",
        "setter-pause-authorized-lower", "register-fresh", "pause-return-true",
        "enumeration-64-targets",
    )
    representatives = {}
    for name in representative_names:
        sol = results[name][0]["gasUsed"]
        blanc = results[name][1]["gasUsed"]
        representatives[name] = {
            "solidityGasUsedByBoundary": sol,
            "blancGasUsedByBoundary": blanc,
            "blancMinusSolidityByBoundary": [b - s for s, b in zip(sol, blanc)],
        }
    short_return_paths = {}
    for name, size in (("pause-return-empty", 0), ("pause-return-one-byte", 1),
                       ("pause-return-31-bytes", 31)):
        solidity = results[name][0]["gasUsed"][-1]
        blanc = results[name][1]["gasUsed"][-1]
        short_return_paths[name] = {
            "returnBytes": size, "solidityGasUsed": solidity,
            "blancGasUsed": blanc, "blancMinusSolidity": blanc - solidity,
        }
    boundaries = full_resource_boundaries(cases, results)
    summary = resource_summary(boundaries)
    identities = resource_identities(lock, artifacts)
    model = resource_model()
    lifecycle = resource_lifecycle()
    baseline_blanc = {
        "creationTemplateSha256": identities["blancCreationTemplateSha256"],
        "officialFullCreateSha256": identities["blancOfficialFullCreateSha256"],
        "officialRuntimeSha256": identities["blancOfficialRuntimeSha256"],
        "independentFullCreateSha256": identities[
            "blancIndependentFullCreateSha256"],
        "independentRuntimeSha256": identities["blancIndependentRuntimeSha256"],
    }
    enforce_resource_lifecycle(
        baseline_blanc, summary, read_only_experiment=read_only_experiment)
    coordinates = [row["coordinate"] for row in boundaries]
    vector_payload = {
        "schema": RESOURCE_SCHEMA, "gasModel": model, "lifecycle": lifecycle,
        "identities": identities, "boundaries": boundaries,
    }
    metrics = {
        "schema": RESOURCE_SCHEMA,
        "adequateGasEnvelope": 20_000_000,
        "gasModel": model,
        "lifecycle": lifecycle,
        "identities": identities,
        "boundaries": boundaries,
        "summary": summary,
        "vectorDigests": {
            "orderedCoordinatesSha256": hashlib.sha256(
                ("\n".join(coordinates) + "\n").encode()).hexdigest(),
            "fullResourceVectorSha256": canonical_digest(vector_payload),
        },
        "successfulLargeReturnPaths": rows,
        "successfulRangeDelta": {
            "fromReturnBytes": 64, "toReturnBytes": sizes[-1],
            "solidityGasUsedDelta": last["solidityGasUsed"] - first["solidityGasUsed"],
            "blancGasUsedDelta": last["blancGasUsed"] - first["blancGasUsed"],
        },
        "oogControls": controls,
        "representativePublicPaths": representatives,
        "shortReturnPaths": short_return_paths,
        "adjudication": (
            "frozen pre-optimization measurement; positive deltas require deliberate "
            "optimized-lifecycle transition" if RESOURCE_LIFECYCLE == "baseline" else
            "optimized lifecycle requires adequate-gas per-boundary dominance and at "
            "least one strict successful improvement"),
    }
    if ac5_shape_evidence is not None:
        metrics["successfulReturnShape"] = ac5_shape_evidence
    return metrics


def validate_manifest_schema(manifest: Mapping) -> None:
    expected_top = {
        "schema", "oracle", "blanc", "projection", "execution", "coverage",
        "counts", "resourceEvidence", "rows", "explicitLimits",
    }
    if set(manifest) != expected_top or manifest.get("schema") != 2:
        die("Lido differential manifest schema/top-level keys drifted")
    rows = manifest.get("rows")
    counts = manifest.get("counts")
    resource_stage = manifest.get("resourceEvidence", {}).get(
        "lifecycle", {}).get("stage")
    if resource_stage not in {"baseline", "optimized"}:
        die("Lido differential resource lifecycle stage drifted")
    candidate_resource_shape = resource_stage == "optimized"
    expected_row_count = 175 if candidate_resource_shape else 172
    expected_boundary_count = 464 if candidate_resource_shape else 455
    if not isinstance(rows, list) or not isinstance(counts, dict):
        die("Lido differential manifest rows/counts have wrong types")
    if counts != {"rows": expected_row_count, "runtimeSelectors": 17,
                  "constructorArguments": 7, "customErrors": 15, "events": 6}:
        die(f"Lido differential manifest fixed counts drifted: {counts}")
    if len(rows) != counts["rows"] or len({row.get("name") for row in rows}) != len(rows):
        die("Lido differential manifest row count/names are inconsistent")
    coverage = manifest.get("coverage")
    if not isinstance(coverage, dict) or coverage.get("requiredTags") != REQUIRED_TAGS:
        die("Lido differential manifest required-tag ownership drifted")
    actual_tags: Dict[str, int] = {}
    actual_families: Dict[str, int] = {}
    actual_endpoints: Dict[str, int] = {}
    actual_channels: Dict[str, int] = {}
    expected_channels = [
        "status", "returndata", "state-projection", "eth", "logs", "call-trace"]
    required_row_keys = {
        "name", "family", "owner", "world", "endpoint", "historyLength",
        "execution", "channels", "tags",
    }
    for row in rows:
        if set(row) != required_row_keys or row.get("channels") != expected_channels:
            die(f"Lido differential row schema/channels drifted: {row.get('name')}")
        execution = row.get("execution")
        if not isinstance(execution, dict) or set(execution) != {
                "constructor", "cloneConstructor", "cloneHistory", "history", "action",
                "boundaryOrder", "targetCode", "observeTargets", "observePausers",
                "observeAuxSlots"}:
            die(f"Lido differential execution descriptor incomplete: {row.get('name')}")
        if len(execution["history"]) + len(execution["cloneHistory"]) != row["historyLength"]:
            die(f"Lido differential history count drifted: {row['name']}")
        expected_boundaries = (1 + (execution["cloneConstructor"] is not None) +
                               len(execution["cloneHistory"]) + len(execution["history"]) +
                               (execution["action"] is not None))
        if len(execution["boundaryOrder"]) != expected_boundaries:
            die(f"Lido differential transaction boundaries incomplete: {row['name']}")
        constructor = execution["constructor"]
        if set(constructor) != {
                "boundary", "target", "caller", "value", "timestamp", "gas",
                "parameters", "argumentSuffixSource", "argumentSuffix",
                "ordinaryArgumentSuffix", "trailing", "malformed"}:
            die(f"Lido differential constructor descriptor incomplete: {row['name']}")
        for field in ("argumentSuffix", "ordinaryArgumentSuffix", "trailing"):
            descriptor = constructor[field]
            raw = bytes.fromhex(descriptor["hex"].removeprefix("0x"))
            if descriptor != byte_descriptor(raw):
                die(f"Lido differential constructor {field} identity corrupt: {row['name']}")
        if set(constructor["malformed"]) != {
                "kind", "expectedArgumentBytes", "actualArgumentBytes",
                "missingArgumentBytes", "dirtyAdminHighBits"}:
            die(f"Lido differential constructor malformed descriptor incomplete: {row['name']}")
        if constructor["malformed"]["actualArgumentBytes"] != \
                constructor["argumentSuffix"]["byteLength"]:
            die(f"Lido differential constructor boundary length corrupt: {row['name']}")
        clone_constructor = execution["cloneConstructor"]
        if clone_constructor is not None:
            if set(clone_constructor) != {
                    "boundary", "target", "caller", "value", "timestamp", "gas",
                    "parameters", "argumentSuffix"}:
                die(f"Lido differential clone constructor descriptor incomplete: {row['name']}")
            clone_suffix = clone_constructor["argumentSuffix"]
            clone_raw = bytes.fromhex(clone_suffix["hex"].removeprefix("0x"))
            if clone_suffix != byte_descriptor(clone_raw):
                die(f"Lido differential clone constructor suffix corrupt: {row['name']}")
        for address, descriptor in execution["targetCode"].items():
            if canonical_address(address) != address or set(descriptor) != {"byteLength", "sha256"}:
                die(f"Lido differential target-code identity corrupt: {row['name']}")
        for tx in [*execution["cloneHistory"], *execution["history"],
                   *([] if execution["action"] is None else [execution["action"]])]:
            if set(tx) != {"boundary", "phase", "orderWithinPhase", "caller", "target",
                           "value", "timestamp", "gas", "calldata"}:
                die(f"Lido differential transaction descriptor incomplete: {row['name']}")
            calldata_descriptor = tx["calldata"]
            raw = bytes.fromhex(calldata_descriptor["hex"].removeprefix("0x"))
            if calldata_descriptor != byte_descriptor(raw):
                die(f"Lido differential calldata identity corrupt: {row['name']}")
        for tag in row["tags"]:
            actual_tags[tag] = actual_tags.get(tag, 0) + 1
        actual_families[row["family"]] = actual_families.get(row["family"], 0) + 1
        actual_endpoints[row["endpoint"]] = actual_endpoints.get(row["endpoint"], 0) + 1
        for channel in row["channels"]:
            actual_channels[channel] = actual_channels.get(channel, 0) + 1
    if any(tag not in actual_tags for tag in REQUIRED_TAGS):
        die("Lido differential manifest lost a required case family/tag")
    for key, actual in [("tagCounts", actual_tags), ("familyCounts", actual_families),
                        ("endpointCounts", actual_endpoints),
                        ("channelCounts", actual_channels)]:
        if coverage.get(key) != actual:
            die(f"Lido differential manifest {key} is inconsistent")
    if set(actual_endpoints) != {
            "constructor", "empty-calldata", "unknown-selector",
            *[row["signature"] for row in _LOCK["abi"]["functions"]]}:
        die("Lido differential manifest endpoint surface is not exact")
    resources = manifest.get("resourceEvidence", {})
    expected_resource_keys = {
        "schema", "adequateGasEnvelope", "gasModel", "lifecycle", "identities",
        "boundaries", "summary", "vectorDigests", "successfulLargeReturnPaths",
        "successfulRangeDelta", "oogControls", "representativePublicPaths",
        "shortReturnPaths", "adjudication",
    }
    if candidate_resource_shape:
        expected_resource_keys.add("successfulReturnShape")
    if not isinstance(resources, dict) or set(resources) != expected_resource_keys or \
            resources.get("schema") != RESOURCE_SCHEMA:
        die("Lido differential full resource-evidence schema drifted")
    resource_rows = resources.get("boundaries")
    if not isinstance(resource_rows, list) or \
            len(resource_rows) != expected_boundary_count or \
            [row.get("ordinal") for row in resource_rows] != \
            list(range(expected_boundary_count)) or \
            len({row.get("coordinate") for row in resource_rows}) != \
            expected_boundary_count:
        die("Lido differential full resource-vector coverage/order drifted")
    if resources.get("summary") != resource_summary(resource_rows):
        die("Lido differential full resource-vector summary drifted")
    coordinates = [row["coordinate"] for row in resource_rows]
    vector_payload = {
        "schema": resources["schema"], "gasModel": resources["gasModel"],
        "lifecycle": resources["lifecycle"], "identities": resources["identities"],
        "boundaries": resource_rows,
    }
    expected_digests = {
        "orderedCoordinatesSha256": hashlib.sha256(
            ("\n".join(coordinates) + "\n").encode()).hexdigest(),
        "fullResourceVectorSha256": canonical_digest(vector_payload),
    }
    if resources.get("vectorDigests") != expected_digests:
        die("Lido differential full resource-vector digest drifted")
    successful = resources.get("successfulLargeReturnPaths", {})
    expected_resource_names = {
        f"pause-return-true-large-{size}"
        for size in ((64, 256, 1024, 4096, 16384, 32768, 65536)
                     if candidate_resource_shape else
                     (64, 256, 1024, 4096, 16384, 32768))}
    if set(successful) != expected_resource_names or resources.get("adequateGasEnvelope") != 20_000_000:
        die("Lido differential resource/gas evidence is incomplete")
    if set(resources.get("representativePublicPaths", {})) != {
            "constructor-success-official", "view-pause-duration",
            "setter-pause-authorized-lower", "register-fresh", "pause-return-true",
            "enumeration-64-targets"}:
        die("Lido differential representative public-path gas evidence is incomplete")
    if set(resources.get("shortReturnPaths", {})) != {
            "pause-return-empty", "pause-return-one-byte", "pause-return-31-bytes"}:
        die("Lido differential short-return chronology evidence is incomplete")
    if candidate_resource_shape:
        validate_candidate_shape_against_resource_paths(
            resources.get("successfulReturnShape"), successful)
    blanc = manifest.get("blanc", {})
    if blanc.get("patchControlsValid") is not True or blanc.get("runtimeSyntaxSiteCounts") != {
            "persistent": 20, "transient": 3, "external": 2}:
        die("Lido differential patch/source inventory metadata drifted")
    if blanc.get("constructorInventoryCounts") != {
            "persistent": 2, "transient": 0, "external": 0}:
        die("Lido differential constructor source inventory metadata drifted")


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--eels-root", required=True)
    parser.add_argument("--blanc-artifacts", required=True)
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--manifest-only", action="store_true")
    parser.add_argument("--experiment-summary", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)
    if args.write_manifest and args.experiment_summary:
        die("--experiment-summary is read-only and cannot write the manifest")
    resource_experiment_escape_self_check()

    verify_eels_pin(Path(args.eels_root).expanduser().resolve())
    global _LOCK
    _LOCK = json.loads(LOCK_PATH.read_text())
    artifacts = parse_artifacts(Path(args.blanc_artifacts).read_text())
    positive_artifact_checks, identity_corruptions = validate_identities(_LOCK, artifacts)
    candidate_resource_shape = args.experiment_summary or \
        RESOURCE_LIFECYCLE == "optimized"
    cases = build_cases(candidate_resource_shape)
    mismatches = []
    results: Dict[str, Tuple[Mapping, Mapping]] = {}
    # Manifest generation owns the complete resource vector, so even the
    # deliberate --manifest-only route executes all cases and all boundaries.
    for case in cases:
        solidity = run_side(case, "solidity", _LOCK, artifacts)
        blanc = run_side(case, "blanc", _LOCK, artifacts)
        bad = compare(case, solidity, blanc)
        if bad:
            mismatches.append((case.name, bad, solidity, blanc))
            if args.verbose:
                print(f"MISMATCH {case.name}: {bad}", file=sys.stderr)
        else:
            assert_case_evidence(case, solidity, blanc)
        results[case.name] = (solidity, blanc)
    if mismatches:
        name, bad, solidity, blanc = mismatches[0]
        detail = "; ".join(f"{field}: S={json.dumps(solidity[field], sort_keys=True)} "
                           f"B={json.dumps(blanc[field], sort_keys=True)}" for field in bad)
        die(f"{len(mismatches)}/{len(cases)} rows mismatch; first {name}: {detail[:1800]}")
    ac5_shape_evidence = resource_evidence(
        results, candidate_shape=candidate_resource_shape)
    metrics = resource_metrics(
        cases, results, _LOCK, artifacts,
        read_only_experiment=args.experiment_summary,
        ac5_shape_evidence=ac5_shape_evidence)
    if args.experiment_summary:
        print(json.dumps(experiment_summary_payload(metrics), indent=2, sort_keys=True))
        return 0
    expected_manifest = build_manifest(cases, _LOCK, artifacts, metrics)
    require_manifest(expected_manifest, args.write_manifest)
    if args.manifest_only:
        print(f"OK — Lido CircuitBreaker differential manifest: {len(cases)} explicit rows; "
              f"{metrics['summary']['boundaryCount']} complete resource boundaries; "
              "17/17 selectors + constructor covered; 15 positive artifact checks + "
              "1 runtime corruption live")
        return 0

    sample_case = next(case for case in cases if case.name == "pause-return-true")
    sample = results[sample_case.name]
    falsifiers = channel_falsifiers(sample_case, sample[0], sample[1])
    projection_case = next(case for case in cases if case.name == "remove-middle")
    projection = results[projection_case.name]
    projection_checks = projection_falsifiers(
        projection_case, projection[0], projection[1])
    traced = sum(sum(len(trace) for trace in result[0]["callTrace"]) for result in results.values())
    histories = sum(len(case.history) + len(case.clone_history) for case in cases)
    print(f"OK — Lido CircuitBreaker differential: {len(cases)}/{len(cases)} rows agree; "
          f"17/17 selectors + constructor; {histories} causal history transactions; "
          f"{metrics['summary']['boundaryCount']} resource boundaries; "
          f"{traced} Solidity CALL/STATICCALL traces; {positive_artifact_checks} positive "
          f"artifact checks + {identity_corruptions} runtime corruption; "
          f"{falsifiers + projection_checks + identity_corruptions + 1} live "
          "channel/projection/identity/manifest falsifiers")
    return 0


if __name__ == "__main__":
    try:
        from ethereum.crypto.hash import keccak256 as _KECCAK
        raise SystemExit(main(sys.argv[1:]))
    except Exception as exc:
        print("REGRESSION — Lido CircuitBreaker differential: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
