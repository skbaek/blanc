#!/usr/bin/env python3
"""Goal-specific EELS Prague reproducer for Blanc LidoCircuitBreakerSpike.

The repository supplies the runtime via its committed Lean evaluator.  This
fixture models the post-constructor state by installing the two documented
initial storage words.  Its hostile-callback cases are bounded smoke evidence,
not universal semantic proofs.  It refuses dirty Blanc or EELS inputs.  This
is completion evidence for the feasibility spike, not a catalogue-owned gate.
"""

from __future__ import annotations

import hashlib
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ethereum.crypto.hash import Hash32, keccak256
from ethereum.prague.fork_types import Account, Address
from ethereum.prague.state import State, TransientStorage, get_storage, set_account, set_storage
from ethereum.prague.vm import BlockEnvironment, Message, TransactionEnvironment
from ethereum.prague.vm.interpreter import MessageCallOutput, process_message_call
from ethereum.trace import OpEnd, OpStart, set_evm_trace
from ethereum_types.bytes import Bytes, Bytes32
from ethereum_types.numeric import U256, U64, Uint


REPO = Path(__file__).resolve().parents[1]
EELS_REPO = Path(os.environ.get("EELS_ROOT", str(Path.home() / "execution-specs")))
EXPECTED_EELS_COMMIT = "4198b9c5996713b268aed602739d5aa40e277694"
EXPECTED_LENGTH = 4894
EXPECTED_SHA256 = "2e5e7efbbfded4b19cea86fa0b35d4c8e7326c22532940e74c0c00e91e0be044"
EXPECTED_KECCAK = "80a4ff98bb2bd220daf198e3608e23d849f741e014f051857a66eed3bcc33036"

CIRCUIT = "cccccccccccccccccccccccccccccccccccccccc"
CLONE = "9999999999999999999999999999999999999999"
ADMIN = "3e40d73eb977dc6a537af587d48316fee66e9c8c"
OTHER = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
PAUSER_A = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
PAUSER_B = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
PAUSER_D = "dddddddddddddddddddddddddddddddddddddddd"
TARGET_1 = "1111111111111111111111111111111111111111"
TARGET_2 = "2222222222222222222222222222222222222222"
TARGET_3 = "3333333333333333333333333333333333333333"
COINBASE = "6666666666666666666666666666666666666666"

MIN_PAUSE = 432_000
MAX_PAUSE = 5_184_000
INITIAL_PAUSE = 1_814_400
MIN_HEARTBEAT = 2_592_000
MAX_HEARTBEAT = 94_608_000
INITIAL_HEARTBEAT = 31_536_000

REGION_SHIFT = 252
CONFIG_REGION = 1
EXPIRY_REGION = 2
ASSIGNMENT_REGION = 3
INDEX_REGION = 4
COUNT_REGION = 5
ARRAY_REGION = 6


def sh(cmd: Sequence[str], cwd: Optional[Path] = None) -> str:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True,
                          check=True).stdout.strip()


def load_runtime() -> Tuple[bytes, str]:
    head = sh(["git", "rev-parse", "HEAD"], REPO)
    dirty = sh(["git", "status", "--porcelain"], REPO)
    eels_head = sh(["git", "rev-parse", "HEAD"], EELS_REPO)
    eels_dirty = sh(["git", "status", "--porcelain"], EELS_REPO)
    assert not dirty, f"Blanc worktree dirty: {dirty}"
    assert eels_head == EXPECTED_EELS_COMMIT, (eels_head, EXPECTED_EELS_COMMIT)
    assert not eels_dirty, f"EELS worktree dirty: {eels_dirty}"
    output = sh(["lake", "env", "lean", "scripts/eval-lido-circuit-breaker-spike-code.lean"], REPO)
    line = next(row for row in output.splitlines() if row.startswith("official "))
    _, declared_length, encoded = line.split()
    code = bytes.fromhex(encoded)
    assert len(code) == int(declared_length) == EXPECTED_LENGTH
    assert hashlib.sha256(code).hexdigest() == EXPECTED_SHA256
    assert bytes(keccak256(code)).hex() == EXPECTED_KECCAK
    return code, head


RUNTIME, RUNTIME_COMMIT = load_runtime()


def addr(text: str) -> Address:
    return Address(bytes.fromhex(text))


def addr_int(text: str) -> int:
    return int(text, 16)


def h256(value: int) -> bytes:
    return value.to_bytes(32, "big")


def selector(signature: str) -> bytes:
    return bytes(keccak256(signature.encode()))[:4]


def calldata(signature: str, args: Sequence[int] = ()) -> bytes:
    return selector(signature) + b"".join(h256(value) for value in args)


def tagged(region: int, payload: int = 0) -> int:
    return (region << REGION_SHIFT) | payload


PAUSE_DURATION_SLOT = tagged(CONFIG_REGION, 0)
HEARTBEAT_INTERVAL_SLOT = tagged(CONFIG_REGION, 1)
ARRAY_LENGTH_SLOT = tagged(ARRAY_REGION, 0)
LOCK_KEY = tagged(15, 0)


def expiry_slot(pauser: str) -> int:
    return tagged(EXPIRY_REGION, addr_int(pauser))


def assignment_slot(target: str) -> int:
    return tagged(ASSIGNMENT_REGION, addr_int(target))


def index_slot(target: str) -> int:
    return tagged(INDEX_REGION, addr_int(target))


def count_slot(pauser: str) -> int:
    return tagged(COUNT_REGION, addr_int(pauser))


def array_entry_slot(index: int) -> int:
    return tagged(ARRAY_REGION, index)


def target_code(result_word: int, result_size: int = 32) -> bytes:
    """STOP on pauseFor(bytes=36); return configured bytes on isPaused(bytes=4)."""
    prefix = bytes.fromhex("36600414600857005b")
    store = bytes([0x7F]) + h256(result_word) + bytes.fromhex("5f52")
    if result_size == 32:
        ret = bytes.fromhex("60205ff3")
    elif result_size == 1:
        ret = bytes.fromhex("6001601ff3")
    else:
        raise ValueError(result_size)
    return prefix + store + ret


def push_bytes(value: bytes) -> bytes:
    """Encode a nonempty PUSH payload of at most 32 bytes."""
    if not 1 <= len(value) <= 32:
        raise ValueError(len(value))
    return bytes([0x5F + len(value)]) + value


def return_word_body(result_word: int, result_size: int = 32) -> bytes:
    store = bytes([0x7F]) + h256(result_word) + bytes.fromhex("5f52")
    if result_size == 32:
        return store + bytes.fromhex("60205ff3")
    if result_size == 1:
        return store + bytes.fromhex("6001601ff3")
    raise ValueError(result_size)


def revert_data_body(payload: bytes) -> bytes:
    """MSTORE and REVERT an exact payload of at most one word."""
    if not payload:
        return bytes.fromhex("5f5ffd")
    if len(payload) > 32:
        raise ValueError(len(payload))
    return (push_bytes(payload) + bytes.fromhex("5f52") +
            push_bytes(bytes([len(payload)])) +
            push_bytes(bytes([32 - len(payload)])) + bytes([0xFD]))


def calldata_size_dispatch(pause_for_body: bytes, is_paused_body: bytes) -> bytes:
    """Dispatch calldata size four to isPaused; every other size to pauseFor."""
    view_pc = 8 + len(pause_for_body)
    if view_pc >= 2**16:
        raise ValueError(view_pc)
    prefix = bytes.fromhex("3660041461") + view_pc.to_bytes(2, "big") + bytes([0x57])
    return prefix + pause_for_body + bytes([0x5B]) + is_paused_body


def pause_for_revert_code(payload: bytes) -> bytes:
    return calldata_size_dispatch(revert_data_body(payload), return_word_body(1))


def is_paused_revert_code(payload: bytes) -> bytes:
    return calldata_size_dispatch(bytes([0x00]), revert_data_body(payload))


def recursive_pause_body(circuit: str, target: str, propagate: bool) -> bytes:
    """CALL circuit.pause(target), then either catch or bubble its outcome.

    Slot zero records `success + 1` in the caught form.  The propagating form
    writes seven before reverting, so its absence after the top-level result
    also checks child-frame rollback.
    """
    write_calldata = (
        push_bytes(selector("pause(address)")) + bytes.fromhex("5f52") +
        push_bytes(bytes.fromhex(target)) + bytes.fromhex("602052"))
    call = (bytes.fromhex("5f5f6024601c5f") +
            push_bytes(bytes.fromhex(circuit)) + bytes.fromhex("5af1"))
    if propagate:
        suffix = bytes.fromhex("5060075f553d5f5f3e3d5ffd")
    else:
        suffix = bytes.fromhex("6001015f5500")
    return write_calldata + call + suffix


def recursive_target_code(circuit: str, target: str, propagate: bool) -> bytes:
    return calldata_size_dispatch(
        recursive_pause_body(circuit, target, propagate), return_word_body(1))


ALL_ADDRESSES = [CIRCUIT, CLONE, ADMIN, OTHER, PAUSER_A, PAUSER_B, PAUSER_D,
                 TARGET_1, TARGET_2, TARGET_3, COINBASE]


@dataclass
class World:
    state: State
    target_code_by_address: Dict[str, bytes]


def make_world(target_codes: Optional[Dict[str, bytes]] = None,
               runtime_addresses: Sequence[str] = (CIRCUIT,)) -> World:
    target_codes = target_codes or {}
    state = State()
    addresses = set(ALL_ADDRESSES) | set(target_codes) | set(runtime_addresses)
    for text in addresses:
        code = RUNTIME if text in runtime_addresses else target_codes.get(text, b"")
        nonce = 1 if code else 0
        set_account(state, addr(text), Account(Uint(nonce), U256(10**24), Bytes(code)))
    for runtime_address in runtime_addresses:
        set_storage(state, addr(runtime_address), Bytes32(h256(PAUSE_DURATION_SLOT)),
                    U256(INITIAL_PAUSE))
        set_storage(state, addr(runtime_address), Bytes32(h256(HEARTBEAT_INTERVAL_SLOT)),
                    U256(INITIAL_HEARTBEAT))
    return World(state, target_codes)


def storage(world: World, key: int) -> int:
    return storage_at(world, CIRCUIT, key)


def storage_at(world: World, address: str, key: int) -> int:
    return int(get_storage(world.state, addr(address), Bytes32(h256(key))))


@dataclass
class CallTrace:
    opcode: str
    source: str
    depth: int
    target: str
    value: int
    input: bytes
    success: Optional[int] = None
    returndata: Optional[bytes] = None


@dataclass
class OpcodeTrace:
    opcode: str
    source: str
    depth: int
    pc: int
    key: int
    value: Optional[int] = None


@dataclass
class Result:
    output: MessageCallOutput
    trace: List[CallTrace]
    op_trace: List[OpcodeTrace]


def invoke(world: World, caller: str, signature: str,
           args: Sequence[int] = (), timestamp: int = 1_700_000_000,
           trace: bool = False, value: int = 0,
           raw_data: Optional[bytes] = None,
           contract: str = CIRCUIT) -> Result:
    gas = 20_000_000
    caller_addr = addr(caller)
    circuit_addr = addr(contract)
    block = BlockEnvironment(
        chain_id=U64(1), state=world.state, block_gas_limit=Uint(30_000_000),
        block_hashes=[Hash32(bytes(32))], coinbase=addr(COINBASE),
        number=Uint(20_000_000), base_fee_per_gas=Uint(0), time=U256(timestamp),
        prev_randao=Bytes32(bytes(32)), excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(bytes(32)))
    tx = TransactionEnvironment(
        origin=caller_addr, gas_price=Uint(0), gas=Uint(gas),
        access_list_addresses=set(), access_list_storage_keys=set(),
        transient_storage=TransientStorage(), blob_versioned_hashes=(),
        authorizations=(), index_in_block=None, tx_hash=None, traces=[])
    message = Message(
        block_env=block, tx_env=tx, caller=caller_addr, target=circuit_addr,
        current_target=circuit_addr, gas=Uint(gas), value=U256(value),
        data=Bytes(calldata(signature, args) if raw_data is None else raw_data),
        code_address=circuit_addr,
        code=Bytes(RUNTIME), depth=Uint(0), should_transfer_value=True,
        is_static=False, accessed_addresses={caller_addr, circuit_addr},
        accessed_storage_keys=set(), disable_precompiles=False, parent_evm=None)

    records: List[CallTrace] = []
    op_records: List[OpcodeTrace] = []
    pending: Dict[int, List[int]] = {}

    def memory_read(memory: bytearray, start: int, size: int) -> bytes:
        found = bytes(memory[start:start + size])
        return found + bytes(size - len(found))

    def tracer(evm, event, /, **_kw) -> None:
        if not isinstance(event, (OpStart, OpEnd)):
            return
        if isinstance(event, OpStart):
            opcode = event.op.name
            if opcode in ("SSTORE", "TSTORE", "TLOAD", "EXTCODESIZE"):
                key = int(evm.stack[-1])
                value_at_start = (int(evm.stack[-2])
                                  if opcode in ("SSTORE", "TSTORE") else None)
                op_records.append(OpcodeTrace(
                    opcode, bytes(evm.message.current_target).hex(),
                    int(evm.message.depth), int(evm.pc), key, value_at_start))
            if opcode not in ("CALL", "STATICCALL"):
                return
            target = int(evm.stack[-2]).to_bytes(32, "big")[-20:].hex()
            if opcode == "CALL":
                call_value = int(evm.stack[-3])
                input_offset, input_size = int(evm.stack[-4]), int(evm.stack[-5])
            else:
                call_value = 0
                input_offset, input_size = int(evm.stack[-3]), int(evm.stack[-4])
            records.append(CallTrace(opcode,
                                     bytes(evm.message.current_target).hex(),
                                     int(evm.message.depth), target, call_value,
                                     memory_read(evm.memory, input_offset, input_size)))
            pending.setdefault(id(evm), []).append(len(records) - 1)
        else:
            indices = pending.get(id(evm), [])
            if indices:
                index = indices.pop()
                records[index].success = int(evm.stack[-1])
                records[index].returndata = bytes(evm.return_data)

    old_tracer = set_evm_trace(tracer) if trace else None
    try:
        out = process_message_call(message)
    finally:
        if old_tracer is not None:
            set_evm_trace(old_tracer)
    assert not any(pending.values())
    return Result(out, records, op_records)


def assert_success(result: Result, returndata: Optional[bytes] = None) -> None:
    assert result.output.error is None, type(result.output.error).__name__
    if returndata is not None:
        assert bytes(result.output.return_data) == returndata, \
            (bytes(result.output.return_data).hex(), returndata.hex())


def assert_revert(result: Result, returndata: bytes) -> None:
    assert type(result.output.error).__name__ == "Revert", type(result.output.error).__name__
    assert bytes(result.output.return_data) == returndata, \
        (bytes(result.output.return_data).hex(), returndata.hex())


def word_result(world: World, caller: str, signature: str,
                args: Sequence[int] = (), timestamp: int = 1_700_000_000) -> int:
    result = invoke(world, caller, signature, args, timestamp)
    assert_success(result)
    raw = bytes(result.output.return_data)
    assert len(raw) == 32, (signature, raw.hex())
    return int.from_bytes(raw, "big")


def array_result(world: World, expected: Sequence[str]) -> None:
    result = invoke(world, OTHER, "getPausables()")
    expected_raw = h256(32) + h256(len(expected)) + b"".join(h256(addr_int(x)) for x in expected)
    assert_success(result, expected_raw)


def register(world: World, target: str, pauser: str, timestamp: int,
             contract: str = CIRCUIT) -> Result:
    result = invoke(world, ADMIN, "registerPauser(address,address)",
                    [addr_int(target), addr_int(pauser)], timestamp,
                    contract=contract)
    assert_success(result, b"")
    return result


def check_registry(world: World, entries: Sequence[Tuple[str, str]],
                   absent_targets: Iterable[str] = ()) -> None:
    assert storage(world, ARRAY_LENGTH_SLOT) == len(entries)
    array_result(world, [target for target, _ in entries])
    counts: Dict[str, int] = {}
    for i, (target, pauser) in enumerate(entries, 1):
        counts[pauser] = counts.get(pauser, 0) + 1
        assert storage(world, array_entry_slot(i)) == addr_int(target)
        assert storage(world, assignment_slot(target)) == addr_int(pauser)
        assert storage(world, index_slot(target)) == i
        assert word_result(world, OTHER, "getPauser(address)", [addr_int(target)]) == addr_int(pauser)
    for target in absent_targets:
        assert storage(world, assignment_slot(target)) == 0
        assert storage(world, index_slot(target)) == 0
        assert word_result(world, OTHER, "getPauser(address)", [addr_int(target)]) == 0
    for pauser in (PAUSER_A, PAUSER_B, PAUSER_D):
        expected = counts.get(pauser, 0)
        assert storage(world, count_slot(pauser)) == expected
        assert word_result(world, OTHER, "getPausableCount(address)", [addr_int(pauser)]) == expected


def expected_log(signature: str, indexed: Sequence[int], data_words: Sequence[int]) -> Tuple[List[bytes], bytes]:
    return ([bytes(keccak256(signature.encode()))] + [h256(value) for value in indexed],
            b"".join(h256(value) for value in data_words))


def assert_log(log, signature: str, indexed: Sequence[int], data_words: Sequence[int]) -> None:
    topics, data = expected_log(signature, indexed, data_words)
    assert bytes(log.address).hex() == CIRCUIT
    assert [bytes(topic) for topic in log.topics] == topics
    assert bytes(log.data) == data


CASES: List[str] = []


def passed(name: str) -> None:
    CASES.append(name)
    print(f"PASS {name}")


def test_view_defaults() -> None:
    world = make_world()
    expected = {
        "ADMIN()": addr_int(ADMIN),
        "MIN_PAUSE_DURATION()": MIN_PAUSE,
        "MAX_PAUSE_DURATION()": MAX_PAUSE,
        "MIN_HEARTBEAT_INTERVAL()": MIN_HEARTBEAT,
        "MAX_HEARTBEAT_INTERVAL()": MAX_HEARTBEAT,
        "pauseDuration()": INITIAL_PAUSE,
        "heartbeatInterval()": INITIAL_HEARTBEAT,
    }
    for signature, value in expected.items():
        assert word_result(world, OTHER, signature) == value
    for signature in ("getPauser(address)", "getPausableCount(address)",
                      "heartbeatExpiry(address)", "isPauserLive(address)"):
        assert word_result(world, OTHER, signature, [addr_int(TARGET_1)]) == 0
    array_result(world, [])
    passed("view-defaults-and-empty-array-ABI")


def test_registry_mutations() -> None:
    world = make_world()
    t1, t2, t3 = 1_700_000_000, 1_700_001_000, 1_700_002_000
    fresh_result = register(world, TARGET_1, PAUSER_A, t1)
    assert len(fresh_result.output.logs) == 2
    assert_log(fresh_result.output.logs[0], "PauserSet(address,address,address)",
               [addr_int(TARGET_1), 0, addr_int(PAUSER_A)], [])
    assert_log(fresh_result.output.logs[1], "HeartbeatUpdated(address,uint256)",
               [addr_int(PAUSER_A)], [t1 + INITIAL_HEARTBEAT])
    check_registry(world, [(TARGET_1, PAUSER_A)])
    assert storage(world, expiry_slot(PAUSER_A)) == t1 + INITIAL_HEARTBEAT
    array_result(world, [TARGET_1])
    passed("fresh-register-and-one-element-array-ABI")

    register(world, TARGET_1, PAUSER_A, t2)
    check_registry(world, [(TARGET_1, PAUSER_A)])
    assert storage(world, expiry_slot(PAUSER_A)) == t2 + INITIAL_HEARTBEAT
    passed("same-pauser-replace-preserves-count-and-refreshes-expiry")

    replacement = make_world()
    register(replacement, TARGET_1, PAUSER_A, t1)
    replacement_result = register(replacement, TARGET_1, PAUSER_B, t2)
    check_registry(replacement, [(TARGET_1, PAUSER_B)])
    assert storage(replacement, expiry_slot(PAUSER_A)) == 0
    assert storage(replacement, expiry_slot(PAUSER_B)) == t2 + INITIAL_HEARTBEAT
    assert len(replacement_result.output.logs) == 3
    assert_log(replacement_result.output.logs[0],
               "PauserSet(address,address,address)",
               [addr_int(TARGET_1), addr_int(PAUSER_A), addr_int(PAUSER_B)], [])
    assert_log(replacement_result.output.logs[1],
               "HeartbeatUpdated(address,uint256)", [addr_int(PAUSER_A)], [0])
    assert_log(replacement_result.output.logs[2],
               "HeartbeatUpdated(address,uint256)", [addr_int(PAUSER_B)],
               [t2 + INITIAL_HEARTBEAT])
    passed("distinct-nonzero-pauser-replacement-updates-counts-expiries-and-events")

    zero_target = make_world()
    zero_result = invoke(
        zero_target, ADMIN, "registerPauser(address,address)",
        [0, addr_int(PAUSER_A)], t1, trace=True)
    assert_revert(zero_result, selector("PausableZero()"))
    assert zero_result.output.logs == ()
    assert not any(row.opcode == "SSTORE" for row in zero_result.op_trace)
    check_registry(zero_target, [])
    assert storage(zero_target, expiry_slot(PAUSER_A)) == 0
    passed("zero-pausable-register-reverts-before-persistent-write")

    register(world, TARGET_1, "0000000000000000000000000000000000000000", t3)
    check_registry(world, [], [TARGET_1])
    assert storage(world, array_entry_slot(1)) == 0
    assert storage(world, expiry_slot(PAUSER_A)) == 0
    register(world, TARGET_1, "0000000000000000000000000000000000000000", t3 + 1)
    check_registry(world, [], [TARGET_1])
    assert storage(world, array_entry_slot(1)) == 0
    passed("idempotent-unregister-present-then-absent")

    removal_cases = [
        ("first", TARGET_1, [(TARGET_3, PAUSER_D), (TARGET_2, PAUSER_B)]),
        ("last", TARGET_3, [(TARGET_1, PAUSER_A), (TARGET_2, PAUSER_B)]),
        ("middle", TARGET_2, [(TARGET_1, PAUSER_A), (TARGET_3, PAUSER_D)]),
    ]
    assignments = [(TARGET_1, PAUSER_A), (TARGET_2, PAUSER_B), (TARGET_3, PAUSER_D)]
    for label, removed, expected in removal_cases:
        candidate = make_world()
        for i, (target, pauser) in enumerate(assignments):
            register(candidate, target, pauser, t1 + i)
        register(candidate, removed, "0000000000000000000000000000000000000000", t2)
        check_registry(candidate, expected, [removed])
        assert storage(candidate, array_entry_slot(3)) == 0
        removed_pauser = dict(assignments)[removed]
        assert storage(candidate, expiry_slot(removed_pauser)) == 0
        passed(f"swap-pop-{label}-removal-and-reverse-index")

    many = make_world()
    for i, (target, pauser) in enumerate(assignments):
        register(many, target, pauser, t1 + i)
    check_registry(many, assignments)
    array_result(many, [TARGET_1, TARGET_2, TARGET_3])
    passed("many-element-array-ABI-preserves-order")

    shared = make_world()
    register(shared, TARGET_1, PAUSER_A, t1)
    register(shared, TARGET_2, PAUSER_A, t2)
    expiry = storage(shared, expiry_slot(PAUSER_A))
    check_registry(shared, [(TARGET_1, PAUSER_A), (TARGET_2, PAUSER_A)])
    register(shared, TARGET_1, "0000000000000000000000000000000000000000", t3)
    check_registry(shared, [(TARGET_2, PAUSER_A)], [TARGET_1])
    assert storage(shared, expiry_slot(PAUSER_A)) == expiry
    register(shared, TARGET_2, "0000000000000000000000000000000000000000", t3 + 1)
    check_registry(shared, [], [TARGET_1, TARGET_2])
    assert storage(shared, expiry_slot(PAUSER_A)) == 0
    passed("shared-pauser-count-keeps-expiry-until-last-unregister")

    long_world = make_world()
    long_targets = [f"{0x1000 + i:040x}" for i in range(64)]
    for i, target in enumerate(long_targets):
        register(long_world, target, PAUSER_A, t1 + i)
    array_result(long_world, long_targets)
    assert storage(long_world, ARRAY_LENGTH_SLOT) == len(long_targets)
    assert storage(long_world, count_slot(PAUSER_A)) == len(long_targets)
    assert storage(long_world, index_slot(long_targets[-1])) == len(long_targets)
    passed("64-element-tail-enumeration-exact-ABI-and-order")


def test_strict_calldata_and_checked_addition() -> None:
    short = make_world()
    one_arg_only = selector("registerPauser(address,address)") + h256(addr_int(TARGET_1))
    assert_revert(invoke(short, ADMIN, "registerPauser(address,address)",
                         raw_data=one_arg_only), b"")
    check_registry(short, [], [TARGET_1])
    passed("selector-matched-short-two-arg-register-empty-reverts")

    overflow = make_world()
    timestamp = 2**256 - INITIAL_HEARTBEAT + 1
    panic_0x11 = selector("Panic(uint256)") + h256(0x11)
    assert_revert(invoke(overflow, ADMIN, "registerPauser(address,address)",
                         [addr_int(TARGET_1), addr_int(PAUSER_A)], timestamp),
                  panic_0x11)
    check_registry(overflow, [], [TARGET_1])
    assert storage(overflow, expiry_slot(PAUSER_A)) == 0
    passed("timestamp-plus-heartbeat-overflow-Panic-0x11-and-full-rollback")


def test_admin_config() -> None:
    world = make_world()
    initial = storage(world, PAUSE_DURATION_SLOT)
    assert_revert(invoke(world, OTHER, "setPauseDuration(uint256)", [MIN_PAUSE]),
                  selector("SenderNotAdmin()"))
    assert storage(world, PAUSE_DURATION_SLOT) == initial
    assert_revert(invoke(world, ADMIN, "setPauseDuration(uint256)", [MIN_PAUSE - 1]),
                  selector("PauseDurationBelowMin()"))
    assert_revert(invoke(world, ADMIN, "setPauseDuration(uint256)", [MAX_PAUSE + 1]),
                  selector("PauseDurationAboveMax()"))
    assert_success(invoke(world, ADMIN, "setPauseDuration(uint256)", [MIN_PAUSE]), b"")
    assert word_result(world, OTHER, "pauseDuration()") == MIN_PAUSE
    assert_success(invoke(world, ADMIN, "setPauseDuration(uint256)", [MAX_PAUSE]), b"")
    assert word_result(world, OTHER, "pauseDuration()") == MAX_PAUSE
    passed("pause-duration-admin-auth-range-and-inclusive-boundaries")

    initial = storage(world, HEARTBEAT_INTERVAL_SLOT)
    assert_revert(invoke(world, OTHER, "setHeartbeatInterval(uint256)", [MIN_HEARTBEAT]),
                  selector("SenderNotAdmin()"))
    assert storage(world, HEARTBEAT_INTERVAL_SLOT) == initial
    assert_revert(invoke(world, ADMIN, "setHeartbeatInterval(uint256)", [MIN_HEARTBEAT - 1]),
                  selector("HeartbeatIntervalBelowMin()"))
    assert_revert(invoke(world, ADMIN, "setHeartbeatInterval(uint256)", [MAX_HEARTBEAT + 1]),
                  selector("HeartbeatIntervalAboveMax()"))
    assert_success(invoke(world, ADMIN, "setHeartbeatInterval(uint256)", [MIN_HEARTBEAT]), b"")
    assert word_result(world, OTHER, "heartbeatInterval()") == MIN_HEARTBEAT
    assert_success(invoke(world, ADMIN, "setHeartbeatInterval(uint256)", [MAX_HEARTBEAT]), b"")
    assert word_result(world, OTHER, "heartbeatInterval()") == MAX_HEARTBEAT
    passed("heartbeat-interval-admin-auth-range-and-inclusive-boundaries")


def test_heartbeat_strictness() -> None:
    base = 1_700_000_000
    equality = make_world()
    register(equality, TARGET_1, PAUSER_A, base)
    expiry = base + INITIAL_HEARTBEAT
    assert word_result(equality, OTHER, "isPauserLive(address)", [addr_int(PAUSER_A)], expiry - 1) == 1
    assert word_result(equality, OTHER, "isPauserLive(address)", [addr_int(PAUSER_A)], expiry) == 0
    assert_revert(invoke(equality, PAUSER_A, "heartbeat()", timestamp=expiry),
                  selector("HeartbeatExpired()"))
    assert storage(equality, expiry_slot(PAUSER_A)) == expiry
    passed("heartbeat-expiry-equality-is-expired-and-rolls-back")

    before = make_world()
    register(before, TARGET_1, PAUSER_A, base)
    assert_success(invoke(before, PAUSER_A, "heartbeat()", timestamp=expiry - 1), b"")
    assert storage(before, expiry_slot(PAUSER_A)) == expiry - 1 + INITIAL_HEARTBEAT
    assert_revert(invoke(before, OTHER, "heartbeat()", timestamp=expiry - 1),
                  selector("SenderNotPauser()"))
    passed("heartbeat-before-expiry-refreshes-and-non-pauser-reverts")


def run_pause_variant(name: str, word: int, size: int,
                      expected_error: Optional[bytes]) -> None:
    base = 1_700_000_000
    world = make_world({TARGET_1: target_code(word, size)})
    register(world, TARGET_1, PAUSER_A, base)
    expiry_before = storage(world, expiry_slot(PAUSER_A))
    result = invoke(world, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 1, trace=True)
    if expected_error is None:
        assert_success(result, b"")
    else:
        assert_revert(result, expected_error)
    assert len(result.trace) == 2, [(r.opcode, r.input.hex()) for r in result.trace]
    call, static = result.trace
    assert (call.opcode, call.target, call.value, call.success) == \
           ("CALL", TARGET_1, 0, 1)
    assert call.input == selector("pauseFor(uint256)") + h256(INITIAL_PAUSE)
    assert call.returndata == b""
    assert (static.opcode, static.target, static.value, static.success) == \
           ("STATICCALL", TARGET_1, 0, 1)
    assert static.input == selector("isPaused()")
    expected_target_return = (h256(word) if size == 32 else h256(word)[31:])
    assert static.returndata == expected_target_return
    if expected_error is None:
        check_registry(world, [], [TARGET_1])
        assert storage(world, array_entry_slot(1)) == 0
        assert storage(world, expiry_slot(PAUSER_A)) == 0
        assert len(result.output.logs) == 3
        assert_log(result.output.logs[0], "PauserSet(address,address,address)",
                   [addr_int(TARGET_1), addr_int(PAUSER_A), 0], [])
        assert_log(result.output.logs[1], "PauseTriggered(address,address,uint256)",
                   [addr_int(TARGET_1), addr_int(PAUSER_A)], [INITIAL_PAUSE])
        assert_log(result.output.logs[2], "HeartbeatUpdated(address,uint256)",
                   [addr_int(PAUSER_A)], [0])
    else:
        assert result.output.logs == ()
        check_registry(world, [(TARGET_1, PAUSER_A)])
        assert storage(world, expiry_slot(PAUSER_A)) == expiry_before
    passed(name)


def test_pause_results() -> None:
    run_pause_variant("pause-canonical-false-reverts-PauseFailed-and-restores-registry",
                      0, 32, selector("PauseFailed()"))
    run_pause_variant("pause-canonical-true-succeeds-with-exact-call-calldata",
                      1, 32, None)
    run_pause_variant("pause-short-isPaused-return-empty-reverts-and-restores-registry",
                      1, 1, b"")
    run_pause_variant("pause-noncanonical-isPaused-word-empty-reverts-and-restores-registry",
                      2, 32, b"")

    base = 1_700_000_000
    remaining = make_world({TARGET_1: target_code(1, 32)})
    register(remaining, TARGET_1, PAUSER_A, base)
    register(remaining, TARGET_2, PAUSER_A, base + 1)
    pause_time = base + 2
    result = invoke(remaining, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=pause_time)
    assert_success(result, b"")
    check_registry(remaining, [(TARGET_2, PAUSER_A)], [TARGET_1])
    assert storage(remaining, expiry_slot(PAUSER_A)) == pause_time + INITIAL_HEARTBEAT
    assert_log(result.output.logs[-1], "HeartbeatUpdated(address,uint256)",
               [addr_int(PAUSER_A)], [pause_time + INITIAL_HEARTBEAT])
    passed("pause-with-remaining-assignment-refreshes-expiry")


def test_s4_callback_separation() -> None:
    """Bounded hostile-callback smoke cases; these are not universal proofs."""
    base = 1_700_000_000

    eoa = make_world()
    register(eoa, TARGET_1, PAUSER_A, base)
    expiry_before = storage(eoa, expiry_slot(PAUSER_A))
    result = invoke(eoa, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 1, trace=True)
    assert_revert(result, b"")
    assert result.output.logs == ()
    assert result.trace == []
    assert any(row.opcode == "EXTCODESIZE" and row.source == CIRCUIT and
               row.depth == 0 and row.key == addr_int(TARGET_1)
               for row in result.op_trace)
    assert any(row.opcode == "SSTORE" and row.source == CIRCUIT and row.depth == 0
               for row in result.op_trace)
    check_registry(eoa, [(TARGET_1, PAUSER_A)])
    assert storage(eoa, expiry_slot(PAUSER_A)) == expiry_before
    passed("EOA-pausable-empty-reverts-before-child-CALL-and-restores-registry")

    pause_revert_data = bytes.fromhex("feedfacec0decafe")
    pause_revert = make_world({TARGET_1: pause_for_revert_code(pause_revert_data)})
    register(pause_revert, TARGET_1, PAUSER_A, base)
    expiry_before = storage(pause_revert, expiry_slot(PAUSER_A))
    result = invoke(pause_revert, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 1, trace=True)
    assert_revert(result, pause_revert_data)
    assert result.output.logs == ()
    assert len(result.trace) == 1
    outbound = result.trace[0]
    assert (outbound.opcode, outbound.source, outbound.depth, outbound.target,
            outbound.success, outbound.returndata) == \
           ("CALL", CIRCUIT, 0, TARGET_1, 0, pause_revert_data)
    assert outbound.input == selector("pauseFor(uint256)") + h256(INITIAL_PAUSE)
    assert any(row.opcode == "SSTORE" and row.source == CIRCUIT and row.depth == 0
               for row in result.op_trace)
    check_registry(pause_revert, [(TARGET_1, PAUSER_A)])
    assert storage(pause_revert, expiry_slot(PAUSER_A)) == expiry_before
    passed("pauseFor-child-revert-bubbles-exactly-and-restores-outer-registry")

    static_revert_data = bytes.fromhex("deadbeef")
    static_revert = make_world({TARGET_1: is_paused_revert_code(static_revert_data)})
    register(static_revert, TARGET_1, PAUSER_A, base)
    expiry_before = storage(static_revert, expiry_slot(PAUSER_A))
    result = invoke(static_revert, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 1, trace=True)
    assert_revert(result, static_revert_data)
    assert result.output.logs == ()
    assert len(result.trace) == 2
    call, static = result.trace
    assert (call.opcode, call.source, call.target, call.success, call.returndata) == \
           ("CALL", CIRCUIT, TARGET_1, 1, b"")
    assert (static.opcode, static.source, static.target, static.success,
            static.returndata) == \
           ("STATICCALL", CIRCUIT, TARGET_1, 0, static_revert_data)
    assert any(row.opcode == "SSTORE" and row.source == CIRCUIT and row.depth == 0
               for row in result.op_trace)
    check_registry(static_revert, [(TARGET_1, PAUSER_A)])
    assert storage(static_revert, expiry_slot(PAUSER_A)) == expiry_before
    passed("isPaused-child-revert-bubbles-exactly-and-restores-outer-registry")

    reentrant_error = selector("ReentrantCall()")
    same_target = make_world({
        TARGET_1: recursive_target_code(CIRCUIT, TARGET_1, propagate=False),
    })
    register(same_target, TARGET_1, PAUSER_A, base)
    result = invoke(same_target, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 1, trace=True)
    assert_success(result, b"")
    assert len(result.trace) == 3
    outer_call, recursive_call, outer_static = result.trace
    assert (outer_call.opcode, outer_call.source, outer_call.depth,
            outer_call.target, outer_call.success) == \
           ("CALL", CIRCUIT, 0, TARGET_1, 1)
    assert (recursive_call.opcode, recursive_call.source, recursive_call.depth,
            recursive_call.target, recursive_call.success,
            recursive_call.returndata) == \
           ("CALL", TARGET_1, 1, CIRCUIT, 0, reentrant_error)
    assert recursive_call.input == selector("pause(address)") + h256(addr_int(TARGET_1))
    assert (outer_static.opcode, outer_static.source, outer_static.target,
            outer_static.success) == ("STATICCALL", CIRCUIT, TARGET_1, 1)
    assert not any(row.source == CIRCUIT and row.depth == 2
                   for row in result.trace)
    inner_ops = [row for row in result.op_trace
                 if row.source == CIRCUIT and row.depth == 2]
    assert [(row.opcode, row.key, row.value) for row in inner_ops] == \
           [("TLOAD", LOCK_KEY, None)]
    check_registry(same_target, [], [TARGET_1])
    assert storage_at(same_target, TARGET_1, 0) == 1
    passed("same-pausable-target-recursion-caught-at-transient-lock")

    caught = make_world({
        TARGET_1: recursive_target_code(CIRCUIT, TARGET_2, propagate=False),
        TARGET_2: target_code(1),
    })
    register(caught, TARGET_1, PAUSER_A, base)
    register(caught, TARGET_2, TARGET_1, base + 1)
    target_two_expiry = storage(caught, expiry_slot(TARGET_1))
    result = invoke(caught, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 2, trace=True)
    assert_success(result, b"")
    assert len(result.trace) == 3
    outer_call, recursive_call, outer_static = result.trace
    assert (outer_call.opcode, outer_call.source, outer_call.depth,
            outer_call.target, outer_call.success) == \
           ("CALL", CIRCUIT, 0, TARGET_1, 1)
    assert (recursive_call.opcode, recursive_call.source, recursive_call.depth,
            recursive_call.target, recursive_call.success,
            recursive_call.returndata) == \
           ("CALL", TARGET_1, 1, CIRCUIT, 0, reentrant_error)
    assert recursive_call.input == selector("pause(address)") + h256(addr_int(TARGET_2))
    assert (outer_static.opcode, outer_static.source, outer_static.target,
            outer_static.success) == ("STATICCALL", CIRCUIT, TARGET_1, 1)
    assert not any(row.source == CIRCUIT and row.depth == 2
                   for row in result.trace)
    inner_ops = [row for row in result.op_trace
                 if row.source == CIRCUIT and row.depth == 2]
    assert [(row.opcode, row.key, row.value) for row in inner_ops] == \
           [("TLOAD", LOCK_KEY, None)]
    assert any(row.opcode == "SSTORE" and row.source == TARGET_1 and
               row.depth == 1 and row.key == 0 and row.value == 1
               for row in result.op_trace)
    check_registry(caught, [(TARGET_2, TARGET_1)], [TARGET_1])
    assert storage(caught, count_slot(TARGET_1)) == 1
    assert storage(caught, expiry_slot(TARGET_1)) == target_two_expiry
    assert storage_at(caught, TARGET_1, 0) == 1
    passed("same-instance-different-target-recursion-caught-before-inner-write-or-call")

    propagated = make_world({
        TARGET_1: recursive_target_code(CIRCUIT, TARGET_2, propagate=True),
        TARGET_2: target_code(1),
    })
    register(propagated, TARGET_1, PAUSER_A, base)
    register(propagated, TARGET_2, TARGET_1, base + 1)
    pauser_a_expiry = storage(propagated, expiry_slot(PAUSER_A))
    target_one_expiry = storage(propagated, expiry_slot(TARGET_1))
    result = invoke(propagated, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 2, trace=True)
    assert_revert(result, reentrant_error)
    assert result.output.logs == ()
    assert len(result.trace) == 2
    outer_call, recursive_call = result.trace
    assert (outer_call.opcode, outer_call.source, outer_call.target,
            outer_call.success, outer_call.returndata) == \
           ("CALL", CIRCUIT, TARGET_1, 0, reentrant_error)
    assert (recursive_call.opcode, recursive_call.source, recursive_call.target,
            recursive_call.success, recursive_call.returndata) == \
           ("CALL", TARGET_1, CIRCUIT, 0, reentrant_error)
    inner_ops = [row for row in result.op_trace
                 if row.source == CIRCUIT and row.depth == 2]
    assert [(row.opcode, row.key, row.value) for row in inner_ops] == \
           [("TLOAD", LOCK_KEY, None)]
    assert any(row.opcode == "SSTORE" and row.source == CIRCUIT and row.depth == 0
               for row in result.op_trace)
    assert any(row.opcode == "SSTORE" and row.source == TARGET_1 and
               row.depth == 1 and row.key == 0 and row.value == 7
               for row in result.op_trace)
    check_registry(propagated,
                   [(TARGET_1, PAUSER_A), (TARGET_2, TARGET_1)])
    assert storage(propagated, expiry_slot(PAUSER_A)) == pauser_a_expiry
    assert storage(propagated, expiry_slot(TARGET_1)) == target_one_expiry
    assert storage_at(propagated, TARGET_1, 0) == 0
    passed("propagated-reentrant-child-failure-rolls-back-child-and-outer-writes")

    clone = make_world({
        TARGET_1: recursive_target_code(CLONE, TARGET_2, propagate=False),
        TARGET_2: target_code(1),
    }, runtime_addresses=(CIRCUIT, CLONE))
    register(clone, TARGET_1, PAUSER_A, base, contract=CIRCUIT)
    register(clone, TARGET_2, TARGET_1, base + 1, contract=CLONE)
    result = invoke(clone, PAUSER_A, "pause(address)", [addr_int(TARGET_1)],
                    timestamp=base + 2, trace=True, contract=CIRCUIT)
    assert_success(result, b"")
    assert len(result.trace) == 5
    expected_edges = [
        ("CALL", CIRCUIT, TARGET_1, 1),
        ("CALL", TARGET_1, CLONE, 1),
        ("CALL", CLONE, TARGET_2, 1),
        ("STATICCALL", CLONE, TARGET_2, 1),
        ("STATICCALL", CIRCUIT, TARGET_1, 1),
    ]
    assert [(row.opcode, row.source, row.target, row.success)
            for row in result.trace] == expected_edges
    clone_inner_ops = [row for row in result.op_trace
                       if row.source == CLONE and row.depth == 2]
    assert any(row.opcode == "TLOAD" and row.key == LOCK_KEY
               for row in clone_inner_ops)
    assert any(row.opcode == "TSTORE" and row.key == LOCK_KEY and row.value == 1
               for row in clone_inner_ops)
    assert any(row.opcode == "SSTORE" for row in clone_inner_ops)
    assert any(row.opcode == "TSTORE" and row.key == LOCK_KEY and row.value == 0
               for row in clone_inner_ops)
    check_registry(clone, [], [TARGET_1])
    assert storage_at(clone, CLONE, ARRAY_LENGTH_SLOT) == 0
    assert storage_at(clone, CLONE, assignment_slot(TARGET_2)) == 0
    assert storage_at(clone, CLONE, index_slot(TARGET_2)) == 0
    assert storage_at(clone, CLONE, array_entry_slot(1)) == 0
    assert storage_at(clone, CLONE, count_slot(TARGET_1)) == 0
    assert storage_at(clone, CLONE, expiry_slot(TARGET_1)) == 0
    assert storage_at(clone, TARGET_1, 0) == 2
    passed("clone-address-has-distinct-transient-namespace-and-can-recurse")


def main() -> None:
    test_view_defaults()
    test_registry_mutations()
    test_strict_calldata_and_checked_addition()
    test_admin_config()
    test_heartbeat_strictness()
    test_pause_results()
    test_s4_callback_separation()
    head_after = sh(["git", "rev-parse", "HEAD"], REPO)
    dirty_after = sh(["git", "status", "--porcelain"], REPO)
    assert head_after == RUNTIME_COMMIT and not dirty_after
    print(f"SUMMARY {len(CASES)} cases passed")
    print(f"RUNTIME commit={RUNTIME_COMMIT} bytes={len(RUNTIME)} sha256={EXPECTED_SHA256} keccak256={EXPECTED_KECCAK}")
    print(f"EELS commit={EXPECTED_EELS_COMMIT} fork=Prague")


if __name__ == "__main__":
    main()
