#!/usr/bin/env python3
"""Shared pinned-EELS mechanics for manifest-backed differentials.

This module owns only generic execution mechanics: clean-pin verification,
Prague block/transaction environments, direct CREATE/message execution,
call/write tracing, log normalization, and fixture-code installation.  Contract
ABI, storage projections, mocks, semantic channels, and deviation policy stay
with each contract's differential generator.
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import Callable, Dict, List, Mapping, Sequence

import eels_semantic_closure


def verify_eels_pin(root: Path, expected_pin: str,
                    fail: Callable[[str], object]) -> None:
    head = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(root), "status", "--porcelain"], text=True).strip()
    if head != expected_pin or dirty:
        fail(f"pinned EELS must be clean at {expected_pin}; "
             f"found {head}, dirty={bool(dirty)}")

    # The commit pins the specification's source; this pins what that source
    # imports.  Both must hold before an oracle comparison means anything.
    eels_semantic_closure.assert_prague_environment(
        fail, checkout_root=root
    )


def environments(state, timestamp: int, gas: int, *,
                 address_bytes: Callable[[str], bytes], coinbase: str,
                 origin: str):
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, TransactionEnvironment
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    block = BlockEnvironment(
        chain_id=U64(1), state=state, block_gas_limit=Uint(30_000_000),
        block_hashes=[Hash32(bytes(32))],
        coinbase=Address(address_bytes(coinbase)), number=Uint(20_000_000),
        base_fee_per_gas=Uint(0), time=U256(timestamp),
        prev_randao=Bytes32(bytes(32)), excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(bytes(32)))
    tx = TransactionEnvironment(
        origin=Address(address_bytes(origin)), gas_price=Uint(0), gas=Uint(gas),
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


def execute_create(state, target: str, initcode: bytes, value: int, *,
                   address_bytes: Callable[[str], bytes], coinbase: str,
                   create_caller: str, timestamp: int = 1_700_000_000,
                   gas: int = 20_000_000):
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import get_account, set_account
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_message_call
    from ethereum_types.bytes import Bytes, Bytes0
    from ethereum_types.numeric import U256, Uint

    caller = Address(address_bytes(create_caller))
    target_address = Address(address_bytes(target))
    set_account(state, caller, Account(Uint(0), U256(10**24), Bytes(b"")))
    block, tx = environments(
        state, timestamp, gas, address_bytes=address_bytes,
        coinbase=coinbase, origin=create_caller)
    message = Message(
        block_env=block, tx_env=tx, caller=caller, target=Bytes0(b""),
        current_target=target_address, gas=Uint(gas), value=U256(value),
        data=Bytes(b""), code_address=None, code=Bytes(initcode), depth=Uint(0),
        should_transfer_value=True, is_static=False,
        accessed_addresses={caller, target_address}, accessed_storage_keys=set(),
        disable_precompiles=False, parent_evm=None)
    output = process_message_call(message)
    return output, bytes(get_account(state, target_address).code), \
        gas - int(output.gas_left)


def execute_tx(state, txspec, *, address_bytes: Callable[[str], bytes],
               coinbase: str, default_origin: str,
               fail: Callable[[str], object]):
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
        set_account(state, caller, Account(
            caller_account.nonce, U256(10**24), caller_account.code))
    block, txenv = environments(
        state, txspec.timestamp, txspec.gas, address_bytes=address_bytes,
        coinbase=coinbase, origin=default_origin)
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
            fail(f"refusing traced input of {size} bytes")
        raw = bytes(memory[start:start + size])
        return raw + bytes(size - len(raw))

    def tracer(evm, event, /, **_kw) -> None:
        if isinstance(event, OpStart) and event.op.name == "SSTORE":
            if len(evm.stack) < 2:
                fail("traced SSTORE stack underflow")
            writes.append({
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "key": hex(int(evm.stack[-1])), "value": hex(int(evm.stack[-2])),
            })
            return
        if isinstance(event, OpStart) and event.op.name in ("CALL", "STATICCALL"):
            opcode = event.op.name
            need = 7 if opcode == "CALL" else 6
            if len(evm.stack) < need:
                fail(f"traced {opcode} stack underflow")
            target_word = int(evm.stack[-2])
            called = target_word.to_bytes(32, "big")[-20:]
            if opcode == "CALL":
                value = int(evm.stack[-3])
                offset = int(evm.stack[-4])
                size = int(evm.stack[-5])
                output_offset = int(evm.stack[-6])
                output_size = int(evm.stack[-7])
            else:
                value = 0
                offset = int(evm.stack[-3])
                size = int(evm.stack[-4])
                output_offset = int(evm.stack[-5])
                output_size = int(evm.stack[-6])
            resource_ops.append({
                "opcode": opcode,
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "outputOffset": output_offset, "outputSize": output_size,
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
                fail("traced RETURNDATACOPY stack underflow")
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
        fail("call trace contains unmatched opcode start")
    return output, traces, txspec.gas - int(output.gas_left), writes, resource_ops


def install_code(state, mapping: Mapping[str, bytes], *,
                 address_bytes: Callable[[str], bytes]) -> None:
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import get_account, set_account
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import Uint

    for address, code in mapping.items():
        account_address = Address(address_bytes(address))
        old = get_account(state, account_address)
        set_account(state, account_address, Account(
            Uint(max(1, int(old.nonce))), old.balance, Bytes(code)))
