#!/usr/bin/env python3
"""Executable fresh-deployment evidence for Blanc WETH10.

The fixture runs the generic Blanc initcode as a Prague creation message in
two valid identity worlds.  It independently derives the EIP-712 separator,
checks the patched spans and exact deposited runtime, checks the constructor
boundary, and executes bounded mutations to prove those observations are live.
No network access or fixture rewrite occurs.
"""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
MAINNET = "f4bb2e28688e89fcce3c0580d37d36a7672e8a9f"
SYNTHETIC = "0000000000000000000000000000000000001000"
CALLER = "1111111111111111111111111111111111111111"
COINBASE = "6666666666666666666666666666666666666666"
CHAIN_OFFSETS = (372, 691, 2875)
DOMAIN_OFFSETS = (536, 3039)


def parse_artifacts(path: Path) -> Tuple[bytes, int, Dict[str, bytes]]:
    initcode = None
    prefix_length = None
    runtimes: Dict[str, bytes] = {}
    for raw in path.read_text().splitlines():
        parts = raw.split()
        if not parts:
            continue
        if parts[0] == "prefix-length" and len(parts) == 2:
            prefix_length = int(parts[1])
        elif parts[0] in ("initcode", "mainnet-runtime", "synthetic-runtime") \
                and len(parts) == 3:
            code = bytes.fromhex(parts[2])
            if len(code) != int(parts[1]):
                raise RuntimeError(f"{parts[0]}: declared length mismatch")
            if parts[0] == "initcode":
                initcode = code
            else:
                runtimes[parts[0]] = code
        else:
            raise RuntimeError(f"unrecognized evaluator output: {raw!r}")
    if initcode is None or prefix_length is None or set(runtimes) != {
            "mainnet-runtime", "synthetic-runtime"}:
        raise RuntimeError("deployment evaluator output is incomplete")
    runtime_lengths = {len(code) for code in runtimes.values()}
    if len(runtime_lengths) != 1:
        raise RuntimeError("deployment runtime family changed byte length")
    if not 0 <= prefix_length <= len(initcode) or \
            len(initcode) - prefix_length != next(iter(runtime_lengths)):
        raise RuntimeError("initcode runtime-tail length mismatch")
    return initcode, prefix_length, runtimes


def verify_eels_pin(root: Path) -> None:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True,
        capture_output=True, check=True).stdout.strip()
    dirty = subprocess.run(
        ["git", "status", "--porcelain"], cwd=root, text=True,
        capture_output=True, check=True).stdout
    if head != EELS_PIN or dirty:
        raise RuntimeError(
            f"pinned EELS checkout must be clean at {EELS_PIN}; "
            f"found {head} dirty={bool(dirty)}")


def opcode_positions(code: bytes) -> List[Tuple[int, int]]:
    out = []
    pc = 0
    while pc < len(code):
        op = code[pc]
        out.append((pc, op))
        pc += 1 + (op - 0x5F if 0x60 <= op <= 0x7F else 0)
    if pc != len(code):
        raise RuntimeError("truncated PUSH in constructor prefix")
    return out


def forbidden_constructor_ops(code: bytes, prefix_length: int) \
        -> List[Tuple[int, int]]:
    """Return state-changing, storage, log, and child-frame opcodes."""
    forbidden = {
        0x54, 0x55, 0x5C, 0x5D,
        0xA0, 0xA1, 0xA2, 0xA3, 0xA4,
        0xF0, 0xF1, 0xF2, 0xF4, 0xF5, 0xFA, 0xFF,
    }
    return [(pc, op) for pc, op in opcode_positions(code[:prefix_length])
            if op in forbidden]


def domain_separator(chain_id: int, target: bytes) -> bytes:
    from ethereum.crypto.hash import keccak256

    def h(text: bytes) -> bytes:
        return keccak256(text)

    return h(
        h(b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")
        + h(b"Wrapped Ether v10") + h(b"1")
        + chain_id.to_bytes(32, "big") + bytes(12) + target)


def make_environments(state, chain_id: int, gas: int):
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, TransactionEnvironment
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    caller = Address(bytes.fromhex(CALLER))
    block = BlockEnvironment(
        chain_id=U64(chain_id), state=state,
        block_gas_limit=Uint(30_000_000),
        block_hashes=[Hash32(bytes(32))],
        coinbase=Address(bytes.fromhex(COINBASE)), number=Uint(20_000_000),
        base_fee_per_gas=Uint(0), time=U256(1_700_000_000),
        prev_randao=Bytes32(bytes(32)), excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(bytes(32)))
    tx = TransactionEnvironment(
        origin=caller, gas_price=Uint(0), gas=Uint(gas),
        access_list_addresses=set(), access_list_storage_keys=set(),
        transient_storage=TransientStorage(), blob_versioned_hashes=(),
        authorizations=(), index_in_block=None, tx_hash=None, traces=[])
    return block, tx, caller


def create(initcode: bytes, chain_id: int, target: bytes, value: int = 0):
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import State, get_account, set_account
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_message_call
    from ethereum_types.bytes import Bytes, Bytes0
    from ethereum_types.numeric import U256, Uint

    gas = 20_000_000
    state = State()
    caller_address = Address(bytes.fromhex(CALLER))
    target_address = Address(target)
    set_account(state, caller_address,
                Account(Uint(0), U256(10**24), Bytes(b"")))
    block, tx, caller = make_environments(state, chain_id, gas)
    message = Message(
        block_env=block, tx_env=tx, caller=caller, target=Bytes0(b""),
        current_target=target_address, gas=Uint(gas), value=U256(value),
        data=Bytes(b""), code_address=None, code=Bytes(initcode),
        depth=Uint(0), should_transfer_value=True, is_static=False,
        accessed_addresses={caller, target_address},
        accessed_storage_keys=set(), disable_precompiles=False,
        parent_evm=None)
    output = process_message_call(message)
    return (state, target_address, get_account(state, target_address), output,
            gas - int(output.gas_left))


def validate_world(initcode: bytes, expected: bytes, chain_id: int,
                   target: bytes) -> Tuple[List[str], int]:
    from ethereum.prague.state import account_has_storage

    failures: List[str] = []
    state, target_address, account, output, gas_used = create(
        initcode, chain_id, target)
    if output.error is not None:
        failures.append("creation did not succeed")
        return failures, gas_used
    deployed = bytes(account.code)
    if deployed != expected:
        failures.append("deposited runtime differs from witnessed family member")
    if bytes(output.return_data) != expected:
        failures.append("constructor output differs from deposited runtime")
    if output.logs:
        failures.append("constructor emitted logs")
    if int(account.nonce) != 1 or int(account.balance) != 0:
        failures.append("fresh account nonce/balance is not canonical")
    if account_has_storage(state, target_address):
        failures.append("fresh deployment initialized persistent storage")
    chain_word = chain_id.to_bytes(32, "big")
    separator = domain_separator(chain_id, target)
    for off in CHAIN_OFFSETS:
        if deployed[off:off + 32] != chain_word:
            failures.append(f"chain word not installed at {off}")
    for off in DOMAIN_OFFSETS:
        if deployed[off:off + 32] != separator:
            failures.append(f"domain word not installed at {off}")
    return failures, gas_used


def expect_falsifier(name: str, initcode: bytes, expected: bytes,
                     chain_id: int, target: bytes) -> None:
    failures, _ = validate_world(initcode, expected, chain_id, target)
    if not failures:
        raise RuntimeError(f"deployment falsifier {name} was not detected")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--eels-root", required=True)
    parser.add_argument("--artifacts", required=True)
    args = parser.parse_args()
    eels_root = Path(args.eels_root).resolve()
    verify_eels_pin(eels_root)
    initcode, prefix_length, runtimes = parse_artifacts(Path(args.artifacts))

    if len(initcode) > 49_152:
        raise RuntimeError("initcode exceeds Prague EIP-3860 limit")
    if any(len(code) > 24_576 for code in runtimes.values()):
        raise RuntimeError("runtime exceeds Prague EIP-170 limit")
    runtime_template = initcode[prefix_length:]
    for off in CHAIN_OFFSETS + DOMAIN_OFFSETS:
        if runtime_template[off:off + 32] != bytes(32):
            raise RuntimeError(
                f"zero-parameter runtime template is prepatched at {off}")
    bad_ops = forbidden_constructor_ops(initcode, prefix_length)
    if bad_ops:
        raise RuntimeError(f"constructor contains state/log/call opcode: {bad_ops}")

    worlds = [
        ("mainnet", 1, bytes.fromhex(MAINNET), runtimes["mainnet-runtime"]),
        ("synthetic", 31_337, bytes.fromhex(SYNTHETIC),
         runtimes["synthetic-runtime"]),
    ]
    gas_values = []
    for label, chain_id, target, expected in worlds:
        failures, gas_used = validate_world(
            initcode, expected, chain_id, target)
        if failures:
            raise RuntimeError(f"{label} deployment: {failures}")
        gas_values.append(gas_used)

    from ethereum.prague.state import account_has_storage, get_account_optional

    rejected_state, rejected_target, _, rejected, _ = create(
        initcode, 1, bytes.fromhex(MAINNET), 1)
    if rejected.error is None or type(rejected.error).__name__ != "Revert":
        raise RuntimeError("nonzero constructor endowment did not deliberately revert")
    if bytes(rejected.return_data) or rejected.logs:
        raise RuntimeError("rejected deployment returned data or emitted logs")
    if get_account_optional(rejected_state, rejected_target) is not None or \
            account_has_storage(rejected_state, rejected_target):
        raise RuntimeError("rejected deployment left a target account effect")

    # Independent mutations exercise the opcode scan, nonpayability, both
    # chain-ID uses, address-derived domain, and runtime installation.  Opcode
    # positions avoid mistaking immediate bytes for executable opcodes.
    positions = opcode_positions(initcode[:prefix_length])
    callvalue_pcs = [pc for pc, op in positions if op == 0x34]
    chain_pcs = [pc for pc, op in positions if op == 0x46]
    address_pcs = [pc for pc, op in positions if op == 0x30]
    if len(callvalue_pcs) != 1 or len(chain_pcs) != 4 or \
            len(address_pcs) != 1:
        raise RuntimeError(
            "constructor opcode layout changed: expected one CALLVALUE, "
            "four CHAINID, and one ADDRESS")
    callvalue_pc = callvalue_pcs[0]
    address_pc = address_pcs[0]
    mutated = bytearray(initcode)
    mutated[callvalue_pc] = 0x55
    if not forbidden_constructor_ops(bytes(mutated), prefix_length):
        raise RuntimeError("constructor-opcode falsifier was not detected")
    mutated = bytearray(initcode)
    mutated[callvalue_pc] = 0x5f
    _, _, _, nonpayable_out, _ = create(
        bytes(mutated), 1, bytes.fromhex(MAINNET), 1)
    if nonpayable_out.error is not None:
        raise RuntimeError("nonpayability falsifier was not detected")
    mutated = bytearray(initcode)
    mutated[chain_pcs[0]] = 0x5f
    expect_falsifier("chainid", bytes(mutated), runtimes["mainnet-runtime"],
                     1, bytes.fromhex(MAINNET))
    mutated = bytearray(initcode)
    mutated[chain_pcs[-1]] = 0x5f
    expect_falsifier(
        "domain-chainid", bytes(mutated), runtimes["synthetic-runtime"],
        31_337, bytes.fromhex(SYNTHETIC))
    mutated = bytearray(initcode)
    mutated[address_pc] = 0x5f
    expect_falsifier("address", bytes(mutated), runtimes["mainnet-runtime"],
                     1, bytes.fromhex(MAINNET))
    mutated = bytearray(initcode)
    mutated[prefix_length + 17] ^= 1
    expect_falsifier("runtime-tail", bytes(mutated),
                     runtimes["mainnet-runtime"], 1, bytes.fromhex(MAINNET))

    print(
        "OK — WETH10 deployment: 2 fresh identity worlds; exact derived "
        f"runtime {len(runtimes['mainnet-runtime'])} bytes; initcode "
        f"{len(initcode)} bytes; nonpayable boundary; no calls/logs/storage "
        f"opcodes; empty initial storage; 6 falsifiers; observed creation gas "
        f"{gas_values[0]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
