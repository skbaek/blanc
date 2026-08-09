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
import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
MAINNET = "f4bb2e28688e89fcce3c0580d37d36a7672e8a9f"
SYNTHETIC = "0000000000000000000000000000000000001000"
TRANSACTION_TARGET = "cf024a39b81692e3c25b9ceb8474dc6203d584d7"
TRANSACTION_KEY = 29
CALLER = "1111111111111111111111111111111111111111"
COINBASE = "6666666666666666666666666666666666666666"
CHAIN_OFFSETS = (372, 691, 2875)
DOMAIN_OFFSETS = (536, 3039)


def parse_artifacts(path: Path) -> Tuple[bytes, int, Dict[str, bytes], bytes]:
    initcode = None
    prefix_length = None
    system_code = None
    runtimes: Dict[str, bytes] = {}
    for raw in path.read_text().splitlines():
        parts = raw.split()
        if not parts:
            continue
        if parts[0] == "prefix-length" and len(parts) == 2:
            prefix_length = int(parts[1])
        elif parts[0] in (
                "initcode", "mainnet-runtime", "synthetic-runtime",
                "transaction-runtime", "system-code") \
                and len(parts) == 3:
            code = bytes.fromhex(parts[2])
            if len(code) != int(parts[1]):
                raise RuntimeError(f"{parts[0]}: declared length mismatch")
            if parts[0] == "initcode":
                initcode = code
            elif parts[0] == "system-code":
                system_code = code
            else:
                runtimes[parts[0]] = code
        else:
            raise RuntimeError(f"unrecognized evaluator output: {raw!r}")
    if initcode is None or prefix_length is None or system_code is None or \
            set(runtimes) != {
                "mainnet-runtime", "synthetic-runtime", "transaction-runtime"
            }:
        raise RuntimeError("deployment evaluator output is incomplete")
    runtime_lengths = {len(code) for code in runtimes.values()}
    if len(runtime_lengths) != 1:
        raise RuntimeError("deployment runtime family changed byte length")
    if not 0 <= prefix_length <= len(initcode) or \
            len(initcode) - prefix_length != next(iter(runtime_lengths)):
        raise RuntimeError("initcode runtime-tail length mismatch")
    if not system_code:
        raise RuntimeError("deployment system program must be nonempty")
    return initcode, prefix_length, runtimes, system_code


def load_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load deployment fixture support {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def validate_transaction_fixture(
        initcode: bytes, expected_runtime: bytes, system_code: bytes,
        jaune_bin: Path) -> Tuple[int, int]:
    """Generate and replay one strict singleton type-2 creation block."""
    repo = Path(__file__).resolve().parents[1]
    fixtures = load_script(
        "weth10_deployment_transaction_support",
        repo / "scripts" / "gen-weth10-redemption-fixtures.py",
    )
    from ethereum.crypto.hash import keccak256
    from ethereum_rlp import rlp
    from ethereum_types.numeric import Uint

    sender = fixtures.derive_address(TRANSACTION_KEY)
    computed_target = keccak256(
        rlp.encode((fixtures.address_bytes(sender), Uint(0)))
    )[-20:]
    if computed_target.hex() != TRANSACTION_TARGET:
        raise RuntimeError(
            "transaction fixture CREATE address no longer matches the "
            "independently named Lean runtime member"
        )
    target = "0x" + TRANSACTION_TARGET
    gas_limit = 2_000_000
    tx = {
        "type": "0x2",
        "chainId": "0x1",
        "nonce": "0x0",
        "maxPriorityFeePerGas": fixtures.q(fixtures.GAS_PRICE),
        "maxFeePerGas": fixtures.q(fixtures.GAS_PRICE),
        "gas": fixtures.q(gas_limit),
        "to": "",
        "value": "0x0",
        "input": "0x" + initcode.hex(),
        "accessList": [],
        "v": "0x0",
        "r": "0x0",
        "s": "0x0",
        "secretKey": fixtures.private_key_hex(TRANSACTION_KEY),
    }
    system_hex = "0x" + system_code.hex()
    system_addresses = fixtures.support.SYSTEM[:4]
    alloc = {
        sender: fixtures.eoa(10**18),
        **{
            address: fixtures.contract(system_hex, nonce=1)
            for address in system_addresses
        },
    }

    def expect(e):
        profile = (
            tx["type"] == "0x2"
            and tx["to"] == ""
            and tx["value"] == "0x0"
            and tx["input"] == "0x" + initcode.hex()
            and tx["accessList"] == []
            and "authorizationList" not in tx
            and int(tx["gas"], 16) >= 1_421_317
        )
        e._record(
            profile,
            "canonical singleton creation profile",
            True,
            profile,
            "the block body contains one funded EIP-1559 type-2 CREATE with "
            "zero value, exact Blanc initcode, empty access list, no blobs, "
            "no authorizations, and gas above the proved top-level bound",
        )
        e._record(
            target.lower() not in {key.lower() for key in alloc},
            "fresh computed target",
            "absent",
            "present" if target.lower() in {
                key.lower() for key in alloc
            } else "absent",
            "the independently derived CREATE address has no pre-state code, "
            "nonce, balance, or storage entry",
        )
        e.expect_tx_succeeded(
            0,
            "the singleton top-level creation transaction has a successful "
            "receipt rather than merely a successful outer transition",
        )
        e.expect_nonce(
            "deployment sender", sender, 1,
            "the accepted creation transaction increments its recovered "
            "sender nonce exactly once",
        )
        e.expect_nonce(
            "computed deployment target", target, 1,
            "successful CREATE installs the canonical fresh-account nonce",
        )
        e.expect_code(
            "computed deployment target", target,
            "0x" + expected_runtime.hex(),
            "the transaction installs the exact chain/address-parameterized "
            "Blanc runtime named by Lean",
        )
        e.expect_storage_exact(
            "computed deployment target", target, {},
            "the constructor leaves the complete persistent storage empty",
        )
        e.expect_ether(
            "computed deployment target", target, 0,
            "the canonical zero-endowment deployment leaves zero contract ETH",
        )
        for address in system_addresses:
            e.expect_code(
                f"request/prefix system address {address}", address, system_hex,
                "the beacon/history prefix and withdrawal/consolidation suffix "
                "execute the exact nonempty state-neutral program",
            )
        e.expect_fee_accounting([(sender, [0])])
        e.expect_logs(
            [[]],
            "the constructor receipt and block log sequence are exactly empty, "
            "so deposit-request parsing observes no constructor deposit log",
        )

    fixture, result, assertion_count = fixtures.build_fixture(
        "01-canonical-type2-deployment", alloc, [tx], expect
    )
    old_name = next(iter(fixture))
    case = fixture.pop(old_name)
    fixture = {
        old_name.replace("weth10-redemption", "weth10-deployment"): case
    }
    if len(result["receipts"]) != 1 or not result["receipts"][0]["succeeded"]:
        raise RuntimeError("transaction fixture did not retain one successful receipt")
    with tempfile.TemporaryDirectory() as tmp:
        fixture_path = Path(tmp) / "canonical-type2-deployment.json"
        fixture_path.write_text(json.dumps(fixture, indent=2) + "\n")
        replay = subprocess.run(
            [str(jaune_bin), str(fixture_path), "--network", "Prague"],
            text=True,
            capture_output=True,
        )
        if replay.returncode != 0:
            detail = (replay.stdout + replay.stderr).strip()
            raise RuntimeError(
                f"Jaune strict checked deployment fixture replay failed: {detail}"
            )
    return assertion_count, int(result["gasUsed"], 16)


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
    parser.add_argument("--jaune-bin", required=True)
    args = parser.parse_args()
    eels_root = Path(args.eels_root).resolve()
    verify_eels_pin(eels_root)
    initcode, prefix_length, runtimes, system_code = parse_artifacts(
        Path(args.artifacts)
    )

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

    transaction_assertions, transaction_gas = validate_transaction_fixture(
        initcode, runtimes["transaction-runtime"], system_code,
        Path(args.jaune_bin).resolve(),
    )

    print(
        "OK — WETH10 deployment: 2 fresh identity worlds and 1 singleton "
        "type-2 strict checked Prague block; exact successful receipt; exact "
        f"runtime {len(runtimes['mainnet-runtime'])} bytes; initcode "
        f"{len(initcode)} bytes; nonpayable boundary; no calls/logs/storage "
        f"opcodes; empty initial storage; {transaction_assertions} transaction "
        f"assertions; 6 falsifiers; observed direct/transaction creation gas "
        f"{gas_values[0]}/{transaction_gas}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
