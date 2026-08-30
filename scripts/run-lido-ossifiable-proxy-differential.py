#!/usr/bin/env python3
"""Run the frozen 85-case OssifiableProxy differential offline in EELS Prague.

The runner never derives or rewrites the corpus.  Each side of every row gets a
fresh state.  Solidity creation/runtime bytes come only from the locked
reference JSON; Blanc bytes come only from the strict two-row Lean evaluator
envelope.  A result is emitted only after all 85 cases execute, and is created
exclusively so an existing immutable result cannot be overwritten.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, NoReturn, Sequence

from lido_ossifiable_proxy_differential_schema import (
    CASE_COUNT,
    EELS_COMMIT,
    EVALUATOR_RELATIVE,
    LAUNCHER_RELATIVE,
    MANIFEST_DIGEST,
    MANIFEST_RELATIVE,
    PERFORMANCE_DIGEST,
    PERFORMANCE_RELATIVE,
    PROJECTION_CHANNELS,
    REFERENCE_LOCK_SHA256,
    REFERENCE_RELATIVE,
    RESULT_FORMAT,
    RUNNER_RELATIVE,
    SCHEMA_RELATIVE,
    load_and_validate_campaign,
    manifest_order_sha256,
    materialize_expected_projection,
    projection_mismatches,
    resolve_reference,
    resolve_tree,
    seal_result,
    sha256_bytes,
    sha256_file,
    validate_result,
)


DEFAULT_GAS = 20_000_000
EIP170_LIMIT = 24_576
EIP3860_LIMIT = 49_152


class RunnerError(RuntimeError):
    pass


def die(message: str) -> NoReturn:
    raise RunnerError(message)


def hex_bytes(value: Any, owner: str) -> bytes:
    if not isinstance(value, str) or not value.startswith("0x") or len(value) % 2:
        die(f"{owner} must be even-length 0x hex")
    try:
        return bytes.fromhex(value[2:])
    except ValueError:
        die(f"{owner} is not hex")


def address_bytes(value: Any, owner: str = "address") -> bytes:
    raw = hex_bytes(value, owner)
    if len(raw) != 20:
        die(f"{owner} must be exactly 20 bytes")
    return raw


def canonical_address(value: str) -> str:
    return "0x" + address_bytes(value).hex()


def word_hex(value: Any, owner: str) -> str:
    if isinstance(value, int):
        number = value
    elif isinstance(value, str) and value.startswith("0x"):
        raw = hex_bytes(value, owner)
        if len(raw) == 20:
            raw = bytes(12) + raw
        if len(raw) != 32:
            die(f"{owner} cannot be normalized to one word")
        return "0x" + raw.hex()
    elif isinstance(value, str) and value.isdigit():
        number = int(value)
    else:
        die(f"{owner} is not a word/address/integer")
    if number < 0 or number >= 1 << 256:
        die(f"{owner} integer is outside uint256")
    return "0x" + number.to_bytes(32, "big").hex()


def sha_identity(raw: bytes) -> Dict[str, Any]:
    return {"byteLength": len(raw), "sha256": sha256_bytes(raw)}


def git_output(root: Path, *args: str) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), *args], text=True, stderr=subprocess.STDOUT
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        die(f"cannot inspect git checkout {root}: {exc}")


def verify_clean_blanc(root: Path) -> str:
    commit = git_output(root, "rev-parse", "HEAD")
    if len(commit) != 40 or any(ch not in "0123456789abcdef" for ch in commit):
        die(f"invalid Blanc commit identity: {commit}")
    dirty = git_output(root, "status", "--porcelain")
    if dirty:
        die("Blanc checkout is dirty; immutable differential identity requires a clean commit")
    return commit


def verify_eels(root: Path) -> None:
    commit = git_output(root, "rev-parse", "HEAD")
    dirty = git_output(root, "status", "--porcelain")
    if commit != EELS_COMMIT or dirty:
        die(f"EELS must be clean at {EELS_COMMIT}; found {commit}, dirty={bool(dirty)}")
    expected_python = (root / "venv/bin/python").absolute()
    if Path(sys.executable).absolute() != expected_python:
        die(f"runner must use pinned EELS interpreter {expected_python}; found {sys.executable}")
    expected_source = (root / "src").resolve()
    if os.environ.get("PYTHONDONTWRITEBYTECODE") != "1" or \
            Path(os.environ.get("PYTHONPATH", "")).resolve() != expected_source:
        die("EELS requires PYTHONDONTWRITEBYTECODE=1 and exact PYTHONPATH=<EELS_ROOT>/src")
    import ethereum
    module_path = Path(ethereum.__file__).resolve()
    if not module_path.is_relative_to(expected_source):
        die(f"ethereum package was not imported from pinned EELS root: {module_path}")


def parse_blanc_artifacts(path: Path) -> Dict[str, Any]:
    """Parse the exact W2c evaluator contract; aliases and extra rows reject."""
    try:
        lines = path.read_text().splitlines()
    except OSError as exc:
        die(f"cannot read Blanc artifact envelope {path}: {exc}")
    labels = ("creation-template", "returned-runtime")
    if len(lines) != 2:
        die(f"Blanc evaluator must emit exactly two nonempty rows, got {len(lines)}")
    parsed: Dict[str, bytes] = {}
    for line, wanted in zip(lines, labels):
        parts = line.split()
        if len(parts) != 3 or parts[0] != wanted:
            die(f"expected evaluator row '{wanted} <byteLength> <lowercase hex>'")
        if not parts[1].isdigit() or str(int(parts[1])) != parts[1] or \
                not parts[2] or parts[2].lower() != parts[2] or \
                any(ch not in "0123456789abcdef" for ch in parts[2]) or len(parts[2]) % 2:
            die(f"malformed evaluator row: {wanted}")
        raw = bytes.fromhex(parts[2])
        if len(raw) != int(parts[1]):
            die(f"evaluator length mismatch: {wanted}")
        parsed[wanted] = raw
    template, runtime = parsed["creation-template"], parsed["returned-runtime"]
    if not runtime or len(template) <= len(runtime) or not template.endswith(runtime):
        die("returned-runtime must be a proper nonempty exact suffix of creation-template")
    if len(template) > EIP3860_LIMIT or len(runtime) > EIP170_LIMIT:
        die("Blanc artifact exceeds EIP-3860/EIP-170 limit")
    return {
        "creationTemplate": template,
        "returnedRuntime": runtime,
        "envelopeSha256": sha256_file(path),
    }


@dataclass(frozen=True)
class ArtifactSide:
    name: str
    creation_template: bytes
    returned_runtime: bytes


class Fixtures:
    def __init__(self, manifest: Mapping[str, Any], performance: Mapping[str, Any]):
        self.manifest = manifest
        self.performance = performance
        self.slots = manifest["fixtures"]["slots"]

    def resolve(self, value: Any) -> Any:
        return resolve_reference(self.manifest, self.performance, value)

    def tree(self, value: Any) -> Any:
        return resolve_tree(self.manifest, self.performance, value)

    def raw(self, value: Any, owner: str) -> bytes:
        return hex_bytes(self.resolve(value), owner)

    def address(self, value: Any, owner: str) -> str:
        resolved = self.resolve(value)
        return canonical_address(resolved)

    def direct_ref(self, value: str) -> Any:
        if value.startswith("performance:"):
            bindings = self.manifest["sharedPerformanceManifest"]["sharedReferenceBindings"]
            source = self.performance
        elif value.startswith("differential:"):
            bindings = self.manifest["fixtures"]["localReferenceBindings"]
            source = self.manifest
        else:
            return value
        pointer = bindings[value]
        current: Any = source
        for token in pointer[1:].split("/"):
            token = token.replace("~1", "/").replace("~0", "~")
            current = current[int(token)] if isinstance(current, list) else current[token]
        return current

    def code(self, value: Any, owner: str) -> bytes:
        resolved = self.resolve(value)
        if not isinstance(resolved, Mapping):
            die(f"{owner} mock bytecode did not resolve to a blob")
        return hex_bytes(resolved.get("hex"), owner)

    def proxy_state_slots(self, value: Any) -> Dict[str, str]:
        if isinstance(value, str) and value.startswith(("performance:", "differential:")):
            value = self.direct_ref(value)
        if not isinstance(value, Mapping):
            die("proxy state did not resolve to an object")
        if "base" in value:
            slots = self.proxy_state_slots(value["base"])
        else:
            default = word_hex(value.get("storageDefault", "0x" + "00" * 32), "storage default")
            slots = {slot: default for slot in self.slots.values()}
        for key, raw in value.get("storageOverrides", {}).items():
            if key in slots:
                slots[key] = word_hex(raw, f"storage override {key}")
        return slots


def observed_addresses(fixtures: Fixtures) -> tuple[str, ...]:
    values: set[str] = set()

    def visit(value: Any) -> None:
        if isinstance(value, str) and re.fullmatch(r"0x[0-9a-fA-F]{40}", value):
            values.add(canonical_address(value))
        elif isinstance(value, Mapping):
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(fixtures.performance)
    visit(fixtures.manifest)
    return tuple(sorted(values))


def expected_storage(
    case: Mapping[str, Any], fixtures: Fixtures, pre_storage: Mapping[str, Any]
) -> Dict[str, Any]:
    specification = case["expected"]["storage"]
    zero = "0x" + "00" * 32
    if specification == "exact-prestate":
        return copy.deepcopy(pre_storage)
    if specification == "target-absent":
        return {"targetExists": False, "slots": {slot: zero for slot in fixtures.slots.values()}}
    if not isinstance(specification, Mapping):
        die(f"{case['id']} has unsupported storage expectation")
    if "base" in specification:
        slots = fixtures.proxy_state_slots(specification["base"])
    else:
        slots = {slot: zero for slot in fixtures.slots.values()}
    key_map = {
        "admin": fixtures.slots["admin"],
        "implementation": fixtures.slots["implementation"],
        "fixtureSlot": fixtures.slots["fixture"],
    }
    for name, slot in key_map.items():
        if name in specification:
            slots[slot] = word_hex(fixtures.resolve(specification[name]), f"{case['id']} {name}")
    if specification.get("allOtherStorage") not in (None, "differential:word:zero"):
        die(f"{case['id']} allOtherStorage contract drifted")
    return {"targetExists": True, "slots": slots}


def expected_eth(
    case: Mapping[str, Any], fixtures: Fixtures, addresses: Sequence[str]
) -> Dict[str, str]:
    result = {address: "0" for address in addresses}
    specification = case["expected"]["eth"]
    if specification == "exact-prestate":
        return result
    if specification != "forwarding-caller decreases by receive-value; proxy-target increases by receive-value":
        die(f"{case['id']} has unsupported ETH expectation")
    caller = fixtures.address("performance:forwarding-caller", "forwarding caller")
    target = fixtures.address("performance:proxy-target", "proxy target")
    amount = int(fixtures.resolve("performance:receive-value"))
    result[caller], result[target] = str(-amount), str(amount)
    return result


def expected_delegatecalls(case: Mapping[str, Any], fixtures: Fixtures) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    for row in case["expected"]["delegatecalls"]:
        resolved = fixtures.tree(row)
        rows.append({
            "caller": canonical_address(resolved["caller"]),
            "childReturndata": "0x" + hex_bytes(resolved["childReturndata"], "child returndata").hex(),
            "childStatus": resolved["childStatus"],
            "codeAddress": canonical_address(resolved["codeAddress"]),
            "input": "0x" + hex_bytes(resolved["input"], "delegate input").hex(),
            "opcode": "DELEGATECALL",
            "source": canonical_address(resolved["source"]),
            "storageOwner": canonical_address(resolved["storageOwner"]),
            "value": str(int(resolved["value"])),
        })
    return rows


def expected_projection(
    case: Mapping[str, Any], fixtures: Fixtures, pre_storage: Mapping[str, Any],
    addresses: Sequence[str],
) -> Dict[str, Any]:
    returndata = case["expected"]["returndata"]
    if returndata != "own-returned-runtime":
        returndata = "0x" + fixtures.raw(returndata, f"{case['id']} returndata").hex()
    logs = [copy.deepcopy(fixtures.manifest["fixtures"]["logAtoms"][name])
            for name in case["expected"]["logs"]]
    return {
        "status": case["expected"]["status"],
        "returndata": returndata,
        "storage": expected_storage(case, fixtures, pre_storage),
        "eth": expected_eth(case, fixtures, addresses),
        "logs": logs,
        "delegatecalls": expected_delegatecalls(case, fixtures),
        "targetAccount": case["expected"]["targetAccount"],
    }


def dry_resolve(
    manifest: Mapping[str, Any], performance: Mapping[str, Any]
) -> int:
    fixtures = Fixtures(manifest, performance)
    addresses = observed_addresses(fixtures)
    if not addresses:
        die("fixture resolver found no observed addresses")
    for case in manifest["cases"]:
        world = case["world"]
        fixtures.address(world["caller"], f"{case['id']} caller")
        fixtures.address(world["target"], f"{case['id']} target")
        value = int(fixtures.resolve(world["value"]))
        if value < 0 or value >= 1 << 256:
            die(f"{case['id']} value is outside uint256")
        access = fixtures.resolve(world["accessSet"])
        if not isinstance(access, Mapping) or set(access) != {
            "accessedAddresses", "accessedStorageKeys"
        }:
            die(f"{case['id']} access set shape drifted")
        for address in access["accessedAddresses"]:
            canonical_address(address)
        for row in access["accessedStorageKeys"]:
            canonical_address(row["address"])
            if len(hex_bytes(row["key"], f"{case['id']} accessed storage key")) != 32:
                die(f"{case['id']} accessed storage key width drifted")
        if world["kind"] == "direct-create-message":
            zero = "0x" + "00" * 32
            pre = {"targetExists": False, "slots": {slot: zero for slot in fixtures.slots.values()}}
            fixtures.raw(world["constructorArguments"], f"{case['id']} constructor arguments")
            if fixtures.raw(world["messageData"], f"{case['id']} CREATE message data"):
                die(f"{case['id']} CREATE message data must be empty")
        elif world["kind"] == "direct-call-message":
            pre = {"targetExists": True, "slots": fixtures.proxy_state_slots(world["proxyState"])}
            fixtures.raw(world["calldata"], f"{case['id']} calldata")
        else:
            die(f"{case['id']} has unsupported world kind")
        projection = expected_projection(case, fixtures, pre, addresses)
        canonical_projection = materialize_expected_projection(
            manifest, performance, case
        )
        if projection != canonical_projection:
            die(f"{case['id']} runner/schema expected projection drifted")
        if set(projection) != set(PROJECTION_CHANNELS):
            die(f"{case['id']} dry projection is incomplete")
        for account in world["implementationAccounts"]:
            fixtures.address(account["address"], f"{case['id']} implementation")
            fixtures.code(account["bytecode"], f"{case['id']} implementation code")
            template = fixtures.resolve(account["accountTemplate"])
            if not isinstance(template, Mapping):
                die(f"{case['id']} implementation account template drifted")
        for absent in world["absentAccounts"]:
            fixtures.address(absent, f"{case['id']} absent account")
    return len(addresses)


def _balance(state: Any, address: str) -> int:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account_optional

    account = get_account_optional(state, Address(address_bytes(address)))
    return 0 if account is None else int(account.balance)


def _account_exists(state: Any, address: str) -> bool:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account_optional

    return get_account_optional(state, Address(address_bytes(address))) is not None


def _storage_projection(state: Any, target: str, fixtures: Fixtures) -> Dict[str, Any]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_storage
    from ethereum_types.bytes import Bytes32

    address = Address(address_bytes(target))
    slots = {
        slot: "0x" + int(get_storage(state, address, Bytes32(hex_bytes(slot, "slot")))).to_bytes(32, "big").hex()
        for slot in fixtures.slots.values()
    }
    return {"targetExists": _account_exists(state, target), "slots": slots}


def _set_account(state: Any, address: str, nonce: int, balance: int, code: bytes) -> None:
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import set_account
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import U256, Uint

    set_account(
        state, Address(address_bytes(address)),
        Account(Uint(nonce), U256(balance), Bytes(code)),
    )


def _build_state(case: Mapping[str, Any], side: ArtifactSide, fixtures: Fixtures) -> Any:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import State, get_account_optional, set_storage
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256

    state = State()
    world = case["world"]
    caller = fixtures.address(world["caller"], f"{case['id']} caller")
    caller_template = fixtures.performance["fixtures"]["accountTemplates"]["caller"]
    nonce = int(world.get("callerNonce", caller_template["nonce"]))
    _set_account(state, caller, nonce, int(caller_template["balance"]), b"")
    target = fixtures.address(world["target"], f"{case['id']} target")
    if world["kind"] == "direct-call-message":
        proxy = fixtures.performance["fixtures"]["proxyStates"]["unossified"]
        state_ref = world["proxyState"]
        raw_state = fixtures.direct_ref(state_ref) if isinstance(state_ref, str) else state_ref
        while isinstance(raw_state, Mapping) and "base" in raw_state:
            raw_state = fixtures.direct_ref(raw_state["base"])
        account_nonce = int(raw_state.get("accountNonce", proxy["accountNonce"]))
        account_balance = int(raw_state.get("accountBalance", proxy["accountBalance"]))
        _set_account(state, target, account_nonce, account_balance, side.returned_runtime)
        for slot, value in fixtures.proxy_state_slots(state_ref).items():
            set_storage(
                state, Address(address_bytes(target)), Bytes32(hex_bytes(slot, "state slot")),
                U256(int(value, 16)),
            )
    elif not world.get("targetInitiallyAbsent"):
        die(f"{case['id']} CREATE target must begin absent")

    for row in world["implementationAccounts"]:
        address = fixtures.address(row["address"], f"{case['id']} implementation address")
        template = fixtures.resolve(row["accountTemplate"])
        code = fixtures.code(row["bytecode"], f"{case['id']} implementation bytecode")
        _set_account(state, address, int(template["nonce"]), int(template["balance"]), code)
    for absent in world["absentAccounts"]:
        address = fixtures.address(absent, f"{case['id']} absent account")
        if get_account_optional(state, Address(address_bytes(address))) is not None:
            die(f"{case['id']} required absent account was materialized: {address}")
    return state


def _environments(
    state: Any, caller: str, case: Mapping[str, Any], fixtures: Fixtures
) -> tuple[Any, Any, set[Any], set[Any]]:
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, TransactionEnvironment
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    block_spec = fixtures.performance["fixtures"]["blockEnvironment"]
    access = fixtures.resolve(case["world"]["accessSet"])
    accessed_addresses = {
        Address(address_bytes(value, "accessed address")) for value in access["accessedAddresses"]
    }
    accessed_storage = {
        (Address(address_bytes(row["address"], "accessed storage address")),
         Bytes32(hex_bytes(row["key"], "accessed storage key")))
        for row in access["accessedStorageKeys"]
    }
    block = BlockEnvironment(
        chain_id=U64(int(block_spec["chainId"])), state=state,
        block_gas_limit=Uint(int(block_spec["blockGasLimit"])),
        block_hashes=[Hash32(hex_bytes(value, "block hash")) for value in block_spec["blockHashes"]],
        coinbase=Address(address_bytes(block_spec["coinbase"], "coinbase")),
        number=Uint(int(block_spec["number"])),
        base_fee_per_gas=Uint(int(block_spec["baseFeePerGas"])),
        time=U256(int(block_spec["timestamp"])),
        prev_randao=Bytes32(hex_bytes(block_spec["prevRandao"], "prevRandao")),
        excess_blob_gas=U64(int(block_spec["excessBlobGas"])),
        parent_beacon_block_root=Hash32(hex_bytes(block_spec["parentBeaconBlockRoot"], "beacon root")),
    )
    tx = TransactionEnvironment(
        origin=Address(address_bytes(caller)), gas_price=Uint(0), gas=Uint(DEFAULT_GAS),
        access_list_addresses=set(), access_list_storage_keys=set(),
        transient_storage=TransientStorage(), blob_versioned_hashes=(),
        authorizations=(), index_in_block=None, tx_hash=None, traces=[],
    )
    return block, tx, accessed_addresses, accessed_storage


def _outcome(error: Any) -> str:
    if error is None:
        return "success"
    return "revert" if type(error).__name__ == "Revert" else "exception:" + type(error).__name__


def _child_status(error: Any) -> str:
    if error is None:
        return "success"
    name = type(error).__name__
    if name == "Revert":
        return "revert"
    if name == "StackUnderflowError":
        name = "StackUnderflow"
    return "exception:" + name


def _normalized_logs(logs: Iterable[Any]) -> List[Dict[str, Any]]:
    return [{
        "address": "0x" + bytes(log.address).hex(),
        "topics": ["0x" + bytes(topic).hex() for topic in log.topics],
        "data": "0x" + bytes(log.data).hex(),
    } for log in logs]


class DelegateTracer:
    def __init__(self):
        self.rows: List[Dict[str, Any]] = []
        self.pending: Dict[int, List[int]] = {}

    @staticmethod
    def memory_read(memory: bytearray, start: int, size: int) -> bytes:
        if size > 1_100_000:
            die(f"refusing oversized traced DELEGATECALL input: {size}")
        available = bytes(memory[start:start + size])
        return available + bytes(size - len(available))

    def __call__(self, evm: Any, event: Any, /, **_kw: Any) -> None:
        from ethereum.trace import OpEnd, OpException, OpStart

        if isinstance(event, OpStart) and event.op.name == "DELEGATECALL":
            if len(evm.stack) < 6:
                die("traced DELEGATECALL stack underflow")
            code_address = int(evm.stack[-2]).to_bytes(32, "big")[-20:]
            input_offset, input_size = int(evm.stack[-3]), int(evm.stack[-4])
            row = {
                "caller": "0x" + bytes(evm.message.caller).hex(),
                "childReturndata": None,
                "childStatus": None,
                "codeAddress": "0x" + code_address.hex(),
                "input": "0x" + self.memory_read(evm.memory, input_offset, input_size).hex(),
                "opcode": "DELEGATECALL",
                "source": "0x" + bytes(evm.message.current_target).hex(),
                "storageOwner": "0x" + bytes(evm.message.current_target).hex(),
                "value": str(int(evm.message.value)),
                "_childError": None,
            }
            self.rows.append(row)
            self.pending.setdefault(id(evm), []).append(len(self.rows) - 1)
            return
        if isinstance(event, OpException) and evm.message.parent_evm is not None:
            parent_id = id(evm.message.parent_evm)
            indices = self.pending.get(parent_id, [])
            if indices:
                self.rows[indices[-1]]["_childError"] = event.error
            return
        if isinstance(event, OpEnd):
            indices = self.pending.get(id(evm), [])
            if not indices:
                return
            index = indices.pop()
            row = self.rows[index]
            success = int(evm.stack[-1])
            if success:
                row["childStatus"] = "success"
            elif row["_childError"] is not None:
                row["childStatus"] = _child_status(row["_childError"])
            else:
                die("failed DELEGATECALL had no traced child outcome")
            row["childReturndata"] = "0x" + bytes(evm.return_data).hex()
            del row["_childError"]

    def finish(self) -> List[Dict[str, Any]]:
        if any(self.pending.values()) or any(row.get("childStatus") is None for row in self.rows):
            die("DELEGATECALL trace contains an unmatched opcode")
        return self.rows


def _execute(
    case: Mapping[str, Any], side: ArtifactSide, fixtures: Fixtures, state: Any
) -> tuple[str, bytes, Sequence[Any], List[Dict[str, Any]]]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_create_message, process_message_call
    from ethereum.trace import set_evm_trace
    from ethereum_types.bytes import Bytes, Bytes0
    from ethereum_types.numeric import U256, Uint

    if process_message_call.__module__ != "ethereum.prague.vm.interpreter" or \
            process_create_message.__module__ != "ethereum.prague.vm.interpreter":
        die("imported EELS entrypoint identity drifted")
    world = case["world"]
    caller = fixtures.address(world["caller"], f"{case['id']} caller")
    target = fixtures.address(world["target"], f"{case['id']} target")
    block, tx, accessed_addresses, accessed_storage = _environments(
        state, caller, case, fixtures
    )
    tracer = DelegateTracer()
    previous = set_evm_trace(tracer)
    try:
        if world["kind"] == "direct-create-message":
            arguments = fixtures.raw(world["constructorArguments"], f"{case['id']} constructor arguments")
            message_data = fixtures.raw(world["messageData"], f"{case['id']} CREATE message data")
            if message_data:
                die(f"{case['id']} CREATE message data must be empty")
            initcode = side.creation_template + arguments
            if len(initcode) > EIP3860_LIMIT:
                die(f"{case['id']}/{side.name} full CREATE input exceeds EIP-3860")
            message = Message(
                block_env=block, tx_env=tx,
                caller=Address(address_bytes(caller)), target=Bytes0(b""),
                current_target=Address(address_bytes(target)), gas=Uint(DEFAULT_GAS),
                value=U256(int(fixtures.resolve(world["value"]))), data=Bytes(message_data),
                code_address=None, code=Bytes(initcode), depth=Uint(0),
                should_transfer_value=True, is_static=False,
                accessed_addresses=accessed_addresses, accessed_storage_keys=accessed_storage,
                disable_precompiles=False, parent_evm=None,
            )
            evm = process_create_message(message)
            status, returndata = _outcome(evm.error), bytes(evm.output)
            logs = () if evm.error is not None else evm.logs
        else:
            calldata = fixtures.raw(world["calldata"], f"{case['id']} calldata")
            message = Message(
                block_env=block, tx_env=tx,
                caller=Address(address_bytes(caller)), target=Address(address_bytes(target)),
                current_target=Address(address_bytes(target)), gas=Uint(DEFAULT_GAS),
                value=U256(int(fixtures.resolve(world["value"]))), data=Bytes(calldata),
                code_address=Address(address_bytes(target)), code=Bytes(side.returned_runtime),
                depth=Uint(0), should_transfer_value=True, is_static=False,
                accessed_addresses=accessed_addresses, accessed_storage_keys=accessed_storage,
                disable_precompiles=False, parent_evm=None,
            )
            output = process_message_call(message)
            status, returndata, logs = _outcome(output.error), bytes(output.return_data), output.logs
    finally:
        set_evm_trace(previous)
    return status, returndata, logs, tracer.finish()


def _target_account_label(
    case: Mapping[str, Any], side: ArtifactSide, state: Any, fixtures: Fixtures,
    status: str,
) -> str:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account_optional

    target = fixtures.address(case["world"]["target"], f"{case['id']} target")
    account = get_account_optional(state, Address(address_bytes(target)))
    if case["world"]["kind"] == "direct-create-message":
        if status == "success":
            if account is None or bytes(account.code) != side.returned_runtime or int(account.nonce) != 1:
                die(f"{case['id']}/{side.name}: successful CREATE did not install its bound runtime")
            return "exists-with-own-returned-runtime"
        if account is not None:
            die(f"{case['id']}/{side.name}: failed CREATE left a target account")
        return "absent"
    if account is None or bytes(account.code) != side.returned_runtime or int(account.nonce) != 1:
        die(f"{case['id']}/{side.name}: runtime world lost its side-specific proxy account")
    return "preexisting-proxy-account"


def run_case(
    case: Mapping[str, Any], side: ArtifactSide, fixtures: Fixtures,
    addresses: Sequence[str],
) -> tuple[Dict[str, Any], Dict[str, Any]]:
    state = _build_state(case, side, fixtures)
    target = fixtures.address(case["world"]["target"], f"{case['id']} target")
    pre_storage = _storage_projection(state, target, fixtures)
    pre_balances = {address: _balance(state, address) for address in addresses}
    expected = expected_projection(case, fixtures, pre_storage, addresses)
    try:
        status, returndata_raw, logs_raw, delegatecalls = _execute(case, side, fixtures, state)
    except Exception as exc:
        die(f"{case['id']}/{side.name} execution failed: {exc}")
    if status == "success" and case["world"]["kind"] == "direct-create-message":
        returndata = "own-returned-runtime"
        if returndata_raw != side.returned_runtime:
            die(f"{case['id']}/{side.name}: CREATE return is not its bound runtime")
    else:
        returndata = "0x" + returndata_raw.hex()
    actual = {
        "status": status,
        "returndata": returndata,
        "storage": _storage_projection(state, target, fixtures),
        "eth": {address: str(_balance(state, address) - pre_balances[address]) for address in addresses},
        "logs": _normalized_logs(logs_raw),
        "delegatecalls": delegatecalls,
        "targetAccount": _target_account_label(case, side, state, fixtures, status),
    }
    return expected, actual


def build_identity(
    repo_root: Path, commit: str,
    manifest: Mapping[str, Any], performance_path: Path, reference: Mapping[str, Any],
    artifacts: Mapping[str, Any],
) -> Dict[str, Any]:
    evaluator = repo_root / EVALUATOR_RELATIVE
    launcher = repo_root / LAUNCHER_RELATIVE
    runner = repo_root / RUNNER_RELATIVE
    schema = repo_root / SCHEMA_RELATIVE
    for owner in (evaluator, launcher, runner, schema):
        if not owner.is_file():
            die(f"identity-owned implementation file is missing: {owner}")
    return {
        "manifestDigest": MANIFEST_DIGEST,
        "manifestPath": MANIFEST_RELATIVE.as_posix(),
        "manifestCaseCount": CASE_COUNT,
        "manifestOrderSha256": manifest_order_sha256(manifest),
        "performanceManifestDigest": PERFORMANCE_DIGEST,
        "performanceManifestSha256": sha256_file(performance_path),
        "referenceLockSha256": REFERENCE_LOCK_SHA256,
        "referenceArtifacts": {
            "creationTemplate": {
                "byteLength": reference["artifacts"]["creationTemplate"]["byteLength"],
                "sha256": reference["artifacts"]["creationTemplate"]["sha256"],
            },
            "runtime": {
                "byteLength": reference["artifacts"]["runtime"]["byteLength"],
                "sha256": reference["artifacts"]["runtime"]["sha256"],
            },
        },
        "eels": {
            "callEntrypoint": "ethereum.prague.vm.interpreter.process_message_call",
            "commit": EELS_COMMIT,
            "createEntrypoint": "ethereum.prague.vm.interpreter.process_create_message",
            "fork": "Prague", "network": False,
            "python": "venv/bin/python", "pythonPath": "src", "rootEnv": "EELS_ROOT",
            "requiredEnvironment": {
                "PYTHONDONTWRITEBYTECODE": "1", "PYTHONPATH": "${EELS_ROOT}/src",
            },
        },
        "blanc": {
            "artifactEnvelopeSha256": artifacts["envelopeSha256"],
            "commit": commit,
            "creationTemplate": sha_identity(artifacts["creationTemplate"]),
            "evaluatorPath": EVALUATOR_RELATIVE.as_posix(),
            "evaluatorSha256": sha256_file(evaluator),
            "repositoryClean": True,
            "returnedRuntime": sha_identity(artifacts["returnedRuntime"]),
        },
        "implementation": {
            "launcherPath": LAUNCHER_RELATIVE.as_posix(),
            "launcherSha256": sha256_file(launcher),
            "runnerPath": RUNNER_RELATIVE.as_posix(), "runnerSha256": sha256_file(runner),
            "schemaPath": SCHEMA_RELATIVE.as_posix(), "schemaSha256": sha256_file(schema),
        },
        "resultDigest": {
            "algorithm": "sha256",
            "canonicalization": 'json.dumps(parsed, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")',
            "scope": "the entire parsed result with /identity/resultDigest/value replaced by the empty string",
            "value": "",
        },
    }


def write_exclusive(path: Path, document: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(document, indent=2, sort_keys=True) + "\n"
    try:
        with path.open("x") as handle:
            handle.write(payload)
    except FileExistsError:
        die(f"refusing to overwrite immutable result: {path}")
    except OSError as exc:
        die(f"cannot create immutable result {path}: {exc}")


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--eels-root", type=Path,
                        default=Path(os.environ.get("EELS_ROOT", "~/execution-specs")))
    parser.add_argument("--blanc-artifacts", type=Path)
    parser.add_argument("--result-out", type=Path)
    parser.add_argument("--dry-run", action="store_true",
                        help="validate manifest/dependencies and resolve all fixtures; execute nothing")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)
    repo_root = args.repo_root.expanduser().resolve()
    manifest, performance, reference = load_and_validate_campaign(repo_root)
    resolved_count = dry_resolve(manifest, performance)
    if args.dry_run:
        if args.blanc_artifacts or args.result_out:
            die("--dry-run does not accept artifact or result paths")
        print(f"OK — OssifiableProxy differential dry run: {CASE_COUNT} cases; "
              f"{resolved_count} observed accounts; all fixtures/projections resolved; no EELS execution")
        return 0
    if args.blanc_artifacts is None or args.result_out is None:
        die("real execution requires both --blanc-artifacts and --result-out")
    result_out = args.result_out.expanduser().resolve()
    if result_out.exists():
        die(f"refusing to overwrite immutable result: {result_out}")
    commit = verify_clean_blanc(repo_root)
    eels_root = args.eels_root.expanduser().resolve()
    verify_eels(eels_root)
    artifacts_path = args.blanc_artifacts.expanduser().resolve()
    artifacts = parse_blanc_artifacts(artifacts_path)
    reference_template = hex_bytes(reference["artifacts"]["creationTemplate"]["hex"], "reference creation")
    reference_runtime = hex_bytes(reference["artifacts"]["runtime"]["hex"], "reference runtime")
    sides = (
        ArtifactSide("reference", reference_template, reference_runtime),
        ArtifactSide("blanc", artifacts["creationTemplate"], artifacts["returnedRuntime"]),
    )
    fixtures = Fixtures(manifest, performance)
    addresses = observed_addresses(fixtures)
    rows: List[Dict[str, Any]] = []
    for case in manifest["cases"]:
        expected_reference, reference_projection = run_case(case, sides[0], fixtures, addresses)
        expected_blanc, blanc_projection = run_case(case, sides[1], fixtures, addresses)
        if expected_reference != expected_blanc:
            die(f"{case['id']}: side-specific expected projection drifted")
        mismatches = projection_mismatches(expected_reference, reference_projection, blanc_projection)
        rows.append({
            "id": case["id"], "ordinal": case["ordinal"],
            "expected": expected_reference,
            "reference": reference_projection, "blanc": blanc_projection,
            "matches": not mismatches, "mismatches": mismatches,
        })
        if args.verbose:
            print(f"{case['id']} {'MATCH' if not mismatches else 'MISMATCH ' + ','.join(mismatches)}",
                  file=sys.stderr)
    if len(rows) != CASE_COUNT:
        die(f"internal execution count {len(rows)} != {CASE_COUNT}; no result emitted")
    mismatch_count = sum(not row["matches"] for row in rows)
    identity = build_identity(
        repo_root, commit, manifest, repo_root / PERFORMANCE_RELATIVE,
        reference, artifacts,
    )
    result: Dict[str, Any] = {
        "schema": RESULT_FORMAT,
        "identity": identity,
        "summary": {
            "allCasesExecuted": True,
            "allMatched": mismatch_count == 0,
            "caseCount": CASE_COUNT,
            "executedCaseCount": CASE_COUNT,
            "matchedCaseCount": CASE_COUNT - mismatch_count,
            "mismatchCaseCount": mismatch_count,
            "skippedCaseCount": 0,
        },
        "rows": rows,
    }
    seal_result(result)
    validate_result(result, manifest, performance=performance, repo_root=repo_root)
    write_exclusive(result_out, result)
    if mismatch_count:
        print(f"REGRESSION — OssifiableProxy differential: {mismatch_count}/{CASE_COUNT} rows mismatch; "
              f"immutable result written to {result_out}", file=sys.stderr)
        return 1
    print(f"OK — OssifiableProxy differential: {CASE_COUNT}/{CASE_COUNT} rows agree; "
          f"zero skipped; immutable result {identity['resultDigest']['value']} written to {result_out}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except Exception as exc:
        print("REGRESSION — OssifiableProxy differential: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
