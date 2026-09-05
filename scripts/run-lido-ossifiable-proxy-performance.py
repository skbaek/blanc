#!/usr/bin/env python3
"""Generate an immutable 25-cell OssifiableProxy performance ledger.

This runner consumes the frozen v2 performance manifest.  Solidity bytes are
read only from the locked reference document and Blanc bytes are read only
from the strict two-row Lean evaluator envelope.  Every executable cell uses
fresh, side-symmetric EELS Prague state.  A scalar is scoreable only when both
sides match the manifest-derived semantic projection.

The runner deliberately has no EELS imports at module import time so its
``--dry-run`` and evidence validation paths remain static.  Real generation
must use the pinned EELS interpreter and environment and refuses to overwrite
either the ledger or its evidence directory.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, NoReturn, Sequence

import lido_ossifiable_proxy_performance_schema as schema
import eels_semantic_closure


EVALUATOR_RELATIVE = Path("scripts/eval-lido-ossifiable-proxy-artifacts.lean")
RUNNER_RELATIVE = Path("scripts/run-lido-ossifiable-proxy-performance.py")
LAUNCHER_RELATIVE = Path("scripts/run-lido-ossifiable-proxy-performance.sh")
BOOTSTRAP_RELATIVE = Path("scripts/run-isolated-python.py")
LOADER_GUARD_RELATIVE = Path("scripts/eels_semantic_closure.py")
LOADER_LOCK_RELATIVE = Path("scripts/eels-prague-closure.json")
EVIDENCE_CHECKER_RELATIVE = Path("scripts/check-lido-ossifiable-proxy-performance-results.py")
SCHEMA_RELATIVE = Path("scripts/lido_ossifiable_proxy_performance_schema.py")
REFERENCE_RUNTIME_POINTER = "/artifacts/runtime"
REFERENCE_CREATION_POINTER = "/artifacts/creationTemplate"
EVIDENCE_FORMAT = "blanc.lido-ossifiable-proxy.performance-cell-evidence"
DIAGNOSTIC_FORMAT = "blanc.lido-ossifiable-proxy.performance-diagnostics"
EIP170_LIMIT = 24_576
EIP3860_LIMIT = 49_152
CODE_DEPOSIT_GAS_PER_BYTE = 200


class RunnerError(RuntimeError):
    """A generation or evidence-validation failure."""


def die(message: str) -> NoReturn:
    raise RunnerError(message)


def canonical_bytes(value: Any) -> bytes:
    return schema.canonical_bytes(value)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def hex_bytes(value: Any, owner: str) -> bytes:
    if not isinstance(value, str) or re.fullmatch(r"0x(?:[0-9a-f]{2})*", value) is None:
        die(f"{owner} must be lowercase, even-length 0x hex")
    return bytes.fromhex(value[2:])


def address_bytes(value: Any, owner: str) -> bytes:
    raw = hex_bytes(value, owner)
    if len(raw) != 20:
        die(f"{owner} must be exactly 20 bytes")
    return raw


def canonical_address(value: Any, owner: str = "address") -> str:
    return "0x" + address_bytes(value, owner).hex()


def word_hex(value: Any, owner: str) -> str:
    if isinstance(value, int):
        number = value
    elif isinstance(value, str) and value.startswith("0x"):
        raw = hex_bytes(value, owner)
        if len(raw) == 20:
            raw = bytes(12) + raw
        if len(raw) != 32:
            die(f"{owner} cannot be normalized to a 32-byte word")
        return "0x" + raw.hex()
    elif isinstance(value, str) and value.isdigit():
        number = int(value)
    else:
        die(f"{owner} is not an integer, address, or word")
    if number < 0 or number >= 1 << 256:
        die(f"{owner} is outside uint256")
    return "0x" + number.to_bytes(32, "big").hex()


def artifact_identity(raw: bytes) -> dict[str, Any]:
    return {
        "byteLength": len(raw),
        "keccak256": "0x" + schema.keccak256(raw),
        "sha256": sha256_bytes(raw),
    }


def git_output(root: Path, *arguments: str) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), *arguments],
            text=True,
            stderr=subprocess.STDOUT,
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        die(f"cannot inspect git checkout {root}: {exc}")


def verify_clean_blanc(root: Path) -> str:
    commit = git_output(root, "rev-parse", "HEAD")
    if re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        die(f"invalid Blanc commit identity: {commit}")
    if git_output(root, "status", "--porcelain"):
        die("Blanc checkout is dirty; immutable performance identity requires a clean commit")
    return commit


def verify_eels(root: Path) -> None:
    commit = git_output(root, "rev-parse", "HEAD")
    dirty = git_output(root, "status", "--porcelain")
    if commit != schema.EELS_COMMIT or dirty:
        die(f"EELS must be clean at {schema.EELS_COMMIT}; found {commit}, dirty={bool(dirty)}")
    expected_python = (root / "venv/bin/python").resolve()
    if Path(sys.executable).resolve() != expected_python:
        die(f"runner must use pinned EELS interpreter {expected_python}; found {sys.executable}")
    expected_source = (root / "src").resolve()
    if os.environ.get("PYTHONDONTWRITEBYTECODE") != "1" or \
            Path(os.environ.get("PYTHONPATH", "")).resolve() != expected_source:
        die("EELS requires PYTHONDONTWRITEBYTECODE=1 and exact PYTHONPATH=<EELS_ROOT>/src")
    eels_semantic_closure.assert_prague_environment(
        die, checkout_root=root
    )
    import ethereum
    module_path = Path(ethereum.__file__).resolve()
    if not module_path.is_relative_to(expected_source):
        die(f"ethereum package was not imported from pinned EELS root: {module_path}")


def parse_blanc_artifacts(path: Path) -> dict[str, Any]:
    """Parse exactly ``creation-template`` then ``returned-runtime``."""
    try:
        lines = path.read_text().splitlines()
    except OSError as exc:
        die(f"cannot read Blanc evaluator envelope {path}: {exc}")
    labels = ("creation-template", "returned-runtime")
    if len(lines) != 2:
        die(f"Blanc evaluator must emit exactly two rows, got {len(lines)}")
    parsed: dict[str, bytes] = {}
    for line, label in zip(lines, labels):
        parts = line.split()
        if len(parts) != 3 or parts[0] != label:
            die(f"expected evaluator row '{label} <byteLength> <lowercase hex>'")
        if re.fullmatch(r"0|[1-9][0-9]*", parts[1]) is None or \
                re.fullmatch(r"(?:[0-9a-f]{2})+", parts[2]) is None:
            die(f"malformed evaluator row: {label}")
        raw = bytes.fromhex(parts[2])
        if len(raw) != int(parts[1]):
            die(f"evaluator length mismatch: {label}")
        parsed[label] = raw
    creation = parsed["creation-template"]
    runtime = parsed["returned-runtime"]
    if not runtime or len(creation) <= len(runtime) or not creation.endswith(runtime):
        die("returned-runtime must be a proper nonempty suffix of creation-template")
    if len(creation) > EIP3860_LIMIT or len(runtime) > EIP170_LIMIT:
        die("Blanc artifacts exceed EIP-3860 or EIP-170")
    return {
        "creationTemplate": creation,
        "returnedRuntime": runtime,
        "envelopeSha256": sha256_file(path),
    }


def load_campaign(root: Path) -> tuple[dict[str, Any], dict[str, Any], bytes]:
    manifest_path = root / schema.MANIFEST_RELATIVE
    _, manifest_value = schema.load_json(manifest_path, "performance manifest")
    manifest = schema.validate_manifest_schema(
        manifest_value,
        root=root,
        enforce_frozen_digest=True,
        validate_external=True,
    )
    lock_path = root / schema.REFERENCE_LOCK_RELATIVE
    lock_raw = lock_path.read_bytes()
    if sha256_bytes(lock_raw) != schema.REFERENCE_LOCK_SHA256:
        die("reference lock SHA-256 differs from the frozen campaign")
    lock = schema.strict_json(lock_raw, "reference lock")
    return manifest, lock, lock_raw


@dataclass(frozen=True)
class ArtifactSide:
    name: str
    creation_template: bytes
    returned_runtime: bytes


class Fixtures:
    def __init__(self, manifest: Mapping[str, Any]):
        self.manifest = manifest
        self.values = manifest["fixtures"]
        self.zero_word = "0x" + "00" * 32
        self.slot_names = {
            "implementation": schema.IMPLEMENTATION_SLOT,
            "admin": schema.ADMIN_SLOT,
            "fixture": word_hex(self.values["values"]["fixture-slot"], "fixture slot"),
        }

    def named(self, section: str, name: Any, owner: str) -> Any:
        rows = self.values[section]
        if not isinstance(name, str) or name not in rows:
            die(f"{owner}: unresolved {section} fixture {name!r}")
        return rows[name]

    def address(self, name: Any, owner: str) -> str:
        return canonical_address(self.named("addresses", name, owner), owner)

    def calldata(self, name: Any, owner: str) -> bytes:
        return hex_bytes(self.named("calldata", name, owner)["hex"], owner)

    def code(self, name: Any, owner: str) -> bytes:
        return hex_bytes(self.named("mockImplementations", name, owner)["hex"], owner)

    def scalar(self, name: Any, owner: str) -> int:
        value = self.named("values", name, owner)
        if isinstance(value, str) and value.startswith("0x"):
            return int.from_bytes(hex_bytes(value, owner), "big")
        try:
            parsed = int(value)
        except (TypeError, ValueError) as exc:
            raise RunnerError(f"{owner}: invalid scalar {value!r}") from exc
        if parsed < 0 or parsed >= 1 << 256:
            die(f"{owner}: scalar is outside uint256")
        return parsed

    def constructor_arguments(self, name: Any, owner: str) -> bytes:
        return hex_bytes(self.named("constructorTuples", name, owner)["abiArgumentsHex"], owner)

    def proxy_slots(self, name: Any, owner: str) -> dict[str, str]:
        state = self.named("proxyStates", name, owner)
        default = word_hex(state["storageDefault"], f"{owner} default")
        result = {slot: default for slot in self.slot_names.values()}
        for slot, value in state["storageOverrides"].items():
            if slot in result:
                result[slot] = word_hex(value, f"{owner} slot {slot}")
        return result

    def access_set(self, name: Any, owner: str) -> Mapping[str, Any]:
        return self.named("accessSets", name, owner)

    def observed_addresses(self) -> tuple[str, ...]:
        return tuple(sorted({
            canonical_address(value, f"address fixture {name}")
            for name, value in self.values["addresses"].items()
            if name != "proxyTargetDerivation"
        }))


def dry_resolve(manifest: Mapping[str, Any]) -> int:
    fixtures = Fixtures(manifest)
    addresses = fixtures.observed_addresses()
    for cell in manifest["cells"]:
        world = cell["world"]
        if world["kind"] == "artifact":
            fixtures.named("artifactBindings", world["artifactBinding"], cell["id"])
            if "constructorTuple" in world:
                fixtures.constructor_arguments(world["constructorTuple"], cell["id"])
            continue
        fixtures.address(world["caller"], f"{cell['id']} caller")
        fixtures.address(world["target"], f"{cell['id']} target")
        fixtures.scalar(world["gasAllowance"], f"{cell['id']} gas")
        fixtures.scalar(world["value"], f"{cell['id']} value")
        fixtures.access_set(world["accessSet"], f"{cell['id']} access set")
        fixtures.named("expectedSemantics", world["expected"], f"{cell['id']} expected")
        for account in world["implementationAccounts"]:
            fixtures.address(account["address"], f"{cell['id']} implementation")
            fixtures.code(account["code"], f"{cell['id']} implementation code")
        if world["kind"] == "direct-create-message":
            fixtures.constructor_arguments(world["constructorTuple"], cell["id"])
            if fixtures.calldata(world["messageData"], f"{cell['id']} message data"):
                die(f"{cell['id']}: direct CREATE message data must be empty")
        else:
            fixtures.calldata(world["calldata"], f"{cell['id']} calldata")
            fixtures.proxy_slots(world["proxyState"], f"{cell['id']} proxy state")
        for name in world.get("absentAccounts", []):
            fixtures.address(name, f"{cell['id']} absent account")
        if world["kind"] == "direct-create-message":
            pre_slots = {slot: fixtures.zero_word for slot in fixtures.slot_names.values()}
        else:
            pre_slots = fixtures.proxy_slots(
                world["proxyState"], f"{cell['id']} expected prestate"
            )
        projection = expected_projection(cell, fixtures, pre_slots, addresses)
        if set(projection) != {
            "account", "delegatecalls", "eth", "logs", "returndata", "status", "storage",
        }:
            die(f"{cell['id']}: expected semantic projection is incomplete")
    return len(addresses)


def _set_account(state: Any, address: str, nonce: int, balance: int, code: bytes) -> None:
    from ethereum.prague.fork_types import Account, Address
    from ethereum.prague.state import set_account
    from ethereum_types.bytes import Bytes
    from ethereum_types.numeric import U256, Uint

    set_account(
        state,
        Address(address_bytes(address, "account address")),
        Account(Uint(nonce), U256(balance), Bytes(code)),
    )


def _build_state(cell: Mapping[str, Any], side: ArtifactSide, fixtures: Fixtures) -> Any:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import State, get_account_optional, set_storage
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256

    state = State()
    world = cell["world"]
    caller = fixtures.address(world["caller"], f"{cell['id']} caller")
    caller_template = fixtures.values["accountTemplates"]["caller"]
    caller_nonce = int(world.get("callerNonce", caller_template["nonce"]))
    _set_account(state, caller, caller_nonce, int(caller_template["balance"]), b"")
    target = fixtures.address(world["target"], f"{cell['id']} target")
    if world["kind"] == "direct-call-message":
        proxy = fixtures.named("proxyStates", world["proxyState"], f"{cell['id']} state")
        _set_account(
            state, target, int(proxy["accountNonce"]), int(proxy["accountBalance"]),
            side.returned_runtime,
        )
        for slot, value in fixtures.proxy_slots(world["proxyState"], f"{cell['id']} state").items():
            set_storage(
                state,
                Address(address_bytes(target, "proxy target")),
                Bytes32(hex_bytes(slot, "proxy slot")),
                U256(int(value, 16)),
            )
    elif world.get("targetInitiallyAbsent") is not True:
        die(f"{cell['id']}: CREATE target must begin absent")

    implementation_template = fixtures.values["accountTemplates"]["mock-implementation"]
    for account in world["implementationAccounts"]:
        address = fixtures.address(account["address"], f"{cell['id']} implementation")
        _set_account(
            state,
            address,
            int(implementation_template["nonce"]),
            int(implementation_template["balance"]),
            fixtures.code(account["code"], f"{cell['id']} implementation code"),
        )
    for name in world.get("absentAccounts", []):
        address = fixtures.address(name, f"{cell['id']} absent account")
        if get_account_optional(state, Address(address_bytes(address, "absent account"))) is not None:
            die(f"{cell['id']}: required absent account was materialized")
    return state


def _environments(
    state: Any,
    caller: str,
    cell: Mapping[str, Any],
    fixtures: Fixtures,
    gas: int,
) -> tuple[Any, Any, set[Any], set[Any]]:
    from ethereum.crypto.hash import Hash32
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import TransientStorage
    from ethereum.prague.vm import BlockEnvironment, TransactionEnvironment
    from ethereum_types.bytes import Bytes32
    from ethereum_types.numeric import U256, U64, Uint

    block_spec = fixtures.values["blockEnvironment"]
    access = fixtures.access_set(cell["world"]["accessSet"], f"{cell['id']} access set")
    accessed_addresses = {
        Address(address_bytes(value, "accessed address"))
        for value in access["accessedAddresses"]
    }
    accessed_storage = {
        (
            Address(address_bytes(row["address"], "accessed storage address")),
            Bytes32(hex_bytes(row["key"], "accessed storage key")),
        )
        for row in access["accessedStorageKeys"]
    }
    block = BlockEnvironment(
        chain_id=U64(int(block_spec["chainId"])),
        state=state,
        block_gas_limit=Uint(int(block_spec["blockGasLimit"])),
        block_hashes=[
            Hash32(hex_bytes(value, "block hash")) for value in block_spec["blockHashes"]
        ],
        coinbase=Address(address_bytes(block_spec["coinbase"], "coinbase")),
        number=Uint(int(block_spec["number"])),
        base_fee_per_gas=Uint(int(block_spec["baseFeePerGas"])),
        time=U256(int(block_spec["timestamp"])),
        prev_randao=Bytes32(hex_bytes(block_spec["prevRandao"], "prevRandao")),
        excess_blob_gas=U64(int(block_spec["excessBlobGas"])),
        parent_beacon_block_root=Hash32(
            hex_bytes(block_spec["parentBeaconBlockRoot"], "beacon root")
        ),
    )
    tx = TransactionEnvironment(
        origin=Address(address_bytes(caller, "origin")),
        gas_price=Uint(0),
        gas=Uint(gas),
        access_list_addresses=set(),
        access_list_storage_keys=set(),
        transient_storage=TransientStorage(),
        blob_versioned_hashes=(),
        authorizations=(),
        index_in_block=None,
        tx_hash=None,
        traces=[],
    )
    return block, tx, accessed_addresses, accessed_storage


def _outcome(error: Any) -> str:
    if error is None:
        return "success"
    return "revert" if type(error).__name__ == "Revert" else "exception:" + type(error).__name__


def _child_outcome(error: Any) -> str:
    if error is None:
        return "success"
    name = type(error).__name__
    return "revert" if name == "Revert" else "exception:" + name


class PerformanceTracer:
    """Capture delegatecall observations and a compact opcode/cost profile."""

    def __init__(self, profile: bool):
        self.profile_enabled = profile
        self.delegatecalls: list[dict[str, Any]] = []
        self.pending_delegatecalls: dict[int, list[int]] = defaultdict(list)
        self.active_ops: dict[int, list[tuple[str, int, int, str, int]]] = defaultdict(list)
        self.profile_rows: dict[tuple[int, str, int, str], list[int]] = defaultdict(
            lambda: [0, 0]
        )
        self.sequence = hashlib.sha256()
        self.opcode_count = 0
        self.unframed_charges: Counter[str] = Counter()

    @staticmethod
    def _memory_read(memory: bytearray, start: int, size: int) -> bytes:
        if size > 1_100_000:
            die(f"refusing oversized traced DELEGATECALL input: {size}")
        available = bytes(memory[start:start + size])
        return available + bytes(size - len(available))

    @staticmethod
    def _code_address(evm: Any) -> str:
        value = evm.message.code_address
        if value is None:
            return "create-initcode"
        return "0x" + bytes(value).hex()

    def _finish_op(self, evm: Any) -> None:
        stack = self.active_ops.get(id(evm), [])
        if not stack:
            return
        name, before, depth, code_address, pc = stack.pop()
        delta = before - int(evm.gas_left)
        row = self.profile_rows[(depth, code_address, pc, name)]
        row[0] += 1
        row[1] += delta

    def __call__(self, evm: Any, event: Any, /, **_kw: Any) -> None:
        from ethereum.trace import GasAndRefund, OpEnd, OpException, OpStart

        if isinstance(event, OpStart):
            name = event.op.name
            if self.profile_enabled:
                depth = int(evm.message.depth)
                code_address = self._code_address(evm)
                pc = int(evm.pc)
                self.active_ops[id(evm)].append(
                    (name, int(evm.gas_left), depth, code_address, pc)
                )
                self.sequence.update(f"{depth}:{code_address}:{pc}:{name}\n".encode())
                self.opcode_count += 1
            if name == "DELEGATECALL":
                if len(evm.stack) < 6:
                    die("traced DELEGATECALL stack underflow")
                code_address = int(evm.stack[-2]).to_bytes(32, "big")[-20:]
                input_offset, input_size = int(evm.stack[-3]), int(evm.stack[-4])
                row = {
                    "caller": "0x" + bytes(evm.message.caller).hex(),
                    "childReturndata": None,
                    "childStatus": None,
                    "codeAddress": "0x" + code_address.hex(),
                    "input": "0x" + self._memory_read(
                        evm.memory, input_offset, input_size
                    ).hex(),
                    "opcode": "DELEGATECALL",
                    "source": "0x" + bytes(evm.message.current_target).hex(),
                    "storageOwner": "0x" + bytes(evm.message.current_target).hex(),
                    "value": str(int(evm.message.value)),
                    "_childError": None,
                }
                self.delegatecalls.append(row)
                self.pending_delegatecalls[id(evm)].append(len(self.delegatecalls) - 1)
            return

        if isinstance(event, GasAndRefund):
            if self.profile_enabled and not self.active_ops.get(id(evm)):
                phase = f"depth={int(evm.message.depth)}:{self._code_address(evm)}"
                self.unframed_charges[phase] += int(event.gas_cost)
            return

        if isinstance(event, OpException):
            if self.profile_enabled:
                self._finish_op(evm)
            own_pending = self.pending_delegatecalls.get(id(evm), [])
            if own_pending:
                index = own_pending.pop()
                row = self.delegatecalls[index]
                row["childStatus"] = _child_outcome(event.error)
                row["childReturndata"] = "0x" + bytes(evm.return_data).hex()
                del row["_childError"]
            if evm.message.parent_evm is not None:
                pending = self.pending_delegatecalls.get(id(evm.message.parent_evm), [])
                if pending:
                    self.delegatecalls[pending[-1]]["_childError"] = event.error
            return

        if isinstance(event, OpEnd):
            if self.profile_enabled:
                self._finish_op(evm)
            pending = self.pending_delegatecalls.get(id(evm), [])
            if not pending:
                return
            index = pending.pop()
            row = self.delegatecalls[index]
            if int(evm.stack[-1]):
                row["childStatus"] = "success"
            elif row["_childError"] is not None:
                row["childStatus"] = _child_outcome(row["_childError"])
            else:
                die("failed DELEGATECALL had no traced child outcome")
            row["childReturndata"] = "0x" + bytes(evm.return_data).hex()
            del row["_childError"]

    def finish_delegatecalls(self) -> list[dict[str, Any]]:
        if any(self.pending_delegatecalls.values()) or any(
            row.get("childStatus") is None for row in self.delegatecalls
        ):
            die("DELEGATECALL trace contains an unmatched opcode")
        return self.delegatecalls

    def finish_profile(self) -> dict[str, Any]:
        if any(self.active_ops.values()):
            die("opcode profile contains an unmatched opcode")
        rows = [
            {
                "codeAddress": code,
                "count": counts[0],
                "depth": depth,
                "netGasDelta": counts[1],
                "opcode": opcode,
                "pc": pc,
            }
            for (depth, code, pc, opcode), counts in sorted(self.profile_rows.items())
        ]
        return {
            "notes": (
                "netGasDelta is gas-before minus gas-after at each opcode boundary; "
                "CALL-family parent rows include child gas consumption and therefore must not "
                "be summed with child-depth rows"
            ),
            "opcodeCount": self.opcode_count,
            "opcodeSequenceSha256": self.sequence.hexdigest(),
            "rows": rows,
            "unframedGasCharges": [
                {"gas": gas, "phase": phase}
                for phase, gas in sorted(self.unframed_charges.items())
            ],
        }


def _balance(state: Any, address: str) -> int:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account_optional

    account = get_account_optional(state, Address(address_bytes(address, "balance address")))
    return 0 if account is None else int(account.balance)


def _target_projection(state: Any, target: str, side: ArtifactSide, fixtures: Fixtures) -> dict[str, Any]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account_optional, get_storage
    from ethereum_types.bytes import Bytes32

    address = Address(address_bytes(target, "target address"))
    account = get_account_optional(state, address)
    slots = {
        slot: "0x" + int(get_storage(
            state, address, Bytes32(hex_bytes(slot, "storage slot"))
        )).to_bytes(32, "big").hex()
        for slot in fixtures.slot_names.values()
    }
    if account is None:
        account_projection = {"code": "absent", "nonce": None}
    else:
        code = bytes(account.code)
        account_projection = {
            "code": "own-returned-runtime" if code == side.returned_runtime else artifact_identity(code),
            "nonce": int(account.nonce),
        }
    return {
        "account": account_projection,
        "storage": {"slots": slots, "targetExists": account is not None},
    }


def _normalized_logs(logs: Iterable[Any]) -> list[dict[str, Any]]:
    return [{
        "address": "0x" + bytes(log.address).hex(),
        "data": "0x" + bytes(log.data).hex(),
        "topics": ["0x" + bytes(topic).hex() for topic in log.topics],
    } for log in logs]


def _execute(
    cell: Mapping[str, Any],
    side: ArtifactSide,
    fixtures: Fixtures,
    state: Any,
    gas: int,
    *,
    profile: bool,
) -> dict[str, Any]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.vm import Message
    from ethereum.prague.vm.interpreter import process_create_message, process_message_call
    from ethereum.trace import set_evm_trace
    from ethereum_types.bytes import Bytes, Bytes0
    from ethereum_types.numeric import U256, Uint

    if process_message_call.__module__ != "ethereum.prague.vm.interpreter" or \
            process_create_message.__module__ != "ethereum.prague.vm.interpreter":
        die("imported EELS entrypoint identity drifted")
    world = cell["world"]
    caller = fixtures.address(world["caller"], f"{cell['id']} caller")
    target = fixtures.address(world["target"], f"{cell['id']} target")
    block, tx, accessed_addresses, accessed_storage = _environments(
        state, caller, cell, fixtures, gas
    )
    tracer = PerformanceTracer(profile)
    previous = set_evm_trace(tracer)
    try:
        if world["kind"] == "direct-create-message":
            arguments = fixtures.constructor_arguments(world["constructorTuple"], cell["id"])
            message_data = fixtures.calldata(world["messageData"], cell["id"])
            initcode = side.creation_template + arguments
            if len(initcode) > EIP3860_LIMIT:
                die(f"{cell['id']}/{side.name}: full CREATE input exceeds EIP-3860")
            message = Message(
                block_env=block,
                tx_env=tx,
                caller=Address(address_bytes(caller, "caller")),
                target=Bytes0(b""),
                current_target=Address(address_bytes(target, "target")),
                gas=Uint(gas),
                value=U256(fixtures.scalar(world["value"], cell["id"])),
                data=Bytes(message_data),
                code_address=None,
                code=Bytes(initcode),
                depth=Uint(0),
                should_transfer_value=True,
                is_static=False,
                accessed_addresses=accessed_addresses,
                accessed_storage_keys=accessed_storage,
                disable_precompiles=False,
                parent_evm=None,
            )
            output = process_create_message(message)
            status = _outcome(output.error)
            returndata = bytes(output.output)
            logs = () if output.error is not None else output.logs
            gas_left = int(output.gas_left)
            refund_counter = int(output.refund_counter)
            full_create_input = initcode
        else:
            calldata = fixtures.calldata(world["calldata"], cell["id"])
            message = Message(
                block_env=block,
                tx_env=tx,
                caller=Address(address_bytes(caller, "caller")),
                target=Address(address_bytes(target, "target")),
                current_target=Address(address_bytes(target, "target")),
                gas=Uint(gas),
                value=U256(fixtures.scalar(world["value"], cell["id"])),
                data=Bytes(calldata),
                code_address=Address(address_bytes(target, "target")),
                code=Bytes(side.returned_runtime),
                depth=Uint(0),
                should_transfer_value=True,
                is_static=False,
                accessed_addresses=accessed_addresses,
                accessed_storage_keys=accessed_storage,
                disable_precompiles=False,
                parent_evm=None,
            )
            output = process_message_call(message)
            status = _outcome(output.error)
            returndata = bytes(output.return_data)
            logs = output.logs
            gas_left = int(output.gas_left)
            refund_counter = int(output.refund_counter)
            full_create_input = None
    finally:
        set_evm_trace(previous)
    return {
        "delegatecalls": tracer.finish_delegatecalls(),
        "fullCreateInput": full_create_input,
        "gasLeft": gas_left,
        "gasUsed": gas - gas_left,
        "logs": _normalized_logs(logs),
        "opcodeProfile": tracer.finish_profile() if profile else None,
        "refundCounterExcluded": refund_counter,
        "returndata": returndata,
        "status": status,
    }


def _event_log(
    fixtures: Fixtures,
    target: str,
    name: str,
    arguments: Sequence[str],
) -> dict[str, Any]:
    event = fixtures.values["events"][name]
    topics = [event["topic0"]]
    data_words: list[bytes] = []
    for indexed, argument in zip(event["indexed"], arguments):
        word = bytes.fromhex(word_hex(argument, f"{name} argument")[2:])
        if indexed:
            topics.append("0x" + word.hex())
        else:
            data_words.append(word)
    return {"address": target, "data": "0x" + b"".join(data_words).hex(), "topics": topics}


def _expected_logs(cell: Mapping[str, Any], fixtures: Fixtures) -> list[dict[str, Any]]:
    expected = cell["world"]["expected"]
    target = fixtures.address(cell["world"]["target"], f"{cell['id']} target")
    address = lambda name: fixtures.address(name, f"{cell['id']} event address")
    if expected == "create-empty-success" or expected == "create-nonempty-setup-success":
        return [
            _event_log(fixtures, target, "Upgraded(address)", [address("canonical-implementation")]),
            _event_log(fixtures, target, "AdminChanged(address,address)", [
                address("zero"), address("canonical-admin"),
            ]),
        ]
    if expected == "change-admin-success":
        return [_event_log(fixtures, target, "AdminChanged(address,address)", [
            address("control-admin"), address("new-admin"),
        ])]
    if expected in {
        "upgrade-success", "upgrade-empty-false-skip", "upgrade-nonempty-setup-success",
        "upgrade-empty-forced-setup-success",
    }:
        return [_event_log(
            fixtures, target, "Upgraded(address)", [address("new-implementation")]
        )]
    if expected == "ossify-success":
        return [
            _event_log(fixtures, target, "AdminChanged(address,address)", [
                address("control-admin"), address("zero"),
            ]),
            _event_log(fixtures, target, "ProxyOssified()", []),
        ]
    return []


def _expected_delegatecalls(cell: Mapping[str, Any], fixtures: Fixtures) -> list[dict[str, Any]]:
    world = cell["world"]
    expected = world["expected"]
    target = fixtures.address(world["target"], f"{cell['id']} target")
    caller = fixtures.address(world["caller"], f"{cell['id']} caller")
    specifications: dict[str, tuple[str, str, str, str]] = {
        "create-nonempty-setup-success": (
            "canonical-implementation", "setup-data-32", "success", "empty",
        ),
        "fallback-echo-success-32": (
            "canonical-implementation", "fallback-32", "success", "fallback-32",
        ),
        "fallback-empty-revert-32": (
            "canonical-implementation", "fallback-32", "revert", "empty",
        ),
        "fallback-echo-success-256": (
            "canonical-implementation", "fallback-256", "success", "fallback-256",
        ),
        "fallback-echo-revert-256": (
            "canonical-implementation", "fallback-256", "revert", "fallback-256",
        ),
        "receive-empty-success": (
            "canonical-implementation", "empty", "success", "empty",
        ),
        "upgrade-nonempty-setup-success": (
            "new-implementation", "setup-data-32", "success", "empty",
        ),
        "upgrade-empty-forced-setup-success": (
            "new-implementation", "empty", "success", "empty",
        ),
        "upgrade-child-revert-rollback": (
            "new-implementation", "setup-data-32", "revert", "setup-data-32",
        ),
    }
    if expected not in specifications:
        return []
    code_name, input_name, status, output_name = specifications[expected]
    return [{
        "caller": caller,
        "childReturndata": "0x" + fixtures.calldata(output_name, cell["id"]).hex(),
        "childStatus": status,
        "codeAddress": fixtures.address(code_name, f"{cell['id']} child code"),
        "input": "0x" + fixtures.calldata(input_name, cell["id"]).hex(),
        "opcode": "DELEGATECALL",
        "source": target,
        "storageOwner": target,
        "value": str(fixtures.scalar(world["value"], f"{cell['id']} child value")),
    }]


def _expected_storage(
    cell: Mapping[str, Any],
    fixtures: Fixtures,
    pre_slots: Mapping[str, str],
) -> dict[str, Any]:
    expected = cell["world"]["expected"]
    slots = dict(pre_slots)
    implementation = fixtures.slot_names["implementation"]
    admin = fixtures.slot_names["admin"]
    fixture = fixtures.slot_names["fixture"]
    address_word = lambda name: word_hex(
        fixtures.address(name, f"{cell['id']} expected address"), cell["id"]
    )
    if expected in {"create-empty-success", "create-nonempty-setup-success"}:
        slots = {slot: fixtures.zero_word for slot in fixtures.slot_names.values()}
        slots[implementation] = address_word("canonical-implementation")
        slots[admin] = address_word("canonical-admin")
        if expected == "create-nonempty-setup-success":
            slots[fixture] = word_hex(
                fixtures.values["values"]["setup-data-32"], f"{cell['id']} setup value"
            )
    elif expected == "change-admin-success":
        slots[admin] = address_word("new-admin")
    elif expected in {
        "upgrade-success", "upgrade-empty-false-skip", "upgrade-nonempty-setup-success",
        "upgrade-empty-forced-setup-success",
    }:
        slots[implementation] = address_word("new-implementation")
        if expected == "upgrade-nonempty-setup-success":
            slots[fixture] = word_hex(
                fixtures.values["values"]["setup-data-32"], f"{cell['id']} setup value"
            )
        elif expected == "upgrade-empty-forced-setup-success":
            slots[fixture] = word_hex(
                fixtures.values["values"]["empty-setup-value"], f"{cell['id']} empty value"
            )
    elif expected == "ossify-success":
        slots[admin] = fixtures.zero_word
    return {"slots": slots, "targetExists": True}


def _expected_returndata(cell: Mapping[str, Any], fixtures: Fixtures) -> str:
    expected = fixtures.values["expectedSemantics"][cell["world"]["expected"]]["returndata"]
    if expected == "own-returned-runtime":
        return expected
    if expected in fixtures.values["calldata"]:
        return "0x" + fixtures.calldata(expected, f"{cell['id']} expected returndata").hex()
    return "0x" + hex_bytes(expected, f"{cell['id']} expected returndata").hex()


def expected_projection(
    cell: Mapping[str, Any],
    fixtures: Fixtures,
    pre_slots: Mapping[str, str],
    addresses: Sequence[str],
) -> dict[str, Any]:
    world = cell["world"]
    semantic = fixtures.values["expectedSemantics"][world["expected"]]
    eth = {address: "0" for address in addresses}
    if world["expected"] == "receive-empty-success":
        caller = fixtures.address(world["caller"], f"{cell['id']} caller")
        target = fixtures.address(world["target"], f"{cell['id']} target")
        value = fixtures.scalar(world["value"], f"{cell['id']} value")
        eth[caller], eth[target] = str(-value), str(value)
    return {
        "account": {"code": "own-returned-runtime", "nonce": 1},
        "delegatecalls": _expected_delegatecalls(cell, fixtures),
        "eth": eth,
        "logs": _expected_logs(cell, fixtures),
        "returndata": _expected_returndata(cell, fixtures),
        "status": semantic["status"],
        "storage": _expected_storage(cell, fixtures, pre_slots),
    }


def execute_projection(
    cell: Mapping[str, Any],
    side: ArtifactSide,
    fixtures: Fixtures,
    addresses: Sequence[str],
    gas: int,
    *,
    profile: bool,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, str]]:
    state = _build_state(cell, side, fixtures)
    target = fixtures.address(cell["world"]["target"], f"{cell['id']} target")
    before = _target_projection(state, target, side, fixtures)
    pre_balances = {address: _balance(state, address) for address in addresses}
    execution = _execute(cell, side, fixtures, state, gas, profile=profile)
    after = _target_projection(state, target, side, fixtures)
    returndata = "0x" + execution["returndata"].hex()
    if cell["world"]["kind"] == "direct-create-message" and execution["status"] == "success":
        if execution["returndata"] == side.returned_runtime:
            returndata = "own-returned-runtime"
    projection = {
        "account": after["account"],
        "delegatecalls": execution["delegatecalls"],
        "eth": {
            address: str(_balance(state, address) - pre_balances[address])
            for address in addresses
        },
        "logs": execution["logs"],
        "returndata": returndata,
        "status": execution["status"],
        "storage": after["storage"],
    }
    return projection, execution, before["storage"]["slots"]


def projection_mismatches(expected: Mapping[str, Any], actual: Mapping[str, Any]) -> list[str]:
    return [key for key in expected if expected[key] != actual.get(key)]


def completion_threshold(
    cell: Mapping[str, Any],
    side: ArtifactSide,
    fixtures: Fixtures,
    addresses: Sequence[str],
    adequate_gas: int,
    expected: Mapping[str, Any],
) -> dict[str, Any]:
    def agrees(gas: int) -> tuple[bool, str]:
        projection, execution, _ = execute_projection(
            cell, side, fixtures, addresses, gas, profile=False
        )
        return projection == expected, execution["status"]

    high_agrees, high_status = agrees(adequate_gas)
    if not high_agrees:
        die(f"{cell['id']}/{side.name}: adequate gas does not satisfy the semantic projection")
    low, high = 0, adequate_gas
    while low < high:
        middle = (low + high) // 2
        middle_agrees, _ = agrees(middle)
        if middle_agrees:
            high = middle
        else:
            low = middle + 1
    threshold = low
    threshold_agrees, threshold_status = agrees(threshold)
    if not threshold_agrees:
        die(f"{cell['id']}/{side.name}: threshold search did not converge on completion")
    if threshold == 0:
        minus = None
    else:
        minus_agrees, minus_status = agrees(threshold - 1)
        if minus_agrees:
            die(f"{cell['id']}/{side.name}: threshold-minus-one unexpectedly completes")
        minus = {
            "gas": threshold - 1,
            "semanticAgreement": False,
            "status": minus_status,
        }
    return {
        "adequateGas": adequate_gas,
        "adequateStatus": high_status,
        "method": "deterministic binary search plus threshold/threshold-minus-one replay",
        "thresholdGas": threshold,
        "thresholdStatus": threshold_status,
        "thresholdMinusOne": minus,
    }


def _reference_artifacts(lock: Mapping[str, Any]) -> tuple[bytes, bytes]:
    creation_row, creation = schema._validate_artifact_row(
        schema.resolve_json_pointer(lock, REFERENCE_CREATION_POINTER, "reference creation"),
        "reference creation",
    )
    runtime_row, runtime = schema._validate_artifact_row(
        schema.resolve_json_pointer(lock, REFERENCE_RUNTIME_POINTER, "reference runtime"),
        "reference runtime",
    )
    if creation_row["byteLength"] > EIP3860_LIMIT or runtime_row["byteLength"] > EIP170_LIMIT:
        die("reference artifact exceeds EIP-3860 or EIP-170")
    return creation, runtime


def _implementation_identity(root: Path) -> dict[str, str]:
    paths = {
        "bootstrapSha256": root / BOOTSTRAP_RELATIVE,
        "evidenceCheckerSha256": root / EVIDENCE_CHECKER_RELATIVE,
        "evaluatorSha256": root / EVALUATOR_RELATIVE,
        "launcherSha256": root / LAUNCHER_RELATIVE,
        "loaderGuardSha256": root / LOADER_GUARD_RELATIVE,
        "loaderLockSha256": root / LOADER_LOCK_RELATIVE,
        "runnerSha256": root / RUNNER_RELATIVE,
        "schemaSha256": root / SCHEMA_RELATIVE,
    }
    for path in paths.values():
        if not path.is_file():
            die(f"identity-owned implementation file is missing: {path}")
    return {name: sha256_file(path) for name, path in paths.items()}


def _cell_evidence(
    *,
    root: Path,
    manifest: Mapping[str, Any],
    cell: Mapping[str, Any],
    stage: str,
    predecessor: str | None,
    candidate_commit: str,
    implementation_identity: Mapping[str, str],
    envelope_sha256: str,
    reference_lock_sha256: str,
    reference_side: ArtifactSide,
    blanc_side: ArtifactSide,
    fixtures: Fixtures,
    addresses: Sequence[str],
) -> tuple[dict[str, Any], dict[str, Any]]:
    cell_id = cell["id"]
    common = {
        "campaignManifestDigest": schema.MANIFEST_DIGEST,
        "cell": copy.deepcopy(cell),
        "format": EVIDENCE_FORMAT,
        "identities": {
            "candidateArtifacts": {
                "creationTemplate": artifact_identity(blanc_side.creation_template),
                "returnedRuntime": artifact_identity(blanc_side.returned_runtime),
            },
            "candidateCommit": candidate_commit,
            "eelsCommit": schema.EELS_COMMIT,
            "evaluatorEnvelopeSha256": envelope_sha256,
            "implementation": dict(implementation_identity),
            "referenceArtifacts": {
                "creationTemplate": artifact_identity(reference_side.creation_template),
                "returnedRuntime": artifact_identity(reference_side.returned_runtime),
            },
            "referenceLockSha256": reference_lock_sha256,
        },
        "predecessorResultSha256": predecessor,
        "schema": 1,
        "stage": stage,
    }
    if cell_id in {"A1", "A2"}:
        artifact_name = "returnedRuntime" if cell_id == "A1" else "creationTemplate"
        reference_raw = (
            reference_side.returned_runtime if cell_id == "A1" else reference_side.creation_template
        )
        blanc_raw = blanc_side.returned_runtime if cell_id == "A1" else blanc_side.creation_template
        evidence = {
            **common,
            "measurement": {
                "blancValue": len(blanc_raw),
                "formula": "exact artifact byte length",
                "referenceValue": len(reference_raw),
                "unit": "bytes",
            },
            "semantics": {
                "agreement": True,
                "artifact": artifact_name,
                "blancIdentity": artifact_identity(blanc_raw),
                "mismatches": [],
                "referenceIdentity": artifact_identity(reference_raw),
            },
            "sideExecutions": None,
        }
        values = {
            "agreement": True,
            "blanc": len(blanc_raw),
            "reference": len(reference_raw),
        }
        return evidence, values

    adequate_gas = fixtures.scalar(cell["world"]["gasAllowance"], f"{cell_id} gas")
    side_rows: dict[str, Any] = {}
    projections: dict[str, Any] = {}
    expected: dict[str, Any] | None = None
    for side in (reference_side, blanc_side):
        projection, execution, pre_slots = execute_projection(
            cell, side, fixtures, addresses, adequate_gas, profile=True
        )
        side_expected = expected_projection(cell, fixtures, pre_slots, addresses)
        if expected is None:
            expected = side_expected
        elif expected != side_expected:
            die(f"{cell_id}: side-specific expected projection drifted")
        projections[side.name] = projection
        side_rows[side.name] = {
            "completionThreshold": completion_threshold(
                cell, side, fixtures, addresses, adequate_gas, side_expected
            ),
            "fullCreateInput": None if execution["fullCreateInput"] is None else {
                "byteLength": len(execution["fullCreateInput"]),
                "hex": "0x" + execution["fullCreateInput"].hex(),
                "sha256": sha256_bytes(execution["fullCreateInput"]),
            },
            "gasAllowance": adequate_gas,
            "gasLeft": execution["gasLeft"],
            "gasUsed": execution["gasUsed"],
            "opcodeProfile": execution["opcodeProfile"],
            "projection": projection,
            "refundCounterExcluded": execution["refundCounterExcluded"],
        }
    assert expected is not None
    reference_mismatches = projection_mismatches(expected, projections["reference"])
    blanc_mismatches = projection_mismatches(expected, projections["blanc"])
    cross_side_mismatches = projection_mismatches(
        projections["reference"], projections["blanc"]
    )
    agreement = not reference_mismatches and not blanc_mismatches and not cross_side_mismatches
    evidence = {
        **common,
        "measurement": {
            "blancValue": side_rows["blanc"]["gasUsed"],
            "formula": "message.gas - output.gas_left",
            "referenceValue": side_rows["reference"]["gasUsed"],
            "refundAccounting": "pre-refund; refund counter excluded",
            "transactionIntrinsicGasIncluded": False,
            "unit": "gas",
        },
        "semantics": {
            "agreement": agreement,
            "blancMismatches": blanc_mismatches,
            "crossSideMismatches": cross_side_mismatches,
            "expected": expected,
            "referenceMismatches": reference_mismatches,
        },
        "sideExecutions": side_rows,
    }
    return evidence, {
        "agreement": agreement,
        "blanc": side_rows["blanc"]["gasUsed"],
        "reference": side_rows["reference"]["gasUsed"],
    }


def build_diagnostics(
    *,
    manifest: Mapping[str, Any],
    lock: Mapping[str, Any],
    stage: str,
    predecessor: str | None,
    evidence_records: Mapping[str, Mapping[str, Any]],
    evidence_hashes: Mapping[str, str],
    reference_side: ArtifactSide,
    blanc_side: ArtifactSide,
) -> dict[str, Any]:
    artifact_rows = {}
    for side in (reference_side, blanc_side):
        artifact_rows[side.name] = {
            "creationTemplateByteLength": len(side.creation_template),
            "creationTemplateEip3860Headroom": EIP3860_LIMIT - len(side.creation_template),
            "returnedRuntimeByteLength": len(side.returned_runtime),
            "returnedRuntimeCodeDepositGas": len(side.returned_runtime) * CODE_DEPOSIT_GAS_PER_BYTE,
            "returnedRuntimeEip170Headroom": EIP170_LIMIT - len(side.returned_runtime),
        }
    return {
        "campaignManifestDigest": manifest["campaign"]["digest"]["value"],
        "cellEvidenceSha256": dict(evidence_hashes),
        "completionThresholds": {
            cell_id: {
                side: record["sideExecutions"][side]["completionThreshold"]
                for side in ("reference", "blanc")
            }
            for cell_id, record in evidence_records.items()
            if record["sideExecutions"] is not None
        },
        "format": DIAGNOSTIC_FORMAT,
        "historicalReferenceDeployment": {
            "receiptGasUsed": lock["deployment"]["historicalReceipt"]["gasUsed"],
            "transaction": lock["deployment"]["transaction"],
        },
        "limits": {
            "artifacts": artifact_rows,
            "eip170RuntimeLimit": EIP170_LIMIT,
            "eip3860InitcodeLimit": EIP3860_LIMIT,
        },
        "predecessorResultSha256": predecessor,
        "reportOnlyCurrentBpo2Replay": {
            "reason": (
                "the repository shared transaction-level BPO2 replay is a separate report-only "
                "workflow and is not part of the primary Prague direct-message runner"
            ),
            "status": "pending-separate-replay",
        },
        "schema": 1,
        "stage": stage,
    }


def _result_cell(cell: Mapping[str, Any], values: Mapping[str, Any], digest: str) -> dict[str, Any]:
    agreement = bool(values["agreement"])
    row = {
        "blancValue": values["blanc"],
        "classification": "",
        "evidence": {"recordSha256": digest},
        "group": cell["group"],
        "id": cell["id"],
        "incomparableReason": None if agreement else "semantic projection mismatch; see cell evidence",
        "measurementStatus": "complete",
        "ordinal": cell["ordinal"],
        "referenceValue": values["reference"],
        "scalar": cell["scalar"],
        "semanticAgreement": agreement,
        "unit": "bytes" if cell["id"] in {"A1", "A2"} else "gas",
    }
    row["classification"] = schema.classify_cell(row, f"generated cell {cell['id']}")
    return row


def _load_predecessor(
    path: Path | None,
    manifest: Mapping[str, Any],
    root: Path,
    stage: str,
) -> str | None:
    if stage == "baseline":
        if path is not None:
            die("baseline generation does not accept --predecessor-result")
        return None
    if path is None:
        die("final generation requires --predecessor-result pointing to the baseline ledger")
    _, value = schema.load_json(path, "baseline predecessor")
    predecessor = schema.validate_result_schema(
        value, dict(manifest), root=root, enforce_self_digest=True, validate_external=True
    )
    if predecessor["result"]["stage"] != "baseline":
        die("final predecessor must be a baseline result")
    return predecessor["result"]["digest"]["value"]


def _created_at(value: str | None) -> str:
    if value is None:
        return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")
    if re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z", value) is None:
        die("--created-at must be UTC YYYY-MM-DDTHH:MM:SSZ")
    return value


def build_result(
    *,
    manifest: Mapping[str, Any],
    lock_raw: bytes,
    stage: str,
    predecessor: str | None,
    created_at: str,
    candidate_commit: str,
    reference_side: ArtifactSide,
    blanc_side: ArtifactSide,
    cells: list[dict[str, Any]],
    diagnostic_digest: str,
) -> dict[str, Any]:
    result = {
        "campaign": {
            "denominator": schema.DENOMINATOR,
            "fixedOrder": schema.CELL_ORDER,
            "manifestDigest": schema.MANIFEST_DIGEST,
            "manifestFormatVersion": 2,
            "manifestPath": str(schema.MANIFEST_RELATIVE),
            "minimumStrictWins": schema.MINIMUM_STRICT_WINS,
        },
        "cells": cells,
        "diagnostics": [{
            "name": "primary-prague-measurement-diagnostics",
            "recordSha256": diagnostic_digest,
        }],
        "identities": {
            "candidate": {
                "artifacts": {
                    "creationTemplate": artifact_identity(blanc_side.creation_template),
                    "returnedRuntime": artifact_identity(blanc_side.returned_runtime),
                },
                "commit": candidate_commit,
                "evaluator": str(EVALUATOR_RELATIVE),
                "treeClean": True,
            },
            "execution": {"eelsCommit": schema.EELS_COMMIT, "fork": "Prague"},
            "reference": {
                "artifacts": {
                    "creationTemplate": artifact_identity(reference_side.creation_template),
                    "returnedRuntime": artifact_identity(reference_side.returned_runtime),
                },
                "lock": str(schema.REFERENCE_LOCK_RELATIVE),
                "lockSha256": sha256_bytes(lock_raw),
            },
        },
        "result": {
            "createdAt": created_at,
            "digest": {
                "algorithm": "sha256",
                "canonicalization": schema.MANIFEST_CANONICALIZATION,
                "scope": schema.RESULT_DIGEST_SCOPE,
                "value": "",
            },
            "format": schema.RESULT_FORMAT,
            "formatVersion": 1,
            "measurementsIncluded": True,
            "predecessorResultSha256": predecessor,
            "stage": stage,
        },
        "schema": 1,
        "score": schema.score_for_cells(cells),
    }
    result["result"]["digest"]["value"] = schema.result_digest(result)
    return result


def validate_evidence_record(
    record: Any,
    *,
    manifest: Mapping[str, Any],
    result: Mapping[str, Any],
    cell_index: int,
) -> dict[str, Any]:
    if not isinstance(record, dict):
        die("cell evidence must be an object")
    required = {
        "campaignManifestDigest", "cell", "format", "identities", "measurement",
        "predecessorResultSha256", "schema", "semantics", "sideExecutions", "stage",
    }
    if set(record) != required:
        die(f"cell evidence fields differ: {sorted(record)}")
    if record["schema"] != 1 or record["format"] != EVIDENCE_FORMAT:
        die("cell evidence schema/format differs")
    result_cell = result["cells"][cell_index]
    manifest_cell = manifest["cells"][cell_index]
    if record["cell"] != manifest_cell or result_cell["id"] != manifest_cell["id"]:
        die("cell evidence does not bind the exact manifest cell")
    if record["campaignManifestDigest"] != schema.MANIFEST_DIGEST:
        die("cell evidence campaign digest differs")
    if record["stage"] != result["result"]["stage"] or \
            record["predecessorResultSha256"] != result["result"]["predecessorResultSha256"]:
        die("cell evidence stage/predecessor differs from ledger")
    identities = record["identities"]
    identity_keys = {
        "candidateArtifacts", "candidateCommit", "eelsCommit", "evaluatorEnvelopeSha256",
        "implementation", "referenceArtifacts", "referenceLockSha256",
    }
    if not isinstance(identities, dict) or set(identities) != identity_keys or \
            identities.get("candidateCommit") != result["identities"]["candidate"]["commit"] or \
            identities.get("eelsCommit") != schema.EELS_COMMIT:
        die("cell evidence candidate/EELS identity differs")
    if identities.get("candidateArtifacts") != result["identities"]["candidate"]["artifacts"] or \
            identities.get("referenceArtifacts") != result["identities"]["reference"]["artifacts"] or \
            identities.get("referenceLockSha256") != result["identities"]["reference"]["lockSha256"]:
        die("cell evidence artifact/reference identity differs")
    for artifact_owner in ("candidateArtifacts", "referenceArtifacts"):
        artifacts = identities[artifact_owner]
        if not isinstance(artifacts, dict) or set(artifacts) != {
            "creationTemplate", "returnedRuntime",
        }:
            die("cell evidence artifact membership differs")
        for name, artifact in artifacts.items():
            schema._validate_artifact_identity(artifact, f"cell evidence {artifact_owner}.{name}")
    if re.fullmatch(r"[0-9a-f]{64}", identities["evaluatorEnvelopeSha256"]) is None or \
            re.fullmatch(r"[0-9a-f]{64}", identities["referenceLockSha256"]) is None:
        die("cell evidence envelope/reference digest malformed")
    implementation = identities["implementation"]
    if not isinstance(implementation, dict) or set(implementation) != {
        "bootstrapSha256", "evaluatorSha256", "evidenceCheckerSha256",
        "launcherSha256", "loaderGuardSha256", "loaderLockSha256",
        "runnerSha256", "schemaSha256",
    } or any(re.fullmatch(r"[0-9a-f]{64}", value) is None for value in implementation.values()):
        die("cell evidence implementation identity malformed")
    measurement = record["measurement"]
    if not isinstance(measurement, dict):
        die("cell evidence measurement must be an object")
    if measurement.get("referenceValue") != result_cell["referenceValue"] or \
            measurement.get("blancValue") != result_cell["blancValue"] or \
            measurement.get("unit") != result_cell["unit"]:
        die("cell evidence scalar differs from ledger")
    semantics = record["semantics"]
    if not isinstance(semantics, dict):
        die("cell evidence semantics must be an object")
    if semantics.get("agreement") is not result_cell["semanticAgreement"]:
        die("cell evidence semantic verdict differs from ledger")
    if manifest_cell["id"] in {"A1", "A2"}:
        if set(measurement) != {"blancValue", "formula", "referenceValue", "unit"} or \
                measurement["formula"] != "exact artifact byte length":
            die("artifact cell evidence measurement contract differs")
        artifact_name = "returnedRuntime" if manifest_cell["id"] == "A1" else "creationTemplate"
        if set(semantics) != {
            "agreement", "artifact", "blancIdentity", "mismatches", "referenceIdentity",
        } or semantics != {
            "agreement": True,
            "artifact": artifact_name,
            "blancIdentity": identities["candidateArtifacts"][artifact_name],
            "mismatches": [],
            "referenceIdentity": identities["referenceArtifacts"][artifact_name],
        }:
            die("artifact cell evidence semantic identity differs")
        if record["sideExecutions"] is not None:
            die("artifact cell evidence cannot contain EELS execution")
    else:
        if set(measurement) != {
            "blancValue", "formula", "referenceValue", "refundAccounting",
            "transactionIntrinsicGasIncluded", "unit",
        } or measurement.get("refundAccounting") != "pre-refund; refund counter excluded":
            die("gas cell evidence measurement fields differ")
        if set(semantics) != {
            "agreement", "blancMismatches", "crossSideMismatches", "expected",
            "referenceMismatches",
        }:
            die("gas cell evidence semantic fields differ")
        side_rows = record["sideExecutions"]
        if not isinstance(side_rows, dict) or set(side_rows) != {"reference", "blanc"}:
            die("gas cell evidence must contain both side executions")
        if measurement.get("formula") != "message.gas - output.gas_left" or \
                measurement.get("transactionIntrinsicGasIncluded") is not False:
            die("gas cell evidence measurement contract differs")
        fixtures = Fixtures(manifest)
        addresses = fixtures.observed_addresses()
        if manifest_cell["world"]["kind"] == "direct-create-message":
            pre_slots = {slot: fixtures.zero_word for slot in fixtures.slot_names.values()}
        else:
            pre_slots = fixtures.proxy_slots(
                manifest_cell["world"]["proxyState"],
                f"{manifest_cell['id']} evidence prestate",
            )
        materialized_expected = expected_projection(
            manifest_cell, fixtures, pre_slots, addresses
        )
        if semantics["expected"] != materialized_expected:
            die("cell evidence expected projection differs from the frozen manifest")
        for side in ("reference", "blanc"):
            execution = side_rows[side]
            if not isinstance(execution, dict) or set(execution) != {
                "completionThreshold", "fullCreateInput", "gasAllowance", "gasLeft",
                "gasUsed", "opcodeProfile", "projection", "refundCounterExcluded",
            }:
                die("gas cell evidence side-execution fields differ")
            allowance = execution["gasAllowance"]
            gas_left = execution["gasLeft"]
            if type(allowance) is not int or type(gas_left) is not int or \
                    allowance < 0 or gas_left < 0 or gas_left > allowance:
                die("cell evidence gas allowance/left is malformed")
            if execution["gasUsed"] != execution["gasAllowance"] - execution["gasLeft"]:
                die("cell evidence gas formula does not hold")
            if type(execution["refundCounterExcluded"]) is not int or \
                    execution["refundCounterExcluded"] < 0:
                die("cell evidence refund counter is malformed")
            profile = execution["opcodeProfile"]
            if not isinstance(profile, dict) or set(profile) != {
                "notes", "opcodeCount", "opcodeSequenceSha256", "rows", "unframedGasCharges",
            } or type(profile["opcodeCount"]) is not int or \
                    re.fullmatch(r"[0-9a-f]{64}", profile["opcodeSequenceSha256"]) is None:
                die("cell evidence opcode profile is malformed")
            if not isinstance(profile["rows"], list) or not isinstance(
                profile["unframedGasCharges"], list
            ):
                die("cell evidence opcode profile rows are malformed")
            for row in profile["rows"]:
                if not isinstance(row, dict) or set(row) != {
                    "codeAddress", "count", "depth", "netGasDelta", "opcode", "pc",
                } or any(type(row[key]) is not int for key in (
                    "count", "depth", "netGasDelta", "pc",
                )) or row["count"] < 1 or row["depth"] < 0 or row["pc"] < 0 or \
                        not isinstance(row["opcode"], str) or not isinstance(
                            row["codeAddress"], str
                        ):
                    die("cell evidence opcode attribution row is malformed")
            for charge in profile["unframedGasCharges"]:
                if not isinstance(charge, dict) or set(charge) != {"gas", "phase"} or \
                        type(charge["gas"]) is not int or not isinstance(charge["phase"], str):
                    die("cell evidence unframed gas charge is malformed")
            threshold = execution["completionThreshold"]
            if not isinstance(threshold, dict) or set(threshold) != {
                "adequateGas", "adequateStatus", "method", "thresholdGas",
                "thresholdMinusOne", "thresholdStatus",
            } or threshold["adequateGas"] != allowance or \
                    type(threshold["thresholdGas"]) is not int or not (
                        0 <= threshold["thresholdGas"] <= allowance
                    ):
                die("cell evidence completion threshold is malformed")
            minus = threshold["thresholdMinusOne"]
            if threshold["thresholdGas"] == 0:
                if minus is not None:
                    die("zero completion threshold cannot have threshold-minus-one")
            elif not isinstance(minus, dict) or minus.get("gas") != \
                    threshold["thresholdGas"] - 1 or minus.get("semanticAgreement") is not False:
                die("cell evidence threshold-minus-one is malformed")
            full_input = execution["fullCreateInput"]
            if manifest_cell["world"]["kind"] == "direct-create-message":
                if not isinstance(full_input, dict) or set(full_input) != {
                    "byteLength", "hex", "sha256",
                }:
                    die("CREATE cell evidence must contain the full CREATE input")
                raw_input = hex_bytes(full_input["hex"], "evidence full CREATE input")
                if full_input["byteLength"] != len(raw_input) or \
                        full_input["sha256"] != sha256_bytes(raw_input):
                    die("cell evidence full CREATE input identity differs")
                arguments = fixtures.constructor_arguments(
                    manifest_cell["world"]["constructorTuple"],
                    f"{manifest_cell['id']} evidence constructor arguments",
                )
                if not raw_input.endswith(arguments):
                    die("cell evidence full CREATE input has the wrong ABI suffix")
                creation = raw_input[:-len(arguments)] if arguments else raw_input
                expected_creation = identities[
                    "referenceArtifacts" if side == "reference" else "candidateArtifacts"
                ]["creationTemplate"]
                if artifact_identity(creation) != expected_creation:
                    die("cell evidence full CREATE input has the wrong creation template")
            elif full_input is not None:
                die("ordinary-call cell evidence cannot contain a CREATE input")
        derived_reference = projection_mismatches(
            semantics["expected"], side_rows["reference"]["projection"]
        )
        derived_blanc = projection_mismatches(
            semantics["expected"], side_rows["blanc"]["projection"]
        )
        derived_cross = projection_mismatches(
            side_rows["reference"]["projection"], side_rows["blanc"]["projection"]
        )
        derived_agreement = not derived_reference and not derived_blanc and not derived_cross
        if semantics["referenceMismatches"] != derived_reference or \
                semantics["blancMismatches"] != derived_blanc or \
                semantics["crossSideMismatches"] != derived_cross or \
                semantics["agreement"] is not derived_agreement:
            die("cell evidence semantic mismatch derivation differs")
        if measurement["referenceValue"] != side_rows["reference"]["gasUsed"] or \
                measurement["blancValue"] != side_rows["blanc"]["gasUsed"]:
            die("cell evidence scalar does not equal the side gas records")
    return record


def validate_diagnostics_record(
    record: Any,
    *,
    manifest: Mapping[str, Any],
    result: Mapping[str, Any],
    evidence_hashes: Mapping[str, str],
    evidence_records: Mapping[str, Mapping[str, Any]] | None = None,
    lock: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if not isinstance(record, dict) or set(record) != {
        "campaignManifestDigest", "cellEvidenceSha256", "completionThresholds", "format",
        "historicalReferenceDeployment", "limits", "predecessorResultSha256",
        "reportOnlyCurrentBpo2Replay", "schema", "stage",
    } or record.get("format") != DIAGNOSTIC_FORMAT or \
            record.get("schema") != 1:
        die("performance diagnostic schema/format differs")
    if record.get("campaignManifestDigest") != schema.MANIFEST_DIGEST or \
            record.get("stage") != result["result"]["stage"] or \
            record.get("predecessorResultSha256") != result["result"]["predecessorResultSha256"]:
        die("performance diagnostics campaign/stage/predecessor differs")
    if record.get("cellEvidenceSha256") != dict(evidence_hashes):
        die("performance diagnostics cell-evidence inventory differs")
    thresholds = record.get("completionThresholds")
    if not isinstance(thresholds, dict) or set(thresholds) != set(schema.CELL_ORDER[2:]):
        die("performance diagnostics completion-threshold inventory differs")
    if evidence_records is not None:
        expected_thresholds = {
            cell_id: {
                side: evidence_records[cell_id]["sideExecutions"][side]["completionThreshold"]
                for side in ("reference", "blanc")
            }
            for cell_id in schema.CELL_ORDER[2:]
        }
        if thresholds != expected_thresholds:
            die("performance diagnostics completion thresholds differ from cell evidence")
    expected_limits = {
        "artifacts": {
            side: {
                "creationTemplateByteLength": artifacts["creationTemplate"]["byteLength"],
                "creationTemplateEip3860Headroom": (
                    EIP3860_LIMIT - artifacts["creationTemplate"]["byteLength"]
                ),
                "returnedRuntimeByteLength": artifacts["returnedRuntime"]["byteLength"],
                "returnedRuntimeCodeDepositGas": (
                    artifacts["returnedRuntime"]["byteLength"] * CODE_DEPOSIT_GAS_PER_BYTE
                ),
                "returnedRuntimeEip170Headroom": (
                    EIP170_LIMIT - artifacts["returnedRuntime"]["byteLength"]
                ),
            }
            for side, artifacts in {
                "reference": result["identities"]["reference"]["artifacts"],
                "blanc": result["identities"]["candidate"]["artifacts"],
            }.items()
        },
        "eip170RuntimeLimit": EIP170_LIMIT,
        "eip3860InitcodeLimit": EIP3860_LIMIT,
    }
    if record.get("limits") != expected_limits:
        die("performance diagnostics artifact limits/headroom differ")
    if lock is not None and record.get("historicalReferenceDeployment") != {
        "receiptGasUsed": lock["deployment"]["historicalReceipt"]["gasUsed"],
        "transaction": lock["deployment"]["transaction"],
    }:
        die("performance diagnostics historical receipt identity differs")
    if record.get("reportOnlyCurrentBpo2Replay", {}).get("status") != "pending-separate-replay":
        die("performance diagnostics BPO2 replay disposition differs")
    return record


def write_outputs_exclusive(
    result_out: Path,
    evidence_out: Path,
    result: Mapping[str, Any],
    evidence_records: Mapping[str, Mapping[str, Any]],
    diagnostics: Mapping[str, Any],
) -> None:
    if result_out.exists() or evidence_out.exists():
        die("refusing to overwrite immutable result or evidence directory")
    result_out.parent.mkdir(parents=True, exist_ok=True)
    evidence_out.parent.mkdir(parents=True, exist_ok=True)
    try:
        evidence_out.mkdir()
        for cell_id in schema.CELL_ORDER:
            (evidence_out / f"{cell_id}.json").write_bytes(canonical_bytes(evidence_records[cell_id]))
        (evidence_out / "diagnostics.json").write_bytes(canonical_bytes(diagnostics))
        with result_out.open("xb") as handle:
            handle.write(canonical_bytes(result))
    except (FileExistsError, OSError) as exc:
        raise RunnerError(
            "failed while creating the immutable output bundle; inspect and remove only the "
            f"incomplete requested paths before an explicit retry: {exc}"
        ) from exc


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument(
        "--eels-root", type=Path,
        default=Path(os.environ.get("EELS_ROOT", "~/execution-specs")),
    )
    parser.add_argument("--blanc-artifacts", type=Path)
    parser.add_argument("--stage", choices=("baseline", "final"))
    parser.add_argument("--predecessor-result", type=Path)
    parser.add_argument("--result-out", type=Path)
    parser.add_argument("--evidence-out", type=Path)
    parser.add_argument("--created-at")
    parser.add_argument(
        "--dry-run", action="store_true",
        help="validate all frozen fixtures and identities without artifacts, EELS, or measurement",
    )
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)
    root = args.repo_root.expanduser().resolve()
    manifest, lock, lock_raw = load_campaign(root)
    observed = dry_resolve(manifest)
    if args.dry_run:
        forbidden = (
            args.blanc_artifacts, args.stage, args.predecessor_result,
            args.result_out, args.evidence_out, args.created_at,
        )
        if any(value is not None for value in forbidden):
            die("--dry-run does not accept generation arguments")
        print(
            "OK — OssifiableProxy performance dry run: 25 ordered cells; "
            f"{observed} observed addresses; all fixtures resolved; no Lean/EELS/measurement"
        )
        return 0
    required = {
        "--blanc-artifacts": args.blanc_artifacts,
        "--stage": args.stage,
        "--result-out": args.result_out,
        "--evidence-out": args.evidence_out,
    }
    missing = [name for name, value in required.items() if value is None]
    if missing:
        die("real generation requires " + ", ".join(missing))
    assert args.stage is not None and args.result_out is not None and args.evidence_out is not None
    result_out = args.result_out.expanduser().resolve()
    evidence_out = args.evidence_out.expanduser().resolve()
    if result_out.exists() or evidence_out.exists():
        die("refusing to overwrite immutable result or evidence directory")
    candidate_commit = verify_clean_blanc(root)
    predecessor = _load_predecessor(
        args.predecessor_result.expanduser().resolve() if args.predecessor_result else None,
        manifest,
        root,
        args.stage,
    )
    eels_root = args.eels_root.expanduser().resolve()
    verify_eels(eels_root)
    assert args.blanc_artifacts is not None
    artifacts = parse_blanc_artifacts(args.blanc_artifacts.expanduser().resolve())
    reference_creation, reference_runtime = _reference_artifacts(lock)
    reference_side = ArtifactSide("reference", reference_creation, reference_runtime)
    blanc_side = ArtifactSide(
        "blanc", artifacts["creationTemplate"], artifacts["returnedRuntime"]
    )
    fixtures = Fixtures(manifest)
    addresses = fixtures.observed_addresses()
    implementation_identity = _implementation_identity(root)
    evidence_records: dict[str, dict[str, Any]] = {}
    evidence_hashes: dict[str, str] = {}
    values: dict[str, dict[str, Any]] = {}
    for cell in manifest["cells"]:
        evidence, cell_values = _cell_evidence(
            root=root,
            manifest=manifest,
            cell=cell,
            stage=args.stage,
            predecessor=predecessor,
            candidate_commit=candidate_commit,
            implementation_identity=implementation_identity,
            envelope_sha256=artifacts["envelopeSha256"],
            reference_lock_sha256=sha256_bytes(lock_raw),
            reference_side=reference_side,
            blanc_side=blanc_side,
            fixtures=fixtures,
            addresses=addresses,
        )
        evidence_records[cell["id"]] = evidence
        evidence_hashes[cell["id"]] = sha256_bytes(canonical_bytes(evidence))
        values[cell["id"]] = cell_values
        if args.verbose:
            verdict = "AGREE" if cell_values["agreement"] else "MISMATCH"
            print(
                f"{cell['id']} {verdict} reference={cell_values['reference']} "
                f"blanc={cell_values['blanc']}",
                file=sys.stderr,
            )
    cells = [
        _result_cell(cell, values[cell["id"]], evidence_hashes[cell["id"]])
        for cell in manifest["cells"]
    ]
    diagnostics = build_diagnostics(
        manifest=manifest,
        lock=lock,
        stage=args.stage,
        predecessor=predecessor,
        evidence_records=evidence_records,
        evidence_hashes=evidence_hashes,
        reference_side=reference_side,
        blanc_side=blanc_side,
    )
    diagnostic_digest = sha256_bytes(canonical_bytes(diagnostics))
    result = build_result(
        manifest=manifest,
        lock_raw=lock_raw,
        stage=args.stage,
        predecessor=predecessor,
        created_at=_created_at(args.created_at),
        candidate_commit=candidate_commit,
        reference_side=reference_side,
        blanc_side=blanc_side,
        cells=cells,
        diagnostic_digest=diagnostic_digest,
    )
    schema.validate_result_schema(
        result, manifest, root=root, enforce_self_digest=True, validate_external=True
    )
    for index, cell_id in enumerate(schema.CELL_ORDER):
        validate_evidence_record(
            evidence_records[cell_id], manifest=manifest, result=result, cell_index=index
        )
    validate_diagnostics_record(
        diagnostics,
        manifest=manifest,
        result=result,
        evidence_hashes=evidence_hashes,
        evidence_records=evidence_records,
        lock=lock,
    )
    write_outputs_exclusive(result_out, evidence_out, result, evidence_records, diagnostics)
    score = result["score"]
    print(
        f"OK — OssifiableProxy {args.stage} performance: 25/25 cells reported; "
        f"strict wins {score['strictWins']}/25; ties {score['ties']}; losses {score['losses']}; "
        f"incomparables {score['incomparables']}; immutable result "
        f"{result['result']['digest']['value']}"
    )
    return 0 if all(row["semanticAgreement"] for row in cells) else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except Exception as exc:
        print(
            "REGRESSION — OssifiableProxy performance generation: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
