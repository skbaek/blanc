#!/usr/bin/env python3
"""Generate/check the report-only OssifiableProxy BPO2 transaction replay.

The frozen 25-cell score remains the direct-message Prague campaign.  This
consumer replays A3/A4 and every primary call cell that a singleton signed
transaction can represent without changing its frozen world.  It records
receipt gas and a transaction-observable semantic projection under the shared
current-mainnet BPO2 lane.  A1/A2 are not transaction scenarios; F2/F4 are
explicitly excluded because their pre-warmed message state cannot be authored
by a legacy transaction without changing the transaction envelope and its
intrinsic gas.

Normal mode is read-only and byte-compares the committed report.  --write is
the sole writer and is reached only after both artifacts agree with the frozen
semantic projection on every represented cell.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import eels_semantic_closure

eels_semantic_closure.assert_loader_guard_installed(
    eels_semantic_closure.fail,
    label="OssifiableProxy current-mainnet generator",
)

from ethereum.crypto.hash import keccak256
from execution_testing.forks import BPO2 as TestingBPO2
from spec256k1 import PrivateKey

import lido_ossifiable_proxy_performance_schema as performance_schema
from current_mainnet import (
    load_profile,
    resolve_root,
    run_t8n,
    target_paths,
    verify_target,
)


ROOT = Path(__file__).resolve().parents[1]
SCRIPT_PATH = ROOT / "scripts" / "gen-lido-ossifiable-proxy-current-mainnet.py"
WRAPPER_PATH = ROOT / "scripts" / "check-lido-ossifiable-proxy-current-mainnet.sh"
PROFILE_PATH = ROOT / "scripts" / "current-mainnet-target.json"
HELPER_PATH = ROOT / "scripts" / "current_mainnet.py"
MANIFEST_PATH = ROOT / performance_schema.MANIFEST_RELATIVE
REFERENCE_LOCK_PATH = ROOT / performance_schema.REFERENCE_LOCK_RELATIVE
PERFORMANCE_RUNNER_PATH = ROOT / "scripts" / "run-lido-ossifiable-proxy-performance.py"
PERFORMANCE_SCHEMA_PATH = ROOT / "scripts" / "lido_ossifiable_proxy_performance_schema.py"
ARTIFACT_GENERATOR_PATH = ROOT / "scripts" / "lido-ossifiable-proxy-artifacts.py"
ARTIFACT_LEAN_PATH = ROOT / "Blanc" / "ProxyPairOssifiableArtifacts.lean"
ARTIFACT_MANIFEST_PATH = ROOT / "scripts" / "lido-ossifiable-proxy-artifacts.json"
RESULT_PATH = (
    ROOT
    / "scripts"
    / "reference"
    / "lido-ossifiable-proxy"
    / "current-mainnet-results.json"
)

CURRENT_MAINNET_PUBLIC_API = {
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
}
FORMAT = "blanc.lido-ossifiable-proxy.current-mainnet-replay"
SCHEMA = 1
GAS_PRICE = 10
BPO2_TX_MAX_GAS_LIMIT = 16_777_216
PRIVATE_KEYS = {
    "0x7e5f4552091a69125d5dfcb7b8c2659029395bdf": 1,
    "0x2b5ad5c4795c026514f8317c7a215e218dccd6cf": 2,
}
EXPECTED_SYSTEM_ADDRESSES = {
    0x0000F90827F1C53A10CB7A02335B175320002935,
    0x000F3DF6D732807EF1319FB7B8BB8522D0BEAC02,
    0x00000961EF480EB55E80D19AD83579A64C007002,
    0x0000BBDDC7CE488642FB579F8B00F3A590007251,
    0x00000000219AB540356CBB839CBE05303D7705FA,
}
EXCLUSIONS = {
    "A1": (
        "artifact scalar only: returned-runtime byte length has no transaction "
        "scenario and remains exclusively in the primary 25-cell ledger"
    ),
    "A2": (
        "artifact scalar only: creation-template byte length has no transaction "
        "scenario and remains exclusively in the primary 25-cell ledger"
    ),
    "F2": (
        "the frozen world begins with the implementation address and the proxy "
        "implementation slot already warm; a singleton legacy transaction cannot "
        "seed that prior message state, while an access-list transaction would "
        "change the transaction type, envelope, and intrinsic gas"
    ),
    "F4": (
        "the frozen world begins with the implementation address and the proxy "
        "implementation slot already warm; a singleton legacy transaction cannot "
        "seed that prior message state, while an access-list transaction would "
        "change the transaction type, envelope, and intrinsic gas"
    ),
}
REPRESENTED = tuple(
    cell_id for cell_id in performance_schema.CELL_ORDER if cell_id not in EXCLUSIONS
)


class ReplayError(RuntimeError):
    """The current-mainnet replay failed closed."""


@dataclass(frozen=True)
class Side:
    name: str
    creation_template: bytes
    returned_runtime: bytes


def fail(message: str) -> None:
    raise ReplayError(message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def integer(value: Any, owner: str) -> int:
    try:
        if isinstance(value, str) and value.startswith("0x"):
            return int(value, 16)
        return int(value)
    except (TypeError, ValueError) as exc:
        raise ReplayError(f"{owner}: invalid integer {value!r}") from exc


def quantity(value: Any) -> str:
    number = integer(value, "quantity")
    if number < 0:
        fail("negative quantity")
    digits = format(number, "x")
    if len(digits) % 2:
        digits = "0" + digits
    return "0x" + digits


def word(value: Any) -> str:
    number = integer(value, "word")
    if number < 0 or number >= 1 << 256:
        fail("word outside uint256")
    return "0x" + number.to_bytes(32, "big").hex()


def address(value: Any, owner: str) -> str:
    if not isinstance(value, str) or re.fullmatch(r"0x[0-9a-fA-F]{40}", value) is None:
        fail(f"{owner}: malformed address {value!r}")
    return value.lower()


def derive_address(key: int) -> str:
    public = PrivateKey(key.to_bytes(32, "big")).public_key.format(compressed=False)
    return "0x" + bytes(keccak256(public[1:]))[-20:].hex()


def bytes_identity(value: bytes) -> dict[str, Any]:
    return {
        "byteLength": len(value),
        "codeDepositGas": 200 * len(value),
        "keccak256": "0x" + bytes(keccak256(value)).hex(),
        "sha256": sha256_bytes(value),
    }


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        fail(f"cannot load module {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def validate_current_mainnet_boundary() -> None:
    """Pin this consumer to the fork-override-free five-function API."""
    tree = ast.parse(SCRIPT_PATH.read_text(encoding="utf-8"))
    legacy_root_name = "EELS" + "_ROOT"
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value == legacy_root_name:
            fail("replay cross-wires the historical Prague root environment")
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
            fail("replay bypasses the current-mainnet execution API")
    imports = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module == "current_mainnet"
    ]
    imported = {
        alias.name
        for node in imports
        for alias in node.names
        if alias.asname is None
    }
    if (
        len(imports) != 1
        or imported != CURRENT_MAINNET_PUBLIC_API
        or any(alias.asname is not None for node in imports for alias in node.names)
    ):
        fail("replay must import exactly the five public current-mainnet API names")
    calls = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
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
    if (
        not isinstance(keywords["state_test"], ast.Constant)
        or keywords["state_test"].value is not False
    ):
        fail("replay must use explicit block semantics")
    if (
        not isinstance(keywords["timeout"], ast.Constant)
        or keywords["timeout"].value != 120
    ):
        fail("replay run_t8n timeout must remain exactly 120 seconds")


def load_campaign_and_sides() -> tuple[Any, Any, Any, tuple[Side, Side]]:
    raw_manifest, manifest_value = performance_schema.load_json(
        MANIFEST_PATH, "OssifiableProxy performance manifest"
    )
    manifest = performance_schema.validate_manifest_schema(
        manifest_value,
        root=ROOT,
        enforce_frozen_digest=True,
        validate_external=True,
    )
    if sha256_bytes(raw_manifest) != sha256_path(MANIFEST_PATH):
        fail("performance manifest read identity changed")

    performance = load_module(
        "lido_ossifiable_proxy_performance_runner_for_bpo2",
        PERFORMANCE_RUNNER_PATH,
    )
    lock = performance_schema.strict_json(
        REFERENCE_LOCK_PATH.read_bytes(), "OssifiableProxy reference lock"
    )
    reference_creation, reference_runtime = performance._reference_artifacts(lock)

    artifacts = load_module(
        "lido_ossifiable_proxy_artifacts_for_bpo2",
        ARTIFACT_GENERATOR_PATH,
    )
    artifacts.check_keccak_implementation()
    artifacts.check_committed()
    blanc = artifacts.parse_committed_lean()
    sides = (
        Side("reference", reference_creation, reference_runtime),
        Side("blanc", blanc.creation_template, blanc.runtime_baseline),
    )
    return manifest, performance, performance.Fixtures(manifest), sides


def system_alloc() -> dict[str, Any]:
    raw = TestingBPO2.pre_allocation_blockchain()
    if set(raw) != EXPECTED_SYSTEM_ADDRESSES:
        fail(
            "BPO2 system-contract population differs: "
            + repr(sorted(hex(item) for item in raw))
        )
    result: dict[str, Any] = {}
    for raw_address, item in sorted(raw.items()):
        raw_code = item.get("code", b"")
        if isinstance(raw_code, bytes):
            code = "0x" + raw_code.hex()
        elif isinstance(raw_code, str) and raw_code.startswith("0x"):
            code = raw_code.lower()
        else:
            fail(f"BPO2 system code has unknown shape at {raw_address:#x}")
        storage: dict[str, str] = {}
        for raw_slot, raw_value in item.get("storage", {}).items():
            slot = (
                int.from_bytes(raw_slot, "big")
                if isinstance(raw_slot, bytes)
                else int(raw_slot)
            )
            value = (
                int.from_bytes(raw_value, "big")
                if isinstance(raw_value, bytes)
                else int(raw_value)
            )
            if value:
                storage[quantity(slot)] = quantity(value)
        result["0x" + format(raw_address, "040x")] = {
            "balance": quantity(item.get("balance", 0)),
            "code": code,
            "nonce": quantity(item.get("nonce", 0)),
            "storage": storage,
        }
    return result


def account(
    *,
    balance: Any = 0,
    code: bytes = b"",
    nonce: Any = 0,
    storage: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "balance": quantity(balance),
        "code": "0x" + code.hex(),
        "nonce": quantity(nonce),
        "storage": {
            word(slot): word(value)
            for slot, value in (storage or {}).items()
            if integer(value, "storage value") != 0
        },
    }


def block_environment(fixtures: Any) -> dict[str, Any]:
    frozen = fixtures.values["blockEnvironment"]
    number = integer(frozen["number"], "block number")
    hashes = frozen["blockHashes"]
    if not isinstance(hashes, list) or len(hashes) != 1:
        fail("frozen block hash fixture is not singleton")
    return {
        "blockHashes": {quantity(number - 1): hashes[0]},
        "currentBaseFee": quantity(frozen["baseFeePerGas"]),
        "currentCoinbase": address(frozen["coinbase"], "coinbase"),
        "currentExcessBlobGas": quantity(frozen["excessBlobGas"]),
        "currentGasLimit": quantity(frozen["blockGasLimit"]),
        "currentNumber": quantity(number),
        "currentRandom": frozen["prevRandao"],
        "currentTimestamp": quantity(frozen["timestamp"]),
        "parentBeaconBlockRoot": frozen["parentBeaconBlockRoot"],
        "withdrawals": [],
    }


def private_key_for(caller: str) -> int:
    key = PRIVATE_KEYS.get(caller)
    if key is None or derive_address(key) != caller:
        fail(f"no exact private-key fixture for caller {caller}")
    return key


def transaction_gas_limit(cell: Mapping[str, Any], fixtures: Any) -> tuple[int, int]:
    """Adapt the direct-message allowance to BPO2's protocol transaction cap."""
    frozen = fixtures.scalar(cell["world"]["gasAllowance"], f"{cell['id']} gas")
    current = min(frozen, BPO2_TX_MAX_GAS_LIMIT)
    if current <= 0:
        fail(f"{cell['id']}: current transaction gas limit is not positive")
    return frozen, current


def scenario_inputs(
    cell: Mapping[str, Any],
    side: Side,
    fixtures: Any,
) -> tuple[dict[str, Any], dict[str, Any], list[dict[str, Any]], str, int, int]:
    world_row = cell["world"]
    caller = fixtures.address(world_row["caller"], f"{cell['id']} caller")
    target = fixtures.address(world_row["target"], f"{cell['id']} target")
    caller_template = fixtures.values["accountTemplates"]["caller"]
    caller_nonce = integer(
        world_row.get("callerNonce", caller_template["nonce"]),
        f"{cell['id']} caller nonce",
    )

    alloc = system_alloc()
    for required in (caller, target):
        if required in alloc:
            fail(f"{cell['id']}: scenario address collides with a BPO2 system contract")
    alloc[caller] = account(
        balance=caller_template["balance"],
        nonce=caller_nonce,
    )

    if world_row["kind"] == "direct-call-message":
        state = fixtures.named("proxyStates", world_row["proxyState"], cell["id"])
        alloc[target] = account(
            balance=state["accountBalance"],
            code=side.returned_runtime,
            nonce=state["accountNonce"],
            storage=state["storageOverrides"],
        )
        to = target
        tx_input = fixtures.calldata(world_row["calldata"], f"{cell['id']} calldata")
    elif world_row["kind"] == "direct-create-message":
        if target in alloc:
            fail(f"{cell['id']}: CREATE target is not fresh")
        expected_target = derive_contract_address(caller, caller_nonce)
        if expected_target != target:
            fail(
                f"{cell['id']}: CREATE target derivation differs: "
                f"{expected_target} != {target}"
            )
        to = ""
        tx_input = (
            side.creation_template
            + fixtures.constructor_arguments(
                world_row["constructorTuple"], f"{cell['id']} constructor"
            )
            + fixtures.calldata(world_row["messageData"], f"{cell['id']} message data")
        )
    else:
        fail(f"{cell['id']}: unrepresentable world kind {world_row['kind']!r}")

    for implementation in world_row.get("implementationAccounts", []):
        implementation_address = fixtures.address(
            implementation["address"], f"{cell['id']} implementation"
        )
        if implementation_address in alloc:
            fail(f"{cell['id']}: duplicate implementation account {implementation_address}")
        alloc[implementation_address] = account(
            code=fixtures.code(implementation["code"], f"{cell['id']} implementation code"),
            nonce=1,
        )
    for absent_name in world_row.get("absentAccounts", []):
        absent = fixtures.address(absent_name, f"{cell['id']} absent account")
        if absent in alloc:
            fail(f"{cell['id']}: required-absent account is present: {absent}")

    frozen_gas_limit, current_gas_limit = transaction_gas_limit(cell, fixtures)
    transaction = {
        "chainId": "0x1",
        "gas": quantity(current_gas_limit),
        "gasPrice": quantity(GAS_PRICE),
        "input": "0x" + tx_input.hex(),
        "nonce": quantity(caller_nonce),
        "secretKey": "0x" + format(private_key_for(caller), "064x"),
        "to": to,
        "type": "0x0",
        "value": quantity(fixtures.scalar(world_row["value"], f"{cell['id']} value")),
    }
    return (
        alloc,
        block_environment(fixtures),
        [transaction],
        target,
        frozen_gas_limit,
        current_gas_limit,
    )


def derive_contract_address(sender: str, nonce: int) -> str:
    if nonce != 0:
        fail("current replay only owns the frozen nonce-zero CREATE derivation")
    sender_bytes = bytes.fromhex(sender[2:])
    encoded = bytes([0xd6, 0x94]) + sender_bytes + bytes([0x80])
    return "0x" + bytes(keccak256(encoded))[-20:].hex()


def find_account(post: Mapping[str, Any], wanted: str) -> Mapping[str, Any]:
    matches = [
        value
        for raw_address, value in post.items()
        if address(raw_address, "post-state address") == wanted
    ]
    if len(matches) != 1:
        fail(f"post-state account {wanted} has {len(matches)} matches")
    return matches[0]


def storage_word(post_account: Mapping[str, Any], slot: str) -> str:
    wanted = integer(slot, "wanted storage slot")
    matches = [
        integer(value, "post storage value")
        for raw_slot, value in (post_account.get("storage") or {}).items()
        if integer(raw_slot, "post storage slot") == wanted
    ]
    if len(matches) > 1:
        fail(f"post-state storage slot {slot} is duplicated")
    return word(matches[0] if matches else 0)


def normalize_logs(raw_logs: Any) -> list[dict[str, Any]]:
    if not isinstance(raw_logs, list):
        fail("receipt logs are not a list")
    result = []
    for index, raw in enumerate(raw_logs):
        if not isinstance(raw, dict):
            fail(f"receipt log {index} is not an object")
        topics = raw.get("topics")
        if not isinstance(topics, list):
            fail(f"receipt log {index} topics are not a list")
        data = raw.get("data")
        if not isinstance(data, str) or re.fullmatch(r"0x[0-9a-fA-F]*", data) is None:
            fail(f"receipt log {index} data are malformed")
        normalized_topics = []
        for topic in topics:
            if not isinstance(topic, str) or re.fullmatch(r"0x[0-9a-fA-F]{64}", topic) is None:
                fail(f"receipt log {index} topic is malformed")
            normalized_topics.append(topic.lower())
        result.append({
            "address": address(raw.get("address"), f"receipt log {index} address"),
            "data": data.lower(),
            "topics": normalized_topics,
        })
    return result


def normalize_bloom(raw_bloom: Any, owner: str) -> str:
    if (
        not isinstance(raw_bloom, str)
        or re.fullmatch(r"0x[0-9a-fA-F]{512}", raw_bloom) is None
    ):
        fail(f"{owner}: malformed logs bloom")
    return raw_bloom.lower()


def expected_projection(
    cell: Mapping[str, Any],
    performance: Any,
    fixtures: Any,
) -> dict[str, Any]:
    world_row = cell["world"]
    target = fixtures.address(world_row["target"], f"{cell['id']} target")
    if world_row["kind"] == "direct-call-message":
        pre_slots = fixtures.proxy_slots(world_row["proxyState"], f"{cell['id']} prestate")
    else:
        pre_slots = {slot: fixtures.zero_word for slot in fixtures.slot_names.values()}
    expected_storage = performance._expected_storage(cell, fixtures, pre_slots)
    target_balance = (
        fixtures.scalar(world_row["value"], f"{cell['id']} target balance")
        if world_row["expected"] == "receive-empty-success"
        else 0
    )
    return {
        "logs": normalize_logs(performance._expected_logs(cell, fixtures)),
        "status": fixtures.values["expectedSemantics"][world_row["expected"]]["status"],
        "target": {
            "balance": str(target_balance),
            "code": "own-returned-runtime",
            "exists": expected_storage["targetExists"],
            "nonce": 1,
            "storage": expected_storage["slots"],
            "targetAddress": target,
        },
    }


def receipt_gas(receipt: Mapping[str, Any]) -> tuple[int, str]:
    if "gasUsed" in receipt:
        return integer(receipt["gasUsed"], "receipt gasUsed"), "gasUsed"
    if "cumulativeGasUsed" in receipt:
        return (
            integer(receipt["cumulativeGasUsed"], "receipt cumulativeGasUsed"),
            "singleton cumulativeGasUsed",
        )
    fail(f"receipt has no gas field: {sorted(receipt)}")


def run_case(
    cell: Mapping[str, Any],
    side: Side,
    performance: Any,
    fixtures: Any,
    *,
    root: Path,
    profile: dict[str, Any],
) -> dict[str, Any]:
    (
        alloc,
        environment,
        transactions,
        target,
        frozen_gas_limit,
        current_gas_limit,
    ) = scenario_inputs(cell, side, fixtures)
    outputs = run_t8n(
        alloc,
        environment,
        transactions,
        root=root,
        profile=profile,
        state_test=False,
        timeout=120,
    )
    if outputs.result.get("rejected") not in (None, []):
        fail(f"{cell['id']}/{side.name}: transaction rejected: {outputs.result['rejected']!r}")
    if outputs.result.get("blockException") is not None:
        fail(
            f"{cell['id']}/{side.name}: block exception: "
            f"{outputs.result['blockException']!r}"
        )
    receipts = outputs.result.get("receipts")
    if not isinstance(receipts, list) or len(receipts) != 1:
        fail(f"{cell['id']}/{side.name}: expected exactly one receipt")
    receipt = receipts[0]
    if not isinstance(receipt, dict):
        fail(f"{cell['id']}/{side.name}: receipt is not an object")
    status_hex = receipt.get("status")
    if status_hex not in {"0x0", "0x1"}:
        fail(f"{cell['id']}/{side.name}: malformed receipt status {status_hex!r}")
    status = "success" if status_hex == "0x1" else "revert"
    gas_used, gas_source = receipt_gas(receipt)
    block_gas = integer(outputs.result.get("gasUsed"), "block gasUsed")
    if gas_used != block_gas:
        fail(
            f"{cell['id']}/{side.name}: singleton receipt/block gas differ: "
            f"{gas_used} != {block_gas}"
        )
    logs = normalize_logs(receipt.get("logs", []))
    target_account = find_account(outputs.alloc, target)
    actual_code = target_account.get("code", "0x")
    if actual_code != "0x" + side.returned_runtime.hex():
        fail(f"{cell['id']}/{side.name}: target code is not the side-owned runtime")
    projection = {
        "logs": logs,
        "status": status,
        "target": {
            "balance": str(integer(target_account.get("balance", "0x0"), "target balance")),
            "code": "own-returned-runtime",
            "exists": True,
            "nonce": integer(target_account.get("nonce", "0x0"), "target nonce"),
            "storage": {
                slot: storage_word(target_account, slot)
                for slot in fixtures.slot_names.values()
            },
            "targetAddress": target,
        },
    }
    expected = expected_projection(cell, performance, fixtures)
    mismatches = [
        key for key in expected if projection.get(key) != expected[key]
    ]
    if mismatches:
        fail(
            f"{cell['id']}/{side.name}: BPO2 semantic projection differs at "
            + ", ".join(mismatches)
        )
    receipt_bloom = normalize_bloom(
        receipt.get("logsBloom", receipt.get("bloom")),
        f"{cell['id']}/{side.name} receipt",
    )
    aggregate_bloom = normalize_bloom(
        outputs.result.get("logsBloom"),
        f"{cell['id']}/{side.name} aggregate",
    )
    if aggregate_bloom != receipt_bloom:
        fail(f"{cell['id']}/{side.name}: singleton receipt/block blooms differ")
    return {
        "aggregateLogsBloom": aggregate_bloom,
        "expectedProjection": expected,
        "projection": projection,
        "receiptGasSource": gas_source,
        "receiptGasUsed": gas_used,
        "receiptLogsBloom": receipt_bloom,
        "receiptStatus": status_hex,
        "transactionGasLimit": current_gas_limit,
        "frozenDirectMessageGasAllowance": frozen_gas_limit,
    }


def render_summary(
    manifest: Mapping[str, Any],
    performance: Any,
    fixtures: Any,
    sides: tuple[Side, Side],
    *,
    root: Path,
    profile: dict[str, Any],
) -> dict[str, Any]:
    if len(REPRESENTED) != 21 or set(EXCLUSIONS) != {"A1", "A2", "F2", "F4"}:
        fail("report-only represented/excluded inventory differs")
    by_id = {cell["id"]: cell for cell in manifest["cells"]}
    rows: dict[str, Any] = {}
    for cell_id in REPRESENTED:
        cell = by_id[cell_id]
        side_rows = {
            side.name: run_case(
                cell,
                side,
                performance,
                fixtures,
                root=root,
                profile=profile,
            )
            for side in sides
        }
        reference_projection = side_rows["reference"]["projection"]
        blanc_projection = side_rows["blanc"]["projection"]
        if reference_projection != blanc_projection:
            fail(f"{cell_id}: reference and Blanc BPO2 semantic projections differ")
        reference_gas = side_rows["reference"]["receiptGasUsed"]
        blanc_gas = side_rows["blanc"]["receiptGasUsed"]
        rows[cell_id] = {
            "blanc": side_rows["blanc"],
            "cellOrdinal": cell["ordinal"],
            "frozenWorldSha256": sha256_bytes(
                json.dumps(
                    cell,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=True,
                ).encode("utf-8")
            ),
            "gasDeltaReferenceMinusBlanc": reference_gas - blanc_gas,
            "primaryScoreDisposition": "report-only; not a score cell",
            "reference": side_rows["reference"],
            "semanticAgreement": True,
        }

    deltas = [row["gasDeltaReferenceMinusBlanc"] for row in rows.values()]
    return {
        "artifacts": {
            side.name: {
                "creationTemplate": bytes_identity(side.creation_template),
                "returnedRuntime": bytes_identity(side.returned_runtime),
            }
            for side in sides
        },
        "campaign": {
            "bpo2TransactionGasLimit": BPO2_TX_MAX_GAS_LIMIT,
            "excludedPrimaryCells": [
                {"id": cell_id, "reason": EXCLUSIONS[cell_id]}
                for cell_id in performance_schema.CELL_ORDER
                if cell_id in EXCLUSIONS
            ],
            "frozenManifestDigest": manifest["campaign"]["digest"]["value"],
            "gasLimitAdaptation": (
                "the frozen direct-message allowance is capped at BPO2's protocol "
                "maximum transaction gas limit; both sides receive the same cap and "
                "the primary Prague worlds remain unchanged"
            ),
            "primaryScoreEffect": (
                "none; denominator and classifications remain the Prague "
                "25-cell ledger"
            ),
            "representedPrimaryCells": list(REPRESENTED),
            "representedTransactionScenarios": len(REPRESENTED),
        },
        "cases": rows,
        "format": FORMAT,
        "gasSummary": {
            "blancHigherReceiptGas": sum(delta < 0 for delta in deltas),
            "blancLowerReceiptGas": sum(delta > 0 for delta in deltas),
            "equalReceiptGas": sum(delta == 0 for delta in deltas),
            "referenceMinusBlancTotal": sum(deltas),
        },
        "network": {
            "checkoutCommit": profile["target"]["checkoutCommit"],
            "executionFork": profile["execution"]["fork"],
            "logicalCompilerFork": profile["compiler"]["logicalFork"],
            "testingBackend": profile["compiler"]["testingBackend"],
        },
        "provenance": {
            "artifactGeneratorSha256": sha256_path(ARTIFACT_GENERATOR_PATH),
            "artifactLeanSha256": sha256_path(ARTIFACT_LEAN_PATH),
            "artifactManifestSha256": sha256_path(ARTIFACT_MANIFEST_PATH),
            "currentMainnetHelperSha256": sha256_path(HELPER_PATH),
            "generatorSha256": sha256_path(SCRIPT_PATH),
            "performanceManifestSha256": sha256_path(MANIFEST_PATH),
            "performanceRunnerSha256": sha256_path(PERFORMANCE_RUNNER_PATH),
            "performanceSchemaSha256": sha256_path(PERFORMANCE_SCHEMA_PATH),
            "profileSha256": sha256_path(PROFILE_PATH),
            "referenceLockSha256": sha256_path(REFERENCE_LOCK_PATH),
            "wrapperSha256": sha256_path(WRAPPER_PATH),
        },
        "schema": SCHEMA,
        "scope": {
            "gas": (
                "canonical singleton signed legacy-transaction receipt gas under BPO2; "
                "includes intrinsic/calldata gas, applied refunds, and CREATE code deposit; "
                "the transaction envelope uses BPO2's 16,777,216 protocol gas cap instead "
                "of the primary direct-message campaign's 20,000,000 allowance"
            ),
            "scheduleClaim": (
                "separately labelled current-schedule diagnostic; not a cross-fork "
                "dominance claim and not part of the primary score"
            ),
            "semantics": (
                "receipt status and exact logs plus target existence, nonce, balance, "
                "side-owned runtime identity, and the implementation/admin/fixture slots"
            ),
            "transactionObservabilityLimits": (
                "top-level returndata and nested DELEGATECALL traces are not exposed by "
                "a transaction receipt; those remain checked by the primary Prague "
                "direct-message ledger and differential campaign"
            ),
        },
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


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="explicit current-mainnet target root")
    parser.add_argument("--write", action="store_true", help="replace the committed report")
    args = parser.parse_args(argv)

    validate_current_mainnet_boundary()
    profile = load_profile()
    root = resolve_root(profile, args.root)
    verify_target(root, profile)
    paths = target_paths(root, profile)
    if Path(sys.executable).resolve() != paths.python.resolve():
        fail(f"replay must run under {paths.python}, got {Path(sys.executable)}")

    manifest, performance, fixtures, sides = load_campaign_and_sides()
    summary = render_summary(
        manifest,
        performance,
        fixtures,
        sides,
        root=root,
        profile=profile,
    )
    check_or_write(canonical_bytes(summary), write=args.write)
    verb = "wrote" if args.write else "checked"
    print(
        f"OK — {verb} OssifiableProxy BPO2 replay: "
        f"{len(REPRESENTED)} represented primary transaction scenarios, "
        "A1/A2 outside transaction scope, F2/F4 explicitly warm-state excluded, "
        "zero semantic mismatches"
    )


if __name__ == "__main__":
    try:
        main()
    except (
        ReplayError,
        RuntimeError,
        ImportError,
        KeyError,
        OSError,
        TypeError,
        UnicodeError,
        ValueError,
        performance_schema.SchemaError,
    ) as exc:
        print(
            "REGRESSION — OssifiableProxy BPO2 replay: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
