#!/usr/bin/env python3
"""Generate/check the exact-surface PRORATA BPO2 size and gas comparison.

Every case is one signed legacy transaction in an independent canonical BPO2
block.  Normal mode is read-only and byte-compares the committed result;
``--write`` is the sole writer and is allowed only after every runtime agrees
on the receipt/status and selected post-state projection.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / "scripts" / "reference" / "prorata"
LOCK_PATH = REFERENCE / "runtime-lock.json"
RESULT_PATH = REFERENCE / "benchmark-results.json"
FIXTURE_GENERATOR = ROOT / "scripts" / "gen-prorata-fixtures.py"
PROFILE_PATH = ROOT / "scripts" / "current-mainnet-target.json"
HELPER_PATH = ROOT / "scripts" / "current_mainnet.py"
BLANC_SOURCE = ROOT / "Blanc" / "ProrataCode.lean"

from current_mainnet import (  # noqa: E402
    load_profile,
    resolve_root,
    run_t8n,
    target_paths,
    verify_target,
)


CURRENT_MAINNET_PUBLIC_API = {
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
}
EXPECTED_LOCK_SHA256 = "c39ca09114507c775624b0d78106c2ddd90390324d6168c113270c710dd8414e"
EXPECTED_BLANC_BYTES = 343
EXPECTED_BLANC_SHA256 = "f03adb3d97f2519d83e6dc125fd3ca66c03bfeaede491ad8b76fc9f58884555b"
FUNDED_BALANCE = 2 ** 130


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def validate_current_mainnet_boundary() -> None:
    """Pin this consumer to the five-function, fork-override-free API."""
    source = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    legacy_env = "EELS" + "_ROOT"
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and node.value == legacy_env:
            raise RuntimeError("benchmark cross-wires the historical root environment")
        modules = []
        if isinstance(node, ast.ImportFrom) and node.module is not None:
            modules = [node.module]
        elif isinstance(node, ast.Import):
            modules = [alias.name for alias in node.names]
        if any(module == "subprocess" or module.startswith("ethereum.")
               or module.startswith("ethereum_spec_tools") for module in modules):
            raise RuntimeError("benchmark bypasses the current-mainnet execution API")
    imports = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module == "current_mainnet"
    ]
    imported = {
        alias.name for node in imports for alias in node.names if alias.asname is None
    }
    if len(imports) != 1 or imported != CURRENT_MAINNET_PUBLIC_API \
            or any(alias.asname is not None for node in imports for alias in node.names):
        raise RuntimeError("benchmark must import exactly the five public API names")
    calls = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id in CURRENT_MAINNET_PUBLIC_API
    ]
    counts = {name: 0 for name in CURRENT_MAINNET_PUBLIC_API}
    for call in calls:
        counts[call.func.id] += 1
    if counts != {name: 1 for name in CURRENT_MAINNET_PUBLIC_API}:
        raise RuntimeError(f"current-mainnet public API call inventory differs: {counts}")
    transition = next(call for call in calls if call.func.id == "run_t8n")
    keywords = {keyword.arg: keyword.value for keyword in transition.keywords}
    if len(transition.args) != 3 or set(keywords) != {
        "root", "profile", "state_test", "timeout",
    }:
        raise RuntimeError("run_t8n call must have three inputs and four exact keywords")
    if not isinstance(keywords["state_test"], ast.Constant) \
            or keywords["state_test"].value is not False:
        raise RuntimeError("benchmark must use explicit block semantics")
    if not isinstance(keywords["timeout"], ast.Constant) \
            or keywords["timeout"].value != 120:
        raise RuntimeError("benchmark run_t8n timeout must remain explicit at 120 seconds")


def load_fixture_generator():
    spec = importlib.util.spec_from_file_location("prorata_fixture_generator", FIXTURE_GENERATOR)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load fixture generator {FIXTURE_GENERATOR}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_reference_runtimes() -> dict[str, bytes]:
    lock_bytes = LOCK_PATH.read_bytes()
    digest = sha256_bytes(lock_bytes)
    if digest != EXPECTED_LOCK_SHA256:
        raise RuntimeError(f"reference lock digest differs: {digest}")
    lock = json.loads(lock_bytes)
    if lock.get("schema") != 1:
        raise RuntimeError("reference lock schema differs")
    for source in lock["sources"].values():
        path = REFERENCE / source["path"]
        if path.parent != REFERENCE or sha256_path(path) != source["sha256"]:
            raise RuntimeError(f"reference source digest differs: {path}")
    result = {}
    names = {
        "Solidity legacy": "solidityLegacy",
        "Solidity viaIR / Yul": "yul",
    }
    for display, key in names.items():
        item = lock["runtimes"][key]
        runtime = bytes.fromhex(item["hex"])
        if len(runtime) != item["bytes"] or sha256_bytes(runtime) != item["sha256"]:
            raise RuntimeError(f"locked runtime identity differs: {display}")
        result[display] = runtime
    return result


@dataclass(frozen=True)
class Scenario:
    name: str
    target_balance: int
    supply: int
    owner: str
    owner_shares: int
    transaction_to: str
    transaction_data: str
    transaction_value: int = 0
    receiver_code: str | None = None
    expected_status: str = "0x1"


def scenarios(gen: Any) -> tuple[Scenario, ...]:
    caller = gen.derive_address(1)
    deposit = "0x" + gen.selector("deposit()").hex()
    return (
        Scenario("donation-empty", 0, 0, caller, 0, gen.PRORATA, "0x", 17),
        Scenario("unknown-selector", 0, 0, caller, 0, gen.PRORATA, "0xdeadbeef",
                 expected_status="0x0"),
        Scenario("deposit-genesis", 0, 0, caller, 0, gen.PRORATA, deposit, 7),
        Scenario("deposit-existing", 11, 7000, caller, 5000, gen.PRORATA, deposit, 3),
        Scenario("withdraw-partial", 11, 7000, caller, 5000, gen.PRORATA,
                 gen.abi_uint("withdraw(uint256)", 1000)),
        Scenario("withdraw-full", 1002, 2, caller, 2, gen.PRORATA,
                 gen.abi_uint("withdraw(uint256)", 2)),
        Scenario("view-shares", 11, 7000, caller, 5000, gen.PRORATA,
                 gen.abi_uint("convertToShares(uint256)", 3)),
        Scenario("view-assets", 11, 7000, caller, 5000, gen.PRORATA,
                 gen.abi_uint("convertToAssets(uint256)", 1000)),
        Scenario("withdraw-rejected-payout", 1002, 2, gen.RECEIVER, 2,
                 gen.RECEIVER, "0x", receiver_code=gen.rejecting_receiver_code(gen.PRORATA)),
        Scenario("withdraw-reentrant", 1002, 2, gen.RECEIVER, 2,
                 gen.RECEIVER, "0x", receiver_code=gen.receiver_code(gen.PRORATA)),
    )


def scenario_inputs(gen: Any, scenario: Scenario, runtime: bytes):
    caller = gen.derive_address(1)
    storage = {}
    if scenario.supply:
        storage[gen.SUPPLY_SLOT] = scenario.supply
    if scenario.owner_shares:
        storage[int(scenario.owner, 16)] = scenario.owner_shares
    alloc = gen.system_alloc()
    alloc.update({
        gen.PRORATA: gen.account(scenario.target_balance, "0x" + runtime.hex(), storage),
        caller: gen.account(FUNDED_BALANCE),
    })
    if scenario.receiver_code is not None:
        alloc[gen.RECEIVER] = gen.account(0, scenario.receiver_code)
    _, _, environment = gen.transition_environment(alloc)
    transaction = gen.tx(
        1, 0, scenario.transaction_to, scenario.transaction_data,
        scenario.transaction_value,
    )
    return alloc, environment, [transaction]


def integer(value: Any) -> int:
    if isinstance(value, str):
        return int(value, 16)
    return int(value)


def state_projection(gen: Any, post: dict[str, Any], scenario: Scenario) -> dict[str, Any]:
    projection = {
        "targetBalance": gen.balance_of(post, gen.PRORATA),
        "supply": gen.storage_of(post, gen.PRORATA, gen.SUPPLY_SLOT),
        "ownerShares": gen.storage_of(post, gen.PRORATA, int(scenario.owner, 16)),
    }
    if scenario.receiver_code is not None:
        projection.update({
            "receiverBalance": gen.balance_of(post, gen.RECEIVER),
            "receiverSlot0": gen.storage_of(post, gen.RECEIVER, 0),
        })
    return projection


def run_case(gen: Any, scenario: Scenario, runtime: bytes, *, root: Path,
             profile: dict[str, Any]) -> dict[str, Any]:
    alloc, environment, transactions = scenario_inputs(gen, scenario, runtime)
    outputs = run_t8n(
        alloc, environment, transactions, root=root, profile=profile,
        state_test=False, timeout=120,
    )
    if outputs.result.get("rejected") != []:
        raise RuntimeError(f"{scenario.name}: transaction rejected: {outputs.result['rejected']!r}")
    receipts = outputs.result.get("receipts", [])
    if len(receipts) != 1:
        raise RuntimeError(f"{scenario.name}: expected one receipt, got {len(receipts)}")
    receipt = receipts[0]
    status = receipt.get("status")
    if status != scenario.expected_status:
        raise RuntimeError(
            f"{scenario.name}: expected receipt status {scenario.expected_status}, got {status}"
        )
    if "gasUsed" in receipt:
        receipt_gas = integer(receipt["gasUsed"])
        receipt_gas_source = "gasUsed"
    elif "cumulativeGasUsed" in receipt:
        # Every benchmark block is a singleton, so the consensus cumulative
        # field is exactly this transaction's receipt gas.
        receipt_gas = integer(receipt["cumulativeGasUsed"])
        receipt_gas_source = "singleton cumulativeGasUsed"
    else:
        raise RuntimeError(
            f"{scenario.name}: receipt has no gas field: {sorted(receipt)}"
        )
    block_gas = integer(outputs.result["gasUsed"])
    if receipt_gas != block_gas:
        raise RuntimeError(
            f"{scenario.name}: singleton receipt/block gas differ: {receipt_gas} != {block_gas}"
        )
    logs_bloom = outputs.result["logsBloom"]
    if integer(logs_bloom) != 0:
        raise RuntimeError(f"{scenario.name}: benchmark transaction emitted a log")
    return {
        "receiptStatus": status,
        "logsBloom": logs_bloom,
        "state": state_projection(gen, outputs.alloc, scenario),
        "receiptGasUsed": receipt_gas,
        "receiptGasSource": receipt_gas_source,
    }


def runtime_summary(runtime: bytes) -> dict[str, Any]:
    return {
        "bytes": len(runtime),
        "sha256": sha256_bytes(runtime),
        "codeDepositGas": 200 * len(runtime),
    }


def render_summary(gen: Any, runtimes: dict[str, bytes], *, root: Path,
                   profile: dict[str, Any]) -> dict[str, Any]:
    rows = {}
    mismatches = []
    for scenario in scenarios(gen):
        observations = {
            name: run_case(gen, scenario, runtime, root=root, profile=profile)
            for name, runtime in runtimes.items()
        }
        semantic = {
            name: {key: value for key, value in observation.items()
                   if key not in {"receiptGasUsed", "receiptGasSource"}}
            for name, observation in observations.items()
        }
        if len({json.dumps(value, sort_keys=True) for value in semantic.values()}) != 1:
            mismatches.append({"case": scenario.name, "observations": semantic})
        blanc_gas = observations["Blanc"]["receiptGasUsed"]
        rows[scenario.name] = {
            name: {
                **observation,
                "gasDeltaVsBlanc": observation["receiptGasUsed"] - blanc_gas,
            }
            for name, observation in observations.items()
        }
    if mismatches:
        raise RuntimeError(f"semantic mismatch: {json.dumps(mismatches, sort_keys=True)}")

    dominance = {}
    for name in runtimes:
        if name == "Blanc":
            continue
        deltas = [rows[case][name]["gasDeltaVsBlanc"] for case in rows]
        dominance[name] = {
            "blancLowerGasCases": sum(delta > 0 for delta in deltas),
            "equalGasCases": sum(delta == 0 for delta in deltas),
            "blancHigherGasCases": sum(delta < 0 for delta in deltas),
            "competitorGasMinusBlancTotal": sum(deltas),
        }
    return {
        "schema": 1,
        "network": {
            "executionFork": profile["execution"]["fork"],
            "logicalCompilerFork": profile["compiler"]["logicalFork"],
            "testingBackend": profile["compiler"]["testingBackend"],
            "checkoutCommit": profile["target"]["checkoutCommit"],
        },
        "scope": {
            "gas": "canonical transaction receipt gas for one signed legacy transaction in an independent BPO2 block; derived from singleton cumulativeGasUsed when the t8n receipt omits gasUsed; includes intrinsic/calldata gas and applied refunds; excludes code-deposit gas",
            "semantics": "receipt status, block log bloom, target balance/supply/owner shares, and receiver balance/slot when present; top-level return data is outside this transaction-state projection",
        },
        "provenance": {
            "profileSha256": sha256_path(PROFILE_PATH),
            "currentMainnetHelperSha256": sha256_path(HELPER_PATH),
            "fixtureGeneratorSha256": sha256_path(FIXTURE_GENERATOR),
            "referenceLockSha256": sha256_path(LOCK_PATH),
            "blancRuntimeSourceSha256": sha256_path(BLANC_SOURCE),
        },
        "runtimes": {name: runtime_summary(runtime) for name, runtime in runtimes.items()},
        "semanticCases": len(rows),
        "semanticMismatches": [],
        "gasDominance": dominance,
        "cases": rows,
    }


def check_or_write(content: str, *, write: bool) -> None:
    if write:
        RESULT_PATH.parent.mkdir(parents=True, exist_ok=True)
        temporary = RESULT_PATH.with_name(f".{RESULT_PATH.name}.tmp")
        temporary.write_text(content, encoding="utf-8")
        temporary.replace(RESULT_PATH)
        return
    if not RESULT_PATH.is_file():
        raise RuntimeError(f"benchmark result missing: {RESULT_PATH}; run with --write")
    if RESULT_PATH.read_text(encoding="utf-8") != content:
        raise RuntimeError(f"benchmark result differs: {RESULT_PATH}; run with --write")


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="explicit current-mainnet target root")
    parser.add_argument("--write", action="store_true", help="replace benchmark JSON")
    args = parser.parse_args(argv)

    validate_current_mainnet_boundary()
    profile = load_profile()
    root = resolve_root(profile, args.root)
    verify_target(root, profile)
    paths = target_paths(root, profile)
    if Path(sys.executable).resolve() != paths.python.resolve():
        raise RuntimeError(f"benchmark must run under {paths.python}, got {Path(sys.executable)}")

    gen = load_fixture_generator()
    blanc = bytes.fromhex(gen.runtime_hex()[2:])
    if len(blanc) != EXPECTED_BLANC_BYTES or sha256_bytes(blanc) != EXPECTED_BLANC_SHA256:
        raise RuntimeError("Blanc runtime differs from the selected 343-byte artifact")
    runtimes = {"Blanc": blanc, **load_reference_runtimes()}
    summary = render_summary(gen, runtimes, root=root, profile=profile)
    content = json.dumps(summary, indent=2, sort_keys=True) + "\n"
    check_or_write(content, write=args.write)
    verb = "wrote" if args.write else "checked"
    print(
        f"OK — {verb} PRORATA BPO2 benchmark: {summary['semanticCases']} scenarios, "
        f"3 runtimes, zero selected-projection mismatches"
    )


if __name__ == "__main__":
    main()
