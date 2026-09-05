#!/usr/bin/env python3
"""Generate DRIP's deterministic BPO2 transaction fixtures.

``--plan`` and ``--self-test`` remain pure and never invoke the target. Runtime
mode is explicit ``--root TARGET_ROOT``; it reconstructs every case in memory,
executes linked BPO2 blocks and per-transaction prefixes, and only ``--write``
may commit the resulting population after all observations pass. Do not feed
plan output to Jaune as a fixture.
"""
from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

from current_mainnet import (  # noqa: E402
    load_profile, resolve_root, run_t8n, target_paths, verify_target,
)

from drip_oracle import (
    CHI_SLOT, RHO_SLOT, PIE_SLOT, SCALE, MAX_CHI, MAX_ELAPSED, MAX_ASSET,
    MAX_UNITS, MAX_PIE, Drip, Revert, rpow_checked,
)

ROOT = Path(__file__).resolve().parents[1]
TARGET = "0x000000000000000000000000000000000000d219"
# Ethereum addresses of private keys 1 and 2. Integration must independently
# derive these with the identity-checked target signer before executing.
ALICE = "0x7e5f4552091a69125d5dfcb7b8c2659029395bdf"
BOB = "0x2b5ad5c4795c026514f8317c7a215e218dccd6cf"
KEYS = {ALICE: 1, BOB: 2}
START = 1_767_747_671 + 12
FUNDS = 2**200
GAS = 1_000_000
GAS_PRICE = 10
SELECTORS = {
    "convertToAssets": "07a2d13a", "exit": "7f8661a1",
    "convertToUnits": "9227149a", "drip": "9f678cca", "join": "b688a363",
}
ARGUMENTS = {"convertToAssets", "exit", "convertToUnits"}
OBLIGATIONS = (
    "deployment-genesis", "drip-same-timestamp", "drip-local-under-k2",
    "drip-local-over-k3", "drip-one-year", "drip-max-elapsed",
    "drip-elapsed-overflow-revert", "drip-timestamp-regression-revert",
    "drip-chi-below-scale-revert", "drip-chi-above-cap-revert",
    "drip-post-chi-cap-boundary", "drip-post-chi-cap-revert", "join-zero-value",
    "join-genesis-first", "join-future-auto-drip", "join-max-asset",
    "join-over-max-asset-revert", "join-total-or-row-cap-revert",
    "join-zero-unit-credit", "exit-zero-unit-call", "exit-partial", "exit-full",
    "exit-future-auto-drip", "exit-insufficient-units-revert",
    "exit-underfunded-call-rollback", "exit-rejecting-recipient-rollback",
    "exit-successful-reentry", "view-units-fresh-consistency",
    "view-assets-fresh-consistency", "view-arithmetic-cap-boundaries",
    "receive-value-donation", "receive-zero-value", "unknown-selector-revert",
    "short-and-trailing-calldata-revert", "value-bearing-nonpayable-revert",
    "multi-participant-conservation", "segmentation-k3-versus-k1-k2",
    "receipt-returndata-log-matrix",
)
# Every pending entry is a missing executable assertion, never credited coverage.
PENDING = {
    "deployment-genesis": ["actual CREATE transaction and derived address", "creation receipt", "installed runtime and complete genesis storage"],
    "exit-zero-unit-call": ["recipient observed CALL even when payout is zero", "CALL input/value/gas observation"],
    "exit-rejecting-recipient-rollback": ["rejecting recipient bytecode", "nested writes/logs rollback", "outer empty revert instead of child payload"],
    "exit-successful-reentry": ["reentrant recipient bytecode", "ordered child-entry debits", "ordered committed nested logs and payouts"],
    "receipt-returndata-log-matrix": ["returndata observer bytecode for success and revert", "receipt and ordered raw log assertions across nested calls"],
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


CURRENT_MAINNET_PUBLIC_API = {
    "load_profile", "resolve_root", "verify_target", "target_paths", "run_t8n",
}


def validate_current_mainnet_boundary():
    """Keep this consumer on the shared, fork-locked public API."""
    tree = ast.parse(Path(__file__).read_text(encoding="utf-8"))
    imports = [node for node in ast.walk(tree)
               if isinstance(node, ast.ImportFrom) and node.module == "current_mainnet"]
    imported = {alias.name for node in imports for alias in node.names
                if alias.asname is None}
    require(len(imports) == 1 and imported == CURRENT_MAINNET_PUBLIC_API
            and all(alias.asname is None for node in imports for alias in node.names),
            "generator must import exactly the five current-mainnet API names")
    calls = [node for node in ast.walk(tree)
             if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
             and node.func.id in CURRENT_MAINNET_PUBLIC_API]
    counts = {name: 0 for name in CURRENT_MAINNET_PUBLIC_API}
    for call in calls:
        counts[call.func.id] += 1
    require(counts == {name: 1 for name in CURRENT_MAINNET_PUBLIC_API},
            f"current-mainnet API call inventory differs: {counts}")
    transition = next(call for call in calls if call.func.id == "run_t8n")
    keywords = {keyword.arg: keyword.value for keyword in transition.keywords}
    require(len(transition.args) == 3 and set(keywords) == {
        "root", "profile", "state_test", "timeout",
    }, "run_t8n call must use the explicit block API")
    require(isinstance(keywords["state_test"], ast.Constant)
            and keywords["state_test"].value is False,
            "DRIP block generation must disable state-test mode")
    require(isinstance(keywords["timeout"], ast.Constant)
            and keywords["timeout"].value == 120,
            "DRIP t8n timeout must remain 120 seconds")


def q(n):
    require(type(n) is int and n >= 0, "quantity must be a nonnegative integer")
    digits = f"{n:x}"
    return "0x" + ("0" if len(digits) % 2 else "") + digits


def abi(method, argument=0):
    if method == "receive":
        return "0x"
    require(method in SELECTORS, f"unknown ABI method {method}")
    require(0 <= argument < 2**256, "ABI argument out of word")
    return "0x" + SELECTORS[method] + (f"{argument:064x}" if method in ARGUMENTS else "")


def artifacts():
    spec = importlib.util.spec_from_file_location("drip_fixture_literal", ROOT / "scripts/check-runtime-bytes.py")
    require(spec is not None and spec.loader is not None, "missing strict runtime parser")
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    runtime = parser.parse_lean_literal(ROOT / "Blanc/DripCode.lean", "code")
    creation = parser.parse_lean_literal(ROOT / "Blanc/DripCreationCode.lean", "creationCodeLiteral")
    require(len(runtime) == 1917 and len(creation) == 2156, "frozen artifact size changed")
    require(creation[239:] == runtime, "creation suffix does not bind runtime")
    return runtime, creation


def storage(model):
    rows = {CHI_SLOT: model.chi, RHO_SLOT: model.rho, PIE_SLOT: model.Pie, **model.rows}
    return {q(k): q(v) for k, v in sorted(rows.items()) if v}


def target_account(model, runtime):
    return {"balance": q(model.balance), "nonce": "0x01", "code": "0x" + runtime.hex(), "storage": storage(model)}


def execute_model(model, caller, data, value, now):
    """Independent exact ABI boundary, followed by integer model semantics."""
    before = model.snapshot()
    try:
        raw = bytes.fromhex(data[2:])
        if not raw:
            model.receive(value)
            result = None
        else:
            method = next((name for name, sel in SELECTORS.items() if raw[:4].hex() == sel), None)
            if method is None or len(raw) != (36 if method in ARGUMENTS else 4):
                raise Revert("malformed-or-unknown-calldata")
            if value and method != "join":
                raise Revert("nonpayable")
            argument = int.from_bytes(raw[4:], "big")
            if method == "drip": result = model.drip(now)
            elif method == "join": result = model.join(int(caller, 16), value, now)
            elif method == "exit": result = model.exit(int(caller, 16), argument, now)
            elif method == "convertToUnits": result = model.convert_to_units(argument, now)
            else: result = model.convert_to_assets(argument, now)
        return {"status": 1, "returndata": "0x" if result is None else "0x" + f"{result:064x}", "logs": []}
    except Revert as error:
        require(model.snapshot() == before, "failed call did not restore complete pre-state")
        return {"status": 0, "returndata": "0x", "logs": [], "reason": error.reason}


def model_at(*, chi=SCALE, rho=START, total=0, row=0, balance=0):
    model = Drip(START)
    model.chi, model.rho, model.Pie, model.balance = chi, rho, total, balance
    if row: model.rows[int(ALICE, 16)] = row
    return model


def step(method, argument=0, *, value=0, now=START, caller=ALICE, raw=None):
    return {"caller": caller, "data": abi(method, argument) if raw is None else raw, "value": value, "timestamp": now}


def cases(runtime):
    population = []

    def add(name, obligation, operations, initial=None, statuses=None):
        model = copy.deepcopy(initial if initial is not None else model_at())
        nonces = {ALICE: 0, BOB: 0}
        authored = []
        for index, op in enumerate(operations):
            pre = target_account(model, runtime)
            outcome = execute_model(model, op["caller"], op["data"], op["value"], op["timestamp"])
            post = target_account(model, runtime)
            if statuses is not None:
                require(outcome["status"] == statuses[index], f"{name}/{index}: wrong designed outcome")
            payout = max(0, model_balance(pre) + (op["value"] if outcome["status"] else 0) - model.balance)
            nonce = nonces[op["caller"]]
            nonces[op["caller"]] += 1
            authored.append({
                "index": index, "timestamp": op["timestamp"], "caller": op["caller"],
                "transaction": {"type": "0x00", "chainId": "0x01", "nonce": q(nonce),
                    "gasPrice": q(GAS_PRICE), "gas": q(GAS), "to": TARGET,
                    "value": q(op["value"]), "input": op["data"],
                    "secretKey": "0x" + f"{KEYS[op['caller']]:064x}"},
                "preTarget": pre, "expectedTarget": post,
                "expectedOutcome": outcome,
                # This is a transfer delta, not the final EOA balance. Receipts
                # supply the actual fee separately; a failed call still pays gas.
                "callerTransferDelta": payout - (op["value"] if outcome["status"] else 0),
            })
        require(all(a["timestamp"] <= b["timestamp"] for a, b in zip(authored, authored[1:])), f"{name}: decreasing transaction time")
        population.append({"name": name, "obligation": obligation, "initialCallerBalance": q(FUNDS),
                           "steps": authored, "rootKind": "synthetic-preallocation", "executed": False})

    for label, elapsed in (("drip-same-timestamp", 0), ("drip-local-under-k2", 2),
        ("drip-local-over-k3", 3), ("drip-one-year", 31_536_000), ("drip-max-elapsed", MAX_ELAPSED)):
        add(label, label, [step("drip", now=START + elapsed)], statuses=[1])
    factor, _ = rpow_checked(1_000_000_001_547_125_957_863_212_448, MAX_ELAPSED)
    last = ((MAX_CHI + 1) * SCALE - 1) // factor
    for label, initial, now, status in (
        ("drip-elapsed-overflow-revert", model_at(), START + MAX_ELAPSED + 1, 0),
        ("drip-timestamp-regression-revert", model_at(rho=START + 1), START, 0),
        ("drip-chi-below-scale-revert", model_at(chi=SCALE - 1), START, 0),
        ("drip-chi-above-cap-revert", model_at(chi=MAX_CHI + 1), START, 0),
        ("drip-post-chi-cap-boundary", model_at(chi=last), START + MAX_ELAPSED, 1),
        ("drip-post-chi-cap-revert", model_at(chi=last + 1), START + MAX_ELAPSED, 0),
    ):
        add(label, label, [step("drip", now=now)], initial, [status])
    for label, amount, now, status in (
        ("join-zero-value", 0, START, 1), ("join-genesis-first", SCALE, START, 1),
        ("join-future-auto-drip", SCALE, START + 3, 1),
        ("join-max-asset", MAX_ASSET, START, 1),
        ("join-over-max-asset-revert", MAX_ASSET + 1, START, 0),
        ("join-zero-unit-credit", 1, START + 1, 1),
    ):
        add(label, label, [step("join", value=amount, now=now)], statuses=[status])
    for suffix, initial in (
        ("total-result", model_at(total=MAX_PIE)), ("row-result", model_at(row=MAX_UNITS)),
        ("total-pre", model_at(total=MAX_PIE + 1)), ("row-pre", model_at(row=MAX_UNITS + 1)),
    ):
        add("join-cap-" + suffix, "join-total-or-row-cap-revert", [step("join", value=1)], initial, [0])
    for label, units, now, initial, status in (
        ("exit-zero-unit-call", 0, START, model_at(), 1),
        ("exit-partial", 4, START, model_at(total=10, row=10, balance=10), 1),
        ("exit-full", 10, START, model_at(total=10, row=10, balance=10), 1),
        ("exit-future-auto-drip", SCALE, START + 3, model_at(total=SCALE, row=SCALE, balance=2*SCALE), 1),
        ("exit-insufficient-units-revert", 11, START, model_at(total=10, row=10, balance=10), 0),
        ("exit-underfunded-call-rollback", 10, START + 31_536_000, model_at(total=10, row=10, balance=9), 0),
    ):
        add(label, label, [step("exit", units, now=now)], initial, [status])
    add("view-units-fresh-consistency", "view-units-fresh-consistency", [
        step("convertToUnits", SCALE, now=START+3), step("join", value=SCALE, now=START+3)], statuses=[1, 1])
    add("view-assets-fresh-consistency", "view-assets-fresh-consistency", [
        step("convertToAssets", SCALE, now=START+3), step("exit", SCALE, now=START+3)],
        model_at(total=SCALE, row=SCALE, balance=2*SCALE), [1, 1])
    for method in ("convertToUnits", "convertToAssets"):
        for arg, status in ((0, 1), (MAX_UNITS, 1), (MAX_UNITS+1, 0)):
            add(f"view-cap-{method}-{arg}", "view-arithmetic-cap-boundaries", [step(method, arg)], model_at(chi=MAX_CHI), [status])
    for amount in (0, 17):
        label = "receive-zero-value" if amount == 0 else "receive-value-donation"
        add(label, label, [step("receive", value=amount)], model_at(total=5, row=5, balance=5), [1])
    add("unknown-selector-revert", "unknown-selector-revert", [step("receive", raw="0xdeadbeef")], statuses=[0])
    malformed = ["0x00", "0x0000", "0x000000"]
    for method in SELECTORS:
        canonical = abi(method, 1)
        malformed.extend((canonical[:-2], canonical + "00"))
    add("short-and-trailing-calldata-revert", "short-and-trailing-calldata-revert", [step("receive", raw=data) for data in malformed], statuses=[0]*len(malformed))
    nonpayable = [step(method, 0, value=1) for method in SELECTORS if method != "join"]
    add("value-bearing-nonpayable-revert", "value-bearing-nonpayable-revert", nonpayable, statuses=[0]*len(nonpayable))
    add("multi-participant-conservation", "multi-participant-conservation", [
        step("join", value=100), step("join", value=75, caller=BOB), step("receive", value=25),
        step("drip", now=START+3), step("exit", 40, now=START+3), step("exit", 75, caller=BOB, now=START+3)], statuses=[1]*6)
    add("segmentation-one", "segmentation-k3-versus-k1-k2", [step("drip", now=START+3)], statuses=[1])
    add("segmentation-split", "segmentation-k3-versus-k1-k2", [step("drip", now=START+1), step("drip", now=START+3)], statuses=[1, 1])
    return population


def account_from_alloc(alloc, address):
    value = alloc.get(address.lower()) or alloc.get(address)
    require(value is not None, f"missing account {address}")
    return value


def target_at(alloc, address):
    value = alloc.get(address.lower()) or alloc.get(address)
    return value


def sender_prefix_check(before, after, operation, receipt):
    """Check nonce/fee/value deltas at one actual transaction prefix."""
    caller = operation["caller"].lower()
    before_sender = account_from_alloc(before, caller)
    after_sender = account_from_alloc(after, caller)
    used = int(receipt["gasUsed"], 16)
    require(0 < used < int(operation["transaction"]["gas"], 16), "invalid finite gas")
    expected_nonce = int(operation["transaction"]["nonce"], 16)
    require(int(before_sender["nonce"], 16) == expected_nonce, "sender nonce pre-state differs")
    require(int(after_sender["nonce"], 16) == expected_nonce + 1, "sender nonce did not advance")
    expected_balance = int(before_sender["balance"], 16) \
        + operation["callerTransferDelta"] - used * GAS_PRICE
    require(int(after_sender["balance"], 16) == expected_balance,
            "sender value transfer or fee differs")
    require(after_sender.get("code", "0x") == before_sender.get("code", "0x"),
            "sender code changed")
    require(normalized_storage(after_sender.get("storage", {}))
            == normalized_storage(before_sender.get("storage", {})),
            "sender storage changed")


def render_fixture(name, initial_alloc, linked, profile):
    from drip_fixture_blocks import fixture
    return fixture(name, initial_alloc, linked["genesis"], linked["genesis"]["hash"],
                   linked["blocks"], linked["post"], linked["lastblockhash"], profile)


def runtime_transaction_population(root, profile, runtime, creation, paths):
    """Execute all cases and return JSON-ready fixtures plus manifest rows."""
    from drip_fixture_blocks import (
        account, create_address, creation_transaction, execute_linked_blocks,
        derive_address, system_alloc,
    )
    from drip_fixture_observers import (
        log_entry, nested_overdraw, observer_code, observer_expectations,
    )

    require(Path(sys.executable).resolve() == paths.python.resolve(),
            f"generator must run under isolated target Python {paths.python}")
    alice = derive_address(1)
    bob = derive_address(2)
    require(alice == ALICE and bob == BOB, "signer derivation does not match frozen identities")

    def transition(alloc, environment_value, transactions):
        return run_t8n(alloc, environment_value, transactions, root=root, profile=profile,
                        state_test=False, timeout=120)

    files = {}
    manifest = []
    for case in cases(runtime):
        initial = system_alloc()
        first = case["steps"][0]
        initial[TARGET] = first["preTarget"]
        initial[ALICE] = account(FUNDS)
        initial[BOB] = account(FUNDS)

        def prefix_checker(_block, index, before, after, result, *, case=case):
            operation = case["steps"][index]
            actual_pre = target_at(before, TARGET)
            actual_post = target_at(after, TARGET)
            require(actual_pre is not None, f"{case['name']}/{index}: target pre-state absent")
            check_target(actual_pre, operation["preTarget"])
            require(actual_post is not None, f"{case['name']}/{index}: target post-state absent")
            check_target(actual_post, operation["expectedTarget"])
            receipts = result.get("receipts", [])
            require(receipts, f"{case['name']}/{index}: missing prefix receipt")
            receipt = receipts[-1]
            require(int(receipt.get("status", "0x"), 16) == operation["expectedOutcome"]["status"],
                    f"{case['name']}/{index}: receipt status differs")
            require(receipt.get("logs", []) == operation["expectedOutcome"].get("logs", []),
                    f"{case['name']}/{index}: direct DRIP logs differ")
            sender_prefix_check(before, after, operation, receipt)

        scheduled = [{"timestamp": operation["timestamp"], "transaction": operation["transaction"]}
                     for operation in case["steps"]]
        linked = execute_linked_blocks(initial, scheduled, run_transition=transition,
                                       prefix_checker=prefix_checker)
        files[f"{case['name']}.json"] = json.dumps(
            render_fixture(case["name"], initial, linked, profile), indent=2) + "\n"
        manifest.append({"name": case["name"], "obligation": case["obligation"],
                         "steps": len(case["steps"]), "executionEvidence": True,
                         "fixture": f"{case['name']}.json"})

    # Every direct case gets an observer twin for returndata.  t8n exposes
    # receipts and state but not transaction returndata, so the twin forwards
    # the exact calldata/value through a deterministic helper and records the
    # inner status, return size and return word in independently checked
    # storage/logs.  The EOA still signs and pays the outer transaction.
    observer_helpers = {ALICE: "0x000000000000000000000000000000000000d220",
                        BOB: "0x000000000000000000000000000000000000d221"}
    observer_runtime = {
        address: observer_code(TARGET, "ordinary")
        for address in observer_helpers.values()
    }
    for case in cases(runtime):
        mapping = observer_helpers

        def remap_target(account_value):
            storage_value = {}
            for key, value in account_value["storage"].items():
                slot = int(key, 16)
                for source, destination in mapping.items():
                    if slot == int(source, 16):
                        slot = int(destination, 16)
                        break
                storage_value[q(slot)] = value
            return {**account_value, "storage": storage_value}

        initial = system_alloc()
        initial[TARGET] = remap_target(case["steps"][0]["preTarget"])
        for caller, helper in observer_helpers.items():
            initial[helper] = account(0, observer_runtime[helper])
            initial[caller] = account(FUNDS)
        helper_balances = {helper: 0 for helper in observer_helpers.values()}
        helper_storages = {helper: {} for helper in observer_helpers.values()}

        def observer_prefix_checker(_block, index, before, after, result,
                                    *, case=case, helper_balances=helper_balances,
                                    helper_storages=helper_storages):
            operation = case["steps"][index]
            helper = observer_helpers[operation["caller"]]
            expected_target = remap_target(operation["expectedTarget"])
            actual_pre = target_at(before, TARGET)
            actual_post = target_at(after, TARGET)
            require(actual_pre is not None and actual_post is not None,
                    f"observer/{case['name']}/{index}: target account missing")
            check_target(actual_pre, remap_target(operation["preTarget"]))
            check_target(actual_post, expected_target)
            receipt = result["receipts"][-1]
            require(int(receipt["status"], 16) == 1,
                    f"observer/{case['name']}/{index}: outer receipt reverted")
            inner_status = operation["expectedOutcome"]["status"]
            raw_return = operation["expectedOutcome"]["returndata"]
            return_word = int(raw_return, 16) if raw_return != "0x" else 0
            return_size = 32 if raw_return != "0x" else 0
            helper_balances[helper] += operation["value"]
            if inner_status:
                helper_balances[helper] -= operation["value"]
                if operation["data"][2:10].lower() == SELECTORS["exit"]:
                    helper_balances[helper] += return_word
            expected_slots = {0: inner_status, 1: return_size, 2: return_word}
            helper_storages[helper].update(expected_slots)
            expected_logs = [log_entry(helper, 0xD21902,
                                       [inner_status, return_size, return_word])]
            if (inner_status and operation["data"][2:10].lower() == SELECTORS["exit"]):
                expected_slots.update({3: 1, 4: return_word, 5: 0, 6: int(TARGET, 16)})
                helper_storages[helper].update(expected_slots)
                expected_logs.insert(0, log_entry(helper, 0xD21901,
                                                  [1, return_word, 0, int(TARGET, 16)]))
            expected_observer = {
                "balance": q(helper_balances[helper]), "nonce": "0x0",
                "code": observer_runtime[helper],
                "storage": {q(key): q(value) for key, value in helper_storages[helper].items() if value},
            }
            check_target(account_from_alloc(after, helper), expected_observer)
            require(receipt.get("logs", []) == expected_logs,
                    f"observer/{case['name']}/{index}: exact return logs differ")
            sender_prefix_check(before, after, {
                "caller": operation["caller"], "callerTransferDelta": -operation["value"],
                "transaction": {**operation["transaction"], "to": helper},
            }, receipt)

        scheduled = []
        for operation in case["steps"]:
            helper = observer_helpers[operation["caller"]]
            scheduled.append({"timestamp": operation["timestamp"],
                              "transaction": {**operation["transaction"], "to": helper}})
        linked = execute_linked_blocks(initial, scheduled, run_transition=transition,
                                       prefix_checker=observer_prefix_checker)
        observer_name = f"observer-{case['name']}"
        files[f"{observer_name}.json"] = json.dumps(
            render_fixture(observer_name, initial, linked, profile), indent=2) + "\n"
        manifest.append({"name": observer_name, "obligation": case["obligation"],
                         "steps": len(case["steps"]), "executionEvidence": True,
                         "fixture": f"{observer_name}.json",
                         "observerHelpers": sorted(observer_helpers.values())})

    # A real constructor transaction is a separate fixture.  The target is
    # absent in the genesis allocation and is checked at the CREATE-derived
    # address, so a decoy account with equal-length runtime cannot pass.
    create_target = create_address(alice, 0)
    initial = system_alloc()
    initial[ALICE] = account(FUNDS)
    create_tx = creation_transaction(1, 0, creation)
    require("to" not in create_tx and create_tx["input"] == "0x" + creation.hex(),
            "deployment transaction is not the exact CREATE artifact")
    expected_create = {
        "balance": "0x0", "nonce": "0x01", "code": "0x" + runtime.hex(),
        "storage": {q(CHI_SLOT): q(SCALE), q(RHO_SLOT): q(START)},
    }

    def create_prefix_checker(_block, index, before, after, result):
        require(index == 0, "deployment must contain exactly one CREATE transaction")
        require(target_at(before, create_target) is None, "CREATE target was preallocated")
        created = target_at(after, create_target)
        require(created is not None, "CREATE did not install an account")
        check_target(created, expected_create)
        require(result["receipts"][-1].get("status") == "0x1", "CREATE receipt failed")
        sender_prefix_check(before, after, {
            "caller": ALICE, "callerTransferDelta": 0,
            "transaction": create_tx,
        }, result["receipts"][-1])

    linked = execute_linked_blocks(initial, [{"timestamp": START, "transaction": create_tx}],
                                   run_transition=transition,
                                   prefix_checker=create_prefix_checker)
    name = "deployment-genesis"
    files[f"{name}.json"] = json.dumps(render_fixture(name, initial, linked, profile), indent=2) + "\n"
    manifest.append({"name": name, "obligation": name, "steps": 1,
                     "executionEvidence": True, "fixture": f"{name}.json",
                     "target": create_target, "creationCodeSha256": hashlib.sha256(creation).hexdigest()})

    # Observer twins exercise the real target CALL boundary.  The ordinary
    # twin covers zero-value CALLs; one reentry settles nested units, another
    # records a calibrated nested overdraw, and the rejecting twin performs a
    # successful nested settlement before it writes/emits and reverts.
    observer_address = "0x000000000000000000000000000000000000d220"
    observer_cases = (
        ("exit-zero-unit-call-observer", "ordinary", 0, 0, 0),
        ("exit-successful-reentry-observer", "reenter", 3, 2, 1),
        ("exit-nested-overdraw-observer", "reenter", 3, 2, nested_overdraw(3, 2)),
        ("exit-rejecting-recipient-rollback-observer", "reject-after-reentry", 3, 2,
         1),
    )
    for name, mode, original_units, outer_units, nested_units in observer_cases:
        observer = observer_code(create_target, mode, nested_units=max(1, nested_units))
        initial = system_alloc()
        initial[create_target] = account(
            original_units, "0x" + runtime.hex(), {
                CHI_SLOT: SCALE, RHO_SLOT: START, PIE_SLOT: original_units,
                int(observer_address, 16): original_units,
            }, nonce=1)
        initial_target = initial[create_target]
        initial[observer_address] = account(0, observer)
        initial[ALICE] = account(FUNDS)
        outer_data = abi("exit", outer_units)
        transaction = {
            "type": "0x0", "chainId": "0x1", "nonce": "0x00",
            "gasPrice": q(GAS_PRICE), "gas": q(GAS), "to": observer_address,
            "value": "0x0", "input": outer_data,
            "secretKey": "0x" + f"{KEYS[ALICE]:064x}",
        }
        observer_int = int(observer_address, 16)
        model = Drip(START)
        model.chi, model.rho, model.Pie = SCALE, START, original_units
        model.rows[observer_int] = original_units
        model.balance = original_units
        pre_snapshot = model.snapshot()
        outer_payout = model.exit(observer_int, outer_units, START)
        nested_succeeds = False
        nested_payout = 0
        try:
            if mode == "reenter":
                nested_payout = model.exit(observer_int, nested_units, START)
                nested_succeeds = True
        except Revert:
            nested_succeeds = False
        if mode == "reject-after-reentry":
            model.exit(observer_int, nested_units, START)
            expected_snapshot = pre_snapshot
            outer_payout = nested_payout = 0
        else:
            expected_snapshot = model.snapshot()
        inner_status = 1 if mode != "reject-after-reentry" else 0
        expected_observer_balance = outer_payout + nested_payout

        def observer_prefix_checker(_block, index, before, after, result,
                                    *, name=name, mode=mode,
                                    expected_snapshot=expected_snapshot,
                                    observer=observer, initial_target=initial_target):
            require(index == 0, f"{name}: observer transaction count drift")
            receipt = result["receipts"][-1]
            require(int(receipt["status"], 16) == 1, f"{name}: outer receipt must succeed")
            check_target(target_at(before, create_target), initial_target)
            target = target_at(after, create_target)
            require(target is not None, f"{name}: target disappeared")
            target_expected = {
                "balance": q(expected_snapshot["balance"]), "nonce": "0x01",
                "code": "0x" + runtime.hex(),
                "storage": {q(CHI_SLOT): q(expected_snapshot["chi"]),
                             q(RHO_SLOT): q(expected_snapshot["rho"]),
                             q(PIE_SLOT): q(expected_snapshot["Pie"]),
                             **{q(int(address, 16)): q(value)
                                for address, value in expected_snapshot["rows"].items()}},
            }
            check_target(target, target_expected)
            observer_state = account_from_alloc(after, observer_address)
            slots = normalized_storage(observer_state.get("storage", {}))
            require(slots.get(0, 0) == inner_status,
                    f"{name}: inner DRIP status differs")
            result_size = 32 if inner_status else 0
            result_word = outer_units if inner_status else 0
            expected_slots = {0: inner_status, 1: result_size, 2: result_word}
            if mode != "reject-after-reentry":
                expected_slots.update({3: 1 + int(nested_succeeds),
                    4: nested_units if nested_succeeds else outer_units,
                    5: 0, 6: int(create_target, 16)})
                expected_slots.update({7: 1 if nested_succeeds else 0,
                                       8: 32 if nested_succeeds else 0,
                                       9: nested_units if nested_succeeds else 0})
            expected_observer = {
                "balance": q(expected_observer_balance), "nonce": "0x0",
                "code": observer,
                "storage": {q(key): q(value) for key, value in expected_slots.items() if value},
            }
            check_target(observer_state, expected_observer)
            label = ("ordinary" if mode == "ordinary" else
                     "reject-after-reentry" if mode == "reject-after-reentry" else
                     "reenter-success" if nested_succeeds else "reenter-overdraw")
            expected_words = {
                "ordinary": [[1, 0, 0, int(create_target, 16)], [1, 32, 0]],
                "reenter-success": [[1, outer_units, 0, int(create_target, 16)],
                                     [2, nested_units, 0, int(create_target, 16)],
                                     [1, 32, nested_units], [1, 32, outer_units]],
                "reenter-overdraw": [[1, outer_units, 0, int(create_target, 16)],
                                      [0, 0, 0], [1, 32, outer_units]],
                "reject-after-reentry": [[0, 0, 0]],
            }[label]
            logs = result["receipts"][-1].get("logs", [])
            expected_topics = {
                "ordinary": [0xD21901, 0xD21902],
                "reenter-success": [0xD21901, 0xD21901, 0xD21903, 0xD21902],
                "reenter-overdraw": [0xD21901, 0xD21903, 0xD21902],
                "reject-after-reentry": [0xD21902],
            }[label]
            expected_logs = [log_entry(observer_address, topic, words)
                             for topic, words in zip(expected_topics, expected_words)]
            require(logs == expected_logs, f"{name}: exact nested log chronology/data differs")
            sender_prefix_check(before, after, {
                "caller": ALICE, "callerTransferDelta": 0,
                "transaction": transaction,
            }, receipt)

        linked = execute_linked_blocks(initial, [{"timestamp": START,
                                                   "transaction": transaction}],
                                       run_transition=transition,
                                       prefix_checker=observer_prefix_checker)
        files[f"{name}.json"] = json.dumps(render_fixture(name, initial, linked, profile), indent=2) + "\n"
        obligation = name.removesuffix("-observer")
        if obligation == "exit-nested-overdraw":
            obligation = "exit-successful-reentry"
        manifest.append({"name": name, "obligation": obligation, "steps": 1,
                         "executionEvidence": True,
                         "fixture": f"{name}.json",
                         "observer": observer_expectations(create_target, mode,
                                                            nested_units=max(1, nested_units),
                                                            callback_value=outer_units)})
    return files, manifest


def model_balance(account):
    return int(account["balance"], 16)


def normalized_storage(raw):
    require(isinstance(raw, dict), "storage is not an object")
    normalized = {}
    for key, value in raw.items():
        slot, word = int(key, 16), int(value, 16)
        require(0 <= slot < 2**256 and 0 <= word < 2**256, "storage is not word-shaped")
        require(slot not in normalized, "duplicate normalized storage slot")
        normalized[slot] = word
    return {key: value for key, value in normalized.items() if value}


def check_target(actual, expected):
    """Strict entire-account semantic projection; extra nonzero slots fail."""
    require(set(actual) == {"balance", "nonce", "code", "storage"}, "target account keys differ")
    for key in ("balance", "nonce"):
        require(int(actual[key], 16) == int(expected[key], 16), f"target {key} differs")
    require(actual["code"] == expected["code"], "target runtime bytes differ")
    require(normalized_storage(actual["storage"]) == normalized_storage(expected["storage"]), "complete target storage differs")


def check_receipt_accounting(before, after, operation, receipt, actual_target):
    """Validate a future replay result without confusing value transfers/fees.

    This helper is currently tested with synthetic inputs only. It must not be
    recorded as executed assertion coverage until an actual t8n consumer calls it.
    Returndata and nested log chronology require the pending observer route.
    """
    require(int(receipt["status"], 16) == operation["expectedOutcome"]["status"], "receipt status differs")
    used = int(receipt["gasUsed"], 16)
    require(0 < used < int(operation["transaction"]["gas"], 16), "gas exhausted or malformed")
    require(receipt["logs"] == [], "unexpected direct-call log")
    require(int(after["balance"], 16) == int(before["balance"], 16) + operation["callerTransferDelta"] - used * GAS_PRICE, "sender transfer/fee balance differs")
    require(int(after["nonce"], 16) == int(before["nonce"], 16) + 1, "sender nonce differs")
    require(after["code"] == before["code"] and normalized_storage(after["storage"]) == normalized_storage(before["storage"]), "sender frame differs")
    check_target(actual_target, operation["expectedTarget"])


def plan():
    runtime, creation = artifacts()
    population = cases(runtime)
    require(len({case["name"] for case in population}) == len(population), "duplicate case name")
    require({case["obligation"] for case in population} <= set(OBLIGATIONS), "unowned scenario")
    rows = []
    for name in OBLIGATIONS:
        owned = [case["name"] for case in population if case["obligation"] == name]
        require(owned or name in PENDING, f"missing obligation disposition: {name}")
        rows.append({"name": name, "inputCases": owned, "executedCases": [],
                     "requiredAssertions": ["complete pre/post target storage/balance/code", "receipt status, finite gas and sender fees", "exact returndata and ordered logs"],
                     "exactExpectationPaths": [f"cases/{case_name}/steps/*/{{preTarget,expectedTarget,expectedOutcome,callerTransferDelta}}" for case_name in owned],
                     "pendingSpecialAssertions": PENDING.get(name, [])})
    return {"schema": 1, "kind": "drip-execution-input-preparation", "executionEvidence": False,
            "runtimeSha256": hashlib.sha256(runtime).hexdigest(), "creationSha256": hashlib.sha256(creation).hexdigest(),
            "target": TARGET, "obligations": rows, "cases": population,
            "pendingIntegration": ["independent key/address derivation", "shared-current-mainnet identity and execution boundary",
                "canonical BPO2 system preallocation and linked blocks", "per-transaction prefix replay for intermediate state assertions",
                "returndata and child CALL observer bytecode", "actual creation transaction", "Jaune blockchain fixture serialization",
                "generated-owner registration, discovery/staleness controls and full replay"]}


def self_test(document):
    require(len(document["obligations"]) == 38, "SF obligation count drift")
    canonical = json.dumps(document, sort_keys=True)
    require(canonical == json.dumps(plan(), sort_keys=True), "plan is nondeterministic")
    by_name = {case["name"]: case for case in document["cases"]}
    for name in ("view-units-fresh-consistency", "view-assets-fresh-consistency"):
        first, second = by_name[name]["steps"]
        require(first["expectedOutcome"]["returndata"] == second["expectedOutcome"]["returndata"], "fresh view/mutation mismatch")
        require(first["preTarget"] == first["expectedTarget"], "view changes target")
    one = by_name["segmentation-one"]["steps"][-1]["expectedTarget"]
    split = by_name["segmentation-split"]["steps"][-1]["expectedTarget"]
    require(int(one["storage"][q(CHI_SLOT)], 16) - int(split["storage"][q(CHI_SLOT)], 16) == 1, "segmentation witness lost")
    for case in document["cases"]:
        for operation in case["steps"]:
            check_target(operation["expectedTarget"], operation["expectedTarget"])
            if operation["expectedOutcome"]["status"] == 0:
                require(operation["preTarget"] == operation["expectedTarget"], "rollback state differs")
                require(operation["callerTransferDelta"] == 0, "failed call retained entry value")
    operation = by_name["join-genesis-first"]["steps"][0]
    before = {"balance": q(FUNDS), "nonce": "0x00", "code": "0x", "storage": {}}
    used = 50_000
    after = {**before, "balance": q(FUNDS + operation["callerTransferDelta"] - used*GAS_PRICE), "nonce": "0x01"}
    receipt = {"status": "0x01", "gasUsed": q(used), "logs": []}
    expected = operation["expectedTarget"]
    check_receipt_accounting(before, after, operation, receipt, expected)
    controls = []
    for label in ("balance", "nonce", "code", "extra-storage", "missing-storage"):
        mutant = copy.deepcopy(expected)
        if label in ("balance", "nonce"): mutant[label] = q(int(mutant[label], 16)+1)
        elif label == "code": mutant["code"] += "00"
        elif label == "extra-storage": mutant["storage"]["0x1234"] = "0x01"
        else: del mutant["storage"][q(CHI_SLOT)]
        controls.append((label, lambda mutant=mutant: check_target(mutant, expected)))
    controls.append(("fee-not-charged", lambda: check_receipt_accounting(before, {**after, "balance": q(FUNDS + operation['callerTransferDelta'])}, operation, receipt, expected)))
    controls.append(("wrong-receipt-status", lambda: check_receipt_accounting(before, after, operation, {**receipt, "status": "0x00"}, expected)))
    controls.append(("unexpected-log", lambda: check_receipt_accounting(before, after, operation, {**receipt, "logs": [{}]}, expected)))
    for name, action in controls:
        try: action()
        except AssertionError: pass
        else: raise AssertionError(f"projection control did not bite: {name}")
    check_receipt_accounting(before, after, operation, receipt, expected)
    print(f"OK — DRIP input preparation: {len(document['cases'])} cases, {sum(len(c['steps']) for c in document['cases'])} model steps, 38 obligations explicitly dispositioned; {len(controls)} pure projection controls; EVM executions=0")


def write_or_compare(files, *, write):
    output = ROOT / "scripts" / "fixtures" / "drip"
    expected_names = set(files)
    actual_names = {path.name for path in output.glob("*.json")} if output.exists() else set()
    missing = sorted(expected_names - actual_names)
    orphaned = sorted(actual_names - expected_names)
    if not write:
        if missing or orphaned:
            raise RuntimeError(f"fixture population differs: missing={missing}, orphaned={orphaned}")
        for name, expected in sorted(files.items()):
            actual = (output / name).read_text(encoding="utf-8")
            if actual != expected:
                raise RuntimeError(f"generated fixture differs: {output / name}; run with --write")
        return
    output.mkdir(parents=True, exist_ok=True)
    for name, content in sorted(files.items()):
        temporary = output / f".{name}.tmp"
        temporary.write_text(content, encoding="utf-8")
        temporary.replace(output / name)
    for stale in output.glob("*.json"):
        if stale.name not in expected_names:
            stale.unlink()


def execute_and_check(root_arg, *, write):
    validate_current_mainnet_boundary()
    profile = load_profile()
    root = resolve_root(profile, root_arg)
    verify_target(root, profile)
    paths = target_paths(root, profile)
    require(Path(sys.executable).resolve() == paths.python.resolve(),
            f"generator must run under isolated target Python {paths.python}")
    runtime, creation = artifacts()
    files, manifest = runtime_transaction_population(root, profile, runtime, creation, paths)
    obligation_map = []
    for obligation in OBLIGATIONS:
        fixtures = [row["fixture"] for row in manifest
                    if row.get("obligation") == obligation]
        if obligation == "receipt-returndata-log-matrix":
            fixtures = [row["fixture"] for row in manifest
                        if row["name"].endswith("-observer")]
        require(fixtures, f"runtime population has no fixture for {obligation}")
        obligation_map.append({"name": obligation, "fixtures": sorted(set(fixtures)),
                               "requiredAssertions": [
                                   "complete target pre/post account and storage",
                                   "receipt status and cumulative-gas differences",
                                   "returndata bytes/size and ordered observer logs",
                               ]})
    files["manifest.json"] = json.dumps({
        "schema": 2, "kind": "drip-bpo2-runtime-fixtures",
        "executionEvidence": True, "runtimeSha256": hashlib.sha256(runtime).hexdigest(),
        "creationSha256": hashlib.sha256(creation).hexdigest(),
        "targetProfile": profile["target"]["checkoutCommit"],
        "obligations": obligation_map, "cases": manifest,
    }, indent=2) + "\n"
    write_or_compare(files, write=write)
    verb = "wrote" if write else "checked"
    print(f"OK — {verb} DRIP BPO2 fixtures: {len(manifest)} scenarios, per-transaction prefixes verified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--plan", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--write", action="store_true",
                      help="execute the pinned BPO2 target and atomically write verified fixtures")
    mode.add_argument("--check-runtime", action="store_true",
                      help="execute the pinned BPO2 target and compare existing fixtures")
    parser.add_argument("--root", help="explicit current-mainnet target root (required for runtime modes)")
    args = parser.parse_args()
    if args.write or args.check_runtime:
        if not args.root:
            parser.error("--root is required for runtime modes")
        execute_and_check(args.root, write=args.write)
        return
    document = plan()
    if args.self_test: self_test(document)
    else: print(json.dumps(document, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
