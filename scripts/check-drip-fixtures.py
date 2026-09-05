#!/usr/bin/env python3
"""Fail-closed static acceptance for committed DRIP BPO2 fixture evidence.

This checker deliberately does not execute an EVM.  It authenticates only
relationships visible in the committed JSON: schema-2 ownership, the frozen
38-obligation map, exact DRIP literals, target placement, case/file inventory,
and nonempty receipt/observer references.  Jaune replay, prefix execution,
returndata, child traces, and the SF arithmetic evaluator remain separate.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = "0x000000000000000000000000000000000000d219"
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
HEX = re.compile(r"^0x(?:[0-9a-fA-F]{2})*$")


class VerificationError(Exception):
    pass


def reject_duplicates(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise VerificationError(f"duplicate JSON key {key!r}")
        value[key] = item
    return value


def read_json(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicates)
    except (OSError, UnicodeError, json.JSONDecodeError, VerificationError) as exc:
        raise VerificationError(f"{path}: invalid JSON: {exc}") from exc


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def quantity(value, label):
    require(isinstance(value, str) and re.fullmatch(r"0x[0-9a-fA-F]+", value), f"{label}: invalid quantity")
    return int(value, 16)


def literals():
    spec = importlib.util.spec_from_file_location("drip_literal_parser", ROOT / "scripts/check-runtime-bytes.py")
    require(spec is not None and spec.loader is not None, "literal parser cannot load")
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    parse_lean_literal = parser.parse_lean_literal
    runtime = parse_lean_literal(ROOT / "Blanc/DripCode.lean", "code")
    creation = parse_lean_literal(ROOT / "Blanc/DripCreationCode.lean", "creationCodeLiteral")
    require(len(creation) > len(runtime) and creation[-len(runtime):] == runtime,
            "creation literal does not suffix-bind runtime")
    return runtime, creation


def account(alloc, address, runtime, label):
    require(isinstance(alloc, dict), f"{label}: allocation is not an object")
    matches = [(key, value) for key, value in alloc.items() if key.lower() == address]
    require(len(matches) == 1 and isinstance(matches[0][1], dict), f"{label}: target account absent or duplicated")
    value = matches[0][1]
    require(set(value) == {"nonce", "balance", "code", "storage"}, f"{label}: target account keys differ")
    require(value["code"] == "0x" + runtime.hex(), f"{label}: target runtime differs")
    require(isinstance(value["storage"], dict), f"{label}: target storage malformed")
    quantity(value["nonce"], label + " nonce"); quantity(value["balance"], label + " balance")
    return value


def fixture_case(path, expected_name, runtime, deployment, target, helpers):
    doc = read_json(path)
    expected_key = f"blanc/drip::{expected_name}[fork_BPO2-blockchain_test]"
    require(set(doc) == {expected_key}, f"{path.name}: exact case key differs")
    case = doc[expected_key]
    required = {"network", "genesisBlockHeader", "pre", "postState", "lastblockhash", "config", "genesisRLP", "blocks", "sealEngine"}
    require(isinstance(case, dict) and set(case) == required, f"{path.name}: unsupported blockchain_test shape")
    require(case["network"] == "BPO2" and case["config"].get("network") == "BPO2", f"{path.name}: non-BPO2 case")
    require(case["sealEngine"] == "NoProof", f"{path.name}: seal engine differs")
    require(HEX.fullmatch(case["genesisRLP"] or "") and case["genesisRLP"] != "0x", f"{path.name}: genesis RLP absent")
    require(HEX.fullmatch(case["lastblockhash"] or "") and len(case["lastblockhash"]) == 66, f"{path.name}: tip hash malformed")
    blocks = case["blocks"]
    require(isinstance(blocks, list) and blocks, f"{path.name}: no checked blocks")
    numbers = []
    for index, block in enumerate(blocks):
        require(isinstance(block, dict) and set(block) == {"rlp", "blocknumber"}, f"{path.name}: block {index} shape differs")
        require(HEX.fullmatch(block["rlp"] or "") and block["rlp"] != "0x", f"{path.name}: block {index} RLP absent")
        require(isinstance(block["blocknumber"], str) and block["blocknumber"].isdigit(), f"{path.name}: block number malformed")
        numbers.append(int(block["blocknumber"]))
    require(numbers == sorted(numbers) and len(numbers) == len(set(numbers)), f"{path.name}: linked block numbers do not strictly increase")
    if deployment:
        require(not any(key.lower() == target for key in case["pre"]), f"{path.name}: CREATE target preallocated")
    else:
        account(case["pre"], target, runtime, f"{path.name} pre")
    account(case["postState"], target, runtime, f"{path.name} post")
    for helper in helpers:
        require(isinstance(helper, str) and re.fullmatch(r"0x[0-9a-f]{40}", helper), f"{path.name}: observer helper malformed")
        before = account(case["pre"], helper, b"\x01", f"{path.name} observer pre")
        after = account(case["postState"], helper, b"\x01", f"{path.name} observer post")
        require(before["code"] == after["code"] and before["code"] != "0x", f"{path.name}: observer code binding differs")


def verify(directory: Path):
    runtime, creation = literals()
    manifest_path = directory / "manifest.json"
    manifest = read_json(manifest_path)
    required = {"schema", "kind", "executionEvidence", "runtimeSha256", "creationSha256", "artifactSizes", "targetProfile", "obligations", "cases"}
    require(isinstance(manifest, dict) and set(manifest) == required, "manifest: unsupported schema-2 shape")
    require(manifest["schema"] == 2 and manifest["kind"] == "drip-bpo2-runtime-fixtures", "manifest: unsupported schema/kind")
    require(manifest["executionEvidence"] is True, "manifest: executionEvidence is not true")
    require(manifest["runtimeSha256"] == hashlib.sha256(runtime).hexdigest(), "manifest: runtime identity differs")
    require(manifest["creationSha256"] == hashlib.sha256(creation).hexdigest(), "manifest: creation identity differs")
    require(manifest["artifactSizes"] == {"runtime": len(runtime), "creation": len(creation)}, "manifest: artifact sizes differ")
    profile = read_json(ROOT / "scripts/current-mainnet-target.json")
    require(manifest["targetProfile"] == profile["target"]["checkoutCommit"], "manifest: target profile pin differs")
    obligations = manifest["obligations"]
    require(isinstance(obligations, list) and len(obligations) == len(OBLIGATIONS), "manifest: obligation count differs")
    by_obligation = {}
    for row in obligations:
        require(isinstance(row, dict) and set(row) == {"name", "fixtures", "requiredAssertions"}, "manifest: obligation row malformed")
        name = row["name"]
        require(isinstance(name, str) and name not in by_obligation, "manifest: duplicate obligation")
        require(isinstance(row["fixtures"], list) and row["fixtures"] and all(isinstance(x, str) and x.endswith(".json") for x in row["fixtures"]), f"manifest: {name} has no fixture references")
        require(isinstance(row["requiredAssertions"], list) and row["requiredAssertions"] and all(isinstance(x, str) and x for x in row["requiredAssertions"]), f"manifest: {name} has no observation channels")
        by_obligation[name] = row
    require(tuple(by_obligation) == OBLIGATIONS, "manifest: frozen obligation names/order differ")
    cases = manifest["cases"]
    require(isinstance(cases, list) and cases, "manifest: empty case map")
    case_by_file = {}
    observer_obligations = set()
    for row in cases:
        require(isinstance(row, dict), "manifest: case row is not object")
        required_case = {"name", "obligation", "steps", "executionEvidence", "fixture", "receiptGas"}
        require(required_case <= set(row) <= required_case | {"target", "creationCodeSha256", "observer", "observerHelpers"}, "manifest: unsupported case fields")
        name, obligation, filename = row["name"], row["obligation"], row["fixture"]
        require(isinstance(name, str) and name and isinstance(filename, str) and filename.endswith(".json"), "manifest: case name/fixture malformed")
        require(obligation in by_obligation and filename not in case_by_file, "manifest: unknown obligation or duplicate fixture")
        require(row["executionEvidence"] is True and isinstance(row["steps"], int) and row["steps"] > 0, f"manifest: {name} has unexecuted/zero steps")
        receipts = row["receiptGas"]
        require(isinstance(receipts, list) and len(receipts) == row["steps"], f"manifest: {name} receipt observations unbound")
        for receipt in receipts:
            require(isinstance(receipt, dict) and set(receipt) == {"status", "cumulativeGasUsed", "gasUsed", "logs"}, f"manifest: {name} receipt shape differs")
            require(quantity(receipt["gasUsed"], name + " gas") > 0 and isinstance(receipt["logs"], list), f"manifest: {name} has zero/malformed receipt observation")
        deployment = obligation == "deployment-genesis"
        if deployment:
            require(row.get("creationCodeSha256") == hashlib.sha256(creation).hexdigest() and isinstance(row.get("target"), str), "manifest: CREATE binding absent")
        else:
            require(row.get("target", TARGET).lower() == TARGET, f"manifest: {name} target binding differs")
        if "observer" in row or "observerHelpers" in row or name.startswith("observer-") or name.endswith("-observer"):
            observer_obligations.add(obligation)
        case_by_file[filename] = (name, deployment, row.get("target", TARGET).lower(), row.get("observerHelpers", []))
    for name, row in by_obligation.items():
        require(set(row["fixtures"]) <= set(case_by_file), f"manifest: {name} references unknown case file")
        require(all(next(case["obligation"] for case in cases if case["fixture"] == item) == name for item in row["fixtures"]), f"manifest: {name} fixture maps another obligation")
    # Returndata/log and exit callback requirements must have concrete observer cases.
    for name in ("receipt-returndata-log-matrix", "exit-zero-unit-call", "exit-successful-reentry", "exit-rejecting-recipient-rollback"):
        require(name in observer_obligations, f"manifest: {name} lacks observer evidence")
    disk = {path.name for path in directory.glob("*.json") if path.name != "manifest.json"}
    require(disk == set(case_by_file), f"fixture population mismatch: missing={sorted(set(case_by_file)-disk)}, orphaned={sorted(disk-set(case_by_file))}")
    for filename, (name, deployment, target, helpers) in case_by_file.items():
        fixture_case(directory / filename, name, runtime, deployment, target, helpers)
    return len(case_by_file), sum(row["steps"] for row in cases)


def main(argv):
    parser = argparse.ArgumentParser()
    parser.add_argument("--fixtures-dir", type=Path, default=ROOT / "scripts/fixtures/drip")
    args = parser.parse_args(argv)
    try:
        files, steps = verify(args.fixtures_dir)
    except VerificationError as exc:
        print(f"REGRESSION — DRIP committed fixtures: {exc}", file=sys.stderr)
        return 1
    print(f"OK — DRIP committed fixtures: {files} files, {steps} declared receipt references (not replay evidence)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
