#!/usr/bin/env python3
"""Pure corruption controls for the DRIP committed-fixture verifier."""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("drip_fixture_verifier", HERE / "check-drip-fixtures.py")
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC and SPEC.loader
SPEC.loader.exec_module(MODULE)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def population(root):
    for path in root.glob("*.json"):
        path.unlink()
    runtime, creation = MODULE.literals()
    fixture_names = {}
    cases = []
    obligations = []
    account = {"nonce": "0x01", "balance": "0x00", "code": "0x" + runtime.hex(), "storage": {}}
    for obligation in MODULE.OBLIGATIONS:
        name = ("observer-" + obligation if obligation in {
            "receipt-returndata-log-matrix", "exit-zero-unit-call", "exit-successful-reentry", "exit-rejecting-recipient-rollback"
        } else obligation)
        filename = name + ".json"
        fixture_names[obligation] = filename
        deployment = obligation == "deployment-genesis"
        helpers = ["0x000000000000000000000000000000000000d220"] if name.startswith("observer-") else []
        pre = {} if deployment else {MODULE.TARGET: copy.deepcopy(account)}
        for helper in helpers:
            pre[helper] = {"nonce": "0x00", "balance": "0x00", "code": "0x01", "storage": {}}
        post = {MODULE.TARGET: copy.deepcopy(account)}
        for helper in helpers:
            post[helper] = {"nonce": "0x00", "balance": "0x00", "code": "0x01", "storage": {}}
        doc = {f"blanc/drip::{name}[fork_BPO2-blockchain_test]": {
            "network": "BPO2", "genesisBlockHeader": {}, "pre": pre,
            "postState": post, "lastblockhash": "0x" + "11" * 32,
            "config": {"network": "BPO2"}, "genesisRLP": "0x01",
            "blocks": [{"rlp": "0x01", "blocknumber": "1"}], "sealEngine": "NoProof",
        }}
        write(root / filename, doc)
        row = {"name": name, "obligation": obligation, "steps": 1, "executionEvidence": True,
               "fixture": filename, "receiptGas": [{"status": "0x01", "cumulativeGasUsed": "0x01", "gasUsed": "0x01", "logs": []}]}
        if deployment:
            row.update({"target": MODULE.TARGET, "creationCodeSha256": hashlib.sha256(creation).hexdigest()})
        elif name.startswith("observer-"):
            row["observerHelpers"] = ["0x000000000000000000000000000000000000d220"]
        cases.append(row)
        obligations.append({"name": obligation, "fixtures": [filename], "requiredAssertions": ["fixture transaction reference"]})
    manifest = {"schema": 2, "kind": "drip-bpo2-runtime-fixtures", "executionEvidence": True,
                "runtimeSha256": hashlib.sha256(runtime).hexdigest(), "creationSha256": hashlib.sha256(creation).hexdigest(),
                "artifactSizes": {"runtime": len(runtime), "creation": len(creation)}, "targetProfile": "synthetic",
                "obligations": obligations, "cases": cases}
    manifest["targetProfile"] = json.loads((HERE / "current-mainnet-target.json").read_text())["target"]["checkoutCommit"]
    write(root / "manifest.json", manifest)


def must_reject(root, label, boundary, mutate):
    mutate(root)
    try:
        MODULE.verify(root)
    except MODULE.VerificationError as exc:
        if boundary not in str(exc):
            raise AssertionError(f"{label}: rejected at wrong boundary: {exc}") from exc
        return
    raise AssertionError(f"{label}: corruption escaped")


def main():
    with tempfile.TemporaryDirectory(prefix="drip-fixture-verifier-") as raw:
        root = Path(raw)
        population(root); MODULE.verify(root)
        def wrong_runtime(p):
            path = p / "join-zero-value.json"; value = json.loads(path.read_text()); case = next(iter(value.values()))
            case["pre"][MODULE.TARGET]["code"] = "0x00"; write(path, value)
        must_reject(root, "runtime", "target runtime differs", wrong_runtime)
        population(root); must_reject(root, "deleted fixture", "fixture population mismatch", lambda p: (p / "join-zero-value.json").unlink())
        population(root); must_reject(root, "orphan fixture", "fixture population mismatch", lambda p: write(p / "orphan.json", {}))
        def missing_obligation(p):
            path = p / "manifest.json"; value = json.loads(path.read_text()); value["obligations"].pop(); write(path, value)
        population(root); must_reject(root, "missing obligation", "obligation count differs", missing_obligation)
        def wrong_target(p):
            path = p / "manifest.json"; value = json.loads(path.read_text()); value["cases"][1]["target"] = "0x" + "00" * 20; write(path, value)
        population(root); must_reject(root, "wrong target", "target binding differs", wrong_target)
        def corrupt_observation(p):
            path = p / "manifest.json"; value = json.loads(path.read_text()); value["cases"][1]["receiptGas"] = []; write(path, value)
        population(root); must_reject(root, "observation", "receipt observations unbound", corrupt_observation)
        population(root); MODULE.verify(root)
    print("OK — DRIP fixture verifier controls: valid shape plus runtime, missing, orphan, obligation, target, and observation corruptions rejected")


if __name__ == "__main__":
    main()
