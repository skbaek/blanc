#!/usr/bin/env python3
"""Pure corruption controls for the DRIP committed-fixture verifier."""
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import tempfile
from pathlib import Path

from drip_fixture_observers import observer_code, observer_expectations

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("drip_fixture_verifier", HERE / "check-drip-fixtures.py")
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC and SPEC.loader
SPEC.loader.exec_module(MODULE)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")

def enc(x):
    if not isinstance(x, list) and len(x) == 1 and x[0] < 0x80: return x
    if isinstance(x, list): payload = b"".join(enc(v) for v in x); base = 0xc0
    else: payload = x; base = 0x80
    if len(payload) < 56: return bytes([base + len(payload)]) + payload
    size = len(payload).to_bytes((len(payload).bit_length()+7)//8, "big")
    return bytes([base + 55 + len(size)]) + size + payload


def block_rlp(destination, calldata):
    return "0x" + enc([[b""] * 11 + [b"\x01"],
                        [[b"", b"\x01", b"\x01", destination, b"", calldata,
                          b"%", b"\x01", b"\x01"]], [], []]).hex()


def population(root):
    for path in root.glob("*.json"):
        path.unlink()
    runtime, creation = MODULE.literals()
    cases = []
    obligations = []
    account = {"nonce": "0x01", "balance": "0x00", "code": "0x" + runtime.hex(), "storage": {}}
    helper = "0x000000000000000000000000000000000000d220"

    def add_case(name, obligation, *, target=MODULE.TARGET, deployment=False,
                 ordinary=False, observer=None):
        mode = observer["mode"] if observer else "ordinary"
        units = observer["nestedUnits"] if observer else 1
        needs_helper = ordinary or observer is not None
        pre = {} if deployment else {target: copy.deepcopy(account)}
        post = {target: copy.deepcopy(account)}
        if needs_helper:
            helper_account = {"nonce": "0x00", "balance": "0x00",
                              "code": observer_code(target, mode, nested_units=units), "storage": {}}
            pre[helper] = copy.deepcopy(helper_account)
            post[helper] = helper_account
        destination = b"" if deployment else bytes.fromhex((helper if needs_helper else target)[2:])
        doc = {f"blanc/drip::{name}[fork_BPO2-blockchain_test]": {
            "network": "BPO2", "genesisBlockHeader": {}, "pre": pre,
            "postState": post, "lastblockhash": "0x" + "11" * 32,
            "config": {"network": "BPO2"}, "genesisRLP": "0x01",
            "blocks": [{"rlp": block_rlp(destination, creation if deployment else b"\x01"), "blocknumber": "1"}], "sealEngine": "NoProof",
        }}
        write(root / (name + ".json"), doc)
        row = {"name": name, "obligation": obligation, "steps": 1, "executionEvidence": True,
               "fixture": name + ".json", "receiptGas": [{"status": "0x01", "cumulativeGasUsed": "0x01", "gasUsed": "0x01", "logs": []}]}
        if deployment:
            row.update({"target": target, "creationCodeSha256": hashlib.sha256(creation).hexdigest()})
        elif target != MODULE.TARGET:
            row["target"] = target
        if ordinary:
            row["observerHelpers"] = [helper]
        if observer is not None:
            row["observer"] = observer
        cases.append(row)

    add_case("deployment-genesis", "deployment-genesis", target=MODULE.CREATE_TARGET, deployment=True)
    for name, obligation in MODULE.PRIMARY_CASES:
        add_case(name, obligation)
        add_case("observer-" + name, obligation, ordinary=True)
    for name, obligation, mode, units, value in MODULE.SPECIAL_OBSERVERS:
        observer = observer_expectations(MODULE.CREATE_TARGET, mode, nested_units=units, callback_value=value)
        add_case(name, obligation, target=MODULE.CREATE_TARGET, observer=observer)
    for obligation in MODULE.OBLIGATIONS:
        fixtures = [row["fixture"] for row in cases if row["obligation"] == obligation]
        if obligation == MODULE.MATRIX_OBLIGATION:
            fixtures = [row["fixture"] for row in cases if row["name"].startswith("observer-")
                        or row["name"].endswith("-observer")]
        obligations.append({"name": obligation, "fixtures": fixtures,
                            "requiredAssertions": ["fixture transaction reference"]})
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
        def wrong_observer_recipe(p):
            path = p / "observer-exit-zero-unit-call.json"; value = json.loads(path.read_text()); case = next(iter(value.values()))
            case["pre"]["0x000000000000000000000000000000000000d220"]["code"] = "0x" + MODULE.TARGET[2:]
            write(path, value)
        population(root); must_reject(root, "observer recipe", "observer code/target binding differs", wrong_observer_recipe)
        def observer_bypass(p):
            path = p / "observer-exit-zero-unit-call.json"; value = json.loads(path.read_text()); case = next(iter(value.values()))
            case["blocks"][0]["rlp"] = block_rlp(bytes.fromhex(MODULE.TARGET[2:]), b"\x01")
            write(path, value)
        population(root); must_reject(root, "observer bypass", "destination differs", observer_bypass)
        def wrong_create_literal(p):
            path = p / "deployment-genesis.json"; value = json.loads(path.read_text()); case = next(iter(value.values()))
            case["blocks"][0]["rlp"] = block_rlp(b"", b"\x02")
            write(path, value)
        population(root); must_reject(root, "CREATE literal", "CREATE transaction binding", wrong_create_literal)
        def omitted_ordinary_twin(p):
            filename = "observer-exit-zero-unit-call.json"
            (p / filename).unlink()
            path = p / "manifest.json"; value = json.loads(path.read_text())
            value["cases"] = [row for row in value["cases"] if row["fixture"] != filename]
            for row in value["obligations"]:
                row["fixtures"] = [item for item in row["fixtures"] if item != filename]
            write(path, value)
        population(root); must_reject(root, "omitted ordinary twin", "frozen case population differs", omitted_ordinary_twin)
        def direct_matrix_substitution(p):
            path = p / "manifest.json"; value = json.loads(path.read_text())
            matrix = next(row for row in value["obligations"] if row["name"] == MODULE.MATRIX_OBLIGATION)
            matrix["fixtures"].remove("observer-exit-zero-unit-call.json")
            matrix["fixtures"].append("exit-zero-unit-call.json")
            write(path, value)
        population(root); must_reject(root, "direct matrix substitution", "observer population differs", direct_matrix_substitution)
        def special_observer_target(p):
            path = p / "manifest.json"; value = json.loads(path.read_text())
            row = next(row for row in value["cases"] if row["name"] == "exit-zero-unit-call-observer")
            row["target"] = MODULE.TARGET
            write(path, value)
        population(root); must_reject(root, "special observer target", "target binding differs", special_observer_target)
        population(root); MODULE.verify(root)
    print("OK — DRIP fixture verifier controls: cross-cut observer matrix and exact transaction/schema corruptions rejected")


if __name__ == "__main__":
    main()
