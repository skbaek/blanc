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


def block_rlp(destination, calldata, count=1, timestamp=1):
    return "0x" + enc([[b""] * 11 + [bytes([timestamp])],
                        [[b"", b"\x01", b"\x64", destination, b"", calldata,
                          b"%", b"\x01", b"\x01"]] * count, [], []]).hex()


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
            for address in (MODULE.HELPERS if ordinary else [helper]):
                pre[address] = copy.deepcopy(helper_account)
                post[address] = copy.deepcopy(helper_account)
        destination = b"" if deployment else bytes.fromhex((helper if needs_helper else target)[2:])
        # Independent fixture shape: these are the actual frozen schedule
        # counts, while headers/signatures/gas remain synthetic test values.
        counts = {
            "view-units-fresh-consistency": [2], "view-assets-fresh-consistency": [2],
            "short-and-trailing-calldata-revert": [13], "value-bearing-nonpayable-revert": [4],
            "multi-participant-conservation": [3, 3], "segmentation-split": [1, 1],
        }.get(name.removeprefix("observer-"), [1])
        doc = {f"blanc/drip::{name}[fork_BPO2-blockchain_test]": {
            "network": "BPO2", "genesisBlockHeader": {}, "pre": pre,
            "postState": post, "lastblockhash": "0x" + "11" * 32,
            "config": {"network": "BPO2"}, "genesisRLP": "0x01",
            "blocks": [{"rlp": block_rlp(destination, creation if deployment else b"\x01", count, i + 1), "blocknumber": str(i + 1)} for i, count in enumerate(counts)], "sealEngine": "NoProof",
        }}
        write(root / (name + ".json"), doc)
        row = {"name": name, "obligation": obligation, "steps": sum(counts), "executionEvidence": True,
               "fixture": name + ".json", "receiptGas": [{"status": "0x01", "cumulativeGasUsed": hex(i + 1), "gasUsed": "0x01", "logs": []} for count in counts for i in range(count)]}
        if deployment:
            row.update({"target": target, "creationCodeSha256": hashlib.sha256(creation).hexdigest()})
        elif target != MODULE.TARGET:
            row["target"] = target
        if ordinary:
            row["observerHelpers"] = MODULE.HELPERS.copy()
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
                            "requiredAssertions": MODULE.ASSERTIONS + (["returndata bytes/size and ordered observer logs"] if obligation == MODULE.MATRIX_OBLIGATION else [])})
    manifest = {"schema": 2, "kind": "drip-bpo2-runtime-fixtures", "executionEvidence": True,
                "runtimeSha256": hashlib.sha256(runtime).hexdigest(), "creationSha256": hashlib.sha256(creation).hexdigest(),
                "artifactSizes": {"runtime": len(runtime), "creation": len(creation)}, "targetProfile": "synthetic",
                "obligations": obligations, "cases": cases}
    manifest["targetProfile"] = json.loads((HERE / "current-mainnet-target.json").read_text())["target"]["checkoutCommit"]
    write(root / "manifest.json", manifest)


def must_reject(root, label, boundary, mutate):
    original = {path.name: path.read_bytes() for path in root.glob("*.json")}
    assert MODULE.verify(root) == (91, 137)
    mutate(root)
    try:
        MODULE.verify(root)
    except MODULE.VerificationError as exc:
        if boundary not in str(exc):
            raise AssertionError(f"{label}: rejected at wrong boundary: {exc}") from exc
        for path in root.glob("*.json"):
            if path.name not in original:
                path.unlink()
        for name, value in original.items():
            (root / name).write_bytes(value)
        assert MODULE.verify(root) == (91, 137)
        print(f"CONTROL OK — {label}: {exc}; restored 91/137")
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
        def manifest_change(action):
            def change(p):
                path = p / "manifest.json"; value = json.loads(path.read_text())
                action(value); write(path, value)
            return change
        def row(value, name="drip-same-timestamp"):
            return next(r for r in value["cases"] if r["name"] == name)
        def coherent_remap(value):
            a, b = row(value), row(value, "join-genesis-first")
            a["obligation"], b["obligation"] = b["obligation"], a["obligation"]
            for obligation in value["obligations"]:
                if obligation["name"] != MODULE.MATRIX_OBLIGATION:
                    obligation["fixtures"] = [r["fixture"] for r in value["cases"]
                                              if r["obligation"] == obligation["name"]]
        must_reject(root, "coherent primary remap", "frozen primary obligation differs", manifest_change(coherent_remap))
        def extra_receipt(value):
            r = row(value); r["steps"] = 2; r["receiptGas"] *= 2
        must_reject(root, "extra declared receipt", "frozen step count differs", manifest_change(extra_receipt))
        def bypass(p):
            manifest_change(lambda m: row(m, "observer-drip-same-timestamp").pop("observerHelpers"))(p)
            path = p / "observer-drip-same-timestamp.json"; value = json.loads(path.read_text())
            next(iter(value.values()))["blocks"][0]["rlp"] = block_rlp(bytes.fromhex(MODULE.TARGET[2:]), b"\x01")
            write(path, value)
        must_reject(root, "observer removal and bypass", "frozen observer helpers differ", bypass)
        for name, _, mode, units, callback in MODULE.SPECIAL_OBSERVERS:
            for field in ("mode", "units", "callback"):
                def changed_special(p, name=name, mode=mode, units=units, callback=callback, field=field):
                    next_mode = ("reenter" if mode == "ordinary" else "ordinary") if field == "mode" else mode
                    next_units = units + 1 if field == "units" else units
                    next_callback = callback + 1 if field == "callback" else callback
                    metadata = observer_expectations(MODULE.CREATE_TARGET, next_mode,
                                                     nested_units=next_units, callback_value=next_callback)
                    manifest_change(lambda m: row(m, name).__setitem__("observer", metadata))(p)
                    path = p / (name + ".json"); value = json.loads(path.read_text()); case = next(iter(value.values()))
                    for stage in ("pre", "postState"):
                        case[stage][MODULE.HELPERS[0]]["code"] = observer_code(MODULE.CREATE_TARGET, next_mode, nested_units=next_units)
                    write(path, value)
                must_reject(root, name + " wrong " + field, "frozen observer metadata differs", changed_special)
        for field, value, boundary in (
            ("status", "nonsense", "status: invalid quantity"),
            ("status", "0x02", "receipt status differs"),
            ("cumulativeGasUsed", "nonsense", "cumulative gas: invalid quantity"),
            ("cumulativeGasUsed", "0x00", "cumulative gas delta differs"),
            ("gasUsed", "0x02", "cumulative gas delta differs"),
            ("logs", [{"fabricated": True}], "log shape differs"),
            ("logs", [{"address": "0x01", "topics": [], "data": "0x"}], "log address differs"),
            ("logs", [{"address": MODULE.TARGET, "topics": ["0x01"], "data": "0x"}], "log topics differ"),
            ("logs", [{"address": MODULE.TARGET, "topics": [], "data": "0x1"}], "log data differs"),
        ):
            must_reject(root, "receipt " + field + " " + boundary, boundary,
                        manifest_change(lambda m, field=field, value=value: row(m)["receiptGas"][0].__setitem__(field, value)))
        def edit_block(name, action):
            def change(p):
                path = p / (name + ".json"); value = json.loads(path.read_text())
                action(next(iter(value.values()))); write(path, value)
            return change
        must_reject(root, "decoded transaction missing", "frozen block transaction/receipt count differs",
                    edit_block("short-and-trailing-calldata-revert", lambda c: c["blocks"][0].__setitem__(
                        "rlp", block_rlp(bytes.fromhex(MODULE.TARGET[2:]), b"\x01", 12))))
        must_reject(root, "decoded transaction extra", "transaction/receipt count differs",
                    edit_block("drip-same-timestamp", lambda c: c["blocks"][0].__setitem__(
                        "rlp", block_rlp(bytes.fromhex(MODULE.TARGET[2:]), b"\x01", 2))))
        def regroup(p):
            edit_block("segmentation-split", lambda c: c.__setitem__("blocks", [{
                "rlp": block_rlp(bytes.fromhex(MODULE.TARGET[2:]), b"\x01", 2), "blocknumber": "1"}]))(p)
            manifest_change(lambda m: row(m, "segmentation-split")["receiptGas"][1].__setitem__("cumulativeGasUsed", "0x02"))(p)
        must_reject(root, "same total wrong block grouping", "frozen block transaction/receipt count differs", regroup)
        def gas_bound(value):
            r = row(value)["receiptGas"][0]; r["gasUsed"] = r["cumulativeGasUsed"] = "0x64"
        must_reject(root, "gas reaches envelope limit", "finite transaction bound", manifest_change(gas_bound))
        must_reject(root, "multi-block gas not reset", "cumulative gas delta differs",
                    manifest_change(lambda m: row(m, "multi-participant-conservation")["receiptGas"][3].__setitem__("cumulativeGasUsed", "0x04")))
        must_reject(root, "multi-step intermediate delta", "cumulative gas delta differs",
                    manifest_change(lambda m: row(m, "short-and-trailing-calldata-revert")["receiptGas"][6].__setitem__("cumulativeGasUsed", "0x08")))
        must_reject(root, "filename alias", "filename differs", manifest_change(lambda m: row(m).__setitem__("fixture", "alias.json")))
        must_reject(root, "assertion substitution", "observation channels differ", manifest_change(lambda m: m["obligations"][0].__setitem__("requiredAssertions", ["claimed"])))
        must_reject(root, "direct observer metadata", "frozen observer metadata differs", manifest_change(lambda m: row(m).__setitem__("observer", observer_expectations(MODULE.TARGET))))
        manifest_change(lambda m: row(m)["receiptGas"][0].__setitem__("logs", [{
            "address": MODULE.TARGET, "topics": ["0x" + "01" * 32], "data": "0x0102"}]))(root)
        assert MODULE.verify(root) == (91, 137)  # Well-shaped logs are not execution authentication.
        population(root)
        assert MODULE.verify(root) == (91, 137)
    print("OK — DRIP fixture verifier controls: frozen 91 cases/137 references, multi-step/multi-block binding and isolated corruptions rejected/restored")


if __name__ == "__main__":
    main()
