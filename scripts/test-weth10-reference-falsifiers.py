#!/usr/bin/env python3
"""Deletion/mutation falsifiers for every required WETH10 lock family."""
from __future__ import annotations

import copy
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from weth10_reference_schema import SchemaError, keccak256, validate_lock_schema


ROOT = Path(__file__).resolve().parents[1]
LOCK = ROOT / "scripts" / "weth10-reference.json"
GENERATOR = ROOT / "scripts" / "weth10-reference.py"
REFERENCE = ROOT / "scripts" / "reference" / "weth10"


def load_generator_module() -> Any:
    spec = importlib.util.spec_from_file_location("weth10_reference_generator", GENERATOR)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load WETH10 reference generator for derivation falsifiers")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def parent_at(value: Any, path: tuple[Any, ...]) -> tuple[Any, Any]:
    current = value
    for component in path[:-1]:
        current = current[component]
    return current, path[-1]


def delete_at(value: Any, path: tuple[Any, ...]) -> None:
    parent, key = parent_at(value, path)
    del parent[key]


def set_at(value: Any, path: tuple[Any, ...], replacement: Any) -> None:
    parent, key = parent_at(value, path)
    parent[key] = replacement


def flip_hex(value: str) -> str:
    replacement = "1" if value[-1] != "1" else "2"
    return value[:-1] + replacement


def mutate_guard(value: Any) -> None:
    row = next(item for item in value["sourceBehavior"]["guardOrder"] if len(item["guardOrder"]) >= 2)
    row["guardOrder"][0]["sourceLength"] = 0


def mutate_source_digest(value: Any) -> None:
    row = next(item for item in value["provenance"]["sourceDigests"]
               if item["path"] == "contracts/WETH10.sol")
    row["sha256"] = flip_hex(row["sha256"])


def mutate_storage(value: Any) -> None:
    value["sourceBehavior"]["storageLayout"]["types"]["t_address"]["encoding"] = "unknown"


@dataclass(frozen=True)
class Case:
    family: str
    deletion: tuple[Any, ...]
    mutation: Callable[[Any], None]


def scalar_mutation(path: tuple[Any, ...], replacement: Any) -> Callable[[Any], None]:
    return lambda value: set_at(value, path, replacement)


CASES = [
    Case("generated-marker-json-shape", ("_comment",),
         lambda value: value.__setitem__("unexpected", True)),
    Case("schema-generator", ("generator", "version"),
         scalar_mutation(("generator", "regenerationCommand"), "python3 scripts/weth10-reference.py refresh")),
    Case("target-identity", ("target", "address"),
         scalar_mutation(("target", "address"), "0x0000000000000000000000000000000000000000")),
    Case("deployment-record", ("target", "deploymentTransaction"),
         scalar_mutation(("target", "deploymentBlock"), 11954958)),
    Case("repository-provenance", ("provenance", "deploymentCommit"),
         scalar_mutation(("provenance", "deploymentCommit"), "0" * 40)),
    Case("standard-input-provenance", ("provenance", "solcInputHash"),
         scalar_mutation(("provenance", "solcInputHash"), "0" * 32)),
    Case("source-provenance", ("provenance", "sourceDigests"), mutate_source_digest),
    Case("compiler-identity-settings", ("compiler", "metadataSettings"),
         scalar_mutation(("compiler", "metadataSettings", "evmVersion"), "berlin")),
    Case("compiler-release-entry", ("compiler", "releaseManifestEntry"),
         scalar_mutation(("compiler", "releaseManifestEntry", "version"), "0.7.5")),
    Case("abi-functions", ("abi", "functions", 0, "entry", "outputs"),
         scalar_mutation(("abi", "functions", 0, "selector"), "0x00000000")),
    Case("abi-events", ("abi", "events", 0, "entry", "inputs"),
         scalar_mutation(("abi", "events", 0, "topic0"), "0x" + "00" * 32)),
    Case("abi-receive", ("abi", "receive"),
         scalar_mutation(("abi", "receive", "payable"), False)),
    Case("installed-runtime", ("runtime", "installedHex"),
         lambda value: set_at(value, ("runtime", "installedHex"), flip_hex(value["runtime"]["installedHex"]))),
    Case("runtime-observation", ("observation", "captures", 0, "envelopeSha256"),
         lambda value: set_at(value, ("observation", "captures", 0, "envelopeSha256"),
                              flip_hex(value["observation"]["captures"][0]["envelopeSha256"]))),
    Case("template-relation", ("runtime", "templateInstalledAgreeOutsideImmutableReferences"),
         lambda value: set_at(value, ("runtime", "templateSha256"),
                              flip_hex(value["runtime"]["templateSha256"]))),
    Case("immutable-references", ("runtime", "immutableReferences", "44"),
         lambda value: set_at(value, ("runtime", "immutableReferences", "44", 0, "start"), 5474)),
    Case("immutable-values-constants", ("runtime", "constants", "CALLBACK_SUCCESS", "preimage"),
         scalar_mutation(("runtime", "constants", "CALLBACK_SUCCESS", "preimage"),
                         "ERC3156FlashBorrower.onFlashLoan!")),
    Case("deployment-boundary", ("deployment", "constructor", "arguments"),
         scalar_mutation(("deployment", "constructor", "payable"), True)),
    Case("source-reasons", ("sourceBehavior", "reasonStrings"),
         lambda value: set_at(value, ("sourceBehavior", "reasonStrings", 0), "WETH: changed")),
    Case("source-guard-order", ("sourceBehavior", "guardOrder", 0, "signature"), mutate_guard),
    Case("source-callbacks", ("sourceBehavior", "callbacks", 0, "selector"),
         scalar_mutation(("sourceBehavior", "callbacks", 0, "selector"), "0x00000000")),
    Case("source-events", ("sourceBehavior", "events", 0, "inputs"),
         scalar_mutation(("sourceBehavior", "events", 0, "topic0"), "0x" + "00" * 32)),
    Case("storage-layout", ("sourceBehavior", "storageLayout", "storage"), mutate_storage),
]


def schema_must_reject(value: Any, label: str) -> None:
    try:
        validate_lock_schema(value, label)
    except SchemaError:
        return
    raise RuntimeError(f"independent schema accepted falsifier {label}")


def checker_must_reject(value: Any, label: str, directory: Path) -> None:
    lock = directory / (label.replace("/", "-") + ".json")
    lock.write_bytes(canonical(value))
    env = dict(os.environ, WETH10_REFERENCE_LOCK=str(lock), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode == 0:
        raise RuntimeError(f"ordinary checker accepted falsifier {label}: {result.stdout.strip()}")


def checker_bytes_must_reject(data: bytes, label: str, directory: Path) -> None:
    lock = directory / f"raw-{label}.json"
    lock.write_bytes(data)
    env = dict(os.environ, WETH10_REFERENCE_LOCK=str(lock), PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode == 0:
        raise RuntimeError(f"ordinary checker accepted raw JSON falsifier {label}: {result.stdout.strip()}")


def run_lock_falsifiers(reference: Any, directory: Path) -> int:
    count = 0
    for case in CASES:
        deleted = copy.deepcopy(reference)
        delete_at(deleted, case.deletion)
        schema_must_reject(deleted, f"{case.family}/deletion")
        checker_must_reject(deleted, f"{case.family}-deletion", directory)
        count += 1

        mutated = copy.deepcopy(reference)
        case.mutation(mutated)
        schema_must_reject(mutated, f"{case.family}/mutation")
        checker_must_reject(mutated, f"{case.family}-mutation", directory)
        count += 1
    return count


def run_raw_json_falsifiers(reference: Any, directory: Path) -> int:
    baseline = canonical(reference)
    duplicate = baseline.replace(b"{\n", b'{\n  "_comment": "duplicate",\n', 1)
    non_finite = baseline.replace(b'"version": 2', b'"version": NaN', 1)
    noncanonical = json.dumps(reference, separators=(",", ":")).encode()
    for name, data in (("duplicate-key", duplicate), ("non-finite", non_finite),
                       ("noncanonical", noncanonical)):
        checker_bytes_must_reject(data, name, directory)
    return 3


def run_wrong_type_falsifiers(reference: Any, directory: Path) -> int:
    cases = [
        ("source-trailing-lf-bool", ("provenance", "sourceTrailingLfBytes"), True),
        ("input-optimizer-enabled-int", ("compiler", "settings", "optimizer", "enabled"), 1),
        ("input-literal-content-int", ("compiler", "settings", "metadata", "useLiteralContent"), 1),
        ("effective-optimizer-enabled-int",
         ("compiler", "metadataSettings", "optimizer", "enabled"), 1),
        ("effective-literal-content-int",
         ("compiler", "metadataSettings", "metadata", "useLiteralContent"), 1),
        ("constructor-payable-int", ("deployment", "constructor", "payable"), 0),
        ("constructor-rejects-endowment-int",
         ("deployment", "constructor", "rejectsNonzeroEndowment"), 1),
        ("publicnode-request-id-bool", ("observation", "captures", 0, "request", "id"), True),
        ("drpc-request-id-bool", ("observation", "captures", 1, "request", "id"), True),
        ("receive-count-bool", ("abi", "receiveCount"), True),
    ]
    for name, path, replacement in cases:
        value = copy.deepcopy(reference)
        set_at(value, path, replacement)
        schema_must_reject(value, f"wrong-type/{name}")
        checker_must_reject(value, f"wrong-type-{name}", directory)
    return len(cases)


def run_deployment_derivation_falsifiers(reference: Any) -> int:
    generator = load_generator_module()
    baseline_output = json.loads((REFERENCE / "inputs" / "solc-output.json").read_bytes())
    abi = {"constructor": reference["deployment"]["constructor"]["entry"]}
    artifact = {"args": []}
    constants = reference["runtime"]["constants"]

    def contract(output: Any) -> Any:
        return next(node for node in output["sources"]["contracts/WETH10.sol"]["ast"]["nodes"]
                    if node.get("nodeType") == "ContractDefinition" and node.get("name") == "WETH10")

    initialized = copy.deepcopy(baseline_output)
    declaration = next(node for node in contract(initialized)["nodes"]
                       if node.get("nodeType") == "VariableDeclaration" and node.get("name") == "balanceOf")
    declaration["value"] = {"nodeType": "Literal", "value": "0"}

    indexed_write = copy.deepcopy(baseline_output)
    indexed_contract = contract(indexed_write)
    balance_id = next(node["id"] for node in indexed_contract["nodes"]
                      if node.get("nodeType") == "VariableDeclaration" and node.get("name") == "balanceOf")
    constructor = next(node for node in indexed_contract["nodes"]
                       if node.get("nodeType") == "FunctionDefinition" and node.get("kind") == "constructor")
    constructor["body"]["statements"].append({
        "nodeType": "Assignment",
        "leftHandSide": {
            "nodeType": "IndexAccess",
            "baseExpression": {"nodeType": "Identifier", "referencedDeclaration": balance_id},
            "indexExpression": {"nodeType": "Literal", "value": "0"},
        },
        "rightHandSide": {"nodeType": "Literal", "value": "1"},
    })

    for name, output in (("logical-declaration-initializer", initialized),
                         ("constructor-indexed-logical-write", indexed_write)):
        try:
            generator.deployment_inventory(output, abi, artifact, constants)
        except generator.ReferenceError:
            continue
        raise RuntimeError(f"deployment derivation accepted falsifier {name}")
    return 2


def run_coherent_schema_falsifiers(reference: Any, directory: Path) -> int:
    def function_output(value: Any) -> None:
        row = value["abi"]["functions"][0]
        row["entry"]["outputs"][0]["type"] = "uint256"
        row["entry"]["outputs"][0]["internalType"] = "uint256"
        row["returnTypes"][0] = "uint256"

    def function_mutability(value: Any) -> None:
        row = next(item for item in value["abi"]["functions"]
                   if item["entry"]["stateMutability"] == "view")
        row["entry"]["stateMutability"] = "pure"

    def event_indexing(value: Any) -> None:
        abi_event = value["abi"]["events"][0]
        abi_event["entry"]["inputs"][0]["indexed"] = False
        source_event = next(item for item in value["sourceBehavior"]["events"]
                            if item["signature"] == abi_event["signature"])
        source_event["inputs"][0]["indexed"] = False

    def coherent_constant(value: Any) -> None:
        preimage = "ERC3156FlashBorrower.onFlashLoan!"
        derived = "0x" + keccak256(preimage.encode())
        value["runtime"]["constants"]["CALLBACK_SUCCESS"]["preimage"] = preimage
        value["runtime"]["constants"]["CALLBACK_SUCCESS"]["value"] = derived
        value["runtime"]["immutableValues"]["CALLBACK_SUCCESS"] = derived

    def callback_output(value: Any) -> None:
        value["sourceBehavior"]["callbacks"][0]["outputs"][0]["type"] = "uint256"

    def guard_condition(value: Any) -> None:
        row = next(item for item in value["sourceBehavior"]["guardOrder"] if item["guardOrder"])
        row["guardOrder"][0]["condition"] = "true"

    def storage_slot(value: Any) -> None:
        value["sourceBehavior"]["storageLayout"]["storage"][0]["slot"] = "9"

    def secondary_source_digest(value: Any) -> None:
        row = next(item for item in value["provenance"]["sourceDigests"]
                   if item["path"] != "contracts/WETH10.sol")
        row["sha256"] = flip_hex(row["sha256"])

    cases = [
        ("coherent-abi-output", function_output),
        ("coherent-abi-mutability", function_mutability),
        ("coherent-event-indexing", event_indexing),
        ("coherent-immutable-value", coherent_constant),
        ("coherent-callback-output", callback_output),
        ("coherent-guard-condition", guard_condition),
        ("coherent-storage-slot", storage_slot),
        ("coherent-secondary-source-digest", secondary_source_digest),
    ]
    for name, change in cases:
        value = copy.deepcopy(reference)
        change(value)
        schema_must_reject(value, name)
        checker_must_reject(value, name, directory)
    return len(cases)


def mutate_json(path: Path, change: Callable[[Any], None]) -> None:
    value = json.loads(path.read_bytes())
    change(value)
    path.write_bytes(canonical(value))


def coordinated_cases() -> list[tuple[str, str, Callable[[Path], None]]]:
    def standard_settings(ref: Path) -> None:
        mutate_json(ref / "inputs" / "solc-input.json",
                    lambda value: value["settings"]["optimizer"].__setitem__("runs", 19999))

    def compiler_output(ref: Path) -> None:
        mutate_json(ref / "inputs" / "solc-output.json", lambda value: value.__setitem__("falsifier", True))

    def manifest_digest(ref: Path) -> None:
        path = ref / "inputs" / "solc-emscripten-wasm32-list.json"
        def change(value: Any) -> None:
            row = next(item for item in value["builds"]
                       if item.get("path") == "solc-emscripten-wasm32-v0.7.6+commit.7338295f.js")
            row["sha256"] = "0x" + "00" * 32
        mutate_json(path, change)

    def artifact_abi(ref: Path) -> None:
        path = ref / "inputs" / "deployment-artifact.json"
        def change(value: Any) -> None:
            function = next(item for item in value["abi"] if item.get("type") == "function")
            function["stateMutability"] = "payable"
        mutate_json(path, change)

    def both_runtimes(ref: Path) -> None:
        for name in ("rpc-publicnode.json", "rpc-drpc.json"):
            path = ref / "inputs" / name
            envelope = json.loads(path.read_bytes())
            response = json.loads(envelope["responseRaw"])
            body = response["result"][2:]
            for start in (4237, 8473, 8823):
                body = body[:2 * start] + (2).to_bytes(32, "big").hex() + body[2 * (start + 32):]
            response["result"] = "0x" + body
            envelope["responseRaw"] = json.dumps(response, separators=(",", ":"))
            path.write_bytes(canonical(envelope))

    def acquisition_identity(ref: Path) -> None:
        path = ref / "inputs" / "rpc-publicnode.json"
        mutate_json(path, lambda value: value.__setitem__("operator", "https://example.invalid"))

    def immutable_inventory(ref: Path) -> None:
        path = ref / "inputs" / "solc-output.json"
        def change(value: Any) -> None:
            refs = value["contracts"]["contracts/WETH10.sol"]["WETH10"]["evm"]["deployedBytecode"]["immutableReferences"]
            refs["44"][0]["start"] += 1
        mutate_json(path, change)

    def source_preimage(ref: Path) -> None:
        old, new = "ERC3156FlashBorrower.onFlashLoan", "ERC3156FlashBorrower.onFlashLoan!"
        input_path = ref / "inputs" / "solc-input.json"
        standard = json.loads(input_path.read_bytes())
        standard["sources"]["contracts/WETH10.sol"]["content"] = \
            standard["sources"]["contracts/WETH10.sol"]["content"].replace(old, new, 1)
        input_path.write_bytes(canonical(standard))
        source_path = ref / "inputs" / "source" / "deployed-WETH10.sol"
        source_path.write_text(source_path.read_text().replace(old, new, 1))

    return [
        ("standard-input-outer-git-blob-pin", "standard-input Git blob identity differs", standard_settings),
        ("compiler-output-outer-sha-pin", "compiler-output digest differs", compiler_output),
        ("compiler-binary-release-entry-pin",
         "solc release entry differs from independently pinned compiler binary digests", manifest_digest),
        ("deployment-artifact-outer-git-blob-pin", "deployment artifact Git blob identity differs", artifact_abi),
        ("rpc-envelope-outer-sha-pin", "RPC envelope publicnode digest differs", both_runtimes),
        ("rpc-operator-pin", "RPC envelope publicnode operator differs", acquisition_identity),
        ("immutable-inventory-outer-output-pin", "compiler-output digest differs", immutable_inventory),
        ("source-preimage-outer-input-pin", "standard-input Git blob identity differs", source_preimage),
    ]


def run_coordinated_falsifiers(directory: Path) -> int:
    count = 0
    for name, expected_diagnostic, change in coordinated_cases():
        ref = directory / name
        shutil.copytree(REFERENCE, ref)
        change(ref)
        output = directory / f"{name}-lock.json"
        env = dict(os.environ, WETH10_REFERENCE_DIR=str(ref), WETH10_REFERENCE_LOCK=str(output),
                   PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run([sys.executable, str(GENERATOR), "generate"], cwd=ROOT, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if result.returncode == 0:
            raise RuntimeError(f"generator accepted coordinated input falsifier {name}: {result.stdout.strip()}")
        if expected_diagnostic not in result.stdout:
            raise RuntimeError(f"coordinated input falsifier {name} hit an unexpected check: {result.stdout.strip()}")
        count += 1
    return count


def main() -> None:
    try:
        reference = json.loads(LOCK.read_bytes())
        validate_lock_schema(reference, "baseline generated lock")
        with tempfile.TemporaryDirectory(prefix="weth10-reference-falsifiers-") as temp:
            directory = Path(temp)
            lock_cases = run_lock_falsifiers(reference, directory)
            raw_cases = run_raw_json_falsifiers(reference, directory)
            wrong_type_cases = run_wrong_type_falsifiers(reference, directory)
            deployment_derivation_cases = run_deployment_derivation_falsifiers(reference)
            coherent_cases = run_coherent_schema_falsifiers(reference, directory)
            coordinated = run_coordinated_falsifiers(directory)
        print(f"OK — WETH10 reference falsifiers: {len(CASES)} families, "
              f"{lock_cases} deletion/mutation cases, {raw_cases} raw-JSON cases, "
              f"{wrong_type_cases} wrong-type cases, {coherent_cases} coherent-schema cases, "
              f"{deployment_derivation_cases} deployment-derivation cases, "
              f"{coordinated} coordinated-input cases rejected")
    except (OSError, SchemaError, RuntimeError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        raise SystemExit(f"test-weth10-reference-falsifiers.py: {exc}")


if __name__ == "__main__":
    main()
