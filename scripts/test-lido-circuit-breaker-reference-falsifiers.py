#!/usr/bin/env python3
"""Live AC2 falsifiers for the Lido CircuitBreaker reference lock."""
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

from lido_circuit_breaker_reference_schema import SchemaError, validate_lock_schema

ROOT = Path(__file__).resolve().parents[1]
LOCK = ROOT / "scripts" / "lido-circuit-breaker-reference.json"
GENERATOR = ROOT / "scripts" / "lido-circuit-breaker-reference.py"
REFERENCE = ROOT / "scripts" / "reference" / "lido-circuit-breaker"


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
    return value[:-1] + ("1" if value[-1] != "1" else "2")


def schema_must_reject(value: Any, label: str, diagnostic: str) -> None:
    try:
        validate_lock_schema(value, label)
    except SchemaError as exc:
        if diagnostic not in str(exc):
            raise RuntimeError(f"{label} hit unexpected schema diagnostic: {exc}") from exc
        return
    raise RuntimeError(f"independent schema accepted falsifier {label}")


def checker_must_reject(value: Any, label: str, diagnostic: str, directory: Path) -> None:
    lock = directory / f"{label}.json"
    lock.write_bytes(canonical(value))
    environment = dict(os.environ, LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK=str(lock),
                       PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=environment,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode == 0:
        raise RuntimeError(f"ordinary checker accepted falsifier {label}")
    if diagnostic not in result.stdout:
        raise RuntimeError(f"{label} hit unexpected checker diagnostic: {result.stdout.strip()}")


@dataclass(frozen=True)
class LockCase:
    family: str
    deletion: tuple[Any, ...]
    mutate: Callable[[Any], None]
    deletion_diagnostic: str
    mutation_diagnostic: str


LOCK_CASES = [
    LockCase("generated-schema", ("schema",), lambda value: value.__setitem__("schema", True),
             "keys differ", "expected integer"),
    LockCase("wrong-type-compiler-settings", ("compiler", "settings", "optimizer", "runs"),
             lambda value: set_at(value, ("compiler", "settings", "optimizer", "enabled"), 1),
             "expected integer", "expected boolean"),
    LockCase("source-digest", ("sources", 0, "sha256"),
             lambda value: set_at(value, ("sources", 0, "sha256"),
                                  flip_hex(value["sources"][0]["sha256"])),
             "keys differ", "wrong source identity"),
    LockCase("selector", ("abi", "functions", 0, "selector"),
             lambda value: set_at(value, ("abi", "functions", 0, "selector"), "0x00000000"),
             "keys differ", "selector mismatch"),
    LockCase("event-indexing", ("abi", "events", 0, "indexed"),
             lambda value: set_at(value, ("abi", "events", 0, "indexed", 0), False),
             "keys differ", "indexing mismatch"),
    LockCase("immutable-span", ("artifacts", "immutableReferenceSpans", 0, "start"),
             lambda value: set_at(value, ("artifacts", "immutableReferenceSpans", 0, "start"), 314),
             "keys differ", "wrong"),
    LockCase("deployment-derivation", ("deployment", "createAddressDerivation", "derivedAddress"),
             lambda value: set_at(value, ("deployment", "createAddressDerivation", "nonce"), 1),
             "wrong", "wrong"),
    LockCase("formal-report", ("formalReport", "unresolved"),
             lambda value: set_at(value, ("formalReport", "properties", "verified"), 39),
             "keys differ", "wrong immutable report"),
]


def run_lock_cases(reference: Any, directory: Path) -> int:
    count = 0
    for case in LOCK_CASES:
        deleted = copy.deepcopy(reference)
        delete_at(deleted, case.deletion)
        schema_must_reject(deleted, f"{case.family}/deletion", case.deletion_diagnostic)
        checker_must_reject(deleted, f"{case.family}-deletion", case.deletion_diagnostic, directory)
        count += 1
        mutated = copy.deepcopy(reference)
        case.mutate(mutated)
        schema_must_reject(mutated, f"{case.family}/mutation", case.mutation_diagnostic)
        checker_must_reject(mutated, f"{case.family}-mutation", case.mutation_diagnostic, directory)
        count += 1
    return count


def run_event_coherent_case(reference: Any, directory: Path) -> int:
    value = copy.deepcopy(reference)
    event = value["abi"]["events"][0]
    event["indexed"][0] = False
    event["entry"]["inputs"][0]["indexed"] = False
    schema_must_reject(value, "coherent-event-indexing", "pinned indexing differs")
    checker_must_reject(value, "coherent-event-indexing", "pinned indexing differs", directory)
    return 1


def run_coherent_parameter_case(reference: Any, directory: Path) -> int:
    """Change a parameter plus all derived bytes; the independent world is still pinned."""
    spec = importlib.util.spec_from_file_location("lido_reference_generator", GENERATOR)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load Lido reference generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    value = copy.deepcopy(reference)
    world = value["artifacts"]["worlds"][1]
    parameters = copy.deepcopy(world["parameters"])
    parameters["maxPauseDuration"] += 1
    creation = bytes.fromhex(value["artifacts"]["creationTemplate"]["hex"][2:])
    runtime = bytes.fromhex(value["artifacts"]["runtimeTemplate"]["hex"][2:])
    replacement = module.world("independent-parameters", parameters, creation, runtime)
    value["artifacts"]["worlds"][1] = replacement
    schema_must_reject(value, "coherent-parameter-world", "wrong parameter identity")
    checker_must_reject(value, "coherent-parameter-world", "wrong parameter identity", directory)
    return 1


def checker_bytes_must_reject(data: bytes, label: str, diagnostic: str, directory: Path) -> None:
    lock = directory / f"raw-{label}.json"
    lock.write_bytes(data)
    environment = dict(os.environ, LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK=str(lock),
                       PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run([sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=environment,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode == 0 or diagnostic not in result.stdout:
        raise RuntimeError(f"raw JSON falsifier {label} unexpected result: {result.stdout.strip()}")


def run_raw_json_cases(reference: Any, directory: Path) -> int:
    baseline = canonical(reference)
    duplicate = baseline.replace(b"{\n", b'{\n  "schema": 2,\n', 1)
    non_finite = baseline.replace(b'"schema": 2', b'"schema": NaN', 1)
    noncanonical = json.dumps(reference, separators=(",", ":")).encode()
    checker_bytes_must_reject(duplicate, "duplicate-key", "duplicate JSON key", directory)
    checker_bytes_must_reject(non_finite, "non-finite", "non-finite JSON value", directory)
    checker_bytes_must_reject(noncanonical, "noncanonical", "not canonical JSON", directory)
    return 3


def mutate_json(path: Path, change: Callable[[Any], None]) -> None:
    value = json.loads(path.read_bytes())
    change(value)
    path.write_bytes(canonical(value))


def coordinated_input_cases() -> list[tuple[str, str, Callable[[Path], None]]]:
    def input_byte(reference: Path) -> None:
        path = reference / "inputs" / "std-json-input.json"
        path.write_bytes(path.read_bytes() + b" ")

    def source_world(reference: Path) -> None:
        old, new = "Emergency pause manager", "Emergency stop manager"
        source = reference / "inputs" / "source" / "CircuitBreaker.sol"
        source.write_text(source.read_text().replace(old, new, 1))
        standard_path = reference / "inputs" / "std-json-input.json"
        standard = json.loads(standard_path.read_bytes())
        standard["sources"]["src/CircuitBreaker.sol"]["content"] = \
            standard["sources"]["src/CircuitBreaker.sol"]["content"].replace(old, new, 1)
        standard_path.write_bytes(canonical(standard))
        sourcify_path = reference / "inputs" / "sourcify-v2.json"
        sourcify = json.loads(sourcify_path.read_bytes())
        sourcify["sources"]["src/CircuitBreaker.sol"]["content"] = \
            sourcify["sources"]["src/CircuitBreaker.sol"]["content"].replace(old, new, 1)
        sourcify["stdJsonInput"]["sources"]["src/CircuitBreaker.sol"]["content"] = \
            sourcify["stdJsonInput"]["sources"]["src/CircuitBreaker.sol"]["content"].replace(old, new, 1)
        sourcify_path.write_bytes(canonical(sourcify))

    def compiler_settings(reference: Path) -> None:
        for name in ("std-json-input.json", "sourcify-v2.json"):
            path = reference / "inputs" / name
            value = json.loads(path.read_bytes())
            target = value["settings"] if name == "std-json-input.json" else value["stdJsonInput"]["settings"]
            target["optimizer"]["runs"] = 9999
            if name == "sourcify-v2.json":
                value["compilation"]["compilerSettings"]["optimizer"]["runs"] = 9999
            path.write_bytes(canonical(value))

    def report_byte(reference: Path) -> None:
        path = next((reference / "inputs").glob("formal-report-*.pdf.b64"))
        data = bytearray(path.read_bytes())
        data[10] = ord("A") if data[10] != ord("A") else ord("B")
        path.write_bytes(bytes(data))

    return [
        ("input-byte", "authoritative input digest differs for std-json-input.json", input_byte),
        ("coordinated-source-input-sourcify",
         "authoritative input digest differs for source/CircuitBreaker.sol", source_world),
        ("coordinated-compiler-settings",
         "authoritative input digest differs for sourcify-v2.json", compiler_settings),
        ("formal-report-byte", "authoritative input digest differs for formal-report-", report_byte),
    ]


def run_coordinated_input_cases(directory: Path) -> int:
    count = 0
    for name, diagnostic, change in coordinated_input_cases():
        reference = directory / name
        shutil.copytree(REFERENCE, reference)
        change(reference)
        output = directory / f"{name}-lock.json"
        environment = dict(os.environ, LIDO_CIRCUIT_BREAKER_REFERENCE_DIR=str(reference),
                           LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK=str(output),
                           PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run([sys.executable, str(GENERATOR), "generate"], cwd=ROOT,
                                env=environment, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        if result.returncode == 0 or diagnostic not in result.stdout:
            raise RuntimeError(f"coordinated input falsifier {name} unexpected result: {result.stdout.strip()}")
        count += 1
    return count


def main() -> None:
    try:
        reference = json.loads(LOCK.read_bytes())
        validate_lock_schema(reference, "baseline lock")
        with tempfile.TemporaryDirectory(prefix="lido-reference-falsifiers-") as temporary:
            directory = Path(temporary)
            lock_cases = run_lock_cases(reference, directory)
            coherent = run_event_coherent_case(reference, directory)
            coherent += run_coherent_parameter_case(reference, directory)
            raw = run_raw_json_cases(reference, directory)
            coordinated = run_coordinated_input_cases(directory)
        print(f"OK — Lido CircuitBreaker reference falsifiers: {len(LOCK_CASES)} families, "
              f"{lock_cases} deletion/mutation, {coherent} coherent, {raw} raw/wrong-type, "
              f"{coordinated} coordinated-input cases rejected")
    except (OSError, json.JSONDecodeError, SchemaError, RuntimeError, subprocess.SubprocessError) as exc:
        raise SystemExit(f"test-lido-circuit-breaker-reference-falsifiers.py: {exc}")


if __name__ == "__main__":
    main()
