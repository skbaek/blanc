#!/usr/bin/env python3
"""Biting G4-1/G4-2 falsifiers for the OssifiableProxy reference bundle."""
from __future__ import annotations

import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from lido_ossifiable_proxy_reference_schema import (
    SchemaError,
    keccak256,
    section_digest,
    strict_json,
    validate_lock_schema,
)


ROOT = Path(__file__).resolve().parents[1]
LOCK = ROOT / "scripts" / "lido-ossifiable-proxy-reference.json"
GENERATOR = ROOT / "scripts" / "lido-ossifiable-proxy-reference.py"
COMPATIBILITY = ROOT / "scripts" / "lido-ossifiable-proxy-compatibility.py"
REFERENCE = ROOT / "scripts" / "reference" / "lido-ossifiable-proxy"
DOCUMENT = ROOT / "OSSIFIABLE_PROXY_COMPATIBILITY.md"


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def compact(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def flip_hex(value: str) -> str:
    return value[:-1] + ("1" if value[-1] != "1" else "2")


def repair_section_digests(value: dict[str, Any]) -> None:
    for section in value.get("sectionDigests", {}):
        if section in value:
            value["sectionDigests"][section] = section_digest(value[section])


def schema_must_reject(value: Any, label: str) -> None:
    repair_section_digests(value)
    try:
        validate_lock_schema(value, label)
    except SchemaError:
        return
    raise RuntimeError(f"independent schema accepted falsifier {label}")


def checker_must_reject_lock(value: Any, label: str, temporary: Path) -> None:
    repair_section_digests(value)
    path = temporary / f"{label}.json"
    path.write_bytes(canonical(value))
    environment = dict(os.environ,
                       LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK=str(path),
                       PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run(
        [sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=environment,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    if result.returncode == 0:
        raise RuntimeError(f"ordinary checker accepted lock falsifier {label}: {result.stdout.strip()}")


def raw_must_reject(data: bytes, label: str) -> None:
    try:
        strict_json(data, label)
    except SchemaError:
        return
    except Exception as exc:
        if exc.__class__.__name__ == "ReferenceError":
            return
        raise
    raise RuntimeError(f"strict JSON parser accepted raw falsifier {label}")


@dataclass(frozen=True)
class LockCase:
    name: str
    mutate: Callable[[dict[str, Any]], None]


def mutate_coherent_signature(value: dict[str, Any]) -> None:
    row = value["abi"]["functions"][0]
    row["signature"] = "proxy__getAdmin(uint256)"
    row["selector"] = "0x" + keccak256(row["signature"].encode())[:8]
    row["entry"]["inputs"] = [{"internalType": "uint256", "name": "probe", "type": "uint256"}]
    raw = next(entry for entry in value["abi"]["raw"]
               if entry.get("type") == "function" and entry.get("name") == "proxy__getAdmin")
    raw["inputs"] = copy.deepcopy(row["entry"]["inputs"])
    value["abi"]["rawSha256"] = hashlib.sha256(compact(value["abi"]["raw"])).hexdigest()
    value["abi"]["decodingBoundaries"][1]["signature"] = row["signature"]


def mutate_function_addition(value: dict[str, Any]) -> None:
    extra = copy.deepcopy(value["abi"]["functions"][0])
    extra["signature"] = "probe()"
    extra["selector"] = "0x" + keccak256(b"probe()")[:8]
    extra["entry"]["name"] = "probe"
    value["abi"]["functions"].append(extra)
    value["abi"]["counts"]["functions"] += 1


def mutate_behavioral_beacon(value: dict[str, Any]) -> None:
    beacon = next(row for row in value["abi"]["compilerEvents"]
                  if row["signature"] == "BeaconUpgraded(address)")
    value["abi"]["behavioralEvents"].append(copy.deepcopy(beacon))
    value["abi"]["counts"]["behavioralEvents"] = 4


def lock_cases() -> list[LockCase]:
    return [
        LockCase("deletion", lambda value: value.pop("generator")),
        LockCase("wrong-type", lambda value: value["abi"]["constructor"].__setitem__("payable", 0)),
        LockCase("digest", lambda value: value["provenance"]["inputFiles"][0].__setitem__(
            "sha256", flip_hex(value["provenance"]["inputFiles"][0]["sha256"]))),
        LockCase("selector", lambda value: value["abi"]["functions"][0].__setitem__("selector", "0x00000000")),
        LockCase("topic", lambda value: value["abi"]["behavioralEvents"][0].__setitem__("topic0", "0x" + "00" * 32)),
        LockCase("custom-error", lambda value: value["abi"]["errors"][0].__setitem__("selector", "0x00000000")),
        LockCase("dependency", lambda value: value["provenance"]["sourceFiles"].pop()),
        LockCase("compiler-setting", lambda value: value["compiler"]["standardInputSettings"].__setitem__("evmVersion", "berlin")),
        LockCase("constructor-boundary", lambda value: value["deployment"]["constructor"].__setitem__("encodedSuffixBytes", 127)),
        LockCase("deployment-derivation", lambda value: value["deployment"]["createAddressDerivation"].__setitem__(
            "derivedAddress", "0x0000000000000000000000000000000000000000")),
        LockCase("coherent-signature", mutate_coherent_signature),
        LockCase("endpoint-addition", mutate_function_addition),
        LockCase("dispatch-collision", lambda value: value["abi"]["functions"][1].__setitem__(
            "selector", value["abi"]["functions"][0]["selector"])),
        LockCase("named-nonpayability", lambda value: value["abi"]["functions"][-1]["entry"].__setitem__(
            "stateMutability", "payable")),
        LockCase("fallback-payability", lambda value: value["abi"]["fallback"]["entry"].__setitem__(
            "stateMutability", "nonpayable")),
        LockCase("behavioral-beacon-addition", mutate_behavioral_beacon),
        LockCase("reason-string", lambda value: value["sourceBehavior"]["reasonStrings"][0].__setitem__(
            "message", "changed")),
        LockCase("functional-slot", lambda value: value["sourceBehavior"]["slots"][1].__setitem__(
            "value", "0x" + "00" * 32)),
        LockCase("runtime", lambda value: value["artifacts"]["runtime"].__setitem__(
            "hex", flip_hex(value["artifacts"]["runtime"]["hex"]))),
        LockCase("rpc-operator", lambda value: value["rpc"]["captures"][0].__setitem__("operator", "same-operator")),
    ]


def replace_file(path: Path, data: bytes) -> None:
    path.unlink()
    path.write_bytes(data)


def run_input_checker(reference_dir: Path, label: str) -> None:
    environment = dict(os.environ,
                       LIDO_OSSIFIABLE_PROXY_REFERENCE_DIR=str(reference_dir),
                       LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK=str(LOCK),
                       PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run(
        [sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=environment,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    if result.returncode == 0:
        raise RuntimeError(f"ordinary checker accepted input falsifier {label}: {result.stdout.strip()}")


def input_falsifiers(temporary: Path) -> int:
    count = 0

    def stage(name: str) -> tuple[Path, Path]:
        target = temporary / f"reference-{name}"
        def symlink_copy(source: str, destination: str) -> str:
            os.symlink(source, destination)
            return destination

        shutil.copytree(REFERENCE, target, copy_function=symlink_copy)
        return target, target / "inputs"

    reference, inputs = stage("deleted-source")
    (inputs / "source/@openzeppelin/contracts-v4.4/proxy/beacon/IBeacon.sol").unlink()
    run_input_checker(reference, "deleted-source")
    count += 1

    reference, inputs = stage("dependency-edit")
    path = inputs / "source/@openzeppelin/contracts-v4.4/utils/Address.sol"
    replace_file(path, path.read_bytes().replace(b"low-level delegate call failed", b"low-level delegate call changed"))
    run_input_checker(reference, "dependency-edit")
    count += 1

    reference, inputs = stage("compiler-setting")
    path = inputs / "standard-json-input.json"
    value = json.loads(path.read_bytes())
    value["settings"]["evmVersion"] = "berlin"
    replace_file(path, json.dumps(value, sort_keys=True, separators=(",", ":")).encode())
    run_input_checker(reference, "compiler-setting")
    count += 1

    reference, inputs = stage("coordinated-source-input")
    source_path = inputs / "source/contracts/0.8.9/proxy/OssifiableProxy.sol"
    mutated_source = source_path.read_text().replace("An ossifiable proxy contract", "A changed ossifiable proxy contract")
    replace_file(source_path, mutated_source.encode())
    input_path = inputs / "standard-json-input.json"
    value = json.loads(input_path.read_bytes())
    value["sources"]["contracts/0.8.9/proxy/OssifiableProxy.sol"]["content"] = mutated_source
    replace_file(input_path, json.dumps(value, sort_keys=True, separators=(",", ":")).encode())
    run_input_checker(reference, "coordinated-source-input")
    count += 1

    reference, inputs = stage("compiler-binary")
    path = inputs / "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js"
    raw = path.read_bytes()
    replace_file(path, raw[:-1] + bytes([raw[-1] ^ 1]))
    run_input_checker(reference, "compiler-binary")
    count += 1

    reference, inputs = stage("compiler-output")
    path = inputs / "standard-json-output.json"
    value = json.loads(path.read_bytes())
    artifact = value["contracts"]["contracts/0.8.9/proxy/OssifiableProxy.sol"]["OssifiableProxy"]
    artifact["evm"]["bytecode"]["object"] = flip_hex(artifact["evm"]["bytecode"]["object"])
    replace_file(path, json.dumps(value, sort_keys=True, separators=(",", ":")).encode())
    run_input_checker(reference, "compiler-output")
    count += 1

    reference, inputs = stage("rpc-code")
    path = inputs / "rpc-drpc.json"
    value = json.loads(path.read_bytes())
    capture = next(row for row in value["captures"] if row["label"] == "code")
    capture["responseRaw"] = flip_hex(capture["responseRaw"])
    capture["responseSha256"] = hashlib.sha256(capture["responseRaw"].encode()).hexdigest()
    replace_file(path, canonical(value))
    run_input_checker(reference, "rpc-code")
    count += 1
    return count


def compatibility_falsifiers(temporary: Path) -> int:
    original = DOCUMENT.read_text()
    marker_line = next(line for line in original.splitlines()
                       if line.startswith("<!-- OSSIFIABLE-PROXY-ENDPOINT "))
    fake = '<!-- OSSIFIABLE-PROXY-ENDPOINT {"acceptsValue":false,"selector":"0x12345678","signature":"probe()","stateMutability":"nonpayable"} -->'
    cases = {
        "endpoint-deletion": original.replace(marker_line + "\n", "", 1),
        "endpoint-addition": original.replace(marker_line, marker_line + "\n" + fake, 1),
        "signature-mutation": original.replace("proxy__getAdmin()", "proxy__getAdmin(uint256)", 1),
        "crosscut-deletion": original.replace("<!-- OSSIFIABLE-PROXY-CROSSCUT selector-dispatch -->\n", "", 1),
        "lock-digest-drift": original.replace("<!-- OSSIFIABLE-PROXY-LOCK ", "<!-- OSSIFIABLE-PROXY-LOCK 0", 1),
    }
    for name, contents in cases.items():
        path = temporary / f"compat-{name}.md"
        path.write_text(contents)
        environment = dict(os.environ,
                           LIDO_OSSIFIABLE_PROXY_COMPATIBILITY_DOC=str(path),
                           PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run(
            [sys.executable, str(COMPATIBILITY), "check"], cwd=ROOT, env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        if result.returncode == 0:
            raise RuntimeError(f"compatibility checker accepted document falsifier {name}")
    return len(cases)


def main() -> int:
    try:
        reference = strict_json(LOCK.read_bytes(), str(LOCK))
        validate_lock_schema(reference, "falsifier baseline")
        lock_count = 0
        for case in lock_cases():
            mutated = copy.deepcopy(reference)
            case.mutate(mutated)
            schema_must_reject(mutated, case.name)
            lock_count += 1

        baseline = canonical(reference)
        raw_cases = {
            "duplicate-key": baseline.replace(b"{\n", b'{\n  "schema": 1,\n', 1),
            "non-finite": baseline.replace(b'"schema": 1', b'"schema": NaN', 1),
            "noncanonical": json.dumps(reference, separators=(",", ":")).encode(),
        }
        raw_count = 0
        for name, data in raw_cases.items():
            if name == "noncanonical":
                parsed = strict_json(data, name)
                if data == canonical(parsed):
                    raise RuntimeError("noncanonical JSON falsifier unexpectedly canonical")
            else:
                raw_must_reject(data, name)
            raw_count += 1

        with tempfile.TemporaryDirectory(prefix="ossifiable-falsifiers-") as raw_temporary:
            temporary = Path(raw_temporary)
            coherent = copy.deepcopy(reference)
            mutate_coherent_signature(coherent)
            checker_must_reject_lock(coherent, "coherent-signature-checker", temporary)
            noncanonical_path = temporary / "noncanonical.json"
            noncanonical_path.write_bytes(raw_cases["noncanonical"])
            environment = dict(os.environ,
                               LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK=str(noncanonical_path),
                               PYTHONDONTWRITEBYTECODE="1")
            result = subprocess.run(
                [sys.executable, str(GENERATOR), "check"], cwd=ROOT, env=environment,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            if result.returncode == 0:
                raise RuntimeError("ordinary checker accepted noncanonical lock JSON")
            input_count = input_falsifiers(temporary)
            document_count = compatibility_falsifiers(temporary)
    except (OSError, SchemaError, RuntimeError) as exc:
        print(f"REGRESSION — Lido OssifiableProxy reference falsifiers: {exc}", file=sys.stderr)
        return 1
    print(
        "OK — Lido OssifiableProxy falsifiers: "
        f"{lock_count} independent lock/schema families; {raw_count} raw JSON families; "
        f"{input_count} deletion/dependency/compiler/deployment/RPC/coordinated-input families; "
        f"{document_count} compatibility deletion/addition/signature/document-drift families; "
        "ordinary checker rejection exercised"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
