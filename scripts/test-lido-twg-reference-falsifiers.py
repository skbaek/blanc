#!/usr/bin/env python3
"""Live corruptions proving the Lido TWG reference channels reject drift."""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable

from lido_twg_reference_schema import keccak256, section_digest


ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / "scripts" / "reference" / "lido-twg"
LOCK = ROOT / "scripts" / "lido-twg-reference.json"
BUILDER = ROOT / "scripts" / "lido-twg-reference.py"


class FalsifierError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise FalsifierError(message)


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def run_check(reference: Path, lock: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["LIDO_TWG_REFERENCE_DIR"] = str(reference)
    env["LIDO_TWG_REFERENCE_LOCK"] = str(lock)
    return subprocess.run(
        [sys.executable, str(BUILDER), "check"], env=env,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )


def expect_rejected(name: str, result: subprocess.CompletedProcess[str]) -> None:
    combined = result.stdout + result.stderr
    if result.returncode == 0:
        fail(f"{name}: corruption was accepted")
    if "REGRESSION — Lido TWG reference:" not in combined:
        fail(f"{name}: failed outside the reference verdict: {combined}")


def mutate_file(name: str, path: Path, mutation: Callable[[bytes], bytes],
                reference: Path, lock: Path) -> None:
    original = path.read_bytes()
    try:
        changed = mutation(original)
        if changed == original:
            fail(f"{name}: mutation was idle")
        path.write_bytes(changed)
        expect_rejected(name, run_check(reference, lock))
    finally:
        path.write_bytes(original)


def mutate_lock(name: str, lock: Path, mutation: Callable[[dict[str, Any]], str | None],
                reference: Path) -> None:
    original = lock.read_bytes()
    try:
        root = json.loads(original)
        section = mutation(root)
        if section is not None:
            root["sectionDigests"][section] = section_digest(root[section])
        changed = canonical(root)
        if changed == original:
            fail(f"{name}: mutation was idle")
        lock.write_bytes(changed)
        expect_rejected(name, run_check(reference, lock))
    finally:
        lock.write_bytes(original)


def main() -> int:
    try:
        with tempfile.TemporaryDirectory(prefix="lido-twg-reference-falsifiers-") as temporary:
            temporary = Path(temporary)
            reference = temporary / "reference"
            lock = temporary / "lock.json"
            shutil.copytree(REFERENCE, reference)
            shutil.copyfile(LOCK, lock)
            baseline = run_check(reference, lock)
            if baseline.returncode != 0:
                fail(f"baseline failed: {baseline.stdout}{baseline.stderr}")

            inputs = reference / "inputs"
            mutate_file(
                "source-byte", inputs / "source/contracts/0.8.9/TriggerableWithdrawalsGateway.sol",
                lambda data: data.replace(b"uint256 public constant VERSION = 1;",
                                          b"uint256 public constant VERSION = 2;", 1),
                reference, lock,
            )
            mutate_file(
                "compiler-byte", inputs / "solc-emscripten-wasm32-v0.8.9+commit.e5eed63a.js",
                lambda data: bytes([data[0] ^ 1]) + data[1:], reference, lock,
            )
            mutate_file(
                "standard-input-settings", inputs / "standard-json-input.json",
                lambda data: data.replace(b'"runs": 200', b'"runs": 201', 1), reference, lock,
            )
            mutate_file(
                "standard-output-byte", inputs / "standard-json-output.json",
                lambda data: data[:-1] + (b" " if data[-1:] != b" " else b"\n"), reference, lock,
            )
            mutate_file(
                "rpc-response-byte", inputs / "rpc-drpc.json",
                lambda data: data.replace(b'"captureDateUtc": "2026-08-30"',
                                          b'"captureDateUtc": "2026-08-29"', 1),
                reference, lock,
            )

            extra = inputs / "unreviewed-input"
            try:
                extra.write_text("not authoritative\n")
                expect_rejected("extra-input", run_check(reference, lock))
            finally:
                extra.unlink(missing_ok=True)

            removed = inputs / "source/contracts/0.8.9/lib/ExitLimitUtils.sol"
            removed_bytes = removed.read_bytes()
            try:
                removed.unlink()
                expect_rejected("missing-source", run_check(reference, lock))
            finally:
                removed.write_bytes(removed_bytes)

            mutate_lock(
                "target-address", lock,
                lambda root: (root["target"].__setitem__("address", "0x" + "11" * 20), "target")[1],
                reference,
            )
            mutate_lock(
                "abi-selector", lock,
                lambda root: (root["abi"]["functions"][0].__setitem__("selector", "0x00000000"), "abi")[1],
                reference,
            )

            def artifact_mutation(root: dict[str, Any]) -> str:
                artifact = root["artifacts"]["creationTemplate"]
                raw = bytearray.fromhex(artifact["hex"][2:])
                raw[0] ^= 1
                artifact["hex"] = "0x" + raw.hex()
                artifact["sha256"] = hashlib.sha256(raw).hexdigest()
                artifact["keccak256"] = "0x" + keccak256(raw)
                return "artifacts"

            mutate_lock("coherent-creation-artifact", lock, artifact_mutation, reference)
            mutate_lock(
                "pause-role-snapshot", lock,
                lambda root: (root["snapshot"].__setitem__("circuitBreakerHasPauseRole", False),
                              "snapshot")[1], reference,
            )
            mutate_lock(
                "resume-governance", lock,
                lambda root: (root["snapshot"]["roles"]["RESUME_ROLE"]["members"].__setitem__(
                    0, "0x" + "22" * 20), "snapshot")[1], reference,
            )
            mutate_lock(
                "rpc-agreement", lock,
                lambda root: (root["rpc"]["agreement"].__setitem__("codeEqual", False), "rpc")[1],
                reference,
            )
            mutate_lock(
                "claim-boundary", lock,
                lambda root: (root["provenance"].__setitem__("claimBoundary", "deployment verified"),
                              "provenance")[1], reference,
            )

            original = lock.read_bytes()
            try:
                root = json.loads(original)
                root["sectionDigests"]["snapshot"] = "00" * 32
                lock.write_bytes(canonical(root))
                expect_rejected("section-digest", run_check(reference, lock))
            finally:
                lock.write_bytes(original)

            final = run_check(reference, lock)
            if final.returncode != 0:
                fail(f"post-falsifier baseline failed: {final.stdout}{final.stderr}")
    except (OSError, ValueError, json.JSONDecodeError, FalsifierError) as exc:
        print(f"REGRESSION — Lido TWG reference falsifiers: {exc}", file=sys.stderr)
        return 1
    print("PASS — Lido TWG reference falsifiers: 15 corruptions rejected; baseline restored")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
