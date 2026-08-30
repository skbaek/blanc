#!/usr/bin/env python3
"""Static self-tests for performance evidence/lineage generation (no EELS)."""
from __future__ import annotations

import argparse
import copy
import importlib.util
import sys
from pathlib import Path
from types import ModuleType

import lido_ossifiable_proxy_performance_schema as schema


def load_runner(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location("ossifiable_performance_runner_tested", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load runner {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def expect_failure(name: str, action) -> None:
    try:
        action()
    except (RuntimeError, schema.SchemaError):
        return
    raise AssertionError(f"{name}: hostile static mutation was accepted")


def profile(runner: ModuleType) -> dict:
    return {
        "notes": "synthetic static validator fixture",
        "opcodeCount": 1,
        "opcodeSequenceSha256": "1" * 64,
        "rows": [],
        "unframedGasCharges": [],
    }


def threshold(allowance: int) -> dict:
    return {
        "adequateGas": allowance,
        "adequateStatus": "success",
        "method": "deterministic binary search plus threshold/threshold-minus-one replay",
        "thresholdGas": 100,
        "thresholdMinusOne": {
            "gas": 99,
            "semanticAgreement": False,
            "status": "exception:OutOfGasError",
        },
        "thresholdStatus": "success",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument(
        "--runner", type=Path,
        default=Path(__file__).with_name("run-lido-ossifiable-proxy-performance.py"),
    )
    args = parser.parse_args()
    root = args.root.resolve()
    runner = load_runner(args.runner.resolve())
    manifest, lock, lock_raw = runner.load_campaign(root)
    fixtures = runner.Fixtures(manifest)
    addresses = fixtures.observed_addresses()
    reference_creation, reference_runtime = runner._reference_artifacts(lock)
    reference = runner.ArtifactSide("reference", reference_creation, reference_runtime)
    blanc = runner.ArtifactSide("blanc", b"\x60\x00\x00", b"\x00")
    candidate_commit = runner.git_output(root, "rev-parse", "HEAD")
    implementation = {
        "evaluatorSha256": "1" * 64,
        "evidenceCheckerSha256": "2" * 64,
        "launcherSha256": "3" * 64,
        "runnerSha256": "4" * 64,
        "schemaSha256": "5" * 64,
    }
    identities = {
        "candidateArtifacts": {
            "creationTemplate": runner.artifact_identity(blanc.creation_template),
            "returnedRuntime": runner.artifact_identity(blanc.returned_runtime),
        },
        "candidateCommit": candidate_commit,
        "eelsCommit": schema.EELS_COMMIT,
        "evaluatorEnvelopeSha256": "6" * 64,
        "implementation": implementation,
        "referenceArtifacts": {
            "creationTemplate": runner.artifact_identity(reference.creation_template),
            "returnedRuntime": runner.artifact_identity(reference.returned_runtime),
        },
        "referenceLockSha256": runner.sha256_bytes(lock_raw),
    }
    records: dict[str, dict] = {}
    values: dict[str, dict] = {}
    for index, cell in enumerate(manifest["cells"]):
        common = {
            "campaignManifestDigest": schema.MANIFEST_DIGEST,
            "cell": copy.deepcopy(cell),
            "format": runner.EVIDENCE_FORMAT,
            "identities": copy.deepcopy(identities),
            "predecessorResultSha256": None,
            "schema": 1,
            "stage": "baseline",
        }
        cell_id = cell["id"]
        if cell_id in {"A1", "A2"}:
            name = "returnedRuntime" if cell_id == "A1" else "creationTemplate"
            reference_value = identities["referenceArtifacts"][name]["byteLength"]
            blanc_value = identities["candidateArtifacts"][name]["byteLength"]
            record = {
                **common,
                "measurement": {
                    "blancValue": blanc_value,
                    "formula": "exact artifact byte length",
                    "referenceValue": reference_value,
                    "unit": "bytes",
                },
                "semantics": {
                    "agreement": True,
                    "artifact": name,
                    "blancIdentity": identities["candidateArtifacts"][name],
                    "mismatches": [],
                    "referenceIdentity": identities["referenceArtifacts"][name],
                },
                "sideExecutions": None,
            }
        else:
            if cell["world"]["kind"] == "direct-create-message":
                pre_slots = {slot: fixtures.zero_word for slot in fixtures.slot_names.values()}
            else:
                pre_slots = fixtures.proxy_slots(
                    cell["world"]["proxyState"], f"{cell_id} static fixture"
                )
            expected = runner.expected_projection(cell, fixtures, pre_slots, addresses)
            allowance = fixtures.scalar(cell["world"]["gasAllowance"], f"{cell_id} gas")
            side_rows = {}
            for side, artifact, used in (
                ("reference", reference, 1_000 + index),
                ("blanc", blanc, 999 + index),
            ):
                if cell["world"]["kind"] == "direct-create-message":
                    arguments = fixtures.constructor_arguments(cell["world"]["constructorTuple"], cell_id)
                    full = artifact.creation_template + arguments
                    full_input = {
                        "byteLength": len(full),
                        "hex": "0x" + full.hex(),
                        "sha256": runner.sha256_bytes(full),
                    }
                else:
                    full_input = None
                side_rows[side] = {
                    "completionThreshold": threshold(allowance),
                    "fullCreateInput": full_input,
                    "gasAllowance": allowance,
                    "gasLeft": allowance - used,
                    "gasUsed": used,
                    "opcodeProfile": profile(runner),
                    "projection": copy.deepcopy(expected),
                    "refundCounterExcluded": 0,
                }
            reference_value = side_rows["reference"]["gasUsed"]
            blanc_value = side_rows["blanc"]["gasUsed"]
            record = {
                **common,
                "measurement": {
                    "blancValue": blanc_value,
                    "formula": "message.gas - output.gas_left",
                    "referenceValue": reference_value,
                    "refundAccounting": "pre-refund; refund counter excluded",
                    "transactionIntrinsicGasIncluded": False,
                    "unit": "gas",
                },
                "semantics": {
                    "agreement": True,
                    "blancMismatches": [],
                    "crossSideMismatches": [],
                    "expected": expected,
                    "referenceMismatches": [],
                },
                "sideExecutions": side_rows,
            }
        records[cell_id] = record
        values[cell_id] = {
            "agreement": True,
            "blanc": blanc_value,
            "reference": reference_value,
        }

    hashes = {
        cell_id: runner.sha256_bytes(runner.canonical_bytes(record))
        for cell_id, record in records.items()
    }
    cells = [
        runner._result_cell(cell, values[cell["id"]], hashes[cell["id"]])
        for cell in manifest["cells"]
    ]
    diagnostics = runner.build_diagnostics(
        manifest=manifest,
        lock=lock,
        stage="baseline",
        predecessor=None,
        evidence_records=records,
        evidence_hashes=hashes,
        reference_side=reference,
        blanc_side=blanc,
    )
    result = runner.build_result(
        manifest=manifest,
        lock_raw=lock_raw,
        stage="baseline",
        predecessor=None,
        created_at="2026-08-30T00:00:00Z",
        candidate_commit=candidate_commit,
        reference_side=reference,
        blanc_side=blanc,
        cells=cells,
        diagnostic_digest=runner.sha256_bytes(runner.canonical_bytes(diagnostics)),
    )
    schema.validate_result_schema(
        result, manifest, root=root, enforce_self_digest=True, validate_external=True
    )
    for index, cell_id in enumerate(schema.CELL_ORDER):
        runner.validate_evidence_record(
            records[cell_id], manifest=manifest, result=result, cell_index=index
        )
    runner.validate_diagnostics_record(
        diagnostics,
        manifest=manifest,
        result=result,
        evidence_hashes=hashes,
        evidence_records=records,
        lock=lock,
    )

    formula = copy.deepcopy(records["F1"])
    formula["measurement"]["formula"] = "output.gas_left"
    expect_failure(
        "gas formula laundering",
        lambda: runner.validate_evidence_record(
            formula, manifest=manifest, result=result, cell_index=4
        ),
    )
    projection = copy.deepcopy(records["F1"])
    projection["semantics"]["expected"]["status"] = "revert"
    expect_failure(
        "expected projection laundering",
        lambda: runner.validate_evidence_record(
            projection, manifest=manifest, result=result, cell_index=4
        ),
    )
    create_input = copy.deepcopy(records["A3"])
    raw = bytearray(runner.hex_bytes(
        create_input["sideExecutions"]["blanc"]["fullCreateInput"]["hex"], "static input"
    ))
    raw[0] ^= 1
    input_row = create_input["sideExecutions"]["blanc"]["fullCreateInput"]
    input_row["hex"] = "0x" + bytes(raw).hex()
    input_row["sha256"] = runner.sha256_bytes(bytes(raw))
    expect_failure(
        "coherent CREATE input substitution",
        lambda: runner.validate_evidence_record(
            create_input, manifest=manifest, result=result, cell_index=2
        ),
    )
    bad_diagnostics = copy.deepcopy(diagnostics)
    bad_diagnostics["completionThresholds"]["F1"]["blanc"]["thresholdGas"] += 1
    expect_failure(
        "diagnostic threshold laundering",
        lambda: runner.validate_diagnostics_record(
            bad_diagnostics,
            manifest=manifest,
            result=result,
            evidence_hashes=hashes,
            evidence_records=records,
            lock=lock,
        ),
    )
    bad_final = copy.deepcopy(result)
    bad_final["result"]["stage"] = "final"
    bad_final["result"]["digest"]["value"] = schema.result_digest(bad_final)
    expect_failure(
        "final without predecessor",
        lambda: schema.validate_result_schema(
            bad_final, manifest, root=root, validate_external=False
        ),
    )
    print(
        "OK — OssifiableProxy performance runner static tests: valid 25-cell synthetic "
        "baseline + 5 hostile mutations; no Lean/EELS/measurement"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
