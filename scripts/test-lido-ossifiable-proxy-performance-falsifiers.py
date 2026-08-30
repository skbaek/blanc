#!/usr/bin/env python3
"""Hostile static falsifiers for the OssifiableProxy performance contract.

All tests mutate JSON documents or resolve vendored identities.  No EVM,
execution-specs, Lean, network, or timing entrypoint is invoked.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Callable

import lido_ossifiable_proxy_performance_schema as schema


Mutation = Callable[[dict], None]


def repair_manifest(document: dict) -> None:
    document["campaign"]["digest"]["value"] = schema.manifest_digest(document)


def repair_result(document: dict) -> None:
    document["result"]["digest"]["value"] = schema.result_digest(document)


def expect_error(name: str, action: Callable[[], None], fragment: str | None = None) -> None:
    try:
        action()
    except schema.SchemaError as exc:
        if fragment is not None and fragment not in str(exc):
            raise AssertionError(
                f"{name}: rejected for the wrong reason; expected {fragment!r}, got {exc!r}"
            ) from exc
        return
    raise AssertionError(f"{name}: hostile mutation was accepted")


def manifest_falsifier(
    original: dict,
    root: Path,
    name: str,
    mutation: Mutation,
    fragment: str,
    *,
    external: bool = False,
    frozen: bool = False,
) -> None:
    document = copy.deepcopy(original)
    mutation(document)
    repair_manifest(document)
    expect_error(
        name,
        lambda: schema.validate_manifest_schema(
            document,
            root=root,
            enforce_frozen_digest=frozen,
            validate_external=external,
        ),
        fragment,
    )


def result_falsifier(
    original: dict,
    manifest: dict,
    root: Path,
    name: str,
    mutation: Mutation,
    fragment: str,
    *,
    external: bool = False,
) -> None:
    document = copy.deepcopy(original)
    mutation(document)
    repair_result(document)
    expect_error(
        name,
        lambda: schema.validate_result_schema(
            document,
            manifest,
            root=root,
            enforce_self_digest=True,
            validate_external=external,
        ),
        fragment,
    )


def identity(byte_length: int, seed: str) -> dict:
    return {
        "byteLength": byte_length,
        "keccak256": "0x" + seed * 64,
        "sha256": seed.upper().lower() * 64,
    }


def make_result(manifest: dict, root: Path) -> dict:
    lock_raw = (root / schema.REFERENCE_LOCK_RELATIVE).read_bytes()
    lock = schema.strict_json(lock_raw, "reference lock")
    reference_artifacts = {}
    for result_name, lock_name in (
        ("creationTemplate", "creationTemplate"),
        ("returnedRuntime", "runtime"),
    ):
        artifact, _ = schema._validate_artifact_row(
            lock["artifacts"][lock_name], f"reference lock.artifacts.{lock_name}",
        )
        reference_artifacts[result_name] = schema._artifact_identity(artifact)

    candidate_artifacts = {
        "creationTemplate": identity(
            reference_artifacts["creationTemplate"]["byteLength"] - 1, "1",
        ),
        "returnedRuntime": identity(
            reference_artifacts["returnedRuntime"]["byteLength"] - 1, "2",
        ),
    }
    cells = []
    for index, (cell_id, group, scalar, _) in enumerate(schema.CELL_SPECS):
        if cell_id == "A1":
            reference_value = reference_artifacts["returnedRuntime"]["byteLength"]
            blanc_value = candidate_artifacts["returnedRuntime"]["byteLength"]
        elif cell_id == "A2":
            reference_value = reference_artifacts["creationTemplate"]["byteLength"]
            blanc_value = candidate_artifacts["creationTemplate"]["byteLength"]
        else:
            reference_value = 100
            blanc_value = 99 if index < 13 else (100 if index < 19 else 101)

        if index < 13:
            status = "complete"
            agreement = True
            classification = "strict-win"
            reason = None
        elif index < 19:
            status = "complete"
            agreement = True
            classification = "tie"
            reason = None
        elif index < 23:
            status = "complete"
            agreement = True
            classification = "loss"
            reason = None
        elif index == 23:
            status = "complete"
            agreement = False
            classification = "incomparable"
            reason = "proved semantic mismatch"
            reference_value = 100
            blanc_value = 99
        else:
            status = "instrumentation-failure"
            agreement = None
            classification = "incomparable"
            reason = "instrumentation failure: no scalar record"
            reference_value = None
            blanc_value = None

        cells.append({
            "blancValue": blanc_value,
            "classification": classification,
            "evidence": {
                "recordSha256": hashlib.sha256(f"cell:{cell_id}".encode()).hexdigest(),
            },
            "group": group,
            "id": cell_id,
            "incomparableReason": reason,
            "measurementStatus": status,
            "ordinal": index + 1,
            "referenceValue": reference_value,
            "scalar": scalar,
            "semanticAgreement": agreement,
            "unit": "bytes" if cell_id in {"A1", "A2"} else "gas",
        })

    result = {
        "campaign": {
            "denominator": schema.DENOMINATOR,
            "fixedOrder": schema.CELL_ORDER,
            "manifestDigest": schema.MANIFEST_DIGEST,
            "manifestFormatVersion": 2,
            "manifestPath": str(schema.MANIFEST_RELATIVE),
            "minimumStrictWins": schema.MINIMUM_STRICT_WINS,
        },
        "cells": cells,
        "diagnostics": [],
        "identities": {
            "candidate": {
                "artifacts": candidate_artifacts,
                "commit": schema.CAMPAIGN_BASE_COMMIT,
                "evaluator": "scripts/eval-lido-ossifiable-proxy-artifacts.lean",
                "treeClean": True,
            },
            "execution": {"eelsCommit": schema.EELS_COMMIT, "fork": "Prague"},
            "reference": {
                "artifacts": reference_artifacts,
                "lock": str(schema.REFERENCE_LOCK_RELATIVE),
                "lockSha256": hashlib.sha256(lock_raw).hexdigest(),
            },
        },
        "result": {
            "createdAt": "2026-08-30T00:00:00Z",
            "digest": {
                "algorithm": "sha256",
                "canonicalization": schema.MANIFEST_CANONICALIZATION,
                "scope": schema.RESULT_DIGEST_SCOPE,
                "value": "",
            },
            "format": schema.RESULT_FORMAT,
            "formatVersion": 1,
            "measurementsIncluded": True,
            "predecessorResultSha256": None,
            "stage": "baseline",
        },
        "schema": 1,
        "score": schema.score_for_cells(cells),
    }
    repair_result(result)
    return result


def _set_nested(document: dict, keys: tuple[str, ...], value: object) -> None:
    current = document
    for key in keys[:-1]:
        current = current[key]
    current[keys[-1]] = value


def run_manifest_falsifiers(manifest: dict, root: Path) -> int:
    cases: list[tuple[str, Mutation, str, bool, bool]] = [
        ("cell deletion", lambda m: m["cells"].pop(), "expected 25 entries", False, False),
        ("cell reorder", lambda m: m["cells"].__setitem__(slice(0, 2), [m["cells"][1], m["cells"][0]]), "denominator/order", False, False),
        ("ordinal drift", lambda m: _set_nested(m, ("cells",), [dict(row, ordinal=99) if row["id"] == "F1" else row for row in m["cells"]]), "ordinal", False, False),
        ("scalar drift", lambda m: m["cells"][4].__setitem__("scalar", "gas"), "scalar", False, False),
        ("denominator drift", lambda m: m["scoreContract"].__setitem__("denominator", 24), "score contract", False, False),
        ("threshold drift", lambda m: m["scoreContract"].__setitem__("minimumStrictWins", 12), "score contract", False, False),
        ("measurement formula drift", lambda m: m["measurementContract"]["callScalar"].__setitem__("formula", "output.gas_left"), "measurement contract", False, False),
        ("results top-level smuggling", lambda m: m.__setitem__("results", []), "expected fields", False, False),
        ("measurements flag smuggling", lambda m: m["campaign"].__setitem__("measurementsIncluded", True), "result smuggling", False, False),
        ("correction lineage drift", lambda m: m["campaign"]["supersedes"].__setitem__("resultsGenerated", True), "correction lineage", False, False),
        ("unresolved access set", lambda m: m["cells"][4]["world"].__setitem__("accessSet", "missing"), "unresolved fixture", False, False),
        ("calldata odd nibble", lambda m: m["fixtures"]["calldata"]["fallback-32"].__setitem__("hex", m["fixtures"]["calldata"]["fallback-32"]["hex"][:-1]), "malformed value", False, False),
        ("calldata length drift", lambda m: m["fixtures"]["calldata"]["fallback-32"].__setitem__("byteLength", 31), "byte length differs", False, False),
        ("mock bytecode hash drift", lambda m: m["fixtures"]["mockImplementations"]["stop"].__setitem__("sha256", "0" * 64), "SHA-256 differs", False, False),
        ("constructor ABI drift", lambda m: m["fixtures"]["constructorTuples"]["canonical-empty"].__setitem__("abiArgumentsHex", m["fixtures"]["constructorTuples"]["canonical-empty"]["abiArgumentsHex"][:-2] + "01"), "ABI encoding differs", False, False),
        ("warm address delta", lambda m: m["fixtures"]["accessSets"]["forwarding-warm"].__setitem__("accessedAddresses", m["fixtures"]["accessSets"]["forwarding-cold"]["accessedAddresses"]), "warm address delta", False, False),
        ("warm storage delta", lambda m: m["fixtures"]["accessSets"]["forwarding-warm"]["accessedStorageKeys"][0].__setitem__("key", schema.ADMIN_SLOT), "storage-key delta", False, False),
        ("orphan semantic fixture", lambda m: m["fixtures"]["expectedSemantics"].__setitem__("orphan", {}), "key membership drifted", False, False),
        ("duplicate implementation account", lambda m: m["cells"][15]["world"]["implementationAccounts"][1].__setitem__("address", "canonical-implementation"), "duplicate implementation account", False, False),
        ("artifact cell length drift", lambda m: m["cells"][0]["world"].__setitem__("referenceByteLength", 2498), "reference byte length differs", True, False),
        ("compiler identity drift", lambda m: m["identities"]["reference"]["compiler"].__setitem__("sha256", "0x" + "0" * 64), "frozen artifact/reference", False, False),
        ("source identity drift", lambda m: m["identities"]["reference"].__setitem__("sourceSha256", "0" * 64), "frozen artifact/reference", False, False),
    ]
    for name, mutation, fragment, external, frozen in cases:
        manifest_falsifier(
            manifest, root, name, mutation, fragment, external=external, frozen=frozen,
        )

    swapped = lambda m: (
        m["fixtures"]["artifactBindings"]["creationTemplate"].__setitem__(
            "reference", str(schema.REFERENCE_LOCK_RELATIVE) + "#/artifacts/runtime",
        ),
        m["fixtures"]["artifactBindings"]["returnedRuntime"].__setitem__(
            "reference", str(schema.REFERENCE_LOCK_RELATIVE) + "#/artifacts/creationTemplate",
        ),
    )
    manifest_falsifier(
        manifest, root, "swapped external artifact pointers", swapped,
        "reference byte length differs", external=True,
    )
    manifest_falsifier(
        manifest, root, "frozen campaign digest",
        lambda m: m["campaign"].__setitem__("authority", "changed"),
        "frozen campaign identity differs", frozen=True,
    )
    expect_error(
        "unresolved JSON Pointer",
        lambda: schema.resolve_json_pointer({"artifacts": {}}, "/artifacts/runtime", "test"),
        "unresolved JSON Pointer",
    )
    expect_error(
        "malformed JSON Pointer escape",
        lambda: schema.resolve_json_pointer({"a": 1}, "/~2", "test"),
        "invalid JSON Pointer escape",
    )
    return len(cases) + 4


def run_result_falsifiers(baseline: dict, manifest: dict, root: Path) -> int:
    cases: list[tuple[str, Mutation, str, bool]] = [
        ("result cell deletion", lambda r: r["cells"].pop(), "expected 25 entries", False),
        ("result cell reorder", lambda r: r["cells"].__setitem__(slice(0, 2), [r["cells"][1], r["cells"][0]]), "fixed denominator/order", False),
        ("result classification forgery", lambda r: r["cells"][0].__setitem__("classification", "tie"), "expected derived", False),
        ("result score forgery", lambda r: r["score"].__setitem__("strictWins", 14), "counts/13-win verdict", False),
        ("result denominator drift", lambda r: r["campaign"].__setitem__("denominator", 24), "campaign binding", False),
        ("result threshold drift", lambda r: r["score"].__setitem__("minimumStrictWins", 12), "counts/13-win verdict", False),
        ("semantic mismatch scored", lambda r: r["cells"][23].__setitem__("classification", "strict-win"), "expected derived incomparable", False),
        ("instrumentation failure carries value", lambda r: r["cells"][24].__setitem__("referenceValue", 100), "cannot carry score values", False),
        ("runtime reference scalar drift", lambda r: r["cells"][0].__setitem__("referenceValue", r["cells"][0]["referenceValue"] + 1), "locked runtime", False),
        ("runtime candidate scalar drift", lambda r: r["cells"][0].__setitem__("blancValue", r["cells"][0]["blancValue"] - 1), "candidate runtime identity", False),
        ("manifest binding drift", lambda r: r["campaign"].__setitem__("manifestDigest", "0" * 64), "campaign binding", False),
        ("reference lock digest drift", lambda r: r["identities"]["reference"].__setitem__("lockSha256", "0" * 64), "reference-lock identity", True),
        ("reference artifact digest drift", lambda r: r["identities"]["reference"]["artifacts"]["returnedRuntime"].__setitem__("sha256", "0" * 64), "reference returnedRuntime identity", True),
        ("candidate artifact length drift", lambda r: r["identities"]["candidate"]["artifacts"]["returnedRuntime"].__setitem__("byteLength", r["cells"][0]["blancValue"] + 1), "candidate runtime identity", False),
        ("final predecessor missing", lambda r: (r["result"].__setitem__("stage", "final"), r["result"].__setitem__("predecessorResultSha256", None)), "expected string", False),
        ("baseline predecessor present", lambda r: r["result"].__setitem__("predecessorResultSha256", "0" * 64), "baseline must be null", False),
        ("threshold verdict forgery", lambda r: r["score"].__setitem__("thresholdMet", False), "counts/13-win verdict", False),
        ("extra cell result field", lambda r: r["cells"][0].__setitem__("gas", 1), "expected fields", False),
        ("invalid result stage", lambda r: r["result"].__setitem__("stage", "candidate"), "expected baseline or final", False),
        ("complete null scalar", lambda r: r["cells"][2].__setitem__("referenceValue", None), "expected integer", False),
        ("scored cell reason", lambda r: r["cells"][2].__setitem__("incomparableReason", "not allowed"), "must be null", False),
        ("duplicate cell evidence", lambda r: r["cells"][1]["evidence"].__setitem__("recordSha256", r["cells"][0]["evidence"]["recordSha256"]), "distinct evidence", False),
        ("invalid evidence digest", lambda r: r["cells"][0]["evidence"].__setitem__("recordSha256", "x" * 64), "malformed value", False),
        ("result top-level smuggling", lambda r: r.__setitem__("measurements", []), "expected fields", False),
    ]
    for name, mutation, fragment, external in cases:
        result_falsifier(
            baseline, manifest, root, name, mutation, fragment, external=external,
        )

    digest_forgery = copy.deepcopy(baseline)
    digest_forgery["result"]["digest"]["value"] = "0" * 64
    expect_error(
        "result self-digest forgery",
        lambda: schema.validate_result_schema(
            digest_forgery, manifest, root=root, enforce_self_digest=True,
            validate_external=False,
        ),
        "self-digest differs",
    )

    diagnostic_duplicate = copy.deepcopy(baseline)
    diagnostic_duplicate["diagnostics"] = [
        {"name": "report-only", "recordSha256": "3" * 64},
        {"name": "report-only", "recordSha256": "4" * 64},
    ]
    repair_result(diagnostic_duplicate)
    expect_error(
        "duplicate report-only diagnostic",
        lambda: schema.validate_result_schema(
            diagnostic_duplicate, manifest, root=root, validate_external=False,
        ),
        "duplicate report-only diagnostic",
    )

    expect_error(
        "baseline cannot close threshold",
        lambda: schema.require_final_threshold(baseline),
        "requires a final result",
    )

    below = copy.deepcopy(baseline)
    below["result"]["stage"] = "final"
    below["result"]["predecessorResultSha256"] = baseline["result"]["digest"]["value"]
    below["cells"][12]["blancValue"] = below["cells"][12]["referenceValue"]
    below["cells"][12]["classification"] = "tie"
    below["score"] = schema.score_for_cells(below["cells"])
    repair_result(below)
    schema.validate_result_schema(below, manifest, root=root, validate_external=False)
    expect_error(
        "12-win final cannot close threshold",
        lambda: schema.require_final_threshold(below),
        "below 13 strict wins",
    )
    return len(cases) + 4


def run_parser_falsifiers() -> int:
    expect_error(
        "duplicate JSON key",
        lambda: schema.strict_json(b'{"schema":1,"schema":1}', "duplicate"),
        "duplicate JSON key",
    )
    expect_error(
        "non-finite JSON scalar",
        lambda: schema.strict_json(b'{"value":NaN}', "nonfinite"),
        "non-finite JSON value",
    )
    return 2


def run_checker_falsifiers(
    root: Path, manifest_path: Path, manifest: dict, baseline: dict,
) -> int:
    checker = Path(__file__).with_name("check-lido-ossifiable-proxy-performance.py")
    final = copy.deepcopy(baseline)
    final["result"]["stage"] = "final"
    final["result"]["predecessorResultSha256"] = baseline["result"]["digest"]["value"]
    repair_result(final)

    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    with tempfile.TemporaryDirectory(prefix="ossifiable-performance-static-") as temporary:
        directory = Path(temporary)
        baseline_path = directory / "baseline.json"
        final_path = directory / "final.json"
        baseline_path.write_bytes(schema.canonical_bytes(baseline))
        final_path.write_bytes(schema.canonical_bytes(final))
        good = subprocess.run(
            [
                sys.executable, "-B", str(checker), "--root", str(root),
                "--manifest", str(manifest_path), "--result", str(baseline_path),
                "--result", str(final_path), "--require-final-threshold",
            ],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        if good.returncode != 0:
            raise AssertionError(
                "ordinary checker rejected a valid linked baseline/final pair: "
                + good.stderr.strip()
            )

        smuggled = copy.deepcopy(manifest)
        smuggled["results"] = []
        repair_manifest(smuggled)
        bad_manifest = directory / "smuggled-manifest.json"
        bad_manifest.write_bytes(schema.canonical_bytes(smuggled))
        bad = subprocess.run(
            [
                sys.executable, "-B", str(checker), "--root", str(root),
                "--manifest", str(bad_manifest),
            ],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        if bad.returncode == 0 or "REGRESSION" not in bad.stderr:
            raise AssertionError("ordinary checker accepted results smuggled into the manifest")
    return 2


def main() -> int:
    parser = argparse.ArgumentParser(description="Run static hostile schema falsifiers")
    parser.add_argument("--root", type=Path, default=schema.DEFAULT_ROOT)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    manifest_path = (args.manifest or root / schema.MANIFEST_RELATIVE).resolve()
    try:
        _, manifest_value = schema.load_json(manifest_path, "performance manifest")
        manifest = schema.validate_manifest_schema(
            manifest_value, root=root, enforce_frozen_digest=True, validate_external=True,
        )
        baseline = make_result(manifest, root)
        schema.validate_result_schema(
            baseline, manifest, root=root, enforce_self_digest=True, validate_external=True,
        )
        total = 0
        total += run_manifest_falsifiers(manifest, root)
        total += run_result_falsifiers(baseline, manifest, root)
        total += run_parser_falsifiers()
        total += run_checker_falsifiers(root, manifest_path, manifest, baseline)
    except (AssertionError, OSError, schema.SchemaError) as exc:
        print(f"REGRESSION — OssifiableProxy performance falsifier: {exc}", file=sys.stderr)
        return 1
    print(
        "OK — OssifiableProxy performance falsifiers: "
        f"{total} hostile static cases rejected; valid baseline/final schemas accepted; "
        "12 wins rejected and 13 wins accepted; no measurements run"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
