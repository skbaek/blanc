#!/usr/bin/env python3
"""Mutation controls for the independent Lido TWG differential schema."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "fixtures" / "lido-twg" / "manifest.json"
SCHEMA = ROOT / "scripts" / "lido_twg_differential_schema.py"


def compact(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def digest(value: Any) -> str:
    return hashlib.sha256(compact(value)).hexdigest()


def row_digest(row: dict[str, Any]) -> str:
    return digest({
        "assertions": row["tags"], "expected": row["semantic"]["expected"],
        "reference": row["reference"], "blanc": row["blanc"],
    })


def refresh_sections(manifest: dict[str, Any], *sections: str) -> None:
    for section in sections:
        manifest["sectionDigests"][section] = digest(manifest[section])


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def schema_accepts(path: Path) -> bool:
    result = subprocess.run(
        [sys.executable, str(SCHEMA), str(path)], cwd=ROOT,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        env={**__import__("os").environ, "PYTHONDONTWRITEBYTECODE": "1"})
    return result.returncode == 0


def mutate_channel(field: str, evidence_key: str) -> Callable[[dict[str, Any]], None]:
    def mutation(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"]
                   if item["name"] == "trigger-single-exact-fee")
        if field == "status":
            row["blanc"][evidence_key][-1] = "revert"
        else:
            row["blanc"][evidence_key] = "0" * 64
        row["semanticDigest"] = row_digest(row)
        refresh_sections(manifest, "rows")
    return mutation


def main() -> int:
    if not schema_accepts(MANIFEST):
        raise RuntimeError("baseline TWG differential manifest does not pass its schema")
    baseline = json.loads(MANIFEST.read_text())
    mutations: list[tuple[str, Callable[[dict[str, Any]], None]]] = [
        ("status-channel", mutate_channel("status", "status")),
        ("returndata-channel", mutate_channel("returndata", "returndataSha256")),
        ("logical-state-channel", mutate_channel("logicalState", "logicalStateSha256")),
        ("auxiliary-state-channel", mutate_channel("auxiliaryState", "auxiliaryStateSha256")),
        ("eth-channel", mutate_channel("eth", "ethSha256")),
        ("logs-channel", mutate_channel("logs", "logsSha256")),
        ("call-trace-channel", mutate_channel("callTrace", "callTraceSha256")),
    ]

    def identity(manifest: dict[str, Any]) -> None:
        manifest["artifacts"]["reference"]["runtime"]["sha256"] = "0" * 64
        refresh_sections(manifest, "artifacts")

    def artifact_program_identity(manifest: dict[str, Any]) -> None:
        manifest["artifacts"]["proof"]["artifactProgramCommit"] = "0" * 40
        manifest["documentFill"]["evidence"]["artifactProgramCommit"] = "0" * 40
        refresh_sections(manifest, "artifacts", "documentFill")

    def proof_certificate_identity(manifest: dict[str, Any]) -> None:
        manifest["artifacts"]["proof"]["proofCertificateCommit"] = "0" * 40
        manifest["documentFill"]["evidence"]["proofCertificateCommit"] = "0" * 40
        refresh_sections(manifest, "artifacts", "documentFill")

    def oracle(manifest: dict[str, Any]) -> None:
        manifest["oracle"]["eelsCommit"] = "0" * 40
        refresh_sections(manifest, "oracle")

    def row_deletion(manifest: dict[str, Any]) -> None:
        manifest["rows"].pop()
        manifest["counts"]["rows"] -= 1
        refresh_sections(manifest, "rows", "counts")

    def deviation_widening(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"] if item["deviation"] == "TWG-D01")
        row["expectedMismatchFields"].append("status")
        for item in manifest["coverage"]["deviations"]:
            if item["id"] == "TWG-D01":
                item["fields"].append("status")
        refresh_sections(manifest, "rows", "coverage")

    def sentinel_semantic(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"]
                   if item["name"] == "pause-for-sentinel")
        row["semantic"]["expected"]["resumeSince"] -= 1
        row["semanticDigest"] = row_digest(row)
        refresh_sections(manifest, "rows")

    def event_order_semantic(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"]
                   if item["name"] == "constructor-success")
        row["semantic"]["expected"]["eventTopics"].reverse()
        row["semanticDigest"] = row_digest(row)
        refresh_sections(manifest, "rows")

    def pause_error_semantic(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"]
                   if item["name"] == "pause-for-when-paused")
        row["semantic"]["expected"]["actionReturndata"] = "0xb047186b"
        row["semanticDigest"] = row_digest(row)
        refresh_sections(manifest, "rows")

    def router_selector_semantic(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"]
                   if item["name"] == "trigger-single-exact-fee")
        row["semantic"]["expected"]["routerSelector"] = "0x00000000"
        row["semanticDigest"] = row_digest(row)
        refresh_sections(manifest, "rows")

    def extra_semantic_claim(manifest: dict[str, Any]) -> None:
        row = next(item for item in manifest["rows"]
                   if item["name"] == "view-version")
        row["semantic"]["expected"]["unverifiedClaim"] = True
        row["semanticDigest"] = row_digest(row)
        refresh_sections(manifest, "rows")

    def resource_coordinate(manifest: dict[str, Any]) -> None:
        row = manifest["resourceEvidence"]["namedGasRows"][0]
        row["coordinate"] = "constructor-success#99:constructor"
        manifest["documentFill"]["evidence"]["gas"]["rows"][0]["coordinate"] = row["coordinate"]
        refresh_sections(manifest, "resourceEvidence", "documentFill")

    def gas_completeness(manifest: dict[str, Any]) -> None:
        manifest["resourceEvidence"]["namedGasRows"].pop()
        manifest["documentFill"]["evidence"]["gas"]["rows"].pop()
        refresh_sections(manifest, "resourceEvidence", "documentFill")

    def gas_dominance(manifest: dict[str, Any]) -> None:
        row = manifest["resourceEvidence"]["namedGasRows"][0]
        row["blanc"] = row["reference"]
        row["delta"] = 0
        boundary = next(item for item in manifest["resourceEvidence"]["boundaries"]
                        if item["coordinate"] == row["coordinate"])
        boundary["blancGas"] = boundary["referenceGas"]
        boundary["delta"] = 0
        manifest["resourceEvidence"]["vectorSha256"] = digest(
            manifest["resourceEvidence"]["boundaries"])
        manifest["documentFill"]["evidence"]["gas"]["rows"] = copy.deepcopy(
            manifest["resourceEvidence"]["namedGasRows"])
        refresh_sections(manifest, "resourceEvidence", "documentFill")

    def performance_control(control_id: str, field: str) -> Callable[[dict[str, Any]], None]:
        def mutation(manifest: dict[str, Any]) -> None:
            control = next(item for item in manifest["artifacts"]["blanc"]["performanceControls"]
                           if item["id"] == control_id)
            control[field] = False
            refresh_sections(manifest, "artifacts")
        return mutation

    def exclusion_boundary(manifest: dict[str, Any]) -> None:
        manifest["coverage"]["criterion"] = manifest["coverage"]["criterion"].replace(
            "empty/unknown/short dispatch", "empty/unknown dispatch", 1)
        refresh_sections(manifest, "coverage")

    def template_identity(manifest: dict[str, Any]) -> None:
        manifest["documentFill"]["templates"]["compatibility"] = "0" * 64
        refresh_sections(manifest, "documentFill")

    def section_digest(manifest: dict[str, Any]) -> None:
        manifest["sectionDigests"]["rows"] = "0" * 64

    mutations.extend([
        ("artifact-identity", identity),
        ("artifact-program-identity", artifact_program_identity),
        ("proof-certificate-identity", proof_certificate_identity),
        ("eels-oracle", oracle),
        ("case-manifest-deletion", row_deletion),
        ("deviation-field-widening", deviation_widening),
        ("sentinel-semantic", sentinel_semantic),
        ("event-order-semantic", event_order_semantic),
        ("pause-error-semantic", pause_error_semantic),
        ("router-selector-semantic", router_selector_semantic),
        ("extra-semantic-claim", extra_semantic_claim),
        ("resource-coordinate", resource_coordinate),
        ("gas-completeness", gas_completeness),
        ("gas-dominance", gas_dominance),
        ("exclusion-boundary", exclusion_boundary),
        ("document-template-identity", template_identity),
        ("section-digest", section_digest),
    ])
    for control_id in ("packing", "keccak-key", "enumeration", "compiled-route"):
        mutations.extend([
            (f"{control_id}-production", performance_control(control_id, "production")),
            (f"{control_id}-mutant", performance_control(control_id, "mutantRejected")),
        ])

    rejected = 0
    with tempfile.TemporaryDirectory(prefix="lido-twg-differential-falsifiers-") as tmp:
        root = Path(tmp)
        for index, (name, mutation) in enumerate(mutations):
            candidate = copy.deepcopy(baseline)
            mutation(candidate)
            path = root / f"{index:02d}-{name}.json"
            write_json(path, candidate)
            if schema_accepts(path):
                raise RuntimeError(f"{name} falsifier did not bite")
            rejected += 1

        duplicate = MANIFEST.read_text().replace(
            '  "schema": 1,', '  "schema": 1,\n  "schema": 1,', 1)
        path = root / "duplicate-key.json"
        path.write_text(duplicate)
        if schema_accepts(path):
            raise RuntimeError("duplicate-key falsifier did not bite")
        rejected += 1

    print(f"PASS — Lido TWG differential falsifiers: {rejected} "
          "channel/identity/manifest/semantic corruptions rejected; "
          "artifact-program, proof-certificate, gas-completeness, strict-dominance, "
          "performance-shape, and exclusion-boundary controls bite")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("REGRESSION — Lido TWG differential falsifiers: " +
              str(exc).replace("\n", " "), file=sys.stderr)
        raise SystemExit(1)
