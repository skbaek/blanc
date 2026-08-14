#!/usr/bin/env python3
"""Live independent falsifiers for the Lido full resource vector."""
from __future__ import annotations

import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Callable, Mapping

from lido_circuit_breaker_resource_schema import (
    ResourceSchemaError,
    canonical_digest,
    derive_summary,
    load_manifest,
    validate_resource_manifest,
)


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "fixtures" / "lido-circuit-breaker" / "manifest.json"


def resources(value: Mapping[str, Any]) -> dict[str, Any]:
    return value["resourceEvidence"]


def refresh_derived_claims(value: dict[str, Any]) -> None:
    resource = resources(value)
    boundaries = resource["boundaries"]
    resource["summary"] = derive_summary(boundaries)
    coordinates = [row["coordinate"] for row in boundaries]
    payload = {
        "schema": resource["schema"], "gasModel": resource["gasModel"],
        "lifecycle": resource["lifecycle"], "identities": resource["identities"],
        "boundaries": boundaries,
    }
    resource["vectorDigests"] = {
        "orderedCoordinatesSha256": hashlib.sha256(
            ("\n".join(coordinates) + "\n").encode()).hexdigest(),
        "fullResourceVectorSha256": canonical_digest(payload),
    }


def must_reject(baseline: Mapping[str, Any], name: str, diagnostic: str,
                mutate: Callable[[dict[str, Any]], None]) -> None:
    value = copy.deepcopy(baseline)
    mutate(value)
    try:
        validate_resource_manifest(value, name)
    except ResourceSchemaError as exc:
        if diagnostic not in str(exc):
            raise RuntimeError(f"{name} hit unexpected diagnostic: {exc}") from exc
        return
    raise RuntimeError(f"independent resource schema accepted falsifier {name}")


def delete_boundary(value: dict[str, Any]) -> None:
    resources(value)["boundaries"].pop()


def duplicate_boundary(value: dict[str, Any]) -> None:
    rows = resources(value)["boundaries"]
    rows[1] = copy.deepcopy(rows[0])


def reorder_boundaries(value: dict[str, Any]) -> None:
    manifest_rows = value["rows"]
    manifest_rows[0], manifest_rows[1] = manifest_rows[1], manifest_rows[0]
    rows = resources(value)["boundaries"]
    rows[0], rows[1] = rows[1], rows[0]
    rows[0]["ordinal"], rows[1]["ordinal"] = 0, 1
    refresh_derived_claims(value)


def relabel_boundary(value: dict[str, Any]) -> None:
    replacement_target = "0x8888888888888888888888888888888888888888"
    execution = value["rows"][0]["execution"]
    execution["constructor"]["target"] = replacement_target
    replacement_label = "primaryConstructor@" + replacement_target
    execution["boundaryOrder"][0] = replacement_label
    row = resources(value)["boundaries"][0]
    row["label"] = replacement_label
    row["coordinate"] = f"{row['case']}#{row['boundary']}:{replacement_label}"
    refresh_derived_claims(value)


def drop_primary_constructor(value: dict[str, Any]) -> None:
    rows = resources(value)["boundaries"]
    index = next(i for i, row in enumerate(rows) if row["phase"] == "primaryConstructor")
    rows.pop(index)


def mutate_gas(value: dict[str, Any]) -> None:
    resources(value)["boundaries"][0]["blancGasUsed"] += 1


def coherent_gas_delta(value: dict[str, Any]) -> None:
    row = resources(value)["boundaries"][0]
    row["solidityGasUsed"] += 1
    row["blancGasUsed"] += 1
    refresh_derived_claims(value)


def positive_optimized_delta(value: dict[str, Any]) -> None:
    resources(value)["lifecycle"]["stage"] = "optimized"
    replacement = "1" * 64
    value["blanc"]["creationTemplate"]["sha256"] = replacement
    resources(value)["identities"]["blancCreationTemplateSha256"] = replacement


def unpinned_optimized_transition(value: dict[str, Any]) -> None:
    resource = resources(value)
    resource["lifecycle"]["stage"] = "optimized"
    replacement = "2" * 64
    value["blanc"]["creationTemplate"]["sha256"] = replacement
    resource["identities"]["blancCreationTemplateSha256"] = replacement
    for row in resource["boundaries"]:
        if row["adequacy"] == "adequate" and row["blancMinusSolidity"] > 0:
            row["blancGasUsed"] = row["solidityGasUsed"]
            row["blancMinusSolidity"] = 0
            row["comparisonClass"] = "equal"
    refresh_derived_claims(value)


def coherent_identity(value: dict[str, Any]) -> None:
    replacement = "0" * 64
    value["blanc"]["official"]["runtimeSha256"] = replacement
    resources(value)["identities"]["blancOfficialRuntimeSha256"] = replacement
    refresh_derived_claims(value)


def gas_model(value: dict[str, Any]) -> None:
    resources(value)["gasModel"]["refundAccounting"] = "post-refund"
    refresh_derived_claims(value)


def main() -> int:
    baseline = load_manifest(MANIFEST)
    validate_resource_manifest(baseline, "baseline")
    cases = [
        ("delete", "deletion/count", delete_boundary),
        ("duplicate", "duplicate resource coordinate", duplicate_boundary),
        ("reorder", "independent resource-vector digest differs", reorder_boundaries),
        ("relabel", "independent resource-vector digest differs", relabel_boundary),
        ("drop-primary-constructor", "deletion/count", drop_primary_constructor),
        ("mutate-gas", "delta is not derived", mutate_gas),
        ("coherent-gas-delta", "independent resource-vector digest differs", coherent_gas_delta),
        ("positive-optimized-delta", "positive adequate-gas delta", positive_optimized_delta),
        ("unpinned-optimized-transition", "independent resource-vector pin is not installed",
         unpinned_optimized_transition),
        ("coherent-identity", "baseline lifecycle Blanc identity drifted", coherent_identity),
        ("gas-model", "gas model differs", gas_model),
    ]
    for name, diagnostic, mutate in cases:
        must_reject(baseline, name, diagnostic, mutate)
    print(
        "OK — Lido CircuitBreaker resource falsifiers: "
        f"{len(cases)} deletion/duplicate/order/label/constructor/gas/delta/"
        "dominance/transition/identity/model mutants rejected"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, json.JSONDecodeError, ResourceSchemaError, RuntimeError) as exc:
        print("REGRESSION — Lido CircuitBreaker resource falsifiers: " + str(exc),
              file=sys.stderr)
        raise SystemExit(1)
