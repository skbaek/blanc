#!/usr/bin/env python3
"""Deterministic gate-campaign selection; production campaigns stay complete."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / "scripts/gate-campaign-policy.json"
ECONOMY = ROOT / "scripts/gate-economy.json"
REPORT = ROOT / "docs/GATE_SAMPLING.md"


class SamplingError(RuntimeError):
    pass


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def select_campaign(
    gate_id: str,
    candidate: str,
    schema: dict[str, Any],
    cases: list[dict[str, str]],
    *,
    enabled: bool,
    audit_day: int | None = None,
    sampled_failure: bool = False,
) -> dict[str, Any]:
    ids = [case.get("id") for case in cases]
    if not ids or not all(isinstance(item, str) and item for item in ids):
        raise SamplingError("every campaign case needs a stable id")
    if len(ids) != len(set(ids)):
        raise SamplingError("campaign case ids are not unique")
    ordered = sorted(cases, key=lambda case: case["id"])
    mandatory = [case for case in ordered if case.get("class") != "optional"]
    optional = [case for case in ordered if case.get("class") == "optional"]
    strata = sorted({case.get("stratum", "") for case in optional})
    if optional and ("" in strata or any(set(case) != {"id", "class", "stratum"} for case in optional)):
        raise SamplingError("optional cases need exactly one nonempty failure stratum")
    schema_digest = digest(schema)
    seed = digest({"candidate": candidate, "gate": gate_id, "schema": schema_digest})
    eligible = len(optional) >= 9 and bool(strata)
    complete = (
        not enabled
        or not eligible
        or sampled_failure
        or (audit_day is not None and audit_day % 7 == 0)
    )
    if complete:
        selected_optional = optional
    else:
        count = max(2, math.ceil(math.sqrt(len(optional))), len(strata))
        ranked = sorted(optional, key=lambda case: digest([seed, case["id"]]))
        selected_optional = []
        for stratum in strata:
            selected_optional.append(next(case for case in ranked if case["stratum"] == stratum))
        selected_ids = {case["id"] for case in selected_optional}
        selected_optional.extend(
            case for case in ranked if case["id"] not in selected_ids
        )
        selected_optional = selected_optional[:count]
    selected = sorted(
        [case["id"] for case in mandatory + selected_optional]
    )
    omitted = sorted(set(ids) - set(selected))
    return {
        "gate": gate_id,
        "candidate": candidate,
        "schema_digest": schema_digest,
        "seed": seed,
        "population": len(cases),
        "optional_population": len(optional),
        "strata": strata,
        "eligible": eligible,
        "enabled": enabled,
        "expanded_after_failure": sampled_failure,
        "selected": selected,
        "omitted": omitted,
    }


def validate_policy() -> tuple[dict[str, Any], list[str]]:
    policy = json.loads(POLICY.read_text(encoding="utf-8"))
    economy = json.loads(ECONOMY.read_text(encoding="utf-8"))
    if set(policy) != {"schema", "population_source", "default", "enabled_families", "decision"}:
        raise SamplingError("campaign policy shape drifted")
    if policy["schema"] != 1 or policy["population_source"] != "scripts/gate-economy.json":
        raise SamplingError("campaign policy authority drifted")
    if policy["enabled_families"] != []:
        raise SamplingError("production sampling requires family-specific shadow evidence")
    expected_default = {
        "candidate_positive": "complete",
        "mandatory_boundary": "complete",
        "harness_cases": "mandatory-boundary",
        "optional_cases": [],
    }
    if policy["default"] != expected_default:
        raise SamplingError("conservative default classification drifted")
    harness = sorted(
        row["id"] for row in economy["rows"] if "harness-self-test" in row["work"]
    )
    return policy, harness


def render_policy() -> str:
    policy, harness = validate_policy()
    return "\n".join([
        "# Blanc gate campaign policy",
        "",
        "Generated from `scripts/gate-campaign-policy.json` and the economic inventory.",
        "",
        "Production sampling is **disabled**. Every product-positive scenario and every",
        "harness case remains complete; harness cases are conservatively classified as",
        "mandatory boundaries. No optional production case exists, so no sampling boundary",
        "moved and no 20-identity enablement claim is made.",
        "",
        f"Complete harness families ({len(harness)}): " + ", ".join(f"`{item}`" for item in harness) + ".",
        "",
        "The deterministic sampler is retained and self-tested for a future family that",
        "earns eligibility. It binds candidate, gate and schema; includes every stratum;",
        "runs a complete audit every seventh scheduler day; and expands immediately after",
        "a sampled failure.",
        "",
        f"Decision: {policy['decision']}",
        "",
    ])


def self_test() -> None:
    schema = {"version": 1, "contract": "synthetic-shadow-control"}
    cases = [
        {"id": "positive", "class": "candidate-positive"},
        {"id": "boundary", "class": "mandatory-boundary"},
    ] + [
        {"id": f"optional-{index:02d}", "class": "optional", "stratum": f"s{index % 3}"}
        for index in range(16)
    ]
    first = select_campaign("g", "tree-a", schema, cases, enabled=True)
    again = select_campaign("g", "tree-a", schema, list(reversed(cases)), enabled=True)
    if first != again:
        raise SamplingError("selection is not deterministic or enumeration-order independent")
    if not {"positive", "boundary"}.issubset(first["selected"]):
        raise SamplingError("mandatory/product-positive case was sampled")
    selected_strata = {
        case["stratum"] for case in cases
        if case["id"] in first["selected"] and case.get("class") == "optional"
    }
    if selected_strata != {"s0", "s1", "s2"}:
        raise SamplingError("a failure stratum was absent from the draw")
    if len(first["selected"]) != 2 + max(2, math.ceil(math.sqrt(16)), 3):
        raise SamplingError("sample cardinality formula drifted")
    if select_campaign("g", "tree-b", schema, cases, enabled=True)["seed"] == first["seed"]:
        raise SamplingError("candidate movement did not change the seed")
    if select_campaign("g", "tree-a", {"version": 2}, cases, enabled=True)["seed"] == first["seed"]:
        raise SamplingError("schema movement did not change the seed")
    seven_day_union: set[str] = set()
    for day in range(1, 8):
        seven_day_union.update(
            select_campaign("g", "tree-a", schema, cases, enabled=True, audit_day=day)["selected"]
        )
    if seven_day_union != {case["id"] for case in cases}:
        raise SamplingError("seven-day audit rotation did not cover the population")
    expanded = select_campaign(
        "g", "tree-a", schema, cases, enabled=True, sampled_failure=True
    )
    if expanded["omitted"]:
        raise SamplingError("sampled failure did not expand to the complete campaign")
    small = select_campaign("small", "tree", schema, cases[:2] + cases[2:10], enabled=True)
    if small["omitted"]:
        raise SamplingError("a smaller than nine optional campaign was sampled")
    validate_policy()


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args(argv)
    if sum((arguments.self_test, arguments.write, arguments.check)) != 1:
        parser.error("choose exactly one mode")
    try:
        if arguments.self_test:
            self_test()
            print("OK — gate sampling: deterministic strata, rotation and escalation controls")
            return 0
        rendered = render_policy()
        if arguments.write:
            REPORT.write_text(rendered, encoding="utf-8")
            print(f"OK — gate sampling: wrote {REPORT.relative_to(ROOT)}")
            return 0
        if not REPORT.is_file() or REPORT.read_text(encoding="utf-8") != rendered:
            raise SamplingError("generated campaign report is stale")
        print("OK — gate sampling: production remains complete; policy reconciles")
        return 0
    except (OSError, json.JSONDecodeError, SamplingError) as error:
        print(f"REGRESSION — gate sampling: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
