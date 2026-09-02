#!/usr/bin/env python3
"""Generate and check Blanc's economic inventory without executing gates."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "scripts/gate-registry.json"
ECONOMY = ROOT / "scripts/gate-economy.json"
CATALOGUE = ROOT / "scripts/GATES.md"
OUTPUT = ROOT / "docs/GATE_ECONOMY.md"
WORK_CLASSES = {"candidate-positive", "static-corpus", "harness-self-test", "prerequisite"}
RESOURCE_CLASSES = {"light", "elaboration", "exclusive"}


class EconomyError(RuntimeError):
    pass


def load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise EconomyError(f"cannot read {path.relative_to(ROOT)}: {error}") from error


def command_text(gate: dict[str, Any]) -> str:
    return " ".join(gate["command"])


def catalogue_times() -> dict[str, str]:
    times: dict[str, str] = {}
    row = re.compile(r"^\| `([^`]+)` \|.*\| ([^|]+) \|\s*$")
    for line in CATALOGUE.read_text(encoding="utf-8").splitlines():
        match = row.match(line)
        if match:
            times.setdefault(match.group(1), match.group(2).strip())
    return times


def ci_population() -> int:
    commands: set[str] = set()
    for raw in (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("- "):
            line = line[2:].strip()
        if line.startswith("run:"):
            line = line[4:].strip()
        if line.startswith("scripts/check-") and ".sh" in line:
            commands.add(line)
    return len(commands)


def validated() -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]], dict[str, str], dict[str, Any]]:
    registry = load(REGISTRY)
    economy = load(ECONOMY)
    if registry.get("schema") != 1 or not isinstance(registry.get("gates"), list):
        raise EconomyError("gate registry schema is not 1")
    if registry.get("economy_inventory") != "scripts/gate-economy.json":
        raise EconomyError("gate registry does not require its economic inventory")
    if economy.get("schema") != 1 or not isinstance(economy.get("rows"), list):
        raise EconomyError("economic inventory schema is not 1")
    expected_meta = {
        "launch_catalogue_commit": "dfbb0207b7890c8b17fba1c5069350b78d769cd9",
        "launch_population": 53,
        "launch_ci_population": 34,
        "final_ci_population": 40,
        "split_families": [
            "lido-circuit-breaker-registry",
            "execution-occurrence",
            "cycle-write-free",
            "transient-settlement",
            "proxy-pair-upgrade",
        ],
        "post_launch_gates": [
            "beacon-deposit-assurance",
            "beacon-deposit-deployment",
            "weth10-current-mainnet",
            "prorata-weth-vault-artifact",
            "prorata-weth-vault-boundary",
        ],
    }
    for key, expected in expected_meta.items():
        if economy.get(key) != expected:
            raise EconomyError(f"economic inventory {key} is not the reviewed value")
    gates = sorted(registry["gates"], key=lambda gate: gate["order"])
    rows: dict[str, dict[str, Any]] = {}
    for raw in economy["rows"]:
        if not isinstance(raw, dict) or not isinstance(raw.get("id"), str):
            raise EconomyError("economic row is not an identified object")
        identifier = raw["id"]
        if identifier in rows:
            raise EconomyError(f"duplicate economic row {identifier}")
        if set(raw) - {"id", "work", "resource_class", "prerequisites", "historical_catches", "material_identity"} or not {
            "id", "work", "resource_class", "prerequisites", "historical_catches"
        }.issubset(raw):
            raise EconomyError(f"economic row {identifier} has an unknown or missing field")
        work = raw["work"]
        if not isinstance(work, list) or not work or set(work) - WORK_CLASSES:
            raise EconomyError(f"economic row {identifier} has invalid work classes")
        if len(work) != len(set(work)):
            raise EconomyError(f"economic row {identifier} repeats a work class")
        if raw["resource_class"] not in RESOURCE_CLASSES:
            raise EconomyError(f"economic row {identifier} has invalid resource class")
        if not all(isinstance(item, str) for item in raw["prerequisites"]):
            raise EconomyError(f"economic row {identifier} has malformed prerequisites")
        if not all(isinstance(item, str) and item for item in raw["historical_catches"]):
            raise EconomyError(f"economic row {identifier} has malformed historical catches")
        material = raw.get("material_identity")
        if raw["resource_class"] == "exclusive" and (
            not isinstance(material, str)
            or not material.startswith(("output-aware:", "already precise:", "conservative:"))
        ):
            raise EconomyError(
                f"exclusive row {identifier} has no output-aware/already-precise/conservative disposition"
            )
        rows[identifier] = raw
    gate_ids = {gate["id"] for gate in gates}
    if set(rows) != gate_ids:
        missing = sorted(gate_ids - set(rows))
        extra = sorted(set(rows) - gate_ids)
        raise EconomyError(f"economic population mismatch: missing={missing}, extra={extra}")
    for identifier, raw in rows.items():
        unknown = sorted(set(raw["prerequisites"]) - gate_ids)
        if unknown:
            raise EconomyError(f"economic row {identifier} has unknown prerequisites {unknown}")
        if identifier in raw["prerequisites"]:
            raise EconomyError(f"economic row {identifier} depends on itself")
    for gate in gates:
        identifier = gate["id"]
        material = rows[identifier].get("material_identity", "")
        has_certificate = bool(gate.get("inputs", {}).get("material_output"))
        claims_output_aware = material.startswith("output-aware:")
        if has_certificate != claims_output_aware:
            raise EconomyError(
                f"economic row {identifier} and registry disagree on material-output certification"
            )
    times = catalogue_times()
    missing_times = [command_text(gate) for gate in gates if command_text(gate) not in times]
    if missing_times:
        raise EconomyError(f"catalogue timing cells missing for {missing_times}")
    expected_population = (
        economy["launch_population"]
        + len(economy["split_families"])
        + len(economy["post_launch_gates"])
    )
    if len(gates) != expected_population:
        raise EconomyError(
            "final population does not equal launch plus split and post-launch rows"
        )
    if ci_population() != economy["final_ci_population"]:
        raise EconomyError("final CI population does not match the workflow")
    return gates, rows, times, economy


def mark(classes: list[str], name: str) -> str:
    return "yes" if name in classes else "—"


def render() -> str:
    gates, rows, times, economy = validated()
    lines = [
        "# Blanc gate economic inventory",
        "",
        "Generated by `scripts/gate-economy.py` from the launch-current gate registry,",
        "catalogue, and `scripts/gate-economy.json`. Do not edit by hand.",
        "",
        f"Launch population at `{economy['launch_catalogue_commit'][:12]}`: "
        f"**{economy['launch_population']}** catalogue rows and "
        f"**{economy['launch_ci_population']}** CI commands.",
        f"Final population: **{len(gates)}** catalogue rows and "
        f"**{economy['final_ci_population']}** CI commands. CI reconciliation is also audited by",
        "`scripts/check-gates.sh --audit`. Timing cells below are the catalogue's latest",
        "host-local observations; `unmeasured` is preserved honestly and no parallel sums are made.",
        "",
        "| # | gate | positive | static/corpus | harness/self-test | prerequisites | mutable input classes | material-output disposition | ordinary wall time | resource | historical actionable catches |",
        "|---:|---|:---:|:---:|:---:|---|---|---|---|---|---|",
    ]
    for gate in gates:
        row = rows[gate["id"]]
        inputs = ", ".join(sorted(gate.get("inputs", {}))) or "none"
        prerequisites = ", ".join(f"`{item}`" for item in row["prerequisites"]) or "—"
        catches = "; ".join(row["historical_catches"]) or "none known"
        command = command_text(gate).replace("|", "\\|")
        lines.append(
            f"| {gate['order']} | `{command}` | {mark(row['work'], 'candidate-positive')} | "
            f"{mark(row['work'], 'static-corpus')} | {mark(row['work'], 'harness-self-test')} | "
            f"{prerequisites} | {inputs} | {row.get('material_identity', 'not expensive')} | {times[command_text(gate)]} | "
            f"{row['resource_class']} | {catches} |"
        )
    lines += [
        "",
        "## Population reconciliation",
        "",
        "- Five launch composite rows retain their static halves in catalogue order and",
        "  add semantic halves at positions 56–60: "
        + ", ".join(f"`{item}`" for item in economy["split_families"]) + ".",
        "- Four gates landed after the launch inventory: the cheap BeaconDeposit assurance",
        "  row runs early at position 3, while the deployment control at position 44 uses exact",
        "  evaluator stdout and authority as a material-output certificate. Its positive and",
        "  mutation checks are unchanged, but proof-only movement with identical emitted evidence",
        "  does not rerun the EELS/Jaune body. The PRORATA WETH vault artifact row at position 61",
        "  binds its new family-owned runtime, ABI and compile witness; the exact-call boundary",
        "  row at position 62 binds the downstream composition, effects and source staging.",
        "  The final population is therefore 53 + 5 + 4 = 62; no required content was dropped.",
        "- CI makes the same five splits and adds the cheap assurance row, so its registered",
        "  command population moves from 34 to 40. The deployment control remains a local",
        "  merge-candidate row. The prerequisite column also records nested launch composition",
        "  now represented by runner-enforced dependencies that consume exact earlier green",
        "  evidence.",
        "- A catalogue timing cell is retained as published evidence, not relabelled as a new",
        "  measurement. Exact serialized per-row measurements will be imported only from a",
        "  green fresh candidate manifest.",
        "- Empty historical-catch cells mean no catch was found in the reviewed Plans history;",
        "  they do not claim the gate has never caught a defect.",
        "",
    ]
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args(argv)
    if arguments.write == arguments.check:
        parser.error("choose exactly one of --write or --check")
    try:
        rendered = render()
    except EconomyError as error:
        print(f"REGRESSION — gate economy inventory: {error}", file=sys.stderr)
        return 1
    if arguments.write:
        OUTPUT.write_text(rendered, encoding="utf-8")
        print(f"OK — gate economy inventory: wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else None
    if current != rendered:
        print("REGRESSION — gate economy inventory: generated output is stale", file=sys.stderr)
        return 1
    print(f"OK — gate economy inventory: {len(validated()[0])} rows reconcile")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
