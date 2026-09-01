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


def validated() -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]], dict[str, str]]:
    registry = load(REGISTRY)
    economy = load(ECONOMY)
    if registry.get("schema") != 1 or not isinstance(registry.get("gates"), list):
        raise EconomyError("gate registry schema is not 1")
    if registry.get("economy_inventory") != "scripts/gate-economy.json":
        raise EconomyError("gate registry does not require its economic inventory")
    if economy.get("schema") != 1 or not isinstance(economy.get("rows"), list):
        raise EconomyError("economic inventory schema is not 1")
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
    times = catalogue_times()
    missing_times = [command_text(gate) for gate in gates if command_text(gate) not in times]
    if missing_times:
        raise EconomyError(f"catalogue timing cells missing for {missing_times}")
    return gates, rows, times


def mark(classes: list[str], name: str) -> str:
    return "yes" if name in classes else "—"


def render() -> str:
    gates, rows, times = validated()
    lines = [
        "# Blanc gate economic inventory",
        "",
        "Generated by `scripts/gate-economy.py` from the launch-current gate registry,",
        "catalogue, and `scripts/gate-economy.json`. Do not edit by hand.",
        "",
        f"Population: **{len(gates)}** catalogue rows. CI population is audited separately by",
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
        "## Launch interpretation",
        "",
        "- The prerequisite column records the launch and final logical composition;",
        "  final catalogue dependencies are runner-enforced and consume exact green evidence.",
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
