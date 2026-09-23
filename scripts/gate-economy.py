#!/usr/bin/env python3
"""Generate and check Blanc's economic inventory without executing gates.

Every row carries a measured cost (evidence economy rule 4).  That cost is
never typed by hand: `--import-costs` reads the selective runner's shared
evidence ledger -- the same-host store `check-gates.sh` writes a record to
for every fresh green cacheable row, each with its measured `duration_s` --
and freezes what it found into `scripts/gate-measured-costs.json`, which the
rendered inventory then quotes.  `--check` holds the committed document to
the committed import; it never reads the host ledger, so it is the same
verdict on every host and in CI.  Re-import when the ledger has newer
evidence; the import's UTC and record counts say how current it is.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import statistics
import sys
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "scripts/gate-registry.json"
ECONOMY = ROOT / "scripts/gate-economy.json"
COSTS = ROOT / "scripts/gate-measured-costs.json"
CATALOGUE = ROOT / "scripts/GATES.md"
OUTPUT = ROOT / "docs/GATE_ECONOMY.md"
COSTS_SCHEMA = 1
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


def load_gate_cache() -> Any:
    """The runner module, for its ledger reader; never leaves bytecode behind."""

    path = ROOT / "scripts/gate-cache.py"
    if not path.is_file():
        raise EconomyError("gate-cache.py is absent; the evidence ledger cannot be read")
    scripts = str(path.parent)
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec = importlib.util.spec_from_file_location("blanc_gate_cache_for_economy", path)
        if spec is None or spec.loader is None:
            raise EconomyError("cannot load gate-cache.py")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    return module


def import_costs() -> dict[str, Any]:
    """Freeze each gate's measured cost from the shared evidence ledger.

    Per gate: how many retained records carry a duration, their median, and
    the newest record's duration, commit and UTC.  The ledger's stable-host
    token is not copied; the source is named by its path shape only.
    """

    gc = load_gate_cache()
    cache, reason = gc.read_active_cache(ROOT)
    if reason:
        raise EconomyError(f"evidence ledger unavailable: {reason}")
    rows: dict[str, dict[str, Any]] = {}
    for identifier, records in cache["gates"].items():
        timed = [
            record for record in records
            if isinstance(record.get("provenance", {}).get("duration_s"), (int, float))
        ]
        if not timed:
            continue
        latest = max(timed, key=lambda record: record["provenance"].get("recorded_utc", ""))
        rows[identifier] = {
            "records": len(timed),
            "median_s": round(statistics.median(r["provenance"]["duration_s"] for r in timed), 3),
            "latest_s": round(latest["provenance"]["duration_s"], 3),
            "latest_commit": str(latest["provenance"].get("commit", ""))[:12],
            "latest_utc": str(latest["provenance"].get("recorded_utc", "")),
        }
    return {
        "schema": COSTS_SCHEMA,
        "imported_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": (
            f"{gc.SHARED_STATE_RELATIVE}/{gc.EVIDENCE_FILENAME_PREFIX}<stable-host>.json "
            "below the Git common directory; provenance.duration_s of each retained "
            "green record"
        ),
        "rows": dict(sorted(rows.items())),
    }


def load_costs(gate_ids: set[str]) -> dict[str, Any]:
    costs = load(COSTS)
    if not isinstance(costs, dict) or costs.get("schema") != COSTS_SCHEMA:
        raise EconomyError("measured-cost import schema is not 1")
    if not isinstance(costs.get("imported_utc"), str) or not isinstance(costs.get("rows"), dict):
        raise EconomyError("measured-cost import is malformed")
    # A row for a gate that no longer exists is stale evidence, not a fault:
    # a trim that renames or removes a row must not force a host-ledger
    # re-import.  Stale rows are ignored and named in the rendered document.
    costs["stale"] = sorted(identifier for identifier in costs["rows"] if identifier not in gate_ids)
    for identifier, row in costs["rows"].items():
        if identifier not in gate_ids:
            continue
        if (
            not isinstance(row, dict)
            or set(row) != {"records", "median_s", "latest_s", "latest_commit", "latest_utc"}
            or not isinstance(row["records"], int) or row["records"] <= 0
            or not all(isinstance(row[key], (int, float)) and row[key] >= 0
                       for key in ("median_s", "latest_s"))
            or not isinstance(row["latest_commit"], str)
            or not isinstance(row["latest_utc"], str)
        ):
            raise EconomyError(f"measured-cost row {identifier} is malformed")
    return costs


def measured_cost_cell(costs: dict[str, Any], identifier: str) -> str:
    row = costs["rows"].get(identifier)
    if row is None:
        return "no ledger record"
    return (
        f"median {row['median_s']:.1f} s over {row['records']} record(s); "
        f"latest {row['latest_s']:.1f} s at {row['latest_commit'] or '?'} "
        f"({row['latest_utc'][:10] or '?'})"
    )


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


def validated() -> tuple[
    list[dict[str, Any]], dict[str, dict[str, Any]], dict[str, str], dict[str, Any], dict[str, Any]
]:
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
        "final_ci_population": 41,
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
            "keccak-rate-boundary",
            "drip-stack-certificate-data",
            "prorata-weth-vault-artifact",
            "prorata-weth-vault-boundary",
            "prorata-weth-vault-reference",
            "prorata-weth-vault-oracle",
            "prorata-weth-vault-differential",
            "prorata-weth-vault-oracle-self-test",
            "prorata-weth-vault-differential-self-test",
            "prorata-weth-vault-reference-self-test",
            "drip-evidence",
            "drip-current-mainnet",
            "lido-twg-pinned-target-current-mainnet",
            "recipe-dispatch-controls",
            "elab-migration-comparison-controls",
            # Evidence economy, batch 1 (2026-09-23): harness self-tests split
            # out of their main rows; each depends on its main row.
            "extraction-ownership-self-test",
            "execution-occurrence-self-test",
            "cycle-write-free-self-test",
            "transient-settlement-self-test",
            "lido-deployment-self-test",
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
    costs = load_costs(gate_ids)
    return gates, rows, times, economy, costs


def mark(classes: list[str], name: str) -> str:
    return "yes" if name in classes else "—"


def render() -> str:
    gates, rows, times, economy, costs = validated()
    measured = sum(1 for gate in gates if gate["id"] in costs["rows"])
    lines = [
        "# Blanc gate economic inventory",
        "",
        "Generated by `scripts/gate-economy.py` from the launch-current gate registry,",
        "catalogue, `scripts/gate-economy.json` and the ledger import",
        "`scripts/gate-measured-costs.json`. Do not edit by hand.",
        "",
        f"Launch population at `{economy['launch_catalogue_commit'][:12]}`: "
        f"**{economy['launch_population']}** catalogue rows and "
        f"**{economy['launch_ci_population']}** CI commands.",
        f"Final population: **{len(gates)}** catalogue rows and "
        f"**{economy['final_ci_population']}** CI commands. CI reconciliation is also audited by",
        "`scripts/check-gates.sh --audit`. The catalogue time cell is the catalogue's own latest",
        "host-local observation; `unmeasured` is preserved honestly and no parallel sums are made.",
        f"The measured-cost cell is imported from the selective runner's evidence ledger",
        f"(`--import-costs`, last imported {costs['imported_utc']}; {measured} of {len(gates)} rows",
        "have a record): the median and newest `duration_s` of the retained green records,",
        "never typed by hand. `no ledger record` means the row has not yet earned a shared",
        "record on this host, so its only time is the catalogue cell.",
        *(
            [
                f"Ignored as stale (imported for gates no longer registered): "
                + ", ".join(f"`{item}`" for item in costs["stale"]) + "."
            ]
            if costs.get("stale")
            else []
        ),
        "",
        "| # | gate | positive | static/corpus | harness/self-test | prerequisites | mutable input classes | material-output disposition | catalogue time cell | measured cost (ledger) | resource | historical actionable catches |",
        "|---:|---|:---:|:---:|:---:|---|---|---|---|---|---|---|",
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
            f"{measured_cost_cell(costs, gate['id'])} | "
            f"{row['resource_class']} | {catches} |"
        )
    lines += [
        "",
        "## Population reconciliation",
        "",
        "- Five launch composite rows retain their static halves in catalogue order and",
        "  add semantic halves at positions 56–60: "
        + ", ".join(f"`{item}`" for item in economy["split_families"]) + ".",
          "- Eighteen gates landed after the launch inventory: BeaconDeposit assurance runs early;",
          "  BeaconDeposit deployment and WETH10 current-mainnet retain their reviewed output-aware",
          "  boundaries; Keccak rate-boundary is a static row; the local-draft DRIP stack",
          "  certificate data row runs deterministic source comparison and corruption controls;",
          "  target-independent DRIP evidence and the isolated DRIP current-mainnet consumer",
          "  follow it; the PRORATA WETH vault artifact row binds its new family-owned runtime,",
          "  ABI and compile witness; and the exact-call boundary row binds the downstream",
          "  composition, effects and source staging. The PRORATA WETH vault's six evidence",
          "  rows run early among the cheap static gates: the vendored-reference identity,",
          "  the independent oracle, the two-runtime differential, and their three harness",
          "  self-tests; and the TWG pinned-target row replays composed and family pause/query",
          "  arms under literal BPO2 with exact compiler-owned artifacts as direct inputs;",
          "  and the isolated recipe-dispatch controls row elaborates the committed suggestion",
          "  harness alone, so a mutation of the production dispatch has a green baseline that",
          "  the coupled axiom-audit row cannot give it. The elaboration-migration comparison",
          "  control is a disposable-fixture reader test that neither adopts nor initializes",
          "  a normal elaboration baseline.",
          "  The final population is therefore 53 + 5 + 18 = 76; no required content was dropped.",
          "- CI makes the same five splits and adds the cheap assurance, WETH10 current-mainnet",
          "  and DRIP rows, so its registered command population moves from 34 to 41. Deployment,",
          "  the DRIP certificate, and the TWG pinned-target replay remain local merge-candidate",
          "  rows. The prerequisite column also records nested launch composition",
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate docs/GATE_ECONOMY.md")
    parser.add_argument("--check", action="store_true", help="hold the document to its generator")
    parser.add_argument(
        "--import-costs", action="store_true",
        help="freeze measured costs from this host's evidence ledger, then regenerate",
    )
    arguments = parser.parse_args(argv)
    if sum((arguments.write, arguments.check, arguments.import_costs)) != 1:
        parser.error("choose exactly one of --write, --check or --import-costs")
    try:
        if arguments.import_costs:
            costs = import_costs()
            COSTS.write_text(json.dumps(costs, indent=1) + "\n", encoding="utf-8")
            print(
                f"OK — gate economy inventory: imported measured costs for "
                f"{len(costs['rows'])} gate(s) into {COSTS.relative_to(ROOT)}"
            )
        rendered = render()
    except EconomyError as error:
        print(f"REGRESSION — gate economy inventory: {error}", file=sys.stderr)
        return 1
    if arguments.write or arguments.import_costs:
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
