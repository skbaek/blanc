#!/usr/bin/env python3
"""Static controls for the single-authority economic inventory."""

from __future__ import annotations

import copy
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from typing import Optional


SPEC = importlib.util.spec_from_file_location(
    "gate_economy", Path(__file__).with_name("gate-economy.py")
)
assert SPEC is not None and SPEC.loader is not None
economy = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(economy)


def gate(identifier: str, order: int, material: bool = False) -> dict:
    return {
        "id": identifier,
        "order": order,
        "command": [f"scripts/check-{identifier}.sh"],
        "inputs": {"material_output": {"producer": "example"}} if material else {},
    }


def row(identifier: str, material: Optional[str] = None) -> dict:
    result = {
        "id": identifier,
        "work": ["static-corpus"],
        "resource_class": "light",
        "prerequisites": [],
        "historical_catches": [],
    }
    if material is not None:
        result["material_identity"] = material
    return result


class GateEconomyControls(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "scripts").mkdir()
        (self.root / ".github/workflows").mkdir(parents=True)
        self.previous = (economy.ROOT, economy.REGISTRY, economy.ECONOMY,
                         economy.COSTS, economy.CATALOGUE, economy.OUTPUT)
        economy.ROOT = self.root
        economy.REGISTRY = self.root / "scripts/gate-registry.json"
        economy.ECONOMY = self.root / "scripts/gate-economy.json"
        economy.COSTS = self.root / "scripts/gate-measured-costs.json"
        economy.CATALOGUE = self.root / "scripts/GATES.md"
        economy.OUTPUT = self.root / "docs/GATE_ECONOMY.md"
        self.addCleanup(self.restore)
        self.registry = {
            "schema": 1,
            "economy_inventory": "scripts/gate-economy.json",
            "gates": [gate("a", 1), gate("b", 2)],
        }
        self.inventory = {"schema": 1, "rows": [row("a"), row("b")]}
        self.write()

    def restore(self) -> None:
        (economy.ROOT, economy.REGISTRY, economy.ECONOMY,
         economy.COSTS, economy.CATALOGUE, economy.OUTPUT) = self.previous

    def write(self) -> None:
        economy.REGISTRY.write_text(json.dumps(self.registry))
        economy.ECONOMY.write_text(json.dumps(self.inventory))
        economy.COSTS.write_text(json.dumps({
            "schema": 1, "imported_utc": "2026-09-24T00:00:00Z", "rows": {}
        }))
        economy.CATALOGUE.write_text("\n".join(
            f"| `{item['command'][0]}` | checked | ~1 s |"
            for item in self.registry["gates"] if item.get("catalogued", True)
        ))
        (self.root / ".github/workflows/ci.yml").write_text(
            "steps:\n  - run: scripts/check-a.sh\n"
        )

    def rejects(self, phrase: str) -> None:
        self.write()
        with self.assertRaisesRegex(economy.EconomyError, phrase):
            economy.validated()

    def test_live_addition_needs_only_registry_metadata_and_catalogue(self) -> None:
        self.registry["gates"].append(gate("c", 3))
        self.inventory["rows"].append(row("c"))
        self.write()
        gates, _, _, _, _ = economy.validated()
        self.assertEqual([item["id"] for item in gates], ["a", "b", "c"])
        rendered = economy.render()
        self.assertIn("Current population: **3** catalogue rows and **1** CI commands", rendered)
        self.assertNotIn("Final population:", rendered)

    def test_missing_and_extra_metadata_fail(self) -> None:
        self.inventory["rows"].pop()
        self.rejects("missing=\\['b'\\]")
        self.inventory["rows"].append(row("b"))
        self.inventory["rows"].append(row("orphan"))
        self.rejects("extra=\\['orphan'\\]")

    def test_duplicate_ids_fail_on_both_sides(self) -> None:
        self.inventory["rows"].append(copy.deepcopy(self.inventory["rows"][0]))
        self.rejects("duplicate economic row a")
        self.inventory["rows"].pop()
        self.registry["gates"].append(gate("a", 3))
        self.rejects("gate registry repeats an id")

    def test_classes_prerequisites_and_material_agreement_fail(self) -> None:
        self.inventory["rows"][0]["work"] = ["unknown"]
        self.rejects("invalid work classes")
        self.inventory["rows"][0]["work"] = ["static-corpus"]
        self.inventory["rows"][0]["resource_class"] = "unknown"
        self.rejects("invalid resource class")
        self.inventory["rows"][0]["resource_class"] = "light"
        self.inventory["rows"][0]["prerequisites"] = ["missing"]
        self.rejects("unknown prerequisites")
        self.inventory["rows"][0]["prerequisites"] = []
        self.registry["gates"][0]["inputs"]["material_output"] = {"producer": "example"}
        self.rejects("disagree on material-output certification")
        self.inventory["rows"][0]["material_identity"] = "output-aware: example"
        self.write()
        economy.validated()

    def test_catalogue_coverage_and_obsolete_live_list_fail(self) -> None:
        self.registry["gates"][1]["catalogued"] = False
        self.rejects("catalogue timing cells missing")
        self.registry["gates"][1].pop("catalogued")
        self.inventory["post_launch_gates"] = ["a"]
        self.rejects("economic inventory schema is not 1")


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(GateEconomyControls)
    result = unittest.TextTestRunner().run(suite)
    if result.testsRun <= 0 or not result.wasSuccessful():
        raise SystemExit(1)
    print(f"OK — gate economy controls: {result.testsRun} tests")
