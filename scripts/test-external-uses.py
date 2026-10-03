#!/usr/bin/env python3
"""Focused falsifiers for native reference identity and ownership joins."""
import copy
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch
from types import SimpleNamespace

import external_uses as uses
import leaf_audit


def census():
    population = [
        {"raw_name": "Blanc.method", "name": "Blanc.method", "module": "Blanc.A",
         "fp": "1" * 16, "private": False},
        {"raw_name": "_private.A.0.same", "name": "same", "module": "Blanc.A",
         "fp": "2" * 16, "private": True},
        {"raw_name": "_private.B.0.same", "name": "same", "module": "Blanc.B",
         "fp": "2" * 16, "private": True},
    ]
    constants = [{"name": r["raw_name"], "module": r["module"], "fp": r["fp"],
                  "owner": r["raw_name"], "owner_external": False, "dependencies": []}
                 for r in population]
    constants += [
        {"name": "Blanc.method.eq_1", "module": "Blanc.A", "fp": "3" * 16,
         "owner": "Blanc.method", "owner_external": False, "dependencies": []},
        {"name": "_orphan", "module": "Blanc.A", "fp": "4" * 16, "owner": None,
         "owner_external": False, "dependencies": ["Blanc.method.eq_1", "_orphan"]},
        {"name": "Jaune.external.eq_1", "module": "Blanc.A", "fp": "5" * 16,
         "owner": "Jaune.external", "owner_external": True, "dependencies": []},
    ]
    return {"population": 3, "population_declarations": population,
            "external_constants": constants}


def document(row):
    return {"resolved_uses": [{"constant": {k: row[k] for k in ("name", "module", "fp")}}],
            "declaration_uses": []}


class NativeReferences(unittest.TestCase):
    def test_private_identity(self):
        data = census()
        result = uses.resolve_references(data, {"consumer.lean": document(data["external_constants"][1])})
        self.assertEqual(result, {("Blanc.A", "same", "2" * 16): ["consumer.lean"]})

    def test_ownership_and_orphan_cycle(self):
        data = census()
        for i in (0, 3, 4):
            result = uses.resolve_references(data, {"consumer.lean": document(data["external_constants"][i])})
            self.assertEqual(result, {("Blanc.A", "Blanc.method", "1" * 16): ["consumer.lean"]})

    def test_dependency_owner_outside_population(self):
        data = census()
        self.assertEqual(uses.resolve_references(data, {"c.lean": document(data["external_constants"][5])}), {})

    def test_ambiguous_private_alias_fails(self):
        data = census()
        data["population_declarations"][2]["module"] = "Blanc.A"
        data["external_constants"][2]["module"] = "Blanc.A"
        with self.assertRaises(uses.ExternalUseError):
            uses.reference_index(data)

    def test_unreadable_lean_is_not_silently_omitted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            source = root / "scripts/bad.lean"
            listed = SimpleNamespace(returncode=0, stdout=b"scripts/bad.lean\0", stderr=b"")
            for content in (b"\0", b"\xff"):
                source.write_bytes(content)
                with patch.object(leaf_audit.subprocess, "run", return_value=listed):
                    with self.assertRaises(leaf_audit.LeafAuditError):
                        leaf_audit.tracked_external_sources(root)

    def test_comments_imports_and_strings_do_not_supply_references(self):
        self.assertEqual(uses.resolve_references(census(), {"c.lean": {
            "resolved_uses": [], "declaration_uses": []}}), {})

    def test_missing_and_stale_reference_fail(self):
        for key, replacement in (("name", "missing"), ("module", "Blanc.Other"), ("fp", "0" * 16)):
            data = census()
            doc = document(data["external_constants"][0])
            doc["resolved_uses"][0]["constant"][key] = replacement
            with self.assertRaises(uses.ExternalUseError):
                uses.resolve_references(data, {"c.lean": doc})

    def test_truncated_graph_fails(self):
        for mutation in (
            lambda d: d.pop("external_constants"),
            lambda d: d["external_constants"].pop(0),
            lambda d: d["external_constants"][3].update(owner="missing"),
            lambda d: d["external_constants"][4].update(dependencies=["missing"]),
            lambda d: d["population_declarations"].pop(),
            lambda d: d["external_constants"].append(copy.deepcopy(d["external_constants"][0])),
        ):
            data = census()
            mutation(data)
            with self.assertRaises(uses.ExternalUseError):
                uses.reference_index(data)

    def test_incomplete_document_fails(self):
        for doc in ({}, {"resolved_uses": []}, {"resolved_uses": "bad", "declaration_uses": []}):
            with self.assertRaises(uses.ExternalUseError):
                uses.resolve_references(census(), {"c.lean": doc})

    def test_source_and_setup_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            source, setup = Path(tmp) / "source.lean", Path(tmp) / "setup.json"
            source.write_bytes(b"import Lean\n")
            setup.write_bytes(b"{}\n")
            doc = {"schema": 1, "original_path": str(source), "buffer_path": str(source),
                "setup_path": str(setup), "source_sha256": uses.sha(source.read_bytes()),
                "original_sha256": uses.sha(source.read_bytes()), "setup_sha256": uses.sha(setup.read_bytes())}
            uses.check_document(doc, source, setup, source.read_bytes())
            setup.write_bytes(b"[]\n")
            with self.assertRaises(uses.ExternalUseError):
                uses.check_document(doc, source, setup, source.read_bytes())
            setup.write_bytes(b"{}\n")
            source.write_bytes(b"import Blanc\n")
            with self.assertRaises(uses.ExternalUseError):
                uses.check_document(doc, source, setup, b"import Lean\n")


if __name__ == "__main__":
    unittest.main()
