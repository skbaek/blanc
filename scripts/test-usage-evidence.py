#!/usr/bin/env python3
"""Boundary controls only; actual Lean resolution is a separate runtime obligation."""
import copy
import hashlib
import tempfile
import unittest
from pathlib import Path

from static_usage_consumers import StaticConsumerError, literal_requests
from usage_evidence import UsageEvidenceError, declaration_index, reconcile_historical, validate_and_index


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def decl(name, display=None, module="Blanc.X", private=False, owner=None, kind="theorem"):
    return {"name": name, "display_name": display or name, "module": module,
            "private": private, "theorem": kind == "theorem", "kind": kind,
            "owner": owner or name}


class Controls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Blanc").mkdir()
        (self.root / "scripts").mkdir()
        self.source = b"theorem used : True := by simp only [leaf]\n#check leaf\n"
        self.consumer = b'CHECKS = {"Blanc.leaf"}\nINERT = "Blanc.inert"\ndef require_names():\n    return CHECKS\n'
        (self.root / "Blanc/X.lean").write_bytes(self.source)
        (self.root / "scripts/check.py").write_bytes(self.consumer)
        (self.root / "scripts/setup.json").write_bytes(b'{}')
        self.sources = {"Blanc/X.lean": sha(self.source)}
        self.bindings = {"scripts/setup.json": sha(b'{}'), "scripts/check.py": sha(self.consumer)}
        self.requests = literal_requests("scripts/check.py", self.consumer, {
            "binding": "CHECKS", "function": "require_names", "target_source": "Blanc/X.lean",
            "kind": "checked-name", "rationale": "fixture checked-name positive requirement"})
        self.receipt = {"schema": "blanc-resolved-usage-v1", "source_hashes": self.sources,
            "bindings": self.bindings, "errors": [], "sorry": False, "unresolved": [],
            "declarations": [decl("Blanc.leaf"), decl("Blanc.used"),
                decl("_private.Blanc.X.0.Blanc.p", "Blanc.p", private=True)],
            "sources": [{"path": "Blanc/X.lean", "commands": [
                {"id": "c0", "span": [0, 41], "mode": "elaborated"},
                {"id": "c1", "span": [41, len(self.source)], "mode": "elaborated"}],
                "references": [{"command": "c0", "span": [35, 39], "resolved_name": "Blanc.leaf",
                    "kind": "rewrite-positive", "parent": "Blanc.used"}]}],
            "static_resolutions": [{"id": self.requests[0]["id"], "resolved_name": "Blanc.leaf",
                "requested_name": "Blanc.leaf", "target_source": "Blanc/X.lean"}]}

    def run_receipt(self, receipt=None):
        return validate_and_index(self.root, receipt or self.receipt,
                                  self.sources, self.bindings, self.requests)

    def test_green_transport(self):
        result = self.run_receipt()
        self.assertEqual(set(result["uses"]), {"Blanc.leaf"})
        self.assertEqual(len(result["uses"]["Blanc.leaf"]), 2)

    def test_biting_receipt_controls(self):
        mutations = {
            "sorry": lambda r: r.update(sorry=True),
            "error": lambda r: r.update(errors=["failed"]),
            "unresolved": lambda r: r.update(unresolved=["macro quote"]),
            "omitted source": lambda r: r.update(sources=[]),
            "duplicate source": lambda r: r["sources"].append(copy.deepcopy(r["sources"][0])),
            "omitted import binding": lambda r: r.update(bindings={}),
            "unknown target": lambda r: r["sources"][0]["references"][0].update(resolved_name="guess"),
            "unresolved source role": lambda r: r["sources"][0]["commands"][0].update(mode="unknown"),
            "unbound adapter": lambda r: r["sources"][0]["commands"][0].update(mode="reference-adapter"),
            "outside command": lambda r: r["sources"][0]["references"][0].update(span=[42, 46]),
            "boolean offset": lambda r: r["sources"][0]["references"][0].update(span=[True, 4]),
            "unknown reference kind": lambda r: r["sources"][0]["references"][0].update(kind="lexical"),
            "missing parent": lambda r: r["sources"][0]["references"][0].pop("parent"),
            "unknown parent": lambda r: r["sources"][0]["references"][0].update(parent="missing"),
            "unanswered static request": lambda r: r.update(static_resolutions=[]),
            "wrong static name": lambda r: r["static_resolutions"][0].update(requested_name="Blanc.inert"),
            "missing declaration kind": lambda r: r["declarations"][0].pop("kind"),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                candidate = copy.deepcopy(self.receipt)
                mutate(candidate)
                with self.assertRaises(UsageEvidenceError):
                    self.run_receipt(candidate)
                self.assertEqual(candidate != self.receipt, True)

    def test_current_bytes_bite(self):
        original = (self.root / "Blanc/X.lean").read_bytes()
        (self.root / "Blanc/X.lean").write_bytes(original + b"-- drift\n")
        with self.assertRaisesRegex(UsageEvidenceError, "stale candidate"):
            self.run_receipt()
        (self.root / "Blanc/X.lean").write_bytes(original)
        self.assertEqual(sha(original), self.sources["Blanc/X.lean"])  # restored bytes prove green

    def test_self_reference_and_negative_polarity(self):
        self.receipt["static_resolutions"] = []
        self.requests = []
        reference = self.receipt["sources"][0]["references"][0]
        reference.update(parent="Blanc.leaf")
        self.assertEqual(self.run_receipt()["uses"], {})
        reference.update(parent=None, kind="rewrite-remove")
        self.assertEqual(self.run_receipt()["uses"]["Blanc.leaf"][0]["kind"], "rewrite-remove")

    def test_private_aliases_keep_all_original_rows(self):
        historic = decl("_private.Blanc.X.0.Blanc.p", "Blanc.p", private=True)
        moved = decl("_private.Blanc.X.7.Blanc.p", "Blanc.p", private=True)
        current = declaration_index([moved])
        keys = [historic["name"], "Blanc.p [private, Blanc.X]"]
        rows = reconcile_historical(keys, dict.fromkeys(keys, historic), current, {moved["name"]})
        self.assertEqual(len(rows), 2)
        self.assertEqual({r["current_name"] for r in rows}, {moved["name"]})
        self.assertEqual({r["status"] for r in rows}, {"used"})
        with self.assertRaisesRegex(UsageEvidenceError, "ambiguous"):
            reconcile_historical(keys, dict.fromkeys(keys, historic),
                declaration_index([moved, decl("other", "Blanc.p", private=True)]), set())
        with self.assertRaisesRegex(UsageEvidenceError, "accounting"):
            reconcile_historical(keys, {keys[0]: historic}, current, set())

    def test_static_request_excludes_comments_and_inert_strings(self):
        self.assertEqual([r["name"] for r in self.requests], ["Blanc.leaf"])
        descriptor = {"binding": "CHECKS", "function": "require_names", "target_source": "Blanc/X.lean",
                      "kind": "checked-name", "rationale": "control"}
        for raw in (b'CHECKS = build()\ndef require_names(): return CHECKS\n',
                    b'CHECKS = {"x", "x"}\ndef require_names(): return CHECKS\n',
                    b'CHECKS = {"x"}\ndef require_names(): return "CHECKS"\n',
                    b'CHECKS = {"x"}\ndef require_names(CHECKS): return CHECKS\n'):
            with self.subTest(raw=raw), self.assertRaises(StaticConsumerError):
                literal_requests("scripts/check.py", raw, descriptor)

    def test_shared_raw_path_language_bites(self):
        bad_paths = ["Blanc//X.lean", "Blanc\\X.lean", "blanc/X.lean", "Blanc/e\u0301.lean"]
        for bad in bad_paths:
            with self.subTest(path=bad):
                receipt = copy.deepcopy(self.receipt)
                expected = {bad: self.sources["Blanc/X.lean"]}
                receipt["source_hashes"] = expected
                receipt["sources"][0]["path"] = bad
                with self.assertRaises(UsageEvidenceError):
                    validate_and_index(self.root, receipt, expected, self.bindings, self.requests)
        descriptor = {"binding": "CHECKS", "function": "require_names", "target_source": "Blanc/Bad-name.lean",
                      "kind": "checked-name", "rationale": "control"}
        with self.assertRaises(StaticConsumerError):
            literal_requests("scripts/check.py", self.consumer, descriptor)
        for bad in ["scripts//check.py", "scripts\\check.py", "scripts/e\u0301.py"]:
            with self.subTest(path=bad), self.assertRaises(StaticConsumerError):
                literal_requests(bad, self.consumer, {**descriptor, "target_source": "scripts/Fixture.lean"})

    def test_internal_symlink_alias_bites(self):
        local = self.root / "Blanc/X.lean"
        target = self.root / "Blanc/Real.lean"
        local.rename(target)
        local.symlink_to(target)
        with self.assertRaisesRegex(UsageEvidenceError, "symbolic-link"):
            self.run_receipt()

    def test_external_symlink_bites(self):
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / "foreign.lean"
            target.write_bytes(self.source)
            local = self.root / "Blanc/X.lean"
            local.unlink()
            local.symlink_to(target)
            with self.assertRaisesRegex(UsageEvidenceError, "unsafe/unreadable"):
                self.run_receipt()


if __name__ == "__main__":
    unittest.main(verbosity=2)
