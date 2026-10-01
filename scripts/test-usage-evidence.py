#!/usr/bin/env python3
"""Boundary controls only; actual Lean resolution is a separate runtime obligation."""
import copy
import hashlib
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from static_usage_consumers import StaticConsumerError, literal_requests
from usage_evidence import (UsageEvidenceError, capture_native_environment, declaration_index,
                            reconcile_historical, validate_and_index, validate_native_and_index,
                            REQUEST_DIGEST_SCHEME)


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


class NativeControls(unittest.TestCase):
    """All declarations/setup/import artifacts are mocks: no Lean is executed."""
    def setUp(self):
        Controls.setUp(self)
        self.root = self.root.resolve()
        outside = tempfile.TemporaryDirectory()
        self.addCleanup(outside.cleanup)
        self.outside = Path(outside.name).resolve()
        elan = self.outside / "elan"
        self.patch_environment = patch.dict(os.environ, {"ELAN_HOME": str(elan)})
        self.patch_environment.start()
        self.addCleanup(self.patch_environment.stop)
        self.executable = elan / "toolchains/mock--lean---v4.34.0/bin/lean"
        self.executable.parent.mkdir(parents=True)
        self.executable.write_bytes(b"mock compiler bytes, never executed")
        self.import_artifact = self.outside / "External.olean"
        self.import_artifact.write_bytes(b"mock external compiled import")
        (self.root / ".lake/build/bin").mkdir(parents=True)
        (self.root / ".lake/build/bin/simpCollector").write_bytes(b"mock collector, never executed")
        for path, raw in {"lean-toolchain": b"mock/lean:v4.34.0\n", "lakefile.lean": b"import Lake\n",
                          "lake-manifest.json": b"{}", "scripts/SimpCollector.lean": b"import Lean\n"}.items():
            (self.root / path).write_bytes(raw)
        helper = Path(__file__).with_name("run-simp-migration.py").read_bytes()
        (self.root / "scripts/run-simp-migration.py").write_bytes(helper)
        self.bindings["scripts/run-simp-migration.py"] = sha(helper)
        self.source = b"theorem leaf : True := by trivial\ntheorem used : True := by simp only [leaf]\n#check leaf\n"
        fixture = b"theorem leaf : True := by trivial\n"
        (self.root / "Blanc/X.lean").write_bytes(self.source)
        (self.root / "scripts/Fixture.lean").write_bytes(fixture)
        (self.root / "scripts/Imports.lean").write_bytes(b"import Blanc.X\n")
        self.sources = {"Blanc/X.lean": sha(self.source), "scripts/Fixture.lean": sha(fixture),
                        "scripts/Imports.lean": sha(b"import Blanc.X\n")}
        setup = {"name": "Blanc.X", "importArts": {"Mock": [[str(self.import_artifact)]]}}
        self.environments = {"production-env": capture_native_environment(self.root, setup),
                             "fixture-env": capture_native_environment(self.root, {**setup, "name": "Fixture"})}
        first = self.source.index(b"\n") + 1
        second = self.source.index(b"\n", first) + 1
        self.roles = [
            {"id": "production", "path": "Blanc/X.lean", "role": "production", "environment": "production-env",
             "coverage": "commands", "commands": [
                 {"id": "leaf", "span": [0, first], "mode": "elaborated"},
                 {"id": "used", "span": [first, second], "mode": "elaborated"},
                 {"id": "check", "span": [second, len(self.source)], "mode": "elaborated"}]},
            {"id": "fixture", "path": "scripts/Fixture.lean", "role": "fixture", "environment": "fixture-env",
             "coverage": "commands", "commands": [{"id": "fixture-leaf", "span": [0, len(fixture)], "mode": "elaborated"}]},
            {"id": "imports", "path": "scripts/Imports.lean", "role": "verification", "environment": "production-env",
             "coverage": "import-only", "commands": []}]
        def native_decl(did, name, rid, span, module):
            role = next(r for r in self.roles if r["id"] == rid)
            return {**decl(name, module=module), "id": did, "owner": did,
                    "environment": role["environment"], "origin_role": rid,
                    "population": "production" if rid == "production" else "nonproduction",
                    "source": {"path": role["path"], "sha256": self.sources[role["path"]], "span": span},
                    "type_identity": {"scheme": "lean4.34-expr-hash64", "value": "0123456789abcdef"}}
        self.declarations = [native_decl("prod-leaf", "Blanc.leaf", "production", [0, first], "Blanc.X"),
                             native_decl("prod-used", "Blanc.used", "production", [first, second], "Blanc.X"),
                             native_decl("fixture-leaf", "Blanc.leaf", "fixture", [0, len(fixture)], "Fixture")]
        self.native_requests = [{"id": 1, "name_request": "leaf", "operation_kind": "checked-name",
            "owner_candidates": ["Blanc/X.lean", "scripts/Fixture.lean"], "resolution": "pending-native-exact-identity",
            "data_origin": {"path": "scripts/check.py", "sha256": sha(self.consumer), "line": 1, "end_line": 1},
            "check_operation": {"path": "scripts/check.py", "sha256": sha(self.consumer), "line": 3, "end_line": 4}}]
        self.visibility = [{"id": "production-" + c["id"], "role": "production", "command": c["id"],
                            "declarations": ["prod-leaf", "prod-used"]} for c in self.roles[0]["commands"]]
        self.visibility += [{"id": "fixture-view", "role": "fixture", "command": "fixture-leaf",
                             "declarations": ["fixture-leaf", "prod-used"]},
                            {"id": "imports-view", "role": "imports", "command": None,
                             "declarations": ["prod-leaf", "prod-used"]}]
        self.contexts = [{"id": 1, "context": "production", "visibility": "production-check", "declaration": "prod-leaf"}]
        request_sha = sha(json.dumps(self.native_requests[0], sort_keys=True,
                                    allow_nan=False, separators=(",", ":")).encode())
        self.provenance = [{"id": 1, "request_digest_scheme": REQUEST_DIGEST_SCHEME, "overlay_sha256": "a" * 64,
            "witness": {"original_request_id": 1, "original_request_sha256": request_sha,
                        "original_check_operation": self.native_requests[0]["check_operation"],
                        "original_owner_candidates": self.native_requests[0]["owner_candidates"], "name_request": "leaf",
                        "effective_check_operation": self.native_requests[0]["check_operation"],
                        "effective_owner_candidates": self.native_requests[0]["owner_candidates"]}}]
        provenance_sha = sha(json.dumps(self.provenance[0], sort_keys=True,
                                       allow_nan=False, separators=(",", ":")).encode())
        self.native_receipt = {"schema": "blanc-resolved-usage-v2", "source_hashes": self.sources,
            "bindings": self.bindings, "errors": [], "sorry": False, "unresolved": [],
            "environments": copy.deepcopy(self.environments), "visibility": copy.deepcopy(self.visibility),
            "declarations": copy.deepcopy(self.declarations),
            "roles": [{**copy.deepcopy(r), "references": []} for r in self.roles],
            "static_resolutions": [{"id": 1, "context": "production", "declaration": "prod-leaf",
                "visibility": "production-check", "request_sha256": request_sha,
                "request_digest_scheme": REQUEST_DIGEST_SCHEME, "provenance_sha256": provenance_sha}]}
        offset = self.source.index(b"[leaf]") + 1
        self.native_receipt["roles"][0]["references"] = [{"command": "used", "span": [offset, offset + 4],
            "declaration": "prod-leaf", "kind": "rewrite-positive", "parent": "prod-used", "visibility": "production-used"}]

    def run_native(self, receipt=None, **overrides):
        args = {"expected_sources": self.sources, "expected_bindings": self.bindings,
                "expected_roles": self.roles, "expected_declarations": self.declarations,
                "expected_environments": self.environments, "requests": self.native_requests,
                "expected_visibility": self.visibility, "static_contexts": self.contexts,
                "static_provenance": self.provenance, **overrides}
        return validate_native_and_index(self.root, self.native_receipt if receipt is None else receipt, **args)

    def test_green_v2_and_import_only(self):
        result = self.run_native()
        self.assertEqual(set(result["uses"]), {"prod-leaf"})
        self.assertEqual(len(result["uses"]["prod-leaf"]), 2)
        self.assertEqual(result["uses"]["prod-leaf"][1]["request"], self.native_requests[0])
        with self.assertRaisesRegex(UsageEvidenceError, "v1 is preparation"):
            self.run_native({**self.native_receipt, "schema": "blanc-resolved-usage-v1"})

    def test_native_receipt_controls_bite(self):
        mutations = {
            "omitted role": lambda r: r["roles"].pop(),
            "duplicate role": lambda r: r["roles"].append(copy.deepcopy(r["roles"][0])),
            "duplicated equal-length role": lambda r: r["roles"].__setitem__(1, copy.deepcopy(r["roles"][0])),
            "omitted command": lambda r: r["roles"][0]["commands"].pop(),
            "forged import-only": lambda r: r["roles"][0].update(coverage="import-only", commands=[]),
            "import-only references": lambda r: r["roles"][2]["references"].append(copy.deepcopy(r["roles"][0]["references"][0])),
            "missing parent": lambda r: r["roles"][0]["references"][0].pop("parent"),
            "cross-context parent": lambda r: r["roles"][0]["references"][0].update(parent="fixture-leaf"),
            "name instead of declaration ID": lambda r: r["roles"][0]["references"][0].update(declaration="Blanc.leaf"),
            "fixture impostor population": lambda r: r["declarations"][2].update(population="production"),
            "module impostor": lambda r: r["declarations"][0].update(module="Fixture"),
            "environment impostor": lambda r: r["declarations"][0].update(environment="fixture-env"),
            "type impostor": lambda r: r["declarations"][0]["type_identity"].update(value="fedcba9876543210"),
            "source impostor": lambda r: r["declarations"][0]["source"].update(path="scripts/Fixture.lean"),
            "omitted environment": lambda r: r["environments"].pop("fixture-env"),
            "omitted external artifact": lambda r: r["environments"]["production-env"]["identity"]["file_sha256"].pop(str(self.import_artifact)),
            "wrong source setup module": lambda r: r["environments"]["production-env"]["setup"].update(name="Fixture"),
            "omitted visibility": lambda r: r.update(visibility=[]),
            "invisible fixture target": lambda r: r["roles"][0]["references"][0].update(declaration="fixture-leaf"),
            "wrong reference visibility context": lambda r: r["roles"][0]["references"][0].update(visibility="fixture-view"),
            "static boolean ID": lambda r: r["static_resolutions"][0].update(id=True),
            "static wrong context": lambda r: r["static_resolutions"][0].update(context="fixture"),
            "static wrong visible target": lambda r: r["static_resolutions"][0].update(declaration="prod-used"),
            "static wrong digest scheme": lambda r: r["static_resolutions"][0].update(request_digest_scheme="utf8"),
            "static changed witness": lambda r: r["static_resolutions"][0].update(provenance_sha256="0" * 64),
            "static changed request provenance": lambda r: r["static_resolutions"][0].update(request_sha256="0" * 64),
            "omitted static response": lambda r: r.update(static_resolutions=[]),
            "unresolved provenance": lambda r: r.update(unresolved=["missing actual declaration source"]),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                candidate = copy.deepcopy(self.native_receipt)
                mutate(candidate)
                with self.assertRaises(UsageEvidenceError):
                    self.run_native(candidate)

    def test_external_bytes_and_executable_controls_bite(self):
        for path in [self.import_artifact, self.executable, self.root / ".lake/build/bin/simpCollector"]:
            with self.subTest(path=path):
                original = path.read_bytes()
                path.write_bytes(original + b"drift")
                with self.assertRaisesRegex(UsageEvidenceError, "stale/invalid native environment"):
                    self.run_native()
                path.write_bytes(original)
                self.assertEqual(path.read_bytes(), original)  # restored green bytes, no rerun

    def test_same_name_fixture_never_credits_production(self):
        self.native_receipt["roles"][0]["references"][0].update(declaration="fixture-leaf", parent=None)
        with self.assertRaisesRegex(UsageEvidenceError, "invisible"):
            self.run_native()
        # An actual fixture-local constant with the same Name remains nonproduction.
        self.native_receipt["roles"][0]["references"] = []
        self.native_receipt["static_resolutions"] = []
        self.native_receipt["roles"][1]["references"] = [{"command": "fixture-leaf", "span": [8, 12],
            "declaration": "fixture-leaf", "visibility": "fixture-view", "kind": "checked-name", "parent": None}]
        self.assertEqual(self.run_native(requests=[], static_contexts=[], static_provenance=[])["uses"], {})

    def test_fixture_can_consume_visible_imported_production(self):
        self.native_receipt["roles"][0]["references"] = []
        self.native_receipt["static_resolutions"] = []
        self.native_receipt["roles"][1]["references"] = [{"command": "fixture-leaf", "span": [8, 12],
            "declaration": "prod-used", "visibility": "fixture-view", "kind": "checked-name", "parent": None}]
        result = self.run_native(requests=[], static_contexts=[], static_provenance=[])
        self.assertEqual(set(result["uses"]), {"prod-used"})

    def test_independent_inventory_controls_bite(self):
        roles = copy.deepcopy(self.roles)
        roles[0].update(coverage="import-only", commands=[])
        receipt = copy.deepcopy(self.native_receipt)
        receipt["roles"][0] = {**roles[0], "references": []}
        with self.assertRaisesRegex(UsageEvidenceError, "declaration missing"):
            self.run_native(receipt, expected_roles=roles)
        declarations = copy.deepcopy(self.declarations)
        declarations[2].update(population="production")
        with self.assertRaisesRegex(UsageEvidenceError, "impersonates production"):
            self.run_native({**self.native_receipt, "declarations": declarations}, expected_declarations=declarations)
        environments = copy.deepcopy(self.environments)
        environments["production-env"]["identity"]["file_sha256"].pop(str(self.import_artifact))
        receipt = {**self.native_receipt, "environments": environments}
        with self.assertRaisesRegex(UsageEvidenceError, "incomplete captured environment"):
            self.run_native(receipt, expected_environments=environments)
        with self.assertRaisesRegex(UsageEvidenceError, "missing actual resolved static contexts"):
            self.run_native(static_contexts=[])
        with self.assertRaisesRegex(UsageEvidenceError, "missing validated static provenance witness"):
            self.run_native(static_provenance=[])
        visibility = copy.deepcopy(self.visibility)
        visibility[0]["declarations"].append("fixture-leaf")
        with self.assertRaisesRegex(UsageEvidenceError, "conflicting same-name origins"):
            self.run_native({**self.native_receipt, "visibility": visibility}, expected_visibility=visibility)
        requests = copy.deepcopy(self.native_requests)
        requests[0]["data_origin"].update(sha256="0" * 64)
        with self.assertRaisesRegex(UsageEvidenceError, "unbound original static request"):
            self.run_native(requests=requests)

    def test_v2_shared_path_controls_bite(self):
        for bad in ["scripts//check.py", "scripts\\check.py", "Scripts/check.py"]:
            with self.subTest(path=bad):
                bindings = {**self.bindings, bad: self.bindings["scripts/check.py"]}
                receipt = {**self.native_receipt, "bindings": bindings}
                with self.assertRaises(UsageEvidenceError):
                    self.run_native(receipt, expected_bindings=bindings)
        local = self.root / "scripts/check.py"
        target = self.root / "scripts/Real.py"
        local.rename(target)
        local.symlink_to(target)
        with self.assertRaisesRegex(UsageEvidenceError, "symbolic-link"):
            self.run_native()

    def test_ascii_request_digest_and_corrected_operation_binding(self):
        requests = copy.deepcopy(self.native_requests)
        requests[0]["note"] = "non-ASCII provenance: é"
        requests[0]["check_operation"].update(line=1, end_line=1)
        provenance = copy.deepcopy(self.provenance)
        provenance[0]["witness"]["original_check_operation"] = requests[0]["check_operation"]
        digest = sha(json.dumps(requests[0], sort_keys=True, separators=(",", ":")).encode())
        provenance[0]["witness"]["original_request_sha256"] = digest
        provenance_sha = sha(json.dumps(provenance[0], sort_keys=True, separators=(",", ":")).encode())
        receipt = copy.deepcopy(self.native_receipt)
        receipt["static_resolutions"][0].update(request_sha256=digest, provenance_sha256=provenance_sha)
        self.assertEqual(len(self.run_native(receipt, requests=requests, static_provenance=provenance)["uses"]["prod-leaf"]), 2)
        # UTF-8 compact JSON differs from the repair overlay's explicit ASCII scheme.
        receipt["static_resolutions"][0]["request_sha256"] = sha(json.dumps(
            requests[0], sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())
        with self.assertRaisesRegex(UsageEvidenceError, "provenance/resolved-context mismatch"):
            self.run_native(receipt, requests=requests, static_provenance=provenance)


if __name__ == "__main__":
    unittest.main(verbosity=2)
