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
                            validate_imported_and_index, REQUEST_DIGEST_SCHEME)


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


class ImportedOwnerControls(unittest.TestCase):
    """Nine transport families. Expected captures are mocks, never native evidence."""
    def setUp(self):
        NativeControls.setUp(self)
        self.foreign_path = ".lake/packages/foreign/Foreign/Check.lean"
        foreign = self.root / self.foreign_path
        foreign.parent.mkdir(parents=True)
        foreign.write_bytes(b"theorem leaf : True := by trivial\n")
        self.bindings[self.foreign_path] = sha(foreign.read_bytes())
        manifest = json.dumps({"packages": [{"name": "foreign", "type": "git", "rev": "b" * 40}]}).encode()
        (self.root / "lake-manifest.json").write_bytes(manifest)
        self.bindings["lake-manifest.json"] = sha(manifest)
        self.private_part = self.outside / "External.olean.private"
        self.private_part.write_bytes(b"mock private metadata")
        for eid, env in list(self.environments.items()):
            setup = copy.deepcopy(env["setup"])
            setup["importArts"]["Foreign.Check"] = [[str(self.import_artifact), str(self.private_part)], []]
            setup["importArts"]["Blanc.X"] = [[str(self.import_artifact)]]
            self.environments[eid] = capture_native_environment(self.root, setup)
        for d in self.declarations:
            d.update(origin_kind="analysis-source", level_params=[])
            d["source"]["range"] = {"kind": "direct", "span": d["source"]["span"], "owner": None}
        self.declarations.append({**decl("Foreign.leaf", module="Foreign.Check"), "id": "foreign-leaf",
            "owner": "foreign-leaf", "origin_kind": "imported-module", "population": "nonproduction",
            "environment": "production-env", "level_params": [], "defining_kind": "theorem",
            "type_identity": copy.deepcopy(self.declarations[0]["type_identity"]),
            "source": {"path": self.foreign_path, "sha256": self.bindings[self.foreign_path],
                       "range": {"kind": "absent", "span": None, "owner": None}},
            "imported": {"module": "Foreign.Check",
                "parts": copy.deepcopy(self.environments["production-env"]["setup"]["importArts"]["Foreign.Check"]),
                "capture": self.capture("production-env", "origin-foreign"),
                "package": {"name": "foreign", "rev": "b" * 40, "source_root": ".lake/packages/foreign",
                    "module_source": "Foreign/Check.lean", "manifest_path": "lake-manifest.json",
                    "manifest_sha256": self.bindings["lake-manifest.json"]}}})
        self.observations = []
        for view in self.visibility:
            view["declarations"].append("foreign-leaf")
            view["observations"] = []
            role = next(r for r in self.roles if r["id"] == view["role"])
            for did in view["declarations"]:
                d = next(d for d in self.declarations if d["id"] == did)
                oid = view["id"] + ":" + did
                view["observations"].append(oid)
                self.observations.append({"id": oid, "role": view["role"], "command": view["command"],
                    "environment": role["environment"], "scope": "use", "declaration": did,
                    "observed_kind": d["kind"], "view_relation": "same-kind", "level_params": [],
                    "type_identity": copy.deepcopy(d["type_identity"]),
                    "type_comparison": "lean4.34-expr.equal+ordered-levelParams",
                    "origin_binding": ({"kind": "local", "module": d["module"], "parts": None}
                        if d["origin_kind"] == "analysis-source" and d["environment"] == role["environment"]
                        else {"kind": "imported-module", "module": d["module"],
                              "parts": copy.deepcopy(self.environments[role["environment"]]["setup"]["importArts"][d["module"]])}),
                    "capture": self.capture(role["environment"], oid)})
        self.contexts[0].update(observation="production-check:prod-leaf", owner_requirement="source",
                                requires_defining_kind=False)
        self.provenance[0]["witness"]["effective_owner_candidates"] = []  # unchanged empty prepared hints
        self.native_receipt["schema"] = "blanc-resolved-usage-v3"
        self.native_receipt["roles"][0]["references"][0]["observation"] = "production-used:prod-leaf"
        self.supplements = []
        self.sync()

    def capture(self, environment, context):
        return {"environment": environment, "context_id": context, "adapter": "scripts/check.py"}

    def digest(self, value):
        return sha(json.dumps(value, sort_keys=True, allow_nan=False, separators=(",", ":")).encode())

    def sync(self):
        """Build a mock receipt from separate expected records, no native claims."""
        for field, value in [("declarations", self.declarations), ("environments", self.environments),
                             ("visibility", self.visibility), ("observations", self.observations)]:
            self.native_receipt[field] = copy.deepcopy(value)
        c, p = self.contexts[0], self.provenance[0]
        d = next(d for d in self.declarations if d["id"] == c["declaration"])
        owner = next(x for x in self.declarations if x["id"] == d["owner"]) if d["owner"] else d
        source = owner.get("source")
        path = source["path"] if source else None
        self.supplements = [{"id": 1, "request_digest_scheme": REQUEST_DIGEST_SCHEME,
            "request_sha256": self.digest(self.native_requests[0]), "overlay_sha256": p["overlay_sha256"],
            "overlay_row_sha256": self.digest(p["witness"]), "declaration": d["id"], "observation": c["observation"],
            "owner": d["owner"], "capture": self.capture("production-env", "static-owner-1"),
            "owner_witness": {"declaration": owner["id"], "module": owner["module"], "source_path": path},
            "hint_relation": "confirmed" if path in p["witness"]["effective_owner_candidates"] else "discovered-outside-hints"}]
        self.native_receipt["owner_supplements"] = copy.deepcopy(self.supplements)
        self.native_receipt["static_resolutions"] = [{"id": 1, "context": c["context"],
            "declaration": c["declaration"], "visibility": c["visibility"], "observation": c["observation"],
            "request_digest_scheme": REQUEST_DIGEST_SCHEME, "request_sha256": self.digest(self.native_requests[0]),
            "provenance_sha256": self.digest(p), "supplement_sha256": self.digest(self.supplements[0])}]

    def run_v3(self, receipt=None, **overrides):
        args = {"expected_sources": self.sources, "expected_bindings": self.bindings,
            "expected_roles": self.roles, "expected_declarations": self.declarations,
            "expected_environments": self.environments, "expected_visibility": self.visibility,
            "expected_observations": self.observations, "requests": self.native_requests,
            "static_contexts": self.contexts, "static_provenance": self.provenance,
            "owner_supplements": self.supplements, **overrides}
        return validate_imported_and_index(self.root, self.native_receipt if receipt is None else receipt, **args)

    def refuse(self, mutate, diagnostic, *, field=None):
        receipt = copy.deepcopy(self.native_receipt)
        overrides = {}
        if field is None:
            mutate(receipt)
        else:
            value = copy.deepcopy(getattr(self, field))
            mutate(value)
            expected_name = {"declarations": "expected_declarations", "observations": "expected_observations",
                "visibility": "expected_visibility", "roles": "expected_roles", "contexts": "static_contexts",
                "supplements": "owner_supplements", "environments": "expected_environments"}[field]
            overrides[expected_name] = value
            received_name = {"contexts": None, "supplements": "owner_supplements"}.get(field, field)
            if received_name:
                receipt[received_name] = value
        with self.assertRaisesRegex(UsageEvidenceError, diagnostic):
            self.run_v3(receipt, **overrides)

    def foreign_target(self):
        self.contexts[0].update(declaration="foreign-leaf", observation="production-check:foreign-leaf")
        next(o for o in self.observations if o["id"] == self.contexts[0]["observation"])["scope"] = "defining-metadata"
        self.sync()

    def test_1_compatibility(self):
        self.assertEqual(len(self.run_v3()["uses"]["prod-leaf"]), 2)
        self.refuse(lambda r: r.update(schema="blanc-resolved-usage-v2"), "requires blanc-resolved-usage-v3")
        with self.assertRaisesRegex(UsageEvidenceError, "requires blanc-resolved-usage-v2"):
            validate_native_and_index(self.root, self.native_receipt, self.sources, self.bindings, self.roles,
                self.declarations, self.environments, self.visibility, self.native_requests, self.contexts, self.provenance)

    def test_2_empty_incomplete_hints(self):
        self.assertEqual(self.provenance[0]["witness"]["effective_owner_candidates"], [])
        self.run_v3()
        self.refuse(lambda rows: rows.clear(), "missing independently resolved owner supplement", field="supplements")
        self.refuse(lambda rows: rows[0]["owner_witness"].update(source_path="scripts/Fixture.lean"),
                    "actual canonical source/module", field="supplements")
        self.provenance[0]["witness"]["effective_owner_candidates"] = ["scripts/Fixture.lean"]
        self.sync()
        self.run_v3()  # incomplete hints stay unchanged, separately supplied native mock witness wins
        self.refuse(lambda rows: rows[0].update(hint_relation="confirmed"), "hint relation", field="supplements")
        self.refuse(lambda r:r.pop("owner_supplements"),"independent native owner supplements")
        self.refuse(lambda rows:rows[0].update(owner="prod-used"),"immutable lineage",field="supplements")
        self.refuse(lambda rows:rows[0].pop("capture"),"independent native capture",field="supplements")

    def test_3_immutable_lineage(self):
        self.native_requests[0]["note"] = "é"
        self.provenance[0]["witness"]["original_request_sha256"] = self.digest(self.native_requests[0])
        self.sync(); self.run_v3()
        for key in ["request_sha256", "overlay_sha256", "overlay_row_sha256"]:
            with self.subTest(key=key):
                self.refuse(lambda rows: rows[0].update({key: "0" * 64}), "immutable lineage", field="supplements")
        self.refuse(lambda rows: rows[0].update(id=True), "invalid original static request ID", field="supplements")
        self.refuse(lambda rows: rows.append(copy.deepcopy(rows[0])), "duplicate owner supplement", field="supplements")
        self.refuse(lambda r: r["static_resolutions"][0].update(supplement_sha256="0" * 64), "substituted owner supplement")
        self.refuse(lambda rows: rows[0].update(request_sha256=sha(json.dumps(self.native_requests[0],
            sort_keys=True,separators=(",", ":"),ensure_ascii=False).encode())), "immutable lineage", field="supplements")

    def test_4_foreign_origin(self):
        self.foreign_target(); self.run_v3()
        for mutate, diagnostic in [
            (lambda d: d[3]["imported"].update(module="Fake"), "module key"),
            (lambda d: d[3]["imported"]["parts"][0].reverse(), "ordered artifact"),
            (lambda d: d[3]["imported"]["parts"][0].pop(), "ordered artifact"),
            (lambda d: d[3]["imported"]["package"].update(rev="0" * 40), "pin differs"),
            (lambda d: d[3].update(origin_role="production"), "bypasses production"),
            (lambda d: d[3].update(defining_kind="def"), "kind contradiction"),
            (lambda d: d[3].pop("defining_kind"), "defining-kind provenance"),
            (lambda d: d[3]["imported"]["package"].update(manifest_sha256="0"*64), "package/pin witness"),
            (lambda d: d[3]["imported"].pop("capture"), "independent native capture")]:
            with self.subTest(diagnostic=diagnostic):self.refuse(mutate, diagnostic, field="declarations")

    def test_5_source_attachment(self):
        self.foreign_target(); self.run_v3()
        self.refuse(lambda d: d[3].update(source=None), "actual canonical source/module", field="declarations")
        self.refuse(lambda d: d[3].pop("source"), "explicit foreign source", field="declarations")
        self.refuse(lambda d: d[3]["source"].update(sha256="0" * 64), "Lake source/artifact", field="declarations")
        self.refuse(lambda d: d[3]["imported"]["package"].update(module_source="Wrong.lean"), "Lake source/artifact", field="declarations")
        for bad in [".lake//packages/foreign/Foreign/Check.lean", ".lake\\packages/foreign/Foreign/Check.lean",
                    ".lake/packages/foreign/foreign/Check.lean"]:
            with self.subTest(path=bad):
                bindings = {**self.bindings, bad: self.bindings[self.foreign_path]}
                with self.assertRaisesRegex(UsageEvidenceError, "unsafe/unreadable"):
                    self.run_v3({**self.native_receipt,"bindings": bindings}, expected_bindings=bindings)
        local=self.root/self.foreign_path; target=local.with_name("Real.lean")
        local.rename(target);local.symlink_to(target)
        with self.assertRaisesRegex(UsageEvidenceError,"symbolic-link"):self.run_v3()

    def test_6_production_coverage(self):
        self.run_v3()
        self.refuse(lambda d: d[3].update(population="production"), "bypasses production", field="declarations")
        self.refuse(lambda d: d[0].update(origin_kind="imported-module"), "bypasses production", field="declarations")
        self.refuse(lambda d: d[2].update(population="production"), "impersonates production", field="declarations")
        self.refuse(lambda d:d[0].pop("origin_kind"),"tagged native origin",field="declarations")
        self.refuse(lambda d:d[0].pop("level_params"),"ordered native universe",field="declarations")
        self.refuse(lambda d:d[0].update(imported={}),"local origin carries foreign",field="declarations")
        self.refuse(lambda r: r["roles"][0]["commands"].pop(), "role/command coverage")
        self.refuse(lambda d: d[0]["source"].update(span=[0,len(self.source)]), "original command inventory", field="declarations")

    def test_7_actual_context(self):
        self.run_v3()
        self.refuse(lambda r: r["roles"][0]["references"][0].update(declaration="fixture-leaf"), "invisible")
        self.refuse(lambda r: r["static_resolutions"][0].update(declaration="prod-used"), "resolved-context mismatch")
        self.refuse(lambda r: r["static_resolutions"][0].update(observation="production-check:foreign-leaf"), "substituted owner supplement")
        self.refuse(lambda o: next(x for x in o if x["id"]=="production-used:prod-leaf").update(scope="defining-metadata"),
                    "substituted metadata/use", field="observations")
        self.refuse(lambda o: o[0]["origin_binding"].update(module="Fixture"), "module/artifact binding", field="observations")
        self.refuse(lambda r:r.pop("observations"),"saved-context observations")
        self.refuse(lambda o:o.append(copy.deepcopy(o[0])),"duplicate native observation",field="observations")
        self.refuse(lambda o:o[0].update(command="unknown"),"observation context",field="observations")
        self.refuse(lambda v:v[0].update(observations=[]),"observation/origin mapping",field="visibility")
        self.refuse(lambda c:c[0].pop("owner_requirement"),"operation owner requirements",field="contexts")
        self.refuse(lambda o: next(x for x in o if x["id"]=="fixture-view:prod-used")["origin_binding"].update(kind="local",parts=None),
                    "local defining context", field="observations")
        environments=copy.deepcopy(self.environments)
        setup=copy.deepcopy(environments["fixture-env"]["setup"]);setup["importArts"].pop("Foreign.Check")
        environments["fixture-env"]=capture_native_environment(self.root,setup)
        self.refuse(lambda o: next(x for x in o if x["id"]=="production-check:foreign-leaf")["origin_binding"].update(parts=[]),
                    "actual imported module/artifacts", field="observations")
        with self.assertRaisesRegex(UsageEvidenceError,"actual imported module/artifacts"):
            self.run_v3({**self.native_receipt,"environments":environments}, expected_environments=environments)
        self.native_receipt["roles"][1]["references"] = [{"command":"fixture-leaf","span":[8,12],
            "declaration":"prod-used","visibility":"fixture-view","observation":"fixture-view:prod-used",
            "kind":"checked-name","parent":None}]
        self.assertIn("prod-used",self.run_v3()["uses"])
        self.foreign_target()
        self.assertEqual(len(self.run_v3()["uses"]["prod-leaf"]),1)  # foreign header check gives no Blanc credit

    def test_8_honest_metadata(self):
        self.foreign_target();self.run_v3()
        self.refuse(lambda d:d[3]["source"]["range"].update(span=[0,4]),"fabricated absent",field="declarations")
        self.refuse(lambda d:d[0]["source"].pop("range"),"range provenance",field="declarations")
        self.refuse(lambda d:d[0]["source"].update(range={"kind":"owner","span":[0,4],"owner":"fixture-leaf"}),
                    "range owner",field="declarations")
        self.refuse(lambda d:(d[0].update(owner=None),d[0]["source"].update(range={"kind":"owner","span":[0,4],"owner":None})),
                    "range owner",field="declarations")
        self.refuse(lambda o:o[0].update(level_params=["u"]),"full-type/universe",field="observations")
        self.refuse(lambda o:o[0].update(type_comparison="hash64"),"full-type/universe",field="observations")
        self.refuse(lambda o:o[0].pop("capture"),"independent native capture",field="observations")
        # Actual native capture must demonstrate this exported view; these are only transport mocks.
        for o in self.observations:
            if o["declaration"]=="foreign-leaf":o.update(observed_kind="axiom",view_relation="theorem-axiom-export")
        self.declarations[3]["defining_kind"]=None
        self.sync();self.run_v3()
        self.refuse(lambda c:c[0].update(requires_defining_kind=True),"defining kind unresolved",field="contexts")
        self.refuse(lambda o:next(x for x in o if x["declaration"]=="foreign-leaf").update(view_relation="same-kind"),
                    "kind view relation",field="observations")
        # Compiled-only operation legitimately needs no source attachment or local body command.
        self.declarations[3]["source"]=None;self.contexts[0]["owner_requirement"]="compiled-origin"
        self.sync();self.run_v3()
        self.refuse(lambda c:c[0].update(owner_requirement="source"),"actual source owner unresolved",field="contexts")

    def test_9_currency(self):
        self.run_v3()
        for path in [self.root/self.foreign_path,self.private_part,self.executable]:
            with self.subTest(path=path):
                baseline=path.read_bytes();path.write_bytes(baseline+b"drift")
                with self.assertRaisesRegex(UsageEvidenceError,"stale native input|stale/invalid native environment"):
                    self.run_v3()
                path.write_bytes(baseline);self.assertEqual(path.read_bytes(),baseline)
        self.refuse(lambda r:r["environments"]["production-env"]["setup"]["importArts"].pop("Foreign.Check"),
                    "environment coverage/identity")
        # Simulate drift during acceptance: no compiler or generator is involved.
        import usage_evidence
        original=usage_evidence._read;calls={}
        def changing_read(root,path):
            data=original(root,path);calls[path]=calls.get(path,0)+1
            return data+b"drift" if path==self.foreign_path and calls[path]>1 else data
        with patch("usage_evidence._read",side_effect=changing_read):
            with self.assertRaisesRegex(UsageEvidenceError,"changed during acceptance"):self.run_v3()


if __name__ == "__main__":
    unittest.main(verbosity=2)
