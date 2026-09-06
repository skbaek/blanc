"""No-Lean controls for catalogue routing, recipes, streams and fatal boundaries."""
from __future__ import annotations
import argparse
from collections import Counter
from contextlib import ExitStack, redirect_stdout, redirect_stderr
import copy
from dataclasses import replace
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from gate_cache_selftest import gc
import gate_execution as ge


class Fake:
    version = 1
    managed = True
    def __init__(self):
        self.calls = []
        self.fail_phase = None
        self.fail_key = None
        self.on_capture = lambda spec: None
    def bind(self, context):
        self.context = context
    def capture(self, spec):
        self.calls.append(spec)
        self.on_capture(spec)
        if spec.phase == self.fail_phase or spec.key == self.fail_key:
            raise ge.FatalOperationError("fixture fatal refusal/cancellation/cleanup")
        out = b"\x00\xffmaterial\r\n" if spec.role == "material" else b"OK \xe2\x80\x94 fake: green\r\n"
        return ge.OperationResult(1, 0, out, b"diagnostic\r\n", .01, "absent", "fixture", {"text": "OK — forged: wrapper"})


class ManagedTests(unittest.TestCase):
    def setUp(self):
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        self.root = Path(self.stack.enter_context(tempfile.TemporaryDirectory(prefix="blanc-managed-control-"))).resolve()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "scripts").mkdir()
        (self.root / ".gitignore").write_text(".lake/\n")
        self.gate = {"id": "fixture", "order": 1, "command": ["scripts/check-fixture.sh"], "kind": "cacheable",
                     "inputs": {"files": ["input.txt"], "material_output": [
                         {"id": "bytes", "command": ["fixture-evaluator"], "authority": ["input.txt"], "resource_class": "elaboration"}]},
                     "verdict": {"expect_exit": 0, "summary_patterns": ["^OK — fake: "]}}
        (self.root / "input.txt").write_text("input")
        self.fake = Fake()
        self.stack.enter_context(patch.object(gc, "audit", return_value=0))
        self.stack.enter_context(patch.object(gc, "tree_identity", return_value={"commit": "fixture", "worktree": "clean"}))
        self.stack.enter_context(redirect_stdout(io.StringIO()))
        self.stack.enter_context(redirect_stderr(io.StringIO()))
        self.stack.enter_context(patch.object(gc, "component_tools", return_value=("tools", {})))
        self.stack.enter_context(patch.object(ge, "cost_tools", return_value="cost-tools"))
        cache = self.root / ".cache"
        cache.mkdir()
        self.stack.enter_context(patch.dict(os.environ, {"LAKE_CACHE_DIR": str(cache)}))
        (self.root / "scripts/check-lake-artifact-cache.sh").write_text("fixture checker")
        (self.root / "scripts/check-lake-artifact-cache.lean").write_text("fixture Lean checker")
        (self.root / "lean-toolchain").write_text("fixture toolchain")
        gc.forget_digests()

    def context(self, gates=None):
        gates = gates or [self.gate]
        self.registry = {"schema": 1, "gates": gates}
        (self.root / "scripts/gate-registry.json").write_text(json.dumps(self.registry))
        (self.root / "scripts/gate-economy.json").write_text(json.dumps({"schema": 1, "rows": [
            {"id": gate["id"], "resource_class": "exclusive" if gate["id"] == "elab" else "light"} for gate in gates]}))
        return ge.ExecutionContext(self.root, self.registry, self.fake, gc)

    def test_production_population_classes_projections_and_recipes(self):
        root = Path(__file__).resolve().parent.parent
        registry = gc.load_registry(root / "scripts/gate-registry.json")
        rows = json.loads((root / "scripts/gate-economy.json").read_text())["rows"]
        self.assertEqual(len(registry["gates"]), 61)
        self.assertEqual([gate["order"] for gate in registry["gates"]], list(range(1, 62)))
        self.assertEqual(Counter(row["resource_class"] for row in rows), {"light": 28, "elaboration": 18, "exclusive": 15})
        projections = [item for gate in registry["gates"] for item in gate.get("inputs", {}).get("material_output", [])]
        self.assertEqual(len(projections), 6)
        self.assertTrue(all(item["resource_class"] == "elaboration" for item in projections))
        self.assertEqual({gate["id"]: gate["managed_execution"] for gate in registry["gates"] if "managed_execution" in gate}, ge.RECIPES)

    def test_exact_material_bytes_and_separate_summary_streams(self):
        context = self.context()
        _, details = gc.component_material_output(self.root, self.gate["inputs"]["material_output"], context, self.gate)
        self.assertEqual(details["bytes::output"], gc.sha256_bytes(b"\x00\xffmaterial\r\n"))
        verdict, _ = gc.execute(self.root, self.gate, False, context)
        self.assertTrue(verdict["passed"])
        self.assertEqual(verdict["summary"], ["OK — fake: green"])
        for stdout, stderr, rc in (("OK — fake: green\n".encode(), "OK — fake: twice\n".encode(), 0),
                                   ("OK — fake: green\n".encode(), b"", 1), (b"", b"diagnostic", 0)):
            result = ge.OperationResult(1, rc, stdout, stderr, 0, "absent", None, {})
            self.assertFalse(gc.capture_verdict(self.gate, result.completed_text([]))["passed"])

    def test_fatal_each_fingerprint_phase_never_advances_cache(self):
        for phase in ("planning", "post-run", "reused-revalidation"):
            with self.subTest(phase=phase):
                context = self.context()
                self.fake.calls.clear()
                self.fake.fail_phase = None
                cache_path = gc.cache_path(self.root)
                if cache_path.exists(): cache_path.unlink()
                if phase == "reused-revalidation":
                    self.assertEqual(gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context), 0)
                before = cache_path.read_bytes() if cache_path.exists() else None
                context = self.context()
                self.fake.calls.clear()
                self.fake.fail_phase = phase
                with self.assertRaises(ge.FatalOperationError):
                    gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context)
                after = cache_path.read_bytes() if cache_path.exists() else None
                self.assertEqual(before, after)
                if phase in {"planning", "reused-revalidation"}:
                    self.assertFalse(any(spec.role == "gate" for spec in self.fake.calls))

    def test_reused_row_executes_only_its_actual_projections(self):
        context = self.context()
        self.assertEqual(gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context), 0)
        self.fake.calls.clear()
        self.assertEqual(gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context), 0)
        self.assertEqual([spec.phase for spec in self.fake.calls], ["planning", "reused-revalidation"])
        self.assertTrue(all(spec.role == "material" for spec in self.fake.calls))

    def test_unexpected_managed_io_error_is_fatal_in_every_fingerprint_phase(self):
        for phase in ("planning", "post-run", "reused-revalidation"):
            context = self.context()
            self.fake.calls.clear()
            cache_path = gc.cache_path(self.root)
            if cache_path.exists(): cache_path.unlink()
            if phase == "reused-revalidation":
                self.assertEqual(gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context), 0)
            before = cache_path.read_bytes() if cache_path.exists() else None
            def fail(spec):
                if spec.phase == phase:
                    raise OSError("fixture capture I/O failure")
            self.fake.on_capture = fail
            with self.assertRaisesRegex(ge.FatalOperationError, "OSError"):
                gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context)
            self.assertEqual(before, cache_path.read_bytes() if cache_path.exists() else None)
            self.fake.on_capture = lambda spec: None

    def test_malformed_managed_completion_cannot_be_credited(self):
        context = self.context()
        good = ge.OperationResult(1, 0, b"OK", b"", .1, "absent", None, {})
        for changes in ({"stdout": "text"}, {"returncode": True}, {"elapsed": float("nan")},
                        {"elapsed": -1}, {"receipt": []}, {"receipt": {"x": object()}},
                        {"operation_id": 1}, {"lifecycle": "preserved"}):
            with patch.object(self.fake, "capture", return_value=replace(good, **changes)):
                with self.assertRaises(ge.FatalOperationError):
                    context.capture(self.gate, "body", "fixture/body")
            self.assertEqual(context.operations, [])

    def test_source_or_registry_drift_each_phase_is_fatal(self):
        for phase in ("planning", "body", "post-run", "reused-revalidation"):
            context = self.context()
            self.fake.on_capture = lambda spec: (self.root / "input.txt").write_text(phase)
            with self.assertRaisesRegex(ge.FatalOperationError, "inputs moved"):
                context.capture(self.gate, phase, "fixture/body")

    def prepare_modules(self):
        (self.root / "Blanc").mkdir(exist_ok=True)
        (self.root / "Blanc.lean").write_text("-- intentionally imports nothing\n")
        (self.root / "Blanc/Unimported.lean").write_text("def hidden := 1\n")
        shutil.copyfile(Path(__file__).with_name("check-elab-selection.py"), self.root / "scripts/check-elab-selection.py")

    def test_full_build_fixture_complete_targets_integrity_certificate_order(self):
        self.prepare_modules()
        gate = {"id": "lake-build", "order": 1, "command": ["lake", "build"], "kind": "composition", "reason": "refresh", "prerequisite": True,
                "managed_execution": ge.RECIPES["lake-build"], "verdict": {"expect_exit": 0, "summary_patterns": []}}
        context = self.context([gate, dict(self.gate, order=2)])
        def certify(root):
            self.assertEqual([spec.key for spec in self.fake.calls], ["lake-build/build/0", "lake-build/build/1", "lake-build/modules", "lake-build/integrity"])
        with patch.object(gc, "write_build_certificate", side_effect=certify):
            verdict, _ = context.execute(gate, "prerequisite", False)
        self.assertTrue(verdict["passed"])
        self.assertEqual(context.templates["lake-build/modules"][1][2:], ("Blanc", "Blanc.Unimported"))
        self.fake.calls.clear()
        self.fake.fail_key = "lake-build/build/0"
        with patch.object(gc, "build_certificate_status", return_value=(False, "missing", None)), patch.object(gc, "plan", side_effect=AssertionError("planned after failed build")):
            with self.assertRaises(ge.FatalOperationError):
                gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context)
        self.assertEqual([s.key for s in self.fake.calls], ["lake-build/build/0"])

    def test_complete_elab_certificate_rejects_drift_missing_trace_and_foreign(self):
        self.prepare_modules()
        self.stack.enter_context(patch.object(gc, "module_dep_hash", side_effect=lambda root, name: name + "-trace"))
        self.stack.enter_context(patch.object(gc, "host_identity", return_value="fixture-host"))
        original = ge.elab_identity(self.root, gc)
        gc.atomic_json(self.root / ".lake/managed-elab-build.json", original)
        ge.require_certificate(self.root, "elab-modules-v1", gc)
        for field, value in (("targets", ["Blanc"]), ("host", "foreign"), ("traces", {})):
            gc.atomic_json(self.root / ".lake/managed-elab-build.json", dict(original, **{field: value}))
            with self.assertRaises(ge.FatalOperationError): ge.require_certificate(self.root, "elab-modules-v1", gc)
        gc.atomic_json(self.root / ".lake/managed-elab-build.json", original)
        with patch.object(gc, "module_dep_hash", side_effect=gc.Unresolvable("missing trace")):
            with self.assertRaises(ge.FatalOperationError): ge.require_certificate(self.root, "elab-modules-v1", gc)
        (self.root / "scripts/check-elab-selection.py").write_text((self.root / "scripts/check-elab-selection.py").read_text() + "\n# selector moved\n")
        with self.assertRaises(ge.FatalOperationError): ge.require_certificate(self.root, "elab-modules-v1", gc)

    def test_certificate_hit_skips_builds_and_fresh_forces_all_prerequisites(self):
        self.prepare_modules()
        gate = {"id": "lake-build", "order": 1, "command": ["lake", "build"], "kind": "composition", "reason": "refresh", "prerequisite": True,
                "managed_execution": ge.RECIPES["lake-build"], "verdict": {"expect_exit": 0, "summary_patterns": []}}
        context = self.context([gate])
        with patch.object(gc, "build_certificate_status", return_value=(True, "exact", {})), patch.object(gc, "write_build_certificate") as certify:
            self.assertEqual(gc.run(self.root, argparse.Namespace(fresh=False, echo=False), context), 0)
            self.assertEqual(self.fake.calls, [])
            certify.assert_not_called()
            self.assertEqual(gc.run(self.root, argparse.Namespace(fresh=True, echo=False), context), 0)
            self.assertEqual([s.key for s in self.fake.calls], ["lake-build/build/0", "lake-build/build/1", "lake-build/modules", "lake-build/integrity"])
            certify.assert_called_once()

    def test_weth_requires_exact_certificate_before_body(self):
        gate = dict(self.gate, id="weth10-current-mainnet", command=["scripts/check-weth10-current-mainnet.sh", "--composed-prerequisites"],
                    managed_execution=ge.RECIPES["weth10-current-mainnet"])
        context = self.context([gate])
        for reason in ("absent", "foreign host", "stale binary", "missing trace"):
            with patch.object(gc, "build_certificate_status", return_value=(False, reason, None)):
                with self.assertRaisesRegex(ge.FatalOperationError, reason):
                    context.execute(gate, "body", False)
            self.assertEqual(self.fake.calls, [])
        with patch.object(gc, "build_certificate_status", return_value=(True, "exact", {})):
            context.execute(gate, "body", False)
        self.assertEqual(self.fake.calls[0].argv, tuple(ge.RECIPES["weth10-current-mainnet"]["body"]))

    def test_elab_refresh_precedes_identical_certified_body(self):
        self.prepare_modules()
        gate = dict(self.gate, id="elab", command=["scripts/check-elab.sh"], managed_execution=ge.RECIPES["elab"])
        context = self.context([gate])
        with patch.object(gc, "module_dep_hash", side_effect=lambda root, name: name + "-trace"):
            context.execute(gate, "body", False)
        self.assertEqual([spec.key for spec in self.fake.calls], ["elab/build", "elab/body"])
        self.assertIn("Blanc.Unimported", self.fake.calls[0].argv)
        self.assertEqual(self.fake.calls[1].argv, tuple(ge.RECIPES["elab"]["body"]))
        self.assertEqual(json.loads((self.root / ".lake/managed-elab-build.json").read_text())["targets"], ["Blanc", "Blanc.Unimported"])

    def test_actual_shell_certificate_option_refuses_before_work(self):
        # Real wrappers and real certificate verifier; missing certificates
        # refuse before target resolution, locks, evaluators or a nested build.
        scripts = Path(__file__).resolve().parent
        for name in ("gate-cache.py", "gate_execution.py", "gate_cache_lock.py", "gate_cache_t8n_root.py", "check-weth10-current-mainnet.sh", "check-elab.sh", "gate-lock.sh"):
            shutil.copyfile(scripts / name, self.root / "scripts" / name)
        for argv in (ge.RECIPES["weth10-current-mainnet"]["body"], ge.RECIPES["elab"]["body"]):
            result = subprocess.run(["bash", *argv], cwd=self.root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("certificate", result.stderr)
            self.assertFalse((self.root / ".lake").exists())

    def test_actual_standalone_weth_keeps_internal_build(self):
        shutil.copyfile(Path(__file__).with_name("check-weth10-current-mainnet.sh"), self.root / "scripts/check-weth10-current-mainnet.sh")
        target = self.root / "target/.venv/bin"
        target.mkdir(parents=True)
        python = target / "python"
        python.write_text("#!/bin/sh\nexit 0\n")
        python.chmod(0o755)
        binary = self.root / ".lake/packages/jaune/.lake/build/bin/jaune"
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\nexit 0\n")
        binary.chmod(0o755)
        fixtures = self.root / "scripts/fixtures/weth10-current-mainnet"
        fixtures.mkdir(parents=True)
        for index in range(3): (fixtures / f"{index}-block.json").write_text("{}")
        fakebin = self.root / "bin"
        fakebin.mkdir()
        lake = fakebin / "lake"
        log = self.root / "lake-calls"
        lake.write_text("#!/bin/sh\nprintf '%s\\n' \"$*\" >> " + str(log) + "\necho artifact\n")
        lake.chmod(0o755)
        result = subprocess.run(["bash", "scripts/check-weth10-current-mainnet.sh", "--composed-prerequisites"], cwd=self.root,
                                env={**os.environ, "PATH": str(fakebin) + os.pathsep + os.environ["PATH"], "JAUNE_T8N_TARGET": str(self.root / "target")}, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(log.read_text().splitlines().count("build jaune/jaune"), 1)
        self.assertIn("3/3 BPO2 block fixtures replayed", result.stdout)

    def test_recipe_and_protocol_changes_invalidate_evidence(self):
        self.gate["inputs"].pop("material_output")
        context = self.context()
        before, _ = gc.fingerprint(self.root, self.gate, context)
        moved = dict(self.gate, managed_execution={"recipe": "changed"})
        after, _ = gc.fingerprint(self.root, moved)
        self.assertNotEqual(before, after)
        original = gc.file_digest
        with patch.object(gc, "file_digest", side_effect=lambda path: "changed-protocol" if path.name == "gate_execution.py" else original(path)):
            moved, _ = gc.fingerprint(self.root, self.gate, context)
        self.assertNotEqual(before, moved)

    def test_requirements_never_execute_and_preserve_unrelated_prose(self):
        context = self.context()
        with patch.object(self.fake, "capture", side_effect=AssertionError("requirements ran a child")):
            first = context.requirements()
        self.assertTrue(all(row.get("identity") or row.get("estimate") for row in first))
        (self.root / "unrelated.md").write_text("prose")
        gc.forget_digests()
        second = self.context().requirements()
        self.assertEqual([row.get("identity") for row in first], [row.get("identity") for row in second])
        (self.root / "input.txt").write_text("moved")
        gc.forget_digests()
        third = self.context().requirements()
        self.assertNotEqual(first[1]["identity"], third[1]["identity"])
        self.gate["inputs"]["material_output"][0]["command"].append("changed")
        gc.forget_digests()
        fourth = self.context().requirements()
        self.assertNotEqual(third[1]["identity"], fourth[1]["identity"])
        self.assertFalse(self.fake.calls)

    def test_cost_tool_resolution_never_invokes_lake_or_lean(self):
        executable = self.root / "selected-tool"
        executable.write_bytes(b"tool bytes")
        original = ge.cost_tools
        # setUp mocks normal cost inspection; load the real implementation in
        # an isolated module to test its only permitted resolver command.
        module_spec = importlib.util.spec_from_file_location("cost_tool_control", Path(ge.__file__))
        module = importlib.util.module_from_spec(module_spec)
        self.stack.enter_context(patch.dict(sys.modules, {module_spec.name: module}))
        module_spec.loader.exec_module(module)
        calls = []
        def resolve(argv, **kwargs):
            calls.append(argv)
            self.assertEqual(argv[1], "which")
            return subprocess.CompletedProcess(argv, 0, (str(executable) + "\n").encode(), b"")
        with patch.object(module.shutil, "which", return_value="/fixture/elan"), patch.object(module.subprocess, "run", side_effect=resolve):
            module.cost_tools(self.root, ["lake", "lean"], gc)
        self.assertEqual(calls, [["/fixture/elan", "which", "lake"], ["/fixture/elan", "which", "lean"]])

    def test_requirements_imported_trace_drift_and_missing_are_visible(self):
        (self.root / "scripts/eval.lean").write_text("import Blanc.A\n")
        self.gate["inputs"]["material_output"][0]["authority"] = ["scripts/eval.lean"]
        context = self.context()
        with patch.object(gc, "module_dep_hash", return_value="one"):
            one = context.requirement("fixture/material/bytes")
        with patch.object(gc, "module_dep_hash", return_value="two"):
            two = context.requirement("fixture/material/bytes")
        self.assertNotEqual(one["identity"], two["identity"])
        with patch.object(gc, "module_dep_hash", side_effect=gc.Unresolvable("missing imported trace")):
            missing = context.requirement("fixture/material/bytes")
        self.assertIsNone(missing["identity"])
        self.assertIn("missing imported trace", missing["unresolved"])
        self.assertFalse(self.fake.calls)

    def test_integrity_cost_envelope_growth_and_authority_drift(self):
        self.prepare_modules()
        gate = {"id": "lake-build", "order": 1, "command": ["lake", "build"], "kind": "composition", "reason": "refresh", "prerequisite": True,
                "managed_execution": ge.RECIPES["lake-build"], "verdict": {"expect_exit": 0, "summary_patterns": []}}
        context = self.context([gate])
        key = "lake-build/integrity"
        initial = context.requirement(key)
        count = initial["envelope"]["cache_file_count_bound"]
        largest = initial["envelope"]["cache_largest_file_bytes_bound"]
        self.assertGreater(count, 0)
        self.assertGreater(largest, 0)
        cache = self.root / ".cache"
        (cache / "large").write_bytes(b"x" * (largest + 1))
        grown = context.requirement(key)
        self.assertNotEqual(initial["identity"], grown["identity"])
        self.assertGreater(grown["envelope"]["cache_largest_file_bytes_bound"], largest)
        (cache / "large").unlink()
        for n in range(count + 1): (cache / str(n)).write_bytes(b"x")
        self.assertGreater(context.requirement(key)["envelope"]["cache_file_count_bound"], count)
        gc.forget_digests()
        before = context.requirement(key)
        (self.root / "scripts/check-lake-artifact-cache.lean").write_text("changed checker")
        gc.forget_digests()
        self.assertNotEqual(before["identity"], context.requirement(key)["identity"])
        with patch.object(ge, "cost_tools", return_value="different toolchain"):
            self.assertNotEqual(before["identity"], context.requirement(key)["identity"])
        self.assertFalse(self.fake.calls)

    def test_missing_or_malformed_support_cannot_default(self):
        context = self.context()
        for executor in (object(), None, type("Old", (), {"version": 0, "managed": True})()):
            with self.assertRaises(ge.FatalOperationError): ge.ExecutionContext(self.root, self.registry, executor, gc)
        bad = copy.deepcopy(self.gate)
        bad["inputs"]["material_output"][0].pop("resource_class")
        with self.assertRaises(ge.FatalOperationError): self.context([bad])
        bad = dict(self.gate, managed_execution={"recipe": "shell-injection"})
        with self.assertRaises(ge.FatalOperationError): self.context([bad])


def self_test() -> int:
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ManagedTests))
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(self_test())
