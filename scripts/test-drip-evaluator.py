#!/usr/bin/env python3
"""Real shared transport/metadata logic; every compiler process is mocked."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("drip_evaluator_test_target", HERE / "drip_evaluator.py")
HELPER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HELPER)
RECEIPTS = "scripts/eval-drip-receipts.lean"
ARITHMETIC = "scripts/eval-drip-arithmetic.lean"


class EvaluatorControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="drip-evaluator-controls-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / "repo"
        self.root.mkdir()
        self.home = Path(temporary.name) / "home"
        self.home.mkdir()
        for name in HELPER.SHARED_SOURCES:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((HERE.parent / name).read_bytes())
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.1\n")
        for name in (RECEIPTS, ARITHMETIC):
            (self.root / name).write_text("import Jaune.Transaction\n-- mock entry; never elaborate\n")
        self.data = self.root / "scripts/fixture-input.json"
        self.data.write_text('{"owned":"input"}')
        self.files = ("scripts/fixture-input.json",)
        toolchain = self.home / ".elan/toolchains/leanprover--lean4---v4.32.1"
        self.lake, self.lean = (toolchain / "bin" / name for name in ("lake", "lean"))
        self.library = toolchain / "lib/lean/libleanshared.so"
        for path in (self.lake, self.lean, self.library):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("mock compiler artifact; never execute")
            path.chmod(0o755)
        self.cache = Path(temporary.name) / "cache"
        (self.cache / "artifacts").mkdir(parents=True)
        (self.cache / "artifacts/mock").write_text("presence only; not a Lake hash")
        self.trace = self.root / ".lake/packages/jaune/.lake/build/lib/lean/Jaune/Transaction.trace"
        self.trace.parent.mkdir(parents=True)
        self.trace.write_text(json.dumps({"depHash": "built-transitive-closure-A"}))
        self.package_source = self.root / ".lake/packages/jaune/Jaune/Transaction.lean"
        self.package_source.parent.mkdir(parents=True)
        self.package_source.write_text("-- mock pinned Jaune source; never elaborate\n")
        home_patch = patch.object(HELPER.Path, "home", return_value=self.home)
        home_patch.start()
        self.addCleanup(home_patch.stop)
        environment_patch = patch.dict(os.environ, {
            "LAKE_CACHE_DIR": str(self.cache), "PATH": "/unreviewed/path",
            "LEAN_PATH": "/unreviewed/imports", "ELAN_TOOLCHAIN": "unreviewed",
        })
        environment_patch.start()
        self.addCleanup(environment_patch.stop)
        self.child = patch.object(HELPER.subprocess, "run",
                                 return_value=subprocess.CompletedProcess([], 0, "checked output", ""))
        self.run_mock = self.child.start()
        self.addCleanup(self.child.stop)
        self.checks = []
        self.identity = HELPER.snapshot(self.root, RECEIPTS, self.files)

    def check(self):
        HELPER.assert_unchanged(self.root, RECEIPTS, self.files, self.identity)
        self.checks.append("checked")

    def invoke(self):
        return HELPER.evaluate(self.root, RECEIPTS, '{"schema":1}', self.check)

    def test_receipt_absolute_dispatch_and_environment(self):
        self.assertEqual(self.invoke(), "checked output")
        args, kwargs = self.run_mock.call_args
        self.assertEqual(args[0], [str(self.lake), "env", str(self.lean), "--run", RECEIPTS])
        self.assertEqual(kwargs["input"], '{"schema":1}\n')
        self.assertEqual(kwargs["cwd"], self.root)
        self.assertEqual(kwargs["env"], {
            "HOME": str(self.home), "PATH": str(self.lake.parent) + os.pathsep + os.defpath,
            "LANG": "C.UTF-8", "LAKE_CACHE_DIR": str(self.cache),
        })
        self.assertEqual(set(kwargs), {"cwd", "input", "capture_output", "text", "check", "env"})
        self.assertTrue(kwargs["capture_output"] and kwargs["text"])
        self.assertFalse(kwargs["check"])
        self.assertEqual(self.checks, ["checked", "checked"])

    def test_arithmetic_mode_has_no_run_flag_or_input_payload(self):
        checks = []
        self.assertEqual(HELPER.evaluate(self.root, ARITHMETIC, None,
                                        lambda: checks.append(1)), "checked output")
        args, kwargs = self.run_mock.call_args
        self.assertEqual(args[0], [str(self.lake), "env", str(self.lean), ARITHMETIC])
        self.assertNotIn("input", kwargs)
        self.assertEqual(checks, [1, 1])

    def test_no_arbitrary_evaluator_or_mode(self):
        for entry, request in [("scripts/other.lean", None), ("/bin/sh", None),
                               (ARITHMETIC, "override"), (RECEIPTS, None)]:
            with self.subTest(entry=entry, request=request), self.assertRaises(HELPER.HelperError):
                HELPER.evaluate(self.root, entry, request, lambda: None)
        self.run_mock.assert_not_called()
        self.invoke()

    def test_missing_shared_sources_entry_or_trace_never_dispatch(self):
        for path in [self.root / "scripts/drip_evaluator.py", self.root / "scripts/gate-cache.py",
                     self.root / "scripts/gate_cache_lock.py", self.root / RECEIPTS, self.trace]:
            original = path.read_bytes()
            path.unlink()
            with self.subTest(path=path), self.assertRaises((HELPER.HelperError, OSError)):
                self.invoke()
            self.run_mock.assert_not_called()
            path.write_bytes(original)
            HELPER.assert_unchanged(self.root, RECEIPTS, self.files, self.identity)

    def test_cache_prerequisites_fail_before_dispatch(self):
        empty = self.cache.parent / "empty-cache"
        empty.mkdir()
        for value in ["", "relative", str(self.cache.parent / "missing"), str(empty)]:
            with patch.dict(os.environ, {"LAKE_CACHE_DIR": value}), self.subTest(value=value), \
                    self.assertRaises((HELPER.HelperError, OSError)):
                self.invoke()
            self.run_mock.assert_not_called()
        self.invoke()

    def test_cache_normalization_and_environment_drift(self):
        alias = self.cache / "artifacts" / ".."
        with patch.dict(os.environ, {"LAKE_CACHE_DIR": str(alias)}):
            self.assertEqual(HELPER.evaluator_environment(self.root)["LAKE_CACHE_DIR"], str(self.cache))
        alternate = self.cache.parent / "alternate-cache"
        (alternate / "artifacts").mkdir(parents=True)
        (alternate / "artifacts/mock").write_text("presence")
        with patch.dict(os.environ, {"LAKE_CACHE_DIR": str(alternate)}), \
                self.assertRaisesRegex(HELPER.HelperError, "snapshot drift"):
            self.invoke()
        self.run_mock.assert_not_called()
        self.invoke()

    def test_metadata_corruption_and_import_changes_restore(self):
        original = self.trace.read_text()
        for data in ["{", "{}", '{"depHash":true}', '{"depHash":""}']:
            self.trace.write_text(data)
            with self.subTest(data=data), self.assertRaisesRegex(HELPER.HelperError, "import metadata"):
                self.invoke()
            self.run_mock.assert_not_called()
            self.trace.write_text(original)
            HELPER.assert_unchanged(self.root, RECEIPTS, self.files, self.identity)
        self.trace.write_text('{"depHash":"rebuilt-transitive-closure-B"}')
        with self.assertRaisesRegex(HELPER.HelperError, "snapshot drift"):
            self.invoke()
        self.run_mock.assert_not_called()
        self.trace.write_text(original)
        self.invoke()

    def test_unparsable_or_new_unbuilt_import_never_dispatch(self):
        entry = self.root / RECEIPTS
        original = entry.read_text()
        for text in ["import Jaune.Transaction -- not supported by existing parser\n",
                     "import Jaune.Unbuilt\n"]:
            entry.write_text(text)
            with self.subTest(text=text), self.assertRaisesRegex(HELPER.HelperError, "import metadata"):
                self.invoke()
            self.run_mock.assert_not_called()
        entry.write_text(original)
        self.invoke()

    def test_jaune_source_discovery_and_symlink_drift_without_trace_change(self):
        original = self.package_source.read_bytes()
        trace = self.trace.read_bytes()
        self.package_source.write_bytes(original + b"-- source changed without a build\n")
        with self.assertRaisesRegex(HELPER.HelperError, "snapshot drift"):
            self.invoke()
        self.assertEqual(self.trace.read_bytes(), trace)
        self.run_mock.assert_not_called()
        self.package_source.write_bytes(original)
        HELPER.assert_unchanged(self.root, RECEIPTS, self.files, self.identity)
        extra = self.package_source.with_name("Added.lean")
        extra.write_text("-- discovered source; unchanged trace\n")
        with self.assertRaisesRegex(HELPER.HelperError, "snapshot drift"):
            self.invoke()
        self.run_mock.assert_not_called()
        extra.unlink()
        self.package_source.unlink()
        with self.assertRaisesRegex(HELPER.HelperError, "Jaune sources missing"):
            self.invoke()
        self.run_mock.assert_not_called()
        saved = self.package_source.with_suffix(".saved")
        saved.write_bytes(original)
        self.package_source.symlink_to(saved)
        with self.assertRaisesRegex(HELPER.HelperError, "regular file"):
            self.invoke()
        self.run_mock.assert_not_called()
        self.package_source.unlink()
        self.package_source.write_bytes(original)
        package = self.root / ".lake/packages/jaune"
        saved_package = package.with_name("jaune-saved")
        package.rename(saved_package)
        package.symlink_to(saved_package, target_is_directory=True)
        with self.assertRaisesRegex(HELPER.HelperError, "package missing or symlink"):
            self.invoke()
        self.run_mock.assert_not_called()
        package.unlink()
        saved_package.rename(package)
        self.assertEqual(self.trace.read_bytes(), trace)
        self.invoke()

    def test_source_compiler_and_input_drift_during_child(self):
        for path in [self.root / "scripts/drip_evaluator.py", self.root / "scripts/gate-cache.py",
                     self.root / "scripts/gate_cache_t8n_root.py", self.root / RECEIPTS,
                     self.lake, self.lean, self.library, self.data, self.trace]:
            original = path.read_bytes()
            def changed(*args, path=path, original=original, **kwargs):
                path.write_bytes(original + b" ")
                if path == self.trace:
                    path.write_text('{"depHash":"changed"}')
                return subprocess.CompletedProcess(args[0], 0, "checked output", "")
            self.run_mock.side_effect = changed
            with self.subTest(path=path), self.assertRaisesRegex(HELPER.HelperError, "snapshot drift"):
                self.invoke()
            path.write_bytes(original)
            self.run_mock.side_effect = None
            self.invoke()

    def test_callback_failure_before_and_after_child(self):
        def denied():
            raise ValueError("caller input drift")
        with self.assertRaisesRegex(ValueError, "caller input drift"):
            HELPER.evaluate(self.root, RECEIPTS, "{}", denied)
        self.run_mock.assert_not_called()
        checks = []
        def changed_after():
            checks.append(1)
            if len(checks) == 2:
                raise ValueError("caller input drift")
        with self.assertRaisesRegex(ValueError, "caller input drift"):
            HELPER.evaluate(self.root, RECEIPTS, "{}", changed_after)
        self.assertEqual(checks, [1, 1])
        self.assertEqual(self.run_mock.call_count, 1)
        self.invoke()

    def test_child_exit_diagnostics_and_launch_exception(self):
        for code, stderr, error in [(7, "failed", "exit 7"), (0, "warning", "diagnostics")]:
            self.run_mock.return_value = subprocess.CompletedProcess([], code, "prefix", stderr)
            self.checks.clear()
            with self.subTest(code=code, stderr=stderr), self.assertRaisesRegex(HELPER.HelperError, error):
                self.invoke()
            self.assertEqual(self.checks, ["checked", "checked"])
        self.run_mock.side_effect = OSError("mock launch failure")
        self.checks.clear()
        with self.assertRaisesRegex(OSError, "mock launch failure"):
            self.invoke()
        self.assertEqual(self.checks, ["checked", "checked"])
        self.run_mock.side_effect = None
        self.run_mock.return_value = subprocess.CompletedProcess([], 0, "checked output", "")
        self.invoke()

    def test_source_paths_and_compiler_prerequisites(self):
        for files in ["scripts/fixture-input.json", ("../outside",), ("/outside",)]:
            with self.subTest(files=files), self.assertRaises(HELPER.HelperError):
                HELPER.snapshot(self.root, RECEIPTS, files)
        self.lean.chmod(0o644)
        with self.assertRaisesRegex(HELPER.HelperError, "not executable"):
            self.invoke()
        self.lean.chmod(0o755)
        old = self.library.read_bytes()
        self.library.unlink()
        with self.assertRaisesRegex(HELPER.HelperError, "shared libraries missing"):
            self.invoke()
        self.library.write_bytes(old)
        self.run_mock.assert_not_called()
        self.invoke()

    def test_snapshot_order_and_explicit_artifact_integrity_boundary(self):
        self.assertEqual(self.identity, HELPER.snapshot(self.root, RECEIPTS, self.files * 2))
        self.assertIsInstance(self.identity, tuple)
        details = dict(self.identity)
        self.assertEqual(details["lean-entry:" + RECEIPTS + "::import::Jaune.Transaction"],
                         "built-transitive-closure-A")
        # Deliberately unchanged metadata does not authenticate compiled bytes.
        # The owned artifact-integrity gate must reject this independent class.
        compiled = self.trace.with_suffix(".olean")
        compiled.write_text("mock artifact A")
        self.assertEqual(self.identity, HELPER.snapshot(self.root, RECEIPTS, self.files))
        compiled.write_text("corrupted mock artifact B")
        self.assertEqual(self.identity, HELPER.snapshot(self.root, RECEIPTS, self.files))
        self.run_mock.assert_not_called()


if __name__ == "__main__":
    unittest.main(verbosity=2)
