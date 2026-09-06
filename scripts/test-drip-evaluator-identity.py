#!/usr/bin/env python3
"""Identity projection controls on fake compiler/cache/import fixtures only."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FIXTURE = load("identity_fixture", "test-drip-evaluator.py")
IDENTITY = load("identity_target", "drip-evaluator-identity.py")


class IdentityControls(unittest.TestCase):
    def setUp(self):
        # Reuse its real shared metadata logic and temporary mock artifacts;
        # no inherited transport test invokes a fake compiler subprocess.
        FIXTURE.EvaluatorControls.setUp(self)
        self.run_mock.side_effect = AssertionError("identity must not launch any process")
        for mode in IDENTITY.MODES:
            driver = IDENTITY.load_driver(mode)
            for name in (*driver.SOURCE_FILES, IDENTITY.MODES[mode], IDENTITY.SELF):
                target = self.root / name
                if not target.exists():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes((HERE.parent / name).read_bytes())
        for name in ("scripts/check-drip-fixtures.py", "scripts/drip_fixture_observers.py"):
            (self.root / name).write_bytes((HERE.parent / name).read_bytes())
        self.enterContext(patch.object(IDENTITY, "ROOT", self.root))
        self.enterContext(patch.object(IDENTITY, "HELPER", FIXTURE.HELPER))
        self.enterContext(patch.object(FIXTURE.HELPER, "evaluate",
                                      side_effect=AssertionError("no evaluation")))

    def invoke(self, args):
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = IDENTITY.main(args)
        self.run_mock.assert_not_called()
        return code, stdout.getvalue(), stderr.getvalue()

    def good(self, mode="arithmetic"):
        code, output, diagnostic = self.invoke([mode])
        self.assertEqual((code, diagnostic), (0, ""))
        self.assertEqual(output.count("\n"), 1)
        return output

    def test_both_fixed_modes_stable_without_evaluation(self):
        for mode in IDENTITY.MODES:
            output = self.good(mode)
            self.assertEqual(output, self.good(mode))
            data = json.loads(output)
            self.assertEqual(set(data), {"schema", "kind", "mode", "evaluator", "identity"})
            self.assertEqual(data["schema"], 1)
            self.assertEqual(data["mode"], mode)
            self.assertIn("source:" + IDENTITY.SELF, data["identity"])
            self.assertIn("source:" + IDENTITY.MODES[mode], data["identity"])
            with patch.object(IDENTITY, "load_driver", wraps=IDENTITY.load_driver) as loader:
                self.good(mode)
                loader.assert_called_once_with(mode)

    def test_arguments_rejected_before_snapshot(self):
        with patch.object(FIXTURE.HELPER, "snapshot", side_effect=AssertionError("no snapshot")):
            for args in [[], ["other"], ["arithmetic", "extra"], ["--root", "/tmp"],
                         ["receipts", "--write"], ["/bin/sh"]]:
                code, out, err = self.invoke(args)
                self.assertEqual((code, out), (2, ""))
                self.assertIn("usage:", err)

    def test_compiler_bytes_move_identity_without_version_change(self):
        before = self.good()
        version = (self.root / "lean-toolchain").read_bytes()
        for path in (self.lake, self.lean, self.library):
            old = path.read_bytes()
            path.write_bytes(old + b" changed byte")
            self.assertNotEqual(before, self.good())
            self.assertEqual((self.root / "lean-toolchain").read_bytes(), version)
            path.write_bytes(old)
            self.assertEqual(before, self.good())

    def test_sources_import_metadata_and_discovery_move_identity(self):
        before = self.good()
        for path in (self.package_source, self.root / IDENTITY.SELF,
                     self.root / "scripts/drip-oracle-vectors.json", self.trace):
            old = path.read_bytes()
            path.write_bytes(b'{"depHash":"changed"}' if path == self.trace else old+b"\n")
            self.assertNotEqual(before, self.good())
            path.write_bytes(old)
            self.assertEqual(before, self.good())
        extra = self.package_source.with_name("Discovered.lean")
        extra.write_text("-- current source discovery\n")
        self.assertNotEqual(before, self.good())
        extra.unlink()
        self.assertEqual(before, self.good())
        entry = self.root / FIXTURE.ARITHMETIC
        old = entry.read_bytes()
        (self.package_source.parent / "Extra.lean").write_text("-- mock\n")
        self.trace.with_name("Extra.trace").write_text('{"depHash":"extra"}')
        with_extra = self.good()
        entry.write_text("import Jaune.Transaction\nimport Jaune.Extra\n")
        self.assertNotEqual(with_extra, self.good())
        entry.write_bytes(old)
        self.assertEqual(with_extra, self.good())

    def test_cache_environment_normalization_and_change(self):
        before = self.good()
        with patch.dict(os.environ, {"LAKE_CACHE_DIR": str(self.cache / "artifacts/..")}):
            self.assertEqual(before, self.good())
        alternate = self.cache.parent / "alternate"
        (alternate / "artifacts").mkdir(parents=True)
        (alternate / "artifacts/mock").write_text("presence")
        with patch.dict(os.environ, {"LAKE_CACHE_DIR": str(alternate)}):
            self.assertNotEqual(before, self.good())
        self.assertEqual(before, self.good())

    def test_missing_prerequisites_fail_without_output_and_restore(self):
        before = self.good()
        for path in (self.root / FIXTURE.ARITHMETIC, self.lean, self.library,
                     self.trace, self.cache / "artifacts/mock"):
            old = path.read_bytes()
            path.unlink()
            code, out, err = self.invoke(["arithmetic"])
            self.assertEqual((code, out), (1, ""))
            self.assertIn("REGRESSION", err)
            path.write_bytes(old)
            if path == self.lean:
                path.chmod(0o755)
            self.assertEqual(before, self.good())
        old = self.trace.read_bytes()
        self.trace.write_text('{"depHash":true}')
        self.assertEqual(self.invoke(["arithmetic"])[:2], (1, ""))
        self.trace.write_bytes(old)
        self.assertEqual(before, self.good())

    def test_drift_during_projection_rejected_then_restored(self):
        before = self.good()
        real = FIXTURE.HELPER.assert_unchanged
        for path in (self.lean, self.package_source, self.trace):
            old = path.read_bytes()
            def drift(*args, path=path, old=old):
                path.write_bytes(b'{"depHash":"drift"}' if path == self.trace else old+b"x")
                return real(*args)
            with patch.object(FIXTURE.HELPER, "assert_unchanged", side_effect=drift):
                code, out, err = self.invoke(["arithmetic"])
            self.assertEqual((code, out), (1, ""))
            self.assertIn("snapshot drift", err)
            path.write_bytes(old)
            self.assertEqual(before, self.good())

    def test_driver_change_during_import_is_rejected(self):
        before = self.good()
        path = self.root / IDENTITY.MODES["arithmetic"]
        old = path.read_bytes()
        real = IDENTITY.load_driver
        def changed(mode):
            driver = real(mode)
            path.write_bytes(old+b"\n")
            return driver
        with patch.object(IDENTITY, "load_driver", side_effect=changed):
            code, out, err = self.invoke(["arithmetic"])
        self.assertEqual((code, out), (1, ""))
        self.assertIn("driver changed", err)
        path.write_bytes(old)
        self.assertEqual(before, self.good())

    def test_receipts_does_not_read_or_authenticate_fixtures(self):
        self.assertFalse((self.root / "scripts/fixtures/drip").exists())
        driver = IDENTITY.load_driver("receipts")
        with patch.object(driver, "prepare_batch", side_effect=AssertionError("no prepare")), \
                patch.object(driver, "authenticate_batch", side_effect=AssertionError("no auth")), \
                patch.object(IDENTITY, "load_driver", return_value=driver):
            self.good("receipts")


if __name__ == "__main__":
    unittest.main(verbosity=2)
