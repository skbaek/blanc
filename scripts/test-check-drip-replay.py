#!/usr/bin/env python3
"""Mocked replay controls: synthetic JSON never reaches an actual EVM."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


REPLAY = load("drip_replay_test_target", HERE / "check-drip-replay.py")
FIXTURES = load("drip_replay_synthetic", HERE / "test-check-drip-fixtures.py")


class ReplayControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="drip-replay-control-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.directory = self.root / "fixtures"
        self.directory.mkdir()
        FIXTURES.population(self.directory)
        self.original = {p.name: p.read_bytes() for p in self.directory.iterdir()}
        self.runner = self.root / "runner"
        self.runner.write_bytes(b"mock-only; never execute")
        self.identity = (self.runner, "0" * 40, REPLAY.digest(self.runner))
        self.calls = []
        self.child_failure = False
        self.bad_selection = False

    def child(self, argv, **kwargs):
        self.assertEqual(argv[0], str(self.runner))
        self.assertEqual(argv[2:], ["--network", "BPO2"])
        self.assertEqual(kwargs, dict(cwd=REPLAY.ROOT, capture_output=True,
                                     text=True, check=False))
        path = Path(argv[1])
        self.assertEqual(path.parent, self.directory)
        self.calls.append(path.name)
        name = path.stem
        selected = 0 if self.bad_selection else 1
        stdout = (f"SELECTED CASES : {selected}\nSKIPPED CASES : 0\n"
                  f"TEST NAME : blanc/drip::{name}[fork_BPO2-blockchain_test]\n")
        return subprocess.CompletedProcess(argv, 7 if self.child_failure else 0,
                                           stdout, "")

    def run_mocked(self):
        with patch.object(REPLAY, "pinned_runner", return_value=self.identity), \
             patch.object(REPLAY.subprocess, "run", side_effect=self.child), \
             contextlib.redirect_stdout(io.StringIO()), \
             contextlib.redirect_stderr(io.StringIO()):
            return REPLAY.replay(self.directory)

    def restore(self):
        for p in self.directory.iterdir():
            if p.is_dir():
                for child in p.iterdir():
                    child.unlink()
                p.rmdir()
            else:
                p.unlink()
        for name, data in self.original.items():
            (self.directory / name).write_bytes(data)

    def assert_green(self):
        self.calls.clear()
        self.assertEqual(self.run_mocked(), (91, 137))
        expected = sorted(set(self.original) - {"manifest.json"})
        self.assertEqual(self.calls, expected)

    def mutate_json(self, filename, mutate):
        path = self.directory / filename
        data = json.loads(path.read_text())
        mutate(data)
        path.write_text(json.dumps(data))

    def control(self, boundary, mutate):
        self.assert_green()
        mutate()
        self.calls.clear()
        with self.assertRaisesRegex(REPLAY.ReplayError, boundary):
            self.run_mocked()
        self.assertEqual(self.calls, [], "structural refusal must precede dispatch")
        self.restore()
        self.assert_green()

    def test_complete_exact_dispatch(self):
        self.assert_green()

    def test_missing(self):
        self.control("fixture population mismatch", lambda:
                     (self.directory / "drip-one-year.json").unlink())

    def test_extra(self):
        self.control("fixture population mismatch", lambda:
                     (self.directory / "extra.json").write_text("{}"))

    def test_nested_discovery(self):
        def mutate():
            nested = self.directory / "nested"
            nested.mkdir()
            (nested / "orphan.json").write_text("{}")
        self.control("fixture discovery", mutate)

    def test_duplicate(self):
        self.control("duplicate case name", lambda: self.mutate_json("manifest.json",
                     lambda d: d["cases"].append(d["cases"][0])))

    def test_manifest_omission(self):
        self.control("unknown case file", lambda: self.mutate_json("manifest.json",
                     lambda d: d["cases"].pop()))

    def test_runtime_literal_mismatch(self):
        self.control("runtime identity differs", lambda: self.mutate_json("manifest.json",
                     lambda d: d.update(runtimeSha256="0" * 64)))

    def test_unsupported_schema(self):
        self.control("unsupported schema/kind", lambda: self.mutate_json("manifest.json",
                     lambda d: d.update(schema=3)))

    def test_network(self):
        self.control("non-BPO2", lambda: self.mutate_json("drip-one-year.json",
                     lambda d: next(iter(d.values())).update(network="Prague")))

    def test_child_failure_and_restore(self):
        self.assert_green()
        self.child_failure = True
        self.calls.clear()
        with self.assertRaisesRegex(REPLAY.ReplayError, "Jaune exit 7"):
            self.run_mocked()
        self.assertEqual(len(self.calls), 1)
        self.child_failure = False
        self.assert_green()

    def test_zero_selected_and_restore(self):
        self.assert_green()
        self.bad_selection = True
        with self.assertRaisesRegex(REPLAY.ReplayError, "case selection/verdict coverage"):
            self.run_mocked()
        self.bad_selection = False
        self.assert_green()

    def test_absent_runner(self):
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "jaune", "type": "git", "rev": "0" * 40}]}))
        with patch.object(REPLAY, "ROOT", self.root), \
             patch.object(REPLAY.subprocess, "run") as child:
            with self.assertRaisesRegex(REPLAY.ReplayError, "executable absent"):
                REPLAY.pinned_runner()
            child.assert_not_called()

    def test_pin_and_dirty_rejections_restore(self):
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "jaune", "type": "git", "rev": "0" * 40}]}))
        binary = self.root / ".lake/packages/jaune/.lake/build/bin/jaune"
        binary.parent.mkdir(parents=True)
        binary.write_bytes(b"mock only")
        binary.chmod(0o700)
        pin = "0" * 40
        dirty = ""

        def git(argv, **kwargs):
            self.assertEqual(argv[:3], ["git", "-C", str(self.root / ".lake/packages/jaune")])
            self.assertTrue(kwargs["check"])
            if argv[3:] == ["rev-parse", "HEAD"]:
                return subprocess.CompletedProcess(argv, 0, pin + "\n", "")
            self.assertEqual(argv[3:], ["status", "--porcelain", "--untracked-files=no"])
            return subprocess.CompletedProcess(argv, 0, dirty, "")

        with patch.object(REPLAY, "ROOT", self.root), \
             patch.object(REPLAY.subprocess, "run", side_effect=git):
            expected = REPLAY.pinned_runner()
            pin = "1" * 40
            with self.assertRaisesRegex(REPLAY.ReplayError, "differs from Lake Git pin"):
                REPLAY.pinned_runner()
            pin = "0" * 40
            self.assertEqual(REPLAY.pinned_runner(), expected)
            dirty = " M Main.lean\n"
            with self.assertRaisesRegex(REPLAY.ReplayError, "source is dirty"):
                REPLAY.pinned_runner()
            dirty = ""
            self.assertEqual(REPLAY.pinned_runner(), expected)

    def test_fixture_drift_during_dispatch_restore(self):
        self.assert_green()
        original_child = self.child

        def drifting(argv, **kwargs):
            result = original_child(argv, **kwargs)
            (self.directory / "drip-one-year.json").write_text("{}")
            return result

        with patch.object(self, "child", side_effect=drifting):
            with self.assertRaisesRegex(REPLAY.ReplayError, "fixture drift before dispatch"):
                self.run_mocked()
        self.restore()
        self.assert_green()

    def test_runner_drift_during_dispatch_restore(self):
        self.assert_green()
        original_child = self.child

        def drifting(argv, **kwargs):
            result = original_child(argv, **kwargs)
            self.runner.write_bytes(b"changed mocked binary")
            return result

        with patch.object(self, "child", side_effect=drifting):
            with self.assertRaisesRegex(REPLAY.ReplayError, "runner binary drift"):
                self.run_mocked()
        self.runner.write_bytes(b"mock-only; never execute")
        self.assert_green()

    def test_no_cli_override(self):
        with patch.object(REPLAY, "replay") as replay, \
             contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(REPLAY.main(["--runner", "/tmp/other"]), 2)
            replay.assert_not_called()


if __name__ == "__main__":
    unittest.main()
