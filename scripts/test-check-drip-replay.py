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
PROTOCOL = load("drip_replay_receipt_protocol", HERE / "test-drip-receipts.py")


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
        # Existing native/structural controls isolate the new receipt boundary.
        batch = REPLAY.RECEIPTS.ReceiptBatch(self.directory, "{}",
                    tuple(sorted(REPLAY.population(self.directory).items())), ())
        with patch.object(REPLAY.RECEIPTS, "prepare_batch", return_value=batch), \
             patch.object(REPLAY.RECEIPTS, "authenticate_batch", return_value={}), \
             patch.object(REPLAY.RECEIPTS, "assert_unchanged"), \
             patch.object(REPLAY, "pinned_runner", return_value=self.identity), \
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
            with self.assertRaisesRegex(REPLAY.ReplayError, "fixture drift during execution"):
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


class ReceiptBindingControls(unittest.TestCase):
    """Real receipt prepare/validate/snapshot hooks; both child kinds are mocked."""
    def setUp(self):
        PROTOCOL.ReceiptProtocolControls.setUp(self)
        self.enterContext(patch.object(REPLAY, "ROOT", self.root))
        self.enterContext(patch.object(REPLAY, "RECEIPTS", PROTOCOL.DRIVER))
        self.enterContext(patch.object(REPLAY.VERIFIER, "literals",
                                      return_value=(b"\x00", b"\x60\x01\x00")))
        self.runner = self.root / "mock-native-runner"
        self.runner.write_bytes(b"mock native bytes; never execute")
        self.runner_identity = (self.runner, "0"*40, REPLAY.digest(self.runner))
        self.native_calls = []
        self.events = []
        self.mutate_native = lambda: None
        self.native_exception = False
        self.native_returncode = 0
        self.eval_returncode = 0
        self.native_diagnostic = ""

    def child(self, argv, **kwargs):
        # This single mocked boundary intercepts helper and native subprocesses.
        if argv[0] == str(self.compiler):
            self.assertEqual(argv, [str(self.compiler), "env", str(self.lean),
                                   "--run", PROTOCOL.DRIVER.EVALUATOR])
            self.events.append("authenticate")
            response = PROTOCOL.mock_response(json.loads(kwargs["input"]))
            return subprocess.CompletedProcess(argv, self.eval_returncode,
                                               json.dumps(response), "")
        self.assertEqual(argv[0], str(self.runner))
        self.assertEqual(argv[2:], ["--network", "BPO2"])
        self.assertEqual(kwargs, dict(cwd=self.root, capture_output=True, text=True, check=False))
        self.assertIn("authenticate", self.events)
        path = Path(argv[1])
        self.assertEqual(path.parent, self.directory)
        self.native_calls.append(path.name)
        self.events.append("native")
        self.mutate_native()
        if self.native_exception:
            raise OSError("mock native launch exception")
        out = ("SELECTED CASES : 1\nSKIPPED CASES : 0\n"
               f"TEST NAME : blanc/drip::{path.stem}[fork_BPO2-blockchain_test]\n")
        return subprocess.CompletedProcess(argv, self.native_returncode,
                                           out+self.native_diagnostic, self.native_diagnostic)

    def invoke(self):
        self.native_calls.clear(); self.events.clear()
        driver = REPLAY.RECEIPTS
        real_prepare, real_check = driver.prepare_batch, driver.assert_unchanged
        prepared, checked = [], []
        def prepare(directory):
            batch = real_prepare(directory)
            prepared.append(batch)
            return batch
        def unchanged(batch):
            if prepared:
                self.assertIs(batch, prepared[0], "authenticated batch replaced")
            checked.append(batch)
            self.events.append("check")
            return real_check(batch)
        stdout, stderr = io.StringIO(), io.StringIO()
        with patch.object(driver, "prepare_batch", side_effect=prepare) as preparation, \
             patch.object(driver, "assert_unchanged", side_effect=unchanged), \
             patch.object(driver, "authenticate_batch", wraps=driver.authenticate_batch) as authentication, \
             patch.object(REPLAY, "pinned_runner", return_value=self.runner_identity), \
             patch.object(REPLAY.subprocess, "run", side_effect=self.child), \
             contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = REPLAY.main([])
        self.assertEqual(preparation.call_count, 1)
        if authentication.call_count:
            self.assertEqual(authentication.call_count, 1)
            self.assertIs(authentication.call_args.args[0], prepared[0])
            self.assertTrue(all(batch is prepared[0] for batch in checked))
        self.output, self.error = stdout.getvalue(), stderr.getvalue()
        if code:
            self.assertNotIn("OK — DRIP replay:", self.output)
        return code

    def green(self):
        self.assertEqual(self.invoke(), 0, self.error)
        self.assertEqual(self.native_calls, sorted(p.name for p in self.directory.glob("*.json")
                                                 if p.name != "manifest.json"))
        self.assertEqual(len(self.native_calls), 91)
        self.assertEqual(self.events.count("authenticate"), 1)
        self.assertEqual(self.events[-1], "check")
        self.assertEqual(self.output.count("OK — DRIP replay:"), 1)
        receipts = [line.removeprefix("DRIP_RECEIPTS ") for line in self.output.splitlines()
                    if line.startswith("DRIP_RECEIPTS ")]
        self.assertEqual(len(receipts), 1)
        self.assertEqual(json.loads(receipts[0])["done"], "drip-receipts-v1-complete")

    def test_one_batch_authenticates_before_all_native_calls(self):
        self.green()

    def test_missing_evaluator_blocks_all_dispatch_then_restore(self):
        path = self.root / PROTOCOL.DRIVER.EVALUATOR
        old = path.read_bytes(); path.unlink()
        self.assertEqual(self.invoke(), 1)
        self.assertIn("receipt binding: receipt evaluator missing", self.error)
        self.assertNotIn("authenticate", self.events)
        self.assertEqual(self.native_calls, [])
        path.write_bytes(old)
        self.green()

    def test_authentication_failure_blocks_native_then_restore(self):
        self.eval_returncode = 7
        self.assertEqual(self.invoke(), 1)
        self.assertIn("evaluator exit 7", self.error)
        self.assertEqual(self.native_calls, [])
        self.assertEqual(self.events[-1], "check")
        self.eval_returncode = 0
        self.green()

    def test_after_authentication_fixture_and_caller_drift_restore(self):
        driver = REPLAY.RECEIPTS
        real = driver.authenticate_batch
        for path in (self.directory / "drip-one-year.json",
                     self.root / "scripts/check-drip-replay.py"):
            old = path.read_bytes()
            def changed(batch, path=path, old=old):
                result = real(batch)
                path.write_bytes(old+b" ")
                return result
            with patch.object(driver, "authenticate_batch", side_effect=changed):
                self.assertEqual(self.invoke(), 1)
            self.assertIn("snapshot drift", self.error)
            self.assertEqual(self.native_calls, [])
            path.write_bytes(old)
            self.green()

    def test_during_first_and_last_native_drift_restore(self):
        for index, path in ((1, self.directory / "drip-one-year.json"),
                            (1, self.root / "scripts/check-drip-replay.py"),
                            (91, self.lean)):
            old = path.read_bytes()
            def changed(index=index, path=path, old=old):
                if len(self.native_calls) == index:
                    path.write_bytes(old+b" ")
            self.mutate_native = changed
            self.assertEqual(self.invoke(), 1)
            self.assertIn("snapshot drift", self.error)
            self.assertEqual(len(self.native_calls), index)
            self.mutate_native = lambda: None
            path.write_bytes(old)
            self.green()

    def test_native_exception_and_nonzero_exit_final_check_restore(self):
        for attribute in ("native_exception", "native_returncode"):
            setattr(self, attribute, True if attribute == "native_exception" else 7)
            self.assertEqual(self.invoke(), 1)
            self.assertEqual(len(self.native_calls), 1)
            self.assertEqual(self.events[-1], "check")
            setattr(self, attribute, False if attribute == "native_exception" else 0)
            self.green()

    def test_completed_native_diagnostics_survive_drift_refusal(self):
        path = self.root / "scripts/check-drip-replay.py"
        original = path.read_bytes()
        self.native_diagnostic = "mock native diagnostic retained\n"
        self.mutate_native = lambda: path.write_bytes(original+b" ")
        self.assertEqual(self.invoke(), 1)
        self.assertIn(self.native_diagnostic, self.output)
        self.assertIn(self.native_diagnostic, self.error)
        self.assertNotIn("PASS — DRIP replay:", self.output)
        self.assertIn("snapshot drift", self.error)
        path.write_bytes(original)
        self.mutate_native = lambda: None
        self.native_diagnostic = ""
        self.green()

    def test_population_mismatch_prevents_authentication(self):
        driver = REPLAY.RECEIPTS
        real = driver.prepare_batch
        def changed(directory):
            batch = real(directory)
            return batch._replace(files=batch.files[:-1])
        with patch.object(driver, "prepare_batch", side_effect=changed):
            self.assertEqual(self.invoke(), 1)
        self.assertEqual(self.native_calls, [])
        self.assertNotIn("authenticate", self.events)
        self.green()


if __name__ == "__main__":
    unittest.main()
