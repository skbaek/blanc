"""Exact incomplete-run controls using disposable shell/Python gates; no Lean."""
from __future__ import annotations

import contextlib
import copy
import io
import json
from pathlib import Path
import subprocess
import unittest
from unittest import mock

from gate_cache_selftest import gc, gate_semaphore, scratch, simple_gate


class ElabDeferralTest(unittest.TestCase):
    def setUp(self):
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.s = self.stack.enter_context(scratch())
        self.stack.enter_context(mock.patch.object(gc, "ROOT", self.s.root))
        self.stack.enter_context(mock.patch.object(gc, "host_identity", return_value="fixture-host"))
        self.stack.enter_context(mock.patch.object(gate_semaphore, "ENTRY", self.s.coordination.entry))
        self.certificate = self.stack.enter_context(mock.patch.object(
            gc, "build_certificate_status", return_value=(True, "fixture exact certificate", {"fixture": "current"})))
        self.s.write(".gitignore", ".lake/\n*.ran\n")
        self.s.write("payload.txt", "one\n")
        build = self.s.passing_gate("build.sh", "build.ran")
        static = self.s.passing_gate("static.sh", "static.ran")
        elab = self.s.passing_gate("check-elab.sh", "elab.ran")
        self.s.write("scripts/test-elab-migration-comparison.py",
                     "from pathlib import Path\nPath('comparator.ran').write_text('ran\\n')\n"
                     "print('OK — comparator: synthetic controls')\n")
        self.gates = [
            {"id": "lake-build", "order": 1, "command": [build], "kind": "composition",
             "prerequisite": True, "reason": "synthetic authoritative build", "inputs": {},
             "verdict": {"expect_exit": 0, "summary_patterns": ["^OK — build.sh: "]}},
            simple_gate("static", [static], {"files": [static, "payload.txt"]}, "^OK — static.sh: ", 2),
            simple_gate("elab", [elab, "--no-build"],
                        {"files": [elab, "scripts/baseline-elab.txt"]}, "^OK — check-elab.sh: ", 3),
            simple_gate("elab-migration-comparison-controls",
                        ["python3", "-B", "scripts/test-elab-migration-comparison.py"],
                        {"files": ["scripts/test-elab-migration-comparison.py"]}, "^OK — comparator: ", 4),
        ]
        self.s.registry(self.gates)
        self.s.git_init()
        self.output = ""

    def invoke(self, *flags, mode="run"):
        gc.forget_digests()
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            result = gc.main([mode, *flags])
        self.output = out.getvalue()
        return result

    def manifest(self):
        return json.loads(gc.manifest_path(self.s.root).read_text())

    def reject_timing_fingerprint_and_lookup(self):
        fingerprint, lookup = gc.fingerprint, gc.lookup
        def identify(root, gate):
            self.assertNotEqual(gate["id"], "elab", "deferred timing fingerprint must not be read")
            return fingerprint(root, gate)
        def find(cache, identifier, given):
            self.assertNotEqual(identifier, "elab", "deferred timing evidence must not be looked up")
            return lookup(cache, identifier, given)
        self.stack.enter_context(mock.patch.object(gc, "fingerprint", side_effect=identify))
        self.stack.enter_context(mock.patch.object(gc, "lookup", side_effect=find))

    def test_incomplete_full_population_no_timing_and_static_controls_run(self):
        self.reject_timing_fingerprint_and_lookup()
        self.assertEqual(self.invoke("--defer-elab"), 3, self.output)
        manifest = self.manifest()
        self.assertEqual([row["id"] for row in manifest["rows"]], [gate["id"] for gate in self.gates])
        self.assertFalse(manifest["green"])
        self.assertFalse(manifest["complete"])
        self.assertTrue(manifest["non_timing_green"])
        self.assertEqual(manifest["scope"], "non-timing")
        self.assertEqual(manifest["deferred"], ["elab"])
        row = manifest["rows"][2]
        self.assertEqual(row["disposition"], "deferred")
        self.assertEqual(row["verdict"], {})
        self.assertIsNone(row["fingerprint"])
        self.assertIsNone(row["components"])
        self.assertIsNone(row["evidence_from"])
        self.assertFalse(row["cached"])
        self.assertEqual(self.s.ran("elab.ran"), 0)
        self.assertEqual(self.s.ran("build.ran"), 0)
        self.assertEqual(self.s.ran("static.ran"), 1)
        self.assertEqual(self.s.ran("comparator.ran"), 1)
        self.assertEqual(self.s.coordination.calls_made(), [])
        self.assertIn("GATES INCOMPLETE:", self.output)
        self.assertIn("no timing verdict", self.output)
        self.assertNotIn("GATES OK", self.output)
        report = gc.report_path(self.s.root).read_text()
        self.assertIn("| deferred | no timing verdict |", report)
        self.assertIn("complete: false", report)
        self.assertNotIn("elab", self.s.cache()[0]["gates"])

    def test_default_executes_then_reuses_elab_and_deferred_preserves_old_record(self):
        self.assertEqual(self.invoke(), 0, self.output)
        self.assertIn("GATES OK:", self.output)
        self.assertTrue(self.manifest()["green"])
        self.assertNotIn("scope", self.manifest())
        self.assertEqual(self.s.ran("elab.ran"), 1)
        record = copy.deepcopy(self.s.cache()[0]["gates"]["elab"])
        self.assertEqual(self.invoke(), 0, self.output)
        self.assertEqual(self.manifest()["rows"][2]["disposition"], "reused")
        self.reject_timing_fingerprint_and_lookup()
        self.assertEqual(self.invoke("--defer-elab"), 3, self.output)
        self.assertEqual(self.s.ran("elab.ran"), 1)
        self.assertEqual(self.s.cache()[0]["gates"]["elab"], record)
        self.assertEqual(self.manifest()["rows"][2]["verdict"], {})

    def test_authentic_non_timing_records_admit_and_reuse(self):
        self.assertEqual(self.invoke("--defer-elab"), 3, self.output)
        records = self.s.cache()[0]["gates"]
        self.assertEqual(set(records), {"static", "elab-migration-comparison-controls"})
        self.assertEqual(self.invoke("--defer-elab"), 3, self.output)
        self.assertEqual(self.manifest()["rows"][1]["disposition"], "reused")
        self.assertEqual(self.manifest()["rows"][3]["disposition"], "reused")
        self.assertEqual(self.s.ran("static.ran"), 1)
        self.assertEqual(self.s.ran("elab.ran"), 0)

    def test_plan_and_explain_have_same_deferral_without_timing_inputs(self):
        self.reject_timing_fingerprint_and_lookup()
        for flags in [("--defer-elab",), ("--defer-elab", "--explain")]:
            with self.subTest(flags=flags):
                self.assertEqual(self.invoke(*flags, mode="plan"), 0)
                self.assertIn("defer  scripts/check-elab.sh --no-build", self.output)
                self.assertIn("PLAN: 4 rows", self.output)
                self.assertIn("PLAN INCOMPLETE:", self.output)
                self.assertEqual(self.s.ran("static.ran"), 0)
                self.assertEqual(self.s.ran("elab.ran"), 0)
        self.certificate.return_value = (False, "fixture absent", None)
        self.assertEqual(self.invoke("--defer-elab", mode="plan"), 0)
        self.assertIn("fixture absent", self.output)

    def test_absent_stale_certificate_refuses_before_any_gate(self):
        for reason in ["fixture absent", "fixture stale"]:
            self.certificate.return_value = (False, reason, None)
            with self.subTest(reason=reason), mock.patch.object(gc, "execute") as execute:
                self.assertEqual(self.invoke("--defer-elab"), 2, self.output)
                execute.assert_not_called()
                self.assertIn("REFUSED", self.output)
                self.assertEqual(self.s.coordination.calls_made(), [])
                self.assertFalse(gc.manifest_path(self.s.root).exists())

    def test_certificate_race_never_falls_back_to_bare_prerequisite(self):
        self.certificate.side_effect = [(True, "initially current", {}), (False, "changed", None)]
        with mock.patch.object(gc, "execute", side_effect=AssertionError("uncertified build must never execute")) as execute:
            self.assertEqual(self.invoke("--defer-elab"), 2, self.output)
            execute.assert_not_called()
        self.assertEqual(self.s.coordination.calls_made(), [])
        self.assertEqual(self.s.ran("build.ran"), 0)

    def test_cert_drift_rejects_final_candidate_and_shared_admission(self):
        self.certificate.side_effect = [
            (True, "current", {}), (True, "current", {}), (True, "current", {}),
            (False, "changed after rows", None),
        ]
        self.assertEqual(self.invoke("--defer-elab"), 1, self.output)
        self.assertFalse(self.manifest()["non_timing_green"])
        self.assertIn("owned-build certificate no longer describes this tree", self.output)
        self.assertEqual(self.s.cache()[0]["gates"], {})

    def test_missing_changed_duplicate_or_prerequisite_elab_refuses(self):
        changed = copy.deepcopy(self.gates)
        changed[2]["command"] = ["scripts/check-elab.sh", "--full", "--no-build"]
        duplicate = copy.deepcopy(self.gates)
        duplicate.append({**duplicate[2], "id": "another-elab", "order": 5})
        prerequisite = copy.deepcopy(self.gates)
        prerequisite[2].update(prerequisite=True, kind="composition", reason="invalid timing prerequisite")
        for gates in [self.gates[:2] + self.gates[3:], changed, duplicate, prerequisite]:
            with self.subTest(gates=gates):
                self.s.registry(gates)
                with mock.patch.object(gc, "execute") as execute:
                    self.assertEqual(self.invoke("--defer-elab"), 2, self.output)
                    execute.assert_not_called()
                self.assertEqual(self.s.ran("elab.ran"), 0)

    def test_dependency_on_deferred_elab_is_blocked(self):
        consumer = self.s.passing_gate("consumer.sh", "consumer.ran")
        self.gates.append({**simple_gate("consumer", [consumer], {"files": [consumer]},
                                       "^OK — consumer.sh: ", 5), "depends_on": ["elab"]})
        self.s.registry(self.gates)
        self.s.git_init()
        self.assertEqual(self.invoke("--defer-elab"), 1, self.output)
        self.assertFalse(self.manifest()["non_timing_green"])
        self.assertEqual(self.manifest()["rows"][-1]["disposition"], "blocked")
        self.assertEqual(self.s.ran("consumer.ran"), 0)
        self.assertIn("required evidence absent or red: elab", self.output)

    def test_red_missing_summary_and_missing_gate_cannot_pass(self):
        for body in ["#!/bin/sh\nexit 1\n", "#!/bin/sh\necho progress\n", None]:
            with self.subTest(body=body):
                script = self.s.root / "scripts/static.sh"
                if body is None:
                    script.unlink()
                else:
                    script.write_text(body)
                self.s.git("add", "-A")
                self.s.git("-c", "commit.gpgsign=false", "commit", "-q", "-m", "red fixture")
                self.assertEqual(self.invoke("--defer-elab"), 1, self.output)
                self.assertFalse(self.manifest()["non_timing_green"])
                self.assertFalse(self.manifest()["green"])
                self.assertNotIn("GATES INCOMPLETE:", self.output)
                self.assertNotIn("static", self.s.cache()[0]["gates"])
                if body is None:
                    self.assertIsNone(self.manifest()["rows"][1]["verdict"]["exit"])
                    self.assertIn("command did not start", gc.report_path(self.s.root).read_text())

    def test_fresh_row_drift_fails_final_candidate(self):
        real_execute = gc.execute
        def execute(root, gate, **kwargs):
            result = real_execute(root, gate, **kwargs)
            if gate["id"] == "static":
                self.s.write("payload.txt", "two\n")
            return result
        with mock.patch.object(gc, "execute", side_effect=execute):
            self.assertEqual(self.invoke("--defer-elab"), 1, self.output)
        self.assertFalse(self.manifest()["non_timing_green"])
        self.assertEqual(self.s.cache()[0]["gates"], {})

    def test_dirty_row_drift_fails_without_seeding_shared_records(self):
        self.s.write("payload.txt", "dirty\n")
        self.test_fresh_row_drift_fails_final_candidate()
        self.assertIn("dirty worktree", self.output)

    def test_reused_row_drift_fails_and_does_not_advance_store(self):
        self.assertEqual(self.invoke("--defer-elab"), 3, self.output)
        store = gc.cache_path(self.s.root).read_bytes()
        real_lookup = gc.lookup
        def lookup(cache, identifier, given):
            result = real_lookup(cache, identifier, given)
            if identifier == "elab-migration-comparison-controls":
                self.s.write("payload.txt", "two\n")
            return result
        with mock.patch.object(gc, "lookup", side_effect=lookup):
            self.assertEqual(self.invoke("--defer-elab"), 1, self.output)
        self.assertFalse(self.manifest()["non_timing_green"])
        self.assertEqual(gc.cache_path(self.s.root).read_bytes(), store)

    def test_unidentifiable_non_timing_input_cannot_claim_candidate_green(self):
        real_fingerprint = gc.fingerprint
        def fingerprint(root, gate):
            if gate["id"] == "static":
                raise gc.Unresolvable("fixture input unavailable")
            return real_fingerprint(root, gate)
        with mock.patch.object(gc, "fingerprint", side_effect=fingerprint):
            self.assertEqual(self.invoke("--defer-elab"), 1, self.output)
        self.assertFalse(self.manifest()["non_timing_green"])
        self.assertEqual(self.s.cache()[0]["gates"], {})

    def test_incompatible_python_options_and_abbreviations_refuse(self):
        for mode, flags in [
            ("run", ["--defer-elab", "--fresh"]), ("plan", ["--fresh", "--defer-elab"]),
            *((mode, ["--defer-elab"]) for mode in ["audit", "inventory", "self-test", "certify-build"]),
            ("run", ["--defer"]), ("run", ["--skip", "elab"]),
        ]:
            with self.subTest(mode=mode, flags=flags):
                try:
                    code = self.invoke(*flags, mode=mode)
                except SystemExit as error:
                    code = error.code
                self.assertEqual(code, 2)
                self.assertEqual(self.s.ran("elab.ran"), 0)
                self.assertEqual(self.s.ran("static.ran"), 0)

    def test_shell_routes_exact_flag_and_rejects_conflicting_history(self):
        wrapper = self.s.root / "scripts/check-gates.sh"
        wrapper.write_bytes(Path(__file__).with_name("check-gates.sh").read_bytes())
        engine = self.s.root / "scripts/gate-cache.py"
        engine.write_text("import json,sys\nprint(json.dumps(sys.argv[1:]))\n")
        for flags, expected in [
            (["--defer-elab"], ["run", "--defer-elab"]),
            (["--echo", "--defer-elab"], ["run", "--echo", "--defer-elab"]),
            (["--defer-elab", "--plan"], ["plan", "--defer-elab"]),
            (["--explain", "--defer-elab"], ["plan", "--explain", "--defer-elab"]),
        ]:
            result = subprocess.run(["bash", str(wrapper), *flags], capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout), expected)
        for flags in [
            ["--fresh"], ["--fresh", "--plan"], ["--plan", "--fresh"],
            ["--audit"], ["--self-test"], ["--inventory"], ["--certify-build"],
            ["--audit", "--plan"], ["--defer"], ["--defer-elab=elab"], ["--skip", "elab"],
        ]:
            result = subprocess.run(["bash", str(wrapper), "--defer-elab", *flags], capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 2, (flags, result.stdout, result.stderr))
            self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
