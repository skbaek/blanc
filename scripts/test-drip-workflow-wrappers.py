#!/usr/bin/env python3
"""Pure dispatch controls: temporary scripts only, never Lean or a real cache."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent


class WorkflowWrappers(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.scripts = self.root / "scripts"
        self.scripts.mkdir()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.log = self.root / "calls"
        self.cache = self.root / "cache"
        (self.cache / "artifacts").mkdir(parents=True)
        (self.cache / "artifacts" / "123.olean").write_bytes(b"mock artifact")
        for name in ("drip-artifact-writer.sh", "certify-checked-build.sh", "gate-semaphore.sh"):
            shutil.copyfile(SCRIPTS / name, self.scripts / name)
        # Certification takes host admission through gate-semaphore.sh; a mock
        # coordination entry point answers it and records the exchange, so no
        # control here asks the real host.
        self.semaphore_log = self.root / "semaphore-calls"
        creme = self.root / "creme"
        (creme / ".semaphore").mkdir(parents=True)
        self.mock(creme / ".semaphore" / "semaphore",
                  'printf "%s\\n" "$*" >> "$MOCK_SEMAPHORE_LOG"\n'
                  'if [ "$1" = adaptive-acquire ] && [ -n "${MOCK_SEMAPHORE_REFUSE:-}" ]; then\n'
                  '  echo "REFUSED DEFER_HEAVY: mock host is busy"; exit 3\nfi\necho OK\n')
        self.env = dict(os.environ, PATH=f"{self.bin}:/usr/bin:/bin",
                        LAKE_CACHE_DIR=str(self.cache), MOCK_LOG=str(self.log),
                        CREME_ROOT=str(creme), MOCK_SEMAPHORE_LOG=str(self.semaphore_log))
        for name in ("BLANC_GATE_SEMAPHORE", "BLANC_GATE_SEMAPHORE_LABEL",
                     "BLANC_GATE_SEMAPHORE_WAIT", "BLANC_GATE_SEMAPHORE_MEMORY_GIB"):
            self.env.pop(name, None)
        self.mock(self.bin / "lake", 'printf "lake|%s|%s\\n" "$PWD" "$*" >> "$MOCK_LOG"\nexit "${MOCK_LAKE_EXIT:-0}"\n')
        self.mock(self.scripts / "check-lake-artifact-cache.sh",
                  'printf "integrity|%s|%s\\n" "$PWD" "$LAKE_CACHE_DIR" >> "$MOCK_LOG"\nexit "${MOCK_INTEGRITY_EXIT:-0}"\n')
        self.mock(self.scripts / "check-gates.sh",
                  'printf "certificate|%s|%s\\n" "$PWD" "$*" >> "$MOCK_LOG"\nexit "${MOCK_CERTIFICATE_EXIT:-0}"\n')

    def mock(self, path, body):
        path.write_text("#!/usr/bin/env bash\nset -eu\n" + body)
        path.chmod(0o755)

    def run_wrapper(self, name, *args):
        return subprocess.run(["/usr/bin/bash", str(self.scripts / name), *args],
                              cwd=self.root.parent, env=self.env,
                              capture_output=True, text=True, check=False)

    def calls(self):
        return self.log.read_text().splitlines() if self.log.exists() else []

    def test_exact_writer_dispatch(self):
        for mode, evaluator in (("runtime", "gen-drip-code.lean"),
                                ("creation", "gen-drip-creation-code.lean")):
            with self.subTest(mode=mode):
                result = self.run_wrapper("drip-artifact-writer.sh", mode)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(self.calls()[-1], f"lake|{self.root}|env lean scripts/{evaluator}")
        self.assertEqual(len(self.calls()), 2)  # No build, probe or other evaluator.

    def test_writer_rejects_missing_unknown_and_extra(self):
        for args in ((), ("unknown",), ("runtime", "extra"), ("--force",),
                     ("creation", "--memory-gib", "8"), ("/tmp/other.lean",)):
            with self.subTest(args=args):
                self.assertEqual(self.run_wrapper("drip-artifact-writer.sh", *args).returncode, 2)
        self.assertEqual(self.calls(), [])

    def test_writer_propagates_failure(self):
        self.env["MOCK_LAKE_EXIT"] = "19"
        self.assertEqual(self.run_wrapper("drip-artifact-writer.sh", "runtime").returncode, 19)
        self.assertEqual(len(self.calls()), 1)

    def test_certification_rejects_arguments_before_execution(self):
        self.assertEqual(self.run_wrapper("certify-checked-build.sh", "--force").returncode, 2)
        self.assertEqual(self.calls(), [])

    def test_certificate_requires_absolute_existing_nonempty_cache(self):
        for value in (None, "", "relative", str(self.root / "absent")):
            with self.subTest(value=value):
                if value is None:
                    self.env.pop("LAKE_CACHE_DIR", None)
                else:
                    self.env["LAKE_CACHE_DIR"] = value
                self.assertEqual(self.run_wrapper("certify-checked-build.sh").returncode, 2)
        self.env["LAKE_CACHE_DIR"] = str(self.cache)
        (self.cache / "artifacts" / "123.olean").unlink()
        self.assertEqual(self.run_wrapper("certify-checked-build.sh").returncode, 2)
        self.assertEqual(self.calls(), [])

    def test_certificate_rejects_nonregular_entries(self):
        entry = self.cache / "artifacts" / "unexpected"
        entry.mkdir()
        self.assertEqual(self.run_wrapper("certify-checked-build.sh").returncode, 2)
        entry.rmdir()
        entry.symlink_to(self.cache / "artifacts" / "123.olean")
        self.assertEqual(self.run_wrapper("certify-checked-build.sh").returncode, 2)
        self.assertEqual(self.calls(), [])

    def test_integrity_failure_prevents_certificate(self):
        self.env["MOCK_INTEGRITY_EXIT"] = "23"
        result = self.run_wrapper("certify-checked-build.sh")
        self.assertEqual(result.returncode, 23)
        self.assertEqual(self.calls(), [f"integrity|{self.root}|{self.cache}"])

    def test_adjacent_sequence_and_preserved_cache(self):
        result = self.run_wrapper("certify-checked-build.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), [f"integrity|{self.root}|{self.cache}",
                                       f"certificate|{self.root}|--certify-build"])
        self.assertIn("1 cache artifact entries present (not yet hash-verified)", result.stdout)

    def semaphore_calls(self):
        if not self.semaphore_log.exists():
            return []
        return self.semaphore_log.read_text().splitlines()

    def test_certification_is_admitted_and_released(self):
        result = self.run_wrapper("certify-checked-build.sh")
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = self.semaphore_calls()
        self.assertEqual(len(calls), 2, calls)
        self.assertTrue(calls[0].startswith("adaptive-acquire blanc-gates "), calls)
        self.assertIn("--memory-gib 3", calls[0])
        self.assertEqual(calls[1], "release blanc-gates")

    def test_refused_admission_runs_nothing(self):
        self.env["MOCK_SEMAPHORE_REFUSE"] = "1"
        result = self.run_wrapper("certify-checked-build.sh")
        self.assertEqual(result.returncode, 2)
        self.assertIn("REFUSED", result.stdout)
        self.assertEqual(self.calls(), [])

    def test_certificate_failure_is_terminal(self):
        self.env["MOCK_CERTIFICATE_EXIT"] = "31"
        self.assertEqual(self.run_wrapper("certify-checked-build.sh").returncode, 31)
        self.assertEqual(len(self.calls()), 2)


if __name__ == "__main__":
    unittest.main()
