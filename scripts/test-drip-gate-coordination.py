#!/usr/bin/env python3
"""Real shell routing against mock commands; no Lean or host hold is started."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent


class DripGateCoordination(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="drip-gate-routing-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in ("check-drip.sh", "gate-semaphore.sh"):
            shutil.copyfile(SCRIPTS / name, scripts / name)
        self.log = self.root / "calls"
        binary = self.root / "bin"
        binary.mkdir()
        self.command(binary / "python3", '''
printf 'python %s\n' "$*" >> "$MOCK_LOG"
case "$*" in *"${MOCK_FAIL:-no-matching-script}"*) exit 17;; esac
''')
        self.entry = self.root / "creme/.semaphore/semaphore"
        self.entry.parent.mkdir(parents=True)
        self.command(self.entry, '''
printf 'semaphore %s\n' "$*" >> "$MOCK_LOG"
if [ "$1" = adaptive-acquire ] && [ "${MOCK_REFUSE:-0}" = 1 ]; then
  echo 'REFUSED deliberate admission control'
  exit 2
fi
''')
        self.env = dict(os.environ, PATH=f"{binary}:/usr/bin:/bin",
                        CREME_ROOT=str(self.root / "creme"), MOCK_LOG=str(self.log))
        for name in ("BLANC_GATE_SEMAPHORE", "BLANC_GATE_SEMAPHORE_LABEL",
                     "BLANC_GATE_SEMAPHORE_MEMORY_GIB", "BLANC_GATE_SEMAPHORE_WAIT"):
            self.env.pop(name, None)

    @staticmethod
    def command(path, body):
        path.write_text("#!/usr/bin/env bash\nset -eu\n" + body)
        path.chmod(0o755)

    def run_gate(self):
        result = subprocess.run(["/bin/bash", str(self.root / "scripts/check-drip.sh")],
                                env=self.env, capture_output=True, text=True)
        return result, self.log.read_text().splitlines()

    def test_admission_is_lazy_and_released(self):
        result, rows = self.run_gate()
        self.assertEqual(result.returncode, 0, result.stderr)
        acquisition = next(i for i, row in enumerate(rows) if "adaptive-acquire" in row)
        self.assertTrue(all(row.startswith("python ") for row in rows[:acquisition]))
        self.assertIn("--memory-gib 4 --contention tolerant", rows[acquisition])
        self.assertEqual(rows[acquisition + 1], "python -B scripts/check-drip-arithmetic.py")
        self.assertEqual(rows[-2], "python -B scripts/check-drip-replay.py")
        self.assertEqual(rows[-1], "semaphore release blanc-gates")

    def test_refusal_prevents_both_real_evaluators(self):
        self.env["MOCK_REFUSE"] = "1"
        result, rows = self.run_gate()
        self.assertEqual(result.returncode, 2)
        self.assertIn("REFUSED", result.stdout)
        self.assertNotIn("python -B scripts/check-drip-arithmetic.py", rows)
        self.assertNotIn("python -B scripts/check-drip-replay.py", rows)
        self.assertFalse(any("release" in row for row in rows))

    def test_static_failure_takes_no_hold(self):
        self.env["MOCK_FAIL"] = "test-drip-receipts.py"
        result, rows = self.run_gate()
        self.assertEqual(result.returncode, 17)
        self.assertFalse(any(row.startswith("semaphore") for row in rows))

    def test_evaluator_failure_releases_and_prevents_replay(self):
        self.env["MOCK_FAIL"] = "check-drip-arithmetic.py"
        result, rows = self.run_gate()
        self.assertEqual(result.returncode, 17)
        self.assertEqual(rows[-1], "semaphore release blanc-gates")
        self.assertNotIn("python -B scripts/check-drip-replay.py", rows)

    def test_explicit_modes_never_take_or_release_parent_hold(self):
        for mode in ("off", "inherited"):
            with self.subTest(mode=mode):
                self.log.unlink(missing_ok=True)
                self.env.update(BLANC_GATE_SEMAPHORE=mode, MOCK_REFUSE="1")
                result, rows = self.run_gate()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse(any(row.startswith("semaphore") for row in rows))


if __name__ == "__main__":
    unittest.main()
