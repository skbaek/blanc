#!/usr/bin/env python3
"""Mocked controls for check-elab.sh's full-measurement warm-up branch.

The test copies the production shell script unchanged into a temporary miniature
repository. Its Lake, selector, locks, and admission are local stubs, so it
exercises shell routing and verdict handling without Lean, a build, a host hold,
or timing evidence.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
CHECK_ELAB = HERE / "check-elab.sh"

LOCK_STUB = """#!/usr/bin/env bash
gate_lock_release_all() { :; }
gate_lock_heavy_acquire() { :; }
gate_lock_acquire() { :; }
"""
SEMAPHORE_STUB = """#!/usr/bin/env bash
gate_semaphore_release() { :; }
gate_semaphore_acquire() { :; }
"""
LAKE_STUB = """#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$MOCK_LAKE_LOG"
if [ "$1" = env ] && [ "$2" = lean ] && [ "${3:-}" = --version ]; then
  printf '%s\\n' 'Lean mock 0.0'
fi
exit 0
"""
SELECTOR_STUB = """#!/usr/bin/env python3
import os
import sys
from pathlib import Path

args = sys.argv[1:]
def value(name):
    return args[args.index(name) + 1]
if args[0] == 'modules':
    print('Blanc.A Blanc.B')
elif args[0] == 'plan':
    Path(value('--plan')).write_text('{}', encoding='utf-8')
elif args[0] == 'files':
    if '--affected' in args:
        print(os.environ['MOCK_AFFECTED'])
    elif '--shared' not in args:
        print('Blanc/A.lean\\nBlanc/B.lean')
elif args[0] == 'merge':
    Path(value('--report')).write_text(
        'OK\\t' + os.environ['MOCK_A_TIME'] + '\\tBlanc/A.lean\\tMEASURED\\n'
        'OK\\t1.000\\tBlanc/B.lean\\tMEASURED\\n', encoding='utf-8'
    )
elif args[0] in {'commit', 'publish'}:
    pass
else:
    raise SystemExit('unexpected selector invocation: ' + ' '.join(args))
"""


def make_root(base: Path) -> Path:
    root = base / "root"
    scripts = root / "scripts"
    scripts.mkdir(parents=True)
    (root / "Blanc").mkdir()
    (root / "Blanc/A.lean").write_text("import Init\n", encoding="utf-8")
    (root / "Blanc/B.lean").write_text("import Init\n", encoding="utf-8")
    shutil.copy2(CHECK_ELAB, scripts / "check-elab.sh")
    (scripts / "gate-lock.sh").write_text(LOCK_STUB, encoding="utf-8")
    (scripts / "gate-semaphore.sh").write_text(SEMAPHORE_STUB, encoding="utf-8")
    selector = scripts / "check-elab-selection.py"
    selector.write_text(SELECTOR_STUB, encoding="utf-8")
    selector.chmod(0o755)
    (scripts / "baseline-elab.txt").write_text(
        "OK\t1.000\tBlanc/A.lean\nOK\t1.000\tBlanc/B.lean\n", encoding="utf-8"
    )
    fake_bin = base / "bin"
    fake_bin.mkdir()
    lake = fake_bin / "lake"
    lake.write_text(LAKE_STUB, encoding="utf-8")
    lake.chmod(0o755)
    return root


def run_case(root: Path, affected: str, a_time: str, *, full: bool):
    tag = affected.replace("/", "_").replace("\n", "_") + a_time
    log = root.parent / f"lake-{tag}.log"
    environment = dict(os.environ)
    environment.update({
        "MOCK_AFFECTED": affected,
        "MOCK_A_TIME": a_time,
        "MOCK_LAKE_LOG": str(log),
        "PATH": str(root.parent / "bin") + os.pathsep + environment["PATH"],
        "PYTHONDONTWRITEBYTECODE": "1",
    })
    command = [str(root / "scripts/check-elab.sh"), "--no-build"]
    if full:
        command.append("--full")
    result = subprocess.run(
        command,
        cwd=root, env=environment, text=True, capture_output=True, check=False,
    )
    return result, log.read_text(encoding="utf-8").splitlines()


def lean_calls(lines: list[str]) -> list[str]:
    return [line for line in lines if line.startswith("env lean Blanc/")]


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="blanc-elab-warmup-") as directory:
        root = make_root(Path(directory))

        slow, calls = run_case(
            root, "Blanc/A.lean\nBlanc/B.lean", "3.000", full=True
        )
        assert slow.returncode == 1
        assert "discarded one unrecorded warm-up elaboration of Blanc/A.lean" in slow.stdout
        assert "ELAB — Blanc/A.lean: 3.000s vs baseline 1.000s" in slow.stdout
        assert lean_calls(calls) == [
            "env lean Blanc/A.lean", "env lean Blanc/A.lean", "env lean Blanc/B.lean",
        ]

        green, calls = run_case(
            root, "Blanc/A.lean\nBlanc/B.lean", "1.000", full=True
        )
        assert green.returncode == 0 and "OK — elab:" in green.stdout
        assert "discarded one unrecorded warm-up elaboration" in green.stdout
        assert lean_calls(calls) == [
            "env lean Blanc/A.lean", "env lean Blanc/A.lean", "env lean Blanc/B.lean",
        ]

        partial, calls = run_case(root, "Blanc/A.lean", "3.000", full=False)
        assert partial.returncode == 1
        assert "discarded one unrecorded warm-up elaboration" not in partial.stdout
        assert lean_calls(calls) == ["env lean Blanc/A.lean"]

    print("OK — elab warm-up controls: full slowdown/refusal, restored green, partial unchanged (mocked)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
