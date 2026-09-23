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

# The lock and admission stubs record every acquisition in the same event log
# as the Lake stub, so a control can read the order in which the script took
# the report lock, planned, took the heavy boundary, planned again, and
# elaborated -- or, for a plan that measures nothing, that it never took the
# heavy boundary at all.
LOCK_STUB = """#!/usr/bin/env bash
gate_lock_release_all() { :; }
gate_lock_heavy_acquire() { printf 'heavy-lock %s\\n' "$1" >> "$MOCK_LAKE_LOG"; }
gate_lock_acquire() { printf 'report-lock %s\\n' "$2" >> "$MOCK_LAKE_LOG"; }
"""
SEMAPHORE_STUB = """#!/usr/bin/env bash
gate_semaphore_release() { :; }
gate_semaphore_acquire() { printf 'semaphore %s %s %s\\n' "$1" "$2" "$3" >> "$MOCK_LAKE_LOG"; }
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
with open(os.environ['MOCK_LAKE_LOG'], 'a') as log:
    log.write('selector ' + args[0] + '\\n')
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


def first(lines: list[str], prefix: str, occurrence: int = 1) -> int:
    """Index of the n-th event line starting with `prefix`; -1 when absent."""

    seen = 0
    for index, line in enumerate(lines):
        if line.startswith(prefix):
            seen += 1
            if seen == occurrence:
                return index
    return -1


def plan_before_hold_controls(root: Path) -> None:
    """A --no-build run plans first; a plan that measures nothing takes no
    heavy boundary, and a plan that measures takes it before elaborating and
    plans again inside it."""

    noop, events = run_case(root, "", "1.000", full=False)
    assert noop.returncode == 0 and "OK — elab: 0 measured" in noop.stdout, noop.stdout
    assert "no heavy-gate lock or host hold was taken" in noop.stdout
    assert "shared publication skipped: nothing was measured" in noop.stdout
    assert first(events, "report-lock") >= 0, events
    assert first(events, "heavy-lock") == -1 and first(events, "semaphore") == -1, events
    assert first(events, "selector plan", 2) == -1, "a no-op run plans once"
    assert first(events, "selector publish") == -1, "a no-op run publishes nothing"
    assert lean_calls(events) == []

    measuring, events = run_case(root, "Blanc/A.lean", "1.000", full=False)
    assert measuring.returncode == 0 and "OK — elab: 1 measured" in measuring.stdout
    order = [
        first(events, "report-lock"),
        first(events, "selector plan", 1),
        first(events, "heavy-lock elab"),
        first(events, "semaphore the elaboration-time measurement 8 exclusive"),
        first(events, "selector plan", 2),
        first(events, "env lean Blanc/A.lean"),
    ]
    assert all(index >= 0 for index in order), (order, events)
    assert order == sorted(order), (order, events)
    assert first(events, "selector publish") >= 0, "a measuring run publishes"


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

        plan_before_hold_controls(root)

    print("OK — elab warm-up and plan-before-hold controls: full slowdown/refusal, restored green, "
          "partial unchanged, no-op plan takes no heavy boundary, measuring plan takes it "
          "before elaborating and re-plans inside it (mocked)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
