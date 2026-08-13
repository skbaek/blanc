#!/usr/bin/env python3
"""Compile the CREATE rollback regression and exercise its raw-commit mutant."""

from __future__ import annotations

import pathlib
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "ExecutionSettlementRegression.lean"
MARKER = "-- RAW-COMMIT-MUTANT-CONTROL"
MUTANT = r"""
private theorem rawCommitMutant_prunes (w : Fixture) :
    rawCommittedDescendantFrames w.run =
      rawCommittedDescendantFrames w.next := by
  simp only [Fixture.run, rawCommittedDescendantFrames, w.rawCommits]
"""


def run_lean(path: pathlib.Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def fail(message: str, result: subprocess.CompletedProcess[str] | None = None) -> int:
    print(f"ERROR — execution settlement: {message}", file=sys.stderr)
    if result is not None:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
    return 1


def main() -> int:
    source = FIXTURE.read_text(encoding="utf-8")
    if source.count(MARKER) != 1:
        return fail("fixture must contain exactly one raw-mutant marker")
    if source.count("rawChildWrite") != 2:
        return fail("fixture must retain its dependent child-SSTORE witness")

    positive = run_lean(FIXTURE)
    if positive.returncode != 0:
        return fail("positive fixture did not compile", positive)
    if positive.stdout.strip() != "true" or positive.stderr:
        return fail("positive fixture did not report exactly `true`", positive)

    with tempfile.TemporaryDirectory(prefix="execution-settlement-mutant-") as temp:
        mutant_path = pathlib.Path(temp) / "ExecutionSettlementRawMutant.lean"
        mutant_path.write_text(source.replace(MARKER, MUTANT), encoding="utf-8")
        mutant = run_lean(mutant_path)

    evidence = mutant.stdout + mutant.stderr
    if mutant.returncode == 0:
        return fail("raw-commit mutant unexpectedly compiled", mutant)
    if "unsolved goals" not in evidence or "Exec.Frame.ofRun" not in evidence:
        return fail("raw-commit mutant failed for an unexpected reason", mutant)

    print(
        "OK — execution settlement: concrete Exec.runOk CREATE rollback fixture "
        "is live; settlement traversal prunes; raw-commit mutant retains the "
        "storage-writing child"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
