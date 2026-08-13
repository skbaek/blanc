#!/usr/bin/env python3
"""Compile the CREATE rollback regression and exercise its raw-commit mutant."""

from __future__ import annotations

import pathlib
import importlib.util
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "ExecutionSettlementRegression.lean"
MARKER = "-- RAW-COMMIT-MUTANT-CONTROL"
RAW_ROOT_MARKER = "-- SETTLEMENT-FILTERED-RAW-ROOT-MUTANT-CONTROL"
MUTANT = r"""
private theorem rawCommitMutant_prunes (w : Fixture) :
    rawCommittedDescendantFrames w.run =
      rawCommittedDescendantFrames w.next := by
  simp only [Fixture.run, rawCommittedDescendantFrames, w.rawCommits]
"""
RAW_ROOT_MUTANT = r"""
private theorem settlementFilteredRawFrameRootsMutant (w : Fixture) :
    Exec.rawFrameRoots w.run =
      w.root :: Exec.rawFrameDescendants w.next := by
  rfl
"""
REQUIRED_POSITIVE_THEOREMS = {
    "Blanc.ExecutionSettlementRegression.Fixture.rawFrameRoots_retains",
    "Blanc.ExecutionSettlementRegression.concrete_create_raw_vs_settlement",
    "Blanc.ExecutionSettlementRegression.required_positive_controls",
}


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


def load_ownership_parser():
    path = ROOT / "scripts" / "check-extraction-ownership.py"
    spec = importlib.util.spec_from_file_location("extraction_ownership", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the declaration ownership parser")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def missing_positive_theorems(ownership, path: pathlib.Path) -> list[str]:
    declarations = ownership.declarations(path)
    return sorted(
        name for name in REQUIRED_POSITIVE_THEOREMS
        if declarations.get(name, (None,))[0] != "theorem"
    )


def main() -> int:
    source = FIXTURE.read_text(encoding="utf-8")
    if source.count(MARKER) != 1 or source.count(RAW_ROOT_MARKER) != 1:
        return fail("fixture must contain exactly one of each raw-mutant marker")
    if source.count("rawChildWrite") != 2:
        return fail("fixture must retain its dependent child-SSTORE witness")
    try:
        ownership = load_ownership_parser()
    except (OSError, RuntimeError) as exc:
        return fail(f"could not load fail-closed ownership parser: {exc}")
    missing_positives = missing_positive_theorems(ownership, FIXTURE)
    if missing_positives:
        return fail(
            "required positive proof declarations are absent or wrong-kind: "
            + ", ".join(missing_positives)
        )

    positive = run_lean(FIXTURE)
    if positive.returncode != 0:
        return fail("positive fixture did not compile", positive)
    if positive.stdout.strip() != "true" or positive.stderr:
        return fail("positive fixture did not report exactly `true`", positive)

    with tempfile.TemporaryDirectory(prefix="execution-settlement-mutant-") as temp:
        mutant_path = pathlib.Path(temp) / "ExecutionSettlementRawMutant.lean"
        mutant_path.write_text(source.replace(MARKER, MUTANT), encoding="utf-8")
        mutant = run_lean(mutant_path)

        raw_root_mutant_path = (
            pathlib.Path(temp) / "ExecutionSettlementRawRootMutant.lean"
        )
        raw_root_mutant_path.write_text(
            source.replace(RAW_ROOT_MARKER, RAW_ROOT_MUTANT), encoding="utf-8"
        )
        raw_root_mutant = run_lean(raw_root_mutant_path)

        positive_deleted_path = pathlib.Path(temp) / "PositiveDeleted.lean"
        positive_deleted_path.write_text(
            source.replace(
                "private theorem concrete_create_raw_vs_settlement",
                "private theorem concrete_create_raw_vs_settlement_removed",
                1,
            ),
            encoding="utf-8",
        )
        if not missing_positive_theorems(ownership, positive_deleted_path):
            return fail("required-positive deletion control failed")

    evidence = mutant.stdout + mutant.stderr
    if mutant.returncode == 0:
        return fail("raw-commit mutant unexpectedly compiled", mutant)
    if "unsolved goals" not in evidence or "Exec.Frame.ofRun" not in evidence:
        return fail("raw-commit mutant failed for an unexpected reason", mutant)

    raw_root_evidence = raw_root_mutant.stdout + raw_root_mutant.stderr
    if raw_root_mutant.returncode == 0:
        return fail(
            "settlement-filtered raw-root mutant unexpectedly compiled",
            raw_root_mutant,
        )
    if "Tactic `rfl` failed" not in raw_root_evidence:
        return fail(
            "settlement-filtered raw-root mutant failed unexpectedly",
            raw_root_mutant,
        )

    print(
        "OK — execution settlement: concrete Exec.runOk CREATE rollback fixture "
        "is live; rawFrameRoots retains while settlement traversal prunes; "
        "3 required positive proofs + deletion control; 2 mutants retain the "
        "storage-writing child"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
