#!/usr/bin/env python3
"""Compile concrete occurrence fixtures and require every semantic mutant to fail."""

from __future__ import annotations

import pathlib
import json
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "ExecutionOccurrenceRegression.lean"
WETH = ROOT / "Blanc" / "Weth10HolderFlowCompiled.lean"
MOVE_MANIFEST = ROOT / "scripts" / "execution-occurrence-lift-manifest.json"
EXPECTED = "[true, true, true, true, true, true, true, true, true, true, true]"

MUTANTS = {
    "-- TERMINAL-ERROR-MUTANT-CONTROL": r"""
private theorem terminalSuccessOnlyMutant :
    ∃ occurrence : Exec.NinstOccurrence
        (⟨0, terminalErrorSevm, terminalErrorPre, terminalErrorOut,
          terminalErrorRun⟩ : Exec.Deriv),
      occurrence.instruction = .reg .sstore ∧
        ∃ post, occurrence.stepResult = .ok post := by
  rcases terminalError_occurs with ⟨occurrence, instruction⟩
  refine ⟨occurrence, instruction, ?_⟩
""",
    "-- RAW-ERROR-PRUNE-MUTANT-CONTROL": r"""
private theorem rawErrorPruneMutant :
    Exec.rawNodes terminalErrorRun = [] := by
  have reached := Exec.mem_rawNodes_self terminalErrorRun
  exact ?_
""",
    "-- RAW-BYTE-SCAN-MUTANT-CONTROL": r"""
private theorem rawByteScanMutant : payloadHasSourceSstore = true := by
  decide
""",
    "-- FIRST-WRITER-MUTANT-CONTROL": r"""
private theorem firstWriterMutant (fixture : HistoryFixture) :
    ∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨0, historySevm, historyPre, fixture.out, fixture.run⟩ : Exec.Deriv),
      write.Retained ∧ write.storageOwner = historySevm.currentTarget ∧
      write.key = 0 ∧ write.value = 5 ∧ write.IsLastRetained := by
  rcases history_lastWriter fixture with
    ⟨write, retained, owner, key, value, last⟩
  exact ⟨write, retained, owner, key, value, last⟩
""",
    "-- IDENTITY-MUTANT-CONTROL": r"""
private theorem identityWeakenedMutant
    {frame : Exec.Frame} {program : Prog} {storage codeAddress other : Adr}
    (exact : frame.exactInvocation program storage codeAddress) :
    frame.exactInvocation program other codeAddress := by
  exact exact
""",
}


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args, cwd=ROOT, text=True, capture_output=True, check=False
    )


def fail(message: str, result: subprocess.CompletedProcess[str] | None = None) -> int:
    print(f"ERROR — execution occurrence: {message}", file=sys.stderr)
    if result is not None:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
    return 1


def main() -> int:
    source = FIXTURE.read_text(encoding="utf-8")
    for marker in [*MUTANTS, "-- WETH-BRIDGE-MUTANT-CONTROL"]:
        if source.count(marker) != 1:
            return fail(f"fixture must contain exactly one `{marker}` marker")

    positive = run(["lake", "env", "lean", str(FIXTURE)])
    if positive.returncode != 0:
        return fail("positive fixture did not compile", positive)
    if positive.stdout.strip() != EXPECTED or positive.stderr:
        return fail("positive fixture evaluator vector drifted", positive)

    with tempfile.TemporaryDirectory(prefix="execution-occurrence-mutants-") as temp:
        temp_root = pathlib.Path(temp)
        for index, (marker, mutant_source) in enumerate(MUTANTS.items()):
            mutant_path = temp_root / f"ExecutionOccurrenceMutant{index}.lean"
            mutant_path.write_text(
                source.replace(marker, mutant_source), encoding="utf-8"
            )
            mutant = run(["lake", "env", "lean", str(mutant_path)])
            evidence = mutant.stdout + mutant.stderr
            if mutant.returncode == 0:
                return fail(f"mutant `{marker}` unexpectedly compiled", mutant)
            if not any(token in evidence for token in (
                "unsolved goals", "Type mismatch", "Application type mismatch",
                "Tactic `decide` failed",
                "Tactic `decide` proved that the proposition"
            )):
                return fail(f"mutant `{marker}` failed unexpectedly", mutant)

    weth_source = WETH.read_text(encoding="utf-8")
    bridge_tokens = (
        "theorem Exec.Frame.NinstOccurrence.toCommon\n",
        "common.node.devm = stepPre",
        "common.instruction = n",
        "common.slot = xl",
        "common.stepResult = .ok stepPost",
    )
    if not all(token in weth_source for token in bridge_tokens):
        return fail("WETH projection bridge statement is absent or weakened")
    bridge_mutant = weth_source.replace(
        "theorem Exec.Frame.NinstOccurrence.toCommon",
        "theorem Exec.Frame.NinstOccurrence.toCommon_removed",
        1,
    )
    if all(token in bridge_mutant for token in bridge_tokens):
        return fail("WETH bridge-removal mutant unexpectedly passed")

    try:
        manifest = json.loads(MOVE_MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return fail(f"occurrence move manifest is unreadable: {exc}")
    if set(manifest) != {"schema", "mappings"} or manifest["schema"] != 1:
        return fail("occurrence move manifest schema drifted")
    mappings = manifest["mappings"]
    if not isinstance(mappings, list) or len(mappings) != 9:
        return fail("occurrence move manifest must contain exactly 9 rows")
    for index, row in enumerate(mappings, 1):
        if not isinstance(row, dict) or set(row) != {
            "declaration", "kind", "donorModule", "commonModule"
        } or row["kind"] != "theorem":
            return fail(f"occurrence move row {index} has invalid schema")
        token = f'theorem {row["declaration"]}'
        common = (ROOT / row["commonModule"]).read_text(encoding="utf-8")
        donor = (ROOT / row["donorModule"]).read_text(encoding="utf-8")
        if common.count(token) != 1:
            return fail(f"common owner missing or duplicates `{row['declaration']}`")
        if token in donor:
            return fail(f"donor shadow survives for `{row['declaration']}`")
        if token in common.replace(token, "theorem removed_owner", 1):
            return fail(f"common-owner removal mutant passed for `{row['declaration']}`")

    settlement = run([sys.executable, "scripts/check-execution-settlement.py"])
    if settlement.returncode != 0:
        return fail("CREATE settlement/raw-commit control failed", settlement)
    if not settlement.stdout.startswith("OK — execution settlement:"):
        return fail("CREATE settlement control verdict drifted", settlement)

    print(
        "OK — execution occurrence: 11 concrete controls; 5 Lean mutants; "
        "WETH bridge-removal mutant; 9 moved-owner controls; "
        "CREATE raw-commit mutant"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
