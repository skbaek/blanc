#!/usr/bin/env python3
"""Compile concrete occurrence fixtures and require every semantic mutant to fail."""

from __future__ import annotations

import pathlib
import json
import importlib.util
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "ExecutionOccurrenceRegression.lean"
WETH = ROOT / "Blanc" / "Weth10HolderFlowCompiled.lean"
MOVE_MANIFEST = ROOT / "scripts" / "execution-occurrence-lift-manifest.json"
EXPECTED = "[true, true, true, true, true, true, true, true, true, true, true, true, true]"

MUTANTS = {
    "-- TERMINAL-ERROR-MUTANT-CONTROL": r"""
private theorem terminalSuccessOnlyMutant (w : TerminalFixture) :
    w.occurrence.stepResult.isOk = true := by
  rfl
""",
    "-- RAW-ERROR-PRUNE-MUTANT-CONTROL": r"""
private theorem rawErrorPruneMutant (w : TerminalFixture) :
    (Exec.rawNodes w.run).isEmpty = true := by
  rfl
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
      write.key = 0 ∧ write.value = 7 ∧
      write.occurrence.node.pc = 4 ∧ write.IsLastRetained := by
  rcases history_lastWriter fixture with
    ⟨write, retained, owner, key, value, pc, last⟩
  exact ⟨write, retained, owner, key, value, pc, last⟩
""",
    "-- IDENTITY-MUTANT-CONTROL": r"""
private theorem identityWeakenedMutant
    {frame : Exec.Frame} {program : Prog} {storage codeAddress other : Adr}
    (exact : frame.exactInvocation program storage codeAddress) :
    frame.exactInvocation program other codeAddress := by
  exact exact
""",
    "-- CODE-IDENTITY-MUTANT-CONTROL": r"""
private theorem codeIdentityWeakenedMutant
    {frame : Exec.Frame} {program : Prog} {storage codeAddress other : Adr}
    (exact : frame.exactInvocation program storage codeAddress) :
    frame.exactInvocation program storage other := by
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


def load_ownership_parser():
    path = ROOT / "scripts" / "check-extraction-ownership.py"
    spec = importlib.util.spec_from_file_location("extraction_ownership", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load the declaration ownership parser")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


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
            expected_failures = {
                "-- TERMINAL-ERROR-MUTANT-CONTROL": ("Tactic `rfl` failed",),
                "-- RAW-ERROR-PRUNE-MUTANT-CONTROL": ("Tactic `rfl` failed",),
                "-- RAW-BYTE-SCAN-MUTANT-CONTROL":
                    ("Tactic `decide` proved that the proposition",),
                "-- FIRST-WRITER-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- IDENTITY-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- CODE-IDENTITY-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
            }[marker]
            if not any(expected in evidence for expected in expected_failures):
                return fail(f"mutant `{marker}` failed unexpectedly", mutant)

    weth_source = WETH.read_text(encoding="utf-8")
    bridge_tokens = (
        "theorem Exec.Frame.NinstOccurrence.toCommon\n",
        "common.node =\n",
        "(⟨pc, frame.sevm, stepPre, frame.out, current⟩ : Blanc.Exec.Deriv)",
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
    try:
        ownership = load_ownership_parser()
    except (OSError, RuntimeError) as exc:
        return fail(f"could not load fail-closed ownership parser: {exc}")
    moved_names = {f'Blanc.{row["declaration"]}' for row in mappings}
    weth_declarations: dict[str, tuple[pathlib.Path, str, int]] = {}
    alias_hits: list[tuple[pathlib.Path, str, int, str]] = []
    for path in sorted(ROOT.glob("Blanc/Weth10*.lean")):
        for name, (kind, line) in ownership.declarations(path).items():
            weth_declarations[name] = (path, kind, line)
        for name, line, form in ownership.donor_aliases_or_exports(
            path, moved_names
        ):
            alias_hits.append((path, name, line, form))
    if alias_hits:
        path, name, line, form = alias_hits[0]
        return fail(
            f"WETH donor {form} survives for `{name}` at "
            f"{path.relative_to(ROOT)}:{line}"
        )
    for index, row in enumerate(mappings, 1):
        if not isinstance(row, dict) or set(row) != {
            "declaration", "kind", "donorModule", "commonModule"
        } or row["kind"] != "theorem":
            return fail(f"occurrence move row {index} has invalid schema")
        fqn = f'Blanc.{row["declaration"]}'
        common_path = ROOT / row["commonModule"]
        common_declarations = ownership.declarations(common_path)
        if common_declarations.get(fqn, (None,))[0] != row["kind"]:
            return fail(f"common owner missing or wrong-kind `{fqn}`")
        if fqn in weth_declarations:
            path, kind, line = weth_declarations[fqn]
            return fail(
                f"WETH donor declaration survives for `{fqn}` as {kind} at "
                f"{path.relative_to(ROOT)}:{line}"
            )
        token = f'{row["kind"]} {row["declaration"]}'
        common = common_path.read_text(encoding="utf-8")
        if token not in common or token in common.replace(
            token, f'{row["kind"]} removed_owner', 1
        ):
            return fail(f"common-owner removal control failed for `{fqn}`")

    # Parser-channel controls: exact donor aliases and missing/wrong-kind
    # common owners must be detected independently of literal source search.
    first = mappings[0]
    first_fqn = f'Blanc.{first["declaration"]}'
    with tempfile.TemporaryDirectory(prefix="occurrence-ownership-controls-") as temp:
        temp_root = pathlib.Path(temp)
        alias_path = temp_root / "DonorAlias.lean"
        alias_path.write_text(
            "namespace Blanc\n"
            f"alias {first_fqn} => {first['declaration']}\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        alias_control = ownership.donor_aliases_or_exports(
            alias_path, {first_fqn}
        )
        if not alias_control or alias_control[0][0] != first_fqn:
            return fail("ownership parser donor-alias negative control failed")

        common_path = ROOT / first["commonModule"]
        common_source = common_path.read_text(encoding="utf-8")
        token = f'{first["kind"]} {first["declaration"]}'
        missing_path = temp_root / "CommonMissing.lean"
        missing_path.write_text(
            common_source.replace(token, "theorem removed_owner", 1),
            encoding="utf-8",
        )
        if first_fqn in ownership.declarations(missing_path):
            return fail("ownership parser common-missing negative control failed")
        wrong_kind_path = temp_root / "CommonWrongKind.lean"
        wrong_kind_path.write_text(
            common_source.replace(token, f'abbrev {first["declaration"]}', 1),
            encoding="utf-8",
        )
        if ownership.declarations(wrong_kind_path).get(
            first_fqn, (None,)
        )[0] != "abbrev":
            return fail("ownership parser wrong-kind negative control failed")

    settlement = run([sys.executable, "scripts/check-execution-settlement.py"])
    if settlement.returncode != 0:
        return fail("CREATE settlement/raw-commit control failed", settlement)
    if not settlement.stdout.startswith("OK — execution settlement:"):
        return fail("CREATE settlement control verdict drifted", settlement)

    print(
        "OK — execution occurrence: 13 concrete controls; 6 Lean mutants; "
        "WETH bridge-removal mutant; 9 moved-owner + 3 ownership-parser controls; "
        "CREATE raw-commit mutant"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
