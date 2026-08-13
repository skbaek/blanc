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
RAW_ATTRIBUTION_OWNERSHIP = (
    ROOT / "scripts" / "check-execution-raw-attribution-ownership.py"
)
EXPECTED = "[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]"

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
    "-- COMMITMENT-FILTERED-RAW-CHILD-MUTANT-CONTROL": r"""
private theorem commitmentFilteredRawChildMutant (w : CaughtCallFixture) :
    Exec.rawFrameRoots w.call.run =
      w.call.root :: Exec.rawFrameDescendants w.call.next := by
  rfl
""",
    "-- UNCONDITIONAL-MAIN-CURSOR-OOG-MUTANT-CONTROL": r"""
private theorem unconditionalMainCursorAfterEntryOogMutant
    (w : EntryOogFixture) :
    (Exec.rawNodes w.run).map (fun node => node.pc) = [0, 1] := by
  rfl
""",
    "-- CHILD-CONTINUATION-ORDER-MUTANT-CONTROL": r"""
private theorem childContinuationOrderReversalMutant (w : CallFixture) :
    Exec.rawFrameRoots w.run =
      w.root ::
        (Exec.rawFrameDescendants w.next ++ Exec.rawFrameRoots w.child) := by
  rfl
""",
    "-- DUPLICATE-CHILD-ROOT-MUTANT-CONTROL": r"""
private theorem duplicateChildRootConstructionMutant (w : CallFixture) :
    Exec.rawFrameRoots w.run =
      w.root ::
        (Exec.rawFrameRoots w.child ++ Exec.rawFrameRoots w.child ++
          Exec.rawFrameDescendants w.next) := by
  rfl
""",
    "-- CONTINUATION-AS-FRAME-MUTANT-CONTROL": r"""
private theorem continuationAsFrameMutant (w : CallFixture) :
    Exec.rawFrameRoots w.run =
      w.root :: (Exec.rawFrameRoots w.child ++ Exec.rawFrameRoots w.next) := by
  rfl
""",
    "-- COMMIT-REQUIRED-ATTRIBUTION-MUTANT-CONTROL": r"""
private theorem commitRequiredAttributionMutant (w : TerminalSourceFixture) :
    sourceProgram.acceptsSstoreSite ⟨0, []⟩
        w.occurrence.node.pc = true ∧
      Execution.commits (.error w.err) = true := by
  exact ⟨w.exactAttribution.2.2, rfl⟩
""",
    "-- RUNERR-CHILD-PRUNING-MUTANT-CONTROL": r"""
private theorem runErrChildPruningMutant (w : RunErrFixture) :
    Exec.rawFrameRoots w.run = [w.root] := by
  rfl
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
                "-- COMMITMENT-FILTERED-RAW-CHILD-MUTANT-CONTROL":
                    ("Tactic `rfl` failed",),
                "-- UNCONDITIONAL-MAIN-CURSOR-OOG-MUTANT-CONTROL":
                    ("Tactic `rfl` failed",),
                "-- CHILD-CONTINUATION-ORDER-MUTANT-CONTROL":
                    ("Tactic `rfl` failed",),
                "-- DUPLICATE-CHILD-ROOT-MUTANT-CONTROL":
                    ("Tactic `rfl` failed",),
                "-- CONTINUATION-AS-FRAME-MUTANT-CONTROL":
                    ("Tactic `rfl` failed",),
                "-- COMMIT-REQUIRED-ATTRIBUTION-MUTANT-CONTROL":
                    ("Application type mismatch",),
                "-- RUNERR-CHILD-PRUNING-MUTANT-CONTROL":
                    ("Tactic `rfl` failed",),
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

    # Parser-channel controls: exact donor aliases/re-exports and missing or
    # wrong-kind common owners must be detected independently of literal
    # source search.
    first = mappings[0]
    first_fqn = f'Blanc.{first["declaration"]}'
    export_namespace, export_item = first_fqn.rsplit(".", 1)
    ancestor = export_namespace.split(".")[0]
    relative_owner = ".".join(export_namespace.split(".")[1:])
    with tempfile.TemporaryDirectory(prefix="occurrence-ownership-controls-") as temp:
        temp_root = pathlib.Path(temp)
        command_controls: list[tuple[pathlib.Path, str]] = []
        wrapped_alias_path = temp_root / "DonorWrappedAlias.lean"
        wrapped_alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10\n"
            "set_option linter.unusedVariables false in\n"
            f"alias occurrenceWrappedLegacy := {first_fqn}\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        wrapped_alias_control = ownership.donor_aliases_or_exports(
            wrapped_alias_path, {first_fqn}
        )
        if not wrapped_alias_control or wrapped_alias_control[0][0] != first_fqn:
            return fail("ownership parser donor-wrapped-alias negative control failed")
        command_controls.append((wrapped_alias_path, "wrapped alias"))

        alias_path = temp_root / "DonorAlias.lean"
        alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10\n"
            "@[deprecated] public alias occurrenceLegacy :=\n"
            f"  {first_fqn}\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        command_controls.append((alias_path, "protected multiline alias"))
        alias_control = ownership.donor_aliases_or_exports(
            alias_path, {first_fqn}
        )
        if not alias_control or alias_control[0][0] != first_fqn:
            return fail("ownership parser donor-alias negative control failed")

        relative_alias_path = temp_root / "DonorRelativeAlias.lean"
        relative_alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc\n"
            "namespace Weth10\n"
            "alias occurrenceRelativeLegacy :=\n"
            f"  {relative_owner}.{export_item}\n"
            "end Weth10\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        command_controls.append((relative_alias_path, "relative multiline alias"))
        relative_alias_control = ownership.donor_aliases_or_exports(
            relative_alias_path, {first_fqn}
        )
        if (not relative_alias_control or
                relative_alias_control[0][0] != first_fqn):
            return fail(
                "ownership parser donor-relative-alias negative control failed"
            )

        root_alias_path = temp_root / "DonorRootAlias.lean"
        root_alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10\n"
            "alias occurrenceRootLegacy :=\n"
            f"  _root_.{first_fqn}\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        command_controls.append((root_alias_path, "root multiline alias"))
        root_alias_control = ownership.donor_aliases_or_exports(
            root_alias_path, {first_fqn}
        )
        if not root_alias_control or root_alias_control[0][0] != first_fqn:
            return fail("ownership parser donor-root-alias negative control failed")

        export_path = temp_root / "DonorExport.lean"
        export_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10\n"
            f"export {export_namespace} ({export_item})\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        command_controls.append((export_path, "absolute export"))
        export_control = ownership.donor_aliases_or_exports(
            export_path, {first_fqn}
        )
        if not export_control or export_control[0][0] != first_fqn:
            return fail("ownership parser donor-export negative control failed")

        relative_export_path = temp_root / "DonorRelativeExport.lean"
        relative_export_path.write_text(
            "import Blanc.CommonProofs\n"
            f"namespace {ancestor}\n"
            "namespace Weth10\n"
            f"export {relative_owner} ({export_item})\n"
            "end Weth10\n"
            f"end {ancestor}\n",
            encoding="utf-8",
        )
        command_controls.append((relative_export_path, "relative export"))
        relative_export_control = ownership.donor_aliases_or_exports(
            relative_export_path, {first_fqn}
        )
        if (not relative_export_control or
                relative_export_control[0][0] != first_fqn):
            return fail(
                "ownership parser donor-relative-export negative control failed"
            )

        root_export_path = temp_root / "DonorRootExport.lean"
        root_export_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc\n"
            "namespace Weth10\n"
            f"export _root_.{export_namespace} ({export_item})\n"
            "end Weth10\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        command_controls.append((root_export_path, "root export"))
        root_export_control = ownership.donor_aliases_or_exports(
            root_export_path, {first_fqn}
        )
        if not root_export_control or root_export_control[0][0] != first_fqn:
            return fail(
                "ownership parser donor-root-export negative control failed"
            )

        for control_path, label in command_controls:
            compiled_control = run(["lake", "env", "lean", str(control_path)])
            if compiled_control.returncode != 0:
                return fail(
                    f"ownership parser {label} control is not valid Lean",
                    compiled_control,
                )

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

    raw_ownership = run(
        [sys.executable, str(RAW_ATTRIBUTION_OWNERSHIP), "--negative-controls"]
    )
    if raw_ownership.returncode != 0:
        return fail("raw-attribution owner/shadow control failed", raw_ownership)
    if not raw_ownership.stdout.startswith("OK — raw attribution ownership:"):
        return fail("raw-attribution owner/shadow verdict drifted", raw_ownership)

    settlement = run([sys.executable, "scripts/check-execution-settlement.py"])
    if settlement.returncode != 0:
        return fail("CREATE settlement/raw-commit control failed", settlement)
    if not settlement.stdout.startswith("OK — execution settlement:"):
        return fail("CREATE settlement control verdict drifted", settlement)

    print(
        "OK — execution occurrence: 16 concrete controls; 13 Lean mutants; "
        "WETH bridge-removal mutant; 9 moved-owner + 9 ownership-parser controls; "
        "24 raw-attribution owners + exact signature + 4 controls; "
        "CREATE raw-commit mutant"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
