#!/usr/bin/env python3
"""Fail-closed occurrence, direct-code, ownership, and mutant assurance."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "ExecutionOccurrenceRegression.lean"
DIRECT_CODE_FIXTURE = ROOT / "scripts" / "ExecutionOccurrenceControls.lean"
WETH = ROOT / "Blanc" / "Weth10HolderFlowCompiled.lean"
MOVE_MANIFEST = ROOT / "scripts" / "execution-occurrence-lift-manifest.json"
RAW_ATTRIBUTION_OWNERSHIP = (
    ROOT / "scripts" / "check-execution-raw-attribution-ownership.py"
)
EXPECTED = "[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]"
DIRECT_CODE_EXPECTED = ""

CANONICAL_DIRECT_CODE = "Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget"
CANONICAL_DIRECT_CODE_LOCAL = "Xinst.step_spawn_codeAddress_eq_currentTarget"
RETIRED_DIRECT_CODE = "Blanc.Weth10.xinst_spawn_direct"

DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS = {
    "Blanc.ExecutionOccurrenceControls.call_direct_codeAddress_control",
    "Blanc.ExecutionOccurrenceControls.statcall_direct_codeAddress_control",
    "Blanc.ExecutionOccurrenceControls.create_empty_target_control",
    "Blanc.ExecutionOccurrenceControls.create2_empty_target_control",
    "Blanc.ExecutionOccurrenceControls.callcode_same_target_control",
    "Blanc.ExecutionOccurrenceControls.delegatecall_same_target_control",
    "Blanc.ExecutionOccurrenceControls.required_positive_controls",
}

DIRECT_CODE_MUTANTS = {
    "-- DIRECT-CODE-HCODE-MUTANT-CONTROL": (r"""
private theorem directCodeHcodePremiseDeletedMutant
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hs : Xinst.step sevm devm .create = .spawn frame resume)
    (_hne : sevm.currentTarget ≠ frame.inner.currentTarget) :
    frame.inner.codeAddress = some frame.inner.currentTarget := by
  have boundary := create_empty_target_control hs
  rw [boundary.2]
  rfl
""", ("Tactic `rfl` failed", "none = some")),
    "-- DIRECT-CODE-HFOREIGN-MUTANT-CONTROL": (r"""
private theorem directCodeHforeignPremiseDeletedMutant
    : Xinst.step dynamicSevm callcodePre .callcode =
          .spawn callcodeFrame callcodeResume ∧
        callcodePre.getCode callcodeFrame.inner.currentTarget ≠ .empty ∧
        callcodeFrame.inner.codeAddress =
          some callcodeFrame.inner.currentTarget := by
  refine ⟨callcode_spawn, callcode_same_target_control.2.2.1, ?_⟩
  rw [callcode_same_target_control.2.2.2.1,
    callcode_same_target_control.2.1]
  rfl
""", ("Tactic `rfl` failed", "some dynamicSevm.currentTarget")),
}

REQUIRED_POSITIVE_THEOREMS = {
    "Blanc.ExecutionOccurrenceRegression.terminalError_occurs",
    "Blanc.ExecutionOccurrenceRegression.rootWriteControls",
    "Blanc.ExecutionOccurrenceRegression.rootWriteRawFrameControls",
    "Blanc.ExecutionOccurrenceRegression.history_publicLastWriter",
    "Blanc.ExecutionOccurrenceRegression.payload_not_source_sstore",
    "Blanc.ExecutionOccurrenceRegression.concrete_source_and_identity_controls",
    "Blanc.ExecutionOccurrenceRegression.concrete_raw_attribution_controls",
    "Blanc.ExecutionOccurrenceRegression.coincident_identity_top_level_control",
    "Blanc.ExecutionOccurrenceRegression.concrete_successful_source_outcomes",
    "Blanc.ExecutionOccurrenceRegression.Chronology.chronology_branch_eq_before_sstore_control",
    "Blanc.ExecutionOccurrenceRegression.Chronology.chronology_call_eq_before_sstore_control",
    "Blanc.ExecutionOccurrenceRegression.Chronology.chronology_error_suffix_control",
    "Blanc.ExecutionOccurrenceRegression.concreteCall_orders",
    "Blanc.ExecutionOccurrenceRegression.concreteRawFrameRoot_orders",
    "Blanc.ExecutionOccurrenceRegression.concreteRunErr_rawFrameRoots",
    "Blanc.ExecutionOccurrenceRegression.RawChildAttribution.CaughtFixture.control",
    "Blanc.ExecutionOccurrenceRegression.RawChildAttribution.RollbackFixture.control",
    "Blanc.ExecutionOccurrenceRegression.RawChildAttribution.concrete_controls",
    "Blanc.ExecutionOccurrenceRegression.RawChildAttribution.concrete_child_identity_boundaries",
    "Blanc.ExecutionOccurrenceRegression.required_positive_controls",
}

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
    "-- CHILD-AS-PARENT-IDENTITY-MUTANT-CONTROL": r"""
private theorem childAsParentIdentityMutant
    (w : RawChildAttribution.CaughtFixture) :
    w.call.root.exactInvocation RawChildAttribution.caughtProgram
      RawChildAttribution.callTarget RawChildAttribution.callTarget := by
  exact w.call.childExact RawChildAttribution.caughtProgram w.compiled
""",
    "-- MISSING-PARENT-PREFIX-MUTANT-CONTROL": r"""
private theorem missingParentPrefixMutant
    (w : RawChildAttribution.CaughtFixture) :
    ∃ occurrence : Exec.NinstOccurrence w.call.root,
      occurrence.instruction = .reg .sstore ∧
      Exec.Deriv.ParentPrefix w.call.root occurrence.node := by
  rcases w.control with
    ⟨selected, exact, occurrence, instruction, sameFrame, pc, accepted⟩
  exact ⟨occurrence, instruction, sameFrame⟩
""",
    "-- CHRONOLOGY-REJECTED-BRANCH-MUTANT-CONTROL": r"""
private theorem chronologyRejectedBranchMutant :
    ∃ w : Chronology.Fixture Chronology.branchEqProgram
        Chronology.branchEqCode Chronology.branchEqPre,
      ∃ mainCursor : Exec.Deriv.SourceCursor w.root
          Chronology.branchEqProgram ⟨0, []⟩ Chronology.branchEqProgram.main,
        ∃ rejectedCursor : Exec.Deriv.SourceCursor w.root
            Chronology.branchEqProgram ⟨0, [.branchRight]⟩
            (.next (.reg .eq) (.last .rev)),
          Exec.Deriv.SourceCursor.Chronology
            mainCursor rejectedCursor w.target := by
  rcases Chronology.chronology_branch_eq_before_sstore_control with
    ⟨w, mainCursor, guardCursor, route, chronology, distinct, strict⟩
  exact ⟨w, mainCursor, guardCursor, chronology⟩
""",
    "-- CHRONOLOGY-ORDER-REVERSAL-MUTANT-CONTROL": r"""
private theorem chronologyOrderReversalMutant :
    ∃ w : Chronology.Fixture Chronology.branchEqProgram
        Chronology.branchEqCode Chronology.branchEqPre,
      ∃ mainCursor : Exec.Deriv.SourceCursor w.root
          Chronology.branchEqProgram ⟨0, []⟩ Chronology.branchEqProgram.main,
        ∃ guardCursor : Exec.Deriv.SourceCursor w.root
            Chronology.branchEqProgram ⟨0, [.branchLeft]⟩
            (.next (.reg .eq) (.next (.reg .sstore) (.last .stop))),
          Exec.Deriv.lt guardCursor.node w.target := by
  rcases Chronology.chronology_branch_eq_before_sstore_control with
    ⟨w, mainCursor, guardCursor, route, chronology, distinct, strict⟩
  exact ⟨w, mainCursor, guardCursor, strict⟩
""",
    "-- CHRONOLOGY-MISSING-INITIAL-PREFIX-MUTANT-CONTROL": r"""
private theorem chronologyMissingInitialPrefixMutant :
    ∃ w : Chronology.Fixture Chronology.branchEqProgram
        Chronology.branchEqCode Chronology.branchEqPre,
      ∃ mainCursor : Exec.Deriv.SourceCursor w.root
          Chronology.branchEqProgram ⟨0, []⟩ Chronology.branchEqProgram.main,
        ∃ guardCursor : Exec.Deriv.SourceCursor w.root
            Chronology.branchEqProgram ⟨0, [.branchLeft]⟩
            (.next (.reg .eq) (.next (.reg .sstore) (.last .stop))),
          Exec.Deriv.SourceCursor.Chronology
            mainCursor guardCursor w.target := by
  rcases Chronology.chronology_branch_eq_before_sstore_control with
    ⟨w, mainCursor, guardCursor, route, chronology, distinct, strict⟩
  exact ⟨w, mainCursor, guardCursor,
    ⟨.refl guardCursor.node, chronology.cursorToTarget⟩⟩
""",
    "-- CHRONOLOGY-MISSING-TARGET-PREFIX-MUTANT-CONTROL": r"""
private theorem chronologyMissingTargetPrefixMutant :
    ∃ w : Chronology.Fixture Chronology.branchEqProgram
        Chronology.branchEqCode Chronology.branchEqPre,
      ∃ mainCursor : Exec.Deriv.SourceCursor w.root
          Chronology.branchEqProgram ⟨0, []⟩ Chronology.branchEqProgram.main,
        ∃ guardCursor : Exec.Deriv.SourceCursor w.root
            Chronology.branchEqProgram ⟨0, [.branchLeft]⟩
            (.next (.reg .eq) (.next (.reg .sstore) (.last .stop))),
          Exec.Deriv.SourceCursor.Chronology
            mainCursor guardCursor w.target := by
  rcases Chronology.chronology_branch_eq_before_sstore_control with
    ⟨w, mainCursor, guardCursor, route, chronology, distinct, strict⟩
  exact ⟨w, mainCursor, guardCursor,
    ⟨chronology.initialToCursor, .refl guardCursor.node⟩⟩
""",
    "-- CHRONOLOGY-SYNTAX-ONLY-MUTANT-CONTROL": r"""
private theorem chronologySyntaxOnlyMutant
    {root : Exec.Deriv} {program : Prog}
    {leftPath rightPath : Prog.SourcePath} {leftSource rightSource : Func}
    (left : Exec.Deriv.SourceCursor root program leftPath leftSource)
    (right : Exec.Deriv.SourceCursor root program rightPath rightSource)
    (_sourcePathOnly : leftPath.steps.isPrefixOf rightPath.steps = true)
    (samePc : left.pc = right.pc) :
    Exec.Deriv.ParentPrefix left.node right.node := by
  cases samePc
  exact .refl left.node
""",
    "-- CHRONOLOGY-COMMIT-REQUIRED-MUTANT-CONTROL": r"""
private theorem chronologyCommitRequiredMutant :
    ∃ w : Chronology.Fixture Chronology.errorChronologyProgram
        Chronology.errorChronologyCode Chronology.errorChronologyPre,
      Execution.commits w.out = true := by
  rcases Chronology.chronology_error_suffix_control with
    ⟨w, mainCursor, route, chronology, distinct, strict, notCommitted⟩
  exact ⟨w, notCommitted⟩
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


def missing_positive_theorems(ownership, path: pathlib.Path) -> list[str]:
    declarations = ownership.declarations(path)
    return sorted(
        name for name in REQUIRED_POSITIVE_THEOREMS
        if declarations.get(name, (None,))[0] != "theorem"
    )


def missing_public_theorems(
    ownership, path: pathlib.Path, required: set[str]
) -> list[str]:
    """Require plain public theorem commands, not private fixture helpers."""
    source = ownership.strip_comments(path.read_text(encoding="utf-8"))
    lines = source.splitlines()
    declarations = ownership.declarations(path)
    missing: list[str] = []
    for name in sorted(required):
        got = declarations.get(name)
        if got is None or got[0] != "theorem":
            missing.append(name)
            continue
        line = lines[got[1] - 1]
        short = name.rsplit(".", 1)[-1]
        if re.match(rf"^\s*theorem\s+{re.escape(short)}\b", line) is None:
            missing.append(name)
    return missing


def control_signature_pins() -> list[dict[str, str]]:
    """Load the exact public-control proposition pins fail-closed."""
    manifest = json.loads(MOVE_MANIFEST.read_text(encoding="utf-8"))
    pins = manifest.get("controlSignaturePins")
    if not isinstance(pins, list):
        raise ValueError("controlSignaturePins is not a list")
    return pins


def normalized_header(
    ownership, path: pathlib.Path, local_declaration: str
) -> str:
    """Return one comment/whitespace-normalized theorem header through `:=`."""
    source = ownership.strip_comments(path.read_text(encoding="utf-8"))
    token = f"theorem {local_declaration}"
    if source.count(token) != 1:
        display = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        raise ValueError(f"expected exactly one `{token}` in {display}")
    start = source.index(token)
    end = source.find(":= by", start)
    if end < 0:
        raise ValueError(
            f"could not find declaration-level `:= by` for `{local_declaration}`"
        )
    return " ".join(source[start:end + 2].split())


def direct_code_statement_copies(
    ownership, paths: list[pathlib.Path]
) -> list[tuple[pathlib.Path, str, int]]:
    """Find parser-identified contract declarations copying the proposition."""
    required = (
        "Xinst.step", "= .spawn", "currentTarget ≠", ".getCode",
        "≠ .empty", ".codeAddress = some", ".inner.currentTarget",
    )
    found: list[tuple[pathlib.Path, str, int]] = []
    for path in paths:
        source = ownership.strip_comments(path.read_text(encoding="utf-8"))
        lines = source.splitlines(keepends=True)
        offsets: list[int] = []
        cursor = 0
        for line in lines:
            offsets.append(cursor)
            cursor += len(line)
        for full_name, (kind, line) in ownership.declarations(path).items():
            if kind not in {"theorem", "lemma"} or line < 1 or line > len(lines):
                continue
            start = offsets[line - 1]
            short = full_name.rsplit(".", 1)[-1]
            match = re.search(
                rf"\b(?:theorem|lemma)\s+{re.escape(short)}\b",
                source[start:],
            )
            if match is None:
                continue
            declaration_start = start + match.start()
            end = source.find(":=", start + match.end())
            if end < 0:
                continue
            header = " ".join(source[declaration_start:end + 2].split())
            if all(token in header for token in required):
                found.append((path, full_name, line))
    return found


def first_party_lean_paths() -> list[pathlib.Path]:
    paths = sorted((ROOT / "Blanc").rglob("*.lean"))
    root_module = ROOT / "Blanc.lean"
    if root_module.is_file():
        paths.insert(0, root_module)
    return paths


def owner_locations(
    ownership, paths: list[pathlib.Path], declaration: str
) -> list[tuple[pathlib.Path, str, int]]:
    found: list[tuple[pathlib.Path, str, int]] = []
    for path in paths:
        got = ownership.declarations(path).get(declaration)
        if got is not None:
            found.append((path, got[0], got[1]))
    return found


def direct_code_reference_count(ownership, source: str) -> int:
    clean = ownership.strip_comments(source)
    pattern = re.compile(
        rf"(?<![A-Za-z0-9_']){re.escape(CANONICAL_DIRECT_CODE_LOCAL)}"
        rf"(?![A-Za-z0-9_'])"
    )
    return len(pattern.findall(clean))


def consumer_errors(
    ownership,
    sources: dict[pathlib.Path, str],
    required_consumers: list[dict[str, object]],
) -> list[str]:
    expected = {
        ROOT / str(row["module"]): int(row["references"])
        for row in required_consumers
    }
    errors: list[str] = []
    for path, source in sources.items():
        got = direct_code_reference_count(ownership, source)
        want = expected.get(path, 0)
        if got != want:
            rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
            errors.append(
                f"canonical consumer count drifted at {rel}: found {got}, expected {want}"
            )
    missing_paths = sorted(set(expected) - set(sources))
    for path in missing_paths:
        errors.append(f"required canonical consumer is absent: {path.relative_to(ROOT)}")
    return errors


def contract_ownership_errors(
    ownership, paths: list[pathlib.Path], protected_names: set[str]
) -> list[str]:
    """Reject exact survivors, basename shadows, and aliases/exports."""
    errors: list[str] = []
    forbidden_basenames = {name.rsplit(".", 1)[-1] for name in protected_names}
    for path in paths:
        rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        for name, (kind, line) in ownership.declarations(path).items():
            if name in protected_names:
                errors.append(
                    f"contract donor declaration survives for `{name}` as {kind} "
                    f"at {rel}:{line}"
                )
            elif name.rsplit(".", 1)[-1] in forbidden_basenames:
                errors.append(
                    f"contract basename shadow survives for `{name}` as {kind} "
                    f"at {rel}:{line}"
                )
        for name, line, form in ownership.donor_aliases_or_exports(
            path, protected_names
        ):
            errors.append(
                f"contract {form} survives for `{name}` at {rel}:{line}"
            )
    return errors


def check_direct_code_fixture(ownership) -> int | None:
    if not DIRECT_CODE_FIXTURE.is_file():
        return fail(
            "direct-code fixture is missing: "
            "scripts/ExecutionOccurrenceControls.lean"
        )
    source = DIRECT_CODE_FIXTURE.read_text(encoding="utf-8")
    missing = missing_public_theorems(
        ownership, DIRECT_CODE_FIXTURE, DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS
    )
    if missing:
        return fail(
            "direct-code positive proof declarations are absent, private, or "
            "wrong-kind: " + ", ".join(missing)
        )
    try:
        pins = control_signature_pins()
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        return fail(f"direct-code control signature pins are unreadable: {exc}")
    expected_pin_names = sorted(DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS)
    if (len(pins) != len(expected_pin_names) or
            sorted(pin.get("declaration") for pin in pins
                   if isinstance(pin, dict)) != expected_pin_names or
            any(not isinstance(pin, dict) or
                set(pin) != {"declaration", "header"} or
                not isinstance(pin["header"], str) or not pin["header"]
                for pin in pins)):
        return fail("direct-code public-control signature pin inventory drifted")
    for pin in pins:
        short = pin["declaration"].rsplit(".", 1)[-1]
        try:
            actual = normalized_header(ownership, DIRECT_CODE_FIXTURE, short)
        except (OSError, ValueError) as exc:
            return fail(f"direct-code control header is unreadable: {exc}")
        if actual != pin["header"]:
            return fail(
                "direct-code public-control normalized header drifted: "
                f"{pin['declaration']}"
            )
    for marker in DIRECT_CODE_MUTANTS:
        if source.count(marker) != 1:
            return fail(
                f"direct-code fixture must contain exactly one `{marker}` marker"
            )

    positive = run(["lake", "env", "lean", str(DIRECT_CODE_FIXTURE)])
    if positive.returncode != 0:
        return fail("direct-code positive fixture did not compile", positive)
    if positive.stdout.strip() != DIRECT_CODE_EXPECTED or positive.stderr:
        return fail("direct-code positive fixture output drifted", positive)

    with tempfile.TemporaryDirectory(prefix="execution-direct-code-") as temp:
        temp_root = pathlib.Path(temp)
        for index, (marker, (mutant_source, diagnostics)) in enumerate(
            DIRECT_CODE_MUTANTS.items()
        ):
            path = temp_root / f"ExecutionDirectCodeMutant{index}.lean"
            path.write_text(
                source.replace(marker, mutant_source), encoding="utf-8"
            )
            result = run(["lake", "env", "lean", str(path)])
            evidence = result.stdout + result.stderr
            if result.returncode == 0:
                return fail(
                    f"direct-code mutant `{marker}` unexpectedly compiled", result
                )
            if not all(diagnostic in evidence for diagnostic in diagnostics):
                return fail(
                    f"direct-code mutant `{marker}` failed unexpectedly", result
                )

        for index, theorem in enumerate(
            sorted(DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS)
        ):
            short = theorem.rsplit(".", 1)[-1]
            token = f"theorem {short}"
            if source.count(token) != 1:
                return fail(
                    f"direct-code deletion cannot uniquely locate `{theorem}`"
                )
            changed = source.replace(token, f"theorem {short}_removed", 1)
            changed += f"\n#check {theorem}\n"
            path = temp_root / f"ExecutionDirectCodeDeleted{index}.lean"
            path.write_text(changed, encoding="utf-8")
            result = run(["lake", "env", "lean", str(path)])
            evidence = result.stdout + result.stderr
            if result.returncode == 0 or short not in evidence:
                return fail(
                    f"direct-code live deletion did not fail through `{theorem}`",
                    result,
                )

        first_pin = pins[0]
        short = first_pin["declaration"].rsplit(".", 1)[-1]
        header_mutant = source.replace(
            "directCallPre.getCode callFrame.inner.currentTarget ≠ .empty",
            "True",
            1,
        )
        if header_mutant == source:
            return fail("direct-code control-header mutant could not mutate source")
        header_mutant_path = temp_root / "DirectCodeControlHeaderMutant.lean"
        header_mutant_path.write_text(header_mutant, encoding="utf-8")
        try:
            mutated = normalized_header(ownership, header_mutant_path, short)
        except (OSError, ValueError) as exc:
            return fail(f"direct-code control-header mutant is unreadable: {exc}")
        if mutated == first_pin["header"]:
            return fail("direct-code control-header mutation was accepted")
    return None


def main() -> int:
    source = FIXTURE.read_text(encoding="utf-8")
    for marker in [*MUTANTS, "-- WETH-BRIDGE-MUTANT-CONTROL"]:
        if source.count(marker) != 1:
            return fail(f"fixture must contain exactly one `{marker}` marker")

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

    direct_code_error = check_direct_code_fixture(ownership)
    if direct_code_error is not None:
        return direct_code_error

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
                "-- CHILD-AS-PARENT-IDENTITY-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- MISSING-PARENT-PREFIX-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- CHRONOLOGY-REJECTED-BRANCH-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- CHRONOLOGY-ORDER-REVERSAL-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- CHRONOLOGY-MISSING-INITIAL-PREFIX-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- CHRONOLOGY-MISSING-TARGET-PREFIX-MUTANT-CONTROL":
                    ("Application type mismatch", "Type mismatch"),
                "-- CHRONOLOGY-SYNTAX-ONLY-MUTANT-CONTROL":
                    ("Dependent elimination failed",),
                "-- CHRONOLOGY-COMMIT-REQUIRED-MUTANT-CONTROL":
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
    manifest_keys = {
        "schema", "contractModuleGlobs", "mappings", "retiredDeclarations",
        "signaturePins", "controlSignaturePins", "requiredConsumers",
    }
    if (not isinstance(manifest, dict) or
            set(manifest) != manifest_keys or manifest["schema"] != 3):
        return fail("occurrence move manifest schema drifted")
    contract_globs = manifest["contractModuleGlobs"]
    if contract_globs != ["Blanc/Weth10*.lean", "Blanc/Lido*.lean"]:
        return fail("occurrence move manifest contract-module globs drifted")
    mappings = manifest["mappings"]
    if not isinstance(mappings, list) or len(mappings) != 10:
        return fail("occurrence move manifest must contain exactly 10 rows")
    for index, row in enumerate(mappings, 1):
        if not isinstance(row, dict) or set(row) != {
            "declaration", "kind", "donorModule", "commonModule"
        } or row["kind"] != "theorem" or not all(
            isinstance(row[key], str) and row[key]
            for key in ("declaration", "donorModule", "commonModule")
        ):
            return fail(f"occurrence move row {index} has invalid schema")
    if len({row["declaration"] for row in mappings}) != len(mappings):
        return fail("occurrence move declarations must be unique")
    canonical_mapping = {
        "declaration": CANONICAL_DIRECT_CODE_LOCAL,
        "kind": "theorem",
        "donorModule": "Blanc/Weth10HolderFlowEthExec.lean",
        "commonModule": "Blanc/CommonProofs.lean",
    }
    if mappings.count(canonical_mapping) != 1:
        return fail("canonical direct-code move row is absent or drifted")

    retired = manifest["retiredDeclarations"]
    expected_retired = [{
        "declaration": RETIRED_DIRECT_CODE,
        "kind": "theorem",
        "donorModule": "Blanc/Weth10HolderFlowExecAccounting.lean",
        "replacement": CANONICAL_DIRECT_CODE,
    }]
    if retired != expected_retired:
        return fail("retired direct-code declaration row drifted")

    signature_pins = manifest["signaturePins"]
    if (not isinstance(signature_pins, list) or len(signature_pins) != 1 or
            not isinstance(signature_pins[0], dict) or
            set(signature_pins[0]) != {"declaration", "header"} or
            signature_pins[0]["declaration"] != CANONICAL_DIRECT_CODE or
            not isinstance(signature_pins[0]["header"], str) or
            not signature_pins[0]["header"]):
        return fail("canonical direct-code signature pin drifted")

    required_consumers = manifest["requiredConsumers"]
    expected_consumers = [
        {"module": "Blanc/Weth10HolderFlowEthExec.lean", "references": 1},
        {
            "module": "Blanc/Weth10HolderFlowExecAccounting.lean",
            "references": 1,
        },
        {"module": "Blanc/Weth10AllowanceRecursion.lean", "references": 2},
        {
            "module": "Blanc/LidoCircuitBreakerOwnerClosure.lean",
            "references": 1,
        },
    ]
    if required_consumers != expected_consumers:
        return fail("canonical direct-code consumer inventory drifted")

    moved_names = {f'Blanc.{row["declaration"]}' for row in mappings}
    retired_names = {row["declaration"] for row in retired}
    protected_names = moved_names | retired_names
    contract_paths: list[pathlib.Path] = []
    for pattern in contract_globs:
        matches = sorted(ROOT.glob(pattern))
        if not matches:
            return fail(f"occurrence contract-module glob matched nothing: {pattern}")
        contract_paths.extend(matches)
    contract_paths = sorted(set(contract_paths))
    ownership_errors = contract_ownership_errors(
        ownership, contract_paths, protected_names
    )
    if ownership_errors:
        return fail(ownership_errors[0])
    statement_copies = direct_code_statement_copies(ownership, contract_paths)
    if statement_copies:
        path, name, line = statement_copies[0]
        return fail(
            "contract-local direct-code proposition copy survives for "
            f"`{name}` at {path.relative_to(ROOT)}:{line}"
        )

    contract_sources = {
        path: path.read_text(encoding="utf-8") for path in contract_paths
    }
    consumers = consumer_errors(ownership, contract_sources, required_consumers)
    if consumers:
        return fail(consumers[0])

    canonical_locations = owner_locations(
        ownership, first_party_lean_paths(), CANONICAL_DIRECT_CODE
    )
    canonical_owner = ROOT / "Blanc/CommonProofs.lean"
    if (len(canonical_locations) != 1 or
            canonical_locations[0][0] != canonical_owner or
            canonical_locations[0][1] != "theorem"):
        rendered = ", ".join(
            f"{path.relative_to(ROOT)}:{line}:{kind}"
            for path, kind, line in canonical_locations
        ) or "none"
        return fail(f"canonical direct-code sole owner drifted: {rendered}")

    try:
        actual_header = normalized_header(
            ownership, canonical_owner, CANONICAL_DIRECT_CODE_LOCAL
        )
    except (OSError, ValueError) as exc:
        return fail(f"canonical direct-code header is unreadable: {exc}")
    if actual_header != signature_pins[0]["header"]:
        return fail("canonical direct-code normalized header drifted")

    for row in mappings:
        fqn = f'Blanc.{row["declaration"]}'
        common_path = ROOT / row["commonModule"]
        common_declarations = ownership.declarations(common_path)
        if common_declarations.get(fqn, (None,))[0] != row["kind"]:
            return fail(f"common owner missing or wrong-kind `{fqn}`")
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
        positive_deleted_path = temp_root / "PositiveDeleted.lean"
        positive_deleted_path.write_text(
            source.replace(
                "private theorem CaughtFixture.control",
                "private theorem CaughtFixture.control_removed",
                1,
            ),
            encoding="utf-8",
        )
        if not missing_positive_theorems(ownership, positive_deleted_path):
            return fail("required-positive deletion control failed")

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

        lido_shadow_path = temp_root / "LidoShadow.lean"
        lido_shadow_path.write_text(
            "namespace Blanc.LidoCircuitBreaker.ProcessMessage\n"
            "theorem ok_state_eq_committedPost : True := by trivial\n"
            "end Blanc.LidoCircuitBreaker.ProcessMessage\n",
            encoding="utf-8",
        )
        lido_shadow_errors = contract_ownership_errors(
            ownership, [lido_shadow_path], protected_names
        )
        if not any("basename shadow" in error for error in lido_shadow_errors):
            return fail("Lido basename-shadow negative control failed")

        lido_alias_path = temp_root / "LidoAlias.lean"
        lido_alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.LidoCircuitBreaker\n"
            f"alias occurrenceLidoLegacy := {first_fqn}\n"
            "end Blanc.LidoCircuitBreaker\n",
            encoding="utf-8",
        )
        lido_alias_errors = contract_ownership_errors(
            ownership, [lido_alias_path], protected_names
        )
        if not any("contract alias" in error for error in lido_alias_errors):
            return fail("Lido alias negative control failed")
        compiled_lido_alias = run(["lake", "env", "lean", str(lido_alias_path)])
        if compiled_lido_alias.returncode != 0:
            return fail(
                "Lido alias negative control is not valid Lean",
                compiled_lido_alias,
            )

        canonical_shadow_path = temp_root / "CanonicalDirectCodeShadow.lean"
        canonical_shadow_path.write_text(
            "namespace Blanc.LidoCircuitBreaker.Xinst\n"
            "theorem step_spawn_codeAddress_eq_currentTarget : True := by trivial\n"
            "end Blanc.LidoCircuitBreaker.Xinst\n",
            encoding="utf-8",
        )
        canonical_shadow_errors = contract_ownership_errors(
            ownership, [canonical_shadow_path], protected_names
        )
        if not any(
            "basename shadow" in error for error in canonical_shadow_errors
        ):
            return fail("canonical direct-code basename-shadow control failed")
        command_controls.append((canonical_shadow_path, "canonical basename shadow"))

        retired_shadow_path = temp_root / "RetiredDirectCodeShadow.lean"
        retired_shadow_path.write_text(
            "namespace Blanc.LidoCircuitBreaker\n"
            "theorem xinst_spawn_direct : True := by trivial\n"
            "end Blanc.LidoCircuitBreaker\n",
            encoding="utf-8",
        )
        retired_shadow_errors = contract_ownership_errors(
            ownership, [retired_shadow_path], protected_names
        )
        if not any("basename shadow" in error for error in retired_shadow_errors):
            return fail("retired direct-code basename-shadow control failed")
        command_controls.append((retired_shadow_path, "retired basename shadow"))

        canonical_alias_path = temp_root / "CanonicalDirectCodeAlias.lean"
        canonical_alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10.Xinst\n"
            "alias step_spawn_codeAddress_eq_currentTarget :=\n"
            f"  {CANONICAL_DIRECT_CODE}\n"
            "end Blanc.Weth10.Xinst\n",
            encoding="utf-8",
        )
        canonical_alias_errors = contract_ownership_errors(
            ownership, [canonical_alias_path], protected_names
        )
        if not any("contract alias" in error for error in canonical_alias_errors):
            return fail("canonical direct-code alias control failed")
        command_controls.append((canonical_alias_path, "canonical direct-code alias"))

        retired_alias_path = temp_root / "RetiredDirectCodeAlias.lean"
        retired_alias_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10\n"
            f"alias xinst_spawn_direct := {CANONICAL_DIRECT_CODE}\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        retired_alias_errors = contract_ownership_errors(
            ownership, [retired_alias_path], protected_names
        )
        if not any("contract alias" in error for error in retired_alias_errors):
            return fail("retired direct-code alias control failed")
        command_controls.append((retired_alias_path, "retired direct-code alias"))

        canonical_export_path = temp_root / "CanonicalDirectCodeExport.lean"
        canonical_export_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.Weth10\n"
            "export Blanc.Xinst (step_spawn_codeAddress_eq_currentTarget)\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        canonical_export_errors = contract_ownership_errors(
            ownership, [canonical_export_path], protected_names
        )
        if not any("contract export" in error for error in canonical_export_errors):
            return fail("canonical direct-code export control failed")
        command_controls.append((canonical_export_path, "canonical direct-code export"))

        renamed_copy_path = temp_root / "RenamedDirectCodeCopy.lean"
        renamed_copy_path.write_text(
            "import Blanc.CommonProofs\n"
            "namespace Blanc.LidoCircuitBreaker\n"
            "open Jaune Blanc\n"
            "@[simp] theorem unrelatedSpawnInvariant\n"
            "    {sevm : Sevm} {devm : Devm} {x : Xinst}\n"
            "    {f : Frame} {rsm : Resume}\n"
            "    (hs : Xinst.step sevm devm x = .spawn f rsm)\n"
            "    (hne : sevm.currentTarget ≠ f.inner.currentTarget)\n"
            "    (hcode : devm.getCode f.inner.currentTarget ≠ .empty)\n"
            "    (hnodel : getDelegatedCodeAddress\n"
            "      (devm.getCode f.inner.currentTarget) = none) :\n"
            "    f.inner.codeAddress = some f.inner.currentTarget :=\n"
            f"  {CANONICAL_DIRECT_CODE} hs hne hcode hnodel\n"
            "end Blanc.LidoCircuitBreaker\n",
            encoding="utf-8",
        )
        renamed_copy = direct_code_statement_copies(
            ownership, [renamed_copy_path]
        )
        if (len(renamed_copy) != 1 or
                not renamed_copy[0][1].endswith(".unrelatedSpawnInvariant")):
            return fail("renamed direct-code proposition-copy control failed")
        command_controls.append((renamed_copy_path, "renamed direct-code copy"))

        duplicate_owner_path = temp_root / "DuplicateDirectCodeOwner.lean"
        duplicate_owner_path.write_text(
            "namespace Blanc\n"
            "theorem Xinst.step_spawn_codeAddress_eq_currentTarget : True := by trivial\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        duplicate_locations = owner_locations(
            ownership,
            [*first_party_lean_paths(), duplicate_owner_path],
            CANONICAL_DIRECT_CODE,
        )
        if len(duplicate_locations) != 2:
            return fail("canonical direct-code duplicate-owner control failed")

        missing_consumer_sources = dict(contract_sources)
        first_consumer = ROOT / str(required_consumers[0]["module"])
        first_consumer_source = missing_consumer_sources[first_consumer]
        changed_consumer = first_consumer_source.replace(
            CANONICAL_DIRECT_CODE_LOCAL,
            "Xinst.step_spawn_codeAddress_eq_currentTarget_removed",
            1,
        )
        if changed_consumer == first_consumer_source:
            return fail("canonical consumer-removal control could not mutate source")
        missing_consumer_sources[first_consumer] = changed_consumer
        if not consumer_errors(
            ownership, missing_consumer_sources, required_consumers
        ):
            return fail("canonical consumer-removal control failed")

        extra_consumer_path = temp_root / "UnexpectedLidoConsumer.lean"
        extra_consumer_source = (
            "import Blanc.CommonProofs\n"
            f"#check {CANONICAL_DIRECT_CODE}\n"
        )
        extra_consumer_path.write_text(extra_consumer_source, encoding="utf-8")
        extra_consumer_sources = dict(contract_sources)
        extra_consumer_sources[extra_consumer_path] = extra_consumer_source
        if not consumer_errors(
            ownership, extra_consumer_sources, required_consumers
        ):
            return fail("unexpected canonical consumer control failed")
        command_controls.append((extra_consumer_path, "unexpected consumer"))

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

        canonical_common_source = canonical_owner.read_text(encoding="utf-8")
        canonical_token = f'theorem {canonical_mapping["declaration"]}'
        canonical_missing_path = temp_root / "CanonicalCommonMissing.lean"
        canonical_missing_path.write_text(
            canonical_common_source.replace(
                canonical_token, "theorem direct_code_owner_removed", 1
            ),
            encoding="utf-8",
        )
        if CANONICAL_DIRECT_CODE in ownership.declarations(canonical_missing_path):
            return fail("canonical common-owner missing control failed")

        canonical_wrong_kind_path = temp_root / "CanonicalCommonWrongKind.lean"
        canonical_wrong_kind_path.write_text(
            canonical_common_source.replace(
                canonical_token, f'abbrev {canonical_mapping["declaration"]}', 1
            ),
            encoding="utf-8",
        )
        if ownership.declarations(canonical_wrong_kind_path).get(
            CANONICAL_DIRECT_CODE, (None,)
        )[0] != "abbrev":
            return fail("canonical common-owner wrong-kind control failed")

        header_mutant_path = temp_root / "CanonicalHeaderMutant.lean"
        header_mutant = canonical_common_source.replace(
            "(hcode : devm.getCode f.inner.currentTarget ≠ .empty)",
            "(hcode : True)",
            1,
        )
        if header_mutant == canonical_common_source:
            return fail("canonical normalized-header control could not mutate source")
        header_mutant_path.write_text(header_mutant, encoding="utf-8")
        try:
            mutated_header = normalized_header(
                ownership, header_mutant_path, CANONICAL_DIRECT_CODE_LOCAL
            )
        except (OSError, ValueError) as exc:
            return fail(f"canonical normalized-header control failed: {exc}")
        if mutated_header == signature_pins[0]["header"]:
            return fail("canonical normalized-header mutation was accepted")

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
        "OK — execution occurrence: 17 concrete occurrence + 6 direct-code controls; "
        "21 occurrence + 2 direct-code Lean mutants; WETH bridge-removal mutant; "
        "10 moved-owner + 8 exact direct-code headers + 23 ownership-parser controls; "
        "28 raw-attribution owners + exact source/chronology signatures + shared "
        "kernel + 8 controls; 27 required positive proofs + legacy deletion + 7 live direct-code "
        "deletions; 2 CREATE mutants"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
