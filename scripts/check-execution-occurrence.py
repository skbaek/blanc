#!/usr/bin/env python3
"""Fail-closed occurrence, direct-code, ownership, and mutant assurance."""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import subprocess
import sys
import tempfile
from functools import lru_cache

import lean_mutant_batch


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "ExecutionOccurrenceRegression.lean"
DIRECT_CODE_FIXTURE = ROOT / "scripts" / "ExecutionOccurrenceControls.lean"
MOVE_MANIFEST = ROOT / "scripts" / "execution-occurrence-lift-manifest.json"
RAW_ATTRIBUTION_OWNERSHIP = (
    ROOT / "scripts" / "check-execution-raw-attribution-ownership.py"
)
EXPECTED = "[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]"
DIRECT_CODE_EXPECTED = ""

CANONICAL_DIRECT_CODE = "Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget"
CANONICAL_DIRECT_CODE_LOCAL = "Xinst.step_spawn_codeAddress_eq_currentTarget"
RETIRED_DIRECT_CODE = "Blanc.Weth10.xinst_spawn_direct"
CANONICAL_OWNER_MODULE = "Blanc/CommonProofs/Messages.lean"

# UNADOPTED PROPOSAL (pending WSL protected adoption): the consumer inventory
# lists the retained direct-code consumers (scripts/release.py prunes the rows of
# a departing family here and in the manifest), and the two collision tuples
# plus six Jaune export commands below are new exact authority exceptions.
# They are double-pinned here so a manifest-only edit cannot grow them.
EXPECTED_REQUIRED_CONSUMERS = [
]
EXPECTED_LEGITIMATE_COLLISIONS = [
    {
        "module": "Blanc/CommonProofs/Messages.lean",
        "declaration": "Blanc.ProcessMessage.rollback_of_error",
        "kind": "theorem",
    },
    {
        "module": "Blanc/DelegatecallEnvelope.lean",
        "declaration": "Blanc.DelegatedChildCertificate.rollback_of_error",
        "kind": "theorem",
    },
]
EXPECTED_LEGITIMATE_EXPORT_COMMANDS = [
    {"module": "Blanc/ExecutionCellProvenance.lean",
     "command": "export Jaune.Exec (Deriv)"},
    {"module": "Blanc/ExecutionCellProvenance.lean",
     "command": "export Jaune.Exec.Deriv (ParentStep ParentPrefix)"},
    {"module": "Blanc/ExecutionOccurrence.lean",
     "command": "export Jaune.Exec (Deriv)"},
    {"module": "Blanc/ExecutionOccurrence.lean",
     "command": "export Jaune.Exec.Deriv (ParentStep ParentPrefix)"},
    {"module": "Blanc/ExecutionSettlement.lean",
     "command": "export Jaune.Frame (settlementCommits raw_commits_of_settlementCommits)"},
    {"module": "Blanc/ExecutionSettlement.lean",
     "command": "export Jaune.Exec (committedFrames descendantFrames)"},
]

DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS = {
    "Blanc.ExecutionOccurrenceControls.call_direct_codeAddress_control",
    "Blanc.ExecutionOccurrenceControls.staticcall_direct_codeAddress_control",
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
    (exact : Blanc.Exec.Frame.exactInvocation program storage codeAddress frame) :
    Blanc.Exec.Frame.exactInvocation program other codeAddress frame := by
  exact exact
""",
    "-- CODE-IDENTITY-MUTANT-CONTROL": r"""
private theorem codeIdentityWeakenedMutant
    {frame : Exec.Frame} {program : Prog} {storage codeAddress other : Adr}
    (exact : Blanc.Exec.Frame.exactInvocation program storage codeAddress frame) :
    Blanc.Exec.Frame.exactInvocation program storage other frame := by
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
    "-- CHILD-AS-PARENT-IDENTITY-MUTANT-CONTROL": r"""
private theorem childAsParentIdentityMutant
    (w : RawChildAttribution.CaughtFixture) :
    Blanc.Exec.Deriv.exactInvocation RawChildAttribution.caughtProgram
      RawChildAttribution.callTarget RawChildAttribution.callTarget w.call.root := by
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
            (.next (.reg .eq) (.last .revert)),
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

MUTANT_DIAGNOSTICS = {
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
}

# Evidence economy (scripts/GATES.md, "Evidence economy"; the batch-1 trim
# ledger is a planning record outside this repository). These three mutants are
# the only check that would notice a production change: the type of
# `SourceCursor.Chronology.initialToCursor`, the child-before-continuation
# order of `Exec.rawFrameDescendants`, and the path/source indexing of
# `Exec.Deriv.SourceCursor` are pinned by no kept positive or theorem
# statement. They stay in the main semantic row, batched into one
# elaboration. The other 17 occurrence mutants, both direct-code mutants and
# the live deletions contradict a positive the main row compiles, or depend on
# fixture-local terms only; they run in --self-test.
PRODUCTION_MUTANTS = (
    "-- CHRONOLOGY-MISSING-INITIAL-PREFIX-MUTANT-CONTROL",
    "-- CHILD-CONTINUATION-ORDER-MUTANT-CONTROL",
    "-- CHRONOLOGY-REJECTED-BRANCH-MUTANT-CONTROL",
)


def run_batch(source: str, mutants: list[lean_mutant_batch.Mutant],
              name: str) -> str | None:
    """Elaborate every mutant in one copy; None, or the failure detail."""
    text, spans = lean_mutant_batch.insert(source, mutants)
    with tempfile.TemporaryDirectory(prefix="execution-occurrence-batch-") as temp:
        path = pathlib.Path(temp) / f"{name}.lean"
        path.write_text(text, encoding="utf-8")
        result = run(["lake", "env", "lean", str(path)])
    problems = lean_mutant_batch.verdict(
        result.stdout + result.stderr, result.returncode, mutants, spans
    )
    if problems:
        return "; ".join(problems) + "\n" + result.stdout + result.stderr
    return None


def occurrence_mutants(markers) -> list[lean_mutant_batch.Mutant]:
    return [
        lean_mutant_batch.Mutant(marker, MUTANTS[marker], MUTANT_DIAGNOSTICS[marker])
        for marker in markers
    ]


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


_COMMAND_TOKEN_RE = re.compile(
    r'/-|--|\x22|(?<![A-Za-z0-9_\x27])r#+\x22|(?<![A-Za-z0-9_\x27])r\x22|\x27'
)
_BLOCK_TOKEN_RE = re.compile(r"/-|-/")
_CHAR_LITERAL_RE = re.compile("'(?:\\.|[^'\\\n])'")


_INTERPOLATED_TOKEN_RE = re.compile(
    rf"\b(?:alias|export)\b|(?<![A-Za-z0-9_'])"
    rf"{re.escape(CANONICAL_DIRECT_CODE_LOCAL)}(?![A-Za-z0-9_'])"
)


@lru_cache(maxsize=None)
def command_view(source: str) -> str:
    """Mask comments, strings and char literals, preserving offsets/lines.

    Bounded local scanner for command/reference identity only (the frozen
    signature normalization keeps its historical algorithm elsewhere). A
    single pass tracks string state, so comment markers inside strings and
    quotes inside comments cannot hide or invent a real command token.
    Raw strings and unterminated strings/block comments are refused.
    This is not an interpolation parser: a macro-prefixed or brace-bearing
    string containing alias/export/canonical-reference tokens is refused,
    rather than silently masking possible code holes. Ordinary metadata
    strings remain non-code. Frozen signature normalization is independent.
    """
    out = list(source)

    def mask(start: int, end: int) -> None:
        for index in range(start, end):
            if out[index] != "\n":
                out[index] = " "

    index = 0
    total = len(source)
    while index < total:
        match = _COMMAND_TOKEN_RE.search(source, index)
        if match is None:
            break
        token = match.group()
        start = match.start()
        if token == "--":
            end = source.find("\n", start)
            end = total if end < 0 else end
            mask(start, end)
            index = end
        elif token == "/-":
            depth = 1
            cursor = start + 2
            while depth:
                inner = _BLOCK_TOKEN_RE.search(source, cursor)
                if inner is None:
                    raise ValueError("unterminated block comment in command view")
                depth += 1 if inner.group() == "/-" else -1
                cursor = inner.end()
            mask(start, cursor)
            index = cursor
        elif token == '"':
            cursor = start + 1
            while True:
                if cursor >= total:
                    raise ValueError("unterminated string in command view")
                if source[cursor] == "\\":
                    cursor += 2
                    continue
                if source[cursor] == '"':
                    cursor += 1
                    break
                cursor += 1
            body = source[start + 1:cursor - 1]
            prefix_end = start - 1
            while prefix_end >= 0 and source[prefix_end].isspace():
                prefix_end -= 1
            macro_prefix = prefix_end >= 0 and source[prefix_end] == "!"
            if (("{" in body or "}" in body or macro_prefix)
                    and _INTERPOLATED_TOKEN_RE.search(body)):
                raise ValueError(
                    "protected token in unsupported interpolated/macro string"
                )
            mask(start, cursor)
            index = cursor
        elif token == "'":
            if start and (source[start - 1].isalnum()
                          or source[start - 1] in "_'?!"):
                index = start + 1
                continue
            char = _CHAR_LITERAL_RE.match(source, start)
            if char is not None:
                mask(start, char.end())
                index = char.end()
            else:
                index = start + 1
        else:
            raise ValueError("unsupported Lean raw string in command view")
    return "".join(out)


@lru_cache(maxsize=None)
def _written_declarations(
    ownership, path: pathlib.Path, clean: str
) -> tuple[tuple[str, str, int, str], ...]:
    """Bounded named-declaration inventory from the lexical command view.

    Ordinary strings/comments/chars cannot supply declarations. The supported
    name grammar admits Unicode word characters and internal ?/! as used by
    retained sources, with dotted/root-qualified names. Scopes retain the
    shared parser's grammar and unsupported forms refuse. Colon/open-binder
    delimiters gain one space for its parser; names it cannot represent use
    collision-free ASCII surrogates, inverted by exact FQN/kind/line below.
    Local/scoped named-instance modifiers are masked for the shared parser;
    their declared names remain in this inventory.
    Unsupported declaration/scope-looking lines refuse instead of disappearing.
    Anonymous instances have no source-written name and are explicitly omitted.
    This remains a source inventory, not elaborated Lean name resolution or a
    scanner for declarations generated by arbitrary macros/syntax quotations.
    """
    prefix = (
        r"^\s*(?:@\[[^]]+\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
        r"(?:(?:local|scoped)\s+(?=instance\s))?"
    )
    kinds = r"def|theorem|lemma|structure|abbrev|opaque|axiom|inductive|class|instance"
    name_part = r"(?:[^\W\d]|_)[\w'?!]*"
    identifier = rf"{name_part}(?:\.{name_part})*"
    declaration = re.compile(
        prefix + rf"({kinds})\s+({identifier})(?=[\s:({{\[]|$)"
    )
    declaration_start = re.compile(prefix + rf"({kinds})\b")
    anonymous_instance = re.compile(prefix + r"instance\s*(?=[:({\[])")
    scopes: list[list[str]] = []
    found: list[tuple[str, str, int, str]] = []
    normalized_lines: list[str] = []
    surrogates: dict[tuple[str, str, int], str] = {}
    for number, line in enumerate(clean.splitlines(keepends=True), 1):
        normalized = line
        if match := ownership.NAMESPACE_RE.match(line):
            scopes.append(match.group(1).split("."))
        elif ownership.SECTION_RE.match(line) or ownership.MUTUAL_RE.match(line):
            scopes.append([])
        elif ownership.END_RE.match(line):
            if not scopes:
                raise ValueError(f"{path}: line {number}: unmatched end")
            scopes.pop()
        elif match := declaration.match(line):
            kind, written = match.groups()
            namespace = [part for parts in scopes for part in parts]
            full_name = ownership.qualify(namespace, written)
            found.append((full_name, kind, number, written))
            end = match.end(2)
            delimiter = " " if end < len(line) and not line[end].isspace() else ""
            normalized_name = written
            if re.fullmatch(ownership.IDENT, written) is None:
                normalized_name = f"__occ_checked_name_{number}"
                while normalized_name in clean:
                    normalized_name += "_"
                key = (ownership.qualify(namespace, normalized_name), kind, number)
                if key in surrogates:
                    raise ValueError(f"{path}: duplicate surrogate identity")
                surrogates[key] = full_name
            normalized_prefix = re.sub(
                r"\b(?:local|scoped)(?=\s*$)",
                lambda modifier: " " * len(modifier.group()),
                line[:match.start(1)],
            ) + line[match.start(1):match.start(2)]
            normalized = (normalized_prefix + normalized_name
                          + delimiter + line[end:])
        elif anonymous_instance.match(line):
            pass  # Explicit nameless syntax, never a rightful named-owner tuple.
        elif (re.match(r"^\s*(?:set_option|open|attribute|noncomputable|local|scoped)\b", line)
              and (re.search(rf"\b(?:{kinds})\s+{identifier}(?=[\s:({{\[]|$)", line)
                   or re.search(r"\bin\s+(?:namespace|section|mutual|end)\b", line))):
            raise ValueError(
                f"{path}: line {number}: unsupported same-line command wrapper"
            )
        elif declaration_start.match(line) or re.match(
            r"^\s*(?:namespace|section|mutual|end)\b", line
        ):
            raise ValueError(
                f"{path}: line {number}: unsupported declaration/scope syntax"
            )
        normalized_lines.append(normalized)
    if scopes:
        raise ValueError(f"{path}: unclosed scope")
    # Known masking/delimiter/name normalizations only. Restore surrogate names
    # by exact parser-derived identity; no declaration is omitted or exempted.
    expected = list(ownership._tolerant_declarations(
        str(path), "".join(normalized_lines)
    ))
    seen_surrogates = set()
    restored = []
    for name, kind, line in expected:
        key = (name, kind, line)
        if key in surrogates:
            seen_surrogates.add(key)
            name = surrogates[key]
        restored.append((name, kind, line))
    if seen_surrogates != set(surrogates):
        raise ValueError(f"{path}: surrogate declaration identity/line drift")
    if [(fqn, kind, line) for fqn, kind, line, _ in found] != restored:
        raise ValueError(
            f"{path}: checked declarations disagree with normalized shared parser"
        )
    return tuple(found)


def checked_declarations(ownership, path: pathlib.Path):
    """One named-declaration authority channel, also used by the raw checker."""
    clean = command_view(path.read_text(encoding="utf-8"))
    return tuple((name, kind, line) for name, kind, line, _ in
                 _written_declarations(ownership, path, clean))


def checked_declaration_dict(ownership, path: pathlib.Path):
    found = {}
    for name, kind, line in checked_declarations(ownership, path):
        if name in found:
            raise ValueError(f"{path}: line {line}: duplicate declaration {name}")
        found[name] = (kind, line)
    return found


def _header_assignment(source: str, start: int, stop: int) -> int:
    """Find a declaration-level assignment, ignoring balanced default binders.

    The input has already had strings/comments/chars masked. A top-level type
    let is outside this bounded header grammar and explicitly refused. This
    does not attempt proposition equivalence or arbitrary Lean syntax parsing.
    """
    closing = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    stack: list[str] = []
    cursor = start
    while cursor < stop:
        char = source[cursor]
        if char in closing:
            stack.append(closing[char])
        elif char in closing.values():
            if not stack or stack.pop() != char:
                raise ValueError("unsupported unbalanced declaration header")
        elif source.startswith(":=", cursor) and not stack:
            return cursor
        elif char == "|" and not stack and not source[
            source.rfind("\n", start, cursor) + 1:cursor
        ].strip():
            # Equation-style theorem body. A preceding top-level type-let is
            # refused below; this is not a general match-expression parser.
            return cursor
        elif not stack and source.startswith("let", cursor) and (
            cursor + 3 >= stop or not (
                source[cursor + 3].isalnum() or source[cursor + 3] in "_'?!"
            )
        ) and (
            cursor == start or not (source[cursor - 1].isalnum()
                                    or source[cursor - 1] in "_'?!")
        ):
            raise ValueError("unsupported top-level let in declaration header")
        cursor += 1
    raise ValueError("declaration header has no supported top-level :=")


def direct_code_statement_copies(
    ownership, paths: list[pathlib.Path], exempt=frozenset()
) -> list[tuple[pathlib.Path, str, int]]:
    """Find parser-identified declarations copying the proposition.

    Identity is the actual parsed line, its written spelling and the FQN
    the shared parser derives from it (plain, dotted, root-qualified and
    nested-namespace forms alike). Only exact (path, FQN, kind) tuples in
    `exempt` are skipped, never a whole file.
    """
    required = (
        "Xinst.step", "= .spawn", "currentTarget ≠", ".getCode",
        "≠ .empty", ".codeAddress = some", ".inner.currentTarget",
    )
    found: list[tuple[pathlib.Path, str, int]] = []
    for path in paths:
        source = command_view(path.read_text(encoding="utf-8"))
        plain_lines = source.splitlines()
        offsets: list[int] = []
        cursor = 0
        for line in source.splitlines(keepends=True):
            offsets.append(cursor)
            cursor += len(line)
        declarations = _written_declarations(ownership, path, source)
        for declaration_index, (full_name, kind, line, written) in enumerate(declarations):
            if kind not in {"theorem", "lemma"}:
                continue
            if (path, full_name, kind) in exempt:
                continue
            match = re.match(
                rf"^\s*(?:@\[[^]]+\]\s*)*"
                rf"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
                rf"(theorem|lemma)\s+({re.escape(written)})(?=[\s:({{\[]|$)",
                plain_lines[line - 1],
            )
            if (match is None or match.group(1) != kind
                    or match.group(2) != written):
                raise ValueError(
                    f"{path}: line {line}: written spelling disagrees with "
                    f"parser identity for `{full_name}`"
                )
            declaration_start = offsets[line - 1] + match.start(1)
            stop = (offsets[declarations[declaration_index + 1][2] - 1]
                    if declaration_index + 1 < len(declarations) else len(source))
            # Necessary token prefilter for this one proposition heuristic,
            # not an unsupported-syntax exemption. All declarations already
            # passed the common checked inventory. Without these tokens even
            # the whole bounded declaration cannot match its required header.
            candidate = " ".join(source[declaration_start:stop].split())
            if not all(token in candidate for token in required):
                continue
            try:
                end = _header_assignment(
                    source, offsets[line - 1] + match.end(2), stop
                )
            except ValueError as exc:
                raise ValueError(f"{path}:{line}: `{full_name}`: {exc}") from exc
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
        for name, kind, line in checked_declarations(ownership, path):
            if name == declaration:
                found.append((path, kind, line))
    return found


def direct_code_reference_count(
    ownership, source: str, *, mask_canonical_header: bool = False
) -> int:
    """Count real canonical references in the lexical command view.

    String-only metadata mentions are masked. For the canonical owner
    file only its exact declaration header span is masked, never the
    whole file, so other code there still counts.
    """
    del ownership
    clean = command_view(source)
    if mask_canonical_header:
        token = f"theorem {CANONICAL_DIRECT_CODE_LOCAL}"
        if clean.count(token) != 1:
            raise ValueError(
                f"expected exactly one `{token}` in the canonical owner"
            )
        start = clean.index(token)
        end = clean.find(":= by", start)
        if end < 0:
            raise ValueError("canonical header has no `:= by` delimiter")
        chars = list(clean)
        for index in range(start, end + 2):
            if chars[index] != "\n":
                chars[index] = " "
        clean = "".join(chars)
    pattern = re.compile(
        rf"(?<![A-Za-z0-9_']){re.escape(CANONICAL_DIRECT_CODE_LOCAL)}"
        rf"(?![A-Za-z0-9_'])"
    )
    return len(pattern.findall(clean))


def consumer_errors(
    ownership,
    sources: dict[pathlib.Path, str],
    required_consumers: list[dict[str, object]],
    canonical_owner: pathlib.Path | None = None,
) -> list[str]:
    if canonical_owner is None:
        canonical_owner = ROOT / CANONICAL_OWNER_MODULE
    expected = {
        ROOT / str(row["module"]): int(row["references"])
        for row in required_consumers
    }
    errors: list[str] = []
    for path, source in sources.items():
        rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        try:
            got = direct_code_reference_count(
                ownership, source,
                mask_canonical_header=path == canonical_owner,
            )
        except ValueError as exc:
            errors.append(f"canonical consumer scan refused at {rel}: {exc}")
            continue
        want = expected.get(path, 0)
        if got != want:
            errors.append(
                f"canonical consumer count drifted at {rel}: found {got}, expected {want}"
            )
    missing_paths = sorted(set(expected) - set(sources))
    for path in missing_paths:
        errors.append(f"required canonical consumer is absent: {path.relative_to(ROOT)}")
    return errors


def corpus_ownership_errors(
    ownership,
    paths: list[pathlib.Path],
    protected_names: set[str],
    rightful_tuples=frozenset(),
    legitimate_collisions=frozenset(),
    legitimate_exports=frozenset(),
    *,
    require_exception_inventory: bool = False,
) -> list[str]:
    """Reject exact survivors, basename shadows, and aliases/exports.

    Every first-party file is scanned, owner files included: a protected
    declaration is permitted only at its exact (path, FQN, kind) rightful
    tuple, and a basename collision only at an exact legitimate-collision
    tuple. Alias/export tokens are read in the lexical command view; an
    export is permitted only as an exact (module, normalized command)
    tuple. With `require_exception_inventory`, every legitimate tuple
    must occur exactly once across the scanned population.
    """
    errors: list[str] = []
    forbidden_basenames = {name.rsplit(".", 1)[-1] for name in protected_names}
    collision_counts = {tuple_: 0 for tuple_ in legitimate_collisions}
    export_counts = {tuple_: 0 for tuple_ in legitimate_exports}
    for path in paths:
        rel_path = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        rel = rel_path.as_posix() if isinstance(rel_path, pathlib.Path) else str(rel_path)
        for name, kind, line in checked_declarations(ownership, path):
            identity = (path, name, kind)
            if identity in rightful_tuples:
                continue
            if identity in legitimate_collisions:
                collision_counts[identity] += 1
                continue
            if name in protected_names:
                errors.append(
                    f"corpus donor declaration survives for `{name}` as {kind} "
                    f"at {rel}:{line} (not its rightful path/FQN/kind tuple)"
                )
            elif name.rsplit(".", 1)[-1] in forbidden_basenames:
                errors.append(
                    f"corpus basename shadow survives for `{name}` as {kind} "
                    f"at {rel}:{line}"
                )
        try:
            view = command_view(path.read_text(encoding="utf-8"))
        except ValueError as exc:
            errors.append(f"corpus lexical refusal at {rel}: {exc}")
            continue
        view_lines = view.splitlines()
        for match in re.finditer(r"\b(alias|export)\b", view):
            line = view.count("\n", 0, match.start()) + 1
            normalized = " ".join(view_lines[line - 1].split())
            key = (rel, normalized)
            if match.group(1) == "export" and key in legitimate_exports:
                export_counts[key] += 1
                continue
            errors.append(
                f"corpus {match.group(1)} survives at {rel}:{line}: {normalized}"
            )
    if require_exception_inventory:
        for (path, name, kind), count in sorted(
            collision_counts.items(), key=lambda item: item[0][1]
        ):
            if count != 1:
                rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
                errors.append(
                    f"legitimate collision `{name}` as {kind} at {rel} must "
                    f"occur exactly once, found {count}"
                )
        for (module, command), count in sorted(export_counts.items()):
            if count != 1:
                errors.append(
                    f"legitimate export `{command}` at {module} must occur "
                    f"exactly once, found {count}"
                )
    return errors


def check_direct_code_fixture(ownership, *, semantic: bool,
                              self_test: bool = False) -> int | None:
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

    if semantic:
        positive = run(["lake", "env", "lean", str(DIRECT_CODE_FIXTURE)])
        if positive.returncode != 0:
            return fail("direct-code positive fixture did not compile", positive)
        if positive.stdout.strip() != DIRECT_CODE_EXPECTED or positive.stderr:
            return fail("direct-code positive fixture output drifted", positive)

    with tempfile.TemporaryDirectory(prefix="execution-direct-code-") as temp:
        temp_root = pathlib.Path(temp)
        if self_test:
            # Harness self-test: the two premise-deletion mutants (each fails
            # against a positive the main row compiles) and the seven live
            # deletions, each batched into one elaboration.
            detail = run_batch(source, [
                lean_mutant_batch.Mutant(marker, mutant_source, diagnostics,
                                         require_all=True)
                for marker, (mutant_source, diagnostics) in DIRECT_CODE_MUTANTS.items()
            ], "ExecutionDirectCodeMutants")
            if detail is not None:
                return fail("direct-code mutants: " + detail)
            changed = source
            checks = []
            for theorem in sorted(DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS):
                short = theorem.rsplit(".", 1)[-1]
                token = f"theorem {short}"
                if source.count(token) != 1:
                    return fail(
                        f"direct-code deletion cannot uniquely locate `{theorem}`"
                    )
                changed = changed.replace(token, f"theorem {short}_removed", 1)
                checks.append((theorem, short))
            base_lines = changed.count("\n") + (0 if changed.endswith("\n") else 1)
            changed = changed + ("" if changed.endswith("\n") else "\n")
            changed += "".join(f"\n#check {theorem}\n" for theorem, _ in checks)
            path = temp_root / "ExecutionDirectCodeDeleted.lean"
            path.write_text(changed, encoding="utf-8")
            result = run(["lake", "env", "lean", str(path)])
            if result.returncode == 0:
                return fail("direct-code live deletions all compiled", result)
            reported = lean_mutant_batch.errors(result.stdout + result.stderr)
            for index, (theorem, short) in enumerate(checks):
                line = base_lines + 2 + 2 * index
                if not any(at == line and short in message
                           for at, message in reported):
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


def self_test() -> int:
    """Harness self-test (evidence economy rule 3).

    Its registry inputs are the harness and the two fixtures only, so it reruns
    when a control or fixture changes, not on every Lean edit. The fixtures'
    green compile is the prerequisite main semantic row's verdict.
    """
    source = FIXTURE.read_text(encoding="utf-8")
    try:
        ownership = load_ownership_parser()
    except (OSError, RuntimeError) as exc:
        return fail(f"could not load fail-closed ownership parser: {exc}")
    error = check_direct_code_fixture(ownership, semantic=False, self_test=True)
    if error is not None:
        return error
    markers = tuple(marker for marker in MUTANTS if marker not in PRODUCTION_MUTANTS)
    detail = run_batch(source, occurrence_mutants(markers),
                       "ExecutionOccurrenceSelfTestMutants")
    if detail is not None:
        return fail("fixture mutants: " + detail)
    print(
        f"OK — execution occurrence self-test: {len(markers)} occurrence + "
        f"{len(DIRECT_CODE_MUTANTS)} direct-code fixture mutants and "
        f"{len(DIRECT_CODE_REQUIRED_POSITIVE_THEOREMS)} live direct-code deletions, "
        "each failing in its own lines"
    )
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    phase = parser.add_mutually_exclusive_group()
    phase.add_argument("--static-only", action="store_true")
    phase.add_argument("--semantic-only", action="store_true")
    phase.add_argument("--self-test", action="store_true")
    parser.add_argument("--composed-prerequisites", action="store_true")
    arguments = parser.parse_args(argv)
    if arguments.self_test:
        return self_test()
    semantic = not arguments.static_only
    source = FIXTURE.read_text(encoding="utf-8")
    for marker in MUTANTS:
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

    direct_code_error = check_direct_code_fixture(ownership, semantic=semantic)
    if direct_code_error is not None:
        return direct_code_error

    if semantic:
        positive = run(["lake", "env", "lean", str(FIXTURE)])
        if positive.returncode != 0:
            return fail("positive fixture did not compile", positive)
        if positive.stdout.strip() != EXPECTED or positive.stderr:
            return fail("positive fixture evaluator vector drifted", positive)

    if semantic:
        detail = run_batch(source, occurrence_mutants(PRODUCTION_MUTANTS),
                           "ExecutionOccurrenceMutants")
        if detail is not None:
            return fail("production mutants: " + detail)

    if arguments.semantic_only:
        if not arguments.composed_prerequisites:
            settlement = run([sys.executable, "scripts/check-execution-settlement.py"])
            if settlement.returncode != 0:
                return fail("CREATE settlement/raw-commit control failed", settlement)
            if not settlement.stdout.startswith("OK — execution settlement:"):
                return fail("CREATE settlement control verdict drifted", settlement)
        print(
            "OK — execution occurrence semantic: 16 concrete occurrence + 6 direct-code "
            f"controls; {len(PRODUCTION_MUTANTS)} production Lean mutants in one "
            "elaboration"
        )
        return 0

    try:
        manifest = json.loads(MOVE_MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return fail(f"occurrence move manifest is unreadable: {exc}")
    manifest_keys = {
        "schema", "mappings", "retiredDeclarations",
        "signaturePins", "controlSignaturePins", "requiredConsumers",
        "legitimateCollisions", "legitimateExportCommands",
    }
    if (not isinstance(manifest, dict) or
            set(manifest) != manifest_keys or manifest["schema"] != 4):
        return fail("occurrence move manifest schema drifted")
    if manifest["legitimateCollisions"] != EXPECTED_LEGITIMATE_COLLISIONS:
        return fail(
            "unadopted legitimate-collision authority exceptions drifted"
        )
    if (manifest["legitimateExportCommands"] !=
            EXPECTED_LEGITIMATE_EXPORT_COMMANDS):
        return fail(
            "unadopted legitimate-export authority exceptions drifted"
        )
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
        "commonModule": "Blanc/CommonProofs/Messages.lean",
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
    if required_consumers != EXPECTED_REQUIRED_CONSUMERS:
        return fail("canonical direct-code consumer inventory drifted")

    moved_names = {f'Blanc.{row["declaration"]}' for row in mappings}
    retired_names = {row["declaration"] for row in retired}
    protected_names = moved_names | retired_names
    corpus_paths = first_party_lean_paths()
    if not any(path.is_relative_to(ROOT / "Blanc") for path in corpus_paths):
        return fail("first-party Blanc population is empty")
    canonical_owner = ROOT / CANONICAL_OWNER_MODULE
    rightful_tuples = {
        (ROOT / row["commonModule"], f'Blanc.{row["declaration"]}', row["kind"])
        for row in mappings
    }
    collision_tuples = {
        (ROOT / row["module"], row["declaration"], row["kind"])
        for row in manifest["legitimateCollisions"]
    }
    export_tuples = {
        (row["module"], row["command"])
        for row in manifest["legitimateExportCommands"]
    }
    try:
        ownership_errors = corpus_ownership_errors(
            ownership, corpus_paths, protected_names,
            rightful_tuples, collision_tuples, export_tuples,
            require_exception_inventory=True,
        )
    except (OSError, ValueError) as exc:
        return fail(f"corpus ownership scan refused: {exc}")
    if ownership_errors:
        return fail(ownership_errors[0])
    try:
        statement_copies = direct_code_statement_copies(
            ownership, corpus_paths,
            exempt={(canonical_owner, CANONICAL_DIRECT_CODE, "theorem")},
        )
    except (OSError, ValueError) as exc:
        return fail(f"direct-code proposition-copy scan refused: {exc}")
    if statement_copies:
        path, name, line = statement_copies[0]
        return fail(
            "corpus direct-code proposition copy survives for "
            f"`{name}` at {path.relative_to(ROOT)}:{line}"
        )

    corpus_sources = {
        path: path.read_text(encoding="utf-8") for path in corpus_paths
    }
    consumers = consumer_errors(ownership, corpus_sources, required_consumers)
    if consumers:
        return fail(consumers[0])

    canonical_locations = owner_locations(
        ownership, corpus_paths, CANONICAL_DIRECT_CODE
    )
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
        locations = owner_locations(ownership, corpus_paths, fqn)
        if (len(locations) != 1 or locations[0][0] != common_path
                or locations[0][1] != row["kind"]):
            rendered = ", ".join(
                f"{p.relative_to(ROOT)}:{ln}:{k}" for p, k, ln in locations
            ) or "none"
            return fail(
                f"common owner for `{fqn}` is not unique corpus-wide "
                f"at its rightful tuple: {rendered}"
            )
        common_declarations = checked_declaration_dict(ownership, common_path)
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
            "import Blanc.CommonProofs.Messages\n"
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
            "import Blanc.CommonProofs.Messages\n"
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
            "import Blanc.CommonProofs.Messages\n"
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
            "import Blanc.CommonProofs.Messages\n"
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
            "import Blanc.CommonProofs.Messages\n"
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
            "import Blanc.CommonProofs.Messages\n"
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
            "import Blanc.CommonProofs.Messages\n"
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
        lido_shadow_errors = corpus_ownership_errors(
            ownership, [lido_shadow_path], protected_names
        )
        if not any("basename shadow" in error for error in lido_shadow_errors):
            return fail("Lido basename-shadow negative control failed")

        lido_alias_path = temp_root / "LidoAlias.lean"
        lido_alias_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
            "namespace Blanc.LidoCircuitBreaker\n"
            f"alias occurrenceLidoLegacy := {first_fqn}\n"
            "end Blanc.LidoCircuitBreaker\n",
            encoding="utf-8",
        )
        lido_alias_errors = corpus_ownership_errors(
            ownership, [lido_alias_path], protected_names
        )
        if not any("corpus alias" in error for error in lido_alias_errors):
            return fail("Lido alias negative control failed")
        if semantic:
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
        canonical_shadow_errors = corpus_ownership_errors(
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
        retired_shadow_errors = corpus_ownership_errors(
            ownership, [retired_shadow_path], protected_names
        )
        if not any("basename shadow" in error for error in retired_shadow_errors):
            return fail("retired direct-code basename-shadow control failed")
        command_controls.append((retired_shadow_path, "retired basename shadow"))

        canonical_alias_path = temp_root / "CanonicalDirectCodeAlias.lean"
        canonical_alias_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
            "namespace Blanc.Weth10.Xinst\n"
            "alias step_spawn_codeAddress_eq_currentTarget :=\n"
            f"  {CANONICAL_DIRECT_CODE}\n"
            "end Blanc.Weth10.Xinst\n",
            encoding="utf-8",
        )
        canonical_alias_errors = corpus_ownership_errors(
            ownership, [canonical_alias_path], protected_names
        )
        if not any("corpus alias" in error for error in canonical_alias_errors):
            return fail("canonical direct-code alias control failed")
        command_controls.append((canonical_alias_path, "canonical direct-code alias"))

        retired_alias_path = temp_root / "RetiredDirectCodeAlias.lean"
        retired_alias_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
            "namespace Blanc.Weth10\n"
            f"alias xinst_spawn_direct := {CANONICAL_DIRECT_CODE}\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        retired_alias_errors = corpus_ownership_errors(
            ownership, [retired_alias_path], protected_names
        )
        if not any("corpus alias" in error for error in retired_alias_errors):
            return fail("retired direct-code alias control failed")
        command_controls.append((retired_alias_path, "retired direct-code alias"))

        canonical_export_path = temp_root / "CanonicalDirectCodeExport.lean"
        canonical_export_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
            "namespace Blanc.Weth10\n"
            "export Blanc.Xinst (step_spawn_codeAddress_eq_currentTarget)\n"
            "end Blanc.Weth10\n",
            encoding="utf-8",
        )
        canonical_export_errors = corpus_ownership_errors(
            ownership, [canonical_export_path], protected_names
        )
        if not any("corpus export" in error for error in canonical_export_errors):
            return fail("canonical direct-code export control failed")
        command_controls.append((canonical_export_path, "canonical direct-code export"))

        renamed_copy_path = temp_root / "RenamedDirectCodeCopy.lean"
        renamed_copy_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
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

        prop_header = (
            "    {sevm : Sevm} {devm : Devm} {x : Xinst}\n"
            "    {f : Frame} {rsm : Resume}\n"
            "    (hs : Xinst.step sevm devm x = .spawn f rsm)\n"
            "    (hne : sevm.currentTarget ≠ f.inner.currentTarget)\n"
            "    (hcode : devm.getCode f.inner.currentTarget ≠ .empty)\n"
            "    (hnodel : getDelegatedCodeAddress\n"
            "      (devm.getCode f.inner.currentTarget) = none) :\n"
            "    f.inner.codeAddress = some f.inner.currentTarget :=\n"
            f"  {CANONICAL_DIRECT_CODE} hs hne hcode hnodel\n"
        )
        copies_forms_path = temp_root / "DirectCodeCopiesForms.lean"
        copies_forms_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
            "namespace Blanc.OccurrenceControl\n"
            "theorem plainCopy\n" + prop_header +
            "end Blanc.OccurrenceControl\n"
            "namespace Blanc\n"
            "theorem OccurrenceControl.dottedCopy\n" + prop_header +
            "end Blanc\n"
            "theorem _root_.Blanc.OccurrenceControl.rootCopy\n" + prop_header +
            "namespace Blanc\n"
            "namespace OccurrenceControl\n"
            "theorem nestedCopy\n" + prop_header +
            "end OccurrenceControl\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        try:
            forms_copies = direct_code_statement_copies(
                ownership, [copies_forms_path]
            )
        except ValueError as exc:
            return fail(f"direct-code written-form control refused: {exc}")
        expected_forms = {
            "Blanc.OccurrenceControl.plainCopy",
            "Blanc.OccurrenceControl.dottedCopy",
            "Blanc.OccurrenceControl.rootCopy",
            "Blanc.OccurrenceControl.nestedCopy",
        }
        if ({name for _, name, _ in forms_copies} != expected_forms
                or len(forms_copies) != 4):
            return fail(
                "direct-code plain/dotted/root/nested copy control failed"
            )

        canonical_module_path = temp_root / "CanonicalModuleCopy.lean"
        canonical_module_path.write_text(
            "import Blanc.CommonProofs.Messages\n"
            "namespace Blanc\n"
            f"theorem {CANONICAL_DIRECT_CODE_LOCAL}\n" + prop_header +
            "theorem Xinst.renamedCopyInsideCanonical\n" + prop_header +
            "theorem Yinst.step_spawn_codeAddress_eq_currentTarget"
            " : True := by trivial\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        canonical_exempt = {
            (canonical_module_path, CANONICAL_DIRECT_CODE, "theorem")
        }
        try:
            module_copies = direct_code_statement_copies(
                ownership, [canonical_module_path], exempt=canonical_exempt
            )
        except ValueError as exc:
            return fail(f"canonical-module copy control refused: {exc}")
        if [name for _, name, _ in module_copies] != [
            "Blanc.Xinst.renamedCopyInsideCanonical"
        ]:
            return fail(
                "rename-copy inside canonical module control failed"
            )
        module_errors = corpus_ownership_errors(
            ownership, [canonical_module_path], protected_names,
            rightful_tuples=canonical_exempt,
        )
        if not any("basename shadow" in error for error in module_errors):
            return fail(
                "protected shadow inside canonical owner file control failed"
            )

        lexical_string_path = temp_root / "LexicalStringOnly.lean"
        lexical_string_path.write_text(
            'def occurrenceStringOnly : String := '
            '"alias export Xinst.step_spawn_codeAddress_eq_currentTarget -- /-"\n'
            "-- alias export\n"
            "theorem occurrenceStringOnlyTheorem : True := by trivial\n",
            encoding="utf-8",
        )
        if corpus_ownership_errors(
            ownership, [lexical_string_path], protected_names
        ):
            return fail("string-only alias/export lexical control failed")
        if direct_code_reference_count(
            ownership, lexical_string_path.read_text(encoding="utf-8")
        ) != 0:
            return fail("string-only canonical mention lexical control failed")

        no_space_path = temp_root / "NoSpaceShadow.lean"
        no_space_path.write_text(
            "namespace Blanc.OccurrenceControl\n"
            "theorem step_spawn_codeAddress_eq_currentTarget: True := by trivial\n"
            "end Blanc.OccurrenceControl\n", encoding="utf-8",
        )
        if not any("basename shadow" in error for error in
                   corpus_ownership_errors(ownership, [no_space_path], protected_names)):
            return fail("no-whitespace declaration shadow control failed")

        unicode_shadow_path = temp_root / "UnicodeShadow.lean"
        unicode_shadow_path.write_text(
            "theorem Ω.step_spawn_codeAddress_eq_currentTarget: True := by trivial\n",
            encoding="utf-8",
        )
        if not any("basename shadow" in error for error in
                   corpus_ownership_errors(ownership, [unicode_shadow_path], protected_names)):
            return fail("Unicode-prefix protected basename control failed")
        identifier_path = temp_root / "IdentifierNormalization.lean"
        identifier_path.write_text(
            "def __occ_checked_name_2 : Nat := 0\n"
            "def σ : Nat := 0\n"
            "theorem foo?bar: True := by trivial\n",
            encoding="utf-8",
        )
        if [name for name, _, _ in checked_declarations(ownership, identifier_path)] != [
            "__occ_checked_name_2", "σ", "foo?bar"
        ] or corpus_ownership_errors(ownership, [identifier_path], {"foo"}):
            return fail("identifier surrogate collision/suffix distinction control failed")

        wrapped_shadow_path = temp_root / "WrappedShadow.lean"
        wrapped_shadow_path.write_text(
            "set_option maxRecDepth 1000 in theorem "
            "Blanc.OccurrenceControl.rollback_of_error : True := by trivial\n",
            encoding="utf-8",
        )
        try:
            checked_declarations(ownership, wrapped_shadow_path)
        except ValueError as exc:
            if "unsupported same-line command wrapper" not in str(exc):
                return fail("wrapped declaration refused at wrong control")
        else:
            return fail("same-line wrapped protected declaration was not refused")

        fake_collision_path = temp_root / "StringOnlyCollision.lean"
        fake_collision_name = "Blanc.OccurrenceControl.rollback_of_error"
        fake_collision_path.write_text(
            'def collisionMetadata : String := "\n'
            "namespace Blanc.OccurrenceControl\n"
            "theorem rollback_of_error : True := by trivial\n"
            'end Blanc.OccurrenceControl\n"\n', encoding="utf-8",
        )
        if corpus_ownership_errors(ownership, [fake_collision_path], protected_names):
            return fail("string-only declaration metadata control failed")
        fake_errors = corpus_ownership_errors(
            ownership, [fake_collision_path], protected_names,
            legitimate_collisions={
                (fake_collision_path, fake_collision_name, "theorem")
            }, require_exception_inventory=True,
        )
        if not any("exactly once, found 0" in error for error in fake_errors):
            return fail("string-only collision existence control failed")

        default_copy_path = temp_root / "DefaultBinderCopy.lean"
        default_copy_path.write_text(
            "theorem _root_.Blanc.OccurrenceControl.defaultCopy (n : Nat := 0)\n"
            + prop_header, encoding="utf-8",
        )
        if [name for _, name, _ in direct_code_statement_copies(
            ownership, [default_copy_path]
        )] != ["Blanc.OccurrenceControl.defaultCopy"]:
            return fail("default-binder proposition-copy control failed")

        for prefix in ("s!", "m!", "unknownMacro "):
            interpolated = (
                f'def interpolationProbe := {prefix}"{{(let _ := '
                f'@{CANONICAL_DIRECT_CODE}; 0)}}"\n'
            )
            try:
                direct_code_reference_count(ownership, interpolated)
            except ValueError:
                continue
            return fail("interpolated protected reference was not refused")

        lexical_alias_path = temp_root / "LexicalAliasAfterString.lean"
        lexical_alias_path.write_text(
            'def occurrenceLexicalString : String := "/- --"\n'
            '/- a quote " inside a comment -/\n'
            f"alias occurrenceLexicalLegacy := {CANONICAL_DIRECT_CODE}\n",
            encoding="utf-8",
        )
        lexical_alias_errors = corpus_ownership_errors(
            ownership, [lexical_alias_path], protected_names
        )
        if not any("corpus alias" in error for error in lexical_alias_errors):
            return fail("real alias after misleading string/comment control failed")

        lexical_export_path = temp_root / "LexicalExportWrongPath.lean"
        lexical_export_path.write_text(
            'def occurrenceLexicalExportString : String := "--"\n'
            "export Jaune.Exec (Deriv)\n",
            encoding="utf-8",
        )
        lexical_export_errors = corpus_ownership_errors(
            ownership, [lexical_export_path], protected_names
        )
        if not any("corpus export" in error for error in lexical_export_errors):
            return fail(
                "legitimate export command at a wrong path control failed"
            )

        for bad_source in (
            'def occurrenceRaw := r#"alias"#\n',
            'def occurrenceOpen := "unterminated\n',
            "/- unterminated block comment\n",
        ):
            try:
                command_view(bad_source)
            except ValueError:
                continue
            return fail("unsupported lexical form was not refused")


        duplicate_owner_path = temp_root / "DuplicateDirectCodeOwner.lean"
        duplicate_owner_path.write_text(
            "namespace Blanc\n"
            "theorem Xinst.step_spawn_codeAddress_eq_currentTarget : True := by trivial\n"
            "end Blanc\n",
            encoding="utf-8",
        )
        duplicate_locations = owner_locations(
            ownership,
            [*corpus_paths, duplicate_owner_path],
            CANONICAL_DIRECT_CODE,
        )
        if len(duplicate_locations) != 2:
            return fail("canonical direct-code duplicate-owner control failed")

        missing_consumer_sources = dict(corpus_sources)
        removal_consumers = required_consumers
        if not required_consumers:
            # No retained consumer (they left with a released family): plant one,
            # register it, and remove its reference.
            planted_path = temp_root / "PlantedRequiredConsumer.lean"
            missing_consumer_sources[planted_path] = (
                "import Blanc.CommonProofs.Messages\n"
                f"#check {CANONICAL_DIRECT_CODE}\n"
            )
            removal_consumers = [{"module": str(planted_path), "references": 1}]
            if consumer_errors(ownership, missing_consumer_sources, removal_consumers):
                return fail("planted canonical consumer control is not clean before removal")
        first_consumer = ROOT / str(removal_consumers[0]["module"])
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
            ownership, missing_consumer_sources, removal_consumers
        ):
            return fail("canonical consumer-removal control failed")

        extra_consumer_path = temp_root / "UnexpectedLidoConsumer.lean"
        extra_consumer_source = (
            "import Blanc.CommonProofs.Messages\n"
            f"#check {CANONICAL_DIRECT_CODE}\n"
        )
        extra_consumer_path.write_text(extra_consumer_source, encoding="utf-8")
        extra_consumer_sources = dict(corpus_sources)
        extra_consumer_sources[extra_consumer_path] = extra_consumer_source
        if not consumer_errors(
            ownership, extra_consumer_sources, required_consumers
        ):
            return fail("unexpected canonical consumer control failed")
        command_controls.append((extra_consumer_path, "unexpected consumer"))

        if semantic:
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

    if semantic and not arguments.composed_prerequisites:
        settlement = run([sys.executable, "scripts/check-execution-settlement.py"])
        if settlement.returncode != 0:
            return fail("CREATE settlement/raw-commit control failed", settlement)
        if not settlement.stdout.startswith("OK — execution settlement:"):
            return fail("CREATE settlement control verdict drifted", settlement)

    if arguments.static_only:
        print(
            "OK — execution occurrence static: 10 moved owners, exact headers and "
            "consumer counts; corpus-wide shadow/export/copy controls"
        )
    else:
        print(
            "OK — execution occurrence: 16 concrete occurrence + 6 direct-code controls; "
            f"{len(PRODUCTION_MUTANTS)} production Lean mutants; "
            "10 moved-owner + 8 exact direct-code headers + ownership-parser and "
            "lexical controls; "
            "28 raw-attribution owners + exact source/chronology signatures + shared "
            "kernel + 12 controls; 26 required positive proofs + legacy deletion; "
            "2 CREATE mutants"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
