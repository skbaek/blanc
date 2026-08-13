#!/usr/bin/env python3
"""Fail-closed assurance gate for the cycle-safe SSTORE-freedom foundation."""

from __future__ import annotations

import json
import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from functools import lru_cache


ROOT = pathlib.Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "CycleWriteFreeRegression.lean"
MANIFEST = ROOT / "scripts" / "cycle-write-free-owner-manifest.json"

# Filled from the compiled fixture.  This is deliberately exact: adding,
# removing, or reordering an evaluator control is an assurance change.
EXPECTED = (
    "[true, true, true, true, true, true, true, true, true, true, true, "
    "true, true, true, true, true, true, true, true, true,\n"
    "  true, true, true]"
)

REQUIRED_POSITIVE_THEOREMS = {
    "Blanc.CycleWriteFreeRegression.local_checker_controls",
    "Blanc.CycleWriteFreeRegression.function_table_index_controls",
    "Blanc.CycleWriteFreeRegression.component_checker_controls",
    "Blanc.CycleWriteFreeRegression.empty_gateway_controls",
    "Blanc.CycleWriteFreeRegression.duplicate_member_controls",
    "Blanc.CycleWriteFreeRegression.selfLoop_exact_execution",
    "Blanc.CycleWriteFreeRegression.selfLoop_cursor_control",
    "Blanc.CycleWriteFreeRegression.selfLoop_cycle_prefix_control",
    "Blanc.CycleWriteFreeRegression.selfLoop_no_sstore_control",
    "Blanc.CycleWriteFreeRegression.twoNode_exact_execution",
    "Blanc.CycleWriteFreeRegression.twoNode_cursor_control",
    "Blanc.CycleWriteFreeRegression.twoNode_cycle_prefix_control",
    "Blanc.CycleWriteFreeRegression.twoNode_no_sstore_control",
    "Blanc.CycleWriteFreeRegression.cyclic_outcome_controls",
    "Blanc.CycleWriteFreeRegression.noOp_sstore_occurs",
    "Blanc.CycleWriteFreeRegression.reverted_sstore_occurs",
    "Blanc.CycleWriteFreeRegression.terminalError_sstore_occurs",
    "Blanc.CycleWriteFreeRegression.ExternalChild.control",
    "Blanc.CycleWriteFreeRegression.ExternalChild.false_all_frame_refuted",
    "Blanc.CycleWriteFreeRegression.SameOwnerChild.control",
    "Blanc.CycleWriteFreeRegression.SameOwnerChild.storage_equality_refuted",
    "Blanc.CycleWriteFreeRegression.required_positive_controls",
}

NATIVE_FALSE = ("Tactic `native_decide` evaluated that the proposition",)
TYPE_MISMATCH = ("Application type mismatch", "Type mismatch")
RFL_FAILURE = ("Tactic `rfl` failed",)

MUTANTS = {
    "-- ENTRY-LINKAGE-MUTANT-CONTROL": (
        """private theorem entryLinkageMutant :
    callingEmptyProgram.entrySstoreFree callingEmptyProgram.main [] = true := by
  native_decide
""", NATIVE_FALSE),
    "-- MISSING-LOOKUP-MUTANT-CONTROL": (
        """private theorem missingLookupMutant :
    missingLookupProgram.entrySstoreFree missingLookupProgram.main [2] = true := by
  native_decide
""", NATIVE_FALSE),
    "-- OUT-OF-COMPONENT-MUTANT-CONTROL": (
        """private theorem outOfComponentMutant :
    outOfSetProgram.entrySstoreFree outOfSetProgram.main [0] = true := by
  native_decide
""", NATIVE_FALSE),
    "-- BODY-SUBSTITUTION-MUTANT-CONTROL": (
        """private theorem bodySubstitutionMutant
    (w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0]) :
    outsideWriterProgram.entrySstoreFree writer [] = true := by
  exact w.accepted
""", TYPE_MISMATCH),
    "-- INDEX-SUBSTITUTION-MUTANT-CONTROL": (
        """private theorem indexSubstitutionMutant
    (w : CycleFixture twoNodeProgram twoNodeCode twoNodePre [0, 1]) :
    twoNodeProgram.entrySstoreFree twoNodeProgram.main [0] = true := by
  exact w.accepted
""", TYPE_MISMATCH),
    "-- OFF-BY-ONE-LOOKUP-MUTANT-CONTROL": (
        """private theorem offByOneLookupMutant :
    twoNodeProgram.aux[1]?.isSome = true := by
  native_decide
""", NATIVE_FALSE),
    "-- PRE-CYCLE-SSTORE-MUTANT-CONTROL": (
        """private theorem preCycleSstoreMutant :
    sstoreBeforeCycleProgram.entrySstoreFree
      sstoreBeforeCycleProgram.main [0] = true := by native_decide
""", NATIVE_FALSE),
    "-- POST-CYCLE-SSTORE-MUTANT-CONTROL": (
        """private theorem postCycleSstoreMutant :
    possiblePostCycleWriterProgram.entrySstoreFree
      possiblePostCycleWriterProgram.main [0] = true := by native_decide
""", NATIVE_FALSE),
    "-- SELECTED-MEMBER-SSTORE-MUTANT-CONTROL": (
        """private theorem selectedMemberSstoreMutant :
    selectedWriterProgram.entrySstoreFree selectedWriterProgram.main [1] = true := by
  native_decide
""", NATIVE_FALSE),
    "-- RECURSIVE-WRITER-MUTANT-CONTROL": (
        """private theorem recursiveWriterMutant :
    recursiveWriterProgram.entrySstoreFree recursiveWriterProgram.main [0, 1] = true := by
  native_decide
""", NATIVE_FALSE),
    "-- UNTAKEN-BRANCH-WRITER-MUTANT-CONTROL": (
        """private theorem untakenBranchWriterMutant :
    untakenBranchWriterProgram.entrySstoreFree
      untakenBranchWriterProgram.main [1] = true := by native_decide
""", NATIVE_FALSE),
    "-- FUEL-RECURSIVE-SUBSTITUTION-MUTANT-CONTROL": (
        """private theorem fuelRecursiveSubstitutionMutant :
    fuelSstoreFree 8 selfLoopProgram selfLoopProgram.main = true := by
  native_decide
""", NATIVE_FALSE),
    "-- RAW-BYTE-SCAN-MUTANT-CONTROL": (
        """private theorem rawByteScanMutant :
    pushPayloadProgram.main.localSstoreFree = false := by native_decide
""", NATIVE_FALSE),
    "-- WRONG-SOURCE-BODY-MUTANT-CONTROL": (
        """private theorem wrongSourceBodyMutant
    (w : CycleFixture selfLoopProgram selfLoopCode selfLoopPre [0]) :
    selectedWriterProgram.entrySstoreFree
      selectedWriterProgram.main [1] = true := by
  exact w.accepted
""", TYPE_MISMATCH),
    "-- MISSING-PARENT-PREFIX-MUTANT-CONTROL": (
        """private theorem missingParentPrefixMutant :
    ¬ (∃ w : ExternalChild.Fixture,
      some ExternalChild.parentCode.toList =
        ExternalChild.parentProgram.compile ∧
      ExternalChild.parentProgram.entrySstoreFree
        ExternalChild.parentProgram.main [] = true ∧
      ∃ occurrence : Exec.NinstOccurrence w.root,
        occurrence.instruction = .reg .sstore ∧
        ¬ Exec.Deriv.ParentPrefix w.cursor.node occurrence.node) := by
  rintro ⟨w, compiled, accepted, occurrence, isStore, notOwned⟩
  have noStore :=
    occurrence.instruction_ne_sstore_of_entrySstoreFree
      w.cursor compiled [] accepted
  exact noStore isStore
""", TYPE_MISMATCH),
    "-- EXTERNAL-CHILD-ALL-FRAME-MUTANT-CONTROL": (
        """private theorem externalChildAllFrameMutant :
    ∀ w : ExternalChild.Fixture,
      ∀ occurrence : Exec.NinstOccurrence w.root,
        occurrence.instruction = .reg .sstore →
          Exec.Deriv.ParentPrefix w.root occurrence.node := by
  intro w occurrence isStore
  exact Exec.Deriv.ParentPrefix.refl _
""", TYPE_MISMATCH),
    "-- NOOP-SSTORE-PRUNE-MUTANT-CONTROL": (
        """private theorem noOpSstorePruneMutant :
    (¬ ∃ occurrence : Exec.NinstOccurrence
        (rootExec noOpSstoreSevm noOpSstorePre),
      occurrence.instruction = .reg .sstore) ∧
    Execution.commits (rootExec noOpSstoreSevm noOpSstorePre).exn = true := by
  exact noOp_sstore_occurs
""", TYPE_MISMATCH),
    "-- REVERTED-SSTORE-PRUNE-MUTANT-CONTROL": (
        """private theorem revertedSstorePruneMutant :
    (¬ ∃ occurrence : Exec.NinstOccurrence
        (rootExec revertedSstoreSevm revertedSstorePre),
      occurrence.instruction = .reg .sstore) ∧
    Execution.commits (rootExec revertedSstoreSevm revertedSstorePre).exn = false := by
  exact reverted_sstore_occurs
""", TYPE_MISMATCH),
    "-- TERMINAL-ERROR-SSTORE-PRUNE-MUTANT-CONTROL": (
        """private theorem terminalErrorSstorePruneMutant :
    (¬ ∃ occurrence : Exec.NinstOccurrence
        (rootExec terminalErrorSstoreSevm terminalErrorSstorePre),
      occurrence.instruction = .reg .sstore) ∧
    Execution.commits
      (rootExec terminalErrorSstoreSevm terminalErrorSstorePre).exn = false := by
  exact terminalError_sstore_occurs
""", TYPE_MISMATCH),
    "-- SAME-OWNER-ENDPOINT-EQUALITY-MUTANT-CONTROL": (
        """private theorem sameOwnerEndpointEqualityMutant :
    ∀ w : SameOwnerChild.Fixture,
      Execution.commits w.raw = true →
      Execution.commits w.out = true →
      (Devm.getStor SameOwnerChild.parentPre SameOwnerChild.owner).get 0 =
        (Devm.getStor w.resumed SameOwnerChild.owner).get 0 := by
  intro w childCommits parentCommits
  rfl
""", RFL_FAILURE),
}

KINDS = {
    "def", "theorem", "structure", "abbrev", "opaque", "axiom",
    "inductive", "class",
}
NAME = r"[A-Za-z_][A-Za-z0-9_']*[?!]?"
QUALIFIED = rf"{NAME}(?:\.{NAME})*"
NAMESPACE_RE = re.compile(rf"^\s*namespace\s+({QUALIFIED})\s*$")
SECTION_RE = re.compile(
    rf"^\s*(?:noncomputable\s+)?section(?:\s+{QUALIFIED})?\s*$"
)
END_RE = re.compile(rf"^\s*end(?:\s+{QUALIFIED})?\s*$")
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*"
    rf"((?:(?:private|protected|noncomputable|unsafe)\s+)*)"
    rf"({'|'.join(sorted(KINDS))})\s+({QUALIFIED})(?=\s|:|\{{|\(|$)"
)
IMPORT_RE = re.compile(rf"^\s*import\s+({QUALIFIED})(?:\s|$)")


@dataclass(frozen=True)
class Decl:
    kind: str
    line: int
    public: bool
    header: str | None


@lru_cache(maxsize=128)
def strip_comments(text: str) -> str:
    """Remove line and nested block comments while preserving offsets."""
    out: list[str] = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if not quoted and text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif not quoted and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            char = text[i]
            out.append(char)
            if char == '"' and (i == 0 or text[i - 1] != "\\"):
                quoted = not quoted
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(out)


def qualify(namespace: list[str], name: str) -> str:
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    if name == "Blanc" or name.startswith("Blanc."):
        return name
    return ".".join([*namespace, name]) if namespace else name


@lru_cache(maxsize=128)
def declarations(text: str) -> dict[str, Decl]:
    clean = strip_comments(text)
    scopes: list[tuple[str, list[str]]] = []
    found: dict[str, Decl] = {}
    offset = 0
    for number, line in enumerate(clean.splitlines(keepends=True), 1):
        bare = line.rstrip("\r\n")
        if match := NAMESPACE_RE.match(bare):
            scopes.append(("namespace", match.group(1).split(".")))
        elif SECTION_RE.match(bare):
            scopes.append(("section", []))
        elif END_RE.match(bare):
            if not scopes:
                raise ValueError(f"line {number}: unmatched end")
            scopes.pop()
        elif match := DECL_RE.match(bare):
            modifiers, kind, name = match.groups()
            namespace = [
                part
                for scope_kind, parts in scopes
                if scope_kind == "namespace"
                for part in parts
            ]
            fqn = qualify(namespace, name)
            if fqn in found:
                raise ValueError(f"line {number}: duplicate declaration {fqn}")
            keyword_at = offset + bare.index(kind, match.start())
            body_at = clean.find(":=", keyword_at)
            header = None
            if body_at >= 0:
                header = " ".join(clean[keyword_at:body_at + 2].split())
            found[fqn] = Decl(
                kind, number, "private" not in modifiers.split(), header
            )
        offset += len(line)
    if scopes:
        raise ValueError("unclosed namespace or section")
    return found


def imports(text: str) -> list[str]:
    return [
        match.group(1)
        for line in strip_comments(text).splitlines()
        if (match := IMPORT_RE.match(line))
    ]


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args, cwd=ROOT, text=True, capture_output=True, check=False
    )


def fail(message: str, result: subprocess.CompletedProcess[str] | None = None) -> int:
    print(f"ERROR — cycle write free: {message}", file=sys.stderr)
    if result is not None:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
    return 1


def read_manifest() -> dict[str, object]:
    value = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected_keys = {
        "schema", "commonModule", "rootModule", "requiredRootImport",
        "exactCommonImports", "contractModuleGlobs", "owners",
        "signaturePins", "legacyExemptions",
    }
    if not isinstance(value, dict) or set(value) != expected_keys:
        raise ValueError("manifest has the wrong top-level schema")
    if value["schema"] != 1:
        raise ValueError("manifest schema must be 1")
    for key in ("commonModule", "rootModule", "requiredRootImport"):
        if not isinstance(value[key], str) or not value[key]:
            raise ValueError(f"manifest {key} must be a nonempty string")
    if value["exactCommonImports"] != ["Blanc.ExecutionOccurrence"]:
        raise ValueError("manifest must pin the sole common import")
    if value["contractModuleGlobs"] != [
        "Blanc/Weth*.lean", "Blanc/Fmint*.lean", "Blanc/Lido*.lean"
    ]:
        raise ValueError("manifest contract globs drifted")
    owners = value["owners"]
    if not isinstance(owners, list) or len(owners) != 18:
        raise ValueError("manifest must contain exactly 18 owners")
    for index, row in enumerate(owners, 1):
        if not isinstance(row, dict) or set(row) != {"declaration", "kind"}:
            raise ValueError(f"owner row {index} has the wrong schema")
        if row["kind"] not in KINDS or not isinstance(row["declaration"], str):
            raise ValueError(f"owner row {index} is invalid")
    if len({row["declaration"] for row in owners}) != len(owners):
        raise ValueError("owner declarations must be unique")
    pins = value["signaturePins"]
    if not isinstance(pins, list) or len(pins) != 7:
        raise ValueError("manifest must contain exactly 7 signature pins")
    for index, row in enumerate(pins, 1):
        if not isinstance(row, dict) or set(row) != {"declaration", "header"}:
            raise ValueError(f"signature row {index} has the wrong schema")
        if not all(isinstance(row[key], str) and row[key] for key in row):
            raise ValueError(f"signature row {index} is invalid")
    exemptions = value["legacyExemptions"]
    exact_exemption = [{
        "declaration": "Blanc.Weth10.Func.sstoreFreeWithin",
        "kind": "def",
        "module": "Blanc/Weth10HolderFlowWriteCompleteness.lean",
        "reason": "fuel-bounded contract refinement; intentionally rejects cycles",
    }]
    if exemptions != exact_exemption:
        raise ValueError("the sole legacy exemption drifted")
    return value


def contract_paths(manifest: dict[str, object]) -> list[pathlib.Path]:
    globbed: set[pathlib.Path] = set()
    for pattern in manifest["contractModuleGlobs"]:
        globbed.update(ROOT.glob(pattern))
    if not globbed:
        raise ValueError("contract globs matched no modules")
    layering_path = ROOT / "scripts" / "check-layering.py"
    spec = importlib.util.spec_from_file_location(
        "cycle_write_free_layering", layering_path
    )
    if spec is None or spec.loader is None:
        raise ValueError("could not load the authoritative contract classification")
    layering = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(layering)
    classified = {
        ROOT / "Blanc" / f"{module}.lean"
        for modules in layering.CONTRACTS.values()
        for module in modules
    }
    if not classified or not all(path.is_file() for path in classified):
        raise ValueError("authoritative contract classification is empty or stale")
    if not globbed.issubset(classified):
        extras = ", ".join(
            path.relative_to(ROOT).as_posix()
            for path in sorted(globbed - classified)
        )
        raise ValueError(f"contract globs include non-contract modules: {extras}")
    return sorted(classified)


def audit_sources(
    manifest: dict[str, object], common: str, root: str,
    contracts: dict[pathlib.Path, str],
) -> list[str]:
    errors: list[str] = []
    try:
        actual = declarations(common)
        owner_rows = manifest["owners"]
        owner_names = {row["declaration"] for row in owner_rows}
        for row in owner_rows:
            got = actual.get(row["declaration"])
            if got is None:
                errors.append(f"OWNER-MISSING — {row['declaration']}")
            elif got.kind != row["kind"]:
                errors.append(f"OWNER-KIND — {row['declaration']}")
            elif not got.public:
                errors.append(f"OWNER-PRIVATE — {row['declaration']}")
        public = {name for name, decl in actual.items() if decl.public}
        for extra in sorted(public - owner_names):
            errors.append(f"OWNER-UNMANIFESTED — {extra}")
        for missing in sorted(owner_names - public):
            if not any(missing in error for error in errors):
                errors.append(f"OWNER-NONPUBLIC — {missing}")
        if imports(common) != manifest["exactCommonImports"]:
            errors.append("COMMON-IMPORT — exact import list drifted")
        root_imports = imports(root)
        if root_imports.count(manifest["requiredRootImport"]) != 1:
            errors.append("ROOT-IMPORT — common module is not imported exactly once")
        for pin in manifest["signaturePins"]:
            got = actual.get(pin["declaration"])
            if got is None or got.header != pin["header"]:
                errors.append(f"SIGNATURE — {pin['declaration']}")

        basenames = {name.rsplit(".", 1)[-1] for name in owner_names}
        exemption = manifest["legacyExemptions"][0]
        legacy_hits: list[tuple[pathlib.Path, str, Decl]] = []
        for path, source in contracts.items():
            rel = path.relative_to(ROOT).as_posix()
            clean = strip_comments(source)
            parsed = declarations(source)
            for name, decl in parsed.items():
                basename = name.rsplit(".", 1)[-1]
                if basename in basenames:
                    errors.append(f"CONTRACT-SHADOW — {rel}:{decl.line}: {name}")
                if basename == "sstoreFreeWithin":
                    legacy_hits.append((path, name, decl))
            if re.search(r"\b(?:alias|export)\b", clean):
                errors.append(f"CONTRACT-REEXPORT — {rel}")
        if len(legacy_hits) != 1:
            errors.append("LEGACY-EXEMPTION — expected exactly one declaration")
        else:
            path, name, decl = legacy_hits[0]
            if (
                name != exemption["declaration"]
                or decl.kind != exemption["kind"]
                or path.relative_to(ROOT).as_posix() != exemption["module"]
                or not decl.public
            ):
                errors.append("LEGACY-EXEMPTION — exact declaration drifted")
    except (OSError, ValueError) as exc:
        errors.append(f"SETUP — {exc}")
    return errors


def require_control(label: str, errors: list[str], tag: str) -> None:
    if not any(error.startswith(tag) for error in errors):
        raise ValueError(f"negative control {label} did not trigger {tag}")


def ownership_controls(
    manifest: dict[str, object], common: str, root: str,
    contracts: dict[pathlib.Path, str],
) -> int:
    controls = 0

    def checked(label: str, changed_common: str, changed_root: str,
                changed_contracts: dict[pathlib.Path, str], tag: str) -> None:
        nonlocal controls
        require_control(
            label,
            audit_sources(manifest, changed_common, changed_root, changed_contracts),
            tag,
        )
        controls += 1

    checked(
        "owner missing",
        common.replace("def Func.LocalSstoreFree", "def Func.LocalSstoreFree_removed", 1),
        root, contracts, "OWNER-MISSING",
    )
    checked(
        "owner kind",
        common.replace("def Func.LocalSstoreFree", "abbrev Func.LocalSstoreFree", 1),
        root, contracts, "OWNER-KIND",
    )
    checked(
        "owner visibility",
        common.replace("def Func.LocalSstoreFree", "private def Func.LocalSstoreFree", 1),
        root, contracts, "OWNER-PRIVATE",
    )
    checked(
        "common import",
        common.replace("import Blanc.ExecutionOccurrence", "import Blanc.Ladder", 1),
        root, contracts, "COMMON-IMPORT",
    )
    checked(
        "root import", common,
        root.replace("import Blanc.CycleWriteFree", "import Blanc.ExecutionOccurrence", 1),
        contracts, "ROOT-IMPORT",
    )

    first = next(iter(contracts))
    shadowed = dict(contracts)
    shadowed[first] += (
        "\nnamespace Blanc.Weth10\n"
        "private def Func.LocalSstoreFree : Prop := True\n"
        "end Blanc.Weth10\n"
    )
    checked("contract shadow", common, root, shadowed, "CONTRACT-SHADOW")
    for form in (
        "alias legacyCycleProof := Blanc.Prog.entrySstoreFree_sound",
        "export Blanc.Prog (entrySstoreFree_sound)",
    ):
        changed = dict(contracts)
        changed[first] += f"\nnamespace Blanc.Weth10\n{form}\nend Blanc.Weth10\n"
        checked(form.split()[0], common, root, changed, "CONTRACT-REEXPORT")

    legacy_path = ROOT / manifest["legacyExemptions"][0]["module"]
    deleted = dict(contracts)
    deleted[legacy_path] = deleted[legacy_path].replace(
        "def Func.sstoreFreeWithin", "def Func.sstoreFreeWithin_removed", 1
    )
    checked("legacy deleted", common, root, deleted, "LEGACY-EXEMPTION")
    wrong_kind = dict(contracts)
    wrong_kind[legacy_path] = wrong_kind[legacy_path].replace(
        "def Func.sstoreFreeWithin", "opaque Func.sstoreFreeWithin", 1
    )
    checked("legacy kind", common, root, wrong_kind, "LEGACY-EXEMPTION")
    duplicated = dict(contracts)
    duplicated[first] += (
        "\nnamespace Blanc.Weth10\ndef Func.sstoreFreeWithin : Nat := 0\n"
        "end Blanc.Weth10\n"
    )
    checked("legacy duplicate", common, root, duplicated, "LEGACY-EXEMPTION")

    signature_mutations = [
        ("compiled identity", "(compiled : some root.sevm.code.toList = program.compile)",
         "(compiled : True)"),
        ("accepted source", "program.entrySstoreFree source members = true",
         "program.entrySstoreFree program.main members = true"),
        ("member list",
         "theorem Prog.componentSstoreFree_iff\n    {program : Prog} {members : List Nat}",
         "theorem Prog.componentSstoreFree_iff\n    {program : Prog} {members : Array Nat}"),
        ("parent prefix", "Exec.Deriv.ParentPrefix cursor.node target",
         "True"),
        ("exact SSTORE", "Ninst.At target.sevm.code target.pc (.reg .sstore)",
         "True"),
        ("success narrowing", "(reached : Exec.Deriv.ParentPrefix cursor.node target)",
         "(success : target.out.isOk = true) (reached : Exec.Deriv.ParentPrefix cursor.node target)"),
        ("commit narrowing", "(sameFrame : Exec.Deriv.ParentPrefix root target)",
         "(commit : Execution.commits root.out = true) (sameFrame : Exec.Deriv.ParentPrefix root target)"),
        ("settlement narrowing", "(occurrence : Exec.NinstOccurrence root)",
         "(settled : occurrence.Retained) (occurrence : Exec.NinstOccurrence root)"),
        ("RunCompiled narrowing", "(cursor : Exec.Deriv.SourceCursor root program path source)",
         "(run : source.RunCompiled root.sevm.code cursor.pc) (cursor : Exec.Deriv.SourceCursor root program path source)"),
        ("acyclic narrowing",
         "(members : List Nat)\n    (accepted : program.entrySstoreFree source members = true)",
         "(members : List Nat)\n    (acyclic : members.Pairwise (fun left right => left ≠ right))\n"
         "    (accepted : program.entrySstoreFree source members = true)"),
    ]
    for label, old, new in signature_mutations:
        if common.count(old) == 0:
            raise ValueError(f"signature control {label} cannot find its token")
        checked(label, common.replace(old, new), root, contracts, "SIGNATURE")

    parsed = declarations(common)
    if "Blanc.Prog.function?" not in parsed or "Blanc.Prog.function" in parsed:
        raise ValueError("identifier parser did not preserve `Prog.function?`")
    controls += 1
    return controls


def missing_positives(source: str) -> list[str]:
    parsed = declarations(source)
    return sorted(
        name for name in REQUIRED_POSITIVE_THEOREMS
        if parsed.get(name, Decl("", 0, False, None)).kind != "theorem"
        or not parsed.get(name, Decl("", 0, False, None)).public
    )


def main() -> int:
    try:
        manifest = read_manifest()
        common_path = ROOT / manifest["commonModule"]
        root_path = ROOT / manifest["rootModule"]
        common = common_path.read_text(encoding="utf-8")
        root = root_path.read_text(encoding="utf-8")
        contracts = {
            path: path.read_text(encoding="utf-8")
            for path in contract_paths(manifest)
        }
        errors = audit_sources(manifest, common, root, contracts)
        if errors:
            return fail("ownership/signature audit failed: " + "; ".join(errors))
        owner_controls = ownership_controls(manifest, common, root, contracts)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        return fail(f"ownership/signature setup failed: {exc}")

    source = FIXTURE.read_text(encoding="utf-8")
    if EXPECTED.startswith("__PENDING") or not REQUIRED_POSITIVE_THEOREMS or not MUTANTS:
        return fail("gate implementation still has pending fixture pins")
    for marker in MUTANTS:
        if source.count(marker) != 1:
            return fail(f"fixture must contain exactly one `{marker}` marker")
    absent = missing_positives(source)
    if absent:
        return fail("required positive proofs missing/wrong-kind: " + ", ".join(absent))

    positive = run(["lake", "env", "lean", str(FIXTURE)])
    if positive.returncode != 0:
        return fail("positive fixture did not compile", positive)
    if positive.stdout.strip() != EXPECTED or positive.stderr:
        return fail("positive fixture evaluator vector drifted", positive)

    with tempfile.TemporaryDirectory(prefix="cycle-write-free-") as temp:
        temp_root = pathlib.Path(temp)
        for index, (marker, (mutant_source, diagnostics)) in enumerate(MUTANTS.items()):
            path = temp_root / f"CycleWriteFreeMutant{index}.lean"
            path.write_text(source.replace(marker, mutant_source), encoding="utf-8")
            result = run(["lake", "env", "lean", str(path)])
            evidence = result.stdout + result.stderr
            if result.returncode == 0:
                return fail(f"mutant `{marker}` unexpectedly compiled", result)
            if not any(diagnostic in evidence for diagnostic in diagnostics):
                return fail(f"mutant `{marker}` failed unexpectedly", result)

        for index, theorem in enumerate(sorted(REQUIRED_POSITIVE_THEOREMS)):
            short = theorem.rsplit(".", 1)[-1]
            token = f"theorem {short}"
            parsed = declarations(source)
            declaration = parsed.get(theorem)
            if declaration is None:
                return fail(f"positive deletion cannot find `{theorem}`")
            lines = source.splitlines(keepends=True)
            line_index = declaration.line - 1
            if lines[line_index].count(token) != 1:
                return fail(f"positive deletion cannot locate header `{theorem}`")
            lines[line_index] = lines[line_index].replace(
                token, f"theorem {short}_removed", 1
            )
            path = temp_root / f"CycleWriteFreePositiveDeleted{index}.lean"
            path.write_text("".join(lines), encoding="utf-8")
            if theorem not in missing_positives(path.read_text(encoding="utf-8")):
                return fail(f"positive deletion control failed for `{theorem}`")

    print(
        "OK — cycle write free: exact concrete evaluator; "
        f"{len(MUTANTS)} diagnostic-pinned Lean mutants; "
        f"{len(REQUIRED_POSITIVE_THEOREMS)} required positive proofs + "
        f"{len(REQUIRED_POSITIVE_THEOREMS)} deletion controls; "
        f"18 public owners + 7 exact signatures + {owner_controls} parser controls; "
        "1 exact legacy exemption"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
