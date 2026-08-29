#!/usr/bin/env python3
"""Fail-closed ownership audit for the ExecutionSettlement extraction.

The sole ownership map is execution-settlement-lift-manifest.json.  It checks
that every listed declaration is genuinely declared by the common module, that
no listed donor declaration or common-owner basename shadow survives in the
historical WETH10 donor family or the Lido family, that neither family contains
an unapproved alias/export command, and that Weth10HolderFlow imports the
common module directly.  The one exact `Blanc.ExecutionTrace` compatibility
export approved when the retained trace carrier moved is ignored; any drift or
additional alias/export still fails.  It deliberately does not try to
recognize propositionally equivalent declarations under unrelated names; that
remains an independent review obligation.

``--negative-controls`` runs ten controls: the historical donor alias, an
unexpected donor export, a Lido common-owner basename shadow, a Lido alias, a
missing common declaration, a missing direct import, and distinct trailing-`?`
declaration parsing, plus removal of the approved trace compatibility export,
removal of the WETH flow compatibility block, and right-hand-side drift in the
attribution compatibility block.  Each must fail with its own diagnostic tag,
so a green control run proves the relevant channel is live.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


MANIFEST = "scripts/execution-settlement-lift-manifest.json"
DECL_KINDS = {"def", "theorem", "structure", "abbrev", "opaque", "axiom", "inductive", "class"}
# Lean identifiers may carry a trailing `?` or `!`; retaining that suffix is
# essential for ownership because `last` and `last?` are distinct declarations.
IDENT_PART = r"[A-Za-z_][A-Za-z0-9_']*[!?]?"
IDENT = rf"{IDENT_PART}(?:\.{IDENT_PART})*"
NAMESPACE_RE = re.compile(rf"^\s*namespace\s+({IDENT})\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(def|theorem|structure|abbrev|opaque|axiom|inductive|class)\s+({IDENT})(?=\s|$)"
)
IMPORT_RE = re.compile(rf"^\s*import\s+({IDENT})(?:\s|$)")
ALIAS_COMMAND_RE = re.compile(r"\balias\b")
EXPORT_COMMAND_RE = re.compile(r"\bexport\b")
APPROVED_TRACE_COMPAT_EXPORT = """export Blanc.ExecutionTrace
  (messageCreateCollision messageCallDelegation messageCallExecutionMessage
    transactionPreludeBout transactionBlobGasFee transactionTenv
    systemTransactionMessage)"""
APPROVED_TRACE_COMPAT_ABBREVS = {
    "Blanc/Weth10HolderFlow.lean": """abbrev Blanc.ExecutionTrace.RetainedXlot.flowActions :=
  Blanc.Weth10.RetainedXlot.flowActions
abbrev Blanc.ExecutionTrace.RetainedXlot.flowObservations :=
  Blanc.Weth10.RetainedXlot.flowObservations
abbrev Blanc.ExecutionTrace.MessageCallTrace.flowActions :=
  Blanc.Weth10.MessageCallTrace.flowActions
abbrev Blanc.ExecutionTrace.MessageCallTrace.flowObservations :=
  Blanc.Weth10.MessageCallTrace.flowObservations
abbrev Blanc.ExecutionTrace.TransactionTrace.flowActions :=
  Blanc.Weth10.TransactionTrace.flowActions
abbrev Blanc.ExecutionTrace.TransactionTrace.flowObservations :=
  Blanc.Weth10.TransactionTrace.flowObservations
abbrev Blanc.ExecutionTrace.ApplyTransactionsTrace.flowActions :=
  Blanc.Weth10.ApplyTransactionsTrace.flowActions
abbrev Blanc.ExecutionTrace.ApplyTransactionsTrace.flowObservations :=
  Blanc.Weth10.ApplyTransactionsTrace.flowObservations
abbrev Blanc.ExecutionTrace.SystemMessageTrace.flowActions :=
  Blanc.Weth10.SystemMessageTrace.flowActions
abbrev Blanc.ExecutionTrace.SystemMessageTrace.flowObservations :=
  Blanc.Weth10.SystemMessageTrace.flowObservations
abbrev Blanc.ExecutionTrace.RequestsTrace.flowActions :=
  Blanc.Weth10.RequestsTrace.flowActions
abbrev Blanc.ExecutionTrace.RequestsTrace.flowObservations :=
  Blanc.Weth10.RequestsTrace.flowObservations
abbrev Blanc.ExecutionTrace.AppliedBodyTrace.flowActions :=
  Blanc.Weth10.AppliedBodyTrace.flowActions
abbrev Blanc.ExecutionTrace.AppliedBodyTrace.flowObservations :=
  Blanc.Weth10.AppliedBodyTrace.flowObservations""",
    "Blanc/Weth10Attribution.lean": """abbrev Blanc.ExecutionTrace.RetainedXlot.attributionStream :=
  Blanc.Weth10.RetainedXlot.attributionStream
abbrev Blanc.ExecutionTrace.MessageCallTrace.attributionStream :=
  Blanc.Weth10.MessageCallTrace.attributionStream
abbrev Blanc.ExecutionTrace.TransactionTrace.attributionStream :=
  Blanc.Weth10.TransactionTrace.attributionStream
abbrev Blanc.ExecutionTrace.ApplyTransactionsTrace.attributionStream :=
  Blanc.Weth10.ApplyTransactionsTrace.attributionStream
abbrev Blanc.ExecutionTrace.SystemMessageTrace.attributionStream :=
  Blanc.Weth10.SystemMessageTrace.attributionStream
abbrev Blanc.ExecutionTrace.RequestsTrace.attributionStream :=
  Blanc.Weth10.RequestsTrace.attributionStream
abbrev Blanc.ExecutionTrace.AppliedBodyTrace.attributionStream :=
  Blanc.Weth10.AppliedBodyTrace.attributionStream""",
}
APPROVED_TRACE_COMPAT_DECLS = {
    (path, line.split()[1])
    for path, block in APPROVED_TRACE_COMPAT_ABBREVS.items()
    for line in block.splitlines()
    if line.startswith("abbrev ")
}


@dataclass(frozen=True)
class Mapping:
    donor: str
    common: str
    kind: str


@dataclass(frozen=True)
class Config:
    common_module: str
    contract_globs: tuple[str, ...]
    direct_module: str
    direct_import: str
    mappings: tuple[Mapping, ...]


def strip_comments(text: str) -> str:
    """Remove Lean line/nested block comments while preserving line positions."""
    out: list[str] = []
    i = 0
    block = 0
    quoted = False
    while i < len(text):
        if block:
            if text.startswith("/-", i):
                block += 1
                i += 2
            elif text.startswith("-/", i):
                block -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                else:
                    out.append(" ")
                i += 1
            continue
        if not quoted and text.startswith("/-", i):
            block = 1
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
    if block:
        raise ValueError("unterminated block comment")
    return "".join(out)


def qualify(namespace: list[str], name: str) -> str:
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    if name.startswith("Blanc.") or name == "Blanc":
        return name
    if "_root_" in namespace:
        namespace = namespace[namespace.index("_root_") + 1:]
    return ".".join([*namespace, name]) if namespace else name


def declarations(path: Path) -> dict[str, tuple[str, int]]:
    """Return actual Lean declaration headers, qualified under namespaces."""
    scopes: list[tuple[str, list[str]]] = []
    found: dict[str, tuple[str, int]] = {}
    for number, line in enumerate(strip_comments(path.read_text(encoding="utf-8")).splitlines(), 1):
        if match := NAMESPACE_RE.match(line):
            name = match.group(1)
            parts = name.split(".")
            scopes.append(("namespace", parts))
            continue
        if SECTION_RE.match(line):
            scopes.append(("section", []))
            continue
        if END_RE.match(line):
            if not scopes:
                raise ValueError(f"{path}: line {number}: unmatched end")
            scopes.pop()
            continue
        if match := DECL_RE.match(line):
            kind, name = match.groups()
            namespace = [part for scope_kind, parts in scopes if scope_kind == "namespace" for part in parts]
            fqn = qualify(namespace, name)
            if fqn in found:
                raise ValueError(f"{path}: line {number}: duplicate declaration {fqn}")
            found[fqn] = (kind, number)
    if scopes:
        raise ValueError(f"{path}: unclosed scope")
    return found


def imports(path: Path) -> set[str]:
    return {
        match.group(1)
        for line in strip_comments(path.read_text(encoding="utf-8")).splitlines()
        if (match := IMPORT_RE.match(line))
    }


def donor_aliases_or_exports(path: Path, donors: set[str]) -> list[tuple[str, int, str]]:
    """Reject every unapproved alias/export command in a donor module.

    Apart from the exact trace export below, the audited WETH donor set
    contains no legitimate alias or export command. Rejecting either command
    keyword token anywhere outside comments avoids
    unsound approximations of Lean's command wrappers, modifiers, multiline,
    root-qualified, and ancestor-relative name grammar. A future string or
    macro containing the token fails conservatively for human review.  The
    exact retained-trace compatibility export is the sole reviewed exception;
    whitespace or name drift makes it visible again and therefore fail closed.
    """
    source = strip_comments(path.read_text(encoding="utf-8"))
    if path.name == "Weth10HolderFlow.lean":
        count = source.count(APPROVED_TRACE_COMPAT_EXPORT)
        if count == 1:
            erased = "".join(
                "\n" if char == "\n" else " "
                for char in APPROVED_TRACE_COMPAT_EXPORT
            )
            source = source.replace(APPROVED_TRACE_COMPAT_EXPORT, erased, 1)
    hits: list[tuple[str, int, str]] = []
    for form, pattern in (("alias", ALIAS_COMMAND_RE), ("export", EXPORT_COMMAND_RE)):
        for match in pattern.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            hits.extend((donor, line, form) for donor in sorted(donors))
    return hits


def read_config(root: Path) -> Config:
    path = root / MANIFEST
    if not path.is_file():
        raise ValueError(f"missing manifest {MANIFEST}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"malformed manifest {MANIFEST}: {exc.msg}") from exc
    if not isinstance(value, dict) or set(value) != {
        "schema", "commonModule", "contractModuleGlobs", "requiredDirectImport", "mappings"
    }:
        raise ValueError("manifest must contain exactly schema/commonModule/contractModuleGlobs/requiredDirectImport/mappings")
    if value["schema"] != 2 or not isinstance(value["commonModule"], str) or not value["commonModule"]:
        raise ValueError("manifest has unsupported schema or invalid module paths")
    contract_globs = value["contractModuleGlobs"]
    if (not isinstance(contract_globs, list) or
            contract_globs != ["Blanc/Weth10*.lean", "Blanc/Lido*.lean"]):
        raise ValueError("manifest must pin the WETH10 and Lido contract module globs")
    direct = value["requiredDirectImport"]
    if not isinstance(direct, dict) or set(direct) != {"module", "import"} or not all(isinstance(direct[k], str) and direct[k] for k in direct):
        raise ValueError("manifest requiredDirectImport must contain exactly nonempty module/import")
    rows = value["mappings"]
    if not isinstance(rows, list) or len(rows) != 14:
        raise ValueError("manifest must contain exactly 14 mappings")
    mappings: list[Mapping] = []
    for index, row in enumerate(rows, 1):
        if not isinstance(row, dict) or set(row) != {"donor", "common", "kind"}:
            raise ValueError(f"manifest mapping {index} must contain exactly donor/common/kind")
        donor, common, kind = row["donor"], row["common"], row["kind"]
        if not all(isinstance(x, str) and x for x in (donor, common, kind)) or kind not in DECL_KINDS:
            raise ValueError(f"manifest mapping {index} has invalid donor/common/kind")
        if not donor.startswith("Blanc.Weth10.") or not common.startswith("Blanc.") or common.startswith("Blanc.Weth10."):
            raise ValueError(f"manifest mapping {index} has invalid ownership prefixes")
        mappings.append(Mapping(donor, common, kind))
    if len({row.donor for row in mappings}) != len(mappings) or len({row.common for row in mappings}) != len(mappings):
        raise ValueError("manifest mappings must have unique donor and common names")
    return Config(value["commonModule"], tuple(contract_globs), direct["module"], direct["import"], tuple(mappings))


def audit(root: Path) -> list[str]:
    try:
        config = read_config(root)
        common_path = root / config.common_module
        if not common_path.is_file():
            return [f"SETUP — extraction ownership: common module missing: {config.common_module}"]
        actual = declarations(common_path)
        errors: list[str] = []
        for row in config.mappings:
            got = actual.get(row.common)
            if got is None:
                errors.append(f"COMMON-MISSING — {row.common} is not declared in {config.common_module}")
            elif got[0] != row.kind:
                errors.append(f"COMMON-KIND-MISMATCH — {row.common} is {got[0]}, manifest requires {row.kind}")
        donor_files: list[Path] = []
        for pattern in config.contract_globs:
            matches = sorted(root.glob(pattern))
            if not matches:
                errors.append(
                    f"SETUP — extraction ownership: no contract modules match {pattern}"
                )
            donor_files.extend(matches)
        donor_files = sorted(set(donor_files))
        donors = {row.donor for row in config.mappings}
        common_basenames = {row.common.rsplit(".", 1)[-1] for row in config.mappings}
        seen_trace_compat: set[tuple[str, str]] = set()
        for path in donor_files:
            rel = path.relative_to(root).as_posix()
            for name, (kind, line) in declarations(path).items():
                if name.startswith("Blanc.ExecutionTrace."):
                    compat = (rel, name)
                    seen_trace_compat.add(compat)
                    if compat not in APPROVED_TRACE_COMPAT_DECLS or kind != "abbrev":
                        errors.append(
                            f"TRACE-COMPAT-ABBREV — {rel}:{line}: "
                            f"unapproved {kind} {name}"
                        )
                elif name in donors:
                    errors.append(f"DONOR-SURVIVOR — {rel}:{line}: {kind} {name}")
                elif name.rsplit(".", 1)[-1] in common_basenames:
                    errors.append(f"CONTRACT-SHADOW — {rel}:{line}: {kind} {name}")
            for name, line, form in donor_aliases_or_exports(path, donors):
                tag = "CONTRACT-ALIAS" if rel.startswith("Blanc/Lido") else "DONOR-SURVIVOR"
                errors.append(f"{tag} — {rel}:{line}: {form} {name}")
        for rel, block in APPROVED_TRACE_COMPAT_ABBREVS.items():
            path = root / rel
            source = path.read_text(encoding="utf-8") if path.is_file() else ""
            if source.count(block) != 1:
                errors.append(
                    f"TRACE-COMPAT-ABBREV — {rel} must contain its exact "
                    "approved Blanc.ExecutionTrace compatibility block"
                )
        for rel, name in sorted(APPROVED_TRACE_COMPAT_DECLS - seen_trace_compat):
            errors.append(
                f"TRACE-COMPAT-ABBREV — {rel}: missing approved abbrev {name}"
            )
        direct_path = root / config.direct_module
        if not direct_path.is_file():
            errors.append(f"DIRECT-IMPORT-MISSING — required consumer module missing: {config.direct_module}")
        elif config.direct_import not in imports(direct_path):
            errors.append(f"DIRECT-IMPORT-MISSING — {config.direct_module} does not directly import {config.direct_import}")
        elif (
            strip_comments(direct_path.read_text(encoding="utf-8")).count(
                APPROVED_TRACE_COMPAT_EXPORT
            )
            != 1
        ):
            errors.append(
                "TRACE-COMPAT-EXPORT — Blanc/Weth10HolderFlow.lean must "
                "contain the exact approved Blanc.ExecutionTrace export"
            )
        return errors
    except (OSError, ValueError) as exc:
        return [f"SETUP — extraction ownership: {exc}"]


def mutate_donor_alias(root: Path) -> None:
    path = root / "Blanc/Weth10HolderFlow.lean"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\nnamespace Blanc.Weth10.Execution\n"
            "alias commits := Blanc.Execution.commits\n"
            "end Blanc.Weth10.Execution\n"
        )


def mutate_donor_export(root: Path) -> None:
    path = root / "Blanc/Weth10HolderFlow.lean"
    with path.open("a", encoding="utf-8") as handle:
        handle.write("\nexport Blanc.Execution (commits)\n")


def mutate_trace_compat_export_missing(root: Path) -> None:
    path = root / "Blanc/Weth10HolderFlow.lean"
    text = path.read_text(encoding="utf-8")
    if text.count(APPROVED_TRACE_COMPAT_EXPORT) != 1:
        raise ValueError("negative control could not uniquely find approved trace export")
    path.write_text(
        text.replace(
            APPROVED_TRACE_COMPAT_EXPORT,
            "-- removed trace compatibility export",
            1,
        ),
        encoding="utf-8",
    )


def mutate_trace_compat_flow_missing(root: Path) -> None:
    rel = "Blanc/Weth10HolderFlow.lean"
    path = root / rel
    block = APPROVED_TRACE_COMPAT_ABBREVS[rel]
    text = path.read_text(encoding="utf-8")
    if text.count(block) != 1:
        raise ValueError("negative control could not uniquely find flow compatibility block")
    path.write_text(text.replace(block, "-- removed flow compatibility block", 1), encoding="utf-8")


def mutate_trace_compat_attribution_drift(root: Path) -> None:
    rel = "Blanc/Weth10Attribution.lean"
    path = root / rel
    block = APPROVED_TRACE_COMPAT_ABBREVS[rel]
    text = path.read_text(encoding="utf-8")
    if text.count(block) != 1:
        raise ValueError(
            "negative control could not uniquely find attribution compatibility block"
        )
    drifted = block.replace(
        "Blanc.Weth10.RetainedXlot.attributionStream",
        "Blanc.Weth10.MessageCallTrace.attributionStream",
        1,
    )
    path.write_text(text.replace(block, drifted, 1), encoding="utf-8")


def mutate_common_missing(root: Path) -> None:
    path = root / "Blanc/ExecutionSettlement.lean"
    text = path.read_text(encoding="utf-8")
    old = "def Execution.commits"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "def executionSettlementControlMissing", 1), encoding="utf-8")


def mutate_lido_shadow(root: Path) -> None:
    path = root / "Blanc/LidoCircuitBreakerCore.lean"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\nnamespace Blanc.LidoCircuitBreaker.Exec\n"
            "def committedFrames := Blanc.Exec.committedFrames\n"
            "end Blanc.LidoCircuitBreaker.Exec\n"
        )


def mutate_lido_alias(root: Path) -> None:
    path = root / "Blanc/LidoCircuitBreakerCore.lean"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\nnamespace Blanc.LidoCircuitBreaker\n"
            "alias lidoSettlementLegacy := Blanc.Execution.commits\n"
            "end Blanc.LidoCircuitBreaker\n"
        )


def mutate_direct_import_missing(root: Path) -> None:
    path = root / "Blanc/Weth10HolderFlow.lean"
    text = path.read_text(encoding="utf-8")
    old = "import Blanc.ExecutionSettlement"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "-- removed by extraction-audit negative control", 1), encoding="utf-8")


def negative_controls(root: Path) -> list[str]:
    controls = [
        ("donor-alias", "DONOR-SURVIVOR", mutate_donor_alias),
        ("donor-export", "DONOR-SURVIVOR", mutate_donor_export),
        ("trace-export-missing", "TRACE-COMPAT-EXPORT",
         mutate_trace_compat_export_missing),
        ("trace-flow-compat-missing", "TRACE-COMPAT-ABBREV",
         mutate_trace_compat_flow_missing),
        ("trace-attribution-compat-drift", "TRACE-COMPAT-ABBREV",
         mutate_trace_compat_attribution_drift),
        ("lido-shadow", "CONTRACT-SHADOW", mutate_lido_shadow),
        ("lido-alias", "CONTRACT-ALIAS", mutate_lido_alias),
        ("common-missing", "COMMON-MISSING", mutate_common_missing),
        ("direct-import-missing", "DIRECT-IMPORT-MISSING", mutate_direct_import_missing),
    ]
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="extraction-ownership-") as temp:
        parser_probe = Path(temp) / "TrailingQuestionMark.lean"
        parser_probe.write_text(
            "namespace Blanc.ParserProbe\n"
            "def sourceSite : Nat := 0\n"
            "def sourceSite? : Nat := 1\n"
            "end Blanc.ParserProbe\n",
            encoding="utf-8",
        )
        try:
            parsed = declarations(parser_probe)
            expected = {
                "Blanc.ParserProbe.sourceSite",
                "Blanc.ParserProbe.sourceSite?",
            }
            if set(parsed) != expected:
                failures.append(
                    "CONTROL-FAILED — trailing-question-mark-parser: "
                    f"expected {sorted(expected)}, got {sorted(parsed)}"
                )
        except (OSError, ValueError) as exc:
            failures.append(
                f"CONTROL-FAILED — trailing-question-mark-parser: {exc}"
            )
        copied = Path(temp) / "blanc"
        shutil.copytree(root, copied, ignore=shutil.ignore_patterns(".git", ".lake", "build"))
        for name, expected, mutate in controls:
            case = Path(temp) / name
            shutil.copytree(copied, case)
            try:
                mutate(case)
            except (OSError, ValueError) as exc:
                failures.append(f"CONTROL-SETUP — {name}: {exc}")
                continue
            output = audit(case)
            if not any(line.startswith(expected) for line in output):
                rendered = "; ".join(output) if output else "passed unexpectedly"
                failures.append(f"CONTROL-FAILED — {name}: expected {expected}, got {rendered}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    errors = audit(root)
    if errors:
        for error in errors:
            print(error)
        print(f"REGRESSION — extraction ownership: {len(errors)} violation(s)")
        return 1
    if args.negative_controls:
        controls = negative_controls(root)
        if controls:
            for control in controls:
                print(control)
            print(f"REGRESSION — extraction ownership: {len(controls)} negative control(s) failed")
            return 1
        print("OK — extraction ownership: 14/14 common declarations present; WETH10/Lido settlement shadows and unapproved aliases/exports absent; approved trace compatibility export and 21 abbreviations exact; direct import present; 10/10 negative controls live")
    else:
        print("OK — extraction ownership: 14/14 common declarations present; WETH10/Lido settlement shadows and unapproved aliases/exports absent; approved trace compatibility export and 21 abbreviations exact; direct import present")
    return 0


if __name__ == "__main__":
    sys.exit(main())
