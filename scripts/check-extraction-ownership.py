#!/usr/bin/env python3
"""Fail-closed ownership audit for the ExecutionSettlement extraction.

The sole ownership map is execution-settlement-lift-manifest.json.  It checks
that every listed declaration is genuinely declared by the common module, that
no listed donor declaration, alias, or export survives in any WETH10 module,
and that Weth10HolderFlow imports the common module directly.  It deliberately
does not try to recognize renamed or propositionally equivalent shadows; that
is the independent review obligation recorded by the migration goal.

``--negative-controls`` runs three in-memory-copy controls: donor alias,
missing common declaration, and missing direct import.  Each must fail with its
own diagnostic tag, so a green control run proves the relevant channel is live.
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
IDENT = r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
NAMESPACE_RE = re.compile(rf"^\s*namespace\s+({IDENT})\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(def|theorem|structure|abbrev|opaque|axiom|inductive|class)\s+({IDENT})\b"
)
IMPORT_RE = re.compile(rf"^\s*import\s+({IDENT})(?:\s|$)")
EXPORT_RE = re.compile(rf"^\s*export\s+{IDENT}\s*\(([^)]*)\)")
ALIAS_RE = re.compile(r"^\s*alias\s+(.+)$")


@dataclass(frozen=True)
class Mapping:
    donor: str
    common: str
    kind: str


@dataclass(frozen=True)
class Config:
    common_module: str
    weth10_glob: str
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
    if name.startswith("Blanc.") or name == "Blanc":
        return name
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
    """Recognize declared aliases/exports under the current namespace.

    This is deliberately restricted to declaration syntax.  Ordinary use of a
    WETH10-only extension such as ``Exec.Frame.AuthenticContext`` is not an
    ownership regression for the extracted ``Exec.Frame`` structure.
    """
    scopes: list[tuple[str, list[str]]] = []
    hits: list[tuple[str, int, str]] = []
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
        namespace = [part for kind, parts in scopes if kind == "namespace" for part in parts]
        if match := EXPORT_RE.match(line):
            for item in re.findall(IDENT, match.group(1)):
                fqn = qualify(namespace, item)
                if fqn in donors:
                    hits.append((fqn, number, "export"))
        if match := ALIAS_RE.match(line):
            # Lean's alias forms name the newly introduced declaration after
            # either `=>` or `↔`; check every such target on this line.
            for target in re.findall(rf"(?:=>|↔)\s*({IDENT})", match.group(1)):
                fqn = qualify(namespace, target)
                if fqn in donors:
                    hits.append((fqn, number, "alias"))
    if scopes:
        raise ValueError(f"{path}: unclosed scope")
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
        "schema", "commonModule", "weth10ModuleGlob", "requiredDirectImport", "mappings"
    }:
        raise ValueError("manifest must contain exactly schema/commonModule/weth10ModuleGlob/requiredDirectImport/mappings")
    if value["schema"] != 1 or not all(isinstance(value[key], str) and value[key] for key in ("commonModule", "weth10ModuleGlob")):
        raise ValueError("manifest has unsupported schema or invalid module paths")
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
    return Config(value["commonModule"], value["weth10ModuleGlob"], direct["module"], direct["import"], tuple(mappings))


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
        donor_files = sorted(root.glob(config.weth10_glob))
        if not donor_files:
            errors.append(f"SETUP — extraction ownership: no donor modules match {config.weth10_glob}")
        donors = {row.donor for row in config.mappings}
        for path in donor_files:
            rel = path.relative_to(root).as_posix()
            for name, (kind, line) in declarations(path).items():
                if name in donors:
                    errors.append(f"DONOR-SURVIVOR — {rel}:{line}: {kind} {name}")
            for name, line, form in donor_aliases_or_exports(path, donors):
                errors.append(f"DONOR-SURVIVOR — {rel}:{line}: {form} {name}")
        direct_path = root / config.direct_module
        if not direct_path.is_file():
            errors.append(f"DIRECT-IMPORT-MISSING — required consumer module missing: {config.direct_module}")
        elif config.direct_import not in imports(direct_path):
            errors.append(f"DIRECT-IMPORT-MISSING — {config.direct_module} does not directly import {config.direct_import}")
        return errors
    except (OSError, ValueError) as exc:
        return [f"SETUP — extraction ownership: {exc}"]


def mutate_donor_alias(root: Path) -> None:
    path = root / "Blanc/Weth10HolderFlow.lean"
    with path.open("a", encoding="utf-8") as handle:
        handle.write("\nnamespace Blanc.Weth10.Execution\nalias Blanc.Execution.commits => commits\nend Blanc.Weth10.Execution\n")


def mutate_common_missing(root: Path) -> None:
    path = root / "Blanc/ExecutionSettlement.lean"
    text = path.read_text(encoding="utf-8")
    old = "def Execution.commits"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "def executionSettlementControlMissing", 1), encoding="utf-8")


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
        ("common-missing", "COMMON-MISSING", mutate_common_missing),
        ("direct-import-missing", "DIRECT-IMPORT-MISSING", mutate_direct_import_missing),
    ]
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="extraction-ownership-") as temp:
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
        print("OK — extraction ownership: 14/14 common declarations present; no donor survivor; direct import present; 3/3 negative controls live")
    else:
        print("OK — extraction ownership: 14/14 common declarations present; no donor survivor; direct import present")
    return 0


if __name__ == "__main__":
    sys.exit(main())
