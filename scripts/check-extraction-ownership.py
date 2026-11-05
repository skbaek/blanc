#!/usr/bin/env python3
"""Fail-closed ownership audit for the extracted execution layer.

Two ownership maps are audited.

The lift manifest (schema 4), execution-settlement-lift-manifest.json, records
the 14 settlement declarations first lifted out of WETH10.  Their common owner
is Jaune's `Jaune/ExecSettlement.lean` in the pinned Jaune package (Blanc
adopted Jaune's canonical execution layer).  It checks that every listed
declaration is genuinely declared by the common module with its manifest kind,
that no exact historical donor declaration survives anywhere in the nonempty
all-Blanc corpus (`Blanc/**/*.lean` and `Blanc.lean`, read with the existing
`tolerant_declarations` parser; DONOR-SURVIVOR), and that the retained shared
consumer `Blanc/ExecutionSettlement.lean` directly imports
`Jaune.ExecSettlement`.  A declaration scan does not prove absence of every
alias/export-created name, and it does not recognize propositionally
equivalent declarations under unrelated names; those remain independent
review obligations under the broad parser's existing limitations.  The
product-specific WETH10/Lido donor populations, common-owner basename-shadow
and any-alias/export bans in those files, and the 21 WETH retained-trace
compatibility abbreviations are retired with their product surfaces and are
not audited here.

The relocation manifest, jaune-exec-relocation-manifest.json, lists every
handwritten declaration of the canonical execution layer (`Exec`, its
inversions, adequacy, derivations, settlement, chronology and message
execution) that moved from Blanc to Jaune.  Each must be declared under its
`Jaune.*` name by its named module of the pinned Jaune package, and no Blanc
module may declare it again, under its old `Blanc.*` name or under the
`Jaune.*` name: a leftover or disconnected copy fails as
RELOCATED-REDEFINED, a destination that no longer declares it as
RELOCATED-MISSING.

``--negative-controls`` (the wrapper's ``--self-test``; evidence economy rule
3, so it runs when the harness changes, not on every Lean edit) runs eight
controls: seven mutations in a disposable fixture tree seeded from a clean
audit (a test-owned exact historical-donor declaration, a missing common
declaration, a common-kind mismatch, a missing direct import in the retained
shared consumer, a leftover `Blanc.Exec` copy, a disconnected `Jaune.*`-named
copy declared from Blanc, and a relocated declaration missing from its Jaune
module) plus distinct trailing-`?` declaration parsing.  Each mutation must
fail with its own diagnostic tag; afterwards the exact seed bytes are restored
(new files removed) and byte identity with the seed is asserted, without a
redundant restored audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path


MANIFEST = "scripts/execution-settlement-lift-manifest.json"
RELOCATION_MANIFEST = "scripts/jaune-exec-relocation-manifest.json"
RELOCATED_COUNT = 197
DECL_KINDS = {"def", "theorem", "structure", "abbrev", "opaque", "axiom", "inductive", "class"}
RELOCATION_KINDS = DECL_KINDS | {"lemma"}
# Lean identifiers may carry a trailing `?` or `!`; retaining that suffix is
# essential for ownership because `last` and `last?` are distinct declarations.
IDENT_PART = r"[A-Za-z_][A-Za-z0-9_']*[!?]?"
IDENT = rf"{IDENT_PART}(?:\.{IDENT_PART})*"
NAMESPACE_RE = re.compile(rf"^\s*namespace\s+({IDENT})\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(def|theorem|structure|abbrev|opaque|axiom|inductive|class)\s+({IDENT})(?=\s|$)"
)
IMPORT_RE = re.compile(rf"^\s*import\s+({IDENT})(?:\s|$)")
ALIAS_COMMAND_RE = re.compile(r"\balias\b")
EXPORT_COMMAND_RE = re.compile(r"\bexport\b")


@dataclass(frozen=True)
class Mapping:
    donor: str
    common: str
    kind: str


@dataclass(frozen=True)
class Config:
    common_module: str
    direct_module: str
    direct_import: str
    mappings: tuple[Mapping, ...]


_STRIP_NORMAL = re.compile(r'/-|--|"')
_STRIP_QUOTED = re.compile(r'"')
_STRIP_BLOCK = re.compile(r'/-|-/')
_NOT_NEWLINE = re.compile(r'[^\n]')


# Consumers (the occurrence, settlement and raw-attribution audits) call these
# thousands of times over the same few hundred contract texts; both are pure in
# their arguments, so they are memoized without bound. The scan jumps between
# the tokens that change state instead of stepping one character at a time; its
# output is identical to the character loop it replaced on all 29,656 Lean
# files of Blanc, its packages and Jaune, and on 300,000 random strings over
# the token alphabet (evidence economy, batch 2).
@lru_cache(maxsize=None)
def strip_comments(text: str) -> str:
    """Remove Lean line/nested block comments while preserving line positions.

    Inside a block comment every character but a newline becomes a space and
    the nested `/-`/`-/` delimiters themselves are dropped; the opening `/-`
    becomes two spaces; a line comment becomes spaces up to its newline; a
    `"` not preceded by a backslash toggles string state, in which comment
    tokens are text.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    block = 0
    quoted = False
    while i < n:
        if block:
            match = _STRIP_BLOCK.search(text, i)
            if match is None:
                out.append(_NOT_NEWLINE.sub(" ", text[i:]))
                break
            out.append(_NOT_NEWLINE.sub(" ", text[i:match.start()]))
            block += 1 if match.group() == "/-" else -1
            i = match.end()
            continue
        match = (_STRIP_QUOTED if quoted else _STRIP_NORMAL).search(text, i)
        if match is None:
            out.append(text[i:])
            break
        j = match.start()
        out.append(text[i:j])
        token = match.group()
        if token == '"':
            out.append('"')
            if j == 0 or text[j - 1] != "\\":
                quoted = not quoted
            i = j + 1
        elif token == "/-":
            block = 1
            out.append("  ")
            i = j + 2
        else:
            newline = text.find("\n", j)
            if newline < 0:
                newline = n
            out.append(" " * (newline - j))
            i = newline
    if block:
        raise ValueError("unterminated block comment")
    return "".join(out)


def qualify(namespace: list[str], name: str) -> str:
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    if name.startswith(("Blanc.", "Jaune.")) or name in ("Blanc", "Jaune"):
        return name
    if "_root_" in namespace:
        namespace = namespace[namespace.index("_root_") + 1:]
    return ".".join([*namespace, name]) if namespace else name


def declarations(path: Path) -> dict[str, tuple[str, int]]:
    """Return actual Lean declaration headers, qualified under namespaces."""
    return dict(_declarations(str(path), path.read_text(encoding="utf-8")))


@lru_cache(maxsize=None)
def _declarations(path: str, text: str) -> dict[str, tuple[str, int]]:
    # Keyed by the path and its current text, so an edited or temporary file
    # is always re-parsed; callers receive a copy.
    scopes: list[tuple[str, list[str]]] = []
    found: dict[str, tuple[str, int]] = {}
    for number, line in enumerate(strip_comments(text).splitlines(), 1):
        if match := NAMESPACE_RE.match(line):
            name = match.group(1)
            parts = name.split(".")
            scopes.append(("namespace", parts))
            continue
        if SECTION_RE.match(line):
            scopes.append(("section", []))
            continue
        if MUTUAL_RE.match(line):
            scopes.append(("mutual", []))
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
    """Reject every alias/export command in a donor module.

    The audited WETH donor set contains no legitimate alias or export command:
    a contract module consumes common declarations, it never re-provides them.
    Rejecting either command keyword token anywhere outside comments avoids
    unsound approximations of Lean's command wrappers, modifiers, multiline,
    root-qualified, and ancestor-relative name grammar. A future string or
    macro containing the token fails conservatively for human review.
    """
    source = strip_comments(path.read_text(encoding="utf-8"))
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
        "schema", "commonModule", "requiredDirectImport", "mappings"
    }:
        raise ValueError("manifest must contain exactly schema/commonModule/requiredDirectImport/mappings")
    if value["schema"] != 4 or not isinstance(value["commonModule"], str) or not value["commonModule"]:
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
        if not donor.startswith("Blanc.Weth10.") or not common.startswith("Jaune."):
            raise ValueError(f"manifest mapping {index} has invalid ownership prefixes")
        mappings.append(Mapping(donor, common, kind))
    if len({row.donor for row in mappings}) != len(mappings) or len({row.common for row in mappings}) != len(mappings):
        raise ValueError("manifest mappings must have unique donor and common names")
    return Config(value["commonModule"], direct["module"], direct["import"], tuple(mappings))


RELOCATION_DECL_RE = re.compile(
    rf"^\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    rf"(def|theorem|lemma|structure|abbrev|opaque|axiom|inductive|class|instance)\s+({IDENT})(?=\s|$)"
)
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")


@lru_cache(maxsize=None)
def _tolerant_declarations(path: str, text: str) -> tuple[tuple[str, str, int], ...]:
    """Every declaration header of a whole Lean file, qualified.

    Unlike `declarations`, this reads arbitrary modules: `mutual` opens a scope
    its `end` closes, an unmatched `end` is refused, and repeated names (a
    `private` helper reused across sections) are all reported.
    """
    scopes: list[list[str]] = []
    found: list[tuple[str, str, int]] = []
    for number, line in enumerate(strip_comments(text).splitlines(), 1):
        if match := NAMESPACE_RE.match(line):
            scopes.append(match.group(1).split("."))
            continue
        if SECTION_RE.match(line) or MUTUAL_RE.match(line):
            scopes.append([])
            continue
        if END_RE.match(line):
            if not scopes:
                raise ValueError(f"{path}: line {number}: unmatched end")
            scopes.pop()
            continue
        if match := RELOCATION_DECL_RE.match(line):
            kind, name = match.groups()
            namespace = [part for parts in scopes for part in parts]
            found.append((qualify(namespace, name), kind, number))
    if scopes:
        raise ValueError(f"{path}: unclosed scope")
    return tuple(found)


def tolerant_declarations(path: Path) -> tuple[tuple[str, str, int], ...]:
    return _tolerant_declarations(str(path), path.read_text(encoding="utf-8"))


@dataclass(frozen=True)
class Relocated:
    jaune: str
    blanc: str
    module: str


def read_relocation(root: Path) -> tuple[str, tuple[Relocated, ...]]:
    path = root / RELOCATION_MANIFEST
    if not path.is_file():
        raise ValueError(f"missing manifest {RELOCATION_MANIFEST}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"malformed manifest {RELOCATION_MANIFEST}: {exc.msg}") from exc
    if not isinstance(value, dict) or set(value) != {"schema", "source", "jauneRoot", "declarations"}:
        raise ValueError(f"{RELOCATION_MANIFEST} must contain exactly schema/source/jauneRoot/declarations")
    if value["schema"] != 1 or value["jauneRoot"] != ".lake/packages/jaune":
        raise ValueError(f"{RELOCATION_MANIFEST} has an unsupported schema or Jaune root")
    rows = value["declarations"]
    if not isinstance(rows, list) or len(rows) != RELOCATED_COUNT:
        raise ValueError(f"{RELOCATION_MANIFEST} must list exactly {RELOCATED_COUNT} declarations")
    out: list[Relocated] = []
    for index, row in enumerate(rows, 1):
        if not isinstance(row, dict) or not {"jaune", "blanc", "module", "kind"} <= set(row) <= {"jaune", "blanc", "module", "kind", "private"}:
            raise ValueError(f"{RELOCATION_MANIFEST} row {index} has unexpected fields")
        jaune, blanc, module, kind = row["jaune"], row["blanc"], row["module"], row["kind"]
        if (not isinstance(jaune, str) or not jaune.startswith("Jaune.") or blanc != "Blanc." + jaune[len("Jaune."):]
                or not isinstance(module, str) or not re.fullmatch(r"Jaune/[A-Za-z]+\.lean", module)
                or kind not in RELOCATION_KINDS):
            raise ValueError(f"{RELOCATION_MANIFEST} row {index} is malformed")
        out.append(Relocated(jaune, blanc, module))
    if len({row.jaune for row in out}) != len(out):
        raise ValueError(f"{RELOCATION_MANIFEST} repeats a declaration")
    return value["jauneRoot"], tuple(out)


def relocation_audit(root: Path) -> list[str]:
    """Every relocated declaration lives in Jaune and nowhere in Blanc."""
    try:
        jaune_root, rows = read_relocation(root)
        errors: list[str] = []
        by_module: dict[str, set[str]] = {}
        for row in rows:
            by_module.setdefault(row.module, set()).add(row.jaune)
        for module, wanted in sorted(by_module.items()):
            path = root / jaune_root / module
            if not path.is_file():
                errors.append(f"RELOCATED-MISSING — pinned Jaune module {jaune_root}/{module} is missing")
                continue
            declared = {name for name, _kind, _line in tolerant_declarations(path)}
            for name in sorted(wanted - declared):
                errors.append(f"RELOCATED-MISSING — {name} is not declared in {jaune_root}/{module}")
        owners = {row.blanc: row.jaune for row in rows}
        owners.update({row.jaune: row.jaune for row in rows})
        blanc_files = sorted((root / "Blanc").rglob("*.lean"))
        if (root / "Blanc.lean").is_file():
            blanc_files.append(root / "Blanc.lean")
        if not blanc_files:
            errors.append("SETUP — extraction ownership: no Blanc modules to audit for relocated copies")
        for path in blanc_files:
            rel = path.relative_to(root).as_posix()
            for name, kind, line in tolerant_declarations(path):
                if name in owners:
                    errors.append(
                        f"RELOCATED-REDEFINED — {rel}:{line}: {kind} {name} "
                        f"(owned by Jaune as {owners[name]})"
                    )
        return errors
    except (OSError, ValueError) as exc:
        return [f"SETUP — extraction ownership: {exc}"]


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
        donors = {row.donor for row in config.mappings}
        blanc_files = sorted((root / "Blanc").rglob("*.lean"))
        if (root / "Blanc.lean").is_file():
            blanc_files.append(root / "Blanc.lean")
        if not blanc_files:
            errors.append("SETUP — extraction ownership: no Blanc modules to audit for donor survivors")
        for path in blanc_files:
            rel = path.relative_to(root).as_posix()
            for name, kind, line in tolerant_declarations(path):
                if name in donors:
                    errors.append(f"DONOR-SURVIVOR — {rel}:{line}: {kind} {name}")
        direct_path = root / config.direct_module
        if not direct_path.is_file():
            errors.append(f"DIRECT-IMPORT-MISSING — required consumer module missing: {config.direct_module}")
        elif config.direct_import not in imports(direct_path):
            errors.append(f"DIRECT-IMPORT-MISSING — {config.direct_module} does not directly import {config.direct_import}")
        errors.extend(relocation_audit(root))
        return errors
    except (OSError, ValueError) as exc:
        return [f"SETUP — extraction ownership: {exc}"]


def mutate_historical_donor_survivor(root: Path) -> None:
    # Test-owned fixture file: an exact historical donor declaration in the
    # all-Blanc corpus, removed again by the restore step (new-file absence).
    path = root / "Blanc/ExtractionOwnershipControl.lean"
    if path.exists():
        raise ValueError("negative control fixture path already exists")
    path.write_text(
        "namespace Blanc.Weth10.Execution\n"
        "def commits : Prop := True\n"
        "end Blanc.Weth10.Execution\n",
        encoding="utf-8",
    )


COMMON_MODULE = ".lake/packages/jaune/Jaune/ExecSettlement.lean"


def mutate_common_missing(root: Path) -> None:
    path = root / COMMON_MODULE
    text = path.read_text(encoding="utf-8")
    old = "def Execution.commits"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "def executionSettlementControlMissing", 1), encoding="utf-8")


def mutate_common_kind_mismatch(root: Path) -> None:
    path = root / COMMON_MODULE
    text = path.read_text(encoding="utf-8")
    old = "def Execution.commits"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "theorem Execution.commits", 1), encoding="utf-8")


def mutate_relocated_leftover(root: Path) -> None:
    path = root / "Blanc/Semantics.lean"
    text = path.read_text(encoding="utf-8")
    old = "\nend Blanc"
    if not text.endswith(old + "\n") and not text.endswith(old):
        raise ValueError("negative control could not find the end of Blanc/Semantics.lean")
    cut = text.rindex(old)
    path.write_text(
        text[:cut] + "\n\ntheorem Exec.halt_inv : True := trivial\n" + text[cut:],
        encoding="utf-8",
    )


def mutate_relocated_disconnected(root: Path) -> None:
    path = root / "Blanc/CommonCore.lean"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\nnamespace Jaune\n"
            "def Exec.Deriv.Fa : Prop := True\n"
            "end Jaune\n"
        )


def mutate_relocated_missing(root: Path) -> None:
    path = root / ".lake/packages/jaune/Jaune/Exec.lean"
    text = path.read_text(encoding="utf-8")
    old = "lemma exec_iff_exec_eq"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "lemma execControlRenamed", 1), encoding="utf-8")


def mutate_direct_import_missing(root: Path) -> None:
    path = root / "Blanc/ExecutionSettlement.lean"
    text = path.read_text(encoding="utf-8")
    old = "import Jaune.ExecSettlement"
    if text.count(old) != 1:
        raise ValueError(f"negative control could not uniquely find {old}")
    path.write_text(text.replace(old, "-- removed by extraction-audit negative control", 1), encoding="utf-8")


def negative_controls(root: Path) -> list[str]:
    # Exactly eight controls: these seven mutations plus the trailing-`?`
    # parser probe below.  The common-kind tag is COMMON-KIND-MISMATCH.
    controls = [
        ("historical-donor-survivor", "DONOR-SURVIVOR", mutate_historical_donor_survivor),
        ("common-missing", "COMMON-MISSING", mutate_common_missing),
        ("common-kind-mismatch", "COMMON-KIND-MISMATCH", mutate_common_kind_mismatch),
        ("direct-import-missing", "DIRECT-IMPORT-MISSING", mutate_direct_import_missing),
        ("relocated-leftover", "RELOCATED-REDEFINED", mutate_relocated_leftover),
        ("relocated-disconnected", "RELOCATED-REDEFINED", mutate_relocated_disconnected),
        ("relocated-missing", "RELOCATED-MISSING", mutate_relocated_missing),
    ]
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="extraction-ownership-") as temp:
        parser_probe = Path(temp) / "TrailingQuestionMark.lean"
        parser_probe.write_text(
            "namespace Blanc.ParserProbe\n"
            "mutual\n"
            "def sourceSite : Nat := 0\n"
            "def sourceSite? : Nat := 1\n"
            "end\n"
            "def afterMutual : Nat := 2\n"
            "end Blanc.ParserProbe\n",
            encoding="utf-8",
        )
        try:
            parsed = declarations(parser_probe)
            expected = {
                "Blanc.ParserProbe.sourceSite",
                "Blanc.ParserProbe.sourceSite?",
                "Blanc.ParserProbe.afterMutual",
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
        # The audit reads only the two manifests, the Lean sources under
        # Blanc/ (and Blanc.lean), and the pinned Jaune package's Lean sources,
        # so the seed copies exactly those rather than the whole tree.
        copied = Path(temp) / "blanc"
        shutil.copytree(root / "Blanc", copied / "Blanc")
        shutil.copy2(root / "Blanc.lean", copied / "Blanc.lean")
        (copied / MANIFEST).parent.mkdir(parents=True)
        shutil.copy2(root / MANIFEST, copied / MANIFEST)
        shutil.copy2(root / RELOCATION_MANIFEST, copied / RELOCATION_MANIFEST)
        shutil.copytree(
            root / ".lake/packages/jaune/Jaune",
            copied / ".lake/packages/jaune/Jaune",
        )
        if audit(copied):
            failures.append("CONTROL-SETUP — the seed copy does not audit clean")

        def snapshot(tree: Path) -> dict[str, str]:
            return {
                path.relative_to(tree).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(tree.rglob("*"))
                if path.is_file()
            }

        seed_snapshot = snapshot(copied)
        case = Path(temp) / "case"
        shutil.copytree(copied, case)

        def restore_seed_bytes() -> None:
            # Restore exact seed bytes and new-file absence; identity is
            # asserted by the caller without a redundant restored audit.
            for path in sorted(case.rglob("*")):
                if path.is_file() and path.relative_to(case).as_posix() not in seed_snapshot:
                    path.unlink()
            for rel, digest in seed_snapshot.items():
                target = case / rel
                if not target.is_file() or hashlib.sha256(target.read_bytes()).hexdigest() != digest:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(copied / rel, target)

        for name, expected, mutate in controls:
            try:
                mutate(case)
            except (OSError, ValueError) as exc:
                failures.append(f"CONTROL-SETUP — {name}: {exc}")
            else:
                output = audit(case)
                if not any(line.startswith(expected) for line in output):
                    rendered = "; ".join(output) if output else "passed unexpectedly"
                    failures.append(f"CONTROL-FAILED — {name}: expected {expected}, got {rendered}")
            restore_seed_bytes()
            if snapshot(case) != seed_snapshot:
                failures.append(f"CONTROL-FAILED — {name}: restored tree is not byte-identical to the seed")
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
        print("OK — extraction ownership: 14/14 common declarations present with manifest kinds; no exact historical donor declaration in the all-Blanc corpus (alias/export-created names not audited); Blanc/ExecutionSettlement.lean directly imports Jaune.ExecSettlement; 197/197 relocated declarations owned by Jaune only; 8/8 negative controls live")
    else:
        print("OK — extraction ownership: 14/14 common declarations present with manifest kinds; no exact historical donor declaration in the all-Blanc corpus (alias/export-created names not audited); Blanc/ExecutionSettlement.lean directly imports Jaune.ExecSettlement; 197/197 relocated declarations owned by Jaune only")
    return 0


if __name__ == "__main__":
    sys.exit(main())
