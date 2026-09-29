"""The one driver for Blanc's from-scratch axiom audit.

There is no list of audited theorems. One walk audits the whole library: the audit source
(``scripts/AxiomCheck.lean``) imports every Blanc module and runs Jaune's
``#union_axioms_of_modules Blanc`` (``scripts/AxiomAudit.lean`` of the pinned Jaune revision, a root
of Jaune's ``Assurance`` library, namespace ``Jaune.AxiomAudit``), which follows every constant of
every imported module named ``Blanc`` or ``Blanc.…`` through ``Environment.find?`` alone, with one
shared visited set, and fails elaboration if the union contains an axiom outside ``propext``,
``Classical.choice`` and ``Quot.sound``, if the population is empty, or if a reached constant is
absent from the environment. Read that file's header for why Lean's own ``#print axioms`` /
``collectAxioms`` report is not used (https://github.com/leanprover/lean4/issues/15226). Blanc keeps
no copy of the walker: this driver checks the pinned walker's source under
``.lake/packages/jaune`` before every elaboration.

What is left of the per-theorem audit is exactly the *stricter claims*: a register or a gate that
states a smaller-than-standard axiom set for a declaration (four frozen Lido deployment names, the
Registry and access-inventory rows of ``LIDO_CIRCUIT_BREAKER_ASSURANCE.md``). Each is an explicit
``#expect_axioms NAME [ax, …]`` row in the audit source, checked in both directions by the same
walker. Every other axiom set is not stated anywhere and is not checked more tightly than the union.

* :func:`audit_source` validates the committed audit source and returns its claims.
* :func:`stricter_claims` reads those claims for the gates that cite them.
* :func:`declared_names` is the lexical resolver register gates use to require that a cited
  declaration still exists, fully qualified.
* :func:`unreachable_modules` names Blanc source files the audit source does not import: the union
  population is what is imported, so an unimported module would be silently unaudited.
* :func:`elaborate` runs ``lake env lean --stdin`` on a source; no temporary file is written.
* :func:`parse_report` reads the reports back, fail closed.

Fail-closed rules enforced here, so no gate has to remember them:

* The pinned walker source must begin with exactly ``import Lean``, import nothing else, define
  ``#full_axioms``, ``#expect_axioms`` and ``#union_axioms_of_modules`` in namespace
  ``Jaune.AxiomAudit``, and its code (comments aside) may not name Lean's precomputed collector or
  its per-module table.
* The committed audit source, once ``--`` and nested ``/- -/`` comments are removed, may contain
  nothing but blank lines, a leading block of ``import M`` lines (which must include ``AxiomAudit``
  and the three Blanc roots), exactly one ``#union_axioms_of_modules Blanc`` (no allowed-axiom
  override) and ``#expect_axioms NAME [..]`` rows, each name at most once. ``#print axioms``, the
  report markers, ``#eval``, a new ``elab`` or anything else is refused before Lean runs.
* Every ``Blanc/**/*.lean`` module must be reachable from the audit source's imports.
* :func:`parse_report` requires exactly one ``UNION-AXIOMS`` report, over a positive number of roots
  and modules, and exactly one ``AXIOM OK`` report per claim and none for any other name.

These rules tie each verdict to the walker. They are not a sandbox for arbitrary Lean.

Command line (used by ``scripts/check.sh``)::

    python3 scripts/axiom_audit.py run scripts/AxiomCheck.lean
    python3 scripts/axiom_audit.py claims scripts/AxiomCheck.lean

``run`` validates the walker and the file, elaborates the file from the repository root, checks the
reports and prints the walk's own line plus one summary line, exiting 0 only on a green verdict.
``claims`` validates the file and prints its stricter claims, one ``NAME|ax,ax`` line each.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Set, Tuple


# The walker is Jaune's: the `AxiomAudit` module of the pinned Jaune package.
WALKER_MODULE = "AxiomAudit"
WALKER_NAMESPACE = "Jaune.AxiomAudit"
WALKER_RELATIVE = ".lake/packages/jaune/scripts/AxiomAudit.lean"
COMMAND_UNION = "#union_axioms_of_modules"
COMMAND_EXPECT = "#expect_axioms"
COMMAND_FULL = "#full_axioms"
UNION_ROOT = "Blanc"
# The three Blanc roots the population is imported through. `Blanc.lean` does not reach the
# proof-recipe authoring leaf or its generated registry, which are certified like every module.
REQUIRED_IMPORTS = ("Blanc", "Blanc.ProofRecipeTactic", "Blanc.ProofRecipesGenerated", WALKER_MODULE)
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# A declaration or module name as the audit accepts it: a plain dotted identifier.
NAME = r"[A-Za-z_][A-Za-z0-9_.?']*"
NAME_ONLY = re.compile(NAME + r"\Z")
UNION_ROW = re.compile(re.escape(COMMAND_UNION) + r"[ \t]+(" + NAME + r")[ \t]*\Z")
EXPECT_ROW = re.compile(
    re.escape(COMMAND_EXPECT) + r"[ \t]+(" + NAME + r")[ \t]*\[([^\]\n]*)\][ \t]*\Z")
AUDIT_IMPORT = re.compile(r"import[ \t]+(" + NAME + r")[ \t]*\Z")
PRINT_AXIOMS = re.compile(r"^[ \t]*#print[ \t]+axioms\b", re.M)
UNION_REPORT = re.compile(
    r"^UNION-AXIOMS '([^']+)': \[([^\]\n]*)\] roots=(\d+) modules=(\d+) visited=(\d+)$", re.M)
EXPECT_REPORT = re.compile(r"^AXIOM OK (\S+): \[([^\]\n]*)\]$", re.M)
IMPORT = re.compile(r"^import[ \t]+\S")
# Identifiers the walker's code must not use: Lean's precomputed collector and the per-module
# table it reads.
FORBIDDEN_WALKER_CODE = re.compile(
    r"collectAxioms|CollectAxioms|exportedAxioms|#print\s+axioms"
)


class AuditError(Exception):
    """The audit could not be assembled or read; never a pass."""


def strip_lean_comments(text: str, label: str = WALKER_RELATIVE) -> str:
    """Remove `--` line comments and nested `/- -/` block comments.

    String literals are kept verbatim (a comment opener inside one is not a comment). Used to police
    code (the walker's, an audit source's), so it errs toward keeping text: anything it keeps is
    checked.
    """

    out: List[str] = []
    i, depth, n = 0, 0, len(text)
    in_string = False
    while i < n:
        two = text[i:i + 2]
        ch = text[i]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        else:
            if ch == '"':
                in_string = True
            out.append(ch)
            i += 1
    if depth or in_string:
        raise AuditError(f"{label}: unterminated comment or string")
    return "".join(out)


def check_walker(root: Path) -> None:
    """Refuse unless the pinned Jaune walker source still satisfies the rules."""

    path = Path(root) / WALKER_RELATIVE
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise AuditError(f"cannot read the pinned axiom walker {WALKER_RELATIVE}: {exc}")
    lines = text.splitlines()
    if not lines or lines[0].strip() != "import Lean":
        raise AuditError(f"{WALKER_RELATIVE} must begin with exactly `import Lean`")
    if any(IMPORT.match(line) for line in lines[1:]):
        raise AuditError(f"{WALKER_RELATIVE} may import nothing but Lean")
    code = strip_lean_comments(text)
    found = FORBIDDEN_WALKER_CODE.search(code)
    if found:
        raise AuditError(
            f"{WALKER_RELATIVE} code names {found.group(0)!r}; the audit must not "
            "take its answer from Lean's precomputed axiom report (lean4#15226)"
        )
    for command in (COMMAND_FULL, COMMAND_EXPECT):
        if f'elab "{command} "' not in code:
            raise AuditError(f"{WALKER_RELATIVE} no longer defines {command}")
    if f'"{COMMAND_UNION} "' not in code:
        raise AuditError(f"{WALKER_RELATIVE} no longer defines {COMMAND_UNION}")
    if f"namespace {WALKER_NAMESPACE}" not in code:
        raise AuditError(f"{WALKER_RELATIVE} no longer declares namespace {WALKER_NAMESPACE}")


def audit_source(source: str, label: str) -> Tuple[List[str], Dict[str, FrozenSet[str]]]:
    """Validate a committed audit source; return its imports and its stricter claims.

    After comments are removed only blank lines, a leading `import` block, exactly one
    `#union_axioms_of_modules Blanc` and `#expect_axioms NAME [..]` rows may remain, and every
    occurrence of either command in the raw text must be one of those live rows.
    """

    found = PRINT_AXIOMS.search(source)
    if found:
        line = source.count("\n", 0, found.start()) + 1
        raise AuditError(
            f"{label}:{line}: `#print axioms` is not an audit verdict source (lean4#15226)")
    code = strip_lean_comments(source, label)
    for marker in ("FULL-AXIOMS", "UNION-AXIOMS", "AXIOM OK"):
        if marker in source:
            raise AuditError(f"{label}: may not contain the report marker `{marker}`")
    if FORBIDDEN_WALKER_CODE.search(code):
        raise AuditError(
            f"{label}: code names Lean's precomputed collector; an audit may not take its answer "
            "from it (lean4#15226)")
    imports: List[str] = []
    unions: List[str] = []
    claims: Dict[str, FrozenSet[str]] = {}
    live_expect = 0
    for number, raw in enumerate(code.splitlines(), start=1):
        line = raw.strip()
        if not line:
            continue
        imp = AUDIT_IMPORT.match(line)
        if imp:
            if unions or claims:
                raise AuditError(f"{label}:{number}: import after the first audit command")
            imports.append(imp.group(1))
            continue
        uni = UNION_ROW.match(line)
        if uni:
            unions.append(uni.group(1))
            continue
        exp = EXPECT_ROW.match(line)
        if exp:
            name = exp.group(1)
            if name in claims:
                raise AuditError(f"{label}:{number}: duplicate stricter claim for {name}")
            axioms = frozenset(a.strip() for a in exp.group(2).split(",") if a.strip())
            for a in axioms:
                if not NAME_ONLY.match(a):
                    raise AuditError(f"{label}:{number}: not an axiom name: {a!r}")
            if axioms == STANDARD_AXIOMS:
                raise AuditError(
                    f"{label}:{number}: {name} is claimed to use exactly the standard axioms; "
                    "that is what the union walk already checks, so it is not a stricter claim")
            claims[name] = axioms
            live_expect += 1
            continue
        raise AuditError(
            f"{label}:{number}: an audit source may hold only imports, one "
            f"`{COMMAND_UNION} {UNION_ROOT}` and `{COMMAND_EXPECT} NAME [..]` rows; "
            f"found {line[:60]!r}")
    if unions != [UNION_ROOT] or source.count(COMMAND_UNION) != 1:
        raise AuditError(
            f"{label}: expected exactly one live `{COMMAND_UNION} {UNION_ROOT}` (no allowed-axiom "
            f"override, none in a comment); found {unions} and {source.count(COMMAND_UNION)} "
            "mentions")
    if source.count(COMMAND_EXPECT) != live_expect:
        raise AuditError(
            f"{label}: `{COMMAND_EXPECT}` appears {source.count(COMMAND_EXPECT)} times but only "
            f"{live_expect} are live rows; a row inside a comment is refused")
    if COMMAND_FULL in source:
        raise AuditError(f"{label}: `{COMMAND_FULL}` rows are gone; state a stricter claim with "
                         f"`{COMMAND_EXPECT}` or rely on the union walk")
    missing = [m for m in REQUIRED_IMPORTS if m not in imports]
    if missing:
        raise AuditError(f"{label}: an audit source must import {', '.join(missing)}")
    if len(set(imports)) != len(imports):
        raise AuditError(f"{label}: duplicate imports")
    return imports, claims


def stricter_claims(root: Path, relative: str = "scripts/AxiomCheck.lean"
                    ) -> Dict[str, FrozenSet[str]]:
    """The stricter claims of the committed audit source: ``{name: exact axiom set}``."""

    try:
        text = (Path(root) / relative).read_text(encoding="utf-8")
    except OSError as exc:
        raise AuditError(f"cannot read {relative}: {exc}")
    return audit_source(text, relative)[1]


# --------------------------------------------------------------------------------------------
# The population: every Blanc module must be imported by the audit source
# --------------------------------------------------------------------------------------------

def blanc_modules(root: Path) -> Dict[str, Path]:
    """``{module name: path}`` for `Blanc.lean` and every `Blanc/**/*.lean`."""

    root = Path(root)
    found: Dict[str, Path] = {}
    for path in sorted((root / "Blanc").rglob("*.lean")) + [root / "Blanc.lean"]:
        found[".".join(path.relative_to(root).with_suffix("").parts)] = path
    return found


def unreachable_modules(root: Path, imports: Iterable[str]) -> List[str]:
    """Blanc modules that no import of the audit source reaches (they would be unaudited)."""

    modules = blanc_modules(root)
    seen: Set[str] = set()
    stack = [m for m in imports if m in modules]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        code = strip_lean_comments(modules[module].read_text(encoding="utf-8"), module)
        for line in code.splitlines():
            imp = AUDIT_IMPORT.match(line.strip())
            if imp and imp.group(1) in modules:
                stack.append(imp.group(1))
    return sorted(set(modules) - seen)


# --------------------------------------------------------------------------------------------
# Lexical resolution of a cited declaration
# --------------------------------------------------------------------------------------------

_DECL_HEAD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom|instance)\s+"
    r"(?P<name>[^\s({\[:⟨]+)")
_DECL_BARE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom)\s*$")
_NS_OPEN = re.compile(r"^namespace\s+(\S+)")
_NS_SECTION = re.compile(r"^section(?:\s+\S+)?\s*$")
_NS_END = re.compile(r"^end(?:\s+(\S+))?\s*$")


def declared_names(root: Path, extra_files: Iterable[str] = ()) -> Dict[str, Tuple[str, bool]]:
    """``{fully qualified name: (kind, private)}`` for declarations written in Blanc's sources.

    A lexical scan with a namespace stack over comment-stripped text, not Lean's elaborator: it
    recognises the declaration shapes this repository writes (`namespace`/`section`/`end`, dotted
    declaration names, `_root_`, `private`, `protected`) and nothing else. It is deliberately the
    strict side of resolution -- a name it cannot place is reported as not declared -- and it is
    used by the register gates only to require that a cited name still exists, spelled in full.
    """

    root = Path(root)
    names: Dict[str, Tuple[str, bool]] = {}
    paths = sorted((root / "Blanc").rglob("*.lean")) + [root / "Blanc.lean"]
    paths += [root / extra for extra in extra_files]
    for path in paths:
        try:
            code = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
        except OSError as exc:
            raise AuditError(f"cannot read {path}: {exc}")
        stack: List[Tuple[str, str]] = []  # (kind, namespace text or "")
        pending = None
        for line in code.split("\n"):
            text = line.strip()
            if not text:
                continue
            m = _NS_OPEN.match(text)
            if m:
                stack.append(("namespace", m.group(1)))
                continue
            if _NS_SECTION.match(text) and not line[:1].isspace():
                stack.append(("section", ""))
                continue
            m = _NS_END.match(text)
            if m and not line[:1].isspace():
                if stack:
                    stack.pop()
                continue
            if pending is not None:
                kind, mods = pending
                pending = None
                first = re.match(r"[^\s({\[:⟨]+", text)
                if first is not None:
                    name = first.group(0)
                    if name.startswith("_root_."):
                        full = name[len("_root_."):]
                    else:
                        prefix = ".".join(ns for k, ns in stack if k == "namespace")
                        full = f"{prefix}.{name}" if prefix else name
                    names[full] = (kind, "private" in mods.split())
                continue
            if line[:1].isspace():
                continue
            head = _DECL_HEAD.match(text)
            if head is None:
                bare = _DECL_BARE.match(text)
                if bare is not None:  # the name is on the next line
                    pending = (bare.group("kind"), bare.group("mods"))
                continue
            name = head.group("name")
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                prefix = ".".join(ns for kind, ns in stack if kind == "namespace")
                full = f"{prefix}.{name}" if prefix else name
            names[full] = (head.group("kind"), "private" in head.group("mods").split())
    return names


# --------------------------------------------------------------------------------------------
# Elaboration and the verdict
# --------------------------------------------------------------------------------------------

def elaborate(root: Path, source: str) -> Tuple[int, str]:
    """Run `lake env lean --stdin` on `source` from `root`; merged output."""

    try:
        completed = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            cwd=str(root), input=source, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
    except OSError as exc:
        raise AuditError(f"could not run `lake env lean --stdin`: {exc}")
    return completed.returncode, completed.stdout or ""


def parse_report(output: str, claims: Dict[str, FrozenSet[str]]) -> Tuple[str, Dict[str, int]]:
    """The walk's own line and its counts, after checking every report.

    Exactly one `UNION-AXIOMS` report for `Blanc`, over positive numbers of roots, modules and
    visited constants, whose axiom list is within the standard set; and exactly one `AXIOM OK`
    report per stricter claim, equal to the claimed set, and none for any other name.
    """

    unions = UNION_REPORT.findall(output)
    if len(unions) != 1:
        raise AuditError(f"{len(unions)} UNION-AXIOMS reports in the Lean output, expected 1")
    label, axioms_text, roots, modules, visited = unions[0]
    if label != UNION_ROOT:
        raise AuditError(f"the union walk reports on {label!r}, not {UNION_ROOT!r}")
    counts = {"roots": int(roots), "modules": int(modules), "visited": int(visited)}
    if min(counts.values()) <= 0:
        raise AuditError(f"the union walk has an empty population: {counts}")
    axioms = frozenset(a.strip() for a in axioms_text.split(",") if a.strip())
    if not axioms <= STANDARD_AXIOMS:
        raise AuditError(f"the union walk reports non-standard axioms: {sorted(axioms)}")
    reports: Dict[str, List[FrozenSet[str]]] = {}
    for name, listed in EXPECT_REPORT.findall(output):
        reports.setdefault(name, []).append(
            frozenset(a.strip() for a in listed.split(",") if a.strip()))
    problems = []
    for name, claimed in claims.items():
        got = reports.get(name, [])
        if len(got) != 1:
            problems.append(f"{name}: {len(got)} claim reports, expected 1")
        elif got[0] != claimed:
            problems.append(f"{name}: reported {sorted(got[0])}, claimed {sorted(claimed)}")
    unexpected = sorted(set(reports) - set(claims))
    if unexpected:
        problems.append("reports for names that were not claimed: " + ", ".join(unexpected))
    if problems:
        raise AuditError("; ".join(problems))
    counts["claims"] = len(claims)
    return UNION_REPORT.search(output).group(0), counts  # type: ignore[union-attr]


def run(root: Path, relative: str) -> int:
    """Validate, elaborate and judge the audit source; print the verdict lines."""

    text = (Path(root) / relative).read_text(encoding="utf-8")
    imports, claims = audit_source(text, relative)
    check_walker(root)
    stray = unreachable_modules(root, imports)
    if stray:
        raise AuditError(
            f"{len(stray)} Blanc module(s) are not imported by {relative}, so the union walk would "
            f"not audit them: {', '.join(stray[:8])}")
    status, output = elaborate(root, text if text.endswith("\n") else text + "\n")
    if status != 0:
        sys.stdout.write(output)
        raise AuditError(f"`lake env lean` exited {status}: the union walk or a stricter claim "
                         "failed (the locating report is above)")
    line, counts = parse_report(output, claims)
    print(line)
    print(f"AXIOM-AUDIT roots={counts['roots']} modules={counts['modules']} "
          f"visited={counts['visited']} claims={counts['claims']}")
    return 0


# --------------------------------------------------------------------------------------------
# Controls of the driver's own validation (pure Python, run by scripts/check.sh before Lean)
# --------------------------------------------------------------------------------------------

_GOOD_SOURCE = """import Blanc
import Blanc.ProofRecipeTactic
import Blanc.ProofRecipesGenerated
import AxiomAudit

#union_axioms_of_modules Blanc

-- a comment
#expect_axioms Blanc.A.b [propext, Quot.sound]
#expect_axioms Blanc.A.c []
"""

_GOOD_OUTPUT = (
    "UNION-AXIOMS 'Blanc': [Classical.choice, Quot.sound, propext] roots=9 modules=3 visited=40\n"
    "AXIOM OK Blanc.A.b: [Quot.sound, propext]\n"
    "AXIOM OK Blanc.A.c: []\n"
)


def self_test() -> Tuple[List[str], int]:
    """The failures of the driver's controls (empty when every control bites and the good case holds) and
    the number of controls run.

    Each control is a one-line change to the good audit source or the good Lean output, and must
    be refused with the intended reason: the audit's validation is what ties a green verdict to
    the union walk over the whole population, so it must itself be shown to refuse.
    """

    failures: List[str] = []
    controls = 0

    def refused_source(label: str, source: str, needle: str) -> None:
        nonlocal controls
        controls += 1
        try:
            audit_source(source, "AxiomCheck.lean")
        except AuditError as exc:
            if needle not in str(exc):
                failures.append(f"{label}: refused for the wrong reason: {exc}")
        else:
            failures.append(f"{label}: the audit source was accepted")

    def refused_output(label: str, output: str, needle: str) -> None:
        nonlocal controls
        controls += 1
        try:
            parse_report(output, _GOOD_CLAIMS)
        except AuditError as exc:
            if needle not in str(exc):
                failures.append(f"{label}: refused for the wrong reason: {exc}")
        else:
            failures.append(f"{label}: the report was accepted")

    try:
        imports, claims = audit_source(_GOOD_SOURCE, "AxiomCheck.lean")
    except AuditError as exc:
        return [f"the good audit source was refused: {exc}"], 0
    if claims != _GOOD_CLAIMS or imports != list(REQUIRED_IMPORTS[:3]) + [WALKER_MODULE]:
        failures.append(f"the good audit source was misread: {imports} {claims}")

    base = _GOOD_SOURCE
    refused_source("no union command", base.replace("#union_axioms_of_modules Blanc\n", ""),
                   "exactly one live")
    refused_source("union command twice", base.replace(
        "#union_axioms_of_modules Blanc\n", "#union_axioms_of_modules Blanc\n"
        "#union_axioms_of_modules Blanc\n"), "exactly one live")
    refused_source("union command over another root",
                   base.replace("#union_axioms_of_modules Blanc", "#union_axioms_of_modules Blanc.Lift"),
                   "exactly one live")
    refused_source("allowed-axiom override", base.replace(
        "#union_axioms_of_modules Blanc", "#union_axioms_of_modules Blanc [propext, sorryAx]"),
        "an audit source may hold only")
    refused_source("union command only in a comment", base.replace(
        "#union_axioms_of_modules Blanc\n", "-- #union_axioms_of_modules Blanc\n"), "exactly one live")
    refused_source("#print axioms", base + "#print axioms Blanc.A.b\n", "#print axioms")
    refused_source("per-theorem #full_axioms row", base + "#full_axioms Blanc.A.b\n",
                   "an audit source may hold only")
    refused_source("evaluation command", base + "#eval 1\n", "an audit source may hold only")
    refused_source("a claim of exactly the standard set", base + (
        "#expect_axioms Blanc.A.d [propext, Classical.choice, Quot.sound]\n"), "not a stricter claim")
    refused_source("duplicate claim", base + "#expect_axioms Blanc.A.c []\n", "duplicate stricter claim")
    refused_source("claim inside a comment", base + "-- #expect_axioms Blanc.A.z []\n",
                   "live rows")
    refused_source("import after a command", base + "import Lean\n", "import after")
    refused_source("missing Blanc root", base.replace("import Blanc.ProofRecipesGenerated\n", ""),
                   "must import")
    refused_source("missing walker import", base.replace("import AxiomAudit\n", ""), "must import")
    refused_source("report marker forgery", base + "-- UNION-AXIOMS\n", "report marker")
    refused_source("precomputed collector", base + "#eval Lean.collectAxioms\n", "precomputed collector")

    try:
        line, counts = parse_report(_GOOD_OUTPUT, _GOOD_CLAIMS)
    except AuditError as exc:
        failures.append(f"the good report was refused: {exc}")
    else:
        if counts.get("roots") != 9 or counts.get("claims") != 2:
            failures.append(f"the good report was misread: {counts}")
    refused_output("no walk report", _GOOD_OUTPUT.split("\n", 1)[1], "0 UNION-AXIOMS")
    refused_output("two walk reports", _GOOD_OUTPUT.split("\n", 1)[0] + "\n" + _GOOD_OUTPUT,
                   "2 UNION-AXIOMS")
    refused_output("empty population", _GOOD_OUTPUT.replace("roots=9", "roots=0"), "empty population")
    refused_output("no module", _GOOD_OUTPUT.replace("modules=3", "modules=0"), "empty population")
    refused_output("walk over another prefix", _GOOD_OUTPUT.replace("'Blanc'", "'Blanc.Lift'"),
                   "not 'Blanc'")
    refused_output("non-standard axiom", _GOOD_OUTPUT.replace("propext]", "propext, sorryAx]", 1),
                   "non-standard")
    refused_output("missing claim report", _GOOD_OUTPUT.replace("AXIOM OK Blanc.A.c: []\n", ""),
                   "0 claim reports")
    refused_output("wrong claim set", _GOOD_OUTPUT.replace("Blanc.A.c: []", "Blanc.A.c: [propext]"),
                   "reported")
    refused_output("unclaimed report", _GOOD_OUTPUT + "AXIOM OK Blanc.A.z: []\n", "not claimed")
    return failures, controls


_GOOD_CLAIMS = {
    "Blanc.A.b": frozenset({"propext", "Quot.sound"}),
    "Blanc.A.c": frozenset(),
}


def main(argv: List[str]) -> int:
    if argv == ["self-test"]:
        failures, controls = self_test()
        for failure in failures:
            print(f"REGRESSION — axiom audit driver control: {failure}")
        if failures:
            return 1
        print(f"OK — axiom audit driver controls: {controls} controls refuse and the good source "
              "and report pass")
        return 0
    if len(argv) != 2 or argv[0] not in ("run", "claims"):
        print("usage: axiom_audit.py {run|claims} AUDIT.lean | self-test", file=sys.stderr)
        return 2
    root = Path(__file__).resolve().parent.parent
    relative = argv[1]
    try:
        if argv[0] == "claims":
            claims = audit_source((root / relative).read_text(encoding="utf-8"), relative)[1]
            sys.stdout.write("".join(f"{name}|{','.join(sorted(a))}\n"
                                     for name, a in sorted(claims.items())))
            return 0
        return run(root, relative)
    except (AuditError, OSError) as exc:
        print(f"axiom audit: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
