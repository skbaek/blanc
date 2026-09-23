"""The one driver for Blanc's from-scratch axiom audit.

Every Blanc gate that pins a declaration's axiom set takes its verdict from
``#full_axioms``, the walker defined once in ``scripts/AxiomAudit.lean``; read
that file's header for why Lean's own ``#print axioms`` / ``collectAxioms``
report is not used (https://github.com/leanprover/lean4/issues/15226). This
module is how a gate gets the walker into the file it elaborates and reads the
answer back. It never keeps a copy of the walker: the Lean text is read from
the tree under test every time.

* :func:`audit_rows` validates a committed audit source and returns its rows.
* :func:`splice` inserts the walker after a validated audit source's imports
  (``scripts/AxiomCheck.lean``, ``scripts/ProxyPairUpgradeAxiomCheck.lean``).
* :func:`probe_source` builds a probe from an import list and names (the Lido
  gates' generated probes).
* :func:`fixture_probe` appends the walker plus ``#full_axioms`` rows to a
  fixture that is elaborated anyway (the Lido Registry fixtures).
* :func:`elaborate` runs ``lake env lean --stdin`` on a source; no temporary
  file is written into the tree.
* :func:`parse` reads the ``FULL-AXIOMS`` lines back, exactly one per name.

Fail-closed rules enforced here, so no gate has to remember them:

* A committed audit source, once ``--`` and nested ``/- -/`` comments are
  removed, may contain nothing but blank lines, a leading block of
  ``import M`` lines and ``#full_axioms NAME`` rows, each name at most once.
  The text ``#full_axioms`` may not appear inside a comment either (so no
  static reader can count a commented-out row), and the report marker may not
  appear at all. ``#print axioms``, ``#eval``, a new ``elab`` or anything else
  is refused before Lean runs.
* A generated probe is built only from plain dotted module and declaration
  names.
* A fixture that has the walker appended may not mention ``#full_axioms``,
  the report marker, the walker's namespace, or Lean's collector. Its other
  code is the fixture's own reviewed source. A report it forged anyway would
  still fail the gate: every appended row prints its own report, and
  :func:`parse` refuses a name with two.
* Neither the walker's code nor an audit source's code (comments aside) may
  name Lean's precomputed collector or its per-module table.
* :func:`parse` requires exactly one report per requested name and none for
  any other name.

These rules tie each verdict to the walker. They are not a sandbox for
arbitrary Lean in a fixture file.

Command line (used by ``scripts/check.sh``)::

    python3 scripts/axiom_audit.py run scripts/AxiomCheck.lean
    python3 scripts/axiom_audit.py rows scripts/AxiomCheck.lean

``run`` validates and elaborates the spliced file from the repository root and
exits with Lean's status. ``rows`` validates the file and prints its audited
names, one per line, which is the audit inventory. ``splice`` prints the
spliced source.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Tuple


WALKER_RELATIVE = "scripts/AxiomAudit.lean"
COMMAND = "#full_axioms"

# A declaration or module name as the audit accepts it: a plain dotted
# identifier, the character class the gates have always used for the inventory.
NAME = r"[A-Za-z_][A-Za-z0-9_.?']*"
NAME_ONLY = re.compile(NAME + r"\Z")
AUDIT_ROW = re.compile(r"#full_axioms[ \t]+(" + NAME + r")[ \t]*\Z")
AUDIT_IMPORT = re.compile(r"import[ \t]+(" + NAME + r")[ \t]*\Z")
# Lean's report, which is exactly what an audit source may no longer ask for.
PRINT_AXIOMS = re.compile(r"^[ \t]*#print[ \t]+axioms\b", re.M)
REPORT = re.compile(r"^FULL-AXIOMS '([^']+)': \[([^\]\n]*)\]$", re.M)
IMPORT = re.compile(r"^import[ \t]+\S")
# Identifiers the walker's code must not use: Lean's precomputed collector and
# the per-module table it reads.
FORBIDDEN_WALKER_CODE = re.compile(
    r"collectAxioms|CollectAxioms|exportedAxioms|#print\s+axioms"
)


class AuditError(Exception):
    """The audit could not be assembled or read; never a pass."""


def strip_lean_comments(text: str, label: str = WALKER_RELATIVE) -> str:
    """Remove `--` line comments and nested `/- -/` block comments.

    String literals are kept verbatim (a comment opener inside one is not a
    comment). Used to police code (the walker's, an audit source's, a
    fixture's), so it errs toward keeping text: anything it keeps is checked.
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


def walker_body(root: Path) -> str:
    """The walker's text without its own `import Lean` line."""

    path = Path(root) / WALKER_RELATIVE
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise AuditError(f"cannot read the axiom walker {WALKER_RELATIVE}: {exc}")
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
    if 'elab "#full_axioms "' not in code:
        raise AuditError(f"{WALKER_RELATIVE} no longer defines {COMMAND}")
    return "\n".join(lines[1:]).strip("\n") + "\n"


def _refuse_print_axioms(source: str, label: str) -> None:
    found = PRINT_AXIOMS.search(source)
    if found:
        line = source.count("\n", 0, found.start()) + 1
        raise AuditError(
            f"{label}:{line}: `#print axioms` is not an audit verdict source "
            f"(lean4#15226); audit rows are `{COMMAND} NAME`"
        )


def _refuse_report_forgery(source: str, label: str, code: str) -> None:
    if "FULL-AXIOMS" in source:
        raise AuditError(f"{label}: may not contain the report marker `FULL-AXIOMS`")
    found = FORBIDDEN_WALKER_CODE.search(code)
    if found:
        raise AuditError(
            f"{label}: code names {found.group(0)!r}; an audit may not take its "
            "answer from Lean's precomputed axiom report (lean4#15226)"
        )


def audit_rows(source: str, label: str) -> List[str]:
    """Validate a committed audit source; return its row names in order.

    After comments are removed only blank lines, a leading `import` block and
    `#full_axioms NAME` rows may remain; every `#full_axioms` in the raw text
    must be one of those rows, and no name may repeat.
    """

    _refuse_print_axioms(source, label)
    code = strip_lean_comments(source, label)
    _refuse_report_forgery(source, label, code)
    names: List[str] = []
    for number, raw in enumerate(code.splitlines(), start=1):
        line = raw.strip()
        if not line:
            continue
        row = AUDIT_ROW.match(line)
        if row:
            names.append(row.group(1))
            continue
        if AUDIT_IMPORT.match(line):
            if names:
                raise AuditError(f"{label}:{number}: import after the first audit row")
            continue
        raise AuditError(
            f"{label}:{number}: an audit source may hold only imports and "
            f"`{COMMAND} NAME` rows; found {line[:60]!r}"
        )
    mentions = source.count(COMMAND)
    if mentions != len(names):
        raise AuditError(
            f"{label}: `{COMMAND}` appears {mentions} times but only {len(names)} "
            "are live rows; a row inside a comment is refused"
        )
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        raise AuditError(f"{label}: duplicate audit rows: {', '.join(duplicates)}")
    if not names:
        raise AuditError(f"{label}: no audit rows")
    return names


def _checked_names(values: Iterable[str], what: str) -> List[str]:
    checked = list(values)
    for value in checked:
        if not NAME_ONLY.match(value):
            raise AuditError(f"not a plain {what} name: {value!r}")
    return checked


def splice(root: Path, source: str, label: str) -> str:
    """The validated `source` with the walker inserted after its imports."""

    audit_rows(source, label)
    lines = source.splitlines()
    cut = 0
    for index, line in enumerate(lines):
        if IMPORT.match(line):
            cut = index + 1
        elif line.strip() and not line.startswith("--"):
            break
    if cut == 0:
        raise AuditError(f"{label}: no leading import block to splice the walker after")
    head = lines[:cut] + ["import Lean"]
    return "\n".join(head) + "\n\n" + walker_body(root) + "\n" + "\n".join(lines[cut:]) + "\n"


def rows(names: Iterable[str]) -> str:
    return "".join(f"{COMMAND} {name}\n" for name in names)


def probe_source(root: Path, imports: Iterable[str], names: Iterable[str]) -> str:
    """A complete probe: the imports, the walker, one row per name."""

    modules = _checked_names(imports, "module")
    wanted = _checked_names(names, "declaration")
    header = "".join(f"import {module}\n" for module in modules) + "import Lean\n"
    return header + "\n" + walker_body(root) + "\n" + rows(wanted)


def fixture_probe(root: Path, fixture: str, label: str, names: Iterable[str]) -> str:
    """`fixture` followed by the walker and one row per name.

    The fixture may not mention the audit's command, report marker or
    namespace, or Lean's collector; a report it forged anyway would collide
    with the appended row's own report, which `parse` refuses.
    """

    wanted = _checked_names(names, "declaration")
    code = strip_lean_comments(fixture, label)
    _refuse_report_forgery(fixture, label, code)
    for token in (COMMAND, "BlancAxiomAudit"):
        if token in fixture:
            raise AuditError(f"{label}: a fixture may not mention `{token}`")
    return fixture + "\n" + walker_body(root) + "\n" + rows(wanted)


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


def parse(output: str, names: Iterable[str]) -> Dict[str, FrozenSet[str]]:
    """Exactly one `FULL-AXIOMS` report per requested name, as a set.

    A missing or repeated report raises; so does a report for a name that was
    not asked for, since the rows and the answers must be the same population.
    """

    wanted = list(names)
    reports: Dict[str, List[FrozenSet[str]]] = {}
    for match in REPORT.finditer(output):
        axioms = frozenset(
            part.strip() for part in match.group(2).split(",") if part.strip()
        )
        reports.setdefault(match.group(1), []).append(axioms)
    problems = []
    for name in wanted:
        count = len(reports.get(name, []))
        if count != 1:
            problems.append(f"{name}: {count} from-scratch axiom reports, expected 1")
    unexpected = sorted(set(reports) - set(wanted))
    if unexpected:
        problems.append("reports for names that were not audited: " + ", ".join(unexpected))
    if problems:
        raise AuditError("; ".join(problems))
    return {name: reports[name][0] for name in wanted}


def audit(root: Path, imports: Iterable[str], names: Iterable[str]) -> Dict[str, FrozenSet[str]]:
    """Probe `names` under `imports`; raises AuditError on any failure."""

    wanted = list(names)
    status, output = elaborate(root, probe_source(root, imports, wanted))
    if status != 0:
        raise AuditError(f"`lake env lean` exited {status}; output follows:\n{output.rstrip()}")
    return parse(output, wanted)


def main(argv: List[str]) -> int:
    if len(argv) != 2 or argv[0] not in ("run", "rows", "splice"):
        print("usage: axiom_audit.py {run|rows|splice} AUDIT.lean", file=sys.stderr)
        return 2
    root = Path(__file__).resolve().parent.parent
    relative = argv[1]
    try:
        text = (root / relative).read_text(encoding="utf-8")
        if argv[0] == "rows":
            sys.stdout.write("".join(name + "\n" for name in audit_rows(text, relative)))
            return 0
        source = splice(root, text, relative)
    except (AuditError, OSError) as exc:
        print(f"axiom audit: {exc}", file=sys.stderr)
        return 2
    if argv[0] == "splice":
        sys.stdout.write(source)
        return 0
    try:
        status, output = elaborate(root, source)
    except AuditError as exc:
        print(f"axiom audit: {exc}", file=sys.stderr)
        return 2
    sys.stdout.write(output)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
