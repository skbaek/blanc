#!/usr/bin/env python3
"""End-to-end assurance-register gate for Blanc's Lido CircuitBreaker port.

`LIDO_CIRCUIT_BREAKER_ASSURANCE.md` is the one document licensed to say, for
each sentence a reader might quote, which declaration makes it true, which
axioms that declaration leans on, which gate owns the evidence, which
differential channel corroborates it, and where the claim stops. A register
like that is only worth its ink while every one of those columns is still true
of the tree. Prose does not re-derive itself, so a register drifts silently the
moment a declaration is renamed, an axiom pin moves, a gate is retired, or a
non-claim is quietly edited out of a row -- and a register that has drifted is
worse than none, because it is read as authority.

This gate closes that class. It reads the register and requires five things,
each fail-closed:

  1. Structure and anti-vacuity. Every `####` row under a `## Pillar —`
     heading carries all seven labelled fields, exactly once each, in the
     frozen order, non-empty; ROWIDs are unique; every pinned pillar is
     present; and the per-pillar row counts, the total, the number of gate-owned
     rows and the number of rows naming more than one gate all equal the numbers
     pinned in this file. A row deleted, renamed, or reworded out of this gate's
     sight FAILS rather than shrinking a green count -- the anti-vacuity
     contract `check-doc-counts.py` states for quotations, restated for rows.
     The last two counts pin the two escape hatches: a row can decline the axiom
     check by becoming gate-owned, and a row can rescue a mis-attributed
     declaration by naming a second authority for it to resolve against.
     Neither may widen without someone deciding to widen it.

  2. Declaration resolution, against the authority the ROW ITSELF names. A
     row's **Gate** field is not decorative: it names the gate that must pin
     the row's declarations. Blanc has several axiom-expectation authorities,
     not one -- the repository audit pins one population, and the Lido access,
     enumeration, registry and history gates each pin their own family with
     their own `#print axioms` probe -- so "is this name audited?" is only
     answerable relative to a gate. Names are matched FULLY QUALIFIED:
     `Blanc.Weth10.canonicalDeploymentStep_establishes_root` and
     `Blanc.LidoCircuitBreaker.canonicalDeploymentStep_establishes_root` are
     different theorems sharing a last component, and a checker matching on
     the short name would credit a citation no gate ever made.

  3. Axiom-expectation agreement with that authority. The register's **Axioms**
     field must equal, exactly and order-insensitively, the expectation the
     row's authority states for that declaration. An empty expectation means
     "depends on no axioms at all", which the register must write as the single
     word `none`; both directions are checked, so neither a fabricated axiom
     list nor a fabricated `none` passes. Where a name is pinned by two
     authorities, THE TWO MUST AGREE WITH EACH OTHER: a disagreement is
     reported as a repository inconsistency and never quietly resolved in
     either direction, because either answer is a real finding.

  4. Gate existence and registration. Every path in a **Gate** field exists
     under the repository root and is catalogued in `scripts/GATES.md`.

  5. Non-claim coverage. Every load-bearing non-claim phrase pinned below
     still appears somewhere in the register. Non-claims are the half of an
     assurance argument that erodes without anyone deciding to erode it.

WHAT THIS GATE DOES NOT OWN
---------------------------

It does not elaborate Lean and does not re-derive any axiom set. Its DEFAULT
MODE IS STATIC: it checks that the register agrees with the pin tables of the
authorities listed below, and its authority over the axiom column is exactly
theirs -- `scripts/check.sh --no-build` for the repository audit, and each
family gate's own `#print axioms` probe for the family it pins. Those gates
verify their expectations against Lean by elaborating; this gate makes the
register faithful to them. Neither substitutes for the other, and this gate is
not evidence that any theorem holds.

It does not check that a row's prose is a fair summary of its declaration, that
the **Premises** field is complete, or that a **Differential channel** name
corresponds to a real oracle case. Those are review obligations, not
mechanically checkable ones, and pretending otherwise would be the vacuity this
gate exists to prevent.

It owns only this repository's tree, per AGENTS.md's rule that a gate lives in
the repository whose tree it checks. The plain-language companion lives in the
plans repository and no gate here can see it.

GATE-OWNED ROWS
---------------

A few rows carry real evidence with no audited theorem behind them -- an
emitted error table, a finite differential matrix. Dropping them would make the
register less honest, so the schema admits them: a row whose **Declarations**
field is exactly `no audited declaration — gate-owned row` is gate-owned, must
set **Axioms** to exactly `not applicable`, and still carries all seven fields
and a real registered gate. Channels 2 and 3 skip those rows and nothing else,
and the gate-owned COUNT is pinned and printed, so converting a normal row into
a gate-owned one to dodge the axiom check moves the count and FAILS.

A name that resolves in the tree but is pinned by no authority is NOT
tolerated. Several real declarations are deliberately outside every pin table;
the register cites those in **Premises** prose only. Channel 2 fails on them by
design, and says so specifically, because the fix is to move the name to
**Premises** or to make the row gate-owned -- never to widen an audit.

THE AUTHORITIES
---------------

This gate READS other gates' pin tables and never writes them. That coupling is
the point: when a gate's pin table moves, this gate's answer moves with it. The
tables are read with `ast`, never imported or executed.

  * `scripts/check.sh` + `scripts/AxiomCheck.lean` -- the repository axiom
    audit. Resolves every `#print axioms` name; expectation from the `ROWS`
    table, with an empty expectation meaning no axioms at all.
  * `scripts/check-lido-circuit-breaker-deployment.sh` -- that gate's axiom
    section verifies its public inventory against `scripts/AxiomCheck.lean` and
    `scripts/check.sh` themselves, so its authority IS the repository audit and
    it is registered as an alias for it.
  * `scripts/check-lido-circuit-breaker-access.sh` -- `ROLES`, expectation
    `AXIOM_EXCEPTIONS.get(name, STANDARD_AXIOMS)`. Names are written short,
    relative to `Blanc.LidoCircuitBreaker.`.
  * `scripts/check-lido-circuit-breaker-enumeration.sh` -- `ROLES`, uniform
    `EXPECTED_AXIOMS`. Short names.
  * `scripts/check-lido-circuit-breaker-registry.sh` -- resolves the names in
    `REQUIRED` and `EXPECTED_HEADERS`; states a per-name axiom expectation only
    for the four fixture controls in `AXIOM_CONTROLS`. Every other name it
    pins therefore takes its axioms from the repository audit.
  * `scripts/check-lido-circuit-breaker-history.sh` -- expectation uniformly
    `STANDARD_AXIOMS`, over a population DERIVED from its owner modules rather
    than read from a table: every public `theorem`/`lemma` its probe covers.
    The uniformity is not an absence of an expectation, and the absence of an
    exception table is not an absence of exceptions being possible -- it means
    there are none. `HEADER_PINS` is a DIGEST population, not that one: it also
    covers the `def`/`structure` layer (`RegistryStable`, `Coherent`,
    `registrySpec`), which is pinned by digest and never probed. Those names
    stay RESOLUTION-ONLY, which is what keeps them out of **Declarations**
    while the register goes on citing them as premise vocabulary.

A gate that is not in that list is not an authority. A row naming such a gate
may still carry evidence -- it just may not cite declarations, so it is a
gate-owned row.

`--probe`
---------

An optional, non-default mode that closes the loop directly instead of
transitively: it regenerates a `#print axioms` file from the register's own
citations, elaborates it with `lake env lean`, and compares the reported axiom
sets against the register's fields. It REQUIRES the Lean toolchain and a built
dependency graph, is not what CI or the cheap catalogue row runs, and must not
be run beside a measurement that owns the host.

The default mode needs no Lean toolchain, no build and no network -- it reads
committed files only -- so it is instant, takes no report or heavy lock (it
writes nothing), and runs identically here and in CI.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
"""

from __future__ import annotations

import argparse
import ast
import pathlib
import re
import subprocess
import sys
import tempfile

VERDICT_SUBJECT = "lido-circuit-breaker-assurance"

REGISTER_RELATIVE = "LIDO_CIRCUIT_BREAKER_ASSURANCE.md"
AXIOM_CHECK_RELATIVE = "scripts/AxiomCheck.lean"
AXIOM_PINS_RELATIVE = "scripts/check.sh"
CATALOGUE_RELATIVE = "scripts/GATES.md"

# ---------------------------------------------------------------------------
# PINNED EXPECTATIONS -- re-pin this block against the real register.
#
# These numbers are the anti-vacuity contract: they are what makes a deleted,
# renamed, or reworded-away row a FAILURE instead of a smaller green count.
# They were pinned against the register at Stage 8 closure, 2026-08-27, by
# reading the counts the gate itself reported over the finished document.
# Moving a number here to make a red gate green is exactly Rule 1 in
# `scripts/GATES.md`: a row that disappears must fail, and the only legitimate
# reason to edit this block is that the register deliberately gained or lost a
# row, in which case the edit belongs in the same commit as that row.
#
# Every pillar named here must exist in the register and carry at least one
# row; a pillar in the register that is missing here is also a failure, so the
# map is exhaustive in both directions.
EXPECTED_ROWS_PER_PILLAR = {
    "Registry integrity": 12,
    "ABI and observability": 6,
    "Operational monitoring": 5,
    "Access-control completeness": 7,
    "Temporal authority": 8,
    "Single-use pause": 5,
    "External-call honesty": 4,
    "Hostile-world results (Stage 6)": 3,
    "Deployment and history": 13,
    "Artifact conformance and cost": 4,
}

# The total is pinned SEPARATELY from the per-pillar map rather than derived
# from it. Deriving it would let a single edit move a row between pillars and a
# matching edit here keep the gate green with no total to disagree with; two
# independent pins have to be falsified together.
EXPECTED_TOTAL_ROWS = 67

# Rows whose Declarations field is the gate-owned literal. Pinned so the
# escape hatch cannot widen quietly: convert one normal row and this fails.
EXPECTED_GATE_OWNED_ROWS = 9

# Rows whose Gate field names more than one gate.
#
# Naming two gates is legitimate and four rows do it: one gate owns the row's
# evidence and the other pins its axioms, and both really would fail if the row
# moved. But a second gate name is also the one edit that can make a
# MIS-ATTRIBUTED declaration resolve. A name pinned by the access authority,
# sitting on a row whose Gate says enumeration, is a real error this gate
# catches -- until someone appends `scripts/check.sh` to that row, at which
# point the name resolves against the repository audit and the mis-attribution
# is rescued rather than reported. Discipline is not a mechanism, so the count
# is pinned in both directions.
#
# A future editor who genuinely needs a fifth multi-gate row bumps this number
# in the same commit as the row, having decided that the row's second gate is
# an authority it really depends on rather than padding. That is a decision.
# Bumping it to clear a red gate is Rule 1 in `scripts/GATES.md`.
EXPECTED_MULTI_GATE_ROWS = 4

# Load-bearing non-claims. Each must still appear somewhere in the register.
# Matched case-insensitively against the register with all whitespace runs
# collapsed to single spaces, so a phrase may span a line wrap and re-wrapping
# the file is not a failure. Each phrase is chosen to carry the substance of
# its non-claim rather than a heading, so a narrowing edit cannot delete the
# claim's limit and accidentally leave the phrase behind.
NONCLAIM_PHRASES = [
    # No deployed-bytecode claim: the mainnet address is provenance only.
    "0x6019CB557978296BA3C08a7B73225C0975DFB2F7",
    # No target-truth claim: returndata is an observation, not a fact about
    # the callee's state.
    'it is not "the target is paused"',
    # No universal gas claim: the gas evidence is a finite vector.
    "finite 175-row / 464-boundary vector",
    # The deployment root is one exact official creation, not a schema.
    "no parameter-generic deployment root",
    "clone, factory, proxy, or CREATE2 path",
    "no nonzero endowment",
    # No signature, inclusion, or historical-mainnet claim.
    "no signature, inclusion, or historical-mainnet claim",
    # The history witness is existential, not the same list.
    "the history witness is existential, not the same list",
    # Reachability carries a wei bound inherited from the chain model.
    "below `2 ^ 256`",
    # No liveness.
    "nothing here says the contract can be paused",
    # Mid-callback count/expiry incoherence is real source behaviour.
    "no callback-time count/expiry coherence",
    # Finite evidence corroborates; it is never a Lean premise.
    "finite replay and differential evidence are never Lean premises",
    # The synthetic satisfying world is an anti-vacuity exhibit, not a
    # deployment.
    "the synthetic stable world receives no deployment credit",
]
# END PINNED EXPECTATIONS
# ---------------------------------------------------------------------------

# The frozen row schema. Order is part of the schema: a register whose fields
# drift out of order is a register two people will read differently.
FIELD_ORDER = [
    "Declarations",
    "Premises",
    "Axioms",
    "Gate",
    "Differential channel",
    "Non-claims",
    "Source",
]

GATE_OWNED_DECLARATIONS = "no audited declaration — gate-owned row"
GATE_OWNED_AXIOMS = "not applicable"
NO_AXIOMS_WORD = "none"

PILLAR_HEADING = re.compile(r"^##\s+Pillar\s+—\s+(.+?)\s*$")
ANY_HEADING = re.compile(r"^(#{1,6})\s+(.*)$")
ROW_HEADING = re.compile(r"^####\s+(.+?)\s+—\s+(.+?)\s*$")
ROWID = re.compile(r"^[A-Z]+-[0-9]+$")
FIELD_ITEM = re.compile(r"^\s*-\s+\*\*([^*]+?):\*\*\s*(.*)$")

# Same character class scripts/check.sh uses to read the audit's own inventory,
# so the two gates agree on what a name is.
PRINT_AXIOMS = re.compile(r"^#print axioms[ \t]+([A-Za-z0-9_.?']+)", re.M)

# A cited name must be fully qualified; see the module docstring.
DECL_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_.?'!]*$")

# Belt and braces, mirroring scripts/check.sh: these must never appear in a
# probe's Lean output.
FORBIDDEN_AXIOMS = re.compile(r"sorryAx|ofReduceBool|ofReduceNat|_native\.")

# Declaration keywords recognised by the advisory tree scan. See resolve_tree().
TREE_DECL = re.compile(
    r"^(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom|class)"
    r"\s+([A-Za-z_][A-Za-z0-9_.?'!]*)"
)


def squeeze(text: str) -> str:
    """Collapse every whitespace run to one space."""

    return re.sub(r"\s+", " ", text).strip()


def clean_field(value: str) -> str:
    """Normalise a field value: no backticks, no whitespace runs."""

    return squeeze(value.replace("`", ""))


class Register:
    """One parsed row of the register."""

    def __init__(self, rowid: str, claim: str, pillar: str, line: int) -> None:
        self.rowid = rowid
        self.claim = claim
        self.pillar = pillar
        self.line = line
        self.fields: dict[str, str] = {}
        self.field_order: list[str] = []


def parse_register(text: str) -> tuple[list[Register], list[str], list[str]]:
    """Parse rows out of the register.

    Returns (rows, pillars in order of first appearance, structural failures).
    Structural failures are hard: a heading this parser cannot read is reported,
    never skipped, because a skipped row is a row nothing checked.
    """

    rows: list[Register] = []
    pillars: list[str] = []
    failures: list[str] = []

    lines = text.splitlines()
    pillar: str | None = None
    current: Register | None = None
    pending_label: str | None = None

    for index, raw in enumerate(lines, start=1):
        heading = ANY_HEADING.match(raw)
        if heading is not None:
            hashes = heading.group(1)
            if len(hashes) == 4:
                if pillar is None:
                    failures.append(
                        f"{REGISTER_RELATIVE}:{index}: `#### {squeeze(heading.group(2))}` "
                        "is a row block outside any `## Pillar — ...` heading; every row "
                        "must sit under a pillar or nothing counts it"
                    )
                    current = None
                    pending_label = None
                    continue
                match = ROW_HEADING.match(raw)
                if match is None:
                    failures.append(
                        f"{REGISTER_RELATIVE}:{index}: row heading does not match the "
                        "frozen `#### <ROWID> — <claim>` shape (em dash required): "
                        f"{squeeze(raw)}"
                    )
                    current = None
                    pending_label = None
                    continue
                rowid = squeeze(match.group(1)).replace("`", "")
                if not ROWID.match(rowid):
                    failures.append(
                        f"{REGISTER_RELATIVE}:{index}: ROWID {rowid!r} does not match "
                        "^[A-Z]+-[0-9]+$"
                    )
                current = Register(rowid, squeeze(match.group(2)), pillar, index)
                rows.append(current)
                pending_label = None
                continue

            # Any other heading closes the current row, and an `##` heading
            # decides whether we are inside a pillar at all.
            current = None
            pending_label = None
            if len(hashes) == 2:
                pillar_match = PILLAR_HEADING.match(raw)
                if pillar_match is not None:
                    pillar = pillar_match.group(1)
                    if pillar not in pillars:
                        pillars.append(pillar)
                    else:
                        failures.append(
                            f"{REGISTER_RELATIVE}:{index}: pillar {pillar!r} is opened "
                            "twice; its rows would be counted under one heading and "
                            "read under another"
                        )
                else:
                    pillar = None
            continue

        if current is None:
            continue

        item = FIELD_ITEM.match(raw)
        if item is not None:
            label = squeeze(item.group(1))
            value = item.group(2)
            if label in current.fields:
                failures.append(
                    f"{REGISTER_RELATIVE}:{index}: row {current.rowid} repeats the "
                    f"**{label}** field"
                )
            current.fields[label] = value
            current.field_order.append(label)
            pending_label = label
            continue

        if pending_label is not None and raw.strip():
            # A wrapped field value.
            current.fields[pending_label] += " " + raw.strip()
        elif not raw.strip():
            pending_label = None

    return rows, pillars, failures


def parse_axiom_pins(text: str) -> tuple[dict[str, list[str]], list[str]]:
    """Extract scripts/check.sh's ROWS table.

    The block opens with a line that is exactly `ROWS="\\` and closes with the
    double quote that ends the shell string -- which today sits at the end of
    the final row rather than on a line of its own, so both spellings are
    accepted. `$STANDARD` (and `${STANDARD}`) is expanded from the assignment
    immediately above the block, which is the only expansion the table uses.

    A row this parser cannot read is an error, never a skip: check.sh's own
    loop would treat such a line as a theorem name with no expectation, and a
    gate that silently dropped it would credit a register column nothing
    pinned.
    """

    pins: dict[str, list[str]] = {}
    problems: list[str] = []

    standard_match = re.search(r'^STANDARD="([^"]*)"\s*$', text, re.M)
    if standard_match is None:
        problems.append(
            f"{AXIOM_PINS_RELATIVE}: no `STANDARD=\"...\"` assignment; the pinned "
            "expectations cannot be expanded"
        )
        return pins, problems
    standard = standard_match.group(1)

    lines = text.splitlines()
    try:
        start = next(i for i, line in enumerate(lines) if line.rstrip() == 'ROWS="\\')
    except StopIteration:
        problems.append(
            f"{AXIOM_PINS_RELATIVE}: no `ROWS=\"\\` table; this gate has no pinned "
            "axiom expectations to compare the register against"
        )
        return pins, problems

    for offset, raw in enumerate(lines[start + 1 :], start=start + 2):
        line = raw
        closed = False
        if line.rstrip() == '"':
            break
        if line.rstrip().endswith('"') and not line.rstrip().endswith('\\"'):
            line = line.rstrip()[:-1]
            closed = True
        if line.strip():
            if "|" not in line:
                problems.append(
                    f"{AXIOM_PINS_RELATIVE}:{offset}: row has no `|` separator: "
                    f"{squeeze(line)}"
                )
            else:
                name, _, expectation = line.partition("|")
                name = name.strip()
                expectation = expectation.replace("${STANDARD}", standard)
                expectation = expectation.replace("$STANDARD", standard)
                axioms = [
                    part.strip() for part in expectation.split(",") if part.strip()
                ]
                if name in pins:
                    problems.append(
                        f"{AXIOM_PINS_RELATIVE}:{offset}: duplicate pin for {name}"
                    )
                pins[name] = axioms
        if closed:
            break
    else:
        problems.append(
            f"{AXIOM_PINS_RELATIVE}: the `ROWS` table is never closed by a `\"`"
        )

    if not pins:
        problems.append(
            f"{AXIOM_PINS_RELATIVE}: the `ROWS` table parsed to zero pins"
        )
    return pins, problems


def resolve_tree(root: pathlib.Path) -> set[str]:
    """Fully qualified declaration names visible in Blanc's own sources.

    ADVISORY ONLY. This is a lexical scan with a namespace stack, not Lean's
    elaborator: it recognises the declaration shapes this repository actually
    writes and nothing else. It is used exclusively to make a Channel 2 failure
    message more useful -- "this name exists but is unaudited, so cite it in
    **Premises**" rather than "unknown name". It can never make a row pass, so
    an under-approximation costs a sharper message and nothing else.
    """

    names: set[str] = set()
    for path in sorted((root / "Blanc").rglob("*.lean")):
        try:
            source = path.read_text(encoding="utf-8")
        except OSError:
            continue
        stack: list[str] = []
        for line in source.splitlines():
            stripped = line.strip()
            if stripped.startswith("namespace "):
                stack.append(stripped.split()[1])
                continue
            if stripped.startswith("end "):
                closing = stripped.split()[1]
                if stack and stack[-1] == closing:
                    stack.pop()
                continue
            match = TREE_DECL.match(line)
            if match is not None:
                names.add(".".join(stack + [match.group(1)]))
    return names


# --- axiom-expectation authorities -----------------------------------------

LIDO_NAMESPACE = "Blanc.LidoCircuitBreaker."

AUDIT_KEY = "audit"

# Gate path -> the key of the authority whose pin table decides that gate's
# rows. A gate absent from this map is not an authority; see the docstring.
AUTHORITY_BY_GATE = {
    AXIOM_PINS_RELATIVE: AUDIT_KEY,
    "scripts/check-lido-circuit-breaker-deployment.sh": AUDIT_KEY,
    "scripts/check-lido-circuit-breaker-access.sh": "access",
    "scripts/check-lido-circuit-breaker-enumeration.sh": "enumeration",
    "scripts/check-lido-circuit-breaker-registry.sh": "registry",
    "scripts/check-lido-circuit-breaker-history.sh": "history",
}

# The checker source each non-audit authority's pin table is read from.
AUTHORITY_SOURCE = {
    "access": "scripts/check-lido-circuit-breaker-access.py",
    "enumeration": "scripts/check-lido-circuit-breaker-enumeration.py",
    "registry": "scripts/check-lido-circuit-breaker-registry.py",
    "history": "scripts/check-lido-circuit-breaker-history.py",
}


class Unreadable(Exception):
    """A constant in another gate's source this reader will not guess at."""


class Authority:
    """One gate's pin table, as this gate reads it.

    `resolves` is the set of fully qualified names the authority pins at all.
    `expects` maps a name to the axiom set the authority states for it; a name
    in `resolves` but not in `expects` is one the authority pins without
    stating an expectation, which sends the row to the repository audit.
    """

    def __init__(self, key: str, resolves: set[str], expects: dict[str, frozenset[str]]) -> None:
        self.key = key
        self.resolves = resolves
        self.expects = expects


def python_constants(path: pathlib.Path, wanted: list[str]) -> dict[str, object]:
    """Read named top-level constants out of another gate's own source.

    Parsed with `ast` and evaluated by a restricted evaluator: literals,
    containers, `set()`/`frozenset()`, and references to constants already
    bound above. The other gate is never imported and never executed, so
    reading its pin table cannot run its probes, touch the tree, or start Lean.

    A constant that cannot be read is an ERROR for the names asked for, never a
    silent empty table -- an empty pin table would make every row citing that
    authority fail in a way that looks like the register's fault, or, worse,
    would make an authority look permissive.
    """

    tree = ast.parse(path.read_text(encoding="utf-8"))
    env: dict[str, object] = {}

    def evaluate(node: ast.AST) -> object:
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Dict):
            return {
                evaluate(key): evaluate(value)
                for key, value in zip(node.keys, node.values)
                if key is not None
            }
        if isinstance(node, (ast.Tuple, ast.List)):
            return [evaluate(element) for element in node.elts]
        if isinstance(node, ast.Set):
            return {evaluate(element) for element in node.elts}
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id]
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in ("set", "frozenset")
        ):
            if not node.args:
                return set()
            if len(node.args) == 1:
                return set(evaluate(node.args[0]))  # type: ignore[arg-type]
        raise Unreadable(ast.dump(node)[:80])

    for node in tree.body:
        target = None
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            if isinstance(node.targets[0], ast.Name):
                target = node.targets[0].id
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            target = node.target.id
        if target is None or node.value is None:
            continue
        try:
            env[target] = evaluate(node.value)
        except Unreadable:
            # Not every constant in another gate is data -- `ROOT / "x.lean"`,
            # compiled regexes, dataclasses. Skipping those is safe; skipping a
            # WANTED one is not, and is caught below.
            continue

    values: dict[str, object] = {}
    for name in wanted:
        if name not in env:
            raise Unreadable(f"{path.name}: cannot read constant {name}")
        values[name] = env[name]
    return values


def python_class_constants(
    path: pathlib.Path, class_name: str, wanted: list[str]
) -> dict[str, object]:
    """Read literal attributes off a top-level class in another gate's source.

    The history gate holds its Chain owner's activation switch, path and module
    as class attributes of `ChainActivation`, so the module-level reader above
    cannot see them. Same restricted evaluator, same refusal to import.
    """

    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == class_name:
            break
    else:
        raise Unreadable(f"{path.name}: no class {class_name}")

    values: dict[str, object] = {}
    for statement in node.body:
        target = None
        if isinstance(statement, ast.Assign) and len(statement.targets) == 1:
            if isinstance(statement.targets[0], ast.Name):
                target = statement.targets[0].id
        elif isinstance(statement, ast.AnnAssign) and isinstance(
            statement.target, ast.Name
        ):
            target = statement.target.id
        if target is None or target not in wanted or statement.value is None:
            continue
        if isinstance(statement.value, ast.Constant):
            values[target] = statement.value.value

    for name in wanted:
        if name not in values:
            raise Unreadable(f"{path.name}: cannot read {class_name}.{name}")
    return values


# Reproduced from `scripts/check-lido-circuit-breaker-history.py`, whose
# `declarations()` decides which names its axiom probe covers. Kept
# deliberately identical in the two decisions that matter -- declaration KIND
# and PRIVATENESS -- because this gate must never admit a name that gate would
# not probe. Everything that function does beyond those two (slicing a
# declaration's exact text for digests) is irrelevant here and is not copied.
LEAN_DECL_KINDS = (
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|example)"
)
LEAN_DECL_HEAD = re.compile(
    r"^(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)"
    r"(?P<kind>" + LEAN_DECL_KINDS + r")\s+(?P<name>[^\s({\[:]+)"
)


def strip_lean_comments(source: str) -> str:
    """Blank every Lean comment, preserving offsets, newlines and strings.

    Reproduced from the history gate's `strip_comments`. Nesting is honoured,
    `--` inside a string literal is not a comment, and string contents survive.
    An unterminated block comment raises rather than returning a text whose
    comment/code separation is unsafe -- guessing there could hide or invent a
    declaration, and both directions are wrong.
    """

    out: list[str] = []
    index, size, depth = 0, len(source), 0
    while index < size:
        char = source[index]
        if depth == 0 and char == '"':
            out.append(char)
            index += 1
            while index < size:
                out.append(source[index])
                if source[index] == "\\" and index + 1 < size:
                    out.append(source[index + 1])
                    index += 2
                    continue
                if source[index] == '"':
                    index += 1
                    break
                index += 1
            continue
        if source.startswith("/-", index):
            depth += 1
            out.append("  ")
            index += 2
            continue
        if depth > 0 and source.startswith("-/", index):
            depth -= 1
            out.append("  ")
            index += 2
            continue
        if depth > 0:
            out.append("\n" if char == "\n" else " ")
            index += 1
            continue
        if source.startswith("--", index):
            end = source.find("\n", index)
            end = size if end < 0 else end
            out.append(" " * (end - index))
            index = end
            continue
        out.append(char)
        index += 1
    if depth:
        raise Unreadable("unterminated Lean block comment")
    return "".join(out)


def lean_public_theorems(source: str) -> set[str]:
    """Fully qualified public `theorem`/`lemma` names declared in one module.

    The same rule the history gate's axiom probe selects by: kind is `theorem`
    or `lemma`, the declaration is not `private`, and the name is qualified by
    the namespace stack it sits in. Anything this scan cannot classify is
    simply not matched, which excludes it -- the safe direction, since a name
    this gate admits but that gate never probes would be an expectation nobody
    checks.
    """

    code = strip_lean_comments(source)
    namespaces: list[str] = []
    names: set[str] = set()
    for line in code.split("\n"):
        opened = re.match(r"^namespace\s+(\S+)", line)
        if opened:
            namespaces.append(opened.group(1))
            continue
        closed = re.match(r"^end\s+(\S+)", line)
        if closed:
            if namespaces and namespaces[-1] == closed.group(1):
                namespaces.pop()
            continue
        head = LEAN_DECL_HEAD.match(line)
        if head is None:
            continue
        if head.group("kind") not in ("theorem", "lemma"):
            continue
        if "private" in head.group("mods"):
            continue
        names.add(".".join(namespaces) + "." + head.group("name"))
    return names


def qualify(names) -> set[str]:
    """Short Lido names as the register writes them: fully qualified."""

    return {LIDO_NAMESPACE + name for name in names}


def load_authorities(
    root: pathlib.Path, audited: set[str], pins: dict[str, list[str]]
) -> tuple[dict[str, Authority], list[str]]:
    """Build every authority's pin table. Reads; never writes."""

    problems: list[str] = []
    authorities: dict[str, Authority] = {
        AUDIT_KEY: Authority(
            AUDIT_KEY,
            set(audited),
            {name: frozenset(axioms) for name, axioms in pins.items()},
        )
    }

    def source(key: str) -> pathlib.Path:
        return root / AUTHORITY_SOURCE[key]

    # --- access: ROLES, with AXIOM_EXCEPTIONS over STANDARD_AXIOMS ----------
    try:
        read = python_constants(
            source("access"), ["ROLES", "AXIOM_EXCEPTIONS", "STANDARD_AXIOMS"]
        )
        standard = frozenset(read["STANDARD_AXIOMS"])  # type: ignore[arg-type]
        exceptions = read["AXIOM_EXCEPTIONS"]
        names: set[str] = set()
        for role in read["ROLES"].values():  # type: ignore[union-attr]
            names |= set(role)
        expects = {
            LIDO_NAMESPACE + name: frozenset(
                exceptions[name] if name in exceptions else standard  # type: ignore[operator]
            )
            for name in names
        }
        authorities["access"] = Authority("access", qualify(names), expects)
    except (Unreadable, OSError, TypeError, AttributeError) as exc:
        problems.append(f"cannot read the access gate's pin table: {exc}")

    # --- enumeration: ROLES, uniform EXPECTED_AXIOMS ------------------------
    try:
        read = python_constants(source("enumeration"), ["ROLES", "EXPECTED_AXIOMS"])
        expected = frozenset(read["EXPECTED_AXIOMS"])  # type: ignore[arg-type]
        names = set(read["ROLES"])  # type: ignore[arg-type]
        authorities["enumeration"] = Authority(
            "enumeration",
            qualify(names),
            {LIDO_NAMESPACE + name: expected for name in names},
        )
    except (Unreadable, OSError, TypeError, AttributeError) as exc:
        problems.append(f"cannot read the enumeration gate's pin table: {exc}")

    # --- registry: resolves REQUIRED/EXPECTED_HEADERS; states an expectation
    # --- only for the four fixture controls in AXIOM_CONTROLS ---------------
    try:
        read = python_constants(
            source("registry"),
            ["REQUIRED", "EXPECTED_HEADERS", "AXIOM_CONTROLS", "EXPECTED_AXIOMS"],
        )
        expected = frozenset(read["EXPECTED_AXIOMS"])  # type: ignore[arg-type]
        names = set(read["EXPECTED_HEADERS"])  # type: ignore[arg-type]
        for required in read["REQUIRED"].values():  # type: ignore[union-attr]
            names |= set(required)
        resolves = qualify(names)
        expects = {}
        for control in read["AXIOM_CONTROLS"]:  # type: ignore[union-attr]
            qualified = control[1]
            resolves.add(qualified)
            expects[qualified] = expected
        authorities["registry"] = Authority("registry", resolves, expects)
    except (Unreadable, OSError, TypeError, AttributeError, IndexError) as exc:
        problems.append(f"cannot read the registry gate's pin table: {exc}")

    # --- history: the axiom population is DERIVED from its owner modules ----
    #
    # This authority states a per-name expectation for every public
    # theorem/lemma in its owners; it simply happens to be constant, and
    # carries no exception table because there are no exceptions. Its
    # population is therefore reproduced from the owner sources by the same
    # rule its probe uses, not read from `HEADER_PINS` -- that table is a
    # DIGEST population and includes the `def`/`structure` layer
    # (`RegistryStable`, `Coherent`, `registrySpec`), which is pinned by digest
    # and never probed. Those names stay RESOLUTION-ONLY, so the register may
    # keep citing them as premise vocabulary and may not put them in
    # **Declarations**.
    try:
        read = python_constants(
            source("history"), ["OWNERS", "STANDARD_AXIOMS", "HEADER_PINS"]
        )
        standard = frozenset(read["STANDARD_AXIOMS"])  # type: ignore[arg-type]
        owners = dict(read["OWNERS"])  # type: ignore[arg-type]
        chain = python_class_constants(
            source("history"), "ChainActivation", ["active", "key", "path"]
        )
        if chain["active"]:
            owners[str(chain["key"])] = str(chain["path"])

        probed: set[str] = set()
        for relative in sorted(owners.values()):
            owner_path = root / str(relative)
            if not owner_path.is_file():
                raise Unreadable(f"history owner {relative} is missing")
            probed |= lean_public_theorems(
                owner_path.read_text(encoding="utf-8")
            )

        if not probed:
            raise Unreadable(
                "history's owner modules yielded no public theorems; the "
                "declaration scan no longer matches"
            )

        digest_only: set[str] = set()
        for owner in read["HEADER_PINS"].values():  # type: ignore[union-attr]
            digest_only |= set(owner)

        authorities["history"] = Authority(
            "history",
            probed | qualify(digest_only),
            {name: standard for name in probed},
        )
    except (Unreadable, OSError, TypeError, AttributeError) as exc:
        problems.append(f"cannot read the history gate's pin table: {exc}")

    return authorities, problems


# Owner modules `--probe` must import that no readable constant carries.
# Empty today: the history gate's chain owner is read off `ChainActivation`
# and every other owner comes from a module table. Kept as the declared place
# for the next one rather than deleted.
PROBE_EXTRA_IMPORTS: tuple[str, ...] = ()


def probe_import_modules(root: pathlib.Path, axiom_check_text: str) -> list[str]:
    """The import union `--probe` needs to see every cited declaration.

    The register cites names from several families, and no single existing
    probe imports all of them: the repository audit's own import list covers the
    audited population, the access gate's `MODULES` covers the access/temporal
    family, and the history gate's `MODULES` plus `AXIOM_PROBE_IMPORTS` cover
    the Registry-history owners. Reusing only `scripts/AxiomCheck.lean`'s
    imports -- the obvious thing -- would leave every access-family name
    unresolvable, so the union is taken deliberately.

    Order is deterministic: the audit's imports first, in their own order, then
    the additions sorted, so a probe file is reproducible.
    """

    modules: list[str] = []
    seen: set[str] = set()

    def add(module: str) -> None:
        if module not in seen:
            seen.add(module)
            modules.append(module)

    for line in axiom_check_text.splitlines():
        if line.startswith("import "):
            add(line[len("import ") :].strip())

    extra: set[str] = set(PROBE_EXTRA_IMPORTS)
    for relative, wanted in (
        (AUTHORITY_SOURCE["access"], ["MODULES"]),
        (AUTHORITY_SOURCE["history"], ["MODULES", "AXIOM_PROBE_IMPORTS"]),
    ):
        try:
            read = python_constants(root / relative, wanted)
        except (Unreadable, OSError):
            continue
        for value in read.values():
            if isinstance(value, dict):
                extra |= {str(item) for item in value.values()}
            elif isinstance(value, (list, tuple, set)):
                extra |= {str(item) for item in value}
    try:
        chain = python_class_constants(
            root / AUTHORITY_SOURCE["history"],
            "ChainActivation",
            ["active", "module"],
        )
        if chain["active"]:
            extra.add(str(chain["module"]))
    except (Unreadable, OSError):
        pass
    for module in sorted(extra):
        add(module)
    return modules


def probe_axioms(
    root: pathlib.Path, names: list[str], axiom_check_text: str
) -> tuple[dict[str, list[str] | None], list[str]]:
    """`--probe`: ask Lean directly what the cited declarations depend on.

    Writes a temporary Lean file carrying the import union above followed by one
    `#print axioms` line per cited declaration, elaborates it with `lake env
    lean` from the repository root, and reports the axiom set per name (None
    where Lean reported none at all).

    The probe file lives in a real temporary directory, not in the repository:
    `lake env` only sets the environment, so `lean` finds the owners through
    LEAN_PATH and the file need not sit inside the package. Writing it into the
    tree would be one hard kill away from leaving a stray `.lean` behind that
    `lake` would then try to build.

    Requires the Lean toolchain and a built dependency graph. It is not the
    default mode and is not what CI runs.
    """

    problems: list[str] = []
    reports: dict[str, list[str] | None] = {}

    imports = probe_import_modules(root, axiom_check_text)
    if not imports:
        problems.append(
            f"{AXIOM_CHECK_RELATIVE}: no import lines to reuse; --probe cannot build "
            "an equivalent environment"
        )
        return reports, problems

    body = "\n".join(f"import {module}" for module in imports) + "\n\n"
    body += "\n".join(f"#print axioms {name}" for name in names) + "\n"

    with tempfile.TemporaryDirectory() as tmp:
        source = pathlib.Path(tmp) / "AssuranceProbe.lean"
        source.write_text(body, encoding="utf-8")
        try:
            completed = subprocess.run(
                ["lake", "env", "lean", str(source)],
                cwd=str(root),
                capture_output=True,
                text=True,
                check=False,
            )
        except OSError as exc:
            problems.append(f"--probe: could not run `lake env lean`: {exc}")
            return reports, problems

    output = (completed.stdout or "") + "\n" + (completed.stderr or "")
    if completed.returncode != 0:
        problems.append(
            f"--probe: `lake env lean` exited {completed.returncode}; "
            f"output follows:\n{output.strip()}"
        )
        return reports, problems
    if FORBIDDEN_AXIOMS.search(output):
        problems.append(
            "--probe: a forbidden axiom name appears in the Lean output "
            "(sorryAx / ofReduceBool / ofReduceNat / _native.)"
        )

    flat = re.sub(r"\s+", " ", output)
    for name in names:
        depends = re.search(
            re.escape(f"'{name}' depends on axioms:") + r"\s*\[(.*?)\]", flat
        )
        if depends is not None:
            reports[name] = [
                part.strip() for part in depends.group(1).split(",") if part.strip()
            ]
            continue
        if re.search(
            re.escape(f"'{name}' does not depend on any axioms"), flat
        ):
            reports[name] = None
            continue
        problems.append(
            f"--probe: Lean printed no axiom report for {name}. The usual cause is "
            "that the declaration's owner module is not in the probe's import union "
            f"({len(names)} names over {len(imports)} imports); add it to the "
            "authority's own module table, or to PROBE_EXTRA_IMPORTS here"
        )
    return reports, problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=None,
        help="repository root override; exists so a negative control can point "
        "the gate at a mutated copy of the tree",
    )
    parser.add_argument(
        "--probe",
        action="store_true",
        help="ALSO elaborate a generated `#print axioms` file for every cited "
        "declaration and compare Lean's answer against the register directly. "
        "Requires the Lean toolchain and a built dependency graph; not the "
        "default and not what CI runs.",
    )
    args = parser.parse_args()

    root = (
        pathlib.Path(args.root)
        if args.root
        else pathlib.Path(__file__).resolve().parent.parent
    )

    def regression(message: str) -> int:
        print(f"REGRESSION — {VERDICT_SUBJECT}: {message}", file=sys.stderr)
        return 2

    register_path = root / REGISTER_RELATIVE
    if not register_path.is_file():
        return regression(f"missing register {REGISTER_RELATIVE}")
    register_text = register_path.read_text(encoding="utf-8")

    axiom_check_path = root / AXIOM_CHECK_RELATIVE
    if not axiom_check_path.is_file():
        return regression(f"missing audit inventory {AXIOM_CHECK_RELATIVE}")
    axiom_check_text = axiom_check_path.read_text(encoding="utf-8")
    audited = set(PRINT_AXIOMS.findall(axiom_check_text))
    if not audited:
        return regression(
            f"{AXIOM_CHECK_RELATIVE} yielded zero `#print axioms` names; the "
            "producer pattern no longer matches"
        )

    pins_path = root / AXIOM_PINS_RELATIVE
    if not pins_path.is_file():
        return regression(f"missing axiom pins {AXIOM_PINS_RELATIVE}")
    pins, pin_problems = parse_axiom_pins(pins_path.read_text(encoding="utf-8"))
    if pin_problems:
        for problem in pin_problems:
            print(f"FAIL — {VERDICT_SUBJECT}: {problem}", file=sys.stderr)
        return regression(
            f"could not read the pinned axiom expectations out of {AXIOM_PINS_RELATIVE}"
        )

    catalogue_path = root / CATALOGUE_RELATIVE
    if not catalogue_path.is_file():
        return regression(f"missing gate catalogue {CATALOGUE_RELATIVE}")
    catalogue_text = catalogue_path.read_text(encoding="utf-8")

    rows, pillars, failures = parse_register(register_text)

    if not rows:
        for failure in failures:
            print(f"FAIL — {VERDICT_SUBJECT}: {failure}", file=sys.stderr)
        return regression(
            f"{REGISTER_RELATIVE} parsed to zero rows; a register with nothing in "
            "it can never be reported green"
        )

    # --- Channel 1: structure and anti-vacuity ------------------------------

    seen_rowids: dict[str, Register] = {}
    for row in rows:
        if row.rowid in seen_rowids:
            failures.append(
                f"{REGISTER_RELATIVE}:{row.line}: ROWID {row.rowid} is already used at "
                f"line {seen_rowids[row.rowid].line}"
            )
        else:
            seen_rowids[row.rowid] = row

        if row.field_order != FIELD_ORDER:
            missing = [f for f in FIELD_ORDER if f not in row.fields]
            unknown = [f for f in row.field_order if f not in FIELD_ORDER]
            detail = []
            if missing:
                detail.append("missing " + ", ".join(f"**{f}**" for f in missing))
            if unknown:
                detail.append("unknown " + ", ".join(f"**{f}**" for f in unknown))
            if not detail:
                detail.append(
                    "fields out of the frozen order: got "
                    + " / ".join(row.field_order)
                )
            failures.append(
                f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} — "
                + "; ".join(detail)
            )
        for label in FIELD_ORDER:
            if label in row.fields and not row.fields[label].strip():
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} has an empty "
                    f"**{label}** field"
                )

    per_pillar: dict[str, int] = {}
    for row in rows:
        per_pillar[row.pillar] = per_pillar.get(row.pillar, 0) + 1

    for pillar, expected in sorted(EXPECTED_ROWS_PER_PILLAR.items()):
        actual = per_pillar.get(pillar)
        if actual is None:
            failures.append(
                f"{REGISTER_RELATIVE}: pinned pillar {pillar!r} is absent, or carries "
                "no rows"
            )
        elif actual != expected:
            failures.append(
                f"{REGISTER_RELATIVE}: pillar {pillar!r} has {actual} row(s), pinned "
                f"at {expected}"
            )
    for pillar in pillars:
        if pillar not in EXPECTED_ROWS_PER_PILLAR:
            failures.append(
                f"{REGISTER_RELATIVE}: pillar {pillar!r} is not pinned in "
                "EXPECTED_ROWS_PER_PILLAR; add it deliberately rather than letting "
                "rows accumulate outside the count"
            )

    if len(rows) != EXPECTED_TOTAL_ROWS:
        failures.append(
            f"{REGISTER_RELATIVE}: {len(rows)} row(s), pinned at "
            f"{EXPECTED_TOTAL_ROWS}"
        )

    # --- Channels 2 and 3: declarations and axiom expectations --------------

    authorities, authority_problems = load_authorities(root, audited, pins)
    if authority_problems:
        for problem in authority_problems:
            print(f"FAIL — {VERDICT_SUBJECT}: {problem}", file=sys.stderr)
        return regression(
            "could not read one or more axiom-expectation authorities; this gate "
            "will not check a register against a pin table it could not read"
        )
    audit_authority = authorities[AUDIT_KEY]

    tree_names: set[str] | None = None
    declarations_checked = 0
    expectations_matched = 0
    gate_owned = 0
    resolved_by: dict[str, int] = {}
    probe_names: list[str] = []
    probe_expect: dict[str, tuple[str, list[str] | None]] = {}

    for row in rows:
        raw_declarations = clean_field(row.fields.get("Declarations", ""))
        raw_axioms = clean_field(row.fields.get("Axioms", ""))
        if not raw_declarations:
            continue

        is_gate_owned = raw_declarations == GATE_OWNED_DECLARATIONS
        mentions_literal = "gate-owned row" in raw_declarations.lower()
        if mentions_literal and not is_gate_owned:
            failures.append(
                f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} mixes the gate-owned "
                f"literal with other text in **Declarations**: {raw_declarations!r}. "
                f"A row is either exactly `{GATE_OWNED_DECLARATIONS}` or a list of "
                "audited names, never both"
            )
            continue

        if is_gate_owned:
            gate_owned += 1
            if raw_axioms != GATE_OWNED_AXIOMS:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: gate-owned row {row.rowid} has "
                    f"**Axioms** {raw_axioms!r}; a gate-owned row must write exactly "
                    f"`{GATE_OWNED_AXIOMS}`"
                )
            continue

        if raw_axioms == GATE_OWNED_AXIOMS:
            failures.append(
                f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} writes **Axioms** "
                f"`{GATE_OWNED_AXIOMS}` but cites declarations; only a gate-owned row "
                "may decline the axiom check"
            )
            continue

        names = [part.strip() for part in raw_declarations.split(",") if part.strip()]
        if not names:
            failures.append(
                f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} has no readable name "
                "in **Declarations**"
            )
            continue

        expected_axioms: set[str] | None
        if raw_axioms.lower() == NO_AXIOMS_WORD:
            expected_axioms = set()
        else:
            expected_axioms = {
                part.strip() for part in raw_axioms.split(",") if part.strip()
            }
            if not expected_axioms:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} has an "
                    "unreadable **Axioms** field; write a comma-separated axiom list "
                    f"or the single word `{NO_AXIOMS_WORD}`"
                )
                continue

        # The row's own **Gate** field names the authority that must pin its
        # declarations. That is what makes the field load-bearing rather than
        # decorative, and it is why a row's evidence owner cannot drift away
        # from the theorems it claims to own.
        row_gates = [
            part.strip()
            for part in clean_field(row.fields.get("Gate", "")).split(",")
            if part.strip()
        ]
        row_authorities = [
            authorities[AUTHORITY_BY_GATE[gate]]
            for gate in row_gates
            if gate in AUTHORITY_BY_GATE and AUTHORITY_BY_GATE[gate] in authorities
        ]

        for name in names:
            declarations_checked += 1

            if not DECL_NAME.match(name):
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites "
                    f"{name!r}, which is not a declaration name"
                )
                continue
            if "." not in name:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name!r}, "
                    "which is not fully qualified; short names are ambiguous across "
                    "contracts and this gate matches only fully qualified names"
                )
                continue

            # --- Channel 2: does the row's own authority pin this name? -----
            if not row_authorities:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name} but "
                    f"its **Gate** field ({', '.join(row_gates) or 'empty'}) names no "
                    "axiom-expectation authority. A row may cite declarations only "
                    "under a gate that pins them — "
                    f"{', '.join(sorted(AUTHORITY_BY_GATE))} — otherwise it is a "
                    "gate-owned row"
                )
                continue

            resolving = [a for a in row_authorities if name in a.resolves]
            authority = resolving[0] if resolving else None
            if authority is None:
                if tree_names is None:
                    tree_names = resolve_tree(root)
                pinned_elsewhere = sorted(
                    other.key
                    for other in authorities.values()
                    if name in other.resolves
                )
                if pinned_elsewhere:
                    detail = (
                        "it is pinned by the "
                        + "/".join(pinned_elsewhere)
                        + " authority instead, so either the row names the wrong gate "
                        "or it cites the wrong declaration"
                    )
                elif name in tree_names:
                    detail = (
                        "it exists in Blanc's sources but no gate pins it, so it has "
                        "no checked axiom expectation. Cite it in **Premises** prose, "
                        "or make this a gate-owned row"
                    )
                else:
                    detail = (
                        "it does not resolve anywhere in Blanc's sources — check the "
                        "spelling and the namespace"
                    )
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name}, "
                    f"which gate {', '.join(row_gates)} does not pin: {detail}"
                )
                continue

            # --- Channel 3: the authority's expectation for this name -------
            #
            # A row may name several gates -- the one that owns its evidence
            # and the one that pins its axioms. Where more than one of them
            # states an expectation for this name, ALL of them must agree; a
            # first-match-wins rule would let a row that named two authorities
            # quietly select the more permissive of them.
            stated = {
                other.key: other.expects[name]
                for other in resolving
                if name in other.expects
            }
            if len(set(stated.values())) > 1:
                failures.append(
                    f"REPOSITORY INCONSISTENCY: row {row.rowid} names gates whose "
                    f"authorities disagree about {name} — "
                    + "; ".join(
                        f"{key} [{', '.join(sorted(value)) or 'none'}]"
                        for key, value in sorted(stated.items())
                    )
                    + ". This gate will not resolve the disagreement in either "
                    "direction"
                )
                continue

            pinned_frozen = next(iter(stated.values())) if stated else None
            source_key = (
                next(iter(sorted(stated))) if stated else authority.key
            )
            if pinned_frozen is None:
                # An authority that pins the name but states no expectation
                # sends the row to the repository audit.
                if name in audit_authority.expects:
                    pinned_frozen = audit_authority.expects[name]
                    source_key = AUDIT_KEY
                elif name in audit_authority.resolves:
                    failures.append(
                        f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name}, "
                        f"which is audited but has no pinned expectation in "
                        f"{AXIOM_PINS_RELATIVE}'s ROWS table; an unpinned name is a "
                        "gap, not a row this gate may skip"
                    )
                    continue
                else:
                    failures.append(
                        f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name}. "
                        f"Gate {', '.join(row_gates)} pins the name but states no "
                        "axiom expectation for it, and the repository audit does not "
                        "carry it either. Move the name into **Premises** prose, or "
                        "make this a gate-owned row"
                    )
                    continue

            # Two authorities pinning one name must agree with each other.
            if (
                source_key != AUDIT_KEY
                and name in audit_authority.expects
                and audit_authority.expects[name] != pinned_frozen
            ):
                failures.append(
                    f"REPOSITORY INCONSISTENCY: {name} is pinned by both the "
                    f"{source_key} authority [{', '.join(sorted(pinned_frozen)) or 'none'}] "
                    f"and {AXIOM_PINS_RELATIVE} "
                    f"[{', '.join(sorted(audit_authority.expects[name])) or 'none'}]. "
                    f"Row {row.rowid} cannot be checked until the two gates agree; "
                    "this gate will not resolve the disagreement in either direction"
                )
                continue

            pinned = set(pinned_frozen)
            if pinned != expected_axioms:
                if not pinned:
                    detail = (
                        f"the {source_key} authority pins no axioms at all, so the "
                        f"register must write the single word `{NO_AXIOMS_WORD}`; it "
                        f"writes [{', '.join(sorted(expected_axioms))}]"
                    )
                elif not expected_axioms:
                    detail = (
                        f"the register writes `{NO_AXIOMS_WORD}` but the "
                        f"{source_key} authority pins "
                        f"[{', '.join(sorted(pinned))}]"
                    )
                else:
                    extra = sorted(expected_axioms - pinned)
                    missing = sorted(pinned - expected_axioms)
                    detail = (
                        f"register [{', '.join(sorted(expected_axioms))}] vs "
                        f"{source_key} authority [{', '.join(sorted(pinned))}]"
                    )
                    if extra:
                        detail += "; register claims: " + " ".join(extra)
                    if missing:
                        detail += "; register omits: " + " ".join(missing)
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} — axiom "
                    f"expectation for {name} disagrees: {detail}"
                )
                continue

            expectations_matched += 1
            resolved_by[authority.key] = resolved_by.get(authority.key, 0) + 1
            if name not in probe_expect:
                probe_names.append(name)
                probe_expect[name] = (
                    row.rowid,
                    None if not expected_axioms else sorted(expected_axioms),
                )

    if gate_owned != EXPECTED_GATE_OWNED_ROWS:
        failures.append(
            f"{REGISTER_RELATIVE}: {gate_owned} gate-owned row(s), pinned at "
            f"{EXPECTED_GATE_OWNED_ROWS}. A normal row converted into a gate-owned "
            "one stops being axiom-checked, so this count is part of the contract"
        )

    # --- Channel 4: gate existence and registration -------------------------

    gates_checked = 0
    multi_gate_rows = 0
    for row in rows:
        raw_gates = clean_field(row.fields.get("Gate", ""))
        if not raw_gates:
            continue
        named = [part.strip() for part in raw_gates.split(",") if part.strip()]
        if len(named) > 1:
            multi_gate_rows += 1
        for gate in named:
            gates_checked += 1
            if not (root / gate).is_file():
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} names gate "
                    f"{gate}, which does not exist under the repository root"
                )
                continue
            if gate not in catalogue_text:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} names gate "
                    f"{gate}, which exists but is not catalogued in "
                    f"{CATALOGUE_RELATIVE}"
                )

    if multi_gate_rows != EXPECTED_MULTI_GATE_ROWS:
        failures.append(
            f"{REGISTER_RELATIVE}: {multi_gate_rows} row(s) name more than one gate, "
            f"pinned at {EXPECTED_MULTI_GATE_ROWS}. A second gate name is the one "
            "edit that can rescue a mis-attributed declaration by giving it another "
            "authority to resolve against, so this count is part of the contract"
        )

    # --- Channel 5: non-claim coverage --------------------------------------

    flat_register = squeeze(register_text).lower()
    phrases_present = 0
    for phrase in NONCLAIM_PHRASES:
        if squeeze(phrase).lower() in flat_register:
            phrases_present += 1
        else:
            failures.append(
                f"{REGISTER_RELATIVE}: pinned non-claim phrase is gone — {phrase!r}. "
                "A non-claim that stops being written is a claim that quietly widened; "
                "restore the sentence, or retire the phrase here deliberately"
            )

    # --- optional probe -----------------------------------------------------

    probed = 0
    if args.probe:
        print(
            "note: --probe elaborates Lean. The DEFAULT mode is static and derives "
            "its authority over the axiom column from the gates that own the pin "
            f"tables — `{AXIOM_PINS_RELATIVE} --no-build` and the Lido family "
            "gates — each of which verifies its own expectations against Lean."
        )
        # The registry gate's four axiom pins are declarations in fixture FILES
        # (`scripts/LidoCircuitBreaker*.lean`), which it probes by appending to a
        # copy of the fixture rather than by importing a module. There is no
        # module to import here, so --probe cannot reach them and says so rather
        # than reporting a missing report as a disagreement.
        fixture_only = sorted(
            name
            for name in probe_names
            if name in authorities["registry"].expects
        )
        if fixture_only:
            print(
                "note: --probe cannot reach "
                + ", ".join(fixture_only)
                + " — the registry gate pins these in fixture files, not in an "
                "importable module; the static check above still covers them."
            )
        probe_names = [name for name in probe_names if name not in fixture_only]
        reports, probe_problems = probe_axioms(root, probe_names, axiom_check_text)
        failures.extend(probe_problems)
        for name in probe_names:
            if name not in reports:
                continue
            rowid, expected = probe_expect[name]
            actual = reports[name]
            actual_set = set(actual or [])
            expected_set = set(expected or [])
            if actual_set == expected_set:
                probed += 1
                print(f"  ok  {rowid} {name}: {', '.join(sorted(actual_set)) or 'none'}")
            else:
                failures.append(
                    f"--probe: row {rowid} — Lean reports "
                    f"[{', '.join(sorted(actual_set)) or 'none'}] for {name}; the "
                    f"register writes [{', '.join(sorted(expected_set)) or 'none'}]"
                )

    # --- verdict ------------------------------------------------------------

    breakdown = ", ".join(
        f"{count} {key}" for key, count in sorted(resolved_by.items())
    )
    summary = (
        f"{len(rows)} rows across {len(pillars)} pillars, "
        f"{gate_owned} gate-owned row(s), {multi_gate_rows} multi-gate row(s), "
        f"{declarations_checked} declarations resolved"
        + (f" ({breakdown})" if breakdown else "")
        + f", {expectations_matched} axiom expectations matched, "
        f"{gates_checked} gate paths registered, "
        f"{phrases_present}/{len(NONCLAIM_PHRASES)} non-claim phrases present"
    )
    if args.probe:
        summary += f", {probed} declarations probed against Lean"

    if failures:
        for failure in failures:
            print(f"FAIL — {VERDICT_SUBJECT}: {failure}", file=sys.stderr)
        print(
            f"REGRESSION — {VERDICT_SUBJECT}: {len(failures)} failure(s) over "
            f"{summary}",
            file=sys.stderr,
        )
        return 1

    print(f"OK — {VERDICT_SUBJECT}: {summary}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
