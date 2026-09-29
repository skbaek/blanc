#!/usr/bin/env python3
"""End-to-end assurance-register gate for Blanc's Lido CircuitBreaker port.

`LIDO_CIRCUIT_BREAKER_ASSURANCE.md` is the one document licensed to say, for
each sentence a reader might quote, which declaration makes it true, which
axioms that declaration leans on, which gate owns the evidence, which
differential channel corroborates it, and where the claim stops. A register
like that is only worth its ink while every one of those columns is still true
of the tree. Prose does not re-derive itself, so a register drifts silently the
moment a declaration is renamed, an axiom claim moves, a gate is retired, or a
non-claim is quietly edited out of a row -- and a register that has drifted is
worse than none, because it is read as authority.

This gate closes that class. It reads the register and requires five things,
each fail-closed:

  1. Structure and anti-vacuity. Every `####` row under a `## Pillar —`
     heading carries all seven labelled fields, exactly once each, in the
     frozen order, non-empty; ROWIDs are unique; every pinned pillar is
     present; and the per-pillar row counts, the total and the number of
     gate-owned rows all equal the numbers pinned in this file. A row deleted,
     renamed, or reworded out of this gate's sight FAILS rather than shrinking
     a green count -- the anti-vacuity contract `check-doc-counts.py` states
     for quotations, restated for rows. The gate-owned count pins the escape
     hatch: a row can decline the axiom check by becoming gate-owned.

  2. Declaration resolution. Every name in a **Declarations** field must still
     resolve to a public declaration written in Blanc's sources (or, for the
     four Registry fixture controls, in the two Registry fixtures), spelled
     FULLY QUALIFIED: `Blanc.Weth10.canonicalDeploymentStep_establishes_root`
     and `Blanc.LidoCircuitBreaker.canonicalDeploymentStep_establishes_root`
     are different theorems sharing a last component, and a checker matching on
     the short name would credit a citation no gate ever made. The resolver is
     `scripts/axiom_audit.py`'s lexical `declared_names`, a namespace-stack scan
     of the sources; it never elaborates Lean.

  3. Axiom-expectation agreement. There is one authority: the repository's
     union axiom walk (`scripts/check.sh`, `scripts/AxiomCheck.lean`), which
     bounds the axioms of EVERY Blanc constant by `propext`, `Classical.choice`
     and `Quot.sound`. The register's **Axioms** field must therefore be that
     standard triple, except for a declaration that `scripts/AxiomCheck.lean`
     explicitly claims a smaller set for (`#expect_axioms`, checked in both
     directions by the same walker), where it must equal that claim exactly. An
     empty claim is written as the single word `none`. Conversely every
     stricter claim in `scripts/AxiomCheck.lean` must be stated by a row here or
     be one of the five frozen deployment names of
     `scripts/check-lido-circuit-breaker-deployment.py`: a smaller set that no
     register or gate states is not kept.

  4. Gate existence and registration. Every path in a **Gate** field exists
     under the repository root and is catalogued in `scripts/GATES.md`.

  5. Non-claim coverage. Every load-bearing non-claim phrase pinned below
     still appears somewhere in the register. Non-claims are the half of an
     assurance argument that erodes without anyone deciding to erode it.

WHAT THIS GATE DOES NOT OWN
---------------------------

It does not elaborate Lean and does not re-derive any axiom set. Its authority
over the axiom column is the audit source it reads; `scripts/check.sh` verifies
that source against Lean by elaborating, and this gate makes the register
faithful to it. Neither substitutes for the other, and this gate is not
evidence that any theorem holds.

It does not check that a row's prose is a fair summary of its declaration, that
the **Premises** field is complete, or that a **Differential channel** name
corresponds to a real oracle case. Those are review obligations, not
mechanically checkable ones, and pretending otherwise would be the vacuity this
gate exists to prevent.

It owns only this repository's tree, following `scripts/GATES.md`'s rule that a
gate lives in the repository whose tree it checks. Its checked claim map is
`LIDO_CIRCUIT_BREAKER_ASSURANCE.md`; whether each row's prose fairly summarizes
its declaration remains the repository-local review obligation stated above.

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
import sys

import axiom_audit

VERDICT_SUBJECT = "lido-circuit-breaker-assurance"

REGISTER_RELATIVE = "LIDO_CIRCUIT_BREAKER_ASSURANCE.md"
AXIOM_CHECK_RELATIVE = "scripts/AxiomCheck.lean"
DEPLOYMENT_RELATIVE = "scripts/check-lido-circuit-breaker-deployment.py"
FIXTURES_RELATIVE = (
    "scripts/LidoCircuitBreakerRegistrySuccess.lean",
    "scripts/LidoCircuitBreakerRegistryRegression.lean",
)
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
    "Temporal authority": 10,
    "Single-use pause": 5,
    "External-call honesty": 4,
    "Hostile-world results (Stage 6)": 5,
    "Deployment and history": 13,
    "Artifact conformance and cost": 4,
    "Pinned-target composition (entry 3)": 4,
}

# The total is pinned SEPARATELY from the per-pillar map rather than derived
# from it. Deriving it would let a single edit move a row between pillars and a
# matching edit here keep the gate green with no total to disagree with; two
# independent pins have to be falsified together.
EXPECTED_TOTAL_ROWS = 75

# Rows whose Declarations field is the gate-owned literal. Pinned so the
# escape hatch cannot widen quietly: convert one normal row and this fails.
EXPECTED_GATE_OWNED_ROWS = 9

# Load-bearing non-claims. Each must still appear somewhere in the register.
# Matched case-insensitively against the register with all whitespace runs
# collapsed to single spaces, so a phrase may span a line wrap and re-wrapping
# the file is not a failure. Each phrase is chosen to carry the substance of
# its non-claim rather than a heading, so a narrowing edit cannot delete the
# claim's limit and accidentally leave the phrase behind.
# Clauses of the registration-chronology shared-shape paragraph.
#
# That paragraph is the ONLY statement of six rows' common premises: each of
# those rows says "the shared registration shape above, plus ..." and lists only
# what it adds. So the paragraph carries more weight than any single row, and
# its three counts -- all six, five of six, four of six -- are exactly the kind
# of fact that goes stale silently when a seventh chronology lands or an
# existing one gains a premise. Nothing else in this gate would notice.
#
# Pinned here for the same reason the non-claim phrases below are pinned: a
# statement that six rows depend on must not be one edit away from being lost.
# Adding a chronology means updating the counts here in the same commit as the
# row, which is the deliberate act; editing them to clear a red gate is Rule 1.
SHARED_SHAPE_CLAUSES = [
    "**All six** take the exact message target",
    "**Five of six** — all but the fresh-registration chronology",
    "**Four of six** — all but the two *replacement* chronologies",
    "**All six** additionally take **warm**-slot premises",
]

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
    # The two configured TWG worlds are reachable, but no universal liveness or
    # all-world gas claim follows.
    "no universal liveness or all-world gas claim",
    # Mid-callback count/expiry incoherence is real source behaviour.
    "no callback-time count/expiry coherence",
    # Finite evidence corroborates; it is never a Lean premise.
    "finite replay and differential evidence are never Lean premises",
    # The synthetic satisfying world is an anti-vacuity exhibit, not a
    # deployment.
    "the synthetic stable world receives no deployment credit",
    # The BPO2 lane replays rules against closed fixtures; it does not inspect
    # current chain roles or state.
    "not a live-chain role/state attestation",
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

# A cited name must be fully qualified; see the module docstring.
DECL_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_.?'!]*$")

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


# --- the one axiom authority -------------------------------------------------

STANDARD_AXIOMS = frozenset(axiom_audit.STANDARD_AXIOMS)


class Unreadable(Exception):
    """A constant in another gate's source this reader will not guess at."""


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


def deployment_frozen_names(root: pathlib.Path) -> set[str]:
    """The five deployment names whose smaller axiom sets the deployment gate freezes.

    Read with `ast` from that gate's own source, never imported: the table is
    `STRICTER_CLAIMS` in `scripts/check-lido-circuit-breaker-deployment.py`.
    """

    read = python_constants(root / DEPLOYMENT_RELATIVE, ["STRICTER_CLAIMS"])
    return set(read["STRICTER_CLAIMS"])  # type: ignore[arg-type]


def evaluate(
    root: pathlib.Path,
    register_text: str,
    catalogue_text: str,
    stricter: dict,
    frozen_deployment: set,
    declared: dict,
) -> tuple[list[str], str]:
    """Every channel over one register text: (failures, summary)."""

    rows, pillars, failures = parse_register(register_text)

    if not rows:
        return failures + [
            f"{REGISTER_RELATIVE} parsed to zero rows; a register with nothing in "
            "it can never be reported green"
        ], ""

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

    declarations_checked = 0
    expectations_matched = 0
    gate_owned = 0
    stated_stricter: set[str] = set()

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

        expected_axioms: set[str]
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

            # --- Channel 2: the name still resolves, spelled in full --------
            found = declared.get(name)
            if found is None:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name}, "
                    "which does not resolve to a declaration in Blanc's sources — "
                    "check the spelling and the namespace"
                )
                continue
            if found[1]:
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} cites {name}, "
                    "which is private; a register may cite only public declarations"
                )
                continue

            # --- Channel 3: the one authority's expectation for this name ---
            claim = stricter.get(name)
            authority = set(claim) if claim is not None else set(STANDARD_AXIOMS)
            if expected_axioms != authority:
                where = (
                    f"the stricter claim in {AXIOM_CHECK_RELATIVE}"
                    if claim is not None
                    else f"the union axiom walk's bound (no stricter claim for it in "
                    f"{AXIOM_CHECK_RELATIVE})"
                )
                failures.append(
                    f"{REGISTER_RELATIVE}:{row.line}: row {row.rowid} — axiom "
                    f"expectation for {name} disagrees: register "
                    f"[{', '.join(sorted(expected_axioms)) or NO_AXIOMS_WORD}] vs {where} "
                    f"[{', '.join(sorted(authority)) or NO_AXIOMS_WORD}]"
                )
                continue
            if claim is not None:
                stated_stricter.add(name)
            expectations_matched += 1

    # Every stricter claim must be stated by a row above or frozen by the deployment
    # gate: a smaller axiom set that nothing states is not kept.
    for name in sorted(set(stricter) - stated_stricter - frozen_deployment):
        failures.append(
            f"{AXIOM_CHECK_RELATIVE}: the stricter axiom claim for {name} is stated by no "
            f"register row and is not one of the deployment gate's frozen names; drop it "
            "(the union walk already bounds it) or state it"
        )

    if gate_owned != EXPECTED_GATE_OWNED_ROWS:
        failures.append(
            f"{REGISTER_RELATIVE}: {gate_owned} gate-owned row(s), pinned at "
            f"{EXPECTED_GATE_OWNED_ROWS}. A normal row converted into a gate-owned "
            "one stops being axiom-checked, so this count is part of the contract"
        )

    # --- Channel 4: gate existence and registration -------------------------

    gates_checked = 0
    for row in rows:
        raw_gates = clean_field(row.fields.get("Gate", ""))
        if not raw_gates:
            continue
        named = [part.strip() for part in raw_gates.split(",") if part.strip()]
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

    # --- Channel 5: non-claim coverage --------------------------------------

    flat_register = squeeze(register_text).lower()
    phrases_present = 0
    shape_present = 0
    for clause in SHARED_SHAPE_CLAUSES:
        if squeeze(clause).lower() in flat_register:
            shape_present += 1
        else:
            failures.append(
                f"{REGISTER_RELATIVE}: pinned shared-shape clause is gone — {clause!r}. "
                "Six rows state their premises as additions to that paragraph, so a "
                "clause that stops being written silently removes premises from all "
                "six; restore it, or re-pin here deliberately in the same commit as "
                "the row that changed the shape"
            )

    for phrase in NONCLAIM_PHRASES:
        if squeeze(phrase).lower() in flat_register:
            phrases_present += 1
        else:
            failures.append(
                f"{REGISTER_RELATIVE}: pinned non-claim phrase is gone — {phrase!r}. "
                "A non-claim that stops being written is a claim that quietly widened; "
                "restore the sentence, or retire the phrase here deliberately"
            )

    # --- verdict ------------------------------------------------------------

    summary = (
        f"{len(rows)} rows across {len(pillars)} pillars, "
        f"{gate_owned} gate-owned row(s), "
        f"{declarations_checked} declarations resolved, "
        f"{expectations_matched} axiom expectations matched ({len(stricter)} stricter "
        f"claims), "
        f"{gates_checked} gate paths registered, "
        f"{phrases_present}/{len(NONCLAIM_PHRASES)} non-claim phrases present, "
        f"{shape_present}/{len(SHARED_SHAPE_CLAUSES)} shared-shape clauses present"
    )

    return failures, summary


SELF_TEST_CASES = 5


def self_test(
    root: pathlib.Path,
    register_text: str,
    catalogue_text: str,
    stricter: dict,
    frozen_deployment: set,
    declared: dict,
) -> list[str]:
    """In-memory mutants of the register and of the stricter claims; each must FAIL here."""

    problems: list[str] = []

    def rejected(label: str, expect: str, register: str, claims: dict) -> None:
        failures, _ = evaluate(
            root, register, catalogue_text, claims, frozen_deployment, declared
        )
        if not any(expect in failure for failure in failures):
            problems.append(f"{label}: expected a failure mentioning {expect!r}, got {failures[:2]}")

    cited = "Blanc.LidoCircuitBreaker.RegistryWitness.entries_length_le"
    if cited not in register_text:
        problems.append(f"the self-test's cited declaration {cited} is no longer in the register")
    rejected("misspelled declaration", "does not resolve",
             register_text.replace(cited, cited + "_typo", 1), stricter)
    rejected("unqualified declaration", "not fully qualified",
             register_text.replace(cited, "entries_length_le", 1), stricter)
    standard_row = "- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`"
    rejected("wrong axiom field", "axiom expectation",
             register_text.replace(standard_row, "- **Axioms:** `propext`, `Classical.choice`", 1),
             stricter)
    claim = "Blanc.LidoCircuitBreaker.emptyWitness"
    weakened = dict(stricter)
    weakened[claim] = frozenset({"propext"})
    rejected("stricter claim moved away from the register", "axiom expectation", register_text,
             weakened)
    orphan = dict(stricter)
    orphan["Blanc.LidoCircuitBreaker.RegistryWitness.entries_length_le"] = frozenset({"propext"})
    rejected("stricter claim stated by nothing", "stated by no register row", register_text,
             orphan)
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=None,
        help="repository root override; exists so a negative control can point "
        "the gate at a mutated copy of the tree",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="ALSO run the in-memory mutation controls: a misspelled declaration, an "
        "unqualified one, a wrong axiom field, a stricter claim moved away from the "
        "register and an orphan stricter claim must each be rejected",
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
        return regression(f"missing audit source {AXIOM_CHECK_RELATIVE}")
    try:
        stricter = axiom_audit.stricter_claims(root, AXIOM_CHECK_RELATIVE)
    except axiom_audit.AuditError as exc:
        return regression(f"{AXIOM_CHECK_RELATIVE} is not a valid audit source: {exc}")
    try:
        frozen_deployment = deployment_frozen_names(root)
    except (Unreadable, OSError, TypeError, AttributeError) as exc:
        return regression(f"cannot read the deployment gate's frozen claims: {exc}")
    try:
        declared = axiom_audit.declared_names(root, FIXTURES_RELATIVE)
    except axiom_audit.AuditError as exc:
        return regression(f"cannot scan Blanc's sources for declarations: {exc}")

    catalogue_path = root / CATALOGUE_RELATIVE
    if not catalogue_path.is_file():
        return regression(f"missing gate catalogue {CATALOGUE_RELATIVE}")
    catalogue_text = catalogue_path.read_text(encoding="utf-8")

    failures, summary = evaluate(
        root, register_text, catalogue_text, stricter, frozen_deployment, declared
    )
    if args.self_test:
        problems = self_test(
            root, register_text, catalogue_text, stricter, frozen_deployment, declared
        )
        failures = failures + [f"self-test: {problem}" for problem in problems]
        summary += f", {SELF_TEST_CASES} mutation controls"
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
