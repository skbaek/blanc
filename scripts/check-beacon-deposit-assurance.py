#!/usr/bin/env python3
"""Fail-closed checker for BEACON_DEPOSIT_ASSURANCE.md.

The register is a claim index, not an independent theorem authority.  This
checker therefore resolves every cited declaration through the repository's
existing axiom audit (`scripts/AxiomCheck.lean` plus `scripts/check.sh`) and
requires the register's axiom column to agree with that audit exactly.  It also
pins the protected row population, owning gates, and load-bearing non-claims.

Default operation is static and writes nothing.  `--self-test` additionally
runs the required misspelled-declaration and wrong-axiom mutants in memory.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from pathlib import Path
import re
import sys


SUBJECT = "beacon-deposit-assurance"
REGISTER = "BEACON_DEPOSIT_ASSURANCE.md"
AXIOM_CHECK = "scripts/AxiomCheck.lean"
AXIOM_PINS = "scripts/check.sh"
CATALOGUE = "scripts/GATES.md"

FIELD_ORDER = [
    "Declarations",
    "Premises",
    "Axioms",
    "Gate",
    "Differential channel",
    "Non-claims",
    "Source",
]

# Anti-vacuity pins.  These are deliberately independent of the Markdown.
EXPECTED_ROWS = {
    "Opening model": ["OPEN-1"],
    "Compiled port": ["P1", "P2", "P3", "P4", "P5", "P6"],
    "Deployment and open history": ["P7", "P8-FRAME", "P8-HISTORY", "P8-READ"],
}

EXPECTED_DECLARATIONS = {
    "OPEN-1": [
        "Blanc.BeaconDeposit.root_correct",
        "Blanc.BeaconDeposit.deposit_ok_spec",
        "Blanc.BeaconDeposit.deposit_inv",
    ],
    "P1": [
        "Blanc.BeaconDeposit.code_compile",
        "Blanc.BeaconDeposit.code_eip170",
        "Blanc.BeaconDeposit.constructorInitPrefix_compile",
        "Blanc.BeaconDeposit.creationCode_eip3860",
    ],
    "P2": [
        "Blanc.BeaconDeposit.deposit_success_settled_effects",
        "Blanc.BeaconDeposit.deposit_success_retainedStorageEffectTriples",
    ],
    "P3": [
        "Blanc.BeaconDeposit.deposit_ne_assert_false",
        "Blanc.BeaconDeposit.deposit_error_runCompiledTo",
        "Blanc.BeaconDeposit.deposit_malformed_noRawSstore",
        "Blanc.BeaconDeposit.unmatched_selector_noRawSstore",
    ],
    "P4": [
        "Blanc.BeaconDeposit.supportsInterface_runCompiled_noRawSstore",
        "Blanc.BeaconDeposit.getDepositRoot_zero_runCompiled_noRawSstore",
        "Blanc.BeaconDeposit.getDepositCount_warm_runCompiled_noRawSstore",
    ],
    "P5": [
        "Blanc.BeaconDeposit.Exec.NinstOccurrence.beaconRuntime_sstore_pc_of_rawFrameRoot",
        "Blanc.BeaconDeposit.Exec.Deriv.beaconConstructor_sstore_coordinate",
        "Blanc.BeaconDeposit.constructor_success_retainedStorageEffectTriples",
    ],
    "P6": [
        "Blanc.BeaconDeposit.constructorFinalStorage_artifactInv",
        "Blanc.BeaconDeposit.deposit_success_artifactInv",
        "Blanc.BeaconDeposit.ArtifactInv.root_eq_mixedRootOf",
        "Blanc.BeaconDeposit.ArtifactInv.count_eq_history_length",
    ],
    "P7": [
        "Blanc.BeaconDeposit.canonicalDeploymentStep_establishes_root",
        "Blanc.BeaconDeposit.DeploymentRoot.constructorOccurrence",
    ],
    "P8-FRAME": [
        "Blanc.BeaconDeposit.historySpec_sound",
        "Blanc.BeaconDeposit.historySpec_preserves",
    ],
    "P8-HISTORY": [
        "Blanc.BeaconDeposit.pragueOnly_history_extends",
        "Blanc.BeaconDeposit.DeploymentRoot.future_history_extends",
    ],
    "P8-READ": [
        "Blanc.BeaconDeposit.DeploymentRoot.future_count_root",
    ],
}

EXPECTED_GATES = {
    "OPEN-1": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-model.sh",
    ],
    "P1": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-differential.sh",
        "scripts/check-beacon-deposit-current-mainnet.sh",
    ],
    "P2": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-differential.sh",
    ],
    "P3": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-differential.sh",
    ],
    "P4": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-differential.sh",
    ],
    "P5": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-differential.sh",
    ],
    "P6": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-differential.sh",
    ],
    "P7": [
        "scripts/check.sh",
        "scripts/check-claims.sh",
        "scripts/check-beacon-deposit-deployment.sh",
    ],
    "P8-FRAME": ["scripts/check.sh", "scripts/check-claims.sh"],
    "P8-HISTORY": ["scripts/check.sh", "scripts/check-claims.sh"],
    "P8-READ": ["scripts/check.sh", "scripts/check-claims.sh"],
}

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_TOTAL_ROWS = 11
EXPECTED_TOTAL_DECLARATIONS = 30

NONCLAIM_PHRASES = [
    "different artifacts and independent proof developments",
    "not a verification claim about the deployed r2 bytecode",
    "no hash injectivity or collision freedom",
    "finite evidence is not a universal theorem",
    "direct singleton zero-value type-2 create",
    "not transaction-indexed or unique",
    "no universal liveness claim",
    "no create2, factory, proxy, or nonzero-endowment deployment",
]

ROW_RE = re.compile(r"^#### ([A-Z0-9-]+) — (\S.*)$")
PILLAR_RE = re.compile(r"^## Pillar — (\S.*)$")
FIELD_RE = re.compile(r"^- \*\*(%s):\*\*\s*(.*)$" % "|".join(map(re.escape, FIELD_ORDER)))
ANY_FIELD_RE = re.compile(r"^- \*\*([^*]+):\*\*")
FQ_DECL_RE = re.compile(r"^Blanc(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")


@dataclass
class Row:
    row_id: str
    claim: str
    pillar: str
    line: int
    fields: dict[str, str] = field(default_factory=dict)
    field_order: list[str] = field(default_factory=list)


def norm(text: str) -> str:
    return " ".join(text.lower().split())


def code_spans(text: str) -> list[str]:
    return re.findall(r"`([^`]+)`", text)


def parse_register(text: str) -> tuple[list[Row], list[str], list[str]]:
    rows: list[Row] = []
    pillars: list[str] = []
    errors: list[str] = []
    current_pillar: str | None = None
    current: Row | None = None
    current_field: str | None = None

    def finish() -> None:
        nonlocal current, current_field
        if current is not None:
            rows.append(current)
        current = None
        current_field = None

    for line_no, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip()
        pillar_match = PILLAR_RE.match(line)
        if pillar_match:
            finish()
            current_pillar = pillar_match.group(1).strip()
            pillars.append(current_pillar)
            continue

        row_match = ROW_RE.match(line)
        if row_match:
            finish()
            if current_pillar is None:
                errors.append(f"line {line_no}: row appears before a pillar")
                current_pillar = "<missing>"
            current = Row(
                row_id=row_match.group(1),
                claim=row_match.group(2).strip(),
                pillar=current_pillar,
                line=line_no,
            )
            continue

        field_match = FIELD_RE.match(line)
        if field_match:
            if current is None:
                errors.append(f"line {line_no}: labelled field appears outside a row")
                continue
            label, value = field_match.groups()
            if label in current.fields:
                errors.append(f"{current.row_id}: duplicate {label} field")
            current.fields[label] = value.strip()
            current.field_order.append(label)
            current_field = label
            continue

        if ANY_FIELD_RE.match(line):
            errors.append(f"line {line_no}: unknown or malformed labelled field")
            continue

        if current is not None and current_field is not None and line.strip():
            # Markdown continuation text belongs to the current field until the
            # next labelled field or structural heading.
            current.fields[current_field] = (
                current.fields[current_field] + " " + line.strip()
            ).strip()

    finish()
    return rows, pillars, errors


def load_axiom_authority(root: Path) -> tuple[dict[str, set[str]], list[str]]:
    errors: list[str] = []
    axiom_path = root / AXIOM_CHECK
    pins_path = root / AXIOM_PINS
    try:
        axiom_text = axiom_path.read_text()
        pins_text = pins_path.read_text()
    except OSError as exc:
        return {}, [f"cannot read axiom authority: {exc}"]

    printed_list = re.findall(
        r"^#print axioms\s+([A-Za-z0-9_.'?]+)\s*$", axiom_text, re.MULTILINE
    )
    if len(printed_list) != len(set(printed_list)):
        errors.append("scripts/AxiomCheck.lean contains duplicate axiom probes")
    printed = set(printed_list)

    standard_match = re.search(r'^STANDARD="([^"]*)"$', pins_text, re.MULTILINE)
    start_marker = 'ROWS="\\\n'
    start = pins_text.find(start_marker)
    end = pins_text.find('"\n# Secondary net only:', start + len(start_marker))
    if standard_match is None or start < 0 or end < 0:
        return {}, errors + ["scripts/check.sh axiom table is unparseable"]
    standard = {part.strip() for part in standard_match.group(1).split(",") if part.strip()}
    if standard != STANDARD_AXIOMS:
        errors.append(
            "repository STANDARD axiom set drifted: " + ", ".join(sorted(standard))
        )

    pins: dict[str, set[str]] = {}
    block = pins_text[start + len(start_marker):end]
    for line_no, raw in enumerate(block.splitlines(), 1):
        if not raw:
            continue
        if "|" not in raw:
            errors.append(f"scripts/check.sh axiom row {line_no} is unparseable")
            continue
        name, expected = raw.split("|", 1)
        if name in pins:
            errors.append(f"scripts/check.sh duplicates axiom row {name}")
            continue
        if expected == "$STANDARD":
            axioms = set(standard)
        else:
            axioms = {part.strip() for part in expected.split(",") if part.strip()}
        pins[name] = axioms

    if set(pins) != printed:
        errors.append("scripts/AxiomCheck.lean and scripts/check.sh audited sets disagree")
    return pins, errors


def check_text(root: Path, text: str) -> tuple[list[str], dict[str, int]]:
    errors: list[str] = []
    if not text.strip():
        return ["register is empty"], {}

    rows, pillars, parse_errors = parse_register(text)
    errors.extend(parse_errors)
    authority, authority_errors = load_axiom_authority(root)
    errors.extend(authority_errors)
    catalogue_path = root / CATALOGUE
    try:
        catalogue = catalogue_path.read_text()
    except OSError as exc:
        catalogue = ""
        errors.append(f"cannot read gate catalogue: {exc}")

    expected_pillars = list(EXPECTED_ROWS)
    if pillars != expected_pillars:
        errors.append(f"pillar order/population drifted: got {pillars!r}")
    if len(rows) != EXPECTED_TOTAL_ROWS:
        errors.append(
            f"stale row count: expected {EXPECTED_TOTAL_ROWS}, found {len(rows)}"
        )

    actual_ids = [row.row_id for row in rows]
    expected_ids = [row_id for ids in EXPECTED_ROWS.values() for row_id in ids]
    if actual_ids != expected_ids:
        errors.append(f"row identity/order drifted: got {actual_ids!r}")
    if len(actual_ids) != len(set(actual_ids)):
        errors.append("duplicate row identifiers")

    by_pillar: dict[str, list[str]] = {}
    for row in rows:
        by_pillar.setdefault(row.pillar, []).append(row.row_id)
    for pillar, expected in EXPECTED_ROWS.items():
        if by_pillar.get(pillar, []) != expected:
            errors.append(
                f"{pillar}: stale row population; expected {expected!r}, "
                f"found {by_pillar.get(pillar, [])!r}"
            )

    seen_declarations: list[str] = []
    for row in rows:
        if not row.claim.strip():
            errors.append(f"{row.row_id}: empty claim heading")
        if row.field_order != FIELD_ORDER:
            errors.append(
                f"{row.row_id}: fields must appear exactly as {FIELD_ORDER!r}; "
                f"got {row.field_order!r}"
            )
        for label in FIELD_ORDER:
            if not row.fields.get(label, "").strip():
                errors.append(f"{row.row_id}: missing or empty {label} field")

        declarations = code_spans(row.fields.get("Declarations", ""))
        expected_declarations = EXPECTED_DECLARATIONS.get(row.row_id, [])
        if declarations != expected_declarations:
            errors.append(
                f"{row.row_id}: declaration population differs; expected "
                f"{expected_declarations!r}, found {declarations!r}"
            )
        for name in declarations:
            seen_declarations.append(name)
            if not FQ_DECL_RE.fullmatch(name):
                errors.append(f"{row.row_id}: declaration is not fully qualified: {name}")
            if name not in authority:
                errors.append(f"{row.row_id}: unresolved or unaudited declaration: {name}")

        axioms = set(code_spans(row.fields.get("Axioms", "")))
        if axioms != STANDARD_AXIOMS:
            errors.append(
                f"{row.row_id}: wrong axiom field; expected "
                f"{sorted(STANDARD_AXIOMS)!r}, found {sorted(axioms)!r}"
            )
        for name in declarations:
            if name in authority and authority[name] != axioms:
                errors.append(
                    f"{row.row_id}: axiom expectation for {name} disagrees with "
                    f"scripts/check.sh: register={sorted(axioms)!r}, "
                    f"authority={sorted(authority[name])!r}"
                )

        gates = code_spans(row.fields.get("Gate", ""))
        expected_gates = EXPECTED_GATES.get(row.row_id, [])
        if gates != expected_gates:
            errors.append(
                f"{row.row_id}: owning gates differ; expected {expected_gates!r}, "
                f"found {gates!r}"
            )
        for gate in gates:
            if not gate.startswith("scripts/") or not gate.endswith(".sh"):
                errors.append(f"{row.row_id}: malformed gate path: {gate}")
            elif not (root / gate).is_file():
                errors.append(f"{row.row_id}: gate path does not exist: {gate}")
            if f"`{gate}`" not in catalogue:
                errors.append(f"{row.row_id}: gate is not catalogued in {CATALOGUE}: {gate}")

    if len(seen_declarations) != EXPECTED_TOTAL_DECLARATIONS:
        errors.append(
            f"stale declaration count: expected {EXPECTED_TOTAL_DECLARATIONS}, "
            f"found {len(seen_declarations)}"
        )
    if len(seen_declarations) != len(set(seen_declarations)):
        errors.append("a declaration is credited by more than one assurance row")

    normalized = norm(text)
    for phrase in NONCLAIM_PHRASES:
        if norm(phrase) not in normalized:
            errors.append(f"load-bearing non-claim vanished: {phrase!r}")

    stats = {
        "rows": len(rows),
        "pillars": len(pillars),
        "declarations": len(seen_declarations),
        "nonclaims": len(NONCLAIM_PHRASES),
    }
    return errors, stats


def run_self_tests(root: Path, text: str) -> list[str]:
    failures: list[str] = []
    misspelled = text.replace(
        "Blanc.BeaconDeposit.root_correct",
        "Blanc.BeaconDeposit.root_correct_typo",
        1,
    )
    misspelled_errors, _ = check_text(root, misspelled)
    if not any(
        "declaration population differs" in error
        or "unresolved or unaudited declaration" in error
        for error in misspelled_errors
    ):
        failures.append("misspelled-declaration mutant was not rejected")

    good_axioms = "- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`"
    bad_axioms = "- **Axioms:** `propext`, `Classical.choice`, `Quot.sound_typo`"
    wrong_axiom = text.replace(good_axioms, bad_axioms, 1)
    wrong_axiom_errors, _ = check_text(root, wrong_axiom)
    if not any("wrong axiom field" in error for error in wrong_axiom_errors):
        failures.append("wrong-axiom mutant was not rejected")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent.parent
    register_path = root / REGISTER
    try:
        text = register_path.read_text()
    except OSError as exc:
        print(f"REGRESSION — {SUBJECT}: cannot read {REGISTER}: {exc}")
        return 1

    errors, stats = check_text(root, text)
    if errors:
        for error in errors:
            print(f"FAIL — {SUBJECT}: {error}")
        print(f"REGRESSION — {SUBJECT}: {len(errors)} failure(s)")
        return 1

    controls = 0
    if args.self_test:
        failures = run_self_tests(root, text)
        if failures:
            for failure in failures:
                print(f"FAIL — {SUBJECT}: {failure}")
            print(f"REGRESSION — {SUBJECT}: mutation controls failed")
            return 1
        controls = 2

    print(
        f"OK — {SUBJECT}: {stats['rows']} protected rows across "
        f"{stats['pillars']} pillars; {stats['declarations']} fully qualified "
        f"declarations with exact axiom/gate ownership; "
        f"{stats['nonclaims']} non-claim pins; {controls} mutation controls"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
