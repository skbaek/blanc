#!/usr/bin/env python3
"""Fail-closed assurance gate for the proxy-pair upgrade goal.

The gate owns four coupled surfaces: the ten product headline names, three
closed/composed assurance theorems, their kernel axiom sets, the public
claim/non-claim document, and the exact executable success/failure rows.
`--self-test` applies isolated disposable mutations to the checked surfaces
and requires each one to fail at its intended boundary.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SUBJECT = "proxy-pair-upgrade"
DEFAULT_ROOT = Path(__file__).resolve().parents[1]

PRODUCTION = (
    "Blanc/Upgrade.lean",
    "Blanc/ProxyPairUpgradePrograms.lean",
    "Blanc/ProxyPairUpgradeRelation.lean",
    "Blanc/ProxyPairUpgradeExecution.lean",
    "Blanc/ProxyPairUpgradeRefinement.lean",
)

CONFIGURED_FIXTURES = (
    "Blanc/ProxyPairUpgradeExecution.lean",
    "Blanc/ProxyPairUpgradeRefinement.lean",
    "Blanc/ProxyPairOssifiableDeploymentFixture.lean",
    "Blanc/ProxyPairOssifiableBothSlotFixture.lean",
    "Blanc/ProxyPairOssifiableBothSlotDeployment.lean",
)

SUPPORT = (
    "Blanc.lean",
    "docs/PROXY_PAIR_UPGRADE.md",
    "scripts/check-layering.py",
    "scripts/ProxyPairUpgradeWitness.lean",
    "scripts/ProxyPairUpgradeAxiomCheck.lean",
)

HEADLINES = {
    "migration_establishes_initializedDomain": "Blanc/ProxyPairUpgradeRelation.lean",
    "migration_sound": "Blanc/ProxyPairUpgradeRelation.lean",
    "shared_getter_refinement": "Blanc/ProxyPairUpgradeRelation.lean",
    "shared_setter_refinement": "Blanc/ProxyPairUpgradeRelation.lean",
    "upgradeToAndCall_primary_realizes_migration": "Blanc/ProxyPairUpgradeExecution.lean",
    "upgradeTo_realizes_identity": "Blanc/ProxyPairUpgradeExecution.lean",
    "upgradeToAndCall_skipped_empty_realizes_identity": "Blanc/ProxyPairUpgradeExecution.lean",
    "upgradeTo_identity_sound_of_admissible": "Blanc/ProxyPairUpgradeExecution.lean",
    "throughProxy_primary_refinement": "Blanc/ProxyPairUpgradeRefinement.lean",
    "throughProxy_identity_refinement_of_admissible": "Blanc/ProxyPairUpgradeRefinement.lean",
}

ASSURANCE = {
    "fixture_exactProxyPairSharedExecution_value": "Blanc/ProxyPairUpgradeRefinement.lean",
    "fixture_throughProxy_value_refinement": "Blanc/ProxyPairUpgradeRefinement.lean",
    "upgradeToAndCall_primary_throughProxy_refinement": "Blanc/ProxyPairUpgradeRefinement.lean",
}

GENERIC = {
    "UpgradeArchitecture": "structure",
    "MigrationSound": "def",
    "BehavioralRefinement": "def",
}

FULL_HEADLINES = tuple(f"Blanc.ProxyPair.Upgrade.{name}" for name in HEADLINES)
FULL_ASSURANCE = tuple(f"Blanc.ProxyPair.Upgrade.{name}" for name in ASSURANCE)
FULL_AXIOM_PINS = FULL_HEADLINES + FULL_ASSURANCE
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED_WITNESS = (
    "PRIMARY|wrapper=ok|error=false|gas=4941998|implementation=720899|s1=42|s2=42|marker=1|logs=1|output=0",
    "UPGRADE_TO|wrapper=ok|error=false|gas=4988830|implementation=720899|s1=42|s2=0|marker=0|logs=1|output=0",
    "SKIPPED_EMPTY|wrapper=ok|error=false|gas=4988532|implementation=720899|s1=42|s2=0|marker=0|logs=1|output=0",
    "UNAUTHORIZED|wrapper=ok|error=true|gas=4997323|implementation=720898|s1=42|s2=0|marker=0|logs=0|output=4",
    "OSSIFIED|wrapper=ok|error=true|gas=4997340|implementation=720898|s1=42|s2=0|marker=0|logs=0|output=4",
    "MISSING_CODE|wrapper=ok|error=true|gas=4994661|implementation=720898|s1=42|s2=0|marker=0|logs=0|output=132",
    "REVERTING_SETUP|wrapper=ok|error=true|gas=77856|implementation=720898|s1=42|s2=0|marker=0|logs=1|output=132",
    "RELATION|ordinary-identity-admissible=false|primary-initialized=true|primary-r2=true|wrong-r2=false",
    "POST_VALUE|wrapper=ok|error=false|gas=4992892|implementation=720899|s1=42|s2=42|marker=1|logs=0|output=32|word=42",
    "POST_SET|wrapper=ok|error=false|gas=4989974|implementation=720899|s1=42|s2=73|marker=1|logs=0|output=0|word=0",
    "POST_GET|wrapper=ok|error=false|gas=4992892|implementation=720899|s1=42|s2=73|marker=1|logs=0|output=32|word=73",
    "POST_MARKER|wrapper=ok|error=false|gas=4992831|implementation=720899|s1=42|s2=42|marker=1|logs=0|output=32|word=1",
)

CLAIM_TOKENS = (
    "authorized execution of the exact compiled Blanc OssifiableProxy",
    "forceCall = false",
    "proxy-owned storage",
    "DirectTargetTransport",
    "G-5 forwarded-child-budget premise",
    "identity-admissibility premise",
    "Migration soundness and behavioral refinement are separate conclusions",
    "not full-surface R1",
    "not invariant-only R3",
    "does not verify deployed Solidity",
    "not a theorem about arbitrary proxies",
    "Forced-empty setup and redeploy-and-migrate are not product migration routes",
    "GAS-sensitive compatibility claim",
    "scripts/check-proxy-pair-upgrade.sh",
    "fixture_exactProxyPairSharedExecution_value",
    "upgradeToAndCall_primary_throughProxy_refinement",
    "persistent and transient state roll back",
    "returned error machine retains the raw setup log observation",
)

STATIC_FRAGMENTS = {
    "PROGRAM": (
        ("Blanc/ProxyPairUpgradePrograms.lean", "def valueSelector : B256 := 0x3fa4f245"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "def setValueSelector : B256 := 0x55241077"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "def initializeV2Selector : B256 := 0x5cd8a76b"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "def migrationMarkerSelector : B256 := 0x8d8a346e"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "def v1ValueSlot : B256 := 7"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "def v2ValueSlot : B256 := 8"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "def migrationMarkerSlot : B256 := 9"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "theorem scalarSlots_erc1967_separated"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "theorem v1Bytes_length : v1Bytes.length = 74"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "theorem v2Bytes_length : v2Bytes.length = 141"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "theorem v1_v2_code_ne"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "theorem v2_shared_entries_exact"),
        ("Blanc/ProxyPairUpgradePrograms.lean", "theorem marker_selector_new_surface"),
    ),
    "RELATION": (
        ("Blanc/ProxyPairUpgradeRelation.lean", "def upgradeRelation (proxy : Adr) (pre post : State) : Prop :=\n  storageWord pre proxy v1ValueSlot =\n    storageWord post proxy v2ValueSlot"),
        ("Blanc/ProxyPairUpgradeRelation.lean", "theorem relation_inhabited"),
        ("Blanc/ProxyPairUpgradeRelation.lean", "theorem ordinary_not_identityAdmissible"),
        ("Blanc/ProxyPairUpgradeRelation.lean", "theorem wrong_relation_mutant_bites"),
        ("Blanc/ProxyPairUpgradeRelation.lean", "theorem relation_does_not_protect_marker"),
    ),
    "EXECUTION": (
        ("Blanc/ProxyPairUpgradeExecution.lean", "(proxyProg : Prog) (hproxy : proxyProg = runtimeBaseline)"),
        ("Blanc/ProxyPairUpgradeExecution.lean", "(hv1Installed : storedImplementationWord entry sevm.currentTarget =\n      v1Implementation.toB256)"),
        ("Blanc/ProxyPairUpgradeExecution.lean", "(hv2Code : entry.getCode v2Implementation = v2Code)"),
        ("Blanc/ProxyPairUpgradeExecution.lean", "spawn.child.data = initializeV2Calldata"),
        ("Blanc/ProxyPairUpgradeExecution.lean", "UpgradeToAndCallDelegateBoundary"),
    ),
    "FORWARDING": (
        ("Blanc/ProxyPairUpgradeRefinement.lean", "owner : msg.currentTarget = upgradeProxy"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "spawn.child.depth = outer.depth - 1"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "calculateMsgCallGas 0 spawn.gasWord.toNat"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "ForwardingTailBudget spawnV1 childV1"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "routeV1.transportObligation"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "ScalarInputWord (Bytes.toB256 outerV1.data)"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "Prog.RunCompiledTo (initSevm spawn.child)"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "theorem fixture_exactProxyPairSharedExecution_value"),
        ("Blanc/ProxyPairUpgradeRefinement.lean", "theorem upgradeToAndCall_primary_throughProxy_refinement"),
    ),
}

FORBIDDEN = re.compile(
    r"\b(?:sorry|native_decide|axiom|unsafe|partial)\b|"
    r"set_option\s+(?:maxHeartbeats|maxRecDepth)"
)


def read(root: Path, relative: str, errors: list[str]) -> str:
    path = root / relative
    try:
        return path.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(f"FILES — cannot read {relative}: {exc}")
        return ""


def normalized(text: str) -> str:
    return " ".join(text.split())


def static_errors(root: Path) -> list[str]:
    errors: list[str] = []
    paths = tuple(dict.fromkeys(PRODUCTION + CONFIGURED_FIXTURES + SUPPORT))
    texts = {path: read(root, path, errors) for path in paths}
    if errors:
        return errors

    upgrade = texts["Blanc/Upgrade.lean"]
    for name, kind in GENERIC.items():
        pattern = re.compile(rf"^\s*{kind}\s+{re.escape(name)}\b", re.MULTILINE)
        if len(pattern.findall(upgrade)) != 1:
            errors.append(f"GENERIC — expected exactly one {kind} Blanc.{name}")
        for path in PRODUCTION[1:]:
            if re.search(rf"^\s*(?:def|structure|theorem)\s+{re.escape(name)}\b", texts[path], re.MULTILINE):
                errors.append(f"PLACEMENT — generic {name} is duplicated in {path}")
    if "ProxyPair" in upgrade or "runtimeBaseline" in upgrade:
        errors.append("PLACEMENT — shared Upgrade.lean contains product vocabulary")

    product_text = "\n".join(texts[path] for path in PRODUCTION[1:])
    for name, owner in HEADLINES.items():
        found = re.findall(rf"^\s*theorem\s+{re.escape(name)}\b", product_text, re.MULTILINE)
        if len(found) != 1:
            errors.append(f"HEADLINE — expected exactly one theorem {name}")
        if not re.search(rf"^\s*theorem\s+{re.escape(name)}\b", texts[owner], re.MULTILINE):
            errors.append(f"HEADLINE — {name} is not owned by {owner}")
    for name, owner in ASSURANCE.items():
        found = re.findall(rf"^\s*theorem\s+{re.escape(name)}\b", product_text, re.MULTILINE)
        if len(found) != 1:
            errors.append(f"ASSURANCE — expected exactly one theorem {name}")
        if not re.search(rf"^\s*theorem\s+{re.escape(name)}\b", texts[owner], re.MULTILINE):
            errors.append(f"ASSURANCE — {name} is not owned by {owner}")

    for code, relative, name in (
        ("PROGRAM", "Blanc/ProxyPairUpgradePrograms.lean", "v1_v2_code_ne"),
        ("RELATION", "Blanc/ProxyPairUpgradeRelation.lean", "relation_inhabited"),
        ("RELATION", "Blanc/ProxyPairUpgradeRelation.lean", "ordinary_not_identityAdmissible"),
        ("RELATION", "Blanc/ProxyPairUpgradeRelation.lean", "wrong_relation_mutant_bites"),
    ):
        if not re.search(rf"^\s*theorem\s+{re.escape(name)}\b", texts[relative], re.MULTILINE):
            errors.append(f"{code} — required theorem {name} is missing from {relative}")

    root_imports = texts["Blanc.lean"]
    for module in ("Upgrade", "ProxyPairUpgradePrograms", "ProxyPairUpgradeRelation",
                   "ProxyPairUpgradeExecution", "ProxyPairUpgradeRefinement"):
        line = f"import Blanc.{module}"
        if root_imports.splitlines().count(line) != 1:
            errors.append(f"ROOT — expected exactly one root import {line}")

    layering = texts["scripts/check-layering.py"]
    if '"Ladder", "Upgrade"' not in layering:
        errors.append("PLACEMENT — Upgrade is not classified as shared")
    for module in ("ProxyPairUpgradePrograms", "ProxyPairUpgradeRelation",
                   "ProxyPairUpgradeExecution", "ProxyPairUpgradeRefinement"):
        if layering.count(f'"{module}"') != 1:
            errors.append(f"PLACEMENT — {module} is not classified exactly once")

    for code, requirements in STATIC_FRAGMENTS.items():
        for relative, fragment in requirements:
            if normalized(fragment) not in normalized(texts[relative]):
                errors.append(f"{code} — required surface is missing from {relative}: {normalized(fragment)}")

    execution = texts["Blanc/ProxyPairUpgradeExecution.lean"]
    for fragment, expected in (
        ("(proxyProg : Prog) (hproxy : proxyProg = runtimeBaseline)", 3),
        ("(hv2Code : entry.getCode v2Implementation = v2Code)", 3),
    ):
        if execution.count(fragment) != expected:
            errors.append(f"EXECUTION — expected {expected} exact occurrences of {fragment}")
    refinement = texts["Blanc/ProxyPairUpgradeRefinement.lean"]
    if refinement.count("owner : msg.currentTarget = upgradeProxy") != 2:
        errors.append("FORWARDING — both implementation children must name upgradeProxy as storage owner")
    for structure in ("V1SharedChildExecution", "V2SharedChildExecution"):
        match = re.search(
            rf"structure\s+{structure}\b(.*?)(?=\n(?:structure|theorem|def)\s)",
            refinement,
            re.DOTALL,
        )
        if match is None:
            errors.append(f"FORWARDING — cannot inspect {structure}")
            continue
        fields = match.group(1)
        for required in ("initialStorage :", "run : Prog.RunCompiledTo",
                         "certificate : DelegatedChildCertificate",
                         "clean : child.error.isSome = false"):
            if required not in fields:
                errors.append(f"FORWARDING — {structure} is missing derived-run field {required}")
        for forbidden in ("output :", "postStorage :", "initialState :"):
            if forbidden in fields:
                errors.append(f"FORWARDING — {structure} stores forbidden certificate field {forbidden}")

    configured_fragments = (
        ("Blanc/ProxyPairUpgradeExecution.lean",
         "def fixtureBenv (rules : ForkRules)"),
        ("Blanc/ProxyPairOssifiableDeploymentFixture.lean",
         "theorem message_success (rules : ForkRules)"),
        ("Blanc/ProxyPairOssifiableBothSlotFixture.lean",
         "theorem message_success (rules : ForkRules)"),
        ("Blanc/ProxyPairOssifiableBothSlotDeployment.lean",
         "theorem creationMessage_success (rules : ForkRules)"),
        ("Blanc/ProxyPairUpgradeRefinement.lean",
         "theorem fixture_exactProxyPairSharedExecution_value (rules : ForkRules)"),
        ("Blanc/ProxyPairUpgradeRefinement.lean",
         "proxyNotPrecompile : ¬rules.isPrecomp upgradeProxy"),
        ("Blanc/ProxyPairUpgradeRefinement.lean",
         "rules.isPrecomp v1Implementation = false"),
        ("Blanc/ProxyPairUpgradeRefinement.lean",
         "rules.isPrecomp v2Implementation = false"),
    )
    for relative in CONFIGURED_FIXTURES:
        if "pragueRules" in texts[relative]:
            errors.append(
                f"CONFIGURATION — named Prague rules remain in {relative}")
    for relative, fragment in configured_fragments:
        if normalized(fragment) not in normalized(texts[relative]):
            errors.append(
                f"CONFIGURATION — explicit selected-rule surface is missing "
                f"from {relative}: {normalized(fragment)}")

    doc = texts["docs/PROXY_PAIR_UPGRADE.md"]
    for token in CLAIM_TOKENS:
        if normalized(token).lower() not in normalized(doc).lower():
            errors.append(f"CLAIM — public evidence is missing: {token}")
    for name in HEADLINES | ASSURANCE:
        if doc.count(f"`{name}`") < 1:
            errors.append(f"CLAIM — public evidence does not cite {name}")

    probe = texts["scripts/ProxyPairUpgradeAxiomCheck.lean"]
    for full_name in FULL_AXIOM_PINS:
        if probe.splitlines().count(f"#print axioms {full_name}") != 1:
            errors.append(f"AXIOM — expected one probe row for {full_name}")

    witness = texts["scripts/ProxyPairUpgradeWitness.lean"]
    if witness.count("pragueRules") != 1 or (
            "private abbrev rules : ForkRules := pragueRules" not in witness):
        errors.append(
            "WITNESS — expected one explicit Prague specialization boundary")
    for label in ("PRIMARY", "UPGRADE_TO", "SKIPPED_EMPTY", "UNAUTHORIZED",
                  "OSSIFIED", "MISSING_CODE", "REVERTING_SETUP",
                  "POST_VALUE", "POST_SET", "POST_GET", "POST_MARKER"):
        if witness.count(f'"{label}"') != 1:
            errors.append(f"WITNESS — expected exactly one evaluator label {label}")
    if witness.count('"RELATION|') != 2:
        errors.append("WITNESS — expected the two exhaustive evaluator branches for RELATION")

    for relative in tuple(dict.fromkeys(PRODUCTION + CONFIGURED_FIXTURES)):
        for match in FORBIDDEN.finditer(texts[relative]):
            line = texts[relative].count("\n", 0, match.start()) + 1
            errors.append(f"TRUST — forbidden token {match.group(0)!r} at {relative}:{line}")
    return errors


def run_lean(root: Path, relative: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", relative], cwd=root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def parse_axioms(output: str) -> dict[str, set[str]]:
    rows: dict[str, set[str]] = {}
    pattern = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)
    for name, payload in pattern.findall(output):
        rows[name] = {part.strip() for part in payload.replace("\n", " ").split(",") if part.strip()}
    return rows


def dynamic_errors(root: Path) -> list[str]:
    errors: list[str] = []
    axiom = run_lean(root, "scripts/ProxyPairUpgradeAxiomCheck.lean")
    if axiom.returncode != 0:
        errors.append(f"AXIOM — probe failed with exit {axiom.returncode}:\n{axiom.stdout.rstrip()}")
    else:
        rows = parse_axioms(axiom.stdout)
        if set(rows) != set(FULL_AXIOM_PINS):
            errors.append("AXIOM — probe output does not contain exactly the 13 pinned rows")
        for name in FULL_AXIOM_PINS:
            if rows.get(name) != EXPECTED_AXIOMS:
                errors.append(f"AXIOM — {name} uses {sorted(rows.get(name, set()))}, expected {sorted(EXPECTED_AXIOMS)}")

    witness = run_lean(root, "scripts/ProxyPairUpgradeWitness.lean")
    if witness.returncode != 0:
        errors.append(f"WITNESS — evaluator failed with exit {witness.returncode}:\n{witness.stdout.rstrip()}")
    else:
        rows = tuple(line.strip() for line in witness.stdout.splitlines() if line.strip())
        if rows != EXPECTED_WITNESS:
            errors.append("WITNESS — exact executable rows drifted\nexpected:\n  " +
                          "\n  ".join(EXPECTED_WITNESS) + "\nactual:\n  " + "\n  ".join(rows))
    return errors


def run_layering(root: Path) -> list[str]:
    process = subprocess.run(
        ["scripts/check-layering.sh"], cwd=root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    if process.returncode != 0:
        return [f"PLACEMENT — layering gate failed:\n{process.stdout.rstrip()}"]
    return []


def copy_static_tree(source: Path, target: Path) -> None:
    for relative in tuple(dict.fromkeys(PRODUCTION + CONFIGURED_FIXTURES + SUPPORT)):
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / relative, destination)


def self_test(root: Path) -> list[str]:
    failures: list[str] = []
    mutations = (
        ("wrong-headline", "Blanc/ProxyPairUpgradeRelation.lean", "theorem migration_sound", "theorem migration_sound_MUTANT", "HEADLINE"),
        ("wrong-proxy", "Blanc/ProxyPairUpgradeExecution.lean", "hproxy : proxyProg = runtimeBaseline", "hproxy : proxyProg = v1Prog", "EXECUTION"),
        ("wrong-installed-code", "Blanc/ProxyPairUpgradeExecution.lean", "entry.getCode v2Implementation = v2Code", "entry.getCode v2Implementation = v1Code", "EXECUTION"),
        ("v1-equals-v2", "Blanc/ProxyPairUpgradePrograms.lean", "theorem v1_v2_code_ne", "theorem v1_v2_code_ne_MUTANT", "PROGRAM"),
        ("unsatisfiable-relation", "Blanc/ProxyPairUpgradeRelation.lean", "theorem relation_inhabited", "theorem relation_inhabited_MUTANT", "RELATION"),
        ("wrong-r2", "Blanc/ProxyPairUpgradeRelation.lean", "storageWord post proxy v2ValueSlot", "storageWord post proxy migrationMarkerSlot", "RELATION"),
        ("false-admissibility-control", "Blanc/ProxyPairUpgradeRelation.lean", "theorem ordinary_not_identityAdmissible", "theorem ordinary_not_identityAdmissible_MUTANT", "RELATION"),
        ("owner-mismatch", "Blanc/ProxyPairUpgradeRefinement.lean", "owner : msg.currentTarget = upgradeProxy", "owner : msg.currentTarget = v1Implementation", "FORWARDING"),
        ("depth-budget", "Blanc/ProxyPairUpgradeRefinement.lean", "spawn.child.depth = outer.depth - 1", "spawn.child.depth = outer.depth", "FORWARDING"),
        ("tail-budget", "Blanc/ProxyPairUpgradeRefinement.lean", "ForwardingTailBudget spawnV1 childV1", "True", "FORWARDING"),
        ("uninhabited-exact-pair", "Blanc/ProxyPairUpgradeRefinement.lean", "theorem fixture_exactProxyPairSharedExecution_value", "theorem fixture_exactProxyPairSharedExecution_value_MUTANT", "ASSURANCE"),
        ("missing-primary-composition", "Blanc/ProxyPairUpgradeRefinement.lean", "theorem upgradeToAndCall_primary_throughProxy_refinement", "theorem upgradeToAndCall_primary_throughProxy_refinement_MUTANT", "ASSURANCE"),
        ("detached-child-run", "Blanc/ProxyPairUpgradeRefinement.lean", "Prog.RunCompiledTo (initSevm spawn.child)", "Prog.RunCompiledTo (initSevm fixtureV1ValueChildMessage)", "FORWARDING"),
        ("stored-output-certificate", "Blanc/ProxyPairUpgradeRefinement.lean", "initialStorage : MessageStorageEqualAt", "output : MessageStorageEqualAt", "FORWARDING"),
        ("named-fork-regression", "Blanc/ProxyPairUpgradeExecution.lean", "fixtureBenv rules", "fixtureBenv pragueRules", "CONFIGURATION"),
        ("disabled-rollback", "scripts/ProxyPairUpgradeWitness.lean", '"REVERTING_SETUP"', '"DISABLED_SETUP"', "WITNESS"),
        ("disabled-post-value", "scripts/ProxyPairUpgradeWitness.lean", '"POST_VALUE"', '"DISABLED_POST_VALUE"', "WITNESS"),
        ("disabled-post-marker", "scripts/ProxyPairUpgradeWitness.lean", '"POST_MARKER"', '"DISABLED_POST_MARKER"', "WITNESS"),
        ("missing-root-import", "Blanc.lean", "import Blanc.ProxyPairUpgradeRefinement", "-- removed import", "ROOT"),
        ("generic-misplacement", "scripts/check-layering.py", '"Ladder", "Upgrade"', '"Ladder", "Upgrade_MUTANT"', "PLACEMENT"),
        ("stale-evidence", "docs/PROXY_PAIR_UPGRADE.md", "not full-surface R1", "full surface", "CLAIM"),
        ("missing-marker-effect", "Blanc/ProxyPairUpgradePrograms.lean", "def migrationMarkerSlot : B256 := 9", "def migrationMarkerSlot : B256 := 10", "PROGRAM"),
    )
    with tempfile.TemporaryDirectory(prefix="proxy-pair-upgrade-self-test-") as raw:
        target = Path(raw)
        copy_static_tree(root, target)
        if static_errors(target):
            failures.append("self-test baseline static copy is not green")
            return failures
        for label, relative, old, new, expected in mutations:
            path = target / relative
            original = path.read_text(encoding="utf-8")
            if original.count(old) < 1:
                failures.append(f"{label}: mutation anchor is absent")
                continue
            path.write_text(original.replace(old, new, 1), encoding="utf-8")
            found = static_errors(target)
            path.write_text(original, encoding="utf-8")
            if not any(error.startswith(expected + " —") for error in found):
                failures.append(f"{label}: expected {expected} failure, got {found}")

        empty = target / "wrong-root"
        empty.mkdir()
        if not any(error.startswith("FILES —") for error in static_errors(empty)):
            failures.append("wrong-root: absent checkout did not fail closed")

        fake = "\n".join(
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for name in FULL_AXIOM_PINS
        ).replace("[propext, Classical.choice, Quot.sound]", "[propext]", 1)
        parsed = parse_axioms(fake)
        if all(parsed.get(name) == EXPECTED_AXIOMS for name in FULL_AXIOM_PINS):
            failures.append("wrong-axiom: reduced axiom set was not distinguished")
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    phase = parser.add_mutually_exclusive_group()
    phase.add_argument("--static-only", action="store_true")
    phase.add_argument("--semantic-only", action="store_true")
    parser.add_argument("--composed-prerequisites", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()

    errors = [] if args.semantic_only else static_errors(root)
    if not args.static_only:
        if not args.composed_prerequisites:
            errors.extend(run_layering(root))
        errors.extend(dynamic_errors(root))
    if args.self_test and not errors:
        errors.extend(f"CONTROL — {item}" for item in self_test(root))

    if errors:
        for error in errors:
            print(f"FAIL — {SUBJECT}: {error}")
        print(f"REGRESSION — {SUBJECT}: {len(errors)} failure(s)")
        return 1
    suffix = "; 24 disposable controls bite" if args.self_test else ""
    if args.static_only:
        print(f"OK — {SUBJECT} static: 10 headlines, 3 assurance theorems, 3 generic definitions{suffix}")
    elif args.semantic_only:
        print(f"OK — {SUBJECT} semantic: 13 axiom pins, 12 exact witness rows{suffix}")
    else:
        print(f"OK — {SUBJECT}: 10 headlines, 3 assurance theorems, 3 generic definitions, 13 axiom pins, 12 exact witness rows{suffix}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
