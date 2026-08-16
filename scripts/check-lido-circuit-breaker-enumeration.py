#!/usr/bin/env python3
"""Fail-closed local assurance for enumeration-observability S3 controls.

It owns the gate fixture, exact public-role headers, trust/deletion/mutation
controls, and exact axiom expectations for the landed S3 theorem family.
"""
from __future__ import annotations

import re
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OWNER = ROOT / "Blanc/LidoCircuitBreakerEnumeration.lean"
FIXTURE = ROOT / "scripts/LidoCircuitBreakerEnumerationControls.lean"
REQUIRED = (
    "exact_code_empty_control", "exact_code_singleton_control",
    "exact_code_sixty_four_control",
    "empty_image_control", "singleton_size_control", "sixtyFour_size_control",
    "sixtyFour_not_capped_at_one", "full_prefix_image_control",
    "cursor_not_memory_resident_control", "memory_resident_cursor_alias_rejected",
    "reachable_writer_rejected_control",
    "writer_certificate_rejected_control",
    "order_omission_duplication_and_truncation_rejected",
    "abi_header_size_and_padding_control",
    "unbounded_offset_needs_witness_bound",
    "noop_shaped_transitions_still_exist",
    "noop_event_omission_premise_rejected",
    "event_shape_mutants_rejected",
)
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|opaque|native_decide|implemented_by)\b")
ROLES = {
    "getPausables_runCompiled": "860917a14bb01c38221ef7a97c5da4247aa3453b877183eb60d5f5cdde83f0d3",
    "getPausables_noSstore_occurrence": "7729d8af3084bac2f1d5c1a145802b16d520cbca581a6d9d1fc120d072aed521",
    "registryViews_coherent": "2ccb5c749f4b2a56daca773c1430c172e20bf73fdd8e8e29c63c2559dd4b087d",
    "pauserSet_local_transition": "80d926b239cf4ac0df7414260d83a79ce2bc33702bdf3f96d566a0f1d1c7a42d",
    "pauserSet_target_zero_no_success": "5ddcaaebf789223390d7949699b0816c443500d35b49b67600743ba3831ba12d",
    "pauserSet_target_zero_error_logs_unchanged": "6fc80f773bfaad4c9a42e8cefef9c5951daa53f754d1a00cf94995cdc75a127e",
    "pauserSet_register_success": "322d07f5645ed20c12db9421d5dbf18f72e0d9245eca11b199771832bbf5fc34",
    "pauserSet_register_success_committed": "423931268008b2515cb862901f86cae9c17149c842f20a9b1223018207c01ecd",
    "pauserSet_settled_error_not_observable": "fc87de212f62e2e7eed74b6cefe6bd6cbeaa5e5b1f098c997f70b5543a5423b1",
    "registryObservation_sound": "76b2c05b54e1c0ea96cd846651290a27529e065331e2524c3e380ae2ee5b593e",
}
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def fail(message: str) -> None:
    raise SystemExit(f"REGRESSION — S3 enumeration assurance: {message}")

def text(path: Path) -> str:
    if not path.is_file():
        fail(f"missing required file {path.relative_to(ROOT)}")
    return path.read_text()

def require_controls(source: str) -> None:
    for name in REQUIRED:
        if not re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", source):
            fail(f"missing positive/deletion control {name}")
    for token in ("List.range 64", "exactCodeEnumerationRun",
                  "controlRegistryWitness", "enumLoop_pre_memory_independent_of_cursor",
                  "cursorAliasedSingletonMemory",
                  "enumeration_writing_mutant_rejected", "EntrySstoreFree",
                  "enumPrefixMemory_full_read"):
        if token not in source:
            fail(f"fixture no longer owns required semantic channel {token}")

def no_trust_shortcut(path: Path) -> None:
    match = FORBIDDEN.search(text(path))
    if match:
        fail(f"forbidden trust token {match.group(1)!r} in {path.relative_to(ROOT)}")

_DECL_START = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|example|class)\b")


def declaration_slice(source: str, name: str) -> str:
    """Exact source text of one declaration, never crossing into the next.

    The earlier `.*?:= by` form silently ran past a term-mode declaration and
    digested a blend of two theorems, so a pin could name one result and hash
    another.  Slicing first makes that impossible.
    """
    start = re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", source)
    if not start:
        fail(f"missing pinned public role {name}")
    rest = source[start.end():]
    following = _DECL_START.search(rest)
    end = start.end() + (following.start() if following else len(rest))
    return source[start.start():end]


def normalized_header(source: str, name: str) -> str:
    declaration = declaration_slice(source, name)
    tactic = re.search(r"(?s)^.*?:(?==\s*by\b)", declaration)
    if tactic:
        header = tactic.group(0)
    else:
        depth = 0
        cut = -1
        for index, char in enumerate(declaration):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == ":" and depth == 0 and declaration[index:index + 2] == ":=":
                cut = index
        if cut < 0:
            fail(f"pinned public role {name} has no definition marker")
        header = declaration[:cut + 1]
    return " ".join(header.split())


def pin_role_headers(source: str) -> None:
    for name, expected in ROLES.items():
        actual = hashlib.sha256(normalized_header(source, name).encode()).hexdigest()
        if actual != expected:
            fail(f"normalized public header changed for {name}")

def compile_fixture() -> None:
    olean = ROOT / ".lake/build/lib/lean/Blanc/LidoCircuitBreakerEnumeration.olean"
    if not olean.is_file():
        fail("compiled enumeration owner is absent; run the approved elaboration "
             "checkpoint before this fixture gate")
    run = subprocess.run(
        ["lake", "env", "lean", "scripts/LidoCircuitBreakerEnumerationControls.lean"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if run.returncode:
        fail("fixture failed to compile:\n" + run.stdout)

def axiom_checks() -> None:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="enumeration-axioms-", dir=ROOT,
        encoding="utf-8", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        handle.write("import Blanc.LidoCircuitBreakerEnumeration\n")
        for name in ROLES:
            handle.write(
                "#print axioms Blanc.LidoCircuitBreaker." + name + "\n"
            )
    try:
        run = subprocess.run(
            ["lake", "env", "lean", str(temporary.relative_to(ROOT))],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    finally:
        temporary.unlink(missing_ok=True)
    if run.returncode:
        fail("axiom probe failed:\n" + run.stdout)
    for name in ROLES:
        qualified = "Blanc.LidoCircuitBreaker." + name
        match = re.search(
            r"'" + re.escape(qualified) +
            r"' depends on axioms: \[([^\]]*)\]",
            run.stdout, re.DOTALL,
        )
        if not match:
            fail(f"{qualified}: unrecognised #print axioms output")
        actual = {
            item.strip() for item in match.group(1).split(",") if item.strip()
        }
        if actual != EXPECTED_AXIOMS:
            fail(
                f"{qualified}: axioms {sorted(actual)}, "
                f"expected {sorted(EXPECTED_AXIOMS)}"
            )

def deletion_control(source: str) -> None:
    # Mutate a required declaration name in a temporary copy: the parser must
    # reject it before any compiler result can make the gate vacuous.
    with tempfile.TemporaryDirectory() as td:
        mutant = Path(td) / "controls.lean"
        mutant.write_text(source.replace("empty_image_control", "removed_control", 1))
        mutated = mutant.read_text()
        if re.search(r"(?m)^theorem\s+empty_image_control\b", mutated):
            fail("deletion-control mutation did not apply")
        try:
            require_controls(mutated)
        except SystemExit:
            return
        fail("required-control deletion was accepted")

def header_mutation_controls(source: str) -> None:
    # Each mutation changes theorem-level semantics in a protected public role.
    mutations = {
        "fixed enumeration cap": (
            "    (G : Nat)\n    (hdata : sevm.data.length.toB256 = 4)",
            "    (G : Nat)\n    (_hcap : entries.length ≤ 64)\n"
            "    (hdata : sevm.data.length.toB256 = 4)",
        ),
        "wrong event identity": ("pauserSetEvent", "wrongPauserSetEvent"),
        "event before stable Registry boundary": (
            "settled.logs = postRegistry.logs ++",
            "postRegistry.logs = settled.logs ++",
        ),
        "wrong event topic order": (
            "[pauserSetEvent, target, assignmentAt entries target, newPauser]",
            "[pauserSetEvent, assignmentAt entries target, target, newPauser]",
        ),
        "missing no-op-shaped event coverage": (
            "    (hnew : canonicalAddress newPauser)\n"
            "    (hexec : Exec (loc + 1) sevm pre (.ok final)) :",
            "    (hnew : canonicalAddress newPauser)\n"
            "    (_hchanged : assignmentAt entries target ≠ newPauser)\n"
            "    (hexec : Exec (loc + 1) sevm pre (.ok final)) :",
        ),
        "foreign storage owner": (
            "Devm.getStor base sevm.currentTarget", "Devm.getStor base ca",
        ),
        "fixed code identity": (
            "lidoCircuitBreakerCode dp", "lidoCircuitBreakerCode officialParams",
        ),
        "rolled-back raw log treated as committed": (
            "    out.logs = [] ∧\n      RegistryWitness",
            "    out.logs = [⟨ca, [pauserSetEvent, target,\n"
            "        assignmentAt entries target, newPauser], []⟩] ∧\n"
            "      RegistryWitness",
        ),
        "witness arithmetic premise deleted": (
            "    (hw : RegistryWitness\n      (logicalStorageOfStor "
            "(Devm.getStor base sevm.currentTarget)) entries)",
            "    (_hw : True)",
        ),
    }
    for label, (old, new) in mutations.items():
        mutant = source.replace(old, new)
        if mutant == source:
            fail(f"{label} mutation did not apply")
        try:
            pin_role_headers(mutant)
        except SystemExit:
            continue
        fail(f"{label} mutation was accepted")

def main() -> None:
    fixture = text(FIXTURE)
    if not OWNER.is_file():
        fail("missing sole production owner")
    no_trust_shortcut(OWNER)
    no_trust_shortcut(FIXTURE)
    require_controls(fixture)
    pin_role_headers(text(OWNER))
    deletion_control(fixture)
    header_mutation_controls(text(OWNER))
    compile_fixture()
    axiom_checks()
    print("OK — S3 enumeration assurance: 18 Lean controls; 10 exact public/auxiliary headers and axiom pins; exact-code Registry witnesses at empty/singleton/64; ABI/order/padding/wrap, cursor independence and collision rejection, writer certificate rejection, cap, no-op model/event-omission and event-shape controls; header mutation, deletion and trust controls")

if __name__ == "__main__":
    main()
