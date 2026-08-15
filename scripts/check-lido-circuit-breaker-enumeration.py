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
    "empty_image_control", "singleton_size_control", "sixtyFour_size_control",
    "sixtyFour_not_capped_at_one", "full_prefix_image_control",
    "cursor_not_memory_resident_control", "reachable_writer_rejected_control",
    "order_omission_duplication_and_truncation_rejected",
    "abi_header_size_and_padding_control",
    "unbounded_offset_needs_witness_bound",
    "noop_shaped_transitions_still_exist",
    "event_shape_mutants_rejected",
)
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|opaque|native_decide|implemented_by)\b")
ROLES = {
    "getPausables_runCompiled": "3238654f9c531f1893bd3eebb4f197c497db83b0730b0f97a061562288ffea9c",
    "getPausables_noSstore_occurrence": "59044ce54c2dd2bed592ecfc06240c0c55243ed3a3ee88676ca21752b246f8ac",
    "registryViews_coherent": "8bb6bdd2c1819c8d8758e4bb9d3c1eb09e6880248b063a9008d472498f24e565",
    "pauserSet_local_transition": "d81430d517bc25a50015b2eb098bae5ead3e8e17febed62dd30be918fb32ad0d",
    "pauserSet_target_zero_no_success": "5ddcaaebf789223390d7949699b0816c443500d35b49b67600743ba3831ba12d",
    "pauserSet_settled_error_not_observable": "41b67d67d121ee7c98c17f5106372cfe3dc2c0be3416e1df4f15c7a0a87f68e3",
    "registryObservation_sound": "980e86c35658906a9b2b0b50a0ea8322ddf123dce2d859083961a178e723e54d",
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
    for token in ("List.range 64", "enumLoop_pre_memory_independent_of_cursor",
                  "enumeration_writing_mutant_rejected", "enumPrefixMemory_full_read"):
        if token not in source:
            fail(f"fixture no longer owns required semantic channel {token}")

def no_trust_shortcut(path: Path) -> None:
    match = FORBIDDEN.search(text(path))
    if match:
        fail(f"forbidden trust token {match.group(1)!r} in {path.relative_to(ROOT)}")

def normalized_header(source: str, name: str) -> str:
    match = re.search(rf"(?ms)^theorem\s+{re.escape(name)}\b.*?:= by", source)
    if not match:
        fail(f"missing pinned public role {name}")
    return " ".join(match.group(0)[:-4].split())

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
        "wrong event topic order": (
            "[pauserSetEvent, target, assignmentAt entries target, newPauser]",
            "[pauserSetEvent, assignmentAt entries target, target, newPauser]",
        ),
        "foreign storage owner": (
            "Devm.getStor base sevm.currentTarget", "Devm.getStor base ca",
        ),
        "fixed code identity": (
            "lidoCircuitBreakerCode dp", "lidoCircuitBreakerCode officialParams",
        ),
        "rolled-back log treated as visible": (
            ": out.logs = [] :=", ": True :=",
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
    print("OK — S3 enumeration assurance: 12 Lean controls; 7 exact public headers and axiom pins; empty/singleton/64; ABI/order/padding/wrap, cursor, writer, cap, no-op event, event-shape, owner/code and rollback channels; deletion and trust controls")

if __name__ == "__main__":
    main()
