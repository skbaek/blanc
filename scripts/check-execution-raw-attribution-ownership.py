#!/usr/bin/env python3
"""Fail-closed owner and corpus-shadow check for raw attribution APIs."""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "scripts" / "execution-raw-attribution-owner-manifest.json"
EXPECTED_OWNERS = 28
EXPECTED_COMMON_MODULES = 2
SHADOW_POLICIES = {"owner-only", "forbid-contract-basename"}
# UNADOPTED PROPOSAL (pending WSL protected adoption): one exact
# path/FQN/kind authority exception, double-pinned so a manifest-only
# edit cannot grow it. No module- or file-wide exemption exists.
EXPECTED_LEGITIMATE_COLLISIONS = [
    {
        "module": "Blanc/ExecutionOccurrence.lean",
        "declaration": "Blanc.Exec.Frame.successfulSstore_sourceSite",
        "kind": "theorem",
    },
]
SOURCE_SITE_DECLARATION = "Blanc.Exec.NinstOccurrence.sourceSite_of_rawFrameRoot"
SOURCE_SITE_SIGNATURE = """theorem Exec.NinstOccurrence.sourceSite_of_rawFrameRoot
    {globalRoot frameRoot : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (_selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : (Blanc.Exec.Deriv.exactInvocation program storageTarget codeAddress frameRoot))
    (sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = occurrence.node.pc ∧
      site.instruction = .reg .sstore := by"""
STRICT_BEFORE_DECLARATION = (
    "Blanc.Exec.Deriv.SourceCursor.Chronology.strictBefore"
)
STRICT_BEFORE_HEADER = """theorem Exec.Deriv.SourceCursor.Chronology.strictBefore
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root program initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
    (distinct : cursor.node ≠ target) :
    Exec.Deriv.lt target cursor.node :="""
TOWARD_DECLARATION = "Blanc.Exec.Deriv.SourceCursor.toward"
TOWARD_MARKER = "theorem Exec.Deriv.SourceCursor.toward\n"
TOWARD_HEADER = """theorem Exec.Deriv.SourceCursor.toward
    {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    Exec.Deriv.SourceCursor.Toward cursor target instruction cursor :="""
TOWARD_DELEGATION = """exact Exec.Deriv.SourceCursor.toward_core cursor.node cursor cursor rfl
    compiled chronology nonPush instructionAt"""


@dataclass(frozen=True)
class Owner:
    declaration: str
    kind: str
    shadow: str
    module: str


def load_lean_parser():
    path = ROOT / "scripts" / "check-extraction-ownership.py"
    spec = importlib.util.spec_from_file_location("raw_attribution_lean_parser", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load declaration parser")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_checked_inventory():
    # Coupled runtime/input dependency: occurrence owns the bounded lexical
    # declaration channel. Importing its module does not run either gate.
    path = ROOT / "scripts" / "check-execution-occurrence.py"
    spec = importlib.util.spec_from_file_location("raw_occurrence_inventory", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load checked occurrence inventory")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def read_manifest() -> tuple[tuple[str, ...], tuple[Owner, ...], tuple[tuple[str, str, str], ...]]:
    try:
        value = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"manifest is unreadable: {exc}") from exc
    if not isinstance(value, dict) or set(value) != {
        "schema", "commonModules", "owners", "legitimateCollisions"
    }:
        raise ValueError(
            "manifest must contain exactly "
            "schema/commonModules/owners/legitimateCollisions"
        )
    if value["schema"] != 3:
        raise ValueError("unsupported manifest schema")
    modules = value["commonModules"]
    rows = value["owners"]
    if (not isinstance(modules, list) or
            len(modules) != EXPECTED_COMMON_MODULES or
            not all(isinstance(module, str) and module for module in modules) or
            len(set(modules)) != len(modules)):
        raise ValueError(
            f"commonModules must contain exactly {EXPECTED_COMMON_MODULES} "
            "unique nonempty strings"
        )
    if not isinstance(rows, list) or len(rows) != EXPECTED_OWNERS:
        raise ValueError(f"manifest must contain exactly {EXPECTED_OWNERS} owners")
    owners: list[Owner] = []
    for index, row in enumerate(rows, 1):
        if not isinstance(row, dict) or set(row) != {
            "declaration", "kind", "shadow", "module"
        }:
            raise ValueError(
                f"owner {index} must contain exactly "
                "declaration/kind/shadow/module"
            )
        declaration = row["declaration"]
        kind = row["kind"]
        shadow = row["shadow"]
        module = row["module"]
        if (not isinstance(declaration, str) or
                not declaration.startswith("Blanc.") or
                not isinstance(kind, str) or not kind or
                shadow not in SHADOW_POLICIES or module not in modules):
            raise ValueError(
                f"owner {index} has invalid declaration/kind/shadow/module"
            )
        owners.append(Owner(declaration, kind, shadow, module))
    if len({owner.declaration for owner in owners}) != len(owners):
        raise ValueError("owner declarations must be unique")
    if value["legitimateCollisions"] != EXPECTED_LEGITIMATE_COLLISIONS:
        raise ValueError(
            "unadopted legitimate-collision authority exceptions drifted"
        )
    collisions = tuple(
        (row["module"], row["declaration"], row["kind"])
        for row in value["legitimateCollisions"]
    )
    return tuple(modules), tuple(owners), collisions


def corpus_files() -> list[Path]:
    paths = sorted((ROOT / "Blanc").rglob("*.lean"))
    root_module = ROOT / "Blanc.lean"
    if root_module.is_file():
        paths.insert(0, root_module)
    return paths


def owner_errors(
    declarations: dict[str, dict[str, tuple[str, int]]],
    owners: tuple[Owner, ...],
) -> list[str]:
    errors: list[str] = []
    for owner in owners:
        expected_module = declarations[owner.module]
        actual = expected_module.get(owner.declaration)
        if actual is None:
            elsewhere = [
                module for module, found in declarations.items()
                if module != owner.module and owner.declaration in found
            ]
            if elsewhere:
                errors.append(
                    f"COMMON-WRONG-MODULE — {owner.declaration}: found in "
                    f"{', '.join(elsewhere)}, expected {owner.module}"
                )
            else:
                errors.append(f"COMMON-MISSING — {owner.declaration}")
        elif actual[0] != owner.kind:
            errors.append(
                f"COMMON-KIND-MISMATCH — {owner.declaration}: "
                f"found {actual[0]}, expected {owner.kind}"
            )
        duplicates = [
            module for module, found in declarations.items()
            if module != owner.module and owner.declaration in found
        ]
        if actual is not None and duplicates:
            errors.append(
                f"COMMON-DUPLICATE — {owner.declaration}: also declared in "
                f"{', '.join(duplicates)}"
            )
    return errors


def owner_module(declaration: str, owners: tuple[Owner, ...]) -> str:
    matches = [owner.module for owner in owners
               if owner.declaration == declaration]
    if len(matches) != 1:
        raise ValueError(
            f"expected one manifest owner for {declaration}, found {len(matches)}"
        )
    return matches[0]


def _declaration_items(declarations):
    if isinstance(declarations, dict):
        return [(name, kind, line)
                for name, (kind, line) in declarations.items()]
    return list(declarations)


def shadow_errors(
    declarations,
    owners: tuple[Owner, ...],
    label: str,
    exempt=frozenset(),
) -> list[str]:
    """Basename shadows in one file; `exempt` holds exact (FQN, kind) tuples
    for that file only (its own rightful owners and legitimate collisions)."""
    forbidden = {
        owner.declaration.rsplit(".", 1)[-1]: owner.declaration
        for owner in owners if owner.shadow == "forbid-contract-basename"
    }
    errors: list[str] = []
    for name, kind, line in _declaration_items(declarations):
        if (name, kind) in exempt:
            continue
        basename = name.rsplit(".", 1)[-1]
        if basename in forbidden:
            errors.append(
                f"CORPUS-SHADOW — {label}:{line}: {kind} {name} "
                f"shadows {forbidden[basename]}"
            )
    return errors


def owner_redeclaration_errors(
    declarations,
    owners: tuple[Owner, ...],
    label: str,
) -> list[str]:
    """Exact owner FQNs (owner-only rows included) may be declared only at
    their rightful (module, kind) tuple, anywhere in the corpus."""
    by_declaration = {owner.declaration: owner for owner in owners}
    errors: list[str] = []
    for name, kind, line in _declaration_items(declarations):
        owner = by_declaration.get(name)
        if owner is None:
            continue
        if label == owner.module and kind == owner.kind:
            continue
        errors.append(
            f"OWNER-REDECLARED — {label}:{line}: {kind} {name} redeclared "
            f"outside its rightful tuple ({owner.module}, {owner.kind})"
        )
    return errors


def source_site_signature_errors(source: str, strip_comments) -> list[str]:
    clean = strip_comments(source)
    marker = "theorem Exec.NinstOccurrence.sourceSite_of_rawFrameRoot"
    if clean.count(marker) != 1:
        return [
            f"SIGNATURE-MISMATCH — {SOURCE_SITE_DECLARATION}: "
            "declaration header is absent or duplicated"
        ]
    suffix = clean.split(marker, 1)[1]
    if ":= by" not in suffix:
        return [
            f"SIGNATURE-MISMATCH — {SOURCE_SITE_DECLARATION}: "
            "theorem body delimiter is absent"
        ]
    actual = marker + suffix.split(":= by", 1)[0] + ":= by"
    normalize = lambda text: " ".join(text.split())
    if normalize(actual) != normalize(SOURCE_SITE_SIGNATURE):
        return [
            f"SIGNATURE-MISMATCH — {SOURCE_SITE_DECLARATION}: "
            "exact selected-root/ParentPrefix signature drifted"
        ]
    return []


def normalized_header_errors(
    source: str, strip_comments, marker: str, expected: str, declaration: str
) -> list[str]:
    """Pin one comment/whitespace-normalized public header through `:=`."""
    clean = strip_comments(source)
    if clean.count(marker) != 1:
        return [
            f"SIGNATURE-MISMATCH — {declaration}: "
            "declaration header is absent or duplicated"
        ]
    suffix = clean.split(marker, 1)[1]
    if ":=" not in suffix:
        return [
            f"SIGNATURE-MISMATCH — {declaration}: theorem body delimiter is absent"
        ]
    actual = marker + suffix.split(":=", 1)[0] + ":="
    normalize = lambda text: " ".join(text.split())
    if normalize(actual) != normalize(expected):
        return [
            f"SIGNATURE-MISMATCH — {declaration}: normalized header drifted"
        ]
    return []


def shared_kernel_errors(source: str, strip_comments) -> list[str]:
    """Require one traversal kernel and projection through the public route."""
    clean = strip_comments(source)
    required = (
        "private theorem Exec.Deriv.SourceCursor.toward_core :",
        "private theorem Exec.Deriv.SourceCursor.Toward.sourceSite",
        "exact (cursor.toward compiled reached nonPush instructionAt).sourceSite",
    )
    errors = [
        f"SHARED-KERNEL — expected exactly one `{token}`"
        for token in required if clean.count(token) != 1
    ]
    if "sourceSite_core" in clean:
        errors.append("SHARED-KERNEL — parallel sourceSite_core traversal survives")
    normalize = lambda text: " ".join(text.split())
    if normalize(clean).count(normalize(TOWARD_DELEGATION)) != 1:
        errors.append(
            "SHARED-KERNEL — public toward does not delegate exactly once "
            "to toward_core"
        )
    return errors


def audit() -> list[str]:
    try:
        parser = load_lean_parser()
        inventory = load_checked_inventory()
        modules, owners, collisions = read_manifest()
        sources: dict[str, str] = {}
        declarations: dict[str, dict[str, tuple[str, int]]] = {}
        for relative in modules:
            path = ROOT / relative
            if not path.is_file():
                return [f"COMMON-MISSING — common module is absent: {path}"]
            sources[relative] = path.read_text(encoding="utf-8")
            declarations[relative] = inventory.checked_declaration_dict(parser, path)
        errors = owner_errors(declarations, owners)
        source_site_source = sources[owner_module(SOURCE_SITE_DECLARATION, owners)]
        errors.extend(
            source_site_signature_errors(source_site_source, parser.strip_comments)
        )
        strict_source = sources[owner_module(STRICT_BEFORE_DECLARATION, owners)]
        errors.extend(normalized_header_errors(
            strict_source, parser.strip_comments,
            "theorem Exec.Deriv.SourceCursor.Chronology.strictBefore\n",
            STRICT_BEFORE_HEADER, STRICT_BEFORE_DECLARATION,
        ))
        toward_source = sources[owner_module(TOWARD_DECLARATION, owners)]
        errors.extend(normalized_header_errors(
            toward_source, parser.strip_comments,
            TOWARD_MARKER,
            TOWARD_HEADER, TOWARD_DECLARATION,
        ))
        errors.extend(shared_kernel_errors(toward_source, parser.strip_comments))
        files = corpus_files()
        if not any(path.is_relative_to(ROOT / "Blanc") for path in files):
            errors.append("SETUP — first-party Blanc population is empty")
        collision_set = set(collisions)
        collision_counts = {tuple_: 0 for tuple_ in collisions}
        for path in files:
            rel = path.relative_to(ROOT).as_posix()
            found = inventory.checked_declarations(parser, path)
            exempt = {
                (owner.declaration, owner.kind)
                for owner in owners if owner.module == rel
            } | {
                (declaration, kind)
                for module, declaration, kind in collisions if module == rel
            }
            for name, kind, _line in found:
                if (rel, name, kind) in collision_set:
                    collision_counts[(rel, name, kind)] += 1
            errors.extend(shadow_errors(found, owners, rel, exempt))
            errors.extend(owner_redeclaration_errors(found, owners, rel))
        for (module, declaration, kind), count in collision_counts.items():
            if count != 1:
                errors.append(
                    f"COLLISION-INVENTORY — {declaration} as {kind} at "
                    f"{module} must occur exactly once, found {count}"
                )
        return errors
    except (OSError, RuntimeError, ValueError) as exc:
        return [f"SETUP — raw attribution ownership: {exc}"]


def negative_controls() -> list[str]:
    parser = load_lean_parser()
    inventory = load_checked_inventory()
    modules, owners, _collisions = read_manifest()
    sources = {
        relative: (ROOT / relative).read_text(encoding="utf-8")
        for relative in modules
    }
    common = {
        relative: inventory.checked_declaration_dict(parser, ROOT / relative)
        for relative in modules
    }
    first = owners[0]
    missing = {relative: dict(found) for relative, found in common.items()}
    missing[first.module].pop(first.declaration, None)
    missing_live = any(
        error == f"COMMON-MISSING — {first.declaration}"
        for error in owner_errors(missing, owners)
    )

    relocated = {relative: dict(found) for relative, found in common.items()}
    moved = relocated[first.module].pop(first.declaration)
    wrong_module = next(module for module in modules if module != first.module)
    relocated[wrong_module][first.declaration] = moved
    wrong_module_live = any(
        error.startswith(f"COMMON-WRONG-MODULE — {first.declaration}:")
        for error in owner_errors(relocated, owners)
    )

    shadow_owner = next(
        owner for owner in owners if owner.declaration == TOWARD_DECLARATION
    )
    synthetic = f"Blanc.Weth10.RawAttribution.{shadow_owner.declaration.rsplit('.', 1)[-1]}"
    shadow_live = any(
        error.startswith("CORPUS-SHADOW — synthetic.lean:1:")
        for error in shadow_errors(
            {synthetic: ("theorem", 1)}, owners, "synthetic.lean"
        )
    )
    source_site_source = sources[owner_module(SOURCE_SITE_DECLARATION, owners)]
    selected_mutant = source_site_source.replace(
        "(_selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)",
        "(_selected : True)",
        1,
    )
    selected_live = any(
        error.startswith("SIGNATURE-MISMATCH —")
        for error in source_site_signature_errors(
            selected_mutant, parser.strip_comments
        )
    )
    prefix_mutant = source_site_source.replace(
        "(sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node)",
        "(sameFrame : True)",
        1,
    )
    prefix_live = any(
        error.startswith("SIGNATURE-MISMATCH —")
        for error in source_site_signature_errors(prefix_mutant, parser.strip_comments)
    )
    weakened_toward_header = TOWARD_HEADER.replace(
        "(reached : Exec.Deriv.ParentPrefix cursor.node target)",
        "(reached : True)",
        1,
    )
    toward_source = sources[owner_module(TOWARD_DECLARATION, owners)]
    toward_mutant = toward_source.replace(
        TOWARD_HEADER, weakened_toward_header, 1
    )
    toward_live = any(
        error.startswith("SIGNATURE-MISMATCH —")
        for error in normalized_header_errors(
            toward_mutant, parser.strip_comments,
            TOWARD_MARKER,
            TOWARD_HEADER, TOWARD_DECLARATION,
        )
    )
    strict_source = sources[owner_module(STRICT_BEFORE_DECLARATION, owners)]
    strict_mutant = strict_source.replace(
        "(distinct : cursor.node ≠ target)",
        "(distinct : True)",
        1,
    )
    strict_live = any(
        error.startswith("SIGNATURE-MISMATCH —")
        for error in normalized_header_errors(
            strict_mutant, parser.strip_comments,
            "theorem Exec.Deriv.SourceCursor.Chronology.strictBefore\n",
            STRICT_BEFORE_HEADER, STRICT_BEFORE_DECLARATION,
        )
    )
    kernel_mutant = toward_source.replace(
        "private theorem Exec.Deriv.SourceCursor.toward_core :",
        "private theorem Exec.Deriv.SourceCursor.toward_core_removed",
        1,
    )
    kernel_live = any(
        error.startswith("SHARED-KERNEL —")
        for error in shared_kernel_errors(kernel_mutant, parser.strip_comments)
    )
    delegation_mutant = toward_source.replace(
        TOWARD_DELEGATION,
        TOWARD_DELEGATION.replace("toward_core", "toward_core_bypassed", 1),
        1,
    )
    delegation_live = any(
        error.startswith("SHARED-KERNEL —")
        for error in shared_kernel_errors(
            delegation_mutant, parser.strip_comments
        )
    )
    owner_only = next(
        owner for owner in owners if owner.shadow == "owner-only"
    )
    redeclared_live = any(
        error.startswith("OWNER-REDECLARED — Blanc/Synthetic.lean:1:")
        for error in owner_redeclaration_errors(
            [(owner_only.declaration, owner_only.kind, 1)],
            owners, "Blanc/Synthetic.lean",
        )
    ) and not owner_redeclaration_errors(
        [(owner_only.declaration, owner_only.kind, 1)],
        owners, owner_only.module,
    )
    collision = EXPECTED_LEGITIMATE_COLLISIONS[0]
    collision_basename = collision["declaration"].rsplit(".", 1)[-1]
    collision_errors = shadow_errors(
        [(collision["declaration"], collision["kind"], 1),
         (f"Blanc.Other.{collision_basename}", collision["kind"], 2)],
        owners, collision["module"],
        exempt={(collision["declaration"], collision["kind"])},
    )
    collision_live = (
        len(collision_errors) == 1
        and collision_errors[0].startswith(
            f"CORPUS-SHADOW — {collision['module']}:2:"
        )
    )
    owner_module_shadow_live = any(
        error.startswith(f"CORPUS-SHADOW — {shadow_owner.module}:1:")
        for error in shadow_errors(
            [(synthetic, "theorem", 1)], owners, shadow_owner.module,
            exempt={(shadow_owner.declaration, shadow_owner.kind)},
        )
    )
    errors: list[str] = []
    if not missing_live:
        errors.append("CONTROL — common-owner removal was not detected")
    if not wrong_module_live:
        errors.append("CONTROL — wrong common-owner module was not detected")
    if not shadow_live:
        errors.append("CONTROL — corpus-basename shadow was not detected")
    if not selected_live:
        errors.append("CONTROL — selected-root signature weakening was not detected")
    if not prefix_live:
        errors.append("CONTROL — ParentPrefix signature weakening was not detected")
    if not toward_live:
        errors.append("CONTROL — toward signature weakening was not detected")
    if not strict_live:
        errors.append("CONTROL — strict-before signature weakening was not detected")
    if not kernel_live:
        errors.append("CONTROL — shared traversal-kernel removal was not detected")
    if not delegation_live:
        errors.append("CONTROL — public traversal delegation removal was not detected")
    if not redeclared_live:
        errors.append("CONTROL — owner-only exact-FQN redeclaration was not detected")
    if not collision_live:
        errors.append("CONTROL — legitimate collision tuple boundary was not detected")
    if not owner_module_shadow_live:
        errors.append("CONTROL — basename shadow inside an owner module was not detected")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    try:
        errors = audit()
        if args.negative_controls:
            errors.extend(negative_controls())
    except (OSError, RuntimeError, ValueError) as exc:
        errors = [f"SETUP — raw attribution ownership: {exc}"]
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    controls = "; 12/12 controls live" if args.negative_controls else ""
    print(
        f"OK — raw attribution ownership: {EXPECTED_OWNERS}/{EXPECTED_OWNERS} "
        f"common owners across {EXPECTED_COMMON_MODULES} modules; no corpus "
        f"basename shadows; exact selected-root source/chronology "
        f"signatures{controls}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
