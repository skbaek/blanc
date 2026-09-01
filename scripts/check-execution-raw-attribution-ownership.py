#!/usr/bin/env python3
"""Fail-closed owner and contract-shadow check for raw attribution APIs."""

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
SOURCE_SITE_DECLARATION = "Blanc.Exec.NinstOccurrence.sourceSite_of_rawFrameRoot"
SOURCE_SITE_SIGNATURE = """theorem Exec.NinstOccurrence.sourceSite_of_rawFrameRoot
    {globalRoot frameRoot : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (_selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : frameRoot.exactInvocation program storageTarget codeAddress)
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


def read_manifest() -> tuple[tuple[str, ...], tuple[str, ...], tuple[Owner, ...]]:
    try:
        value = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"manifest is unreadable: {exc}") from exc
    if not isinstance(value, dict) or set(value) != {
        "schema", "commonModules", "contractModuleGlobs", "owners"
    }:
        raise ValueError(
            "manifest must contain exactly "
            "schema/commonModules/contractModuleGlobs/owners"
        )
    if value["schema"] != 2:
        raise ValueError("unsupported manifest schema")
    modules = value["commonModules"]
    globs = value["contractModuleGlobs"]
    rows = value["owners"]
    if (not isinstance(modules, list) or
            len(modules) != EXPECTED_COMMON_MODULES or
            not all(isinstance(module, str) and module for module in modules) or
            len(set(modules)) != len(modules)):
        raise ValueError(
            f"commonModules must contain exactly {EXPECTED_COMMON_MODULES} "
            "unique nonempty strings"
        )
    if (not isinstance(globs, list) or not globs or
            not all(isinstance(pattern, str) and pattern for pattern in globs)):
        raise ValueError("contractModuleGlobs must be a nonempty string list")
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
    return tuple(modules), tuple(globs), tuple(owners)


def contract_files(globs: tuple[str, ...]) -> list[Path]:
    return sorted({path for pattern in globs for path in ROOT.glob(pattern)})


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


def shadow_errors(
    declarations: dict[str, tuple[str, int]],
    owners: tuple[Owner, ...],
    label: str,
) -> list[str]:
    forbidden = {
        owner.declaration.rsplit(".", 1)[-1]: owner.declaration
        for owner in owners if owner.shadow == "forbid-contract-basename"
    }
    errors: list[str] = []
    for name, (kind, line) in declarations.items():
        basename = name.rsplit(".", 1)[-1]
        if basename in forbidden:
            errors.append(
                f"CONTRACT-SHADOW — {label}:{line}: {kind} {name} "
                f"shadows {forbidden[basename]}"
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
        modules, globs, owners = read_manifest()
        sources: dict[str, str] = {}
        declarations: dict[str, dict[str, tuple[str, int]]] = {}
        for relative in modules:
            path = ROOT / relative
            if not path.is_file():
                return [f"COMMON-MISSING — common module is absent: {path}"]
            sources[relative] = path.read_text(encoding="utf-8")
            declarations[relative] = parser.declarations(path)
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
        files = contract_files(globs)
        if not files:
            errors.append("SETUP — no contract module matched the manifest globs")
        for path in files:
            rel = path.relative_to(ROOT).as_posix()
            declarations = parser.declarations(path)
            errors.extend(shadow_errors(declarations, owners, rel))
        return errors
    except (OSError, RuntimeError, ValueError) as exc:
        return [f"SETUP — raw attribution ownership: {exc}"]


def negative_controls() -> list[str]:
    parser = load_lean_parser()
    modules, _globs, owners = read_manifest()
    sources = {
        relative: (ROOT / relative).read_text(encoding="utf-8")
        for relative in modules
    }
    common = {
        relative: parser.declarations(ROOT / relative)
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
        error.startswith("CONTRACT-SHADOW — synthetic.lean:1:")
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
    errors: list[str] = []
    if not missing_live:
        errors.append("CONTROL — common-owner removal was not detected")
    if not wrong_module_live:
        errors.append("CONTROL — wrong common-owner module was not detected")
    if not shadow_live:
        errors.append("CONTROL — contract-basename shadow was not detected")
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
    controls = "; 9/9 controls live" if args.negative_controls else ""
    print(
        f"OK — raw attribution ownership: {EXPECTED_OWNERS}/{EXPECTED_OWNERS} "
        f"common owners across {EXPECTED_COMMON_MODULES} modules; no contract "
        f"basename shadows; exact selected-root source/chronology "
        f"signatures{controls}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
