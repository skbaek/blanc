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


def load_lean_parser():
    path = ROOT / "scripts" / "check-extraction-ownership.py"
    spec = importlib.util.spec_from_file_location("raw_attribution_lean_parser", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load declaration parser")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    # The shared parser's historical identifier grammar predates declarations
    # containing `?` (for example `successfulSstore?_sound`).  Keep its
    # comment/scope handling, but prevent those headers from being truncated
    # into duplicate basenames while scanning the larger occurrence module.
    ident = r"[A-Za-z_][A-Za-z0-9_'?!]*(?:\.[A-Za-z_][A-Za-z0-9_'?!]*)*"
    module.DECL_RE = re.compile(
        rf"^\s*(?:@\[[^]]+\]\s*)*"
        rf"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        rf"(def|theorem|structure|abbrev|opaque|axiom|inductive|class)\s+"
        rf"({ident})(?=\s|$)"
    )
    return module


def read_manifest() -> tuple[Path, tuple[str, ...], tuple[Owner, ...]]:
    try:
        value = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"manifest is unreadable: {exc}") from exc
    if not isinstance(value, dict) or set(value) != {
        "schema", "commonModule", "contractModuleGlobs", "owners"
    }:
        raise ValueError(
            "manifest must contain exactly schema/commonModule/contractModuleGlobs/owners"
        )
    if value["schema"] != 1:
        raise ValueError("unsupported manifest schema")
    common = value["commonModule"]
    globs = value["contractModuleGlobs"]
    rows = value["owners"]
    if not isinstance(common, str) or not common:
        raise ValueError("commonModule must be a nonempty string")
    if (not isinstance(globs, list) or not globs or
            not all(isinstance(pattern, str) and pattern for pattern in globs)):
        raise ValueError("contractModuleGlobs must be a nonempty string list")
    if not isinstance(rows, list) or len(rows) != EXPECTED_OWNERS:
        raise ValueError(f"manifest must contain exactly {EXPECTED_OWNERS} owners")
    owners: list[Owner] = []
    for index, row in enumerate(rows, 1):
        if not isinstance(row, dict) or set(row) != {"declaration", "kind", "shadow"}:
            raise ValueError(
                f"owner {index} must contain exactly declaration/kind/shadow"
            )
        declaration, kind, shadow = row["declaration"], row["kind"], row["shadow"]
        if (not isinstance(declaration, str) or
                not declaration.startswith("Blanc.") or
                not isinstance(kind, str) or not kind or
                shadow not in SHADOW_POLICIES):
            raise ValueError(f"owner {index} has invalid declaration/kind/shadow")
        owners.append(Owner(declaration, kind, shadow))
    if len({owner.declaration for owner in owners}) != len(owners):
        raise ValueError("owner declarations must be unique")
    return ROOT / common, tuple(globs), tuple(owners)


def contract_files(globs: tuple[str, ...]) -> list[Path]:
    return sorted({path for pattern in globs for path in ROOT.glob(pattern)})


def owner_errors(
    declarations: dict[str, tuple[str, int]], owners: tuple[Owner, ...]
) -> list[str]:
    errors: list[str] = []
    for owner in owners:
        actual = declarations.get(owner.declaration)
        if actual is None:
            errors.append(f"COMMON-MISSING — {owner.declaration}")
        elif actual[0] != owner.kind:
            errors.append(
                f"COMMON-KIND-MISMATCH — {owner.declaration}: "
                f"found {actual[0]}, expected {owner.kind}"
            )
    return errors


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
        common_path, globs, owners = read_manifest()
        if not common_path.is_file():
            return [f"COMMON-MISSING — common module is absent: {common_path}"]
        common_source = common_path.read_text(encoding="utf-8")
        common = parser.declarations(common_path)
        errors = owner_errors(common, owners)
        errors.extend(
            source_site_signature_errors(common_source, parser.strip_comments)
        )
        errors.extend(normalized_header_errors(
            common_source, parser.strip_comments,
            "theorem Exec.Deriv.SourceCursor.Chronology.strictBefore\n",
            STRICT_BEFORE_HEADER, STRICT_BEFORE_DECLARATION,
        ))
        errors.extend(normalized_header_errors(
            common_source, parser.strip_comments,
            TOWARD_MARKER,
            TOWARD_HEADER, TOWARD_DECLARATION,
        ))
        errors.extend(shared_kernel_errors(common_source, parser.strip_comments))
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
    common_path, _globs, owners = read_manifest()
    common_source = common_path.read_text(encoding="utf-8")
    common = parser.declarations(common_path)
    first = owners[0]
    missing = dict(common)
    missing.pop(first.declaration, None)
    missing_live = any(
        error == f"COMMON-MISSING — {first.declaration}"
        for error in owner_errors(missing, owners)
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
    selected_mutant = common_source.replace(
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
    prefix_mutant = common_source.replace(
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
    toward_mutant = common_source.replace(
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
    strict_mutant = common_source.replace(
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
    kernel_mutant = common_source.replace(
        "private theorem Exec.Deriv.SourceCursor.toward_core :",
        "private theorem Exec.Deriv.SourceCursor.toward_core_removed",
        1,
    )
    kernel_live = any(
        error.startswith("SHARED-KERNEL —")
        for error in shared_kernel_errors(kernel_mutant, parser.strip_comments)
    )
    delegation_mutant = common_source.replace(
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
    controls = "; 8/8 controls live" if args.negative_controls else ""
    print(
        f"OK — raw attribution ownership: {EXPECTED_OWNERS}/{EXPECTED_OWNERS} "
        f"common owners; no contract basename shadows; exact selected-root "
        f"source/chronology signatures{controls}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
