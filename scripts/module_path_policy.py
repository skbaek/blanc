#!/usr/bin/env python3
"""Exact module-path and filesystem-alias policy for Blanc gate scripts.

The raw accepted language is ``Blanc/`` followed by one or more NFC Unicode
identifier components, with the final component ending in the literal
``.lean`` suffix.  Validation splits the original string on ``/`` before any
``Path`` or ``PurePath`` object is constructed.  Empty, ``.``, ``..``,
absolute, trimmed, backslash, non-NFC, and non-identifier spellings are not in
the language.

Filesystem policy is reject-all-aliases.  Every component must occur with the
exact spelling returned by its parent directory and must not be a symbolic
link.  A final module/output must be a regular file with link count one.  Thus
file and directory symlinks, out-and-back paths, external hardlinks, wrong-case
aliases, and normalization aliases are rejected even when the host resolves
them.  The final canonical path must also remain under the canonical repository
root.  The policy deliberately makes no portability claim for filesystems that
cannot expose the requested alias; controls report those cases as closed skips.
"""

from __future__ import annotations

import ast
import copy
import json
import os
import stat
import tempfile
import unicodedata
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple


CENSUS_REL = Path("scripts/module-path-dereference-census.json")
AUDITED_CALLS = {
    "walk_module_files": "walk",
    "resolve_module_file": "explicit dereference",
    "resolve_source_file": "explicit dereference",
    "resolve_bound_file": "generator output binding",
}


class ModulePathPolicyError(ValueError):
    """A raw-language, containment, alias, or census-integrity failure."""


def _raw_components(raw: object, *, module: bool) -> Tuple[str, ...]:
    if not isinstance(raw, str) or not raw or raw != raw.strip():
        raise ModulePathPolicyError("expected a nonempty exactly trimmed path string")
    if raw.startswith("/") or "\\" in raw:
        raise ModulePathPolicyError(f"absolute or backslash path is forbidden: {raw!r}")
    components = tuple(raw.split("/"))
    if any(component in {"", ".", ".."} for component in components):
        raise ModulePathPolicyError(
            f"empty, '.' and '..' path components are forbidden: {raw!r}"
        )
    if any(unicodedata.normalize("NFC", component) != component for component in components):
        raise ModulePathPolicyError(f"path components must use exact NFC spelling: {raw!r}")
    if module:
        if len(components) < 2 or components[0] != "Blanc":
            raise ModulePathPolicyError(f"module path must begin with literal 'Blanc/': {raw!r}")
        if not components[-1].endswith(".lean"):
            raise ModulePathPolicyError(f"module path must end with literal '.lean': {raw!r}")
        identifiers = (*components[1:-1], components[-1][:-5])
        if any(not component or not component.isidentifier() for component in identifiers):
            raise ModulePathPolicyError(
                f"module components must be NFC Unicode identifiers: {raw!r}"
            )
    return components


def validate_module_path(raw: object) -> str:
    """Validate raw registry/manifest text before constructing any path object."""
    _raw_components(raw, module=True)
    return raw  # type: ignore[return-value]


def validate_source_path(raw: object) -> str:
    """Validate a source name; the static aggregate ``Blanc.lean`` is also legal."""
    if raw == "Blanc.lean":
        return raw
    return validate_module_path(raw)


def _canonical_root(root: Path) -> Path:
    try:
        resolved = root.resolve(strict=True)
    except OSError as error:
        raise ModulePathPolicyError(f"cannot resolve repository root {root}: {error}") from error
    if not resolved.is_dir():
        raise ModulePathPolicyError(f"repository root is not a directory: {root}")
    return resolved


def _directory_names(parent: Path) -> Sequence[str]:
    try:
        with os.scandir(str(parent)) as entries:
            return tuple(entry.name for entry in entries)
    except OSError as error:
        raise ModulePathPolicyError(f"cannot enumerate {parent}: {error}") from error


def _exact_child(parent: Path, component: str, *, final: bool) -> Path:
    names = _directory_names(parent)
    if component not in names:
        aliases = sorted(
            name for name in names
            if unicodedata.normalize("NFC", name).casefold()
            == unicodedata.normalize("NFC", component).casefold()
        )
        detail = f"; aliases present: {aliases}" if aliases else ""
        raise ModulePathPolicyError(
            f"path spelling is not an exact directory entry under {parent}: {component!r}{detail}"
        )
    child = parent / component
    try:
        metadata = child.lstat()
    except OSError as error:
        raise ModulePathPolicyError(f"cannot inspect {child}: {error}") from error
    if stat.S_ISLNK(metadata.st_mode):
        raise ModulePathPolicyError(f"symbolic-link filesystem alias is forbidden: {child}")
    if final:
        if not stat.S_ISREG(metadata.st_mode):
            raise ModulePathPolicyError(f"module/output is not a regular file: {child}")
        if metadata.st_nlink != 1:
            raise ModulePathPolicyError(
                f"hardlink filesystem alias is forbidden (link count {metadata.st_nlink}): {child}"
            )
    elif not stat.S_ISDIR(metadata.st_mode):
        raise ModulePathPolicyError(f"path component is not a directory: {child}")
    return child


def _contained(path: Path, root: Path) -> Path:
    try:
        resolved = path.resolve(strict=True)
        resolved.relative_to(root)
    except (OSError, ValueError) as error:
        raise ModulePathPolicyError(
            f"resolved path escapes or cannot be resolved under repository root: {path}"
        ) from error
    return resolved


def _resolve_existing(root: Path, components: Sequence[str]) -> Path:
    canonical_root = _canonical_root(root)
    current = canonical_root
    for index, component in enumerate(components):
        current = _exact_child(current, component, final=index == len(components) - 1)
    _contained(current, canonical_root)
    return current


def resolve_module_file(root: Path, raw: object, *, site: str) -> Path:
    """Resolve an exact existing module after raw validation and alias checks."""
    del site  # The statically audited call-site identity is evidence, not authority.
    validated = validate_module_path(raw)
    return _resolve_existing(root, validated.split("/"))


def resolve_source_file(root: Path, raw: object, *, site: str) -> Path:
    """Resolve an exact source path, including the static aggregate Blanc.lean."""
    del site
    validated = validate_source_path(raw)
    return _resolve_existing(root, validated.split("/"))


def resolve_bound_file(
    root: Path, raw: object, *, allow_missing: bool, site: str,
) -> Path:
    """Resolve a generator-owned binding without admitting path aliases."""
    del site
    components = _raw_components(raw, module=False)
    canonical_root = _canonical_root(root)
    current = canonical_root
    for component in components[:-1]:
        current = _exact_child(current, component, final=False)
    leaf = components[-1]
    names = _directory_names(current)
    if leaf in names:
        current = _exact_child(current, leaf, final=True)
        _contained(current, canonical_root)
        return current
    aliases = sorted(
        name for name in names
        if unicodedata.normalize("NFC", name).casefold()
        == unicodedata.normalize("NFC", leaf).casefold()
    )
    if aliases:
        raise ModulePathPolicyError(
            f"bound-file spelling is a filesystem alias under {current}: "
            f"{leaf!r}; exact entries {aliases}"
        )
    if not allow_missing:
        raise ModulePathPolicyError(f"bound file does not exist: {raw!r}")
    candidate = current / leaf
    try:
        current.resolve(strict=True).relative_to(canonical_root)
    except (OSError, ValueError) as error:
        raise ModulePathPolicyError(f"bound-file parent escapes repository root: {raw!r}") from error
    return candidate


def walk_module_files(root: Path, *, site: str) -> List[Path]:
    """Walk every Blanc module without following or overlooking aliases."""
    del site
    canonical_root = _canonical_root(root)
    source = _exact_child(canonical_root, "Blanc", final=False)
    found: List[Path] = []

    def visit(directory: Path, relative: Tuple[str, ...]) -> None:
        try:
            with os.scandir(str(directory)) as iterator:
                entries = sorted(iterator, key=lambda entry: entry.name)
        except OSError as error:
            raise ModulePathPolicyError(f"cannot enumerate module directory {directory}: {error}") from error
        for entry in entries:
            entry_path = directory / entry.name
            if entry.is_symlink():
                raise ModulePathPolicyError(
                    f"symbolic-link filesystem alias is forbidden in module tree: {entry_path}"
                )
            if entry.is_dir(follow_symlinks=False):
                if unicodedata.normalize("NFC", entry.name) != entry.name or not entry.name.isidentifier():
                    raise ModulePathPolicyError(
                        f"module directory must be an NFC Unicode identifier: {entry_path}"
                    )
                visit(entry_path, (*relative, entry.name))
            elif entry.name.endswith(".lean"):
                raw = "/".join(("Blanc", *relative, entry.name))
                found.append(resolve_module_file(canonical_root, raw, site="walk-derived"))
    visit(source, ())
    if not found:
        raise ModulePathPolicyError(f"no production Blanc/**/*.lean modules found under {root}")
    return sorted(found, key=lambda path: path.relative_to(canonical_root).as_posix())


def load_census(root: Path) -> Mapping[str, object]:
    path = root / CENSUS_REL
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ModulePathPolicyError(f"cannot read {CENSUS_REL}: {error}") from error
    if not isinstance(value, dict):
        raise ModulePathPolicyError("module-path census must be a JSON object")
    return value


def _consumer_scripts(root: Path) -> Tuple[str, ...]:
    scripts_root = root / "scripts"
    try:
        return tuple(sorted(
            path.relative_to(root).as_posix()
            for path in scripts_root.rglob("*.py")
            if path.name != Path(__file__).name
        ))
    except OSError as error:
        raise ModulePathPolicyError(f"cannot enumerate Python consumers: {error}") from error


def _static_sites(root: Path, scripts: Iterable[str]) -> Dict[str, Tuple[str, str, int]]:
    found: Dict[str, Tuple[str, str, int]] = {}
    for relative in scripts:
        path = root / relative
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=relative)
        except (OSError, SyntaxError) as error:
            raise ModulePathPolicyError(f"cannot audit {relative}: {error}") from error
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            call = (
                node.func.id if isinstance(node.func, ast.Name)
                else node.func.attr if isinstance(node.func, ast.Attribute)
                else ""
            )
            if call not in AUDITED_CALLS:
                continue
            keyword = next((item for item in node.keywords if item.arg == "site"), None)
            if keyword is None or not isinstance(keyword.value, ast.Constant) or not isinstance(keyword.value.value, str):
                raise ModulePathPolicyError(
                    f"{relative}:{node.lineno}: {call} must carry a literal site= identity"
                )
            site = keyword.value.value
            if site in found:
                raise ModulePathPolicyError(f"duplicate static module-path site {site!r}")
            found[site] = (relative, call, node.lineno)
    return found


def audit_census(root: Path, document: Optional[Mapping[str, object]] = None) -> int:
    """Bidirectionally match the committed census to every policy call site."""
    raw = document or load_census(root)
    if set(raw) != {"schemaVersion", "policy", "sites"}:
        raise ModulePathPolicyError("module-path census top-level schema mismatch")
    if raw["schemaVersion"] != 1 or raw["policy"] != "reject-all-filesystem-aliases":
        raise ModulePathPolicyError("module-path census version or policy mismatch")
    rows = raw["sites"]
    if not isinstance(rows, list) or not rows:
        raise ModulePathPolicyError("module-path census must contain at least one site")
    expected: Dict[str, Tuple[str, str, str]] = {}
    fields = {"id", "script", "call", "class", "source"}
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or set(row) != fields:
            raise ModulePathPolicyError(f"module-path census site {index} schema mismatch")
        site = row["id"]
        if not all(isinstance(row[key], str) and row[key] for key in fields):
            raise ModulePathPolicyError(f"module-path census site {index} needs nonempty strings")
        if site in expected:
            raise ModulePathPolicyError(f"duplicate module-path census site {site!r}")
        if row["call"] not in AUDITED_CALLS or AUDITED_CALLS[row["call"]] != row["class"]:
            raise ModulePathPolicyError(f"module-path census site {site!r} class/call mismatch")
        expected[site] = (row["script"], row["call"], row["class"])
    actual = _static_sites(root, _consumer_scripts(root))
    if set(expected) != set(actual):
        raise ModulePathPolicyError(
            f"module-path census/site mismatch: missing rows {sorted(set(actual) - set(expected))}; "
            f"stale rows {sorted(set(expected) - set(actual))}"
        )
    for site, (script, call, _line) in actual.items():
        if expected[site][:2] != (script, call):
            raise ModulePathPolicyError(
                f"module-path census site {site!r} records {expected[site][:2]}, "
                f"code has {(script, call)}"
            )
    return len(expected)


def policy_self_test(root: Path) -> Tuple[int, int, int]:
    """Exercise the raw language, every explicit site, and the alias table.

    Returns ``(controls, closed_skips, explicit_sites)``.  Case and filesystem
    normalization aliases are host capabilities: inability to express one is a
    closed skip because the raw exact-spelling rule still rejects it.
    """
    controls = 0
    closed_skips = 0

    validate_module_path("Blanc/Composition/Café.lean")
    controls += 1
    for raw in (
        "Blanc//X.lean",
        "Blanc/./X.lean",
        "Blanc/A/../X.lean",
        "Blanc/X.lean/",
        "/Blanc/X.lean",
    ):
        try:
            validate_module_path(raw)
        except ModulePathPolicyError:
            controls += 1
        else:
            raise ModulePathPolicyError(f"raw-path control passed unexpectedly: {raw!r}")

    census = load_census(root)
    mutated = copy.deepcopy(census)
    assert isinstance(mutated["sites"], list)
    mutated["sites"].pop(0)
    try:
        audit_census(root, mutated)
    except ModulePathPolicyError as error:
        if "census/site mismatch" not in str(error):
            raise
        controls += 1
    else:
        raise ModulePathPolicyError("census-removal control passed unexpectedly")

    explicit_rows = [
        row for row in census["sites"]  # type: ignore[index]
        if row["class"] == "explicit dereference"  # type: ignore[index]
    ]
    with tempfile.TemporaryDirectory(prefix="module-path-policy-") as directory:
        sandbox = Path(directory)
        repo = sandbox / "repo"
        blanc = repo / "Blanc"
        outside = sandbox / "outside"
        blanc.mkdir(parents=True)
        outside.mkdir()
        (blanc / "Inside.lean").write_text("def inside := True\n", encoding="utf-8")
        resolve_module_file(repo, "Blanc/Inside.lean", site="policy-positive")
        controls += 1

        external_file = outside / "External.lean"
        external_file.write_text("def external := True\n", encoding="utf-8")
        file_link = blanc / "FileLink.lean"
        file_link.symlink_to(external_file)
        try:
            resolve_module_file(repo, "Blanc/FileLink.lean", site="policy-file-symlink")
        except ModulePathPolicyError as error:
            if "symbolic-link" not in str(error):
                raise
            controls += 1
        else:
            raise ModulePathPolicyError("file-symlink control passed unexpectedly")
        file_link.unlink()

        external_dir = outside / "ExternalDir"
        external_dir.mkdir()
        (external_dir / "Nested.lean").write_text("def nested := True\n", encoding="utf-8")
        directory_link = blanc / "DirectoryLink"
        directory_link.symlink_to(external_dir, target_is_directory=True)
        try:
            walk_module_files(repo, site="policy-directory-symlink")
        except ModulePathPolicyError as error:
            if "symbolic-link" not in str(error):
                raise
            controls += 1
        else:
            raise ModulePathPolicyError("directory-symlink control passed unexpectedly")
        directory_link.unlink()

        hard_external = outside / "HardExternal.lean"
        hard_external.write_text("def hard := True\n", encoding="utf-8")
        hard_inside = blanc / "HardInside.lean"
        os.link(str(hard_external), str(hard_inside))
        if not os.path.samefile(str(hard_external), str(hard_inside)):
            raise ModulePathPolicyError("hardlink control setup did not share an inode")
        try:
            resolve_module_file(repo, "Blanc/HardInside.lean", site="policy-hardlink")
        except ModulePathPolicyError as error:
            if "hardlink" not in str(error):
                raise
            controls += 1
        else:
            raise ModulePathPolicyError("external-hardlink control passed unexpectedly")
        hard_inside.unlink()

        out_link = blanc / "Out"
        back_link = outside / "Back"
        out_link.symlink_to(outside, target_is_directory=True)
        back_link.symlink_to(blanc, target_is_directory=True)
        out_and_back = "Blanc/Out/Back/Inside.lean"
        for row in explicit_rows:
            resolver = resolve_source_file if row["call"] == "resolve_source_file" else resolve_module_file
            try:
                resolver(repo, out_and_back, site=row["id"])
            except ModulePathPolicyError as error:
                if "symbolic-link" not in str(error):
                    raise
                controls += 1
            else:
                raise ModulePathPolicyError(
                    f"out-and-back control passed at explicit site {row['id']!r}"
                )
        back_link.unlink()
        out_link.unlink()

        case_file = blanc / "CaseFile.lean"
        case_file.write_text("def caseFile := True\n", encoding="utf-8")
        case_alias = "Blanc/casefile.lean"
        if os.path.exists(str(repo / case_alias)):
            try:
                resolve_module_file(repo, case_alias, site="policy-case-alias")
            except ModulePathPolicyError as error:
                if "exact directory entry" not in str(error):
                    raise
            else:
                raise ModulePathPolicyError("wrong-case alias control passed unexpectedly")
        else:
            closed_skips += 1
        controls += 1

        nfc_name = "Café.lean"
        nfd_name = unicodedata.normalize("NFD", nfc_name)
        (blanc / nfc_name).write_text("def café := True\n", encoding="utf-8")
        nfd_alias = f"Blanc/{nfd_name}"
        alias_expressible = os.path.exists(str(repo / nfd_alias))
        try:
            resolve_module_file(repo, nfd_alias, site="policy-normalization-alias")
        except ModulePathPolicyError as error:
            if "NFC" not in str(error):
                raise
        else:
            raise ModulePathPolicyError("NFD alias control passed unexpectedly")
        if not alias_expressible:
            closed_skips += 1
        controls += 1

    return controls, closed_skips, len(explicit_rows)
