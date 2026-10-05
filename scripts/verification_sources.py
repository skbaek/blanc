#!/usr/bin/env python3
"""Inventory of verification Lean sources (discovery only, no attribution).

Discovers ``scripts/**/*.lean`` (exact ``.lean`` suffix) plus
repository-root ``*.lean`` files except ``Blanc.lean``, which is the library
root and an architectural population boundary, not a verification source.
``Main.lean`` and ``lakefile.lean`` stay inventoried with informational
``source`` role; a later collector selects meaningful consumers.
``scripts/**/*.lean.in`` templates are inventoried separately and
``scripts/fixtures/**`` files get their own ``fixture`` role. The generated
list supplies later admitted elaboration collectors; this unit infers no
term dependencies and makes no executable-use claims.

Each record: repository-relative POSIX path, SHA256 of the exact file
bytes, ``source``/``template``/``fixture`` role (informational only: never
a keep-alive or deletion permission), and ``declared_gate_inputs`` -- the
sorted gate IDs whose ``gate-registry.json`` ``inputs.files`` list the path
literally (a declaration, not an executable-runner claim).

Fail-closed: malformed registry, unreadable tree, a ``scripts/`` source
root or ``gate-registry.json`` that is (or resolves through) an external
symlink, registry Lean entries that are absolute, escape the root, or
resolve outside it through a symlink, source symlinks escaping the root,
symlink source directories, dangling or unreadable root candidates, and a
root ``*.lean`` name that is a directory all raise ``VerificationSourcesError``
(never a misleading all-clean verdict, never external bytes read).
Symlink cycles yield named errors: resolution catches ``RuntimeError`` as
well as ``OSError``. ``.lake``/``.git``/``.worktrees`` subtrees are skipped:
not inventoried and not an error.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import posixpath
import sys
from pathlib import Path
from typing import Dict, List

REGISTRY_REL = Path("scripts/gate-registry.json")
SCRIPTS_REL = Path("scripts")
FIXTURES_PREFIX = "scripts/fixtures/"
LIBRARY_ROOT_REL = "Blanc.lean"  # library root: population boundary, never inventoried
EXCLUDED_DIRS = frozenset({".lake", ".git", ".worktrees"})


class VerificationSourcesError(Exception):
    """Discovery could not be built or trusted; never a pass."""


def _canonical_root(root: Path) -> Path:
    try:
        resolved = root.resolve(strict=True)
    except OSError as error:
        raise VerificationSourcesError(f"cannot resolve root {root}: {error}") from error
    if not resolved.is_dir():
        raise VerificationSourcesError(f"root is not a directory: {root}")
    return resolved


def _resolve_link(path: Path, label: str) -> Path:
    """Resolve a possibly-symlinked path; cycles yield named errors too."""
    try:
        return path.resolve()
    except (OSError, RuntimeError) as error:
        raise VerificationSourcesError(f"cannot resolve {label}: {error}") from error


def _check_registry_entry(canonical: Path, gid: str, entry: str, normalized: str) -> None:
    target = canonical / normalized
    if os.path.lexists(target):
        resolved = _resolve_link(
            target, f"registry gate {gid!r} Lean path {entry!r}"
        )
        try:
            resolved.relative_to(canonical)
        except ValueError:
            raise VerificationSourcesError(
                f"registry gate {gid!r} declares Lean path escaping root via symlink: {entry!r}"
            ) from None


def _load_declared_inputs(canonical: Path) -> Dict[str, List[str]]:
    """Map normalized repo-relative Lean path -> sorted declaring gate IDs."""
    registry_path = canonical / REGISTRY_REL
    if os.path.islink(registry_path):
        resolved = _resolve_link(registry_path, REGISTRY_REL.as_posix())
        try:
            resolved.relative_to(canonical)
        except ValueError:
            raise VerificationSourcesError(
                f"registry {REGISTRY_REL.as_posix()} is an external symlink: refusing to read"
            ) from None
    try:
        raw = registry_path.read_bytes()
    except OSError as error:
        raise VerificationSourcesError(
            f"cannot read registry {REGISTRY_REL}: {error}"
        ) from error
    try:
        data = json.loads(raw.decode("utf-8"))
    except (ValueError, UnicodeDecodeError) as error:
        raise VerificationSourcesError(f"malformed registry JSON: {error}") from error
    if not isinstance(data, dict) or not isinstance(data.get("gates"), list):
        raise VerificationSourcesError("malformed registry: expected {\"gates\": [...]}")
    seen_ids: set = set()
    declared: Dict[str, set] = {}
    for gate in data["gates"]:
        if (
            not isinstance(gate, dict)
            or not isinstance(gate.get("id"), str)
            or not gate["id"]
            or not isinstance(gate.get("inputs"), dict)
        ):
            raise VerificationSourcesError("malformed registry: gate needs id + inputs object")
        gid = gate["id"]
        if gid in seen_ids:
            raise VerificationSourcesError(f"malformed registry: duplicate gate id {gid!r}")
        seen_ids.add(gid)
        files = gate["inputs"].get("files", [])
        if not isinstance(files, list):
            raise VerificationSourcesError(
                f"malformed registry: gate {gid!r} inputs.files is not a list"
            )
        for entry in files:
            if not isinstance(entry, str) or not entry:
                raise VerificationSourcesError(f"malformed registry: bad files entry in {gid!r}")
            if not (entry.endswith(".lean.in") or entry.endswith(".lean")):
                continue  # tools, docs, manifests: not Lean sources, ignore
            if posixpath.isabs(entry):
                raise VerificationSourcesError(
                    f"registry gate {gid!r} declares absolute Lean path {entry!r}"
                )
            normalized = posixpath.normpath(entry)
            if normalized == ".." or normalized.startswith("../"):
                raise VerificationSourcesError(
                    f"registry gate {gid!r} declares Lean path outside root: {entry!r}"
                )
            _check_registry_entry(canonical, gid, entry, normalized)
            declared.setdefault(normalized, set()).add(gid)
    return {path: sorted(gids) for path, gids in declared.items()}


def _role(repo_rel: str) -> str | None:
    if repo_rel == LIBRARY_ROOT_REL:
        return None  # library root: architectural population boundary
    if not (repo_rel.endswith(".lean.in") or repo_rel.endswith(".lean")):
        return None  # exact suffix only: foo.lean.bak is not a Lean source
    if repo_rel.startswith(FIXTURES_PREFIX):
        return "fixture"
    if repo_rel.startswith("scripts/"):
        if repo_rel.endswith(".lean.in"):
            return "template"
        return "source"
    if "/" not in repo_rel:
        return "source"  # repository-root file outside the Blanc library
    return None


def _walk_scripts(scripts_dir: Path, canonical: Path) -> List[Path]:
    """Collect exact-suffix Lean files without following symlink directories."""
    found: List[Path] = []
    stack = [scripts_dir]
    while stack:
        current = stack.pop()
        try:
            with os.scandir(current) as entries:
                batch = sorted(entries, key=lambda e: e.name)
        except OSError as error:
            raise VerificationSourcesError(f"cannot enumerate {current}: {error}") from error
        for entry in batch:
            try:
                is_link = entry.is_symlink()
                is_dir = entry.is_dir(follow_symlinks=False)
            except OSError as error:
                raise VerificationSourcesError(
                    f"cannot stat {entry.path}: {error}"
                ) from error
            if is_link and os.path.isdir(entry.path):
                rel = Path(entry.path).relative_to(canonical).as_posix()
                raise VerificationSourcesError(
                    f"unsupported symlink source directory: {rel}"
                )
            if is_dir:
                if entry.name in EXCLUDED_DIRS:
                    continue
                stack.append(Path(entry.path))
            elif entry.name.endswith(".lean.in") or entry.name.endswith(".lean"):
                found.append(Path(entry.path))
    return sorted(found)


def discover(root: str | Path) -> List[Dict[str, object]]:
    """Inventory verification sources under *root*. Returns path-sorted records."""
    canonical = _canonical_root(Path(root))
    scripts_dir = canonical / SCRIPTS_REL
    if os.path.islink(scripts_dir):
        raise VerificationSourcesError(
            f"scripts/ source root is a symlink, refusing enumeration: {SCRIPTS_REL.as_posix()}"
        )
    if not scripts_dir.is_dir():
        raise VerificationSourcesError("missing scripts/ population: no sources to report")
    declared = _load_declared_inputs(canonical)
    candidates: List[Path] = _walk_scripts(scripts_dir, canonical)
    try:
        root_names = sorted(os.listdir(canonical))
    except OSError as error:
        raise VerificationSourcesError(f"cannot enumerate repository root: {error}") from error
    for name in root_names:
        if not name.endswith(".lean"):
            continue
        candidate = canonical / name
        if os.path.isdir(candidate):
            raise VerificationSourcesError(
                f"root candidate is a directory, not a file: {name}"
            )
        candidates.append(candidate)

    records: Dict[str, Dict[str, object]] = {}
    for path in candidates:
        repo_rel = path.relative_to(canonical).as_posix()
        if any(part in EXCLUDED_DIRS for part in Path(repo_rel).parts):
            continue  # .lake / .git / .worktrees subtrees skipped, never inventoried
        role = _role(repo_rel)
        if role is None:
            continue
        if repo_rel in records:
            continue  # each file inventoried once
        if os.path.islink(path):
            resolved = _resolve_link(path, f"symlink source {repo_rel}")
            try:
                resolved.relative_to(canonical)
            except ValueError:
                raise VerificationSourcesError(
                    f"symlink source escapes repository root: {repo_rel}"
                ) from None
        try:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError as error:
            raise VerificationSourcesError(f"cannot read {repo_rel}: {error}") from error
        records[repo_rel] = {
            "path": repo_rel,
            "sha256": digest,
            "role": role,
            "declared_gate_inputs": declared.get(posixpath.normpath(repo_rel), []),
        }
    ordered = [records[key] for key in sorted(records)]
    if not ordered:
        raise VerificationSourcesError("no verification sources discovered: refusing all-clean")
    return ordered


def main(argv: List[str] | None = None) -> int:
    default_root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description="Inventory verification Lean sources.")
    parser.add_argument("--root", default=str(default_root), help="repository root")
    args = parser.parse_args(argv)
    try:
        sources = discover(args.root)
    except VerificationSourcesError as error:
        print(f"verification-sources: error: {error}", file=sys.stderr)
        return 1
    json.dump({"sources": sources}, sys.stdout, indent=2, sort_keys=False)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
