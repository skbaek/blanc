#!/usr/bin/env python3
"""Report high-confidence proof-recipe anti-patterns in changed declarations.

Every run first executes ``generate-proof-recipes.py --check``. Registry/schema,
symbol, and generated-surface drift is therefore a blocking integrity failure.
The two source findings remain report-only:

* a changed declaration whose bytes match a declaration in a transitively
  imported local Blanc module after replacing only the declaration name and
  removing declaration-boundary documentation trivia; and
* a new ``List B256`` selector table with at least three selector/literal rows,
  outside the registry-declared owner of ``local-selector-table``.

Near-duplicates are intentionally invisible. The exact-copy detector also
requires five substantive lines and 160 bytes after normalization, avoiding
accidental matches among tiny wrapper declarations.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


ROOT = pathlib.Path(__file__).resolve().parent.parent
GENERATOR_REL = pathlib.Path("scripts/generate-proof-recipes.py")
REGISTRY_REL = pathlib.Path("scripts/proof-recipes.toml")
EXCEPTIONS_REL = pathlib.Path("scripts/proof-recipe-exceptions.json")
MIN_COPY_BYTES = 160
MIN_COPY_LINES = 5
SCHEMA_VERSION = 1

DECL_KINDS = {
    "abbrev", "axiom", "class", "def", "inductive", "instance", "lemma",
    "opaque", "structure", "theorem",
}
DECL_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
NAME_PART = r"[A-Za-z_][A-Za-z0-9_'?!]*"
QUALIFIED = rf"{NAME_PART}(?:\.{NAME_PART})*"
DECL_RE = re.compile(
    rf"^(?P<indent>\s*){DECL_MODIFIERS}"
    rf"(?P<kind>{'|'.join(sorted(DECL_KINDS))})\s+"
    rf"(?P<name>{QUALIFIED})(?=\s|:|\{{|\(|$)"
)
NAMESPACE_RE = re.compile(rf"^\s*namespace\s+({QUALIFIED})\s*$")
SECTION_RE = re.compile(rf"^\s*(?:noncomputable\s+)?section(?:\s+{QUALIFIED})?\s*$")
END_RE = re.compile(rf"^\s*end(?:\s+{QUALIFIED})?\s*$")
IMPORT_RE = re.compile(rf"^\s*import\s+({QUALIFIED})\s*$")
TOP_COMMAND_RE = re.compile(
    r"^(?:"
    r"namespace|section|end|open|export|attribute|set_option|variable|variables|"
    r"universe|universes|include|omit|local|scoped|syntax|macro|macro_rules|"
    r"elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|initialize|"
    r"mutual|where|#(?:check|eval|print|reduce|synth|guard|lint|align)"
    r")\b"
)
SELECTOR_TOKEN_RE = re.compile(
    r"selector\s*\"|\b0x[0-9A-Fa-f]+\b|\b[0-9]{6,}\b|"
    r"\b[A-Za-z_][A-Za-z0-9_']*Selector\b"
)
HASH_RE = re.compile(r"^[0-9a-fA-F]{7,40}$")


class GateError(RuntimeError):
    """A fail-closed integrity error."""


@dataclass(frozen=True)
class Declaration:
    file: str
    name: str
    ordinal: int
    kind: str
    start_line: int
    end_line: int
    raw: str
    normalized: bytes

    @property
    def key(self) -> Tuple[str, int]:
        return self.name, self.ordinal


@dataclass(frozen=True)
class ParsedFile:
    file: str
    imports: Tuple[str, ...]
    declarations: Tuple[Declaration, ...]


@dataclass(frozen=True)
class ChangedDeclaration:
    declaration: Declaration
    is_new: bool


@dataclass(frozen=True)
class Finding:
    kind: str
    file: str
    declaration: str
    line: int
    detail: str
    recipe_id: Optional[str]
    suppressible: bool

    @property
    def target(self) -> Tuple[str, str]:
        return self.file, self.declaration


@dataclass(frozen=True)
class RegistryInfo:
    active_ids: frozenset
    selector_recipe_id: str
    selector_status: str
    selector_owner: str


def run_command(
    command: Sequence[str], root: pathlib.Path, label: str,
    echo: bool = False,
) -> subprocess.CompletedProcess:
    result = subprocess.run(
        list(command), cwd=str(root), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if echo:
        if result.stdout:
            print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
        if result.stderr:
            print(result.stderr, end="" if result.stderr.endswith("\n") else "\n", file=sys.stderr)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise GateError(f"{label} failed (exit {result.returncode}): {detail}")
    return result


def generator_check(root: pathlib.Path) -> None:
    generator = root / GENERATOR_REL
    if not generator.is_file():
        raise GateError(f"missing recipe generator: {GENERATOR_REL}")
    run_command(
        [sys.executable, str(generator), "--root", str(root), "--check"],
        root, "proof-recipe generator --check", echo=True,
    )


def load_registry_info(root: pathlib.Path) -> RegistryInfo:
    """Reuse the already checked generator's registry model, not a second TOML dialect."""
    generator = root / GENERATOR_REL
    module_name = "blanc_proof_recipe_generator_for_gate"
    spec = importlib.util.spec_from_file_location(module_name, str(generator))
    if spec is None or spec.loader is None:
        raise GateError(f"cannot import {GENERATOR_REL}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    try:
        spec.loader.exec_module(module)
        registry = module.load_and_validate(root)
    except Exception as error:
        raise GateError(f"cannot load validated recipe registry: {error}") from error
    finally:
        sys.modules.pop(module_name, None)

    active_ids = frozenset(recipe.id for recipe in registry.recipes if recipe.status == "active")
    selectors = [
        recipe for recipe in registry.recipes
        if "local-selector-table" in recipe.anti_patterns
    ]
    if len(selectors) != 1:
        raise GateError(
            "registry must declare local-selector-table on exactly one recipe; "
            f"found {len(selectors)}"
        )
    selector = selectors[0]
    return RegistryInfo(active_ids, selector.id, selector.status, selector.owner_module)


def mask_comments_and_literals(text: str, source: str) -> str:
    """Blank comments/literals byte-for-byte, preserving newlines and offsets."""
    out = list(text)
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
            continue

        # Raw strings r#"..."#.
        if text[i] == "r":
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            if j > i + 1 and j < n and text[j] == '"':
                hashes = j - i - 1
                terminator = '"' + "#" * hashes
                end = text.find(terminator, j + 1)
                if end < 0:
                    raise GateError(f"{source}: unterminated raw string")
                stop = end + len(terminator)
                for k in range(i, stop):
                    if text[k] != "\n":
                        out[k] = " "
                i = stop
                continue

        prefix = 0
        if text[i] == '"':
            prefix = 0
        elif i + 2 < n and text[i] in "sm" and text[i + 1] == "!" and text[i + 2] == '"':
            prefix = 2
        if text[i] == '"' or prefix:
            start = i
            i += prefix + 1
            escaped = False
            while i < n:
                if escaped:
                    escaped = False
                    i += 1
                elif text[i] == "\\":
                    escaped = True
                    i += 1
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise GateError(f"{source}: unterminated string literal")
            for k in range(start, i):
                if text[k] != "\n":
                    out[k] = " "
            continue
        i += 1
    if depth:
        raise GateError(f"{source}: unterminated block comment")
    return "".join(out)


def qualify(namespace: Sequence[str], name: str) -> str:
    if name.startswith("_root_."):
        return name[len("_root_."):]
    if name == "Blanc" or name.startswith("Blanc."):
        return name
    return ".".join([*namespace, name]) if namespace else name


def trim_trailing_doc_trivia(text: str) -> str:
    """Remove only whitespace/comments following the declaration body."""
    previous = None
    current = text.rstrip()
    block = re.compile(r"/\-(?:[^-]|-(?!/)|/(?!-))*-/$", re.S)
    line = re.compile(r"--[^\n]*$", re.S)
    while current != previous:
        previous = current
        match = block.search(current)
        if match:
            current = current[:match.start()].rstrip()
            continue
        match = line.search(current)
        if match and "\n" not in current[match.start():]:
            current = current[:match.start()].rstrip()
    return current


def normalize_declaration(
    raw: str, header_offset: int, name_start: int, name_end: int,
) -> bytes:
    """Name/doc-only normalization; every other source byte remains exact."""
    prefix = raw[:header_offset]
    # Prefix contains declaration attributes/options and documentation between
    # them. Blank only comments there; attributes and options remain exact.
    masked_prefix = mask_comments_and_literals(prefix, "declaration prefix")
    kept_prefix = "".join(
        original if masked.strip() else "\n" if original.endswith("\n") else ""
        for original, masked in zip(prefix.splitlines(True), masked_prefix.splitlines(True))
    )
    body = raw[header_offset:]
    relative_start = name_start - header_offset
    relative_end = name_end - header_offset
    normalized = kept_prefix + body[:relative_start] + "$DECL" + body[relative_end:]
    normalized = trim_trailing_doc_trivia(normalized.replace("\r\n", "\n"))
    return normalized.encode("utf-8")


def parse_lean_file(text: str, rel: str) -> ParsedFile:
    masked = mask_comments_and_literals(text, rel)
    original_lines = text.splitlines(True)
    masked_lines = masked.splitlines(True)
    if len(original_lines) != len(masked_lines):
        raise GateError(f"{rel}: lexer did not preserve line structure")
    offsets: List[int] = []
    offset = 0
    for line in original_lines:
        offsets.append(offset)
        offset += len(line)

    imports: List[str] = []
    scopes: List[Tuple[str, List[str]]] = []
    headers: List[Tuple[int, re.Match, str]] = []
    boundaries: Set[int] = set()
    namespace_for_line: Dict[int, Tuple[str, ...]] = {}

    for index, line in enumerate(masked_lines):
        without_newline = line.rstrip("\r\n")
        namespace = tuple(
            part for kind, parts in scopes if kind == "namespace" for part in parts
        )
        namespace_for_line[index] = namespace
        if not without_newline.strip():
            continue
        if without_newline[0].isspace():
            continue
        if match := IMPORT_RE.fullmatch(without_newline):
            imports.append(match.group(1))
            boundaries.add(index)
            continue
        if match := NAMESPACE_RE.fullmatch(without_newline):
            scopes.append(("namespace", match.group(1).split(".")))
            boundaries.add(index)
            continue
        if SECTION_RE.fullmatch(without_newline):
            scopes.append(("section", []))
            boundaries.add(index)
            continue
        if END_RE.fullmatch(without_newline):
            if not scopes:
                raise GateError(f"{rel}:{index + 1}: unmatched end")
            scopes.pop()
            boundaries.add(index)
            continue
        match = DECL_RE.match(without_newline)
        if match:
            full_name = qualify(namespace, match.group("name"))
            headers.append((index, match, full_name))
            boundaries.add(index)
            continue
        if TOP_COMMAND_RE.match(without_newline) or without_newline.startswith("@["):
            boundaries.add(index)
            continue
        if re.match(r"^instance\s*(?:\([^)]*\)\s*)?:", without_newline):
            # Unnamed instances have no declaration identifier suitable for a
            # declaration-scoped exception. They still delimit adjacent named
            # declarations, but are outside these two high-confidence rules.
            boundaries.add(index)
            continue
        # An unindented declaration-looking keyword outside the recognized
        # grammar is ambiguous and must not disappear from the diff scanner.
        first = without_newline.split(None, 1)[0]
        if first in DECL_KINDS or first in {"private", "protected", "noncomputable", "unsafe", "partial"}:
            raise GateError(f"{rel}:{index + 1}: cannot parse top-level declaration header")
    if scopes:
        raise GateError(f"{rel}: unclosed namespace or section")

    sorted_boundaries = sorted(boundaries)
    counts: Dict[str, int] = {}
    declarations: List[Declaration] = []
    for header_line, match, full_name in headers:
        end_line = len(original_lines)
        for boundary in sorted_boundaries:
            if boundary > header_line:
                end_line = boundary
                break
        start_line = header_line
        # Attach immediately preceding attributes and scoped option wrappers;
        # intervening blank/doc lines are declaration trivia.
        cursor = header_line - 1
        candidate = header_line
        while cursor >= 0:
            stripped = masked_lines[cursor].strip()
            if not stripped:
                cursor -= 1
                continue
            if stripped.startswith("@[") or (
                stripped.startswith("set_option ") and re.search(r"\bin\s*$", stripped)
            ):
                candidate = cursor
                cursor -= 1
                continue
            break
        start_line = candidate
        raw_start = offsets[start_line]
        # Documentation/blank trivia immediately before the next top-level
        # command belongs to that boundary, not to this declaration.
        trimmed_end_line = end_line
        while trimmed_end_line > header_line + 1 and not masked_lines[trimmed_end_line - 1].strip():
            trimmed_end_line -= 1
        raw_end = offsets[trimmed_end_line] if trimmed_end_line < len(offsets) else len(text)
        raw = text[raw_start:raw_end]
        header_absolute = offsets[header_line]
        header_offset = header_absolute - raw_start
        name_start = header_offset + match.start("name")
        name_end = header_offset + match.end("name")
        counts[full_name] = counts.get(full_name, 0) + 1
        declarations.append(Declaration(
            file=rel,
            name=full_name,
            ordinal=counts[full_name],
            kind=match.group("kind"),
            start_line=start_line + 1,
            end_line=end_line,
            raw=raw,
            normalized=normalize_declaration(raw, header_offset, name_start, name_end),
        ))
    return ParsedFile(rel, tuple(imports), tuple(declarations))


def module_to_path(module: str) -> Optional[str]:
    if module == "Blanc":
        return "Blanc.lean"
    if not module.startswith("Blanc."):
        return None
    return module.replace(".", "/") + ".lean"


class SourceIndex:
    def __init__(self, root: pathlib.Path):
        self.root = root
        self.cache: Dict[str, ParsedFile] = {}

    def parse_worktree(self, rel: str) -> ParsedFile:
        if rel in self.cache:
            return self.cache[rel]
        path = self.root / rel
        if not path.is_file():
            raise GateError(f"missing local imported module: {rel}")
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise GateError(f"cannot read {rel}: {error}") from error
        parsed = parse_lean_file(text, rel)
        self.cache[rel] = parsed
        return parsed

    def transitive_imports(self, rel: str) -> Set[str]:
        result: Set[str] = set()
        visiting: Set[str] = set()

        def visit(current: str) -> None:
            if current in visiting:
                raise GateError(f"local Blanc import cycle while scanning {current}")
            visiting.add(current)
            for module in self.parse_worktree(current).imports:
                child = module_to_path(module)
                if child is None:
                    continue
                if child not in result:
                    result.add(child)
                    visit(child)
            visiting.remove(current)

        visit(rel)
        result.discard(rel)
        return result


def git_output(root: pathlib.Path, args: Sequence[str], label: str) -> str:
    return run_command(["git", *args], root, label).stdout


def changed_paths(root: pathlib.Path, base: str) -> Dict[str, Optional[str]]:
    """Map current Lean path to its base path, or None for a new file."""
    output = git_output(
        root,
        ["diff", "--name-status", "-z", "--find-renames", base, "--", "Blanc", "Blanc.lean"],
        f"git diff against {base}",
    )
    fields = output.split("\0")
    if fields and fields[-1] == "":
        fields.pop()
    changed: Dict[str, Optional[str]] = {}
    i = 0
    while i < len(fields):
        status = fields[i]
        i += 1
        code = status[0] if status else "?"
        if code in {"M", "A", "D", "T"}:
            if i >= len(fields):
                raise GateError("truncated git --name-status output")
            path = fields[i]
            i += 1
            if code != "D" and path.endswith(".lean"):
                changed[path] = None if code == "A" else path
        elif code in {"R", "C"}:
            if i + 1 >= len(fields):
                raise GateError("truncated rename/copy in git --name-status output")
            old, new = fields[i], fields[i + 1]
            i += 2
            if new.endswith(".lean"):
                changed[new] = old
        else:
            raise GateError(f"unsupported git diff status {status!r}")

    untracked = git_output(
        root,
        ["ls-files", "--others", "--exclude-standard", "-z", "--", "Blanc", "Blanc.lean"],
        "git untracked-file discovery",
    )
    for path in filter(None, untracked.split("\0")):
        if path.endswith(".lean"):
            changed[path] = None
    for path in changed:
        if not (path == "Blanc.lean" or path.startswith("Blanc/")) or ".." in pathlib.PurePosixPath(path).parts:
            raise GateError(f"unsafe changed path from Git: {path!r}")
    return changed


def git_file(root: pathlib.Path, revision: str, rel: str) -> str:
    result = subprocess.run(
        ["git", "show", f"{revision}:{rel}"], cwd=str(root), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode != 0:
        raise GateError(f"cannot read {rel} at {revision}: {result.stderr.strip()}")
    return result.stdout


def changed_declarations(
    root: pathlib.Path, base: str, index: SourceIndex,
) -> List[ChangedDeclaration]:
    result: List[ChangedDeclaration] = []
    for current_path, base_path in sorted(changed_paths(root, base).items()):
        current = index.parse_worktree(current_path)
        old_by_key: Dict[Tuple[str, int], Declaration] = {}
        if base_path is not None:
            old_text = git_file(root, base, base_path)
            old = parse_lean_file(old_text, base_path)
            old_by_key = {decl.key: decl for decl in old.declarations}
        for declaration in current.declarations:
            prior = old_by_key.get(declaration.key)
            if prior is None or prior.raw != declaration.raw:
                result.append(ChangedDeclaration(declaration, prior is None))
    return result


def substantive(normalized: bytes) -> bool:
    text = normalized.decode("utf-8")
    lines = [line for line in text.splitlines() if line.strip()]
    return len(normalized) >= MIN_COPY_BYTES and len(lines) >= MIN_COPY_LINES


def imported_copy_findings(
    changed: Sequence[ChangedDeclaration], index: SourceIndex,
) -> List[Finding]:
    findings: List[Finding] = []
    imported_cache: Dict[str, Dict[bytes, List[Declaration]]] = {}
    for item in changed:
        declaration = item.declaration
        if not substantive(declaration.normalized):
            continue
        if declaration.file not in imported_cache:
            by_normalized: Dict[bytes, List[Declaration]] = {}
            for imported in sorted(index.transitive_imports(declaration.file)):
                for candidate in index.parse_worktree(imported).declarations:
                    if substantive(candidate.normalized):
                        by_normalized.setdefault(candidate.normalized, []).append(candidate)
            imported_cache[declaration.file] = by_normalized
        matches = imported_cache[declaration.file].get(declaration.normalized, [])
        if not matches:
            continue
        origins = ", ".join(f"{match.file}:{match.name}" for match in matches)
        digest = hashlib.sha256(declaration.normalized).hexdigest()[:16]
        findings.append(Finding(
            kind="imported-identical-copy",
            file=declaration.file,
            declaration=declaration.name,
            line=declaration.start_line,
            detail=f"normalized sha256 {digest}; imported origin(s): {origins}",
            recipe_id=None,
            suppressible=True,
        ))
    return findings


def selector_row_count(raw: str) -> int:
    return len(SELECTOR_TOKEN_RE.findall(raw))


def selector_findings(
    changed: Sequence[ChangedDeclaration], registry: RegistryInfo,
) -> List[Finding]:
    findings: List[Finding] = []
    for item in changed:
        declaration = item.declaration
        if not item.is_new or declaration.file == registry.selector_owner:
            continue
        if not re.search(r"\bList\s+B256\b", declaration.raw):
            continue
        rows = selector_row_count(declaration.raw)
        if rows < 3:
            continue
        findings.append(Finding(
            kind="local-selector-table",
            file=declaration.file,
            declaration=declaration.name,
            line=declaration.start_line,
            detail=(
                f"new List B256 declaration has {rows} selector/literal rows; "
                f"canonical owner is {registry.selector_owner}"
            ),
            recipe_id=registry.selector_recipe_id,
            suppressible=False,
        ))
    return findings


EXCEPTION_FIELDS = {
    "id", "file", "declaration", "recipe_id", "boundary", "rationale",
    "alternative_or_removal_trigger", "evidence", "owner", "expires",
}


def validate_exceptions(
    path: pathlib.Path,
    findings: Sequence[Finding],
    active_recipe_ids: Set[str],
    today: Optional[dt.date] = None,
) -> Set[Tuple[str, str]]:
    if not path.is_file():
        raise GateError(f"missing exception registry: {path}")
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise GateError(f"{path}: invalid JSON: {error}") from error
    if not isinstance(document, dict) or set(document) != {"schema_version", "exceptions"}:
        raise GateError(f"{path}: expected schema_version and exceptions")
    if document["schema_version"] != SCHEMA_VERSION or not isinstance(document["exceptions"], list):
        raise GateError(f"{path}: unsupported schema or non-list exceptions")

    eligible = {finding.target for finding in findings if finding.suppressible}
    all_targets = {finding.target: finding for finding in findings}
    today = today or dt.date.today()
    seen_ids: Set[str] = set()
    seen_targets: Set[Tuple[str, str]] = set()
    suppressed: Set[Tuple[str, str]] = set()
    for number, exception in enumerate(document["exceptions"], 1):
        where = f"{path}:exception[{number}]"
        if not isinstance(exception, dict) or set(exception) != EXCEPTION_FIELDS:
            raise GateError(f"{where}: fields must be exactly {sorted(EXCEPTION_FIELDS)}")
        exception_id = exception["id"]
        file = exception["file"]
        declaration = exception["declaration"]
        if not isinstance(exception_id, str) or not exception_id:
            raise GateError(f"{where}: id must be a nonempty string")
        if exception_id in seen_ids:
            raise GateError(f"{where}: duplicate exception id {exception_id}")
        seen_ids.add(exception_id)
        if not isinstance(file, str) or not file.startswith("Blanc/") or not file.endswith(".lean"):
            raise GateError(f"{where}: file must be one exact Blanc/*.lean path")
        if not isinstance(declaration, str) or not declaration or any(mark in declaration for mark in ("*", "$file", "<all>")):
            raise GateError(f"{where}: file-wide/wildcard exceptions are forbidden")
        target = (file, declaration)
        if target in seen_targets:
            raise GateError(f"{where}: duplicate exception target {file}:{declaration}")
        seen_targets.add(target)
        recipe_id = exception["recipe_id"]
        if recipe_id not in active_recipe_ids:
            raise GateError(f"{where}: recipe_id must name an active recipe")
        if target not in eligible:
            if target in all_targets and not all_targets[target].suppressible:
                raise GateError(
                    f"{where}: planned/advisory finding cannot receive an exception"
                )
            raise GateError(f"{where}: orphan exception does not match a suppressible finding")
        try:
            expiry = dt.date.fromisoformat(exception["expires"])
        except (TypeError, ValueError) as error:
            raise GateError(f"{where}: expires must be an ISO date") from error
        if expiry < today:
            raise GateError(f"{where}: exception expired on {expiry.isoformat()}")
        for field in (
            "boundary", "rationale", "alternative_or_removal_trigger", "evidence", "owner",
        ):
            if not isinstance(exception[field], str) or not exception[field].strip():
                raise GateError(f"{where}: {field} must be a nonempty string")
        suppressed.add(target)
    return suppressed


def _write_exceptions(path: pathlib.Path, exceptions: List[dict]) -> None:
    path.write_text(
        json.dumps({"schema_version": 1, "exceptions": exceptions}, indent=2) + "\n",
        encoding="utf-8",
    )


def _exception_for(finding: Finding, recipe_id: str, expiry: dt.date) -> dict:
    return {
        "id": "fixture-exception",
        "file": finding.file,
        "declaration": finding.declaration,
        "recipe_id": recipe_id,
        "boundary": "fixture non-applicability boundary",
        "rationale": "fixture rationale",
        "alternative_or_removal_trigger": "remove when the fixture helper is upstream",
        "evidence": "fixture exact-byte evidence",
        "owner": "fixture-owner",
        "expires": expiry.isoformat(),
    }


def detector_self_test(active_recipe_id: str) -> None:
    owner_source = """namespace Blanc.Fixture

private theorem upstreamLongLemma (n : Nat) :
    (n + 0) + 0 = n := by
  rw [Nat.add_zero]
  rw [Nat.add_zero]
  have stable : n = n := rfl
  have stableAgain : n = n := stable
  have stableFinally : n = n := stableAgain
  exact stableFinally

end Blanc.Fixture
"""
    consumer_source = """import Blanc.Owner

namespace Blanc.Fixture

private theorem copiedLongLemma (n : Nat) :
    (n + 0) + 0 = n := by
  rw [Nat.add_zero]
  rw [Nat.add_zero]
  have stable : n = n := rfl
  have stableAgain : n = n := stable
  have stableFinally : n = n := stableAgain
  exact stableFinally

def localSelectors : List B256 := [
  approveSelector,
  transferSelector,
  transferFromSelector,
]

end Blanc.Fixture
"""
    with tempfile.TemporaryDirectory(prefix="proof-recipe-detectors-") as directory:
        root = pathlib.Path(directory)
        (root / "Blanc").mkdir()
        (root / "Blanc/Owner.lean").write_text(owner_source, encoding="utf-8")
        (root / "Blanc/Consumer.lean").write_text(consumer_source, encoding="utf-8")
        index = SourceIndex(root)
        parsed = index.parse_worktree("Blanc/Consumer.lean")
        changed = [ChangedDeclaration(decl, True) for decl in parsed.declarations]
        copies = imported_copy_findings(changed, index)
        if len(copies) != 1 or copies[0].declaration != "Blanc.Fixture.copiedLongLemma":
            raise GateError("self-test: imported byte-identical copy was not detected")
        registry = RegistryInfo(
            active_ids=frozenset({active_recipe_id}),
            selector_recipe_id="selector-separation",
            selector_status="planned",
            selector_owner="Blanc/CanonicalSelectors.lean",
        )
        selectors = selector_findings(changed, registry)
        if len(selectors) != 1 or selectors[0].declaration != "Blanc.Fixture.localSelectors":
            raise GateError("self-test: new local selector table was not detected")

        exception_path = root / "exceptions.json"
        today = dt.date(2026, 8, 20)
        valid = _exception_for(copies[0], active_recipe_id, today + dt.timedelta(days=1))

        expired = dict(valid)
        expired["expires"] = (today - dt.timedelta(days=1)).isoformat()
        _write_exceptions(exception_path, [expired])
        try:
            validate_exceptions(exception_path, [*copies, *selectors], {active_recipe_id}, today)
        except GateError as error:
            if "expired" not in str(error):
                raise
        else:
            raise GateError("self-test: expired exception passed")

        orphan = dict(valid)
        orphan["declaration"] = "Blanc.Fixture.missing"
        _write_exceptions(exception_path, [orphan])
        try:
            validate_exceptions(exception_path, [*copies, *selectors], {active_recipe_id}, today)
        except GateError as error:
            if "orphan" not in str(error):
                raise
        else:
            raise GateError("self-test: orphan exception passed")

        filewide = dict(valid)
        filewide["declaration"] = "*"
        _write_exceptions(exception_path, [filewide])
        try:
            validate_exceptions(exception_path, [*copies, *selectors], {active_recipe_id}, today)
        except GateError as error:
            if "file-wide" not in str(error):
                raise
        else:
            raise GateError("self-test: file-wide exception passed")

        duplicate = dict(valid)
        duplicate["id"] = "fixture-exception-2"
        _write_exceptions(exception_path, [valid, duplicate])
        try:
            validate_exceptions(exception_path, [*copies, *selectors], {active_recipe_id}, today)
        except GateError as error:
            if "duplicate exception target" not in str(error):
                raise
        else:
            raise GateError("self-test: duplicate exception passed")

        planned = _exception_for(selectors[0], active_recipe_id, today + dt.timedelta(days=1))
        _write_exceptions(exception_path, [planned])
        try:
            validate_exceptions(exception_path, [*copies, *selectors], {active_recipe_id}, today)
        except GateError as error:
            if "planned/advisory" not in str(error):
                raise
        else:
            raise GateError("self-test: planned selector finding received an exception")


def self_test(root: pathlib.Path, registry: RegistryInfo) -> None:
    # The generator owns the byte-drift fixture. Invoking its self-test here
    # proves this gate's blocking dependency remains live without mutating the
    # real generated surfaces.
    run_command(
        [sys.executable, str(root / GENERATOR_REL), "--root", str(root), "--self-test"],
        root, "proof-recipe generated-drift self-test", echo=True,
    )
    if not registry.active_ids:
        raise GateError("self-test requires at least one active recipe")
    detector_self_test(sorted(registry.active_ids)[0])
    print(
        "OK — proof-recipe gate self-test: generated drift, imported copy, selector table, "
        "and 5 exception controls passed"
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=ROOT)
    parser.add_argument("--base", default="HEAD", help="git-ish used to identify changed declarations")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()

    generator_check(root)
    registry = load_registry_info(root)
    if args.self_test:
        self_test(root, registry)
        return 0

    index = SourceIndex(root)
    changed = changed_declarations(root, args.base, index)
    findings = [
        *imported_copy_findings(changed, index),
        *selector_findings(changed, registry),
    ]
    exceptions = validate_exceptions(
        root / EXCEPTIONS_REL, findings, set(registry.active_ids)
    )
    print(f"changed declarations: {len(changed)}")
    for finding in findings:
        status = "EXCEPTED" if finding.target in exceptions else (
            "ADVISORY" if not finding.suppressible else "FINDING"
        )
        recipe = f" [{finding.recipe_id}]" if finding.recipe_id else ""
        print(
            f"  {status} {finding.kind}{recipe}: {finding.file}:{finding.line} "
            f"{finding.declaration} — {finding.detail}"
        )
    unexcepted = sum(
        finding.suppressible and finding.target not in exceptions for finding in findings
    )
    advisory = sum(not finding.suppressible for finding in findings)
    print(
        f"OK — proof-recipe gate (report-only): {len(changed)} changed declaration(s); "
        f"{unexcepted} unexcepted copy finding(s), {advisory} planned advisory finding(s)"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateError as error:
        print(f"REGRESSION — proof-recipe gate: {error}", file=sys.stderr)
        sys.exit(1)
