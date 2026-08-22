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

``--duplication`` runs a different thing in the same file: the **blocking**
whole-tree K1 duplication ratchet. K1 is the standing inventory of production
declarations that are byte-identical after the same normalization and at the
same floor, grouped into families by their normalized bytes. It is measured
over the whole ``Blanc/*.lean`` corpus rather than the changed set, compared
against a shrink-only baseline, and any rise without a matching bounded
exception exits nonzero. The report-only character of the two findings above is
unchanged and belongs to the ordinary mode alone; ``--duplication`` is reached
only through ``scripts/check-proof-duplication.sh``.

CLI contract for both modes: exit 0 if and only if the gate passes, and output
ends with one unambiguous verdict line naming which part produced it.
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
NAME_PART = r"(?:[^\W\d]|_)[\w'?!]*"
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
        if re.fullmatch(
            r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
            r"instance\s*(?:(?:\([^)]*\)|\{[^}]*\}|\[[^]]*\])\s*)*(?::.*)?",
            without_newline,
        ):
            # Unnamed instances have no declaration identifier suitable for a
            # declaration-scoped exception. Their header may continue on the
            # next line after one or more explicit/implicit binders; they still
            # delimit adjacent named declarations, but are outside these two
            # high-confidence rules.
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


# ---------------------------------------------------------------------------
# K1 duplication ratchet
#
# The ratcheted quantity is K1: whole production declarations that are
# byte-identical after this gate's own name-and-documentation normalization,
# at the same 160-byte / 5-substantive-line floor the imported-copy detector
# uses. It is computed over the whole production tree rather than the changed
# set, so it is a standing inventory rather than a diff finding.
#
# Only K1 is ratcheted. The corpus census is deliberately not: overlapping
# shingles double-count, adoption boilerplate moves it, and the frozen rule
# forbids summing kinds. K1 has none of those properties -- every site is a
# whole declaration, and a call site is not a declaration.
#
# Unlike the two source findings above, this part BLOCKS: a rise without a
# matching bounded exception exits nonzero.
# ---------------------------------------------------------------------------

DUPLICATION_BASELINE_REL = pathlib.Path("scripts/proof-duplication-baseline.json")
DUPLICATION_EXCEPTIONS_REL = pathlib.Path("scripts/proof-duplication-exceptions.json")
DUPLICATION_SCAN_ROOT = "Blanc"
DUPLICATION_BASELINE_COMMENT = (
    "K1 duplication ratchet: production declarations that are byte-identical after "
    "the proof-recipe gate's own name-and-documentation normalization, at its "
    "160-byte / 5-substantive-line floor. restated_lines is sites minus families. "
    "Shrink-only evidence, not a knob: regenerate only with "
    "scripts/check-proof-duplication.sh --write-baseline, which never raises a site "
    "count, never admits a new family, and never grandfathers a newly unparsable "
    "module. A family id is the first 16 hex digits of its own normalized_sha256; "
    "run the gate with --list to see where a family's sites currently are."
)
DUPLICATION_MODULE_RE = re.compile(r"Blanc/[A-Za-z_][A-Za-z0-9_]*\.lean\Z")
FAMILY_ID_RE = re.compile(r"[0-9a-f]{16}\Z")
FULL_DIGEST_RE = re.compile(r"[0-9a-f]{64}\Z")
SLUG_RE = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*\Z")
DUPLICATION_BASELINE_FIELDS = {
    "_comment", "schema_version", "scan_root", "min_copy_bytes", "min_copy_lines",
    "families", "sites", "restated_lines", "unparsable_modules", "entries", "digest",
}
DUPLICATION_ENTRY_FIELDS = {"id", "normalized_sha256", "sites"}
DUPLICATION_EXCEPTION_FIELDS = {
    "id", "family_id", "allowed_sites", "rationale", "evidence", "owner",
    "expires", "removal_condition",
}
DUPLICATION_RISE_KINDS = ("new-family", "family-growth")


@dataclass(frozen=True)
class DuplicationFamily:
    id: str
    digest: str
    sites: int
    locations: Tuple[str, ...]


@dataclass
class DuplicationInventory:
    modules: int
    declarations: int
    families: Dict[str, DuplicationFamily]
    unparsable: Dict[str, str]

    @property
    def sites(self) -> int:
        return sum(family.sites for family in self.families.values())

    @property
    def restated_lines(self) -> int:
        return self.sites - len(self.families)


@dataclass(frozen=True)
class DuplicationEntry:
    id: str
    digest: str
    sites: int


@dataclass
class DuplicationBaseline:
    families: Dict[str, DuplicationEntry]
    unparsable_modules: Tuple[str, ...]

    @property
    def sites(self) -> int:
        return sum(entry.sites for entry in self.families.values())

    @property
    def restated_lines(self) -> int:
        return self.sites - len(self.families)


@dataclass(frozen=True)
class DuplicationFinding:
    kind: str
    subject: str
    sites: int
    baseline_sites: Optional[int]
    detail: str


@dataclass(frozen=True)
class DuplicationImprovement:
    kind: str
    subject: str
    before: int
    after: int
    detail: str


@dataclass
class DuplicationResult:
    inventory: DuplicationInventory
    baseline: DuplicationBaseline
    findings: List[DuplicationFinding]
    improvements: List[DuplicationImprovement]
    exceptions: Dict[str, dict]

    @property
    def blocking(self) -> List[DuplicationFinding]:
        return [
            finding for finding in self.findings
            if not (finding.kind in DUPLICATION_RISE_KINDS
                    and finding.subject in self.exceptions)
        ]


def strict_json_pairs(pairs: Sequence[Tuple[str, object]]) -> dict:
    result: Dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise GateError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_strict_json(text: str, where: str):
    try:
        return json.loads(text, object_pairs_hook=strict_json_pairs)
    except json.JSONDecodeError as error:
        raise GateError(f"{where}: invalid JSON: {error}") from error


def production_modules(root: pathlib.Path) -> List[str]:
    """The ratchet's corpus.

    This mirrors ``production_modules`` in scripts/check-proof-module-size.py
    exactly -- the non-recursive ``Blanc/*.lean`` glob, sorted, and an empty
    result is an error, never an empty pass. Both gates state the same corpus
    contract, so a disagreement between their module counts is itself visible.
    """
    source = root / DUPLICATION_SCAN_ROOT
    if not source.is_dir():
        raise GateError(f"production source directory not found: {source}")
    modules = [path.relative_to(root).as_posix() for path in sorted(source.glob("*.lean"))]
    if not modules:
        raise GateError(
            f"no production {DUPLICATION_SCAN_ROOT}/*.lean modules found under {root}"
        )
    return modules


def duplication_inventory(
    root: pathlib.Path, index: Optional[SourceIndex] = None,
) -> DuplicationInventory:
    """Group every substantive production declaration by its normalized bytes."""
    index = index or SourceIndex(root)
    modules = production_modules(root)
    groups: Dict[bytes, List[Declaration]] = {}
    unparsable: Dict[str, str] = {}
    declarations = 0
    for rel in modules:
        try:
            parsed = index.parse_worktree(rel)
        except GateError as error:
            # Recorded, never silently dropped: a module this gate cannot read
            # is a hole in the census, so the pinned set of them is ratcheted
            # alongside the families themselves.
            unparsable[rel] = str(error)
            continue
        declarations += len(parsed.declarations)
        for declaration in parsed.declarations:
            if substantive(declaration.normalized):
                groups.setdefault(declaration.normalized, []).append(declaration)
    if declarations == 0:
        raise GateError(
            f"anti-vacuity: inspected 0 declarations across {len(modules)} module(s); "
            "a run that saw nothing FAILS rather than reporting zero families"
        )
    families: Dict[str, DuplicationFamily] = {}
    duplicated = 0
    for normalized, found in groups.items():
        if len(found) < 2:
            continue
        duplicated += 1
        digest = hashlib.sha256(normalized).hexdigest()
        families[digest[:16]] = DuplicationFamily(
            id=digest[:16],
            digest=digest,
            sites=len(found),
            locations=tuple(sorted(
                f"{item.file}:{item.start_line}:{item.name}" for item in found
            )),
        )
    if len(families) != duplicated:
        raise GateError("duplication family id collision at 16 hex digits")
    return DuplicationInventory(len(modules), declarations, families, unparsable)


def duplication_digest(document: dict) -> str:
    payload = {key: value for key, value in document.items() if key != "digest"}
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def duplication_document(baseline: DuplicationBaseline) -> dict:
    entries = [
        {"id": entry.id, "normalized_sha256": entry.digest, "sites": entry.sites}
        for entry in sorted(baseline.families.values(), key=lambda item: item.id)
    ]
    document = {
        "_comment": DUPLICATION_BASELINE_COMMENT,
        "schema_version": SCHEMA_VERSION,
        "scan_root": DUPLICATION_SCAN_ROOT,
        "min_copy_bytes": MIN_COPY_BYTES,
        "min_copy_lines": MIN_COPY_LINES,
        "families": len(entries),
        "sites": baseline.sites,
        "restated_lines": baseline.restated_lines,
        "unparsable_modules": list(baseline.unparsable_modules),
        "entries": entries,
    }
    document["digest"] = duplication_digest(document)
    return document


def load_duplication_baseline_text(text: str, where: str) -> DuplicationBaseline:
    raw = load_strict_json(text, where)
    if not isinstance(raw, dict) or set(raw) != DUPLICATION_BASELINE_FIELDS:
        missing = sorted(DUPLICATION_BASELINE_FIELDS - set(raw if isinstance(raw, dict) else {}))
        extra = sorted(set(raw if isinstance(raw, dict) else {}) - DUPLICATION_BASELINE_FIELDS)
        raise GateError(f"{where}: baseline fields mismatch; missing={missing}, extra={extra}")
    if raw["schema_version"] != SCHEMA_VERSION:
        raise GateError(f"{where}: baseline schema_version must be {SCHEMA_VERSION}")
    if raw["scan_root"] != DUPLICATION_SCAN_ROOT:
        raise GateError(f"{where}: baseline scan_root must be {DUPLICATION_SCAN_ROOT!r}")
    # The floor is what decides which declarations are counted at all. A
    # baseline recorded under a different floor is not comparable with this
    # code's inventory, so it is rejected rather than silently reinterpreted.
    if raw["min_copy_bytes"] != MIN_COPY_BYTES or raw["min_copy_lines"] != MIN_COPY_LINES:
        raise GateError(
            f"{where}: baseline floor {raw['min_copy_bytes']}/{raw['min_copy_lines']} "
            f"disagrees with this gate's pinned floor {MIN_COPY_BYTES}/{MIN_COPY_LINES}"
        )
    if not isinstance(raw["_comment"], str) or not raw["_comment"].strip():
        raise GateError(f"{where}: _comment must be a nonempty string")
    if raw["digest"] != duplication_digest(raw):
        raise GateError(f"{where}: recorded digest does not match the baseline contents")
    entries_raw = raw["entries"]
    if not isinstance(entries_raw, list):
        raise GateError(f"{where}: entries must be a list")
    families: Dict[str, DuplicationEntry] = {}
    previous = ""
    for index, item in enumerate(entries_raw):
        at = f"{where}:entries[{index}]"
        if not isinstance(item, dict) or set(item) != DUPLICATION_ENTRY_FIELDS:
            raise GateError(f"{at}: entry fields must be exactly {sorted(DUPLICATION_ENTRY_FIELDS)}")
        digest = item["normalized_sha256"]
        entry_id = item["id"]
        sites = item["sites"]
        if not isinstance(digest, str) or not FULL_DIGEST_RE.fullmatch(digest):
            raise GateError(f"{at}: normalized_sha256 must be 64 lowercase hex digits")
        if not isinstance(entry_id, str) or not FAMILY_ID_RE.fullmatch(entry_id):
            raise GateError(f"{at}: id must be 16 lowercase hex digits")
        if entry_id != digest[:16]:
            raise GateError(f"{at}: id does not match its fields (normalized_sha256 prefix)")
        if type(sites) is not int or sites < 2:
            raise GateError(f"{at}: sites must be an integer of at least 2")
        if entry_id in families:
            raise GateError(f"{at}: duplicate baseline family id {entry_id}")
        if entry_id <= previous:
            raise GateError(f"{where}: entries are not strictly sorted by id")
        previous = entry_id
        families[entry_id] = DuplicationEntry(entry_id, digest, sites)
    unparsable_raw = raw["unparsable_modules"]
    if not isinstance(unparsable_raw, list):
        raise GateError(f"{where}: unparsable_modules must be a list")
    unparsable: List[str] = []
    for item in unparsable_raw:
        if not isinstance(item, str) or not DUPLICATION_MODULE_RE.fullmatch(item):
            raise GateError(
                f"{where}: unparsable_modules must name concrete Blanc/*.lean modules"
            )
        unparsable.append(item)
    if tuple(sorted(unparsable)) != tuple(unparsable) or len(set(unparsable)) != len(unparsable):
        raise GateError(f"{where}: unparsable_modules must be sorted and unique")
    baseline = DuplicationBaseline(families, tuple(unparsable))
    if raw["families"] != len(families):
        raise GateError(f"{where}: recorded families disagrees with the entry list")
    if raw["sites"] != baseline.sites:
        raise GateError(f"{where}: recorded sites disagrees with the entry list")
    if raw["restated_lines"] != baseline.restated_lines:
        raise GateError(f"{where}: recorded restated_lines disagrees with the entry list")
    return baseline


def load_duplication_baseline(root: pathlib.Path) -> DuplicationBaseline:
    path = root / DUPLICATION_BASELINE_REL
    if not path.is_file():
        raise GateError(f"missing duplication baseline: {DUPLICATION_BASELINE_REL}")
    return load_duplication_baseline_text(path.read_text(encoding="utf-8"), str(path))


def duplication_findings(
    inventory: DuplicationInventory, baseline: DuplicationBaseline,
) -> Tuple[List[DuplicationFinding], List[DuplicationImprovement]]:
    findings: List[DuplicationFinding] = []
    improvements: List[DuplicationImprovement] = []
    for family_id in sorted(inventory.families):
        family = inventory.families[family_id]
        entry = baseline.families.get(family_id)
        where = ", ".join(family.locations)
        if entry is None:
            findings.append(DuplicationFinding(
                "new-family", family_id, family.sites, None,
                f"{family.sites} byte-identical site(s) with no baseline family: {where}",
            ))
        elif family.sites > entry.sites:
            findings.append(DuplicationFinding(
                "family-growth", family_id, family.sites, entry.sites,
                f"{entry.sites} -> {family.sites} byte-identical site(s): {where}",
            ))
        elif family.sites < entry.sites:
            improvements.append(DuplicationImprovement(
                "family-shrank", family_id, entry.sites, family.sites,
                f"{entry.sites} -> {family.sites} site(s): {where}",
            ))
    for family_id in sorted(baseline.families):
        if family_id not in inventory.families:
            # Documented rule: a baseline family that no longer exists in the
            # tree is the ratchet's success case, not a stale-baseline error.
            # It is reported as an improvement and the run still passes; the
            # totals are always recomputed from the tree, so a leftover entry
            # can never mask a rise. --write-baseline drops it.
            improvements.append(DuplicationImprovement(
                "family-resolved", family_id, baseline.families[family_id].sites, 0,
                "no longer present in the tree; ratchet with --write-baseline",
            ))
    for rel in sorted(inventory.unparsable):
        if rel not in baseline.unparsable_modules:
            findings.append(DuplicationFinding(
                "unparsable-module", rel, 0, None,
                f"module is outside the census and is not pinned in the baseline: "
                f"{inventory.unparsable[rel]}",
            ))
    for rel in baseline.unparsable_modules:
        if rel not in inventory.unparsable:
            improvements.append(DuplicationImprovement(
                "module-now-parsable", rel, 1, 0,
                "pinned unparsable module now parses; ratchet with --write-baseline",
            ))
    if not findings and inventory.restated_lines > baseline.restated_lines:
        raise GateError(
            "internal inconsistency: restated_lines rose "
            f"{baseline.restated_lines} -> {inventory.restated_lines} with no per-family finding"
        )
    return findings, improvements


def validate_duplication_exceptions(
    path: pathlib.Path,
    findings: Sequence[DuplicationFinding],
    today: Optional[dt.date] = None,
) -> Dict[str, dict]:
    if not path.is_file():
        raise GateError(f"missing exception registry: {path}")
    raw = load_strict_json(path.read_text(encoding="utf-8"), str(path))
    if not isinstance(raw, dict) or set(raw) != {"_comment", "schema_version", "exceptions"}:
        raise GateError(f"{path}: expected _comment, schema_version and exceptions")
    if raw["schema_version"] != SCHEMA_VERSION or not isinstance(raw["exceptions"], list):
        raise GateError(f"{path}: unsupported schema or non-list exceptions")
    if not isinstance(raw["_comment"], str) or not raw["_comment"].strip():
        raise GateError(f"{path}: _comment must be a nonempty string")
    today = today or dt.date.today()
    violations = {
        finding.subject: finding for finding in findings
        if finding.kind in DUPLICATION_RISE_KINDS
    }
    applied: Dict[str, dict] = {}
    ids: Set[str] = set()
    for index, exception in enumerate(raw["exceptions"]):
        where = f"{path}:exceptions[{index}]"
        if not isinstance(exception, dict) or set(exception) != DUPLICATION_EXCEPTION_FIELDS:
            raise GateError(
                f"{where}: fields must be exactly {sorted(DUPLICATION_EXCEPTION_FIELDS)}"
            )
        exception_id = exception["id"]
        if not isinstance(exception_id, str) or not SLUG_RE.fullmatch(exception_id):
            raise GateError(f"{where}: id must be a lowercase kebab slug")
        if exception_id in ids:
            raise GateError(f"{where}: duplicate exception id {exception_id}")
        ids.add(exception_id)
        family_id = exception["family_id"]
        if not isinstance(family_id, str) or not FAMILY_ID_RE.fullmatch(family_id):
            raise GateError(
                f"{where}: family_id must be exactly one concrete 16-hex-digit family; "
                "wildcards and file-wide selectors are forbidden"
            )
        if family_id in applied:
            raise GateError(f"{where}: duplicate exception for family {family_id}")
        finding = violations.get(family_id)
        if finding is None:
            raise GateError(
                f"{where}: orphan exception does not match a live duplication rise"
            )
        allowed = exception["allowed_sites"]
        if type(allowed) is not int or allowed != finding.sites:
            raise GateError(
                f"{where}: allowed_sites must exactly equal the current violating value "
                f"({finding.sites})"
            )
        expires_text = exception["expires"]
        if not isinstance(expires_text, str):
            raise GateError(f"{where}: expires must be a canonical YYYY-MM-DD string")
        try:
            expiry = dt.date.fromisoformat(expires_text)
        except ValueError as error:
            raise GateError(f"{where}: expires must be a canonical YYYY-MM-DD string") from error
        if expiry.isoformat() != expires_text:
            raise GateError(f"{where}: expires must be a canonical YYYY-MM-DD string")
        if expiry < today:
            raise GateError(f"{where}: exception expired on {expiry.isoformat()}")
        owner = exception["owner"]
        if not isinstance(owner, str) or not SLUG_RE.fullmatch(owner):
            raise GateError(f"{where}: owner must be a lowercase kebab slug")
        for field in ("rationale", "evidence", "removal_condition"):
            if not isinstance(exception[field], str) or not exception[field].strip():
                raise GateError(f"{where}: {field} must be a nonempty string")
        applied[family_id] = exception
    return applied


def evaluate_duplication(
    root: pathlib.Path, today: Optional[dt.date] = None,
) -> DuplicationResult:
    inventory = duplication_inventory(root)
    baseline = load_duplication_baseline(root)
    findings, improvements = duplication_findings(inventory, baseline)
    exceptions = validate_duplication_exceptions(
        root / DUPLICATION_EXCEPTIONS_REL, findings, today
    )
    return DuplicationResult(inventory, baseline, findings, improvements, exceptions)


def monotone_duplication_update(
    inventory: DuplicationInventory, previous: Optional[DuplicationBaseline],
) -> DuplicationBaseline:
    """Shrink-only writer. Bootstrap records the tree; afterwards it can only fall."""
    if previous is None:
        return DuplicationBaseline(
            {
                family.id: DuplicationEntry(family.id, family.digest, family.sites)
                for family in inventory.families.values()
            },
            tuple(sorted(inventory.unparsable)),
        )
    raised: List[str] = []
    families: Dict[str, DuplicationEntry] = {}
    for family_id in sorted(inventory.families):
        family = inventory.families[family_id]
        entry = previous.families.get(family_id)
        if entry is None:
            raised.append(f"refuses to admit a new family: {family_id} at {family.sites} site(s)")
            continue
        if family.sites > entry.sites:
            raised.append(
                f"refuses to raise sites for {family_id}: {entry.sites} -> {family.sites}"
            )
            continue
        families[family_id] = DuplicationEntry(family_id, family.digest, family.sites)
    unparsable: List[str] = []
    for rel in sorted(inventory.unparsable):
        if rel not in previous.unparsable_modules:
            raised.append(f"refuses to grandfather a newly unparsable module: {rel}")
            continue
        unparsable.append(rel)
    if raised:
        raise GateError(
            "duplication baseline writer is shrink-only:\n  " + "\n  ".join(raised)
        )
    candidate = DuplicationBaseline(families, tuple(unparsable))
    if candidate.restated_lines > previous.restated_lines:
        raise GateError(
            "duplication baseline writer refuses to raise restated_lines "
            f"{previous.restated_lines} -> {candidate.restated_lines}"
        )
    return candidate


def write_duplication_atomic(path: pathlib.Path, document: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(document, indent=2, ensure_ascii=False) + "\n"
    handle = tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", newline="", dir=str(path.parent),
        prefix=f".{path.name}.", delete=False,
    )
    temporary = pathlib.Path(handle.name)
    try:
        with handle:
            handle.write(text)
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def build_duplication_baseline(root: pathlib.Path) -> DuplicationBaseline:
    """Compute and write the shrink-only baseline. Raises rather than raising a value."""
    inventory = duplication_inventory(root)
    path = root / DUPLICATION_BASELINE_REL
    previous = load_duplication_baseline(root) if path.is_file() else None
    updated = monotone_duplication_update(inventory, previous)
    write_duplication_atomic(path, duplication_document(updated))
    return updated


def write_duplication_baseline(root: pathlib.Path) -> int:
    previous = (root / DUPLICATION_BASELINE_REL).is_file()
    updated = build_duplication_baseline(root)
    print(
        f"OK — proof duplication baseline: {len(updated.families)} K1 families, "
        f"{updated.sites} sites, {updated.restated_lines} restated lines, "
        f"{len(updated.unparsable_modules)} pinned unparsable module(s); "
        f"{'monotone baseline written' if previous else 'bootstrapped'}"
    )
    return 0


def run_duplication(root: pathlib.Path, list_families: bool = False) -> int:
    result = evaluate_duplication(root)
    inventory = result.inventory
    baseline = result.baseline
    print(
        f"duplication scan: {inventory.modules} production module(s), "
        f"{inventory.declarations} declaration(s), "
        f"{len(inventory.unparsable)} unparsable module(s)"
    )
    if list_families:
        for family_id in sorted(inventory.families):
            family = inventory.families[family_id]
            print(f"  FAMILY {family_id} x{family.sites}: {', '.join(family.locations)}")
    for finding in result.findings:
        excepted = (
            finding.kind in DUPLICATION_RISE_KINDS and finding.subject in result.exceptions
        )
        status = "EXCEPTED" if excepted else "FINDING"
        suffix = ""
        if excepted:
            exception = result.exceptions[finding.subject]
            suffix = f" [exception {exception['id']} through {exception['expires']}]"
        print(f"  {status} {finding.kind}: {finding.subject} — {finding.detail}{suffix}")
    for improvement in result.improvements:
        print(
            f"  IMPROVED {improvement.kind}: {improvement.subject} — {improvement.detail}"
        )
    blocking = result.blocking
    new_families = sum(1 for item in blocking if item.kind == "new-family")
    grown = sum(1 for item in blocking if item.kind == "family-growth")
    unreadable = sum(1 for item in blocking if item.kind == "unparsable-module")
    if blocking:
        print(
            f"REGRESSION — proof duplication ratchet: the K1 duplication ratchet FAILED "
            f"with {len(blocking)} unexcepted finding(s) "
            f"({new_families} new family/families, {grown} grown, {unreadable} newly unparsable); "
            f"sites {baseline.sites} -> {inventory.sites}, restated lines "
            f"{baseline.restated_lines} -> {inventory.restated_lines}; the recipe-copy and "
            f"selector-table checks are separate and unaffected"
        )
        return 1
    print(
        f"OK — proof duplication ratchet: {inventory.modules} module(s), "
        f"{inventory.declarations} declaration(s); {len(inventory.families)} K1 families, "
        f"{inventory.sites} site(s), {inventory.restated_lines} restated line(s) "
        f"against a baseline of {len(baseline.families)}/{baseline.sites}/"
        f"{baseline.restated_lines}; 0 unexcepted rise(s), "
        f"{len(result.improvements)} improvement(s), {len(result.exceptions)} exception(s) "
        f"applied, {len(baseline.unparsable_modules)} pinned unparsable module(s)"
    )
    return 0


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

instance (α : Type)
    (x : α) :
    Inhabited α := ⟨x⟩

private theorem copiedLongLemma₀ (n : Nat) :
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
        if len(copies) != 1 or copies[0].declaration != "Blanc.Fixture.copiedLongLemma₀":
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


DUPLICATION_CONTROL_COUNT = 18
UNPARSABLE_FIXTURE_SOURCE = """namespace Blanc.DupFixture

private theorem
    brokenHeaderLemma (n : Nat) :
    (n + 0) + 0 = n := by
  rw [Nat.add_zero]
  rw [Nat.add_zero]
  have stable : n = n := rfl
  exact stable

end Blanc.DupFixture
"""


def _dup_declaration(name: str, tag: str) -> str:
    """A substantive declaration whose normalized bytes depend only on ``tag``."""
    return (
        f"private theorem {name} (n : Nat) :\n"
        "    (n + 0) + 0 = n := by\n"
        "  rw [Nat.add_zero]\n"
        "  rw [Nat.add_zero]\n"
        f"  have step{tag} : n = n := rfl\n"
        f"  have again{tag} : n = n := step{tag}\n"
        f"  have last{tag} : n = n := again{tag}\n"
        f"  exact last{tag}\n"
    )


def _dup_module(root: pathlib.Path, name: str, declarations: Sequence[Tuple[str, str]]) -> None:
    body = "\n".join(_dup_declaration(decl, tag) for decl, tag in declarations)
    (root / "Blanc" / name).write_text(
        "namespace Blanc.DupFixture\n\n" + body + "\nend Blanc.DupFixture\n",
        encoding="utf-8",
    )


def _write_dup_exceptions(root: pathlib.Path, rows: Sequence[dict]) -> None:
    write_duplication_atomic(
        root / DUPLICATION_EXCEPTIONS_REL,
        {"_comment": "fixture registry", "schema_version": SCHEMA_VERSION,
         "exceptions": list(rows)},
    )


def _dup_exception(family_id: str, sites: int, expires: dt.date) -> dict:
    return {
        "id": "fixture-duplication-exception",
        "family_id": family_id,
        "allowed_sites": sites,
        "rationale": "fixture rationale",
        "evidence": "fixture exact-byte evidence",
        "owner": "proof-infrastructure",
        "expires": expires.isoformat(),
        "removal_condition": "remove when the fixture family is deduplicated",
    }


def _mutate_dup_baseline(root: pathlib.Path, mutate, reseal: bool) -> None:
    document = duplication_document(load_duplication_baseline(root))
    mutate(document)
    if reseal:
        document["digest"] = duplication_digest(document)
    write_duplication_atomic(root / DUPLICATION_BASELINE_REL, document)


def duplication_self_test(today: Optional[dt.date] = None) -> int:
    """Named duplication controls with an explicitly enforced count."""
    today = today or dt.date(2026, 8, 22)
    future = today + dt.timedelta(days=30)
    past = today - dt.timedelta(days=1)
    base = {
        "Alpha.lean": [("alphaOne", "A"), ("alphaTwo", "B")],
        "Beta.lean": [("betaOne", "A")],
        "Gamma.lean": [("gammaOne", "A")],
    }
    controls = 0

    def expect_error(label: str, action, expected: str) -> None:
        nonlocal controls
        try:
            action()
        except GateError as error:
            if expected not in str(error):
                raise GateError(
                    f"self-test {label}: expected {expected!r}, got {str(error)!r}"
                ) from error
        else:
            raise GateError(f"self-test {label}: invalid control passed")
        controls += 1

    def expect_blocking(label: str, root: pathlib.Path, kinds: Sequence[str]) -> DuplicationResult:
        nonlocal controls
        result = evaluate_duplication(root, today)
        observed = sorted(item.kind for item in result.blocking)
        if observed != sorted(kinds):
            raise GateError(
                f"self-test {label}: expected blocking {sorted(kinds)}, got {observed}"
            )
        controls += 1
        return result

    def expect_pass(label: str, root: pathlib.Path, improvement: Optional[str] = None) -> DuplicationResult:
        nonlocal controls
        result = evaluate_duplication(root, today)
        if result.blocking:
            raise GateError(
                f"self-test {label}: expected a pass, blocked on "
                f"{[item.kind for item in result.blocking]}"
            )
        if improvement is not None and not any(
            item.kind == improvement for item in result.improvements
        ):
            raise GateError(f"self-test {label}: expected an {improvement} improvement")
        controls += 1
        return result

    with tempfile.TemporaryDirectory(prefix="proof-duplication-") as directory:
        parent = pathlib.Path(directory)
        made = 0

        def make(modules: Dict[str, List[Tuple[str, str]]], bootstrap: bool = True) -> pathlib.Path:
            nonlocal made
            made += 1
            root = parent / f"case{made}"
            (root / "Blanc").mkdir(parents=True)
            (root / "scripts").mkdir(parents=True)
            for name, declarations in modules.items():
                _dup_module(root, name, declarations)
            _write_dup_exceptions(root, [])
            if bootstrap:
                build_duplication_baseline(root)
            return root

        # 1. rise-new-family-blocks
        new_family_root = make(base)
        _dup_module(new_family_root, "Delta.lean", [("deltaOne", "B")])
        expect_blocking("rise-new-family-blocks", new_family_root, ["new-family"])

        # 2. rise-family-growth-blocks
        growth_root = make(base)
        _dup_module(growth_root, "Delta.lean", [("deltaOne", "A")])
        growth = expect_blocking("rise-family-growth-blocks", growth_root, ["family-growth"])
        grown_family = growth.blocking[0].subject
        if growth.blocking[0].sites != 4 or growth.blocking[0].baseline_sites != 3:
            raise GateError("self-test rise-family-growth-blocks: wrong site accounting")

        # 3. fall-reported-as-improvement
        shrink_root = make(base)
        _dup_module(shrink_root, "Gamma.lean", [("gammaOne", "C")])
        expect_pass("fall-reported-as-improvement", shrink_root, "family-shrank")

        # 4. writer-refuses-raise
        expect_error(
            "writer-refuses-raise",
            lambda: build_duplication_baseline(growth_root),
            "refuses to raise sites",
        )

        # 5. writer-refuses-new-family
        expect_error(
            "writer-refuses-new-family",
            lambda: build_duplication_baseline(new_family_root),
            "refuses to admit a new family",
        )

        # 6. writer-ratchets-fall
        build_duplication_baseline(shrink_root)
        ratcheted = load_duplication_baseline(shrink_root)
        if ratcheted.sites != 2 or ratcheted.restated_lines != 1 or len(ratcheted.families) != 1:
            raise GateError("self-test writer-ratchets-fall: decrease did not ratchet down")
        expect_pass("writer-ratchets-fall", shrink_root)

        # 7. exception-expired-rejected
        _write_dup_exceptions(growth_root, [_dup_exception(grown_family, 4, past)])
        expect_error(
            "exception-expired-rejected",
            lambda: evaluate_duplication(growth_root, today),
            "expired on",
        )

        # 8. exception-orphan-rejected
        _write_dup_exceptions(growth_root, [_dup_exception("0" * 16, 4, future)])
        expect_error(
            "exception-orphan-rejected",
            lambda: evaluate_duplication(growth_root, today),
            "orphan exception",
        )

        # 9. exception-wildcard-family-id-rejected
        _write_dup_exceptions(growth_root, [_dup_exception("*", 4, future)])
        expect_error(
            "exception-wildcard-family-id-rejected",
            lambda: evaluate_duplication(growth_root, today),
            "wildcards and file-wide selectors are forbidden",
        )

        # 10. exception-allowed-sites-mismatch-rejected
        _write_dup_exceptions(growth_root, [_dup_exception(grown_family, 3, future)])
        expect_error(
            "exception-allowed-sites-mismatch-rejected",
            lambda: evaluate_duplication(growth_root, today),
            "must exactly equal the current violating value",
        )

        # 11. exception-nonslug-owner-rejected
        bad_owner = _dup_exception(grown_family, 4, future)
        bad_owner["owner"] = "Proof Infrastructure"
        _write_dup_exceptions(growth_root, [bad_owner])
        expect_error(
            "exception-nonslug-owner-rejected",
            lambda: evaluate_duplication(growth_root, today),
            "owner must be a lowercase kebab slug",
        )

        # 12. exception-suppresses-rise
        _write_dup_exceptions(growth_root, [_dup_exception(grown_family, 4, future)])
        suppressed = expect_pass("exception-suppresses-rise", growth_root)
        if len(suppressed.exceptions) != 1 or len(suppressed.findings) != 1:
            raise GateError("self-test exception-suppresses-rise: exception was not applied")
        _write_dup_exceptions(growth_root, [])

        # 13. baseline-id-disagrees-with-fields-rejected
        forged_root = make(base)

        def forge_id(document: dict) -> None:
            document["entries"][0]["id"] = "f" * 16

        _mutate_dup_baseline(forged_root, forge_id, reseal=True)
        expect_error(
            "baseline-id-disagrees-with-fields-rejected",
            lambda: load_duplication_baseline(forged_root),
            "id does not match its fields",
        )

        # 14. baseline-digest-mismatch-rejected
        tampered_root = make(base)

        def bump_sites(document: dict) -> None:
            document["entries"][0]["sites"] += 1
            document["sites"] += 1
            document["restated_lines"] += 1

        _mutate_dup_baseline(tampered_root, bump_sites, reseal=False)
        expect_error(
            "baseline-digest-mismatch-rejected",
            lambda: load_duplication_baseline(tampered_root),
            "recorded digest does not match",
        )

        # 15. baseline-floor-mismatch-rejected
        floor_root = make(base)

        def lower_floor(document: dict) -> None:
            document["min_copy_bytes"] = 1
            document["min_copy_lines"] = 1

        _mutate_dup_baseline(floor_root, lower_floor, reseal=True)
        expect_error(
            "baseline-floor-mismatch-rejected",
            lambda: load_duplication_baseline(floor_root),
            "disagrees with this gate's pinned floor",
        )

        # 16. baseline-stale-family-is-improvement
        stale_root = make(base)
        (stale_root / "Blanc/Beta.lean").unlink()
        (stale_root / "Blanc/Gamma.lean").unlink()
        stale = expect_pass("baseline-stale-family-is-improvement", stale_root, "family-resolved")
        if stale.inventory.families:
            raise GateError("self-test baseline-stale-family-is-improvement: family survived")

        # 17. unparsable-module-blocks
        broken_root = make(base)
        (broken_root / "Blanc/Broken.lean").write_text(
            UNPARSABLE_FIXTURE_SOURCE, encoding="utf-8"
        )
        expect_blocking("unparsable-module-blocks", broken_root, ["unparsable-module"])

        # 18. anti-vacuity-zero-declarations-fails
        empty_root = make({}, bootstrap=False)
        (empty_root / "Blanc/Empty.lean").write_text(
            "-- a module with no declarations at all\n", encoding="utf-8"
        )
        expect_error(
            "anti-vacuity-zero-declarations-fails",
            lambda: duplication_inventory(empty_root),
            "anti-vacuity",
        )

    if controls != DUPLICATION_CONTROL_COUNT:
        raise GateError(
            f"self-test accounting: expected {DUPLICATION_CONTROL_COUNT} duplication "
            f"controls, ran {controls}"
        )
    return controls


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
    controls = duplication_self_test()
    print(
        "OK — proof-recipe gate self-test: generated drift, anonymous-instance boundary, "
        "imported copy, selector table, and 5 exception controls passed; "
        f"duplication ratchet {controls}/{controls} controls passed"
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=ROOT)
    parser.add_argument("--base", default="HEAD", help="git-ish used to identify changed declarations")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--duplication", action="store_true",
        help="run the blocking whole-tree K1 duplication ratchet instead of the "
             "report-only changed-declaration recipe checks",
    )
    parser.add_argument(
        "--write-baseline", action="store_true",
        help=f"rewrite {DUPLICATION_BASELINE_REL.as_posix()}; shrink-only, implies --duplication",
    )
    parser.add_argument(
        "--list", action="store_true", dest="list_families",
        help="with --duplication, also print every live K1 family and its sites",
    )
    args = parser.parse_args(argv)
    root = args.root.resolve()

    if args.write_baseline or args.duplication:
        # The duplication ratchet owns its own verdict prefix so an exit code is
        # never ambiguous about which part of this file failed. Both verdicts go
        # to stdout so the verdict line is genuinely the last line of output.
        try:
            if args.write_baseline:
                if args.self_test:
                    raise GateError("--write-baseline and --self-test are mutually exclusive")
                return write_duplication_baseline(root)
            if args.self_test:
                controls = duplication_self_test()
                print(
                    f"OK — proof duplication ratchet self-test: {controls}/{controls} rise, "
                    "improvement, writer-monotonicity, exception, baseline-integrity, "
                    "unparsable-coverage and anti-vacuity controls live"
                )
                return 0
            return run_duplication(root, args.list_families)
        except GateError as error:
            print(f"REGRESSION — proof duplication ratchet: {error}")
            return 1

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
