#!/usr/bin/env python3
"""Inventory and downward-ratchet Blanc's local Lean resource overrides.

Ordinary mode never writes. New scopes and increases are findings but remain
report-only; malformed syntax, stale downward baselines, invalid exceptions,
and baseline-integrity failures are regressions. ``--write-baseline`` refreshes
the observed inventory and lowers ceilings, but can never raise one.
"""

from __future__ import annotations

import argparse
import bisect
import datetime as dt
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, replace
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


SCHEMA_VERSION = 1
TARGET_OPTIONS = ("maxHeartbeats", "maxRecDepth")
DECL_KINDS = {"theorem", "lemma", "def"}
DECL_MODIFIERS = {
    "private", "protected", "noncomputable", "unsafe", "partial",
}
BASELINE_REL = pathlib.Path("scripts/proof-debt-baseline.json")
EXCEPTIONS_REL = pathlib.Path("scripts/proof-debt-exceptions.json")
HASH_RE = re.compile(r"^[0-9a-fA-F]{7,40}$")
DECIMAL_RE = re.compile(r"^[0-9]+$")


class GateError(RuntimeError):
    """A fail-closed parser, baseline, or exception error."""


@dataclass(frozen=True)
class Token:
    text: str
    kind: str
    start: int
    end: int
    line: int
    column: int


@dataclass(frozen=True)
class Declaration:
    file: str
    name: str
    ordinal: int
    kind: str
    token_index: int
    start: int
    line: int

    @property
    def ref(self) -> str:
        suffix = "" if self.ordinal == 1 else f"#{self.ordinal}"
        return f"{self.name}{suffix}"


@dataclass(frozen=True)
class Scope:
    file: str
    declaration: Optional[str]
    declaration_ordinal: Optional[int]
    scope_kind: str
    scope_ordinal: int
    option: str
    value: int
    line: int
    anchor: Optional[str] = None

    @property
    def scope_id(self) -> str:
        owner = self.declaration if self.declaration is not None else "$ambient"
        decl_ord = self.declaration_ordinal or 0
        anchor = self.anchor or "-"
        return (
            f"{self.file}::{owner}#{decl_ord}::{self.scope_kind}::"
            f"{anchor}::{self.option}#{self.scope_ordinal}"
        )


@dataclass(frozen=True)
class BaselineEntry:
    scope_id: str
    file: str
    declaration: Optional[str]
    declaration_ordinal: Optional[int]
    scope_kind: str
    scope_ordinal: int
    option: str
    value: int
    ceiling: Optional[int]
    anchor: Optional[str]


@dataclass(frozen=True)
class Finding:
    kind: str
    scope: Scope
    ceiling: Optional[int]


def _is_ident_start(ch: str) -> bool:
    return ch == "_" or ch.isalpha() or ord(ch) >= 128


def _is_ident_continue(ch: str) -> bool:
    return (
        ch == "_" or ch == "'" or ch.isalnum() or ord(ch) >= 128
        or ch in ".?!"
    )


def lex_lean(text: str, rel: str) -> List[Token]:
    """Tokenize enough Lean syntax to find options without regex false hits.

    Comments are nested; normal/raw/interpolated strings and character literals
    are skipped as opaque literal tokens. Unknown syntax is retained as symbols,
    so attribution can reject rather than silently overlook a target option.
    """

    tokens: List[Token] = []
    i = 0
    line = 1
    column = 0
    n = len(text)

    def advance_one() -> None:
        nonlocal i, line, column
        if text[i] == "\n":
            line += 1
            column = 0
        else:
            column += 1
        i += 1

    def advance_to(end: int) -> None:
        while i < end:
            advance_one()

    def emit(start: int, start_line: int, start_col: int, kind: str) -> None:
        tokens.append(Token(text[start:i], kind, start, i, start_line, start_col))

    while i < n:
        ch = text[i]
        if ch.isspace():
            advance_one()
            continue

        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                advance_one()
            continue

        if text.startswith("/-", i):
            start_line = line
            start_col = column
            depth = 0
            while i < n:
                if text.startswith("/-", i):
                    depth += 1
                    advance_to(i + 2)
                elif text.startswith("-/", i):
                    depth -= 1
                    advance_to(i + 2)
                    if depth == 0:
                        break
                else:
                    advance_one()
            if depth != 0:
                raise GateError(
                    f"{rel}:{start_line}:{start_col + 1}: unterminated block comment"
                )
            continue

        # Lean raw string: r#"..."#, with any positive number of hashes.
        if ch == "r":
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            if j > i + 1 and j < n and text[j] == '"':
                start, start_line, start_col = i, line, column
                hashes = j - (i + 1)
                advance_to(j + 1)
                terminator = '"' + ("#" * hashes)
                end = text.find(terminator, i)
                if end < 0:
                    raise GateError(
                        f"{rel}:{start_line}:{start_col + 1}: unterminated raw string"
                    )
                advance_to(end + len(terminator))
                emit(start, start_line, start_col, "literal")
                continue

        # String and interpolated-string prefixes. Treat interpolation as opaque:
        # debt syntax hidden in generated syntax is unsupported and caught by
        # the separate command grammar, not inferred from string contents.
        prefix = 0
        if ch == '"':
            prefix = 0
        elif i + 2 < n and ch in "sm" and text[i + 1] == "!" and text[i + 2] == '"':
            prefix = 2
        if ch == '"' or prefix:
            start, start_line, start_col = i, line, column
            advance_to(i + prefix + 1)
            escaped = False
            while i < n:
                if escaped:
                    escaped = False
                    advance_one()
                elif text[i] == "\\":
                    escaped = True
                    advance_one()
                elif text[i] == '"':
                    advance_one()
                    break
                else:
                    advance_one()
            else:
                raise GateError(
                    f"{rel}:{start_line}:{start_col + 1}: unterminated string literal"
                )
            emit(start, start_line, start_col, "literal")
            continue

        if ch == "'":
            # Apostrophe is also Lean syntax (for example getElem's
            # ``xs[i]'h`` form). It is a character literal only when a closing
            # quote occurs on this physical line.
            probe = i + 1
            probe_escaped = False
            closing_quote = -1
            while probe < n and text[probe] != "\n":
                if probe_escaped:
                    probe_escaped = False
                elif text[probe] == "\\":
                    probe_escaped = True
                elif text[probe] == "'":
                    closing_quote = probe
                    break
                probe += 1
            if closing_quote < 0:
                start, start_line, start_col = i, line, column
                advance_one()
                emit(start, start_line, start_col, "symbol")
                continue
            start, start_line, start_col = i, line, column
            advance_one()
            escaped = False
            while i < n:
                if escaped:
                    escaped = False
                    advance_one()
                elif text[i] == "\\":
                    escaped = True
                    advance_one()
                elif text[i] == "'":
                    advance_one()
                    break
                elif text[i] == "\n":
                    raise GateError(
                        f"{rel}:{start_line}:{start_col + 1}: unterminated character literal"
                    )
                else:
                    advance_one()
            else:
                raise GateError(
                    f"{rel}:{start_line}:{start_col + 1}: unterminated character literal"
                )
            emit(start, start_line, start_col, "literal")
            continue

        if ch == "«":
            start, start_line, start_col = i, line, column
            advance_one()
            while i < n and text[i] != "»":
                advance_one()
            if i == n:
                raise GateError(
                    f"{rel}:{start_line}:{start_col + 1}: unterminated quoted identifier"
                )
            advance_one()
            emit(start, start_line, start_col, "quoted_ident")
            continue

        if _is_ident_start(ch):
            start, start_line, start_col = i, line, column
            advance_one()
            while i < n and _is_ident_continue(text[i]):
                advance_one()
            emit(start, start_line, start_col, "ident")
            continue

        if ch.isdigit():
            start, start_line, start_col = i, line, column
            advance_one()
            while i < n and (text[i].isalnum() or text[i] == "_"):
                advance_one()
            emit(start, start_line, start_col, "numeral")
            continue

        start, start_line, start_col = i, line, column
        advance_one()
        emit(start, start_line, start_col, "symbol")

    return tokens


def _quoted_name(token: Token) -> str:
    if token.kind == "quoted_ident":
        return token.text[1:-1]
    return token.text


def _namespace_by_line(tokens: Sequence[Token], rel: str) -> Dict[int, Tuple[str, ...]]:
    by_line: Dict[int, List[Token]] = {}
    for token in tokens:
        by_line.setdefault(token.line, []).append(token)

    current: List[str] = []
    frames: List[Tuple[str, int]] = []
    result: Dict[int, Tuple[str, ...]] = {}
    max_line = max(by_line, default=0)
    for line in range(1, max_line + 1):
        result[line] = tuple(current)
        row = by_line.get(line, [])
        if not row:
            continue
        first = row[0].text
        offset = 0
        if first == "noncomputable" and len(row) > 1 and row[1].text == "section":
            offset = 1
            first = "section"
        if first == "namespace" and len(row) > 1:
            name = _quoted_name(row[1])
            parts = tuple(part for part in name.split(".") if part)
            frames.append(("namespace", len(parts)))
            current.extend(parts)
        elif first == "section":
            frames.append(("section", 0))
        elif first == "end":
            if not frames:
                raise GateError(f"{rel}:{line}: unmatched end while indexing namespaces")
            kind, count = frames.pop()
            if kind == "namespace" and count:
                del current[-count:]
    return result


def _skip_attribute(tokens: Sequence[Token], index: int) -> int:
    if index + 1 >= len(tokens) or tokens[index].text != "@" or tokens[index + 1].text != "[":
        return index
    depth = 0
    i = index + 1
    while i < len(tokens):
        if tokens[i].text == "[":
            depth += 1
        elif tokens[i].text == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise GateError(
        f"line {tokens[index].line}: unterminated declaration attribute"
    )


def index_declarations(tokens: Sequence[Token], rel: str) -> List[Declaration]:
    namespace_at = _namespace_by_line(tokens, rel)
    line_indices: Dict[int, List[int]] = {}
    for i, token in enumerate(tokens):
        line_indices.setdefault(token.line, []).append(i)

    raw: List[Tuple[int, int, str, str]] = []
    for line, indices in sorted(line_indices.items()):
        i = indices[0]
        limit = indices[-1] + 1
        changed = True
        while changed and i < limit:
            changed = False
            j = _skip_attribute(tokens, i)
            if j != i:
                i = j
                changed = True
            while i < limit and tokens[i].text in DECL_MODIFIERS:
                i += 1
                changed = True
        if i >= limit or tokens[i].text not in DECL_KINDS or i + 1 >= len(tokens):
            continue
        name_token = tokens[i + 1]
        if name_token.kind not in {"ident", "quoted_ident"}:
            raise GateError(
                f"{rel}:{tokens[i].line}: cannot read name of {tokens[i].text} declaration"
            )
        name = _quoted_name(name_token)
        namespace = namespace_at.get(line, ())
        if name.startswith("_root_."):
            full_name = name[len("_root_."):]
        else:
            full_name = ".".join((*namespace, name)) if namespace else name
        raw.append((i, tokens[i].start, tokens[i].text, full_name))

    counts: Dict[str, int] = {}
    declarations: List[Declaration] = []
    for token_index, start, kind, name in sorted(raw, key=lambda row: row[1]):
        counts[name] = counts.get(name, 0) + 1
        declarations.append(
            Declaration(
                file=rel,
                name=name,
                ordinal=counts[name],
                kind=kind,
                token_index=token_index,
                start=start,
                line=tokens[token_index].line,
            )
        )
    return declarations


def _parse_option(tokens: Sequence[Token], index: int, rel: str) -> Tuple[str, int, bool, int]:
    token = tokens[index]
    if token.text != "set_option" or index + 2 >= len(tokens):
        raise GateError(f"{rel}:{token.line}: malformed set_option")
    option_token = tokens[index + 1]
    option = _quoted_name(option_token)
    if option in TARGET_OPTIONS and option_token.kind == "quoted_ident":
        raise GateError(
            f"{rel}:{option_token.line}: quoted spelling of {option} is unsupported"
        )
    value_token = tokens[index + 2]
    if option in TARGET_OPTIONS:
        if value_token.kind != "numeral" or not DECIMAL_RE.fullmatch(value_token.text):
            raise GateError(
                f"{rel}:{value_token.line}: {option} must use a plain decimal numeral; "
                f"found {value_token.text!r}"
            )
        value = int(value_token.text)
    else:
        value = 0
    has_in = index + 3 < len(tokens) and tokens[index + 3].text == "in"
    return option, value, has_in, index + (4 if has_in else 3)


def _resolve_wrapped_declaration(
    tokens: Sequence[Token],
    index: int,
    declarations_by_token: Dict[int, Declaration],
    rel: str,
) -> Optional[Declaration]:
    i = index
    while i < len(tokens) and tokens[i].text == "set_option":
        _option, _value, has_in, next_i = _parse_option(tokens, i, rel)
        if not has_in:
            return None
        i = next_i

    changed = True
    while changed and i < len(tokens):
        changed = False
        j = _skip_attribute(tokens, i)
        if j != i:
            i = j
            changed = True
        while i < len(tokens) and tokens[i].text in DECL_MODIFIERS:
            i += 1
            changed = True
    return declarations_by_token.get(i)


def scan_source(text: str, rel: str) -> List[Scope]:
    tokens = lex_lean(text, rel)
    for token in tokens:
        if token.text == "unlock_limits":
            raise GateError(
                f"{rel}:{token.line}: unlock_limits disables maxHeartbeats and "
                "maxRecDepth; spell both scopes explicitly so debt is attributable"
            )

    declarations = index_declarations(tokens, rel)
    decl_by_token = {decl.token_index: decl for decl in declarations}
    decl_starts = [decl.start for decl in declarations]
    raw: List[Tuple[Scope, int]] = []

    for i, token in enumerate(tokens):
        if token.text != "set_option" or i + 1 >= len(tokens):
            continue
        option_token = tokens[i + 1]
        option = _quoted_name(option_token)
        if option not in TARGET_OPTIONS:
            continue
        option, value, has_in, next_i = _parse_option(tokens, i, rel)

        if not has_in:
            j = bisect.bisect_right(decl_starts, token.start)
            anchor = declarations[j].ref if j < len(declarations) else "$eof"
            raw.append((Scope(
                file=rel,
                declaration=None,
                declaration_ordinal=None,
                scope_kind="ambient_command",
                scope_ordinal=0,
                option=option,
                value=value,
                line=token.line,
                anchor=anchor,
            ), token.start))
            continue

        wrapped = _resolve_wrapped_declaration(tokens, next_i, decl_by_token, rel)
        if wrapped is not None:
            raw.append((Scope(
                file=rel,
                declaration=wrapped.name,
                declaration_ordinal=wrapped.ordinal,
                scope_kind="command_scoped",
                scope_ordinal=0,
                option=option,
                value=value,
                line=token.line,
            ), token.start))
            continue

        if token.column == 0:
            following = tokens[next_i].text if next_i < len(tokens) else "$eof"
            raise GateError(
                f"{rel}:{token.line}: scoped {option} wraps unsupported or unnamed "
                f"command/term starting with {following!r}; cannot prove one enclosing declaration"
            )
        j = bisect.bisect_right(decl_starts, token.start) - 1
        if j < 0:
            raise GateError(
                f"{rel}:{token.line}: local {option} is not inside a named declaration"
            )
        owner = declarations[j]
        raw.append((Scope(
            file=rel,
            declaration=owner.name,
            declaration_ordinal=owner.ordinal,
            scope_kind="local_scoped",
            scope_ordinal=0,
            option=option,
            value=value,
            line=token.line,
        ), token.start))

    counters: Dict[Tuple[object, ...], int] = {}
    scopes: List[Scope] = []
    for scope, _start in sorted(raw, key=lambda pair: pair[1]):
        key = (
            scope.file,
            scope.declaration,
            scope.declaration_ordinal,
            scope.scope_kind,
            scope.anchor,
            scope.option,
        )
        counters[key] = counters.get(key, 0) + 1
        scopes.append(replace(scope, scope_ordinal=counters[key]))
    ids = [scope.scope_id for scope in scopes]
    if len(ids) != len(set(ids)):
        raise GateError(f"{rel}: internal duplicate scope identity")
    return scopes


def scan_tree(root: pathlib.Path) -> List[Scope]:
    source_root = root / "Blanc"
    if not source_root.is_dir():
        raise GateError(f"missing production source directory: {source_root}")
    files = sorted(path for path in source_root.rglob("*.lean") if path.is_file())
    if not files:
        raise GateError(f"no production Lean files found below {source_root}")
    scopes: List[Scope] = []
    for path in files:
        rel = path.relative_to(root).as_posix()
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise GateError(f"cannot read {rel}: {error}") from error
        scopes.extend(scan_source(text, rel))
    ids = [scope.scope_id for scope in scopes]
    if len(ids) != len(set(ids)):
        raise GateError("inventory contains duplicate scope identities")
    return sorted(scopes, key=lambda scope: scope.scope_id)


def _entry_from_dict(raw: object, where: str) -> BaselineEntry:
    if not isinstance(raw, dict):
        raise GateError(f"{where}: baseline entry must be an object")
    required = {
        "id", "file", "declaration", "declaration_ordinal", "scope_kind",
        "scope_ordinal", "option", "value", "ceiling",
    }
    allowed = required | {"anchor"}
    if set(raw) != required and set(raw) != allowed:
        missing = sorted(required - set(raw))
        extra = sorted(set(raw) - allowed)
        raise GateError(f"{where}: baseline entry fields mismatch; missing={missing}, extra={extra}")
    scope_kind = raw["scope_kind"]
    if scope_kind not in {"command_scoped", "local_scoped", "ambient_command"}:
        raise GateError(f"{where}: invalid scope_kind {scope_kind!r}")
    option = raw["option"]
    if option not in TARGET_OPTIONS:
        raise GateError(f"{where}: invalid option {option!r}")
    value = raw["value"]
    ceiling = raw["ceiling"]
    if type(value) is not int or value < 0:
        raise GateError(f"{where}: value must be a nonnegative integer")
    if ceiling is not None and (type(ceiling) is not int or ceiling < 0):
        raise GateError(f"{where}: ceiling must be null or a nonnegative integer")
    declaration = raw["declaration"]
    decl_ord = raw["declaration_ordinal"]
    anchor = raw.get("anchor")
    if scope_kind == "ambient_command":
        if declaration is not None or decl_ord is not None or not isinstance(anchor, str):
            raise GateError(f"{where}: ambient entry requires null declaration and string anchor")
    else:
        if not isinstance(declaration, str) or not declaration:
            raise GateError(f"{where}: declaration-scoped entry requires a declaration")
        if type(decl_ord) is not int or decl_ord < 1 or anchor is not None:
            raise GateError(f"{where}: invalid declaration ordinal/anchor")
    scope_ord = raw["scope_ordinal"]
    if type(scope_ord) is not int or scope_ord < 1:
        raise GateError(f"{where}: scope_ordinal must be positive")
    entry = BaselineEntry(
        scope_id=str(raw["id"]),
        file=str(raw["file"]),
        declaration=declaration,
        declaration_ordinal=decl_ord,
        scope_kind=scope_kind,
        scope_ordinal=scope_ord,
        option=option,
        value=value,
        ceiling=ceiling,
        anchor=anchor,
    )
    synthetic = Scope(
        file=entry.file,
        declaration=entry.declaration,
        declaration_ordinal=entry.declaration_ordinal,
        scope_kind=entry.scope_kind,
        scope_ordinal=entry.scope_ordinal,
        option=entry.option,
        value=entry.value,
        line=0,
        anchor=entry.anchor,
    )
    if entry.scope_id != synthetic.scope_id:
        raise GateError(f"{where}: id does not match its fields")
    if ceiling is not None and effective(ceiling) > effective(value):
        raise GateError(f"{where}: ceiling exceeds observed value; downward ratchet is stale")
    return entry


def load_baseline_text(text: str, where: str) -> Dict[str, BaselineEntry]:
    try:
        raw = json.loads(text)
    except json.JSONDecodeError as error:
        raise GateError(f"{where}: invalid JSON: {error}") from error
    if not isinstance(raw, dict) or set(raw) != {"schema_version", "scan_root", "entries"}:
        raise GateError(f"{where}: expected schema_version, scan_root, and entries")
    if raw["schema_version"] != SCHEMA_VERSION or raw["scan_root"] != "Blanc":
        raise GateError(f"{where}: unsupported schema version or scan root")
    if not isinstance(raw["entries"], list):
        raise GateError(f"{where}: entries must be a list")
    entries: Dict[str, BaselineEntry] = {}
    previous = ""
    for index, item in enumerate(raw["entries"]):
        entry = _entry_from_dict(item, f"{where}:entries[{index}]")
        if entry.scope_id in entries:
            raise GateError(f"{where}: duplicate baseline id {entry.scope_id}")
        if entry.scope_id <= previous:
            raise GateError(f"{where}: entries are not strictly sorted by id")
        previous = entry.scope_id
        entries[entry.scope_id] = entry
    return entries


def load_baseline(path: pathlib.Path) -> Dict[str, BaselineEntry]:
    if not path.is_file():
        raise GateError(f"missing baseline: {path}")
    return load_baseline_text(path.read_text(encoding="utf-8"), str(path))


def effective(value: int) -> float:
    return float("inf") if value == 0 else float(value)


def compare(scopes: Sequence[Scope], baseline: Dict[str, BaselineEntry]) -> Tuple[List[Finding], List[str]]:
    current = {scope.scope_id: scope for scope in scopes}
    findings: List[Finding] = []
    regressions: List[str] = []
    for scope_id, scope in current.items():
        entry = baseline.get(scope_id)
        if entry is None:
            findings.append(Finding("new", scope, None))
            continue
        if effective(scope.value) < effective(entry.value):
            regressions.append(
                f"{scope.file}:{scope.line}: {scope.option} decreased "
                f"{entry.value} -> {scope.value}; run --write-baseline to ratchet it"
            )
            continue
        ceiling = entry.ceiling
        if ceiling is None or effective(scope.value) > effective(ceiling):
            findings.append(Finding("increase", scope, ceiling))
    for scope_id, entry in baseline.items():
        if scope_id not in current:
            regressions.append(
                f"baseline scope disappeared: {scope_id}; run --write-baseline to remove it"
            )
    return findings, regressions


def baseline_document(
    scopes: Sequence[Scope],
    old: Optional[Dict[str, BaselineEntry]],
    bootstrap: bool,
) -> dict:
    entries = []
    for scope in sorted(scopes, key=lambda item: item.scope_id):
        prior = old.get(scope.scope_id) if old is not None else None
        if bootstrap:
            ceiling: Optional[int] = scope.value
        elif prior is None:
            ceiling = None
        elif prior.ceiling is None:
            ceiling = None
        elif effective(scope.value) < effective(prior.ceiling):
            ceiling = scope.value
        else:
            ceiling = prior.ceiling
        row = {
            "id": scope.scope_id,
            "file": scope.file,
            "declaration": scope.declaration,
            "declaration_ordinal": scope.declaration_ordinal,
            "scope_kind": scope.scope_kind,
            "scope_ordinal": scope.scope_ordinal,
            "option": scope.option,
            "value": scope.value,
            "ceiling": ceiling,
        }
        if scope.anchor is not None:
            row["anchor"] = scope.anchor
        entries.append(row)
    return {
        "schema_version": SCHEMA_VERSION,
        "scan_root": "Blanc",
        "entries": entries,
    }


def write_json_atomic(path: pathlib.Path, document: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(document, indent=2, ensure_ascii=False) + "\n"
    fd, temp_name = tempfile.mkstemp(prefix=path.name + ".", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def validate_monotone_against_base(
    candidate: Dict[str, BaselineEntry],
    base: Dict[str, BaselineEntry],
) -> None:
    failures = []
    for scope_id, entry in candidate.items():
        old = base.get(scope_id)
        if old is None:
            if entry.ceiling is not None:
                failures.append(f"new baseline scope has non-null ceiling: {scope_id}")
            continue
        if old.ceiling is None:
            if entry.ceiling is not None:
                failures.append(f"null ceiling was raised for {scope_id}")
        elif entry.ceiling is not None and effective(entry.ceiling) > effective(old.ceiling):
            failures.append(
                f"ceiling raised {old.ceiling} -> {entry.ceiling} for {scope_id}"
            )
    if failures:
        raise GateError("baseline is not downward-monotone:\n  " + "\n  ".join(failures))


def baseline_from_git(root: pathlib.Path, revision: str) -> Optional[Dict[str, BaselineEntry]]:
    result = subprocess.run(
        ["git", "show", f"{revision}:{BASELINE_REL.as_posix()}"],
        cwd=str(root),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        # The installation commit legitimately has no predecessor baseline.
        if "does not exist" in result.stderr or "exists on disk, but not in" in result.stderr:
            return None
        raise GateError(f"cannot read baseline from {revision}: {result.stderr.strip()}")
    return load_baseline_text(result.stdout, f"{revision}:{BASELINE_REL}")


EXCEPTION_FIELDS = {
    "id", "scope_id", "allowed_value", "owner", "expires", "review_commit",
    "profiler_evidence", "structural_reason", "recipes_considered", "removal_condition",
}


def validate_exceptions(
    path: pathlib.Path,
    findings: Sequence[Finding],
    scopes: Sequence[Scope],
    today: Optional[dt.date] = None,
) -> Dict[str, dict]:
    if not path.is_file():
        raise GateError(f"missing exception registry: {path}")
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise GateError(f"{path}: invalid JSON: {error}") from error
    if not isinstance(raw, dict) or set(raw) != {"schema_version", "exceptions"}:
        raise GateError(f"{path}: expected schema_version and exceptions")
    if raw["schema_version"] != SCHEMA_VERSION or not isinstance(raw["exceptions"], list):
        raise GateError(f"{path}: unsupported schema or non-list exceptions")

    today = today or dt.date.today()
    violations = {finding.scope.scope_id: finding for finding in findings}
    scope_map = {scope.scope_id: scope for scope in scopes}
    by_scope: Dict[str, dict] = {}
    ids = set()
    for index, exception in enumerate(raw["exceptions"]):
        where = f"{path}:exceptions[{index}]"
        if not isinstance(exception, dict) or set(exception) != EXCEPTION_FIELDS:
            raise GateError(f"{where}: exception fields must be exactly {sorted(EXCEPTION_FIELDS)}")
        exception_id = exception["id"]
        scope_id = exception["scope_id"]
        if not isinstance(exception_id, str) or not exception_id:
            raise GateError(f"{where}: id must be a nonempty string")
        if exception_id in ids:
            raise GateError(f"{where}: duplicate exception id {exception_id}")
        ids.add(exception_id)
        if not isinstance(scope_id, str) or any(mark in scope_id for mark in ("*", "$file", "::<all>")):
            raise GateError(f"{where}: file-wide/wildcard exceptions are forbidden")
        if scope_id in by_scope:
            raise GateError(f"{where}: duplicate exception for scope {scope_id}")
        scope = scope_map.get(scope_id)
        if scope is not None and scope.scope_kind == "ambient_command":
            raise GateError(f"{where}: ambient/file-wide exceptions are forbidden")
        finding = violations.get(scope_id)
        if finding is None:
            raise GateError(f"{where}: orphan exception does not match a current violation")
        allowed = exception["allowed_value"]
        if type(allowed) is not int or allowed < 0 or allowed != finding.scope.value:
            raise GateError(f"{where}: allowed_value must exactly equal the current violating value")
        try:
            expiry = dt.date.fromisoformat(exception["expires"])
        except (TypeError, ValueError) as error:
            raise GateError(f"{where}: expires must be an ISO date") from error
        if expiry < today:
            raise GateError(f"{where}: exception expired on {expiry.isoformat()}")
        if not isinstance(exception["review_commit"], str) or not HASH_RE.fullmatch(exception["review_commit"]):
            raise GateError(f"{where}: review_commit must be a 7-40 digit hexadecimal commit id")
        for field in (
            "owner", "profiler_evidence", "structural_reason", "removal_condition",
        ):
            if not isinstance(exception[field], str) or not exception[field].strip():
                raise GateError(f"{where}: {field} must be a nonempty string")
        recipes = exception["recipes_considered"]
        if not isinstance(recipes, list) or not recipes or not all(
            isinstance(item, str) and item.strip() for item in recipes
        ):
            raise GateError(f"{where}: recipes_considered must be a nonempty string list")
        by_scope[scope_id] = exception
    return by_scope


def _write_exception_file(path: pathlib.Path, exceptions: List[dict]) -> None:
    path.write_text(
        json.dumps({"schema_version": 1, "exceptions": exceptions}, indent=2) + "\n",
        encoding="utf-8",
    )


def _valid_exception(scope: Scope, expires: dt.date) -> dict:
    return {
        "id": "fixture-exception",
        "scope_id": scope.scope_id,
        "allowed_value": scope.value,
        "owner": "fixture-owner",
        "expires": expires.isoformat(),
        "review_commit": "abcdef1",
        "profiler_evidence": "fixture profile evidence",
        "structural_reason": "fixture structural reason",
        "recipes_considered": ["fixture-recipe"],
        "removal_condition": "remove when fixture is simplified",
    }


def self_test() -> None:
    fixture = r'''
namespace Fixture
/- nested comment: /- set_option maxHeartbeats 0 -/ still ignored -/
def quoted := "set_option maxRecDepth 0 in theorem nope : True := by trivial"
def rawQuoted := r#"set_option maxHeartbeats 0"#

set_option
  maxRecDepth
  4096
in
set_option maxHeartbeats 800000 in
/-- declaration documentation -/
theorem commandScoped : True := by
  trivial

theorem localScoped : True := by
  set_option
    maxRecDepth
    2048
  in
    trivial

set_option maxRecDepth 8000
end Fixture
'''
    scopes = scan_source(fixture, "Blanc/Fixture.lean")
    assert len(scopes) == 4
    assert [scope.scope_kind for scope in scopes].count("command_scoped") == 2
    assert [scope.scope_kind for scope in scopes].count("local_scoped") == 1
    assert [scope.scope_kind for scope in scopes].count("ambient_command") == 1
    assert {scope.declaration for scope in scopes if scope.scope_kind == "command_scoped"} == {
        "Fixture.commandScoped"
    }
    assert next(scope for scope in scopes if scope.scope_kind == "local_scoped").declaration == (
        "Fixture.localScoped"
    )

    base_source = "set_option maxRecDepth 4096 in\ntheorem base : True := by trivial\n"
    base_scopes = scan_source(base_source, "Blanc/Fixture.lean")
    base_doc = baseline_document(base_scopes, None, bootstrap=True)
    base = load_baseline_text(json.dumps(base_doc), "fixture baseline")

    added = scan_source(
        base_source + "set_option maxHeartbeats 1000 in\ntheorem added : True := by trivial\n",
        "Blanc/Fixture.lean",
    )
    findings, regressions = compare(added, base)
    assert not regressions and [finding.kind for finding in findings] == ["new"]

    increased = scan_source(
        base_source.replace("4096", "8192"), "Blanc/Fixture.lean"
    )
    findings, regressions = compare(increased, base)
    assert not regressions and len(findings) == 1 and findings[0].kind == "increase"

    unlimited = scan_source(
        base_source.replace("4096", "0"), "Blanc/Fixture.lean"
    )
    findings, regressions = compare(unlimited, base)
    assert not regressions and len(findings) == 1 and findings[0].kind == "increase"

    decreased = scan_source(
        base_source.replace("4096", "2048"), "Blanc/Fixture.lean"
    )
    findings, regressions = compare(decreased, base)
    assert not findings and len(regressions) == 1 and "--write-baseline" in regressions[0]
    lowered_doc = baseline_document(decreased, base, bootstrap=False)
    lowered = load_baseline_text(json.dumps(lowered_doc), "lowered fixture baseline")
    lowered_entry = next(iter(lowered.values()))
    assert lowered_entry.value == 2048 and lowered_entry.ceiling == 2048
    findings, regressions = compare(base_scopes, lowered)
    assert not regressions and len(findings) == 1 and findings[0].kind == "increase"

    for bad_source, needle in (
        ("unlock_limits in\ntheorem nope : True := by trivial\n", "unlock_limits"),
        ("set_option maxRecDepth 10 in\nnamespace Nope\nend Nope\n", "unsupported"),
        ("set_option maxRecDepth 0x10 in\ntheorem nope : True := by trivial\n", "plain decimal"),
    ):
        try:
            scan_source(bad_source, "Blanc/Bad.lean")
        except GateError as error:
            assert needle in str(error)
        else:
            raise AssertionError(f"parser accepted forbidden fixture: {bad_source!r}")

    today = dt.date(2026, 8, 20)
    with tempfile.TemporaryDirectory() as temp:
        exception_path = pathlib.Path(temp) / "exceptions.json"
        violation = findings[0]
        valid = _valid_exception(violation.scope, today + dt.timedelta(days=1))

        expired = dict(valid)
        expired["expires"] = (today - dt.timedelta(days=1)).isoformat()
        _write_exception_file(exception_path, [expired])
        try:
            validate_exceptions(exception_path, [violation], base_scopes, today=today)
        except GateError as error:
            assert "expired" in str(error)
        else:
            raise AssertionError("expired exception accepted")

        orphan = dict(valid)
        orphan["scope_id"] = "Blanc/Missing.lean::Missing#1::local_scoped::-::maxRecDepth#1"
        _write_exception_file(exception_path, [orphan])
        try:
            validate_exceptions(exception_path, [violation], base_scopes, today=today)
        except GateError as error:
            assert "orphan" in str(error)
        else:
            raise AssertionError("orphan exception accepted")

        filewide = dict(valid)
        filewide["scope_id"] = "Blanc/*.lean::*"
        _write_exception_file(exception_path, [filewide])
        try:
            validate_exceptions(exception_path, [violation], base_scopes, today=today)
        except GateError as error:
            assert "file-wide" in str(error)
        else:
            raise AssertionError("file-wide exception accepted")

        ambient_scope = next(scope for scope in scopes if scope.scope_kind == "ambient_command")
        ambient_finding = Finding("new", ambient_scope, None)
        ambient = _valid_exception(ambient_scope, today + dt.timedelta(days=1))
        _write_exception_file(exception_path, [ambient])
        try:
            validate_exceptions(exception_path, [ambient_finding], scopes, today=today)
        except GateError as error:
            assert "ambient" in str(error)
        else:
            raise AssertionError("ambient exception accepted")

    print("OK — proof-debt self-test: 12/12 parser, ratchet, and exception controls passed")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=None)
    parser.add_argument("--base", default=None, help="base revision for monotone-ceiling validation")
    parser.add_argument("--write-baseline", action="store_true", help="refresh observations and lower ceilings")
    parser.add_argument(
        "--bootstrap-baseline", action="store_true",
        help="one-time creation of the initial grandfathered baseline",
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)

    if args.self_test:
        self_test()
        return 0
    if args.write_baseline and args.bootstrap_baseline:
        parser.error("--write-baseline and --bootstrap-baseline are mutually exclusive")

    default_root = pathlib.Path(__file__).resolve().parent.parent
    root = (args.root or default_root).resolve()
    baseline_path = root / BASELINE_REL
    exceptions_path = root / EXCEPTIONS_REL
    scopes = scan_tree(root)

    if args.bootstrap_baseline:
        if baseline_path.exists():
            raise GateError(f"refusing to bootstrap over existing baseline: {baseline_path}")
        document = baseline_document(scopes, None, bootstrap=True)
        write_json_atomic(baseline_path, document)
        print(f"wrote initial grandfathered baseline: {len(scopes)} scopes")
    elif args.write_baseline:
        old = load_baseline(baseline_path)
        document = baseline_document(scopes, old, bootstrap=False)
        write_json_atomic(baseline_path, document)
        print(f"ratcheted baseline inventory: {len(scopes)} scopes")

    baseline = load_baseline(baseline_path)
    if args.base:
        old_base = baseline_from_git(root, args.base)
        if old_base is not None:
            validate_monotone_against_base(baseline, old_base)
    findings, regressions = compare(scopes, baseline)
    if regressions:
        raise GateError("baseline drift:\n  " + "\n  ".join(regressions))
    exceptions = validate_exceptions(exceptions_path, findings, scopes)

    heartbeat_count = sum(scope.option == "maxHeartbeats" for scope in scopes)
    recdepth_count = sum(scope.option == "maxRecDepth" for scope in scopes)
    files = len({scope.file for scope in scopes})
    print(
        f"inventory: {len(scopes)} scopes in {files} files "
        f"({heartbeat_count} maxHeartbeats, {recdepth_count} maxRecDepth)"
    )
    for finding in findings:
        if finding.scope.scope_id in exceptions:
            print(
                f"  EXCEPTED {finding.kind}: {finding.scope.file}:{finding.scope.line} "
                f"{finding.scope.declaration or '$ambient'} {finding.scope.option}="
                f"{finding.scope.value}"
            )
            continue
        old = "none" if finding.ceiling is None else str(finding.ceiling)
        print(
            f"  FINDING {finding.kind}: {finding.scope.file}:{finding.scope.line} "
            f"{finding.scope.declaration or '$ambient'} {finding.scope.option}="
            f"{finding.scope.value} (ceiling {old})"
        )
    unexcepted = sum(finding.scope.scope_id not in exceptions for finding in findings)
    print(
        f"OK — proof-debt (report-only): {len(scopes)} scopes inventoried; "
        f"{unexcepted} unexcepted new/increased finding(s)"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GateError as error:
        print(f"REGRESSION — proof-debt: {error}", file=sys.stderr)
        sys.exit(1)
