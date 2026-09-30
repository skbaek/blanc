#!/usr/bin/env python3
"""Compact pure-Python preview applier for Lean LSP TryThisInfo TextEdit suggestions.

Frozen interface:
- Input: actual instrumented UTF-8 source bytes and JSON object:
    {
      "schema": 1,
      "source_sha256": "<hex>",
      "edits": [
        {
          "range": {
            "start": {"line": <0-based>, "character": <UTF16>},
            "end": {"line": <0-based>, "character": <UTF16>}
          },
          "newText": "<string>"
        }
      ]
    }
- Function: preview(source_bytes, payload) -> PreviewResult(candidate_bytes, applied_edits)
- CLI: python3 scripts/simp_edits.py SOURCE EDITS_JSON
    Reads SOURCE and EDITS_JSON; NEVER overwrites any file.
    Outputs JSON {candidate_source, candidate_sha256, applied_edits}.

Conservative faithful-site guards:
- Replaced source range must begin after whitespace with a question-family tactic
  (simp?, simp!?, simpa?, simp_all?, dsimp?).
- Rejects enclosing macro invocations, by-blocks, or synthetic ranges.
- Replacement must begin with the same simp-family and explicit 'only' form,
  allowing parenthesized configs and +/- flags before 'only'.
- Rejects implicit replacements (missing 'only') or mismatched families.
- Deterministically deduplicates identical edits; rejects divergent same-span
  replacements or partially overlapping edits.
- Strictly validates integer positions, bounds, UTF-16 surrogates, and source SHA256.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Sequence, Tuple, Union

# Shared library first: reuse explicit_simp facilities from shared module
sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    from explicit_simp import CONFIG_FLAG_RE, ONLY_RE, balanced_end
except ImportError as exc:
    raise ImportError(f"simp_edits requires shared explicit_simp module: {exc}") from exc


class SimpEditError(Exception):
    """Named diagnostic failure during edit validation or preview generation."""


class PreviewResult(NamedTuple):
    """Compact return structure holding preview candidate bytes and applied edit count."""
    candidate_bytes: bytes
    applied_edits: int


# Question-family tactic head: simp_all, simpa, dsimp, simp with ? (and optional !)
QUESTION_TACTIC_RE = re.compile(
    r"^(simp_all|simpa|dsimp|simp)([!]*\?[!]*)(?![\w.'!?])"
)

# Replacement tactic head: same simp-family, optional !, no ?
REPLACEMENT_HEAD_RE = re.compile(
    r"^(simp_all|simpa|dsimp|simp)(?:[!]+)?(?![\w.'!?])"
)


@dataclass(frozen=True)
class LineInfo:
    line_index: int
    start_cp: int
    content: str
    ending: str
    utf16_to_cp: Dict[int, int]
    u16_length: int


def _is_strict_int(val: Any) -> bool:
    """Return True if val is an int and strictly not a bool."""
    return type(val) is int


def parse_lean_lines(text: str) -> List[LineInfo]:
    """Parse text into Lean/LSP lines.

    Newline semantics:
    - Only LF ('\\n') splits lines.
    - Trailing CR ('\\r') before LF is excluded from line content (CRLF line closure).
    - Character offsets inside line closure are not accessible.
    - Unicode astral characters occupy 2 UTF-16 code units; UTF-16 half-surrogate
      positions are recorded and rejected if targeted.
    """
    lines: List[LineInfo] = []
    raw_parts = text.split("\n")
    num_parts = len(raw_parts)
    cur_cp = 0

    for i, raw in enumerate(raw_parts):
        if i < num_parts - 1:
            if raw.endswith("\r"):
                content = raw[:-1]
                ending = "\r\n"
            else:
                content = raw
                ending = "\n"
        else:
            content = raw
            ending = ""

        utf16_to_cp: Dict[int, int] = {}
        u16_pos = 0
        for cp_idx, ch in enumerate(content):
            code = ord(ch)
            utf16_to_cp[u16_pos] = cp_idx
            if code >= 0x10000:
                # Astral character occupies 2 UTF-16 code units
                u16_pos += 2
            else:
                u16_pos += 1
        utf16_to_cp[u16_pos] = len(content)
        u16_length = u16_pos

        lines.append(
            LineInfo(
                line_index=i,
                start_cp=cur_cp,
                content=content,
                ending=ending,
                utf16_to_cp=utf16_to_cp,
                u16_length=u16_length,
            )
        )
        cur_cp += len(content) + len(ending)

    return lines


def _resolve_position(lines: List[LineInfo], line: int, character: int, role: str) -> int:
    """Resolve (line, character) position to an absolute codepoint offset."""
    if line < 0 or line >= len(lines):
        raise SimpEditError(
            f"{role} line {line} out of bounds (file has {len(lines)} lines)"
        )
    li = lines[line]
    if character < 0 or character > li.u16_length:
        raise SimpEditError(
            f"{role} character {character} out of bounds on line {line} (length {li.u16_length})"
        )
    if character not in li.utf16_to_cp:
        raise SimpEditError(
            f"{role} character {character} on line {line} lands on an invalid UTF-16 half-surrogate"
        )
    return li.start_cp + li.utf16_to_cp[character]


@dataclass(frozen=True)
class NormalizedEdit:
    start_cp: int
    end_cp: int
    new_text: str
    original_index: int


def _validate_faithful_site(replaced_text: str, new_text: str) -> None:
    """Enforce conservative faithful-site guards on replaced span and replacement text."""
    stripped_span = replaced_text.lstrip()
    if not stripped_span:
        raise SimpEditError("Replaced range is empty or only whitespace")

    m_orig = QUESTION_TACTIC_RE.match(stripped_span)
    if not m_orig:
        raise SimpEditError(
            f"Replaced source range does not begin with a question-family tactic (found: {stripped_span[:30]!r})"
        )
    orig_family = m_orig.group(1)

    stripped_new = new_text.lstrip()
    m_new = REPLACEMENT_HEAD_RE.match(stripped_new)
    if not m_new:
        raise SimpEditError(
            f"Replacement does not begin with a recognized simp-family tactic (found: {stripped_new[:30]!r})"
        )
    new_family = m_new.group(1)
    if new_family != orig_family:
        raise SimpEditError(
            f"Replacement tactic family '{new_family}' does not match original question tactic family '{orig_family}'"
        )

    # Scan past tactic head: allow parenthesized configs and +/- flags before 'only'
    pos = m_new.end()
    n = len(stripped_new)
    while pos < n:
        while pos < n and stripped_new[pos].isspace():
            pos += 1
        if pos >= n:
            break
        if stripped_new[pos] == "(":
            close_paren = balanced_end(stripped_new, pos, "(", ")")
            if close_paren < 0:
                raise SimpEditError("Unterminated configuration parenthesis in replacement text")
            pos = close_paren + 1
        elif stripped_new[pos] in ("+", "-"):
            flag_m = CONFIG_FLAG_RE.match(stripped_new, pos)
            if flag_m:
                pos = flag_m.end()
            else:
                raise SimpEditError(
                    f"Invalid config flag syntax in replacement text at: {stripped_new[pos:pos+20]!r}"
                )
        else:
            break

    while pos < n and stripped_new[pos].isspace():
        pos += 1

    if pos >= n or not ONLY_RE.match(stripped_new, pos):
        raise SimpEditError(
            f"Replacement must use explicit 'only' form (missing 'only' after tactic/config in {stripped_new[:40]!r})"
        )


def preview(
    source_bytes: bytes,
    payload: Union[Dict[str, Any], str, bytes],
) -> PreviewResult:
    """Generate preview candidate bytes and applied edit count.

    Fails closed with SimpEditError on any malformed input, bounds error,
    half-surrogate offset, hash mismatch, backwards/zero range, divergent
    same-span replacement, partial overlap, or unfaithful site.
    Never overwrites or mutates any input.
    """
    if not isinstance(source_bytes, bytes):
        raise SimpEditError("source_bytes must be raw bytes")

    if isinstance(payload, (str, bytes)):
        try:
            payload_dict = json.loads(payload)
        except Exception as exc:
            raise SimpEditError(f"Malformed JSON payload: {exc}")
    elif isinstance(payload, dict):
        payload_dict = payload
    else:
        raise SimpEditError("Payload must be a JSON object (dict) or JSON string/bytes")

    if not isinstance(payload_dict, dict):
        raise SimpEditError(
            f"Payload top level must be a JSON object (got {type(payload_dict).__name__})"
        )

    # Schema verification
    schema_val = payload_dict.get("schema")
    if not _is_strict_int(schema_val) or schema_val != 1:
        raise SimpEditError(
            f"Invalid or unsupported schema version: {schema_val!r} (expected integer 1)"
        )

    # Source hash verification
    expected_sha = payload_dict.get("source_sha256")
    if not isinstance(expected_sha, str):
        raise SimpEditError("Missing or non-string 'source_sha256' in payload")
    actual_sha = hashlib.sha256(source_bytes).hexdigest()
    if expected_sha.lower() != actual_sha.lower():
        raise SimpEditError(
            f"Source SHA256 mismatch: expected {expected_sha.lower()}, actual {actual_sha.lower()}"
        )

    # Decode UTF-8 source
    try:
        source_text = source_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise SimpEditError(f"Source bytes are not valid UTF-8: {exc}")

    lines = parse_lean_lines(source_text)

    # Edits verification
    raw_edits = payload_dict.get("edits")
    if not isinstance(raw_edits, list):
        raise SimpEditError("Missing or non-list 'edits' field in payload")

    parsed_edits: List[NormalizedEdit] = []
    for idx, ed in enumerate(raw_edits):
        if not isinstance(ed, dict):
            raise SimpEditError(f"Edit at index {idx} is not an object")
        new_text = ed.get("newText")
        if not isinstance(new_text, str):
            raise SimpEditError(f"Edit at index {idx} has missing or non-string 'newText'")
        try:
            new_text.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise SimpEditError(
                f"Edit at index {idx} has unencodable replacement text (contains invalid surrogates): {exc}"
            )
        rng = ed.get("range")
        if not isinstance(rng, dict):
            raise SimpEditError(f"Edit at index {idx} has missing or non-object 'range'")

        start = rng.get("start")
        end = rng.get("end")
        if not isinstance(start, dict) or not isinstance(end, dict):
            raise SimpEditError(f"Edit at index {idx} 'start' or 'end' is not an object")

        s_line, s_char = start.get("line"), start.get("character")
        e_line, e_char = end.get("line"), end.get("character")

        for name, val in [("start.line", s_line), ("start.character", s_char),
                          ("end.line", e_line), ("end.character", e_char)]:
            if not _is_strict_int(val) or val < 0:
                raise SimpEditError(
                    f"Edit at index {idx} has invalid integer position for {name}: {val!r}"
                )

        start_cp = _resolve_position(lines, s_line, s_char, f"Edit {idx} start")
        end_cp = _resolve_position(lines, e_line, e_char, f"Edit {idx} end")

        if start_cp > end_cp:
            raise SimpEditError(
                f"Edit at index {idx} has backwards range (start cp {start_cp} > end cp {end_cp})"
            )
        if start_cp == end_cp:
            raise SimpEditError(
                f"Edit at index {idx} has zero-length range (start cp {start_cp} == end cp {end_cp})"
            )

        replaced_text = source_text[start_cp:end_cp]
        _validate_faithful_site(replaced_text, new_text)

        parsed_edits.append(NormalizedEdit(start_cp, end_cp, new_text, idx))

    if not parsed_edits:
        return PreviewResult(candidate_bytes=source_bytes, applied_edits=0)

    # Deduplicate identical edits & check for divergent replacements on shared span
    # Group by (start_cp, end_cp)
    span_groups: Dict[Tuple[int, int], List[NormalizedEdit]] = {}
    for edit in parsed_edits:
        span_groups.setdefault((edit.start_cp, edit.end_cp), []).append(edit)

    deduped_edits: List[NormalizedEdit] = []
    for span, group in span_groups.items():
        first_text = group[0].new_text
        for other in group[1:]:
            if other.new_text != first_text:
                raise SimpEditError(
                    f"Divergent replacements for shared span ({span[0]}, {span[1]}): "
                    f"{first_text!r} vs {other.new_text!r}"
                )
        # Keep one representative deterministically
        deduped_edits.append(group[0])

    # Check for partially overlapping edits
    # Sort by start_cp ascending, then end_cp ascending
    deduped_edits.sort(key=lambda e: (e.start_cp, e.end_cp))
    for i in range(len(deduped_edits) - 1):
        e1 = deduped_edits[i]
        e2 = deduped_edits[i + 1]
        # Overlap occurs if max(start1, start2) < min(end1, end2)
        if max(e1.start_cp, e2.start_cp) < min(e1.end_cp, e2.end_cp):
            raise SimpEditError(
                f"Partially overlapping edits between span ({e1.start_cp}, {e1.end_cp}) "
                f"and ({e2.start_cp}, {e2.end_cp})"
            )

    # Apply edits in descending offset order
    descending_edits = sorted(deduped_edits, key=lambda e: e.start_cp, reverse=True)
    candidate_text = source_text
    for edit in descending_edits:
        candidate_text = (
            candidate_text[:edit.start_cp] + edit.new_text + candidate_text[edit.end_cp:]
        )

    try:
        candidate_bytes = candidate_text.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise SimpEditError(f"Candidate text cannot be encoded to UTF-8: {exc}")
    return PreviewResult(candidate_bytes=candidate_bytes, applied_edits=len(deduped_edits))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Pure-Python preview applier for Lean TryThisInfo TextEdit suggestions."
    )
    parser.add_argument("source", type=Path, help="Path to instrumented UTF-8 source file.")
    parser.add_argument("edits", type=Path, help="Path to edits JSON file.")
    args = parser.parse_args(argv if argv is not None else sys.argv[1:])

    source_path: Path = args.source
    edits_path: Path = args.edits

    if not source_path.is_file():
        sys.stderr.write(f"ERROR: source file does not exist: {source_path}\n")
        return 1
    if not edits_path.is_file():
        sys.stderr.write(f"ERROR: edits file does not exist: {edits_path}\n")
        return 1

    try:
        source_bytes = source_path.read_bytes()
    except OSError as exc:
        sys.stderr.write(f"ERROR: cannot read source file {source_path}: {exc}\n")
        return 1

    try:
        edits_bytes = edits_path.read_bytes()
    except OSError as exc:
        sys.stderr.write(f"ERROR: cannot read edits file {edits_path}: {exc}\n")
        return 1

    try:
        result = preview(source_bytes, edits_bytes)
    except SimpEditError as exc:
        sys.stderr.write(f"ERROR: {exc}\n")
        return 1

    output = {
        "candidate_source": result.candidate_bytes.decode("utf-8"),
        "candidate_sha256": hashlib.sha256(result.candidate_bytes).hexdigest(),
        "applied_edits": result.applied_edits,
    }
    print(json.dumps(output, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
