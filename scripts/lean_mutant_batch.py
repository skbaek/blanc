"""Batched Lean mutant runs with per-mutant diagnostic attribution.

A gate that shows a Lean mutant fails used to elaborate the whole fixture once
per mutant. Lean keeps elaborating after a failed declaration, so every mutant
can share one elaboration of one copy: this module inserts all of them, maps
each inserted snippet to its line span, and attributes every reported error to
the span it falls in. A mutant passes only when an error inside its own span
carries its pinned diagnostic; any error outside every span (the fixture itself
broke) and any mutant without such an error (it compiled) fail the batch.

The verdict is at least as strict as the per-mutant runs it replaces: those
accepted a pinned diagnostic anywhere in the output, this requires it inside
the mutant's own lines.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

# Lean 4.34 may tag a severity with its message kind, e.g.
# `error(lean.unknownIdentifier):`; an untagged `error:` is the other form.
_ERROR_HEAD = re.compile(r"^(?:.*?):(\d+):(\d+): error(?:\([^)]*\))?: ?(.*)$")
_ANY_HEAD = re.compile(r"^(?:.*?):(\d+):(\d+): (?:error|warning|info)(?:\([^)]*\))?: ?")


@dataclass(frozen=True)
class Mutant:
    marker: str
    snippet: str
    diagnostics: tuple[str, ...]
    require_all: bool = False
    keep_marker: bool = False


def insert(source: str, mutants: list[Mutant]) -> tuple[str, dict[str, tuple[int, int]]]:
    """Insert every mutant at its unique marker; return text and 1-based spans."""
    located = []
    for mutant in mutants:
        if source.count(mutant.marker) != 1:
            raise ValueError(f"marker absent or duplicated: {mutant.marker}")
        located.append((source.index(mutant.marker), mutant))
    located.sort(key=lambda item: item[0])
    pieces: list[str] = []
    spans: dict[str, tuple[int, int]] = {}
    cursor = 0
    lines_so_far = 0
    for position, mutant in located:
        before = source[cursor:position]
        pieces.append(before)
        lines_so_far += before.count("\n")
        snippet = mutant.snippet if mutant.snippet.endswith("\n") else mutant.snippet + "\n"
        start = lines_so_far + 1
        end = start + snippet.count("\n") - 1
        spans[mutant.marker] = (start, end)
        pieces.append(snippet)
        lines_so_far += snippet.count("\n")
        if mutant.keep_marker:
            pieces.append(mutant.marker)
        cursor = position + len(mutant.marker)
    pieces.append(source[cursor:])
    return "".join(pieces), spans


def errors(output: str) -> list[tuple[int, str]]:
    """Every `file:line:col: error:` diagnostic with its continuation lines."""
    found: list[tuple[int, str]] = []
    current: list | None = None
    for line in output.splitlines():
        head = _ERROR_HEAD.match(line)
        if head:
            current = [int(head.group(1)), head.group(3)]
            found.append(current)  # type: ignore[arg-type]
            continue
        if _ANY_HEAD.match(line):
            current = None
            continue
        if current is not None:
            current[1] += "\n" + line
    return [(line, message) for line, message in found]


def verdict(output: str, returncode: int, mutants: list[Mutant],
            spans: dict[str, tuple[int, int]]) -> list[str]:
    """Failures of the batch; empty when every mutant failed for its reason."""
    problems: list[str] = []
    reported = errors(output)
    if returncode == 0:
        problems.append("the batched mutant file compiled")
    for line, message in reported:
        if not any(start <= line <= end for start, end in spans.values()):
            first = message.splitlines()[0] if message else ""
            problems.append(f"error outside every mutant (line {line}): {first}")
    for mutant in mutants:
        start, end = spans[mutant.marker]
        inside = [message for line, message in reported if start <= line <= end]
        if not inside:
            problems.append(f"mutant `{mutant.marker}` unexpectedly compiled")
            continue
        text = "\n".join(inside)
        hit = (all if mutant.require_all else any)(d in text for d in mutant.diagnostics)
        if not hit:
            problems.append(f"mutant `{mutant.marker}` failed unexpectedly: "
                            + inside[0].splitlines()[0])
    return problems
