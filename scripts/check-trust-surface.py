#!/usr/bin/env python3
"""Fail-closed source-trust scan for Blanc's imported library closure.

The inventory is the exact transitive local import closure of ``Blanc.lean``.
Unimported Lean helpers and generators are deliberately outside this gate;
adding an import brings a module into scope immediately.

Only Lean *code* is scanned.  Comments (``--`` line comments and nested
``/- ... -/`` block comments, including ``/-- -/`` doc comments and ``/-! -/``
module docs) and the text of string, raw-string and character literals are
masked first, so prose never needs an allowlist row.  Every remaining match is
reported as its complete normalized source line and must equal a reviewed
allowlist row.

Whether ``{...}`` inside a quoted string is literal text or an interpolation
hole (code) depends on the surrounding parser, which a lexer cannot see:
``"{" ++ x ++ "}"`` and ``throwError "{f "a"} b"`` are both legal.  The file is
therefore lexed twice -- once reading every string as plain, once reading every
brace in a string as an interpolation hole -- and a character is masked only
when BOTH readings put it in a comment or literal.  Either reading hitting an
unterminated comment, string or hole is a setup failure, never a silent pass.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Iterable


# (rule, literal every match contains, pattern).  The literal is only a cheap
# prefilter; the pattern alone decides.
RULES = (
    ("S1-sorry", "sorry", re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")),
    ("S2-axiom", "axiom", re.compile(r"(?<![A-Za-z0-9_])axiom(?![A-Za-z0-9_])")),
    ("S3-opaque", "opaque", re.compile(r"(?<![A-Za-z0-9_])opaque(?![A-Za-z0-9_])")),
    ("S4-extern", "extern", re.compile(r"@\s*\[\s*extern(?:\s|\]|\()")),
    ("S5-implemented-by", "implemented_by", re.compile(r"(?<![A-Za-z0-9_])implemented_by(?![A-Za-z0-9_])")),
    ("S6-native-decide", "native_decide", re.compile(r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])")),
    ("S7-partial-def", "partial", re.compile(r"(?<![A-Za-z0-9_])partial\s+def(?![A-Za-z0-9_])")),
    ("S8-dbg-trace", "dbg_trace", re.compile(r"(?<![A-Za-z0-9_])dbg_trace(?![A-Za-z0-9_])")),
)

IMPORT = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")


# A raw string or character literal cannot start inside an identifier
# (``for"`` is not a raw string; ``h'`` is a primed name).
NOT_AFTER_IDENT = r"(?<![A-Za-z0-9_'!?\u0080-\U0010ffff])"
CHAR_LITERAL = re.compile(
    r"'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]+\}|[^\n])|[^\\'\n])'")


COMMENT_DELIM = re.compile(r"/-|-/")
STRING_SPECIAL = re.compile(r'[\\"{]')
CODE_SPECIAL = re.compile("--|/-|[\"\u00ab{}]|" + NOT_AFTER_IDENT + "(?:r#*\"|')")


NON_CODE_RUN = re.compile(b"\x00+")


class MaskError(ValueError):
    """The lexer could not classify some text as code or non-code."""


def _where(text: str, index: int) -> str:
    line = text.count("\n", 0, index) + 1
    column = index - (text.rfind("\n", 0, index) + 1) + 1
    return f"{line}:{column}"


def code_mask(text: str, interpolate: bool) -> bytes:
    """Return one byte per character: nonzero where it is Lean code under one reading.

    With ``interpolate`` false every quoted string is plain text; with it true
    every unescaped ``{`` inside a quoted string opens a hole that is lexed as
    code (nested strings, comments and braces included) up to its matching
    ``}``.  Raises MaskError on anything unterminated.
    """

    n = len(text)
    code = bytearray(b"\x01") * n

    def blank(start: int, stop: int) -> None:
        code[start:stop] = bytes(stop - start)

    def block_comment(start: int) -> int:
        depth = 0
        k = start
        while True:
            match = COMMENT_DELIM.search(text, k)
            if match is None:
                break
            k = match.end()
            if match.group() == "/-":
                depth += 1
            else:
                depth -= 1
                if depth == 0:
                    blank(start, k)
                    return k
        raise MaskError(f"{_where(text, start)}: unterminated block comment")

    def string(start: int) -> int:
        k = start + 1
        seg = start
        while True:
            match = STRING_SPECIAL.search(text, k)
            if match is None:
                break
            k = match.start()
            c = text[k]
            if c == "\\":
                k += 2
            elif c == '"':
                blank(seg, k + 1)
                return k + 1
            elif c == "{" and interpolate:
                blank(seg, k + 1)
                k = lex(k + 1, in_hole=True)
                seg = k - 1  # the hole's closing brace
            else:
                k += 1
        raise MaskError(f"{_where(text, start)}: unterminated string literal")

    def lex(start: int, in_hole: bool) -> int:
        depth = 0
        i = start
        while True:
            match = CODE_SPECIAL.search(text, i)
            if match is None:
                i = n
                break
            i = match.start()
            c = text[i]
            if text.startswith("--", i):
                end = text.find("\n", i)
                end = n if end < 0 else end
                blank(i, end)
                i = end
            elif text.startswith("/-", i):
                i = block_comment(i)
            elif c == '"':
                i = string(i)
            elif c == "r":
                j = i + 1
                while j < n and text[j] == "#":
                    j += 1
                terminator = '"' + "#" * (j - i - 1)
                end = text.find(terminator, j + 1)
                if end < 0:
                    raise MaskError(f"{_where(text, i)}: unterminated raw string literal")
                blank(i, end + len(terminator))
                i = end + len(terminator)
            elif c == "'":
                match = CHAR_LITERAL.match(text, i)
                if match:
                    blank(i, match.end())
                    i = match.end()
                else:
                    i += 1
            elif c == "\u00ab":  # «guillemet identifier»: code, opaque to lexing
                end = text.find("\u00bb", i + 1)
                if end < 0:
                    raise MaskError(f"{_where(text, i)}: unterminated guillemet identifier")
                i = end + 1
            elif in_hole and c == "{":
                depth += 1
                i += 1
            elif in_hole and c == "}":
                if depth == 0:
                    return i + 1
                depth -= 1
                i += 1
            else:
                i += 1
        if in_hole:
            raise MaskError(f"{_where(text, start)}: unterminated string interpolation hole")
        return i

    lex(0, in_hole=False)
    return bytes(code)


def mask_non_code(text: str) -> str:
    """Blank every character that no reading classifies as code.

    Offsets and newlines are preserved, so masked lines pair with source lines.
    """

    either = (int.from_bytes(code_mask(text, interpolate=False), "big")
              | int.from_bytes(code_mask(text, interpolate=True), "big"))
    code = either.to_bytes(len(text), "big")
    out = list(text)
    for run in NON_CODE_RUN.finditer(code):
        for index in range(run.start(), run.end()):
            if out[index] != "\n":
                out[index] = " "
    return "".join(out)


def normalize(line: str) -> str:
    return " ".join(line.split())


def module_path(root: Path, module: str) -> Path:
    if module == "Blanc":
        return root / "Blanc.lean"
    return root / (module.replace(".", "/") + ".lean")


def local_imports(line: str) -> Iterable[str]:
    match = IMPORT.match(line)
    if not match:
        return ()
    return tuple(token for token in match.group(1).split()
                 if token == "Blanc" or token.startswith("Blanc."))


def closure_files(root: Path) -> list[Path]:
    closure: set[str] = set()
    stack = ["Blanc"]
    while stack:
        module = stack.pop()
        if module in closure:
            continue
        path = module_path(root, module)
        if not path.is_file():
            raise RuntimeError(f"missing local module {module} ({path.relative_to(root)})")
        closure.add(module)
        for line in path.read_text(encoding="utf-8").splitlines():
            stack.extend(local_imports(line))
    return sorted((module_path(root, module) for module in closure),
                  key=lambda path: path.relative_to(root).as_posix())


def inventory(root: Path, files: Iterable[Path]) -> list[str]:
    rows: set[str] = set()
    for path in files:
        rel = path.relative_to(root).as_posix()
        source = path.read_text(encoding="utf-8")
        try:
            masked = mask_non_code(source)
        except MaskError as exc:
            raise RuntimeError(f"{rel}:{exc}") from None
        lines = source.split("\n")
        for rule, literal, pattern in RULES:
            if literal not in masked:
                continue
            for match in pattern.finditer(masked):
                number = masked.count("\n", 0, match.start())
                rows.add(f"{rule} {rel} {normalize(lines[number])}")
    return sorted(rows)


def read_allowlist(path: Path) -> list[str]:
    if not path.is_file():
        raise RuntimeError(f"allowlist not found: {path}")
    rows: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        data = stripped.split("##", 1)[0].strip()
        if not data:
            continue
        rows.add(normalize(data))
    return sorted(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        files = closure_files(root)
        hits = inventory(root, files)
        if args.list:
            for row in hits:
                print(row)
            print(f"OK — trust surface inventory: {len(hits)} occurrence(s) across "
                  f"{len(files)} module(s) in Blanc.lean's import closure")
            return 0
        allowed = read_allowlist(root / "scripts" / "trust-surface-allow.txt")
    except (OSError, RuntimeError, ValueError) as exc:
        print(f"REGRESSION — trust surface: setup failure: {exc}")
        return 2

    unexpected = sorted(set(hits) - set(allowed))
    stale = sorted(set(allowed) - set(hits))
    for row in unexpected:
        print(f"TRUST-SURFACE — unallowlisted occurrence: {row}")
    for row in stale:
        print(f"TRUST-SURFACE — stale allowlist row: {row}")
    if unexpected or stale:
        print("REGRESSION — trust surface: "
              f"{len(unexpected)} unallowlisted and {len(stale)} stale occurrence(s); "
              "the exact allowlist must match the imported closure")
        return 1

    print(f"OK — trust surface: {len(hits)} exact allowlisted occurrence(s) across "
          f"{len(files)} module(s) in Blanc.lean's import closure; no new or stale rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
