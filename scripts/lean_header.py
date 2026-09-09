"""Exact source header extraction for static Lean statement-pin gates."""
from __future__ import annotations

import re


class HeaderError(ValueError):
    """The selected declaration cannot be identified unambiguously."""


DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|example|class)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.?]*)\b"
)


def _escaped(source: str, index: int) -> bool:
    """Whether source[index] has an odd run of preceding backslashes."""
    count = 0
    cursor = index - 1
    while cursor >= 0 and source[cursor] == "\\":
        count += 1
        cursor -= 1
    return count % 2 == 1


def strip_comments(source: str) -> str:
    """Blank Lean comments while retaining every source position."""
    out: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif not in_string and pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif not in_string and pair == "--":
            end = source.find("\n", index)
            if end < 0:
                out.extend(" " * (len(source) - index))
                break
            out.extend(" " * (end - index))
            out.append("\n")
            index = end + 1
        else:
            char = source[index]
            out.append(char)
            if char == '"' and not _escaped(source, index):
                in_string = not in_string
            index += 1
    if depth:
        raise HeaderError("unterminated Lean block comment")
    return "".join(out)


def mask_strings(source: str) -> str:
    """Blank string contents while retaining positions and newlines."""
    out: list[str] = []
    in_string = False
    for index, char in enumerate(source):
        if in_string:
            if char == '\n':
                out.append('\n')
            else:
                out.append(' ')
            if char == '"' and not _escaped(source, index):
                in_string = False
        else:
            if char == '"':
                in_string = True
                out.append(' ')
            else:
                out.append(char)
    if in_string:
        raise HeaderError("unterminated Lean string")
    return "".join(out)


def header_before_definition(source: str, name: str) -> str:
    """Return the exact normalized-pin bytes through a declaration's `:`.

    The marker search follows strings, nested comments, delimiters, and
    top-level `let` bindings, while returning original source bytes so existing
    statement pins retain their documented comment/whitespace normalization.
    """
    cleaned = mask_strings(strip_comments(source))
    matches = [match for match in DECL.finditer(cleaned) if match.group("name") == name]
    if len(matches) != 1:
        raise HeaderError(f"{name}: expected one declaration, found {len(matches)}")
    match = matches[0]
    next_decl = DECL.search(cleaned, match.end())
    index = match.end()
    depth = 0
    pending_let = False
    let_indent: int | None = None
    saw_top_level_let = False
    at_line_start = False
    column = 0

    while index < len(cleaned):
        if next_decl is not None and index >= next_decl.start():
            raise HeaderError(f"{name}: declaration header has no defining :=")
        char = cleaned[index]
        if char == "\n":
            column = 0
            at_line_start = True
            index += 1
            continue
        if at_line_start and char in " \t":
            column += 1
            index += 1
            continue
        if at_line_start:
            if let_indent is not None and column <= let_indent:
                let_indent = None
            at_line_start = False
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
            if depth < 0:
                raise HeaderError(f"{name}: unbalanced delimiter in header")
        elif depth == 0 and (char.isalpha() or char == "_"):
            end = index
            while end < len(cleaned) and (cleaned[end].isalnum() or cleaned[end] in "_'.?"):
                end += 1
            word = cleaned[index:end]
            if word == "let":
                pending_let = True
            elif word == "in" and let_indent is not None:
                let_indent = None
            column += end - index
            index = end
            continue
        elif depth == 0 and char == ";" and let_indent is not None:
            let_indent = None
        elif depth == 0 and cleaned.startswith(":=", index):
            if pending_let:
                pending_let = False
                let_indent = column
                saw_top_level_let = True
                index += 2
                column += 2
                continue
            if let_indent is not None:
                raise HeaderError(f"{name}: unresolved top-level let before :=")
            if (match.group("kind") in {"theorem", "lemma"} and saw_top_level_let
                    and not re.match(r"by\b", cleaned[index + 2:].lstrip())):
                raise HeaderError(f"{name}: theorem defining token is not := by")
            return " ".join(source[match.start():index + 1].split())
        column += 1
        index += 1
    raise HeaderError(f"{name}: missing declaration-level :=")


def parser_controls() -> None:
    """Keep term/tactic/comment/string/header-let marker handling fail-closed."""
    term = "theorem owned : True := trivial\n/-- next := is irrelevant -/\ntheorem later : True := by trivial"
    proof_only = "theorem owned : True := by\n  trivial\n/-- changed neighbouring comment := -/\ntheorem later : True := trivial"
    header_string = "theorem owned (tag : String := \":= in header string\") : True := trivial"
    nested_header_comment = "theorem owned /- outer /- nested := -/ comment -/ : True := trivial"
    fake_only = "def carrier : String := \"first\ntheorem owned : True := trivial\nlast\""
    fake_then_real = fake_only + "\ntheorem owned : True := trivial"
    header_fake_declaration = "theorem owned (tag : String := \"theorem later : True := fake\") : True := trivial"
    even_prefix = 'theorem owned (tag : String := "two backslashes '
    even_backslash = even_prefix + "\\\\" + '") : True := trivial'
    even_backslash_header = even_prefix + "\\\\" + '") : True :'
    let_header = "theorem owned : let x := 1; x = 1 := by\n  rfl\ntheorem later : True := trivial"
    term_header = header_before_definition(term, "owned")
    if term_header != "theorem owned : True :":
        raise HeaderError("term/comment control selected the wrong header")
    if header_before_definition(proof_only, "owned") != term_header:
        raise HeaderError("proof/comment-only control selected a different header")
    if header_before_definition(header_string, "owned") != "theorem owned (tag : String := \":= in header string\") : True :":
        raise HeaderError("header-string control selected the wrong marker")
    if header_before_definition(nested_header_comment, "owned") != "theorem owned /- outer /- nested := -/ comment -/ : True :":
        raise HeaderError("nested-header-comment control selected the wrong marker")
    try:
        header_before_definition(fake_only, "owned")
    except HeaderError:
        pass
    else:
        raise HeaderError("string-only fake declaration was accepted")
    if header_before_definition(fake_then_real, "owned") != term_header:
        raise HeaderError("string fake declaration selected before the real declaration")
    if header_before_definition(header_fake_declaration, "owned") != "theorem owned (tag : String := \"theorem later : True := fake\") : True :":
        raise HeaderError("header-string fake declaration selected as a boundary")
    if header_before_definition(even_backslash, "owned") != even_backslash_header:
        raise HeaderError("even-backslash string closing was not recognised")
    if header_before_definition(let_header, "owned") != "theorem owned : let x := 1; x = 1 :":
        raise HeaderError("top-level let control selected the wrong header")
    changed = term.replace(": True :=", ": False :=", 1)
    if header_before_definition(changed, "owned") == term_header:
        raise HeaderError("statement-change control did not change the header")
