#!/usr/bin/env python3
"""The leaf search: which Blanc declarations are leaves, how many theorem leaves there are, and which are new.

The user's standing rule (theorem-necessity principles, 2026-09-27 and the 2026-09-29 addenda): a
theorem is a *leaf* if and only if it is independently valuable, and every leaf is checked for
axioms, nothing else needs to be. There is no list of pinned theorems and no marker attribute: the
leaf set is COMPUTED from the built environment at every run, and the axiom check is one union walk
over every Blanc constant (``scripts/AxiomCheck.lean``, ``scripts/check.sh``). Whether a leaf is
worth keeping is a human judgement, made by a periodic sweep. This module supplies what the sweep
and the published claims need:

* ``check``: elaborate ``scripts/LeafCensus.lean`` over the built library (a host hold is taken),
  read the sources for the uses the environment cannot show, and print the theorem leaf count.
  It also reports definition leaves informationally. It fails
  closed on an empty, unparseable or internally inconsistent census, on an attribute the census
  cannot count, and when ``scripts/leaf-count.json`` (the number the README publishes) does not
  equal the count just computed. It also prints, informationally, how many leaves are new or
  changed since the last review (``scripts/leaf-review.json``); an unseeded ledger is reported as
  such and is never a failure.
* ``generate [--ledger]``: the registered generator of ``scripts/leaf-count.json`` and, with
  ``--ledger``, of ``scripts/leaf-review.json`` (the review ledger a sweep writes at its close).
  Neither file is ever edited by hand and the ledger is not an input of any gate verdict.
* ``review``: list theorem and definition leaves that are new or whose statement changed since the ledger.
* ``self-test``: bite controls on small fixture environments elaborated by the byte-identical
  driver body, plus the pure-Python controls of the source scan, the count comparison and the ledger.

What counts as use is documented in ``scripts/GATES.md`` ("Leaf audit") and in the header of
``scripts/LeafCensus.lean``. In short: a term mention in any Blanc declaration, or a name written
in the lemma list of a rewriting tactic call (``simp``, ``simp only``, ``dsimp``, ``simpa``, ``rw``, ...),
a double-backtick name literal, or anywhere in a tactic macro of any ``Blanc/**/*.lean`` file.
Attributes alone never count, including an ``rfl`` simp registration. The same exact-identifier
scan records mentions in tracked ``scripts/`` text and ``Main.lean``. External Lean uses are
resolved by ``ExternalUseCensus.lean`` and joined to this census's ownership graph; non-Lean script mentions are report-only external consumers.

Command line (from the repository root)::

    python3 scripts/leaf_audit.py check
    python3 scripts/leaf_audit.py generate [--ledger [--unreviewed FILE]]
    python3 scripts/leaf_audit.py review
    python3 scripts/leaf_audit.py self-test
"""

from __future__ import annotations

import bisect
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate_semaphore  # noqa: E402

DRIVER_RELATIVE = "scripts/LeafCensus.lean"
COUNT_RELATIVE = "scripts/leaf-count.json"
LEDGER_RELATIVE = "scripts/leaf-review.json"
FIXTURE_DIR_RELATIVE = "scripts/fixtures/leaf-audit"
BODY_MARKER = "-- LEAF-CENSUS-BODY"
CENSUS_SCHEMA = 3
COUNT_SCHEMA = 1
LEDGER_SCHEMA = 2
GENERATOR_COUNT = "python3 scripts/leaf_audit.py generate"
GENERATOR_LEDGER = "python3 scripts/leaf_audit.py generate --ledger"

# Attribute heads the driver reads from the environment. Attributes never make a declaration used,
# but known heads remain classified so that a new attribute head is refused until someone decides
# what it does.
USE_ATTRIBUTES = frozenset({"simp", "ext", "instance"})
# Attribute heads that cannot make a theorem used. Anything else found in the source is refused
# until it is classified here and, if it uses a theorem, taught to the driver.
NEUTRAL_ATTRIBUTES = frozenset({
    "irreducible", "reducible", "semireducible", "inline", "noinline", "macro_inline",
    "always_inline", "specialize", "nospecialize", "deprecated", "pp_nodot", "match_pattern",
    "nolint", "unbox",
})

# Tactics whose bracketed argument is a list of lemmas that are rewritten with or simplified by.
# A lemma proved by `rfl` and named only there leaves no term in the proof, so the census cannot
# see the use.
LEMMA_LIST_TACTICS = (
    "simp_all", "simpa", "simp", "dsimp", "simp_arith", "simp_rw", "rwa", "rw", "erw", "rewrite",
    "rw_mod_cast", "norm_num", "norm_cast", "push_cast", "field_simp", "grind", "aesop",
    "ring_nf", "abel_nf", "simp_intro", "unfold_let", "delta",
)
TACTIC_HEAD = re.compile(
    r"(?<![\w.'!?])(" + "|".join(sorted(LEMMA_LIST_TACTICS, key=len, reverse=True))
    + r")(?![\w'!?])")
MACRO_HEAD = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?(?:local\s+|scoped\s+)?"
    r"(?:macro_rules|macro|syntax|elab_rules|elab|notation|declare_simp_like_tactic|"
    r"declare_syntax_cat|register_simp_attr|simproc)\b", re.M)
IDENT = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")
# Trailing field/projection components a rewrite argument may carry (`foo.symm`, `foo.mpr`).
PROJECTIONS = frozenset({"symm", "mp", "mpr", "1", "2", "out", "le", "ge", "trans", "elim", "left",
                         "right", "resolve_left", "resolve_right"})


class LeafAuditError(Exception):
    """The census could not be built or trusted; never a pass."""


# --------------------------------------------------------------------------------------------
# Source text: comment and string stripping
# --------------------------------------------------------------------------------------------

_CHAR = re.compile(r"(?<![\w'])'(?:\\.[^']*|[^'\\])'", re.S)
_RAW_STRING = re.compile(r'(?<![\w\'])r(\#*)"')
_INTERPOLATED_PREFIX = re.compile(
    r"(?<![\w'.])(?:[smf]!|dbg_trace|throwError|println!|"
    r"(?:Macro\.)?trace\[[^\]\n]+\])\s*$")


def strip_comments_and_strings(text: str, label: str = "source") -> str:
    """Mask literal text, retaining executable terms in interpolated strings.

    Offsets/newlines and quote delimiters survive. Ordinary strings, raw strings,
    chars, and nested comments cannot credit a declaration use. The standard
    s!/m!/f! formatters and direct diagnostic forms retain their {...} terms,
    including nested strings, comments, records and further interpolations.
    Lean escapes a literal interpolation opener as \\{ (not doubled braces).
    """

    out = list(text)
    n = len(text)

    def blank(start: int, end: int) -> None:
        for i in range(start, end):
            if text[i] != "\n":
                out[i] = " "

    def block(start: int) -> int:
        depth, pos = 1, start + 2
        while pos < n:
            if text.startswith("/-", pos):
                depth += 1
                pos += 2
            elif text.startswith("-/", pos):
                depth -= 1
                pos += 2
                if not depth:
                    blank(start, pos)
                    return pos
            else:
                pos += 1
        raise LeafAuditError(f"{label}: unterminated block comment")

    def string(start: int, interpolated: bool) -> int:
        pos = start + 1
        while pos < n:
            if text[pos] == '"':
                return pos + 1
            if text[pos] == "\\":
                blank(pos, min(pos + 2, n))
                pos += 2
            elif interpolated and text[pos] == "{":
                pos = code(pos + 1, interpolation=True)
            else:
                blank(pos, pos + 1)
                pos += 1
        raise LeafAuditError(f"{label}: unterminated string literal")

    def code(start: int, interpolation: bool = False) -> int:
        pos, braces = start, 0
        while pos < n:
            if text.startswith("/-", pos):
                pos = block(pos)
            elif text.startswith("--", pos):
                end = text.find("\n", pos)
                end = n if end < 0 else end
                blank(pos, end)
                pos = end
            elif raw := _RAW_STRING.match(text, pos):
                end = text.find('"' + raw.group(1), raw.end())
                if end < 0:
                    raise LeafAuditError(f"{label}: unterminated raw string literal")
                blank(raw.end(), end)
                pos = end + 1 + len(raw.group(1))
            elif text[pos] == '"':
                prefix = "".join(out[:pos])
                pos = string(pos, bool(_INTERPOLATED_PREFIX.search(prefix)))
            elif char := _CHAR.match(text, pos):
                blank(pos + 1, char.end() - 1)
                pos = char.end()
            elif interpolation and text[pos] == "{":
                braces += 1
                pos += 1
            elif interpolation and text[pos] == "}":
                if not braces:
                    return pos + 1
                braces -= 1
                pos += 1
            else:
                pos += 1
        if interpolation:
            raise LeafAuditError(f"{label}: unterminated string interpolation")
        return pos

    code(0)
    return "".join(out)


# --------------------------------------------------------------------------------------------
# Source scan: uses that leave no trace in the environment
# --------------------------------------------------------------------------------------------

def _balanced_end(code: str, start: int, opener: str, closer: str, limit: int = 60000) -> int:
    """Index of the closer matching the opener at ``start``, or -1."""

    depth = 0
    for i in range(start, min(len(code), start + limit)):
        c = code[i]
        if c == opener:
            depth += 1
        elif c == closer:
            depth -= 1
            if depth == 0:
                return i
    return -1


_PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}


def _split_top_level(inner: str) -> List[Tuple[int, str]]:
    """Comma-separated elements of a list body, each with its offset within ``inner``."""

    parts: List[Tuple[int, str]] = []
    stack: List[str] = []
    begin = 0
    for i, c in enumerate(inner):
        if c in _PAIRS:
            stack.append(_PAIRS[c])
        elif stack and c == stack[-1]:
            stack.pop()
        elif c == "," and not stack:
            parts.append((begin, inner[begin:i]))
            begin = i + 1
    parts.append((begin, inner[begin:]))
    return parts


_AFTER_TACTIC = re.compile(
    r"\s*(?:(?:\?|!|only\b|\+[\w.]+|-[\w.]+|<;>)\s*|\((?:[^()]|\([^()]*\))*\)\s*)*\[")


class Scope:
    """The namespace and `open` state of a position, as far as resolution needs it."""

    __slots__ = ("kind", "name", "ns", "opens")

    def __init__(self, kind: str, name: str, ns: Tuple[str, ...]) -> None:
        self.kind = kind
        self.name = name
        self.ns = ns
        self.opens: List[str] = []


_CMD_START = re.compile(r"^[A-Za-z@#/]", re.M)
_NAMESPACE = re.compile(r"^namespace\s+(\S+)")
_SECTION = re.compile(r"^section(?:\s+(\S+))?\s*$")
_END = re.compile(r"^end(?:\s+(\S+))?\s*$")
_OPEN = re.compile(r"^open\s+(.*)$")
_ATTRIBUTE = re.compile(r"^attribute\s*\[([^\]\n]*)\]\s*(.*)$")


def context_events(code: str) -> Tuple[List[int], List[Tuple[Tuple[str, ...], Tuple[str, ...]]]]:
    """``(offsets, states)``: the (namespace components, open namespaces) in force from each offset.

    Only what name resolution needs is tracked: `namespace X`, `section [X]`, `end [X]`, and `open`
    (an `open ... in` is kept until the command it modifies has ended, that is, until the second
    following command start). Sections and namespaces close by their `end`.
    """

    scopes: List[Scope] = [Scope("root", "", ())]
    offsets: List[int] = [0]
    states: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = [((), ())]
    pending_in: List[Tuple[Scope, str, int]] = []  # (scope, namespace, command starts seen since)

    def snapshot() -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
        ns: Tuple[str, ...] = ()
        opens: List[str] = []
        for sc in scopes:
            ns = ns + sc.ns
            opens.extend(sc.opens)
        return ns, tuple(opens)

    pos = 0
    for line in code.split("\n"):
        stripped = line.rstrip()
        start_of_line = pos
        pos += len(line) + 1
        if not stripped or stripped[0] in " \t":
            continue
        changed = False
        # Commands modified by a pending `open ... in` end at the next command start.
        for idx in range(len(pending_in) - 1, -1, -1):
            sc, name, seen = pending_in[idx]
            if seen >= 1:
                if name in sc.opens:
                    sc.opens.remove(name)
                    changed = True
                pending_in.pop(idx)
            else:
                pending_in[idx] = (sc, name, seen + 1)
        m = _NAMESPACE.match(stripped)
        if m:
            comps = tuple(m.group(1).split("."))
            scopes.append(Scope("namespace", m.group(1), comps))
            changed = True
        else:
            m = _SECTION.match(stripped)
            if m:
                scopes.append(Scope("section", m.group(1) or "", ()))
                changed = True
            else:
                m = _END.match(stripped)
                if m and len(scopes) > 1:
                    scopes.pop()
                    changed = True
                else:
                    m = _OPEN.match(stripped)
                    if m:
                        body = m.group(1)
                        has_in = re.search(r"\bin\s*$", body) is not None
                        body = re.sub(r"\bin\s*$", "", body)
                        body = re.split(r"[(]|\bhiding\b|\brenaming\b", body)[0]
                        for word in body.split():
                            if word == "scoped":
                                continue
                            if IDENT.fullmatch(word):
                                scopes[-1].opens.append(word)
                                if has_in:
                                    pending_in.append((scopes[-1], word, 0))
                                changed = True
        if changed:
            offsets.append(start_of_line)
            states.append(snapshot())
    return offsets, states


def _candidates(token: str, ns: Tuple[str, ...], opens: Tuple[str, ...]) -> List[str]:
    """Full names ``token`` could denote, most specific first."""

    if token.startswith("_root_."):
        return [token[len("_root_."):]]
    result: List[str] = []
    for k in range(len(ns), -1, -1):
        prefix = ".".join(ns[:k])
        result.append(f"{prefix}.{token}" if prefix else token)
    for o in reversed(opens):
        for k in range(len(ns), -1, -1):
            prefix = ".".join(ns[:k])
            result.append(f"{prefix}.{o}.{token}" if prefix else f"{o}.{token}")
    return result


def scan_uses(sources: Dict[str, str], population: Set[str]) -> Dict[str, Tuple[str, int, str]]:
    """Theorems of ``population`` named where the environment records no trace.

    ``sources`` maps a module name to its text. A name is used when it occurs (a) as the head of an
    element of the bracketed lemma list of a rewriting tactic call (``simp only [..]``, ``rw [..]``,
    ``dsimp``, ``simpa``, ...; an element written ``-foo`` erases and is not a use), (b) anywhere in
    the body of a ``macro``/``macro_rules``/``syntax``/``elab``/``notation`` command, or (c) in the
    name list of an ``attribute [..]`` command whose attributes are not all neutral, or (d) written as a
    double-backtick name literal (``foo``). Comments and
    string contents are stripped first. A token is resolved like Lean resolves an identifier: the
    innermost enclosing namespace first, then the active ``open``s, and it counts only if the
    resolved name is a Blanc theorem, so a short name that happens to match a theorem of another
    namespace is never credited to it. Returns ``{theorem: (module, line, how)}``, the first
    occurrence of each.
    """

    used: Dict[str, Tuple[str, int, str]] = {}

    for module, text in sources.items():
        code = strip_comments_and_strings(text, module)
        offsets, states = context_events(code)
        line_starts = [0] + [m.end() for m in re.finditer("\n", code)]

        def line_of(off: int) -> int:
            return bisect.bisect_right(line_starts, off)

        def credit(token: str, off: int, how: str) -> None:
            token = token.strip()
            if not token:
                return
            ns, opens = states[bisect.bisect_right(offsets, off) - 1]
            forms = [token]
            parts = token.split(".")
            while len(parts) > 1 and parts[-1] in PROJECTIONS:
                parts = parts[:-1]
                forms.append(".".join(parts))
            for form in forms:
                for cand in _candidates(form, ns, opens):
                    if cand in population:
                        if cand not in used:
                            used[cand] = (module, line_of(off), how)
                        return

        # (a) lemma lists of rewriting tactic calls
        for m in TACTIC_HEAD.finditer(code):
            after = _AFTER_TACTIC.match(code, m.end())
            if after is None:
                continue
            open_at = after.end() - 1
            close_at = _balanced_end(code, open_at, "[", "]")
            if close_at < 0:
                continue
            inner = code[open_at + 1:close_at]
            for begin, element in _split_top_level(inner):
                text_el = element.lstrip()
                skew = len(element) - len(text_el)
                if text_el.startswith("-") and not text_el.startswith("->"):
                    continue
                text_el = re.sub(r"^(?:←|<-|↓|↑|@)+\s*", "", text_el)
                head = IDENT.match(text_el)
                if head is None:
                    continue
                credit(head.group(0), open_at + 1 + begin + skew, f"`{m.group(1)}` list")
        # (b) tactic macro / syntax / elab bodies: every identifier is a possible use
        starts = [m.start() for m in MACRO_HEAD.finditer(code)]
        for s in starts:
            nxt = _CMD_START.search(code, s + 1)
            end = len(code)
            while nxt is not None:
                line_end = code.find("\n", nxt.start())
                line_end = len(code) if line_end < 0 else line_end
                first = code[nxt.start():line_end]
                if not MACRO_HEAD.match(first) or nxt.start() > s:
                    end = nxt.start()
                    break
                nxt = _CMD_START.search(code, nxt.end())
            for tok in IDENT.finditer(code, s, end):
                credit(tok.group(0), tok.start(), "macro body")
        # (c) `attribute [..] names`
        for m in re.finditer(r"^attribute\s*\[([^\]\n]*)\]([^\n]*)", code, re.M):
            heads = [re.sub(r"^(?:local|scoped)\s+", "", a.strip()).split()[0]
                     for a in m.group(1).split(",") if a.strip()]
            if any(h not in NEUTRAL_ATTRIBUTES for h in heads):
                for tok in IDENT.finditer(m.group(2)):
                    credit(tok.group(0), m.start(2) + tok.start(), "attribute command")
        # (d) double-backtick name literals (``foo``): resolved and checked by the elaborator, and a
        # data value, not a constant of the term, so the census cannot see it (a rule table naming
        # its lemmas, a tactic spec). A single backtick is unresolved text and is not a use.
        for m in re.finditer(r"(?<!`)``(" + IDENT.pattern + r")", code):
            credit(m.group(1), m.start(1), "name literal")
    return used


def scan_external_sources(sources: Dict[str, str], population: Set[str]
                          ) -> Tuple[Dict[str, List[str]], Set[str]]:
    """Find exact leaf-name mentions in tracked script text.

    The first result records every path mentioning a declaration. The second marks mentions in
    Lean files as uses: those files are compiled proofs. Non-Lean script mentions are deliberately
    report-only, since a shell/Python gate can name a declaration without elaborating a proof.
    Lean files use the same lexical stripping and namespace/open resolution as ``scan_uses``;
    other text is scanned raw for fully qualified names. A token must resolve exactly to a
    population name; substrings never count.
    """

    consumers: Dict[str, Set[str]] = {}
    lean_uses: Set[str] = set()
    for path, text in sources.items():
        is_lean = path == "Main.lean" or path.endswith(".lean")
        if is_lean:
            code = strip_comments_and_strings(text, path)
            offsets, states = context_events(code)
        else:
            # Shell/Python/Markdown text has no Lean comments, namespaces or `open`s: its `/-` is
            # not a comment opener and its strings are exactly where a gate names a declaration,
            # so it is scanned raw and only a fully qualified mention resolves.
            code = text
            offsets, states = [0], [((), ())]
        for match in IDENT.finditer(code):
            token = match.group(0)
            ns, opens = states[bisect.bisect_right(offsets, match.start()) - 1]
            found: Optional[str] = None
            # Outside Lean a closing quote is not an identifier character (`'Name'`, `"Name"`).
            tokens = [token] if is_lean else list(dict.fromkeys([token, token.rstrip("'")]))
            if is_lean:
                # Prefer a complete declaration name. If none resolves, field notation
                # such as `runtimeSelectors.map` still uses its declaration receiver.
                # Match whole dotted components, never arbitrary string prefixes.
                parts = token.split(".")
                tokens += [".".join(parts[:i]) for i in range(len(parts) - 1, 0, -1)]
            for candidate in (c for t in tokens for c in _candidates(t, ns, opens)):
                if candidate in population:
                    found = candidate
                    break
            if found is None:
                continue
            consumers.setdefault(found, set()).add(path)
            if is_lean:
                lean_uses.add(found)
    return {name: sorted(paths) for name, paths in consumers.items()}, lean_uses


def tracked_external_sources(root: Path) -> Dict[str, str]:
    """Read tracked ``scripts/`` text plus the root ``Main.lean`` for external-consumer reporting."""

    done = subprocess.run(
        ["git", "ls-files", "-z", "--", "scripts", "Main.lean"],
        cwd=str(root), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if done.returncode != 0:
        raise LeafAuditError(f"could not enumerate tracked script sources: {done.stderr.decode(errors='replace')}")
    result: Dict[str, str] = {}
    for raw in done.stdout.split(b"\0"):
        if not raw:
            continue
        relative = raw.decode("utf-8")
        path = root / relative
        try:
            data = path.read_bytes()
        except OSError as exc:
            raise LeafAuditError(f"could not read tracked external source {relative}: {exc}")
        if b"\0" in data:
            if relative.endswith(".lean"):
                raise LeafAuditError(f"tracked Lean source contains NUL: {relative}")
            continue
        try:
            result[relative] = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            if relative.endswith(".lean"):
                raise LeafAuditError(f"tracked Lean source is not UTF-8: {relative}") from exc
            continue
    return result


# --------------------------------------------------------------------------------------------
# Attribute vocabulary guard
# --------------------------------------------------------------------------------------------

def _bracket_spans(code: str, opener: str) -> Iterable[Tuple[int, str]]:
    """Every ``opener`` ... matching ``]`` in ``code``: (offset, inner text)."""

    at = code.find(opener)
    while at >= 0:
        depth, i = 1, at + len(opener)
        while i < len(code) and depth:
            if code[i] == "[":
                depth += 1
            elif code[i] == "]":
                depth -= 1
            i += 1
        yield at, code[at + len(opener):i - 1]
        at = code.find(opener, i)


def scan_attributes_text(name: str, text: str) -> List[str]:
    """Refuse an attribute the census does not know how to count (fail closed).

    A ``local`` or ``scoped`` use-attribute is refused as well: it is not exported to the imported
    environment the census reads, so a theorem carrying only that would look unused.
    """

    problems: List[str] = []
    code = strip_comments_and_strings(text, name)
    for opener in ("@[", "attribute ["):
        for offset, inner in _bracket_spans(code, opener):
            if opener == "@[" and offset > 0 and code[offset - 1] not in " \t\n":
                continue
            depth, parts, current = 0, [], ""
            for ch in inner:
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                if ch == "," and depth == 0:
                    parts.append(current)
                    current = ""
                else:
                    current += ch
            parts.append(current)
            for part in parts:
                words = part.replace("←", " ").replace("-", " ").split()
                scoped = False
                while words and words[0] in ("local", "scoped"):
                    scoped = True
                    words = words[1:]
                if not words:
                    continue
                head = words[0]
                line = code.count("\n", 0, offset) + 1
                if head not in USE_ATTRIBUTES and head not in NEUTRAL_ATTRIBUTES:
                    problems.append(
                        f"{name}:{line}: attribute `{head}` is not classified in "
                        f"scripts/leaf_audit.py (USE_ATTRIBUTES / NEUTRAL_ATTRIBUTES)")
                elif scoped and head in USE_ATTRIBUTES and opener == "@[":
                    problems.append(
                        f"{name}:{line}: a `local`/`scoped` `{head}` attribute is not exported, so "
                        f"the census cannot see the use it makes")
    return problems


def blanc_sources(root: Path) -> Dict[str, str]:
    """``{module name: text}`` for every Blanc source file."""

    files = sorted((root / "Blanc").rglob("*.lean")) + [root / "Blanc.lean"]
    result: Dict[str, str] = {}
    for path in files:
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        result[module] = path.read_text(encoding="utf-8")
    return result


def scan_attributes(sources: Dict[str, str]) -> List[str]:
    problems: List[str] = []
    for module, text in sources.items():
        problems.extend(scan_attributes_text(module, text))
    return problems


# --------------------------------------------------------------------------------------------
# Running the census
# --------------------------------------------------------------------------------------------

def driver_body(root: Path) -> str:
    """The driver from the marker line on: what a fixture run shares byte for byte."""

    text = (root / DRIVER_RELATIVE).read_text()
    index = text.find(BODY_MARKER)
    if index < 0:
        raise LeafAuditError(f"{DRIVER_RELATIVE}: the body marker is missing")
    return text[index:]


def _elaborate(root: Path, args: Sequence[str], stdin: Optional[str], env_extra: Dict[str, str]
               ) -> Tuple[int, str]:
    env = dict(os.environ)
    env.update(env_extra)
    try:
        gate_semaphore.acquire_once("the leaf census")
    except gate_semaphore.Refused as exc:
        raise LeafAuditError(f"host admission refused the leaf census: {exc}")
    try:
        done = subprocess.run(
            ["lake", "env", "lean", *args], cwd=str(root), input=stdin, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, check=False,
        )
    except OSError as exc:
        raise LeafAuditError(f"could not run `lake env lean`: {exc}")
    return done.returncode, done.stdout or ""


def run_census(root: Path, source: Optional[str] = None) -> dict:
    """Elaborate the driver (production, or ``source`` for a fixture) and return its census.

    ``source`` replaces the driver's three-line header and adds a fixture before the shared body.
    """

    with tempfile.TemporaryDirectory(prefix="blanc-leaf-") as tmp:
        out_file = Path(tmp) / "census.json"
        env = {"BLANC_LEAF_OUT": str(out_file)}
        if source is None:
            code, output = _elaborate(root, [DRIVER_RELATIVE], None, env)
        else:
            code, output = _elaborate(root, ["--stdin"], source, env)
        if code != 0 or not out_file.is_file():
            sys.stdout.write(output)
            raise LeafAuditError(f"the leaf census failed to elaborate (exit {code})")
        try:
            census = json.loads(out_file.read_text())
        except (OSError, ValueError) as exc:
            raise LeafAuditError(f"the leaf census is unparseable: {exc}")
    if not isinstance(census, dict):
        raise LeafAuditError("the leaf census is not an object")
    return census


def fixture_source(root: Path, fixture: str, edit: Optional[Tuple[str, str]] = None) -> str:
    """``import Lean``, the fixture, and the shared driver body (optionally with one exact edit)."""

    body = driver_body(root)
    if edit is not None:
        old, new = edit
        if body.count(old) != 1:
            raise LeafAuditError(f"driver mutation site {old!r} occurs {body.count(old)} times")
        body = body.replace(old, new)
    return "import Lean\n\n" + fixture + "\n\n" + body


# --------------------------------------------------------------------------------------------
# The leaf set
# --------------------------------------------------------------------------------------------

def validate_census(census: dict) -> None:
    """Refuse a census that cannot support a verdict (fail closed)."""

    def fail(message: str) -> None:
        raise LeafAuditError(f"the leaf census is not trustworthy: {message}")

    if census.get("schema") != CENSUS_SCHEMA:
        fail(f"schema {census.get('schema')!r}, expected {CENSUS_SCHEMA}")
    for key in ("leaves", "definition_leaves", "population_names"):
        if not isinstance(census.get(key), list):
            fail(f"field {key!r} is missing or not a list")
    population = census.get("population")
    if not isinstance(population, int) or population <= 0:
        fail("the declaration population is empty")
    for key in ("theorem_population", "definition_population"):
        if not isinstance(census.get(key), int) or census[key] < 0:
            fail(f"field {key!r} is missing or invalid")
    if census["theorem_population"] + census["definition_population"] != population:
        fail("theorem and definition populations do not add up")
    if not census["leaves"]:
        fail("the leaf set is empty; a repository with theorems always has leaves")
    for row in census["leaves"] + census["definition_leaves"]:
        if not isinstance(row, dict) or not isinstance(row.get("name"), str) \
                or not isinstance(row.get("private"), bool) or not isinstance(row.get("module"), str) \
                or row.get("kind") not in ("theorem", "definition") \
                or not isinstance(row.get("fp"), str) or len(row["fp"]) != 16:
            fail(f"malformed row {row!r}")
    if len(census["leaves"]) + len(census["definition_leaves"]) > population:
        fail("more leaves than declarations")
    if any(row.get("kind") != "theorem" for row in census["leaves"]):
        fail("theorem leaf list contains a non-theorem")
    if any(row.get("kind") != "definition" for row in census["definition_leaves"]):
        fail("definition leaf list contains a non-definition")


def leaf_key(row: dict) -> str:
    """The ledger key of a leaf: its name, and for a private theorem also its module."""

    return f"{row['name']} [private, {row['module']}]" if row["private"] else row["name"]


def analyze(census: dict, sources: Dict[str, str],
            external: Optional[Dict[str, List[str]]] = None,
            external_lean_uses: Optional[Set[str]] = None,
            native_external: Optional[Dict[tuple, List[str]]] = None) -> dict:
    """The final leaf sets, with source uses and external consumer paths attached."""

    validate_census(census)
    population = set(census["population_names"])
    uses = scan_uses(sources, population)
    external = external or {}
    external_lean_uses = external_lean_uses or set()
    native_external = native_external or {}
    kept: List[dict] = []
    definition_kept: List[dict] = []
    removed: List[Tuple[dict, Tuple[str, int, str]]] = []
    for original in census["leaves"]:
        row = dict(original)
        row["external_consumers"] = sorted(external.get(row["name"], []))
        evidence = uses.get(row["name"])
        if (row["module"], row["name"], row["fp"]) in native_external:
            paths = native_external[(row["module"], row["name"], row["fp"])]
            removed.append((row, (paths[0], 0, "native resolved external consumer")))
        elif not row["private"] and row["name"] in external_lean_uses:
            removed.append((row, ("scripts", 0, "compiled Lean external consumer")))
        elif evidence is not None and (not row["private"] or evidence[0] == row["module"]):
            removed.append((row, evidence))
        else:
            kept.append(row)
    for original in census["definition_leaves"]:
        row = dict(original)
        row["external_consumers"] = sorted(external.get(row["name"], []))
        if (row["module"], row["name"], row["fp"]) in native_external:
            paths = native_external[(row["module"], row["name"], row["fp"])]
            removed.append((row, (paths[0], 0, "native resolved external consumer")))
        elif not row["private"] and row["name"] in external_lean_uses:
            removed.append((row, ("scripts", 0, "compiled Lean external consumer")))
        elif evidence := uses.get(row["name"]):
            if not row["private"] or evidence[0] == row["module"]:
                removed.append((row, evidence))
            else:
                definition_kept.append(row)
        else:
            definition_kept.append(row)
    kept.sort(key=lambda r: (r["name"], r["module"]))
    definition_kept.sort(key=lambda r: (r["name"], r["module"]))
    removed.sort(key=lambda pair: pair[0]["name"])
    return {
        "leaves": kept,
        "definition_leaves": definition_kept,
        "census_leaves": len(census["leaves"]),
        "census_definition_leaves": len(census["definition_leaves"]),
        "removed_by_source_use": removed,
        "population": census["population"],
    }


def counts_of(result: dict) -> dict:
    leaves = result["leaves"]
    return {"leaves": len(leaves), "public": sum(1 for r in leaves if not r["private"]),
            "private": sum(1 for r in leaves if r["private"])}


# --------------------------------------------------------------------------------------------
# The count artifact and the review ledger
# --------------------------------------------------------------------------------------------

def count_document(counts: dict) -> str:
    return json.dumps({"schema": COUNT_SCHEMA, "generator": GENERATOR_COUNT, **counts},
                      indent=1, sort_keys=True) + "\n"


def read_count(root: Path) -> dict:
    path = root / COUNT_RELATIVE
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise LeafAuditError(
            f"{COUNT_RELATIVE} is missing or unparseable ({exc}); regenerate it with "
            f"`{GENERATOR_COUNT}`")
    if not isinstance(data, dict) or data.get("schema") != COUNT_SCHEMA \
            or not all(isinstance(data.get(k), int) for k in ("leaves", "public", "private")):
        raise LeafAuditError(f"{COUNT_RELATIVE} is malformed; regenerate it with `{GENERATOR_COUNT}`")
    return data


def compare_count(committed: dict, counts: dict) -> List[str]:
    """Empty when the committed count is the computed one; else the regression line."""

    if all(committed.get(k) == counts[k] for k in ("leaves", "public", "private")):
        return []
    return [
        f"REGRESSION — leaf count: {COUNT_RELATIVE} says {committed.get('leaves')} leaves "
        f"({committed.get('public')} public, {committed.get('private')} private) but the leaf "
        f"search finds {counts['leaves']} ({counts['public']} public, {counts['private']} "
        f"private); the published count is produced, never edited: regenerate with "
        f"`{GENERATOR_COUNT}`, then update the surfaces that quote it"]


def ledger_document(toolchain: str, leaves: List[dict], definition_leaves: Sequence[dict] = (),
                    unreviewed: Optional[dict] = None) -> str:
    """The ledger for theorem and definition leaves.

    Schema 1 ledgers stored bare fingerprints and are read as theorem-only. New rows carry their
    kind explicitly so a definition leaf cannot be mistaken for a theorem during review.
    """

    all_leaves = list(leaves) + list(definition_leaves)
    return json.dumps({"schema": LEDGER_SCHEMA, "generator": GENERATOR_LEDGER,
                       "toolchain": toolchain,
                       "leaves": {leaf_key(r): {"fp": r["fp"], "kind": r["kind"]}
                                  for r in sorted(all_leaves, key=leaf_key)},
                       **({"unreviewed_excluded": unreviewed} if unreviewed else {})},
                      indent=1, sort_keys=True) + "\n"


def read_ledger(root: Path) -> Optional[dict]:
    """The normalized ledger's ``{key: {fp, kind}}``; old ledgers are theorem-only."""

    path = root / LEDGER_RELATIVE
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise LeafAuditError(f"{LEDGER_RELATIVE} is unparseable: {exc}")
    if not isinstance(data, dict) or data.get("schema") not in (1, LEDGER_SCHEMA) \
            or not isinstance(data.get("leaves"), dict):
        raise LeafAuditError(f"{LEDGER_RELATIVE} is malformed")
    normalized: Dict[str, dict] = {}
    for key, value in data["leaves"].items():
        if not isinstance(key, str):
            raise LeafAuditError(f"{LEDGER_RELATIVE} has a non-string leaf key")
        if data.get("schema") == 1:
            if not isinstance(value, str):
                raise LeafAuditError(f"{LEDGER_RELATIVE} has a malformed old fingerprint")
            normalized[key] = {"fp": value, "kind": "theorem"}
        elif isinstance(value, dict) and isinstance(value.get("fp"), str) \
                and value.get("kind") in ("theorem", "definition"):
            normalized[key] = {"fp": value["fp"], "kind": value["kind"]}
        else:
            raise LeafAuditError(f"{LEDGER_RELATIVE} has a malformed leaf row for {key}")
    return normalized


def ledger_diff(ledger: Optional[dict], leaves: List[dict],
                definition_leaves: Sequence[dict] = ()) -> Optional[dict]:
    """``None`` for an unseeded ledger, else new/changed/removed theorem or definition leaves."""

    if ledger is None:
        return None
    now = {leaf_key(r): {"fp": r["fp"], "kind": r["kind"]}
           for r in list(leaves) + list(definition_leaves)}
    return {
        "new": sorted(k for k in now if k not in ledger),
        "changed": sorted(k for k in now if k in ledger and ledger[k] != now[k]),
        "removed": sorted(k for k in ledger if k not in now),
    }


def review_lines(diff: Optional[dict], total: int, limit: int = 12) -> List[str]:
    if diff is None:
        return [f"LEAF-REVIEW: ledger {LEDGER_RELATIVE} not yet seeded; all {total} theorem and "
                f"definition leaves are "
                f"unreviewed (informational; a sweep seeds it with `{GENERATOR_LEDGER}` at its "
                f"close)"]
    fresh = diff["new"] + diff["changed"]
    lines = [f"LEAF-REVIEW: {len(fresh)} theorem/definition leaves new or changed since the last review "
             f"({len(diff['new'])} new, {len(diff['changed'])} changed; {len(diff['removed'])} "
             f"reviewed leaves are gone) (informational)"]
    for key in fresh[:limit]:
        lines.append(f"  {'new' if key in diff['new'] else 'changed'}: {key}")
    if len(fresh) > limit:
        lines.append(f"  ... {len(fresh) - limit} more: `python3 scripts/leaf_audit.py review`")
    return lines


def toolchain_of(root: Path) -> str:
    try:
        return (root / "lean-toolchain").read_text().strip()
    except OSError:
        return "unknown"


# --------------------------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------------------------

def production_result(root: Path) -> Tuple[dict, dict]:
    import external_uses

    sources = blanc_sources(root)
    problems = scan_attributes(sources)
    if problems:
        raise LeafAuditError("; ".join(problems))
    with gate_semaphore.admitted("the leaf census", memory_gib=8):
        census = run_census(root)
    external_sources = tracked_external_sources(root)
    external, _ = scan_external_sources(external_sources, set(census.get("population_names", [])))
    # Keep the narrow source contexts that can disappear from elaborated terms.
    # General identifier occurrences in Lean scripts are report-only; native resolution
    # decides actual constants, methods and implicit instances.
    traceless = scan_uses({p: s for p, s in external_sources.items() if p.endswith(".lean")},
                          set(census.get("population_names", [])))
    try:
        documents = external_uses.collect(root, external_sources)
        native = external_uses.resolve_references(census, documents)
    except external_uses.ExternalUseError as exc:
        raise LeafAuditError(str(exc)) from exc
    if tracked_external_sources(root) != external_sources or blanc_sources(root) != sources:
        raise LeafAuditError("source population changed during native external collection")
    result = analyze(census, sources, external, set(traceless), native)
    result["external_script_population"] = sorted(documents)
    return census, result


def summary_line(result: dict) -> str:
    c = counts_of(result)
    return (f"{c['leaves']} theorem leaves ({c['public']} public, {c['private']} private) among "
            f"{result['population']} declarations; {len(result['definition_leaves'])} definition "
            f"leaves; {len(result['removed_by_source_use'])} census leaves are used by a term, "
            f"rewriting tactic call, macro or compiled script proof and are not leaves")


def cmd_check(root: Path) -> int:
    try:
        census, result = production_result(root)
        counts = counts_of(result)
        lines = compare_count(read_count(root), counts)
        diff = ledger_diff(read_ledger(root), result["leaves"], result["definition_leaves"])
    except LeafAuditError as exc:
        print(f"REGRESSION — leaf audit: {exc}")
        return 1
    print(f"LEAF-COUNT {counts['leaves']}")
    print(f"DEFINITION-LEAVES {len(result['definition_leaves'])} (informational; not in leaf-count.json)")
    for line in review_lines(diff, counts["leaves"] + len(result["definition_leaves"])):
        print(line)
    if lines:
        print("\n".join(lines))
        return 1
    print(f"OK — leaf audit: {summary_line(result)}")
    return 0


def cmd_generate(root: Path, ledger: bool, unreviewed_path: Optional[Path] = None) -> int:
    try:
        census, result = production_result(root)
    except LeafAuditError as exc:
        print(f"REGRESSION — leaf audit: {exc}")
        return 1
    counts = counts_of(result)
    (root / COUNT_RELATIVE).write_text(count_document(counts))
    print(f"wrote {COUNT_RELATIVE}: {counts['leaves']} leaves ({counts['public']} public, "
          f"{counts['private']} private)")
    if ledger:
        reviewed = list(result["leaves"])
        definition_reviewed = list(result["definition_leaves"])
        unreviewed = None
        if unreviewed_path is not None:
            # Leaves the closing sweep never classified (e.g. theorems that became leaves because
            # their only users were deleted) stay OUT of the ledger, so the next review lists them
            # as new instead of treating them as judged.
            text = unreviewed_path.read_text()
            wanted = [line.strip() for line in text.splitlines() if line.strip()]
            current = {leaf_key(r) for r in reviewed + definition_reviewed}
            stray = sorted(set(wanted) - current)
            if stray:
                print(f"REGRESSION — leaf audit: --unreviewed names {len(stray)} non-leaves, e.g. {stray[:3]}")
                return 1
            reviewed = [r for r in reviewed if leaf_key(r) not in set(wanted)]
            definition_reviewed = [r for r in definition_reviewed if leaf_key(r) not in set(wanted)]
            unreviewed = {"count": len(set(wanted)),
                          "sha256": hashlib.sha256(text.encode()).hexdigest(),
                          "source": unreviewed_path.name}
        (root / LEDGER_RELATIVE).write_text(ledger_document(
            toolchain_of(root), reviewed, definition_reviewed, unreviewed))
        print(f"wrote {LEDGER_RELATIVE}: {len(reviewed)} theorem and {len(definition_reviewed)} definition leaves"
              + (f" ({unreviewed['count']} unreviewed leaves left out, listed as new by `review`)"
                 if unreviewed else ""))
    return 0


def cmd_review(root: Path) -> int:
    try:
        census, result = production_result(root)
        diff = ledger_diff(read_ledger(root), result["leaves"], result["definition_leaves"])
    except LeafAuditError as exc:
        print(f"REGRESSION — leaf audit: {exc}")
        return 1
    all_leaves = result["leaves"] + result["definition_leaves"]
    modules = {leaf_key(r): (r["module"], r["kind"]) for r in all_leaves}
    if diff is None:
        print(review_lines(None, len(all_leaves))[0])
        for r in all_leaves:
            print(f"  unreviewed: {leaf_key(r)}  ({r['kind']}, {r['module']})")
        return 0
    for label in ("new", "changed"):
        for key in diff[label]:
            module, kind = modules[key]
            print(f"{label}: {key}  ({kind}, {module})")
    for key in diff["removed"]:
        print(f"gone: {key}")
    print(review_lines(diff, len(all_leaves), limit=0)[0])
    return 0


# --------------------------------------------------------------------------------------------
# Bite controls
# --------------------------------------------------------------------------------------------

def scan_controls() -> List[str]:
    """Table controls of `scan_uses` on synthetic sources; the failures, empty when all hold."""

    population = {"A.foo", "A.B.foo", "A.B.bar", "C.baz", "D.qux", "foo", "A.mac", "A.at"}
    cases: List[Tuple[str, str, Set[str]]] = [
        ("simp only list", "namespace A\ntheorem t : True := by simp only [B.bar]\nend A\n",
         {"A.B.bar"}),
        ("innermost namespace wins",
         "namespace A.B\ntheorem t : True := by simp [foo]\nend A.B\n", {"A.B.foo"}),
        ("outer namespace when the inner has none",
         "namespace A.B\ntheorem t : True := by simp [bar, baz]\nend A.B\n", {"A.B.bar"}),
        ("root name", "theorem t : True := by\n  rw [foo]\n", {"foo"}),
        ("`_root_` prefix", "namespace A\ntheorem t : True := by rw [_root_.foo]\nend A\n",
         {"foo"}),
        ("open namespace", "open C in\ntheorem t : True := by simp only [baz]\n", {"C.baz"}),
        ("open ends with its command",
         "open C in\ntheorem s : True := trivial\ntheorem t : True := by simp only [baz]\n",
         set()),
        ("open until the end of the section",
         "section\nopen D\ntheorem t : True := by simp [qux]\nend\n"
         "theorem u : True := by simp [qux]\n", {"D.qux"}),
        ("open does not outlive its section",
         "section\nopen D\nend\ntheorem u : True := by simp [qux]\n", set()),
        ("erased lemma", "theorem t : True := by simp [-foo]\n", set()),
        ("reverse rewrite and hypothesis list",
         "theorem t : True := by rw [← foo] at h ⊢\n", {"foo"}),
        ("config and flags before the list",
         "theorem t : True := by simp (config := {}) only [foo]\n", {"foo"}),
        ("comment", "-- simp [foo]\ntheorem t : True := by trivial\n", set()),
        ("block comment", "/- rw [foo] -/\ntheorem t : True := by trivial\n", set()),
        ("string", 'theorem t : String := "simp [foo]"\n', set()),
        ("interpolated term tactic", 'def t := s!"literal simp [foo] {by simp only [A.B.bar]}"',
         {"A.B.bar"}),
        ("interpolated nested string", 'def t := s!"{String.intercalate "simp [foo]" xs}"', set()),
        ("raw string", 'def t := r##"simp [foo] /- "more" -/"##', set()),
        ("not a tactic list", "theorem t : True := by exact foo\n", set()),
        ("projection of a lemma", "theorem t : True := by rw [foo.symm]\n", {"foo"}),
        ("macro body names a theorem", "namespace A\nmacro \"m\" : tactic => `(tactic| exact mac)\n"
         "theorem u : True := trivial\nend A\n", {"A.mac"}),
        ("macro body ends at the next command",
         "namespace A\nmacro \"m\" : tactic => `(tactic| skip)\ntheorem u : True := by exact mac\n"
         "end A\n", set()),
        ("attribute command names a theorem", "attribute [local simp] foo\n", {"foo"}),
        ("neutral attribute command", "attribute [local irreducible] foo\n", set()),
        ("name literal", "namespace A\ndef spec : Lean.Name := ``B.bar\nend A\n", {"A.B.bar"}),
        ("single-backtick name is not a use", "def spec : Lean.Name := `foo\n", set()),
    ]
    failures: List[str] = []
    for label, text, expected in cases:
        got = set(scan_uses({"M": text}, population))
        if got != expected:
            failures.append(f"source scan {label}: expected {sorted(expected)}, got {sorted(got)}")
    # Actual regression: evaluator terms inside s! were erased along with literal text.
    # Both positive uses and same-spelled literal non-uses matter to leaf classification.
    interpolation_cases = [
        ("ordinary literal", '"{A.foo}"', set()),
        ("ordinary message argument", 'logError "{A.foo}"', set()),
        ("qualified message argument", 'Lean.throwError "{A.foo}"', set()),
        ("raw literal", 'r##"{A.foo} " /- --"##', set()),
        ("raw zero hashes", 'r"{A.foo}"', set()),
        ("s formatter", 's!"A.foo {A.B.bar}"', {"A.B.bar"}),
        ("m formatter", 'm!"{A.foo}"', {"A.foo"}),
        ("f formatter", 'f!"{A.foo}"', {"A.foo"}),
        ("comment before quote", 's! /- {A.foo} -/ "{A.B.bar}"', {"A.B.bar"}),
        ("nested record", 's!"{({field := A.foo, other := {field := A.B.bar}})}"',
         {"A.foo", "A.B.bar"}),
        ("nested string", 's!"{String.intercalate "A.foo" [A.B.bar]}"', {"A.B.bar"}),
        ("nested formatter", 's!"{s!"A.foo {A.B.bar}"}"', {"A.B.bar"}),
        ("nested comments", 's!"{/- } /- A.foo -/ -/ A.B.bar}"', {"A.B.bar"}),
        ("line comment", 's!"{-- } A.foo\n A.B.bar}"', {"A.B.bar"}),
        ("character brace", "s!\"{('{', A.foo, '}')}\"", {"A.foo"}),
        ("escaped opener", r's!"\{A.foo} {A.B.bar}"', {"A.B.bar"}),
        ("escaped quote", r's!"\" A.foo {A.B.bar}"', {"A.B.bar"}),
        ("println formatter", 'println! "{A.foo}"', {"A.foo"}),
        ("throwError formatter", 'throwError "{A.foo}"', {"A.foo"}),
        ("trace formatter", 'trace[Blanc.test] "{A.foo}"', {"A.foo"}),
        ("namespace in interpolation", 'namespace A\ndef t := s!"{foo}"\nend A', {"A.foo"}),
        ("method receiver", 'namespace A\ndef t := B.bar.map f\nend A', {"A.B.bar"}),
        ("chained projections", 'def t := A.B.bar.toList.length', {"A.B.bar"}),
        ("exact name before receiver", 'def t := A.B.bar', {"A.B.bar"}),
        ("no partial component", 'def t := A.B.barSuffix.map f', set()),
    ]
    for label, text, expected in interpolation_cases:
        masked = strip_comments_and_strings(text, label)
        if len(masked) != len(text) or [i for i, c in enumerate(masked) if c == "\n"] != [
                i for i, c in enumerate(text) if c == "\n"]:
            failures.append(f"interpolation {label}: changed offsets or newlines")
        external, used = scan_external_sources({"scripts/Eval.lean": text}, population)
        if used != expected or set(external) != expected:
            failures.append(f"interpolation {label}: expected {sorted(expected)}, got {sorted(used)}")
    for malformed in ['s!"{A.foo', 's!"literal', '/- unclosed', 'r##"unclosed"#']:
        try:
            strip_comments_and_strings(malformed, "malformed fixture")
        except LeafAuditError:
            pass
        else:
            failures.append(f"malformed literal did not fail closed: {malformed!r}")
    exact_external, exact_uses = scan_external_sources(
        {"scripts/Eval.lean": "def t := A.foo.map"}, {"A.foo", "A.foo.map"})
    if exact_uses != {"A.foo.map"} or set(exact_external) != {"A.foo.map"}:
        failures.append("field notation: complete declaration name must win over receiver")
    # a private leaf is credited only inside its own module (`analyze` checks the module)
    return failures


def self_test(root: Path) -> int:
    fixture_dir = root / FIXTURE_DIR_RELATIVE
    base = (fixture_dir / "compliant.lean").read_text()
    expected_base_leaves = [line.strip() for line in
                            (fixture_dir / "compliant.leaves").read_text().splitlines()
                            if line.strip()]
    expected_base_definitions = [line.strip() for line in
                                 (fixture_dir / "compliant.definitions").read_text().splitlines()
                                 if line.strip()]
    ns = "LeafFixture."

    failures: List[str] = []
    checks = 0

    def census_of(source: str, edit: Optional[Tuple[str, str]] = None) -> dict:
        return run_census(root, source=fixture_source(root, source, edit))

    def leaf_names(source: str) -> List[str]:
        result = analyze(census_of(source), {"_current": source})
        return [leaf_key(r) if not r["private"] else r["name"] for r in result["leaves"]]

    def definition_names(source: str) -> List[str]:
        result = analyze(census_of(source), {"_current": source})
        return [leaf_key(r) if not r["private"] else r["name"]
                for r in result["definition_leaves"]]

    def expect_leaves(label: str, source: str, expected: Sequence[str]) -> None:
        nonlocal checks
        checks += 1
        got = sorted(leaf_names(source))
        if got != sorted(expected):
            failures.append(f"{label}: expected leaves {sorted(expected)}, got {got}")
        else:
            print(f"OK — {label}: leaves {got}")

    def expect_definitions(label: str, source: str, expected: Sequence[str]) -> None:
        nonlocal checks
        checks += 1
        got = sorted(definition_names(source))
        if got != sorted(expected):
            failures.append(f"{label}: expected definition leaves {sorted(expected)}, got {got}")
        else:
            print(f"OK — {label}: definition leaves {got}")

    def replaced(text: str, old: str, new: str, label: str) -> str:
        if text.count(old) != 1:
            failures.append(f"{label}: the fixture lost its edit site {old!r}")
            return text
        return text.replace(old, new)

    # The compliant fixture is the green baseline every control is a one-line change from.
    expect_leaves("compliant fixture", base, expected_base_leaves)
    expect_definitions("compliant fixture definitions", base, expected_base_definitions)
    checks += 1
    base_census = census_of(base)
    if base_census.get("excluded_auxiliary_theorems", 0) < 1:
        failures.append("the fixture no longer exercises a compiler-auxiliary theorem "
                        "(`picked._proof_N`), so auxiliary attribution is untested")

    # A new unused theorem is a leaf; a private one too, and it is marked private.
    extra = base + "\n\nnamespace LeafFixture\ntheorem extra_unused : 2 + 2 = 4 := rfl\nend LeafFixture\n"
    expect_leaves("unused theorem added", extra, expected_base_leaves + [ns + "extra_unused"])
    private = base + ("\n\nnamespace LeafFixture\nprivate theorem hidden_unused : 3 + 3 = 6 := rfl\n"
                      "end LeafFixture\n")
    checks += 1
    result = analyze(census_of(private), {"_current": private})
    rows = [r for r in result["leaves"] if r["private"]]
    if len(rows) != 1 or rows[0]["name"] != ns + "hidden_unused":
        failures.append(f"private leaf: unexpected private leaves {rows}")
    else:
        print(f"OK — private leaf: {leaf_key(rows[0])}")

    # Definitions have their own leaf list and a definition used in a theorem is not a leaf.
    expect_definitions("used definition loses its only user",
                       replaced(base, "theorem uses_definition : used_definition = 42 := rfl",
                                "theorem uses_definition : 42 = 42 := rfl", "definition user"),
                       expected_base_definitions + [ns + "used_definition"])

    # A theorem another theorem uses is not a leaf: delete the only user and it becomes one.
    expect_leaves("used theorem loses its only user",
                  replaced(base, "theorem headline_one : (1 + 1 = 2) ∧ True := ⟨base_fact, trivial⟩",
                           "theorem headline_one : (1 + 1 = 2) ∧ True := ⟨rfl, trivial⟩",
                           "base_fact user"),
                  expected_base_leaves + [ns + "base_fact"])
    # Auxiliary attribution: a theorem used only inside a definition's abstracted proof is used.
    expect_leaves("theorem used only inside a definition's proof auxiliary loses that use",
                  replaced(base, "⟨2, Nat.lt_of_lt_of_le bound_fact (Nat.le_refl 3)⟩",
                           "⟨2, by decide⟩", "bound_fact user"),
                  expected_base_leaves + [ns + "bound_fact"])

    # Attributes do not exempt anything: the unused rfl simp lemma is an ordinary theorem leaf,
    # just like the unused non-rfl simp lemma, ext lemma and instance.
    checks += 1
    raw_names = {r["name"] for r in base_census["leaves"]}
    expected_attribute_leaves = {ns + "simp_only_fact", ns + "simp_nonrfl_fact",
                                 ns + "Pt.ext_fx", ns + "instNonemptyPt"}
    if not expected_attribute_leaves <= raw_names or "attribute_only" in base_census:
        failures.append("attribute rule: rfl simp lemmas must be ordinary leaves and attribute_only "
                        "must be absent")
    else:
        print(f"OK — attribute rule removed: {sorted(expected_attribute_leaves)} are leaves")
    # A mutation restoring the former rfl-simp exemption must visibly remove simp leaves.
    checks += 1
    blanket = run_census(root, source=fixture_source(
        root, base, ('if kind == "theorem" then leaves := leaves.push row',
                     'if kind == "theorem" && !ks.any (·.startsWith "simp-set:") then '
                     'leaves := leaves.push row')))
    lost = sorted(set(r["name"] for r in base_census["leaves"])
                  - set(r["name"] for r in blanket["leaves"]))
    if lost != [ns + "simp_nonrfl_fact", ns + "simp_only_fact"]:
        failures.append(f"attribute-exemption control: expected simp leaves to vanish, got {lost}")
    else:
        print(f"OK — old attribute-exemption mutation loses only simp leaves: {lost}")
    expect_leaves("simp lemma no longer used by the `simp` call that mentions its `_simp_1`",
                  replaced(base, "theorem uses_gq : gq 1 = true := by simp",
                           "theorem uses_gq : gq 1 = true := by decide", "gq user"),
                  expected_base_leaves + [ns + "gq_iff"])
    expect_leaves("unused instance used by a term",
                  replaced(base, "end LeafFixture\n\nnamespace Elsewhere",
                           "def ptWitness : Nonempty Pt := inferInstance\n\n"
                           "end LeafFixture\n\nnamespace Elsewhere", "instance user"),
                  [n for n in expected_base_leaves if n != ns + "instNonemptyPt"])
    expect_leaves("unused `@[ext]` lemma applied by a term",
                  replaced(base, "end LeafFixture\n\nnamespace Elsewhere",
                           "def ptExtUse (a b : Pt) (h : a.x = b.x) : a = b := Pt.ext_fx h\n\n"
                           "end LeafFixture\n\nnamespace Elsewhere", "ext user"),
                  [n for n in expected_base_leaves if n != ns + "Pt.ext_fx"])
    # Attributes never change liveness in the driver: a mutation exempting every attributed
    # theorem from the leaf set (a blanket attribute rule) must visibly lose all four attributed
    # leaves (the two simp lemmas, the `@[ext]` lemma and the instance).
    checks += 1
    blanket = run_census(root, source=fixture_source(
        root, base, ('if kind == "theorem" then leaves := leaves.push row',
                     'if kind == "theorem" && ks.isEmpty then leaves := leaves.push row')))
    lost = sorted(set(r["name"] for r in base_census["leaves"])
                  - set(r["name"] for r in blanket["leaves"]))
    expected_lost = [ns + "Pt.ext_fx", ns + "instNonemptyPt", ns + "simp_nonrfl_fact",
                     ns + "simp_only_fact"]
    if lost != expected_lost:
        failures.append(f"blanket-attribute control: expected {expected_lost} to vanish, got {lost}")
    else:
        print(f"OK — blanket attribute rule in the driver: {lost} would vanish from the leaf set; "
              f"the shared driver keeps them")

    # Parser descriptors generated by `syntax`/`macro` declarations are not population: the
    # elaborator uses them through their node kind, never through a term, so without the rule every
    # tactic macro would surface as a definition leaf.
    checks += 1
    with_parsers = run_census(root, source=fixture_source(
        root, base, ("if d.type.isConstOf ``Lean.ParserDescr || "
                     "d.type.isConstOf ``Lean.TrailingParserDescr then none", "if false then none")))
    gained = sorted(set(r["name"] for r in with_parsers["definition_leaves"])
                    - set(r["name"] for r in base_census["definition_leaves"]))
    if gained != [ns + "tacticLeaf_fixture_tac", ns + "tacticLeaf_fixture_unused_tac"]:
        failures.append(f"parser-descriptor control: expected the two macro descriptors to become "
                        f"definition leaves, got {gained}")
    else:
        print(f"OK — parser-descriptor rule disabled in the driver: {gained} become definition "
              f"leaves; the shared driver leaves syntax machinery out of the population")

    # Generated per-constructor eliminators (`Two.left.elim`) belong to their inductive: without
    # the rule every multi-constructor inductive contributes one definition leaf per constructor.
    checks += 1
    with_elims = run_census(root, source=fixture_source(
        root, base, ('(match n with | .str p "elim" => env.find? p | _ => (none : Option ConstantInfo))',
                     "(none : Option ConstantInfo)")))
    gained = sorted(set(r["name"] for r in with_elims["definition_leaves"])
                    - set(r["name"] for r in base_census["definition_leaves"]))
    if gained != [ns + "Two.left.elim", ns + "Two.right.elim"]:
        failures.append(f"constructor-eliminator control: expected Two's two eliminators to become "
                        f"definition leaves, got {gained}")
    else:
        print(f"OK — constructor-eliminator attribution disabled in the driver: {gained} become "
              f"definition leaves; the shared driver attributes them to their inductive")

    # The used side is attributed to the parent as well: without it `gq_iff` (used only through its
    # generated `gq_iff._simp_1`) is a leaf although the `simp` call in `uses_gq` needs it.
    checks += 1
    unattributed = run_census(root, source=fixture_source(
        root, base, ("let usedKey : Name := (owner env u).getD u", "let usedKey : Name := u")))
    gained = sorted(set(r["name"] for r in unattributed["leaves"])
                    - set(r["name"] for r in base_census["leaves"]))
    if gained != [ns + "gq_iff"]:
        failures.append(f"used-side attribution control: expected only gq_iff to become a leaf, got {gained}")
    else:
        print(f"OK — used-side attribution disabled in the driver: {gained} becomes a leaf although "
              f"a `simp` call uses it; the shared driver attributes `_simp_1` to its parent")

    # Auxiliary attribution in the driver: without it the generated theorems (`Qt.mk.injEq`, ...)
    # join the population, which is the failure the rule exists to prevent (in the real
    # environment: tens of thousands of them).
    checks += 1
    mutated = run_census(root, source=fixture_source(
        root, base, ("let (kept, cut) := cutAux rest", "let (kept, cut) := (rest, false)")))
    joined = sorted(set(mutated["population_names"]) - set(base_census["population_names"]))
    if ns + "Qt.mk.injEq" not in joined or base_census["population"] >= mutated["population"] \
            or mutated["excluded_auxiliary_theorems"] != 0:
        failures.append(f"auxiliary control: disabling attribution changed the population by {joined}")
    else:
        print(f"OK — auxiliary attribution disabled in the driver: {len(joined)} generated "
              f"theorems (e.g. {ns}Qt.mk.injEq) join the population; the shared driver excludes them")

    # Uses that leave no term trace: an rfl-proved lemma named only in a `simp only`, `dsimp only`
    # or `simpa` call, in a tactic macro, or through an `open`ed namespace is seen by the census as
    # a leaf and by the source scan as used. Each control replaces only that one call by `rfl`,
    # which puts the lemma back into the leaf set (the lemma is then used by nothing).
    checks += 1
    raw_leaves = {r["name"] for r in base_census["leaves"]}
    traceless = ["rfl_simp_lemma", "rfl_dsimp_lemma", "rfl_simpa_lemma", "rfl_macro_lemma",
                 "rfl_macro2_lemma", "rfl_open_lemma", "Sub.dup"]
    if not {ns + n for n in traceless} <= raw_leaves:
        failures.append("source-scan fixture: the census no longer shows the rfl-proved lemmas as "
                        f"leaves, so the source scan is untested (raw leaves {sorted(raw_leaves)})")
    for label, old, target in (
        ("`simp only [..]` call", "simp only [rfl_simp_lemma]", "rfl_simp_lemma"),
        ("`dsimp only [..]` call", "dsimp only [rfl_dsimp_lemma]", "rfl_dsimp_lemma"),
        ("`simpa [..]` call", "simpa [rfl_simpa_lemma]", "rfl_simpa_lemma"),
        ("tactic-macro `simp only` call", "simp only [rfl_macro_lemma]", "rfl_macro_lemma"),
        ("name in a macro that is never used", "exact rfl_macro2_lemma", "rfl_macro2_lemma"),
        ("call through an `open`ed namespace", "simp only [rfl_open_lemma]", "rfl_open_lemma"),
        ("call resolved through its own namespace", "simp only [dup]", "Sub.dup"),
    ):
        expect_leaves(f"{label} replaced by `rfl`",
                      replaced(base, old, "rfl", label), expected_base_leaves + [ns + target])

    # A name only in a comment, a docstring or a string is not a use; `-name` erases and is not one.
    expect_leaves("name only in a comment and a string",
                  replaced(base, "simp only [rfl_simp_lemma]",
                           "have _h : String := \"simp only [rfl_simp_lemma]\"\n"
                           "  rfl -- simp only [rfl_simp_lemma]", "comment"),
                  expected_base_leaves + [ns + "rfl_simp_lemma"])
    expect_leaves("name erased with `-name`",
                  replaced(base, "simp only [rfl_simp_lemma]",
                           "first | rfl | simp only [-rfl_simp_lemma]", "erase"),
                  expected_base_leaves + [ns + "rfl_simp_lemma"])
    # The short name must resolve to the theorem it denotes, not to a same-named one elsewhere:
    # `dup` inside `LeafFixture.Sub` is `LeafFixture.Sub.dup`, so `LeafFixture.dup` stays a leaf
    # (it is in the compliant leaf set above, with `Sub.dup` used).

    # Pure-Python controls of the source scan (no elaboration).
    scan_failures = scan_controls()
    checks += 1
    if scan_failures:
        failures.extend(scan_failures)
    else:
        print("OK — source scan: rewriting-tactic lemma lists, namespaces, `open`s, sections, "
              "macros, comments and strings resolved as specified")

    # External consumers: a Lean proof file removes a leaf, while a shell/Python mention is
    # retained on the row as report-only evidence.
    # Elaborate the interpolation regression too: this is executable evaluator syntax,
    # even though these tracked scripts are not imported into the library census.
    interpolation_source = '#eval IO.println s!"literal LeafFixture.simp_only_fact {LeafFixture.definition_leaf.succ}"\n'
    census_of(base + "\n" + interpolation_source)
    checks += 1
    external, lean_external = scan_external_sources(
        {"scripts/check-fixture.sh": "echo LeafFixture.definition_leaf\n",
         "scripts/check-fixture.py": "print('LeafFixture.definition_leaf')  # a /- in Python text\n",
         "scripts/ProofFixture.lean": interpolation_source},
        {ns + "definition_leaf", ns + "simp_only_fact"})
    external_result = analyze(base_census, {"_current": base}, external, lean_external)
    ext_rows = [r for r in external_result["definition_leaves"]
                if r["name"] == ns + "definition_leaf"]
    if external != {ns + "definition_leaf": ["scripts/ProofFixture.lean", "scripts/check-fixture.py",
                                             "scripts/check-fixture.sh"]} \
            or lean_external != {ns + "definition_leaf"} or ext_rows:
        failures.append(f"external consumer control: {external} {lean_external} {ext_rows}")
    else:
        report_only = analyze(base_census, {"_current": base},
                              {ns + "definition_leaf": ["scripts/check-fixture.sh"]}, set())
        rows = [r for r in report_only["definition_leaves"]
                if r["name"] == ns + "definition_leaf"]
        if len(rows) != 1 or rows[0]["external_consumers"] != ["scripts/check-fixture.sh"]:
            failures.append(f"non-Lean external consumer was not recorded: {rows}")
        else:
            print("OK — external consumers: Lean mentions count as uses; non-Lean script mentions "
                  "are recorded without silently exempting the leaf")

    # The statement fingerprint follows the type, not the proof or the binder names.
    checks += 1
    fp = {r["name"]: r["fp"] for r in base_census["leaves"]}
    proof_changed = census_of(replaced(base, "theorem headline_two : picked.val = 2 := rfl",
                                       "theorem headline_two : picked.val = 2 := by decide",
                                       "headline_two proof"))
    binder_renamed = census_of(replaced(base, "theorem fp_binder (n : Nat) : n + 0 = n := rfl",
                                        "theorem fp_binder (m : Nat) : m + 0 = m := rfl",
                                        "binder"))
    statement_changed = census_of(replaced(base, "theorem headline_two : picked.val = 2 := rfl",
                                           "theorem headline_two : picked.val = 3 + 0 - 1 := rfl",
                                           "headline_two statement"))
    f2 = lambda c, n: {r["name"]: r["fp"] for r in c["leaves"]}.get(ns + n)  # noqa: E731
    if not (f2(proof_changed, "headline_two") == fp[ns + "headline_two"]
            and f2(binder_renamed, "fp_binder") == fp[ns + "fp_binder"]
            and f2(statement_changed, "headline_two") != fp[ns + "headline_two"]
            and f2(statement_changed, "headline_two") is not None):
        failures.append("fingerprint: it must ignore proofs and binder names and follow the type")
    else:
        print("OK — statement fingerprint: unchanged by a new proof or a renamed binder, changed by "
              "a new statement")

    # The ledger: unseeded is informational, then new / changed / removed leaves are told apart.
    checks += 1
    result = analyze(base_census, {"_current": base})
    leaves = result["leaves"]
    definitions = result["definition_leaves"]
    if ledger_diff(None, leaves, definitions) is not None or "not yet seeded" not in review_lines(None, 1)[0]:
        failures.append("ledger: an unseeded ledger must be reported as such")
    doc = json.loads(ledger_document("t", leaves, definitions))
    ledger = doc["leaves"]
    if ledger_diff(ledger, leaves, definitions) != {"new": [], "changed": [], "removed": []} \
            or ledger[ns + "definition_leaf"]["kind"] != "definition":
        failures.append("ledger: a ledger generated from the leaves must show no difference")
    edited = dict(ledger)
    edited[ns + "headline_two"] = {"fp": "0" * 16, "kind": "theorem"}
    gone = {k: v for k, v in ledger.items() if k != ns + "headline_one"}
    edited_diff = ledger_diff(edited, leaves, definitions)
    gone_diff = ledger_diff(gone, leaves, definitions)
    extra_diff = ledger_diff({**ledger, "Blanc.deleted_result": {"fp": "1" * 16,
                                                                  "kind": "theorem"}},
                             leaves, definitions)
    if edited_diff != {"new": [], "changed": [ns + "headline_two"], "removed": []} \
            or gone_diff != {"new": [ns + "headline_one"], "changed": [], "removed": []} \
            or extra_diff != {"new": [], "changed": [], "removed": ["Blanc.deleted_result"]}:
        failures.append(f"ledger: unexpected differences {edited_diff} {gone_diff} {extra_diff}")
    elif "1 theorem/definition leaves new or changed" not in review_lines(edited_diff, len(leaves))[0]:
        failures.append("ledger: the review line must state the number of new or changed leaves")
    else:
        print("OK — review ledger: unseeded is informational; a changed statement, a new leaf and a "
              "gone leaf are each told apart")

    # The published count: a stale artifact is a regression, an equal one is not.
    checks += 1
    counts = counts_of(result)
    stale = {**counts, "leaves": counts["leaves"] + 1}
    if compare_count(counts, counts) or not compare_count(stale, counts) \
            or "regenerate" not in compare_count(stale, counts)[0]:
        failures.append("count: a stale committed count must be refused and an equal one accepted")
    else:
        print("OK — count artifact: an equal count passes, a stale one is a regression")

    # Fail-closed controls on the census itself.
    for label, mutate in (
        ("empty leaf set", lambda c: c.update(leaves=[], definition_leaves=[])),
        ("empty population", lambda c: c.update(population=0)),
        ("wrong schema", lambda c: c.update(schema=99)),
        ("missing field", lambda c: c.pop("population_names")),
        ("row without a fingerprint", lambda c: c["leaves"][0].pop("fp")),
    ):
        checks += 1
        broken = json.loads(json.dumps(base_census))
        mutate(broken)
        try:
            analyze(broken, {"_current": base})
        except LeafAuditError:
            print(f"OK — {label}: refused")
        else:
            failures.append(f"{label}: an untrustworthy census was accepted")

    # The attribute-vocabulary guard refuses a new attribute head and an unexported use attribute.
    checks += 1
    unclassified = scan_attributes_text("A", "@[simp, norm_cast] theorem x : True := trivial\n"
                                             "@[local irreducible] def y := 1\n")
    scoped_use = scan_attributes_text("B", "@[local simp] theorem z : True := trivial\n")
    fine = scan_attributes_text("C", "@[simp, ext] theorem x : True := trivial\n"
                                     "attribute [local irreducible] y\n"
                                     "/- @[local simp] in a comment -/\n")
    if len(unclassified) != 1 or "norm_cast" not in unclassified[0] or len(scoped_use) != 1 \
            or fine:
        failures.append(f"attribute guard: {unclassified} {scoped_use} {fine}")
    else:
        print("OK — attribute guard: an unclassified attribute and an unexported use attribute are "
              "refused, classified ones and comments pass")

    if failures:
        for failure in failures:
            print(f"REGRESSION — leaf audit self-test: {failure}")
        return 1
    print(f"OK — leaf audit self-test: {checks} controls bite and the compliant fixture is green")
    return 0


# --------------------------------------------------------------------------------------------

def main(argv: List[str]) -> int:
    root = Path(__file__).resolve().parent.parent
    if not argv or argv[0] not in ("check", "generate", "review", "self-test"):
        print(__doc__)
        return 2
    try:
        if argv[0] == "check" and len(argv) == 1:
            return cmd_check(root)
        if argv[0] == "generate" and (len(argv) == 1 or argv[1:] == ["--ledger"]):
            return cmd_generate(root, ledger=len(argv) == 2)
        if argv[0] == "generate" and len(argv) == 4 and argv[1:3] == ["--ledger", "--unreviewed"]:
            return cmd_generate(root, ledger=True, unreviewed_path=Path(argv[3]))
        if argv[0] == "review" and len(argv) == 1:
            return cmd_review(root)
        if argv[0] == "self-test" and len(argv) == 1:
            return self_test(root)
    except LeafAuditError as exc:
        print(f"REGRESSION — leaf audit: {exc}")
        return 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
