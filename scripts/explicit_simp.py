#!/usr/bin/env python3
"""Bounded pure-Python syntax inventory and verification control for explicit simps in Blanc.

Scans Blanc Lean sources (Blanc.lean, every Blanc/**/*.lean, and every other Git-tracked
*.lean outside .lake except the named EXEMPT_FIXTURES) for:
(a) Simp registrations:
    - Declaration attributes: @[simp], @[scoped simp], @[local simp], @[simp high],
      @[simp ↓], @[simp ←], @[← simp], @[↓ simp], grouped attributes like @[simp, inline], etc.
    - Attribute commands: attribute [simp] foo, local attribute [simp] foo,
      scoped attribute [simp] foo, attribute [simp high] foo, etc.
(b) Implicit simp/simpa/simp_all/dsimp/norm_num tactics and suggestion variants:
    - Calls to simp, simpa, simp_all, dsimp, norm_num and simp-family suggestion variants
      that do NOT use `only`.
    - Exact explicit `only` forms may include optional configuration parentheses before
      `only` (e.g. `simp (config := ...) only [...]`), config flags (e.g. `simp +zeta only [...]`,
      `simp -zeta only [...]`), and locations after lists (`at h`, `using ...`).
    - Macro quotation bodies (e.g. `(tactic| simp)`) are inspected and caught.
(c) Aesop builtin simplification:
    - Retained aesop calls must start with a literal config whose top-level
      enableSimp field is exactly false. Duplicate config arguments refuse.

Inventory and control aid scope (limits and unresolved lexical ambiguity):
This scanner is a bounded pure-Python inventory and control aid for the Lean parser
collector; it does NOT claim full syntax-aware completeness, which requires Lean elaboration.
Known unresolved lexical ambiguities include:
- Arbitrary custom syntax and DSLs: custom user tactics or DSL macros embedding `simp`
  tokens in non-standard productions without macro quotation syntax.
- Antiquotations in macro quotations: antiquoted tactic trees (e.g. `$x:tactic`, `$(...)`)
  where the tactic head or arguments are generated or substituted dynamically.
- Non-tactic Lean expressions: terms where `simp` appears outside comments, strings, and
  dot-qualified paths (e.g. a local binder `(simp : Nat)`).
- Elaboration-time macro expansions: tactics emitted during elaboration that do not exist
  in concrete source text.

Lexical guarantees:
- Reuses `leaf_audit.strip_comments_and_strings` so single-line comments (`--`),
  nested block comments (`/- ... -/`), docstrings (`/-- ... -/`), character literals
  and string literals (e.g. `syntax "simp" : tactic`) are blanked out while preserving
  exact offsets, line numbers, and column numbers.
- Macro quotations using backticks (e.g. `(tactic| simp)`) are preserved and inspected.
- Dot lookaround and token boundaries prevent false positives on longer identifiers
  (simp_rw, simp_arith) and qualified references or projections (Lean.Meta.simp, ctx.simp, simp.foo).

Modes:
- `inventory`: Scans the tree and reports findings and spans. Exits 0 on present files.
- `check`: Enforces 0 implicit simp calls and 0 simp registrations. Exits 0 if clean, 1 on violations.
- Fails closed with exit code 2 on read errors, malformed comments, or missing source tree.
"""

from __future__ import annotations

import argparse
import bisect
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

# Shared library first: reuse leaf_audit's comment/string stripper
sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    from leaf_audit import LeafAuditError, strip_comments_and_strings
    from module_path_policy import (
        ModulePathPolicyError, resolve_bound_file, resolve_source_file, walk_module_files,
    )
except ImportError as exc:
    raise SystemExit(f"ERROR: cannot import leaf_audit: {exc}")


# ---------------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Finding:
    """A detected simp registration or implicit simp tactic call."""
    path: str
    line: int
    column: int
    kind: str
    category: str  # "registration" or "implicit-tactic"
    snippet: str


class ExplicitSimpError(Exception):
    """Raised when source cannot be read or parsed safely."""


# ---------------------------------------------------------------------------
# Lexical analysis helpers
# ---------------------------------------------------------------------------

_PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}


def balanced_end(code: str, start: int, opener: str, closer: str) -> int:
    """Index of the closer matching opener at `start`, or -1 if unbalanced."""
    depth = 0
    n = len(code)
    for i in range(start, n):
        c = code[i]
        if c == opener:
            depth += 1
        elif c == closer:
            depth -= 1
            if depth == 0:
                return i
    return -1


def split_top_level(text: str, start_offset: int = 0) -> List[Tuple[int, int, str]]:
    """Return list of (start_offset, end_offset, substring) split by comma at depth 0."""
    parts: List[Tuple[int, int, str]] = []
    stack: List[str] = []
    begin = 0
    for i, c in enumerate(text):
        if c in _PAIRS:
            stack.append(_PAIRS[c])
        elif stack and c == stack[-1]:
            stack.pop()
        elif c == "," and not stack:
            parts.append((start_offset + begin, start_offset + i, text[begin:i]))
            begin = i + 1
    parts.append((start_offset + begin, start_offset + len(text), text[begin:]))
    return parts


# ---------------------------------------------------------------------------
# Simp registration and implicit tactic detectors
# ---------------------------------------------------------------------------

# Tactic heads including norm_num, whose pinned driver uses the global simp set
# unless only is supplied. Optional suggestion/bang marks remain lexically inspected.
# Negative lookbehind and lookahead ensure longer identifiers (simp_rw, simp_arith, simple, etc.)
# and qualified references or projections (Lean.Meta.simp, ctx.simp, simp.foo) are NOT matched.
TACTIC_HEAD_RE = re.compile(
    r"(?<![\w.'!?])(simp_all|simpa|dsimp|simp|norm_num)(?:[?!]+)?(?![\w.'!?])"
)

# Retained Aesop must disable builtin simplification.
AESOP_HEAD_RE = re.compile(r"(?<![\w.'!?])aesop(?:[?!]+)?(?![\w.'!?])")
CONFIG_FIELD_RE = re.compile(r"([A-Za-z_][\w']*)\s*:=")


def aesop_simp_disabled(code: str, start: int) -> bool:
    """Recognize the house form, not arbitrary Lean config computation.

    Comment/string masking has already preserved offsets. A literal top-level
    false field disables the pinned builtin normalization rule; nested fields,
    Boolean expressions, and later config overrides grant no lexical credit.
    Actual elaboration and custom-rule coverage are separate migration evidence.
    """
    pos = start
    while pos < len(code) and code[pos].isspace():
        pos += 1
    if pos >= len(code) or code[pos] != "(":
        return False
    end = balanced_end(code, pos, "(", ")")
    if end < 0:
        return False
    config = code[pos + 1:end]
    prefix = re.match(r"\s*config\s*:=\s*\{", config)
    if prefix is None:
        return False
    opening = prefix.end() - 1
    closing = balanced_end(config, opening, "{", "}")
    if closing < 0 or config[closing + 1:].strip():
        return False
    fields = config[opening + 1:closing]
    assignments = []
    stack = []
    offset = 0
    while offset < len(fields):
        char = fields[offset]
        if char in _PAIRS:
            stack.append(_PAIRS[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif not stack:
            match = CONFIG_FIELD_RE.match(fields, offset)
            if match:
                assignments.append((match.group(1), offset, match.end()))
                offset = match.end()
                continue
        offset += 1
    if stack or not assignments or fields[:assignments[0][1]].strip(" \t\r\n,"):
        return False
    values = []
    for index, (name, _, value_start) in enumerate(assignments):
        value_end = assignments[index + 1][1] if index + 1 < len(assignments) else len(fields)
        if name == "enableSimp":
            values.append(fields[value_start:value_end].strip(" \t\r\n,"))
    if values != ["false"]:
        return False
    # A later config could override the first one. Other parenthesized Aesop
    # rule arguments are allowed, with their actual rules reviewed separately.
    pos = end + 1
    while True:
        while pos < len(code) and code[pos].isspace():
            pos += 1
        if pos >= len(code) or code[pos] != "(":
            return True
        end = balanced_end(code, pos, "(", ")")
        if end < 0:
            return False
        if re.match(r"\s*config\s*:=", code[pos + 1:end]):
            return False
        pos = end + 1


CONFIG_FLAG_RE = re.compile(r"[+-]\s*[A-Za-z_][\w.]*")

# Explicit 'only' keyword immediately following tactic or config
ONLY_RE = re.compile(r"only(?![\w'!?])")

# Identifier regex matching Lean identifier components
IDENT_RE = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")

# Declaration attribute start: @[ or @ [
DECL_ATTR_START_RE = re.compile(r"@\s*\[")

# Attribute command start: (local|scoped)? attribute [
ATTR_CMD_START_RE = re.compile(
    r"(?<![\w'!?])(?:(?:local|scoped)\s+)?attribute\s*\["
)

# Prefix modifiers that can precede simp in an attribute item
ATTR_PREFIX_STRIP_RE = re.compile(r"^(?:(?:local|scoped)\s+|[←↓↑]|<-)+\s*")


def _line_starts_of(text: str) -> List[int]:
    """Compute line start offsets (1-indexed line numbers map to line_starts[line - 1])."""
    return [0] + [m.end() for m in re.finditer(r"\n", text)]


def _line_col_of(line_starts: List[int], offset: int) -> Tuple[int, int]:
    """Map character offset to (1-indexed line, 1-indexed column)."""
    line_idx = bisect.bisect_right(line_starts, offset) - 1
    line = line_idx + 1
    col = offset - line_starts[line_idx] + 1
    return line, col


def scan_source(code_raw: str, path: str) -> List[Finding]:
    """Scan a single Lean file's content for simp registrations and implicit simp calls.

    Raises ExplicitSimpError on unparseable block comments or malformed syntax.
    """
    try:
        code = strip_comments_and_strings(code_raw, path)
    except LeafAuditError as exc:
        raise ExplicitSimpError(f"{path}: comment/string stripping error: {exc}")

    line_starts = _line_starts_of(code)
    lines_raw = code_raw.split("\n")

    def snippet_at(offset: int) -> str:
        l, _ = _line_col_of(line_starts, offset)
        if 1 <= l <= len(lines_raw):
            return lines_raw[l - 1].strip()
        return ""

    findings: List[Finding] = []
    # Set of (start, end) spans for attribute brackets to prevent double-matching as tactics
    attr_spans: List[Tuple[int, int]] = []

    # -----------------------------------------------------------------------
    # Part (a): Simp registrations
    # -----------------------------------------------------------------------

    # 1. Declaration attributes: @[...]
    for m in DECL_ATTR_START_RE.finditer(code):
        open_bracket = code.find("[", m.start())
        close_bracket = balanced_end(code, open_bracket, "[", "]")
        if close_bracket < 0:
            raise ExplicitSimpError(f"{path}: unterminated declaration attribute bracket at offset {open_bracket}")
        attr_spans.append((m.start(), close_bracket + 1))

        inner = code[open_bracket + 1:close_bracket]
        for item_start, item_end, item_text in split_top_level(inner, open_bracket + 1):
            s = item_text.strip()
            if not s or s.startswith("-"):
                continue  # negation/unregistration: attribute [-simp]
            # Strip optional local/scoped/arrow prefixes
            stripped = ATTR_PREFIX_STRIP_RE.sub("", s)
            head_m = IDENT_RE.match(stripped)
            if head_m and head_m.group(0) == "simp":
                # Pinpoint exact offset of 'simp' token
                simp_match = re.search(r"\bsimp\b", item_text)
                simp_off = item_start + (simp_match.start() if simp_match else 0)
                l, c = _line_col_of(line_starts, simp_off)
                findings.append(Finding(
                    path=path,
                    line=l,
                    column=c,
                    kind="simp-attr-decl",
                    category="registration",
                    snippet=snippet_at(simp_off),
                ))

    # 2. Attribute commands: attribute [...]
    for m in ATTR_CMD_START_RE.finditer(code):
        open_bracket = code.find("[", m.start())
        close_bracket = balanced_end(code, open_bracket, "[", "]")
        if close_bracket < 0:
            raise ExplicitSimpError(f"{path}: unterminated attribute command bracket at offset {open_bracket}")
        attr_spans.append((m.start(), close_bracket + 1))

        inner = code[open_bracket + 1:close_bracket]
        for item_start, item_end, item_text in split_top_level(inner, open_bracket + 1):
            s = item_text.strip()
            if not s or s.startswith("-"):
                continue
            stripped = ATTR_PREFIX_STRIP_RE.sub("", s)
            head_m = IDENT_RE.match(stripped)
            if head_m and head_m.group(0) == "simp":
                simp_match = re.search(r"\bsimp\b", item_text)
                simp_off = item_start + (simp_match.start() if simp_match else 0)
                l, c = _line_col_of(line_starts, simp_off)
                findings.append(Finding(
                    path=path,
                    line=l,
                    column=c,
                    kind="simp-attr-cmd",
                    category="registration",
                    snippet=snippet_at(simp_off),
                ))

    # -----------------------------------------------------------------------
    # Part (b): Implicit simp tactics
    # -----------------------------------------------------------------------

    def is_inside_attr(off: int) -> bool:
        for b_start, b_end in attr_spans:
            if b_start <= off < b_end:
                return True
        return False

    n_code = len(code)
    for m in TACTIC_HEAD_RE.finditer(code):
        tactic_start = m.start()
        tactic_end = m.end()

        # Attribute bracket tokens were already classified
        if is_inside_attr(tactic_start):
            continue

        # Check line context: skip 'import ...' and 'namespace ...'
        line_num, col_num = _line_col_of(line_starts, tactic_start)
        line_start_off = line_starts[line_num - 1]
        line_str = code[line_start_off:line_starts[line_num] if line_num < len(line_starts) else n_code].lstrip()
        if line_str.startswith(("import ", "namespace ", "end ")):
            continue

        # Lookahead after tactic head: consume config parens (...) and config flags (+zeta, -zeta, etc.)
        pos = tactic_end
        while pos < n_code:
            while pos < n_code and code[pos].isspace():
                pos += 1
            if pos >= n_code:
                break
            if code[pos] == "(":
                close_paren = balanced_end(code, pos, "(", ")")
                if close_paren < 0:
                    raise ExplicitSimpError(f"{path}: unterminated config parenthesis at line {line_num}")
                pos = close_paren + 1
            elif code[pos] in ("+", "-"):
                flag_m = CONFIG_FLAG_RE.match(code, pos)
                if flag_m:
                    pos = flag_m.end()
                else:
                    break
            else:
                break

        # Check if immediately followed by 'only'
        if ONLY_RE.match(code, pos):
            # Safe explicit form: simp only [...], simp +zeta only [...], simp (config := ...) only [...], etc.
            continue

        # No 'only' following: this is an implicit simp call
        tactic_name = m.group(0)
        findings.append(Finding(
            path=path,
            line=line_num,
            column=col_num,
            kind=f"implicit-{tactic_name}",
            category="implicit-tactic",
            snippet=snippet_at(tactic_start),
        ))

    for match in AESOP_HEAD_RE.finditer(code):
        if is_inside_attr(match.start()):
            continue
        line, _ = _line_col_of(line_starts, match.start())
        context = code[line_starts[line - 1]:].lstrip()
        if context.startswith(("import ", "namespace ", "end ")):
            continue
        if aesop_simp_disabled(code, match.end()):
            continue
        line, column = _line_col_of(line_starts, match.start())
        findings.append(Finding(
            path=path, line=line, column=column,
            kind="implicit-aesop-simp", category="implicit-tactic",
            snippet=snippet_at(match.start()),
        ))

    # Sort findings by (line, column, kind) deterministically
    return sorted(findings, key=lambda f: (f.line, f.column, f.kind))


# ---------------------------------------------------------------------------
# Repository discovery
# ---------------------------------------------------------------------------

# Deliberate fixtures and controls outside Blanc/ that must keep implicit
# simplification or simp registrations as their subject matter. Every entry must
# name a tracked file; a stale or Blanc/ entry refuses the population.
EXEMPT_FIXTURES: Dict[str, str] = {
    "scripts/fixtures/leaf-audit/compliant.lean":
        "leaf-audit self-test fixture: its @[simp] lemmas and `by simp`/`simpa`/`simp_all` proofs"
        " are the cases leaf_audit.py self-test asserts (a simp attribute no longer exempts a leaf;"
        " a `by simp` use is attributed through the generated _simp_1 auxiliary)",
    "scripts/SimpaUsingSyntaxControl.lean":
        "parser control for the simpa-using migration tooling: its `(tactic| simpa ...)`"
        " quotation is a syntax pattern it matches, not a proof call",
}


def tracked_lean_files(root: Path) -> List[str]:
    """Every Git-tracked `*.lean` path outside `.lake`, fail-closed without Git."""
    try:
        completed = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
            check=True, capture_output=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ExplicitSimpError(f"cannot list tracked Lean sources under {root}: {exc}")
    paths = [raw.decode("utf-8") for raw in completed.stdout.split(b"\0") if raw]
    return sorted(p for p in paths if ".lake" not in p.split("/"))


def discover_lean_files(root: Path, targets: Optional[Sequence[str]] = None) -> List[Path]:
    """Find the production population.

    Blanc.lean and Blanc/**/*.lean (walked, so an untracked new module is still
    scanned) plus every other Git-tracked `*.lean` outside `.lake` (Main.lean,
    lakefile.lean, scripts/**), except the named EXEMPT_FIXTURES.
    Fails closed if targets, Git, an exemption or repository sources cannot be found.
    """
    try:
        if targets:
            resolved = []
            for target in targets:
                if not target.endswith(".lean"):
                    raise ExplicitSimpError(f"target is not a Lean source: {target}")
                resolved.append(resolve_bound_file(
                    root, target, allow_missing=False, site="explicit-simp-target",
                ))
            return sorted(set(resolved))

        root_file = resolve_source_file(root, "Blanc.lean", site="explicit-simp-root")
        modules = walk_module_files(root, site="explicit-simp-population")
        if not modules:
            raise ExplicitSimpError(f"empty Blanc module population under {root}")
        tracked = tracked_lean_files(root)
        for exempt in EXEMPT_FIXTURES:
            if exempt == "Blanc.lean" or exempt.startswith("Blanc/"):
                raise ExplicitSimpError(f"production module cannot be exempt: {exempt}")
            if exempt not in tracked:
                raise ExplicitSimpError(f"stale explicit-simp exemption (not a tracked Lean file): {exempt}")
        extra = [
            resolve_bound_file(root, rel, allow_missing=False, site="explicit-simp-tracked")
            for rel in tracked
            if rel not in EXEMPT_FIXTURES and rel != "Blanc.lean" and not rel.startswith("Blanc/")
        ]
        return sorted(set([root_file, *modules, *extra]))
    except ModulePathPolicyError as error:
        raise ExplicitSimpError(str(error)) from error


# ---------------------------------------------------------------------------
# Inventory and Report Aggregation
# ---------------------------------------------------------------------------

def aggregate_report(root: Path, files: Sequence[Path]) -> Tuple[List[Finding], Dict]:
    """Scan all files and return (findings_list, summary_dict)."""
    all_findings: List[Finding] = []
    file_spans: Dict[str, Dict] = {}
    counts_by_kind: Dict[str, int] = {}
    counts_by_category: Dict[str, int] = {"registration": 0, "implicit-tactic": 0}

    for p in files:
        rel_path = str(p.relative_to(root)) if p.is_relative_to(root) else str(p)
        try:
            content = p.read_text(encoding="utf-8")
        except OSError as exc:
            raise ExplicitSimpError(f"{rel_path}: cannot read file: {exc}")
        except UnicodeDecodeError as exc:
            raise ExplicitSimpError(f"{rel_path}: UTF-8 decode error: {exc}")

        file_findings = scan_source(content, rel_path)
        if file_findings:
            first_line = min(f.line for f in file_findings)
            last_line = max(f.line for f in file_findings)
            file_spans[rel_path] = {
                "count": len(file_findings),
                "first_line": first_line,
                "last_line": last_line,
            }
            for f in file_findings:
                counts_by_kind[f.kind] = counts_by_kind.get(f.kind, 0) + 1
                counts_by_category[f.category] = counts_by_category.get(f.category, 0) + 1
            all_findings.extend(file_findings)

    # Sort all findings by path, line, column, kind
    all_findings.sort(key=lambda f: (f.path, f.line, f.column, f.kind))

    summary = {
        "files_scanned": len(files),
        "files_with_findings": len(file_spans),
        "total_findings": len(all_findings),
        "counts_by_category": counts_by_category,
        "counts_by_kind": dict(sorted(counts_by_kind.items())),
        "file_spans": dict(sorted(file_spans.items())),
    }

    return all_findings, summary


def format_human_inventory(summary: Dict, findings: Sequence[Finding]) -> str:
    """Render a human-readable inventory summary with migration spans."""
    lines = [
        "=== Blanc Explicit Simp Inventory (Lexical Aid) ===",
        "Inventory/control aid for Lean parser collector; does not claim syntax-aware",
        "completeness over arbitrary custom DSL syntax, antiquotations, or macro elaboration.",
        f"Files scanned: {summary['files_scanned']}",
        f"Files with findings: {summary['files_with_findings']}",
        f"Total findings: {summary['total_findings']}",
        "",
        "Counts by category:",
        f"  Registrations (attributes):     {summary['counts_by_category']['registration']}",
        f"  Implicit tactic calls:          {summary['counts_by_category']['implicit-tactic']}",
        "",
        "Counts by kind:",
    ]
    for kind, count in summary["counts_by_kind"].items():
        lines.append(f"  {kind:25s}: {count}")

    if summary["file_spans"]:
        lines.extend(["", "File spans for migration:"])
        for path, info in summary["file_spans"].items():
            lines.append(
                f"  {path:45s}: {info['count']:3d} finding(s) (lines {info['first_line']}-{info['last_line']})"
            )

    if findings:
        lines.extend(["", "Sample site inventory (first 50):"])
        for f in findings[:50]:
            lines.append(f"  {f.path}:{f.line}:{f.column}: [{f.kind}] {f.snippet}")
        if len(findings) > 50:
            lines.append(f"  ... and {len(findings) - 50} more sites (use --json for full list)")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI entrypoint
# ---------------------------------------------------------------------------

def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Inventory and check explicit simps in Blanc."
    )
    parser.add_argument(
        "mode",
        choices=["inventory", "check"],
        help="'inventory' reports occurrences without failing; 'check' fails on any violation.",
    )
    parser.add_argument(
        "targets",
        nargs="*",
        help="Optional specific Lean source files to check (defaults to Blanc.lean, Blanc/**/*.lean and every other tracked *.lean outside .lake except EXEMPT_FIXTURES).",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root directory (defaults to parent of scripts/).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit deterministic JSON output.",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv if argv is not None else sys.argv[1:])
    root = args.root.resolve()

    try:
        files = discover_lean_files(root, args.targets if args.targets else None)
        findings, summary = aggregate_report(root, files)
    except ExplicitSimpError as exc:
        sys.stderr.write(f"ERROR: {exc}\n")
        return 2

    # Deterministic JSON output
    if args.json:
        payload = {
            "summary": summary,
            "findings": [asdict(f) for f in findings],
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        if args.mode == "inventory":
            print(format_human_inventory(summary, findings))
        else:  # check mode
            if findings:
                print(f"FAIL: explicit-simp check failed with {len(findings)} violation(s):")
                for f in findings:
                    print(f"  {f.path}:{f.line}:{f.column}: [{f.kind}] {f.snippet}")
            else:
                print(f"OK: explicit-simp check passed: 0 violations across {summary['files_scanned']} files.")

    if args.mode == "check" and findings:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
