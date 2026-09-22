#!/usr/bin/env python3
"""Regression controls for ``check-trust-surface.py``'s code-only scan.

Each case builds a one-module temporary tree (``Blanc.lean`` only) with an
empty allowlist and runs the real checker's ``main`` on it.  A forbidden token
in code must fail (exit 1); the same token in a comment or literal must pass
(exit 0); anything the lexer cannot classify must be a setup failure (exit 2).
No Lean toolchain is used.
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
import tempfile
from pathlib import Path


SCRIPT = Path(__file__).with_name("check-trust-surface.py")

CODE, CLEAN, SETUP = 1, 0, 2

CASES: tuple[tuple[str, int, str], ...] = (
    ("token in code", CODE, "theorem t : True := sorry\n"),
    ("each rule still bites in code", CODE, "axiom a : False\n"),
    ("extern attribute in code", CODE, '@[extern "c"] opaque f : Nat\n'),
    ("line comment", CLEAN, "-- this proof does not use sorry or an axiom\n"),
    ("trailing line comment", CLEAN, "def x := 1 -- no native_decide here\n"),
    ("block comment", CLEAN, "/- an opaque word -/\ndef x := 1\n"),
    ("nested block comment", CLEAN,
     "/- outer /- inner -/ still comment: sorry -/\ndef x := 1\n"),
    ("code after nested block comment", CODE,
     "/- outer /- inner -/ still comment -/ theorem t : True := sorry\n"),
    ("doc comment", CLEAN, "/-- not `native_decide` -/\ndef x := 1\n"),
    ("module doc", CLEAN, "/-! No hash axiom is assumed. -/\ndef x := 1\n"),
    ("multi-line doc comment", CLEAN,
     "/--\nThis is not a cryptographic\ncorrectness axiom.\n-/\ndef x := 1\n"),
    ("string literal", CLEAN, 'def s : String := "sorry, dbg_trace"\n'),
    ("raw string literal", CLEAN, 'def s : String := r#"a "partial def" b"#\n'),
    ("escaped quote in string", CLEAN, 'def s : String := "\\" sorry"\n'),
    ("line comment marker inside a string hides nothing", CODE,
     'def s : String := "--" ++ toString sorry\n'),
    ("block comment marker inside a string hides nothing", CODE,
     'def s : String := "/-" ++ toString sorry ++ "-/"\n'),
    ("quote inside a comment opens no string", CODE,
     '-- a " quote\ntheorem t : True := sorry\n'),
    ("character literal quote opens no string", CODE,
     "def c : Char := '\"'\ntheorem t : True := sorry\n"),
    ("primed name is not a character literal", CODE,
     "def h' := 1\ndef g' := 2\ntheorem t : True := sorry\n"),
    ("interpolation hole is code", CODE, 'def s : String := s!"{sorry}"\n'),
    ("interpolation hole with nested string is code", CODE,
     'def s : String := s!"{f "x" (sorry : Nat)}"\n'),
    ("literal braces in plain strings do not hide code", CODE,
     'def s : String := "{" ++ toString sorry ++ "}"\n'),
    ("unterminated block comment", SETUP, "/- sorry\ndef x := 1\n"),
    ("unterminated nested block comment", SETUP, "/- /- sorry -/\ndef x := 1\n"),
    ("unterminated string", SETUP, 'def s : String := "sorry\n'),
    ("unterminated raw string", SETUP, 'def s : String := r#"sorry"\n'),
)


def load_checker():
    spec = importlib.util.spec_from_file_location("check_trust_surface_tested", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run(module, source: str, allow: str = "") -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "scripts").mkdir()
        (root / "Blanc.lean").write_text(source, encoding="utf-8")
        (root / "scripts" / "trust-surface-allow.txt").write_text(allow, encoding="utf-8")
        argv = sys.argv
        sys.argv = [str(SCRIPT), "--root", str(root)]
        out = io.StringIO()
        try:
            with contextlib.redirect_stdout(out):
                status = module.main()
        finally:
            sys.argv = argv
        return status, out.getvalue()


def main() -> int:
    module = load_checker()
    failures: list[str] = []
    for name, expected, source in CASES:
        status, output = run(module, source)
        if status != expected:
            failures.append(f"{name}: exit {status}, expected {expected}\n{output}")

    # Exact allowlisting still works, and a comment-only row is now stale.
    code = "theorem t : True := sorry\n"
    status, output = run(module, code, "S1-sorry Blanc.lean theorem t : True := sorry ## ok\n")
    if status != CLEAN:
        failures.append(f"allowlisted code occurrence: exit {status}\n{output}")
    status, output = run(module, "-- sorry\n", "S1-sorry Blanc.lean -- sorry ## prose\n")
    if status != CODE or "stale allowlist row" not in output:
        failures.append(f"comment-only allowlist row must be stale: exit {status}\n{output}")

    if failures:
        for failure in failures:
            print(f"FAIL — {failure}")
        print(f"REGRESSION — trust-surface controls: {len(failures)} of "
              f"{len(CASES) + 2} failed")
        return 1
    print(f"OK — trust-surface controls: {len(CASES) + 2} cases")
    return 0


if __name__ == "__main__":
    sys.exit(main())
