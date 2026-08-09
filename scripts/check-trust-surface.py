#!/usr/bin/env python3
"""Fail-closed source-trust scan for Blanc's imported library closure.

The inventory is the exact transitive local import closure of ``Blanc.lean``.
Unimported Lean helpers and generators are deliberately outside this gate;
adding an import brings a module into scope immediately.  Every matching line,
including a comment-only mention, must equal a reviewed allowlist row.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Iterable


RULES = (
    ("S1-sorry", re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")),
    ("S2-axiom", re.compile(r"(?<![A-Za-z0-9_])axiom(?![A-Za-z0-9_])")),
    ("S3-opaque", re.compile(r"(?<![A-Za-z0-9_])opaque(?![A-Za-z0-9_])")),
    ("S4-extern", re.compile(r"@\s*\[\s*extern(?:\s|\]|\()")),
    ("S5-implemented-by", re.compile(r"(?<![A-Za-z0-9_])implemented_by(?![A-Za-z0-9_])")),
    ("S6-native-decide", re.compile(r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])")),
    ("S7-partial-def", re.compile(r"(?<![A-Za-z0-9_])partial\s+def(?![A-Za-z0-9_])")),
    ("S8-dbg-trace", re.compile(r"(?<![A-Za-z0-9_])dbg_trace(?![A-Za-z0-9_])")),
)

IMPORT = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")


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
        for line in path.read_text(encoding="utf-8").splitlines():
            text = normalize(line)
            for rule, pattern in RULES:
                if pattern.search(line):
                    rows.add(f"{rule} {rel} {text}")
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
