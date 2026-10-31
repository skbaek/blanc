#!/usr/bin/env python3
"""Growth ledger between two commits: net lines, shard families, literal density.

Report-only. It exists because every gate was green both before and after the
37k-line signing-hash bloat was removed (the consolidation register, section
7.1): no check measured net proof text per fact, so bloat moved between shapes
(many small modules, qualified names, literal tables) instead of disappearing.
The master reads this ledger before merging a worker branch; a worker quotes it
in its growth report.

    python3 scripts/report-growth.py BASE [HEAD]      # HEAD defaults to HEAD
    python3 scripts/report-growth.py BASE --worktree  # BASE against the working tree
    python3 scripts/report-growth.py --self-test

Three tables, all from `git diff --numstat` and the blob bytes at each side:

* **Net lines per family.** Added, removed and net lines, and file count at each
  side, grouped by `scripts/module_family.py` (a nested module's directory, a
  top-level module's shard stem, or the first two path components of any other
  file), with Lean and non-Lean totals.
* **Shard families.** A family whose Lean file count grew, or that holds a shard
  group (three or more files sharing a stem once a trailing shard number is
  removed, e.g. `SigningRounds00..28`) at HEAD. A new shard group is the shape
  the module-size warning cannot see.
* **Literal density.** For every family whose Lean text changed: the share of
  non-whitespace characters that sit in numeric literals (`0x...` and decimal
  runs of two or more digits) at each side, and the literal characters added.
  A family whose density is at least 25% at HEAD and whose literal characters
  grew is marked `LITERAL`: hand-written proof text that is mostly constants is
  usually a generator's or a kernel decision's job.

Exit 0 whenever both revisions resolve; the verdict line ends `(report-only)`.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from module_family import module_family, shard_stem  # noqa: E402

LITERAL_RE = re.compile(r"\b0x[0-9a-fA-F_]+\b|\b[0-9][0-9_]+\b")
LITERAL_FLAG_DENSITY = 0.25
SHARD_GROUP_MIN = 3
WORKTREE = None  # sentinel revision meaning "the working tree"


class GrowthError(RuntimeError):
    pass


def git(root: pathlib.Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(["git", *args], cwd=str(root), capture_output=True,
                            text=True, check=False)
    if check and result.returncode != 0:
        raise GrowthError(f"git {' '.join(args)}: {result.stderr.strip()}")
    return result.stdout


def resolve(root: pathlib.Path, revision: str) -> str:
    return git(root, "rev-parse", "--verify", f"{revision}^{{commit}}").strip()


def tree_paths(root: pathlib.Path, revision: Optional[str]) -> List[str]:
    if revision is WORKTREE:
        tracked = git(root, "ls-files", "-z").split("\0")
        untracked = git(root, "ls-files", "--others", "--exclude-standard", "-z").split("\0")
        return sorted({p for p in tracked + untracked if p and (root / p).is_file()})
    return sorted(p for p in git(root, "ls-tree", "-r", "-z", "--name-only", revision).split("\0") if p)


def blob(root: pathlib.Path, revision: Optional[str], path: str) -> str:
    if revision is WORKTREE:
        try:
            return (root / path).read_text(encoding="utf-8", errors="replace")
        except OSError:
            return ""
    result = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=str(root),
                            capture_output=True, check=False)
    return result.stdout.decode("utf-8", errors="replace") if result.returncode == 0 else ""


def numstat(root: pathlib.Path, base: str, head: Optional[str]) -> List[Tuple[int, int, str]]:
    args = ["diff", "--numstat", "-z", "--no-renames", base]
    if head is not WORKTREE:
        args.append(head)
    output = git(root, *args)
    rows: List[Tuple[int, int, str]] = []
    for record in output.split("\0"):
        if not record:
            continue
        added, removed, path = record.split("\t", 2)
        if added == "-":  # binary
            continue
        rows.append((int(added), int(removed), path))
    if head is WORKTREE:
        for path in git(root, "ls-files", "--others", "--exclude-standard", "-z").split("\0"):
            if path and (root / path).is_file():
                text = blob(root, WORKTREE, path)
                rows.append((len(text.splitlines()), 0, path))
    return rows


@dataclass
class Family:
    added: int = 0
    removed: int = 0
    base_files: int = 0
    head_files: int = 0
    base_chars: int = 0
    head_chars: int = 0
    base_literal: int = 0
    head_literal: int = 0
    lean_changed: bool = False
    head_stems: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    base_stems: Dict[str, int] = field(default_factory=lambda: defaultdict(int))


def literal_measure(text: str) -> Tuple[int, int]:
    total = sum(1 for ch in text if not ch.isspace())
    literal = sum(len(m.group(0)) for m in LITERAL_RE.finditer(text))
    return total, literal


def ledger(root: pathlib.Path, base: str, head: Optional[str]) -> Dict[str, Family]:
    families: Dict[str, Family] = defaultdict(Family)
    base_paths = tree_paths(root, base)
    head_paths = tree_paths(root, head)
    for path in base_paths:
        if path.endswith(".lean"):
            fam = families[module_family(path)]
            fam.base_files += 1
            fam.base_stems[shard_stem(path)] += 1
    for path in head_paths:
        if path.endswith(".lean"):
            fam = families[module_family(path)]
            fam.head_files += 1
            fam.head_stems[shard_stem(path)] += 1
    for added, removed, path in numstat(root, base, head):
        fam = families[module_family(path)]
        fam.added += added
        fam.removed += removed
        if path.endswith(".lean"):
            fam.lean_changed = True
            b_total, b_lit = literal_measure(blob(root, base, path))
            h_total, h_lit = literal_measure(blob(root, head, path))
            fam.base_chars += b_total
            fam.base_literal += b_lit
            fam.head_chars += h_total
            fam.head_literal += h_lit
    return families


def shard_groups(stems: Dict[str, int]) -> Dict[str, int]:
    return {stem: n for stem, n in stems.items() if n >= SHARD_GROUP_MIN}


def density(literal: int, total: int) -> float:
    return literal / total if total else 0.0


def render(families: Dict[str, Family], base: str, head_label: str) -> List[str]:
    out: List[str] = []
    changed = {name: f for name, f in families.items() if f.added or f.removed}
    lean_net = sum(f.added - f.removed for n, f in changed.items() if f.lean_changed)
    other_net = sum(f.added - f.removed for n, f in changed.items() if not f.lean_changed)
    out.append(f"growth ledger: {base[:12]}..{head_label}")
    out.append("")
    out.append("## Net lines per family (added / removed / net; Lean files base -> head)")
    for name, f in sorted(changed.items(), key=lambda kv: (-(kv[1].added - kv[1].removed), kv[0])):
        files = f"  files {f.base_files} -> {f.head_files}" if (f.base_files or f.head_files) else ""
        out.append(f"  {f.added - f.removed:+8d}  +{f.added:<7d} -{f.removed:<7d} {name}{files}")
    out.append(f"  totals: Lean families {lean_net:+d}, other {other_net:+d}, "
               f"all {lean_net + other_net:+d} over {len(changed)} famil(y/ies)")
    out.append("")
    out.append("## Shard families (Lean file count grew, or a shard group of "
               f">= {SHARD_GROUP_MIN} same-stem files at HEAD)")
    shard_rows = 0
    for name, f in sorted(families.items()):
        groups = shard_groups(f.head_stems)
        new_groups = {s: n for s, n in groups.items() if f.base_stems.get(s, 0) < n}
        if f.head_files > f.base_files or new_groups:
            shard_rows += 1
            detail = ", ".join(f"{s}x{n}" for s, n in sorted(new_groups.items())) or "-"
            out.append(f"  SHARD {name}: files {f.base_files} -> {f.head_files}; "
                       f"grown shard groups: {detail}")
    if not shard_rows:
        out.append("  (none)")
    out.append("")
    out.append("## Literal density of changed Lean families (numeric-literal share of "
               "non-whitespace characters)")
    literal_rows = 0
    flagged = 0
    for name, f in sorted(families.items()):
        if not f.lean_changed:
            continue
        literal_rows += 1
        b, h = density(f.base_literal, f.base_chars), density(f.head_literal, f.head_chars)
        grew = f.head_literal - f.base_literal
        mark = ""
        if h >= LITERAL_FLAG_DENSITY and grew > 0:
            mark = "LITERAL "
            flagged += 1
        out.append(f"  {mark}{name}: {b:6.1%} -> {h:6.1%}; literal chars {grew:+d}")
    if not literal_rows:
        out.append("  (no Lean change)")
    out.append("")
    out.append(
        f"OK — growth ledger (report-only): net {lean_net + other_net:+d} lines "
        f"({lean_net:+d} Lean), {shard_rows} shard famil(y/ies), "
        f"{flagged} literal-dense famil(y/ies) grew"
    )
    return out


def self_test() -> int:
    from module_family import self_test as family_self_test
    controls = family_self_test()
    with tempfile.TemporaryDirectory(prefix="growth-ledger-") as directory:
        root = pathlib.Path(directory)
        def run(*args: str) -> None:
            subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)
        run("init", "-q")
        run("config", "user.email", "fixture@example.invalid")
        run("config", "user.name", "fixture")
        (root / "Blanc" / "Fam").mkdir(parents=True)
        (root / "Blanc" / "Fam" / "Main.lean").write_text("theorem a : True := trivial\n" * 4)
        run("add", "-A")
        run("commit", "-q", "-m", "base")
        base = resolve(root, "HEAD")
        # Plant: four shards of literal-heavy text in the same family.
        for index in range(4):
            (root / "Blanc" / "Fam" / f"Rounds{index:02d}.lean").write_text(
                "def r := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a]\n" * 5)
        report = "\n".join(render(ledger(root, base, WORKTREE), base, "worktree"))
        for needle in ("SHARD Blanc/Fam/: files 1 -> 5", "Roundsx4", "LITERAL Blanc/Fam/",
                       "+20"):
            if needle not in report:
                raise GrowthError(f"self-test: planted growth not reported ({needle!r}):\n{report}")
        controls += 1
        # Remove the plant: the ledger must report nothing.
        for index in range(4):
            (root / "Blanc" / "Fam" / f"Rounds{index:02d}.lean").unlink()
        report = "\n".join(render(ledger(root, base, WORKTREE), base, "worktree"))
        if "SHARD" in report or "LITERAL" in report or "net +0 lines" not in report:
            raise GrowthError(f"self-test: clean tree reported growth:\n{report}")
        controls += 1
    print(f"OK — growth ledger self-test: {controls}/{controls} controls live")
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base", nargs="?")
    parser.add_argument("head", nargs="?", default="HEAD")
    parser.add_argument("--worktree", action="store_true",
                        help="compare BASE with the working tree (tracked and untracked files)")
    parser.add_argument("--root", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parent.parent)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    if not args.base:
        parser.error("BASE is required")
    root = args.root.resolve()
    base = resolve(root, args.base)
    if args.worktree:
        head, label = WORKTREE, "worktree"
    else:
        head = resolve(root, args.head)
        label = head[:12]
    print("\n".join(render(ledger(root, base, head), base, label)))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except GrowthError as error:
        print(f"REGRESSION — growth ledger: {error}")
        sys.exit(1)
