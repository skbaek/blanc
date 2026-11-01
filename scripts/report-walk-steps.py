#!/usr/bin/env python3
"""Hand-listed walk steps and repeated `simp only` lists (safeguard S4, report-only).

Walks were written one instruction per line (`xr (rx_push rfl (by hr) ·)`, `xs 0x2234 ...`,
`obtain ... := ric_next run`) long after a step tactic could have read the instruction off the
goal: no check counted them, so 20k such lines accumulated. This report names them where they are
added, together with `simp only [...]` lists that are spelled out again and again instead of
being named once.

    python3 scripts/report-walk-steps.py BASE [HEAD]       # runs touching lines added since BASE
    python3 scripts/report-walk-steps.py BASE --worktree   # ... against the working tree
    python3 scripts/report-walk-steps.py --paths F.lean …  # whole files
    python3 scripts/report-walk-steps.py --all             # every tracked Blanc/**/*.lean
    python3 scripts/report-walk-steps.py --all --at REV    # ... as committed at REV (a census)
    python3 scripts/report-walk-steps.py --self-test

Two finding classes, both report-only:

* **hand-walk**: at least `--min-run` (default 8) consecutive single-instruction step lines at
  one indentation (deeper-indented continuation lines and comment lines do not break a run). The
  report counts how many of the run's lines a kit takes as they are: `Blanc/Lift/WalkKit.lean`'s
  `wrun` (the forward straight-line `xr` forms), Curve 3pool's backward `xa`
  (`Blanc/Lift/Curve3Pool/Walk/AutoStep.lean`), or `Blanc/Lift/WalkInvKit.lean`'s `winv`/`wskip`
  (the `ric_next` + `ri_<op>` inversion pairs, one- or two-line, `ric_dest`, and forgetful
  `obtain ⟨_, _, h⟩ := ric_next h`); the rest want a step tactic of their own family.
* **repeated-simp-list**: a `simp only [...]` lemma list of at least three entries that occurs at
  least `--min-repeat` (default 3) times in the scanned files: name it once (a macro or a
  `simp` set argument) instead.

With BASE, a run or a list is reported only when one of its lines was added since BASE. Exit 0
whenever the inputs resolve; the verdict line ends `(report-only)`.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from typing import Dict, List, Optional, Set, Tuple

STEP_RE = re.compile(
    r"^\s*(?:"
    r"(?:xr|xrc|xs|xs2|xm|xmo|xw|xjd|xjmp|xl|xsw|istep|xstep|wstep)\b"
    r"|(?:refine|exact|apply) rxc?e?_\w+"
    r"|obtain .*:= (?:ric_next|ric_nextP|ric_dest|ric_destP|rpw_next|rr_next|ri_\w+)\b"
    r"|(?:have|replace) \w+ := (?:ric_next|ric_nextP|xa_nextAt|xa_next)\b"
    r")")
_R = r"\(by (?:hr|hrs|wroom)\)"
_VAL = "mul|div|mod|lt|gt|slt|sgt|eq|iszero|and|or|xor|not|byte"
_ENV = "calldataload|callvalue|calldatasize|caller|gas|timestamp|number|codesize|returndatasize"
KIT_RE = re.compile(r"^\s*xr \((?:" + "|".join([
    rf"rx_push rfl {_R}", rf"rx_dup(?: \(n := \d+\))? rfl {_R}", r"rx_swap1",
    r"rx_swap(?: \(n := \d+\))? rfl", r"rx_pop", r"rx_dest", rf"rx_(?:add|sub) {_R}",
    rf"rx_(?:{_VAL}) rfl {_R}", rf"rx_(?:{_ENV}) {_R}"]) + r") ·\)\s*$")
_H = r"0x[0-9a-fA-F]+"
_BOPS = ("add|mul|sub|div|lt|gt|eq|iszero|and|or|xor|not|pop|address|caller|callvalue|"
         "calldataload|calldatasize|returndatasize|timestamp")
# Backward Curve 3pool steps that `xa` (Blanc/Lift/Curve3Pool/Walk/AutoStep.lean) takes as written.
XA_RE = re.compile(r"^\s*(?:" + "|".join([
    rf"xs {_H} \(\.push \[[^\]]*\] \(by decide\)\) ri_push",
    rf"xs {_H} \(\.reg \(\.(?:dup|swap) \d+\)\) \(ri_(?:dup|swap) \(by rfl\)\)",
    rf"xs {_H} \(\.reg \.(?P<op>{_BOPS})\) ri_(?P=op)", rf"xs {_H} \(\.reg \.gas\) ri_gas_remaining",
    rf"xs2 {_H} \(\.reg \.(?P<op2>slt|sgt)\) ri_(?P=op2)", rf"xjd {_H}"]) + r")\s*(?:--.*)?$")
_ID = r"[A-Za-z_][A-Za-z0-9_']*"
_IOPS = ("add|mul|sub|div|mod|exp|lt|gt|eq|iszero|and|or|xor|not|byte|shl|shr|address|caller|"
         "callvalue|calldataload|calldatasize|returndatasize|timestamp|pop|mload|mstore|mstore8|"
         "tload|keccak|log1|log2|log3|log4|push")
_INEXT = rf"obtain ⟨{_ID}, {_ID}, {_ID}⟩ := ric_nextP? {_ID}"
_ISEC = (rf"obtain ⟨{_ID}, rfl⟩ := (?:ri_(?:{_IOPS})|ri_(?:dup|swap) rfl) "
         rf"(?:{_ID}|\({_ID}(?:\.{_ID})* {_ID}\))")
# Inversion steps that `winv`/`wskip` (Blanc/Lift/WalkInvKit.lean) take as written.
INV_RE = re.compile(r"^\s*(?:" + "|".join([
    rf"{_INEXT}; {_ISEC}", _INEXT, _ISEC, rf"obtain ⟨{_ID}, {_ID}⟩ := ric_destP? {_ID}"])
    + r")\s*$")
SIMP_RE = re.compile(r"simp only \[([^\]]*)\]")
WORKTREE = None


class ReportError(RuntimeError):
    pass


def git(root: pathlib.Path, *args: str) -> str:
    r = subprocess.run(["git", *args], cwd=str(root), capture_output=True, text=True, check=False)
    if r.returncode != 0:
        raise ReportError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def walk_runs(lines: List[str], min_run: int) -> List[Tuple[int, int, int, int]]:
    """(first line, last line, step lines, kit-convertible lines), 1-based, per run."""
    runs, i = [], 0
    while i < len(lines):
        if not STEP_RE.match(lines[i]):
            i += 1
            continue
        ind, j, steps, kit, last = indent(lines[i]), i, 0, 0, i
        while j < len(lines):
            line = lines[j]
            if STEP_RE.match(line) and indent(line) == ind:
                steps += 1
                kit += bool(KIT_RE.match(line) or XA_RE.match(line) or INV_RE.match(line))
                last = j
            elif not (line.strip().startswith("--") or (line.strip() and indent(line) > ind)):
                break
            j += 1
        if steps >= min_run:
            runs.append((i + 1, last + 1, steps, kit))
        i = last + 1
    return runs


def simp_lists(lines: List[str]) -> List[Tuple[int, str]]:
    out = []
    for n, line in enumerate(lines, 1):
        for m in SIMP_RE.finditer(line):
            items = [x.strip() for x in m.group(1).split(",") if x.strip()]
            if len(items) >= 3:
                out.append((n, ", ".join(items)))
    return out


def added_lines(root: pathlib.Path, base: str, head: Optional[str], path: str) -> Set[int]:
    args = ["diff", "-U0", base] + ([head] if head else []) + ["--", path]
    got: Set[int] = set()
    for m in re.finditer(r"^@@ -\S+ \+(\d+)(?:,(\d+))? @@", git(root, *args), re.M):
        start, count = int(m.group(1)), int(m.group(2) or "1")
        got.update(range(start, start + count))
    return got


def read(root: pathlib.Path, head: Optional[str], path: str) -> List[str]:
    if head is WORKTREE:
        return (root / path).read_text(encoding="utf-8").split("\n")
    return git(root, "show", f"{head}:{path}").split("\n")



def report(root: pathlib.Path, files: Dict[str, Optional[Set[int]]], head: Optional[str],
           min_run: int, min_repeat: int, out=sys.stdout) -> Tuple[int, int]:
    nruns = nsteps = nkit = 0
    lists: Dict[str, List[Tuple[str, int, bool]]] = defaultdict(list)
    for path in sorted(files):
        lines = read(root, head, path)
        new = files[path]
        for a, b, steps, kit in walk_runs(lines, min_run):
            if new is not None and not any(a <= n <= b for n in new):
                continue
            nruns, nsteps, nkit = nruns + 1, nsteps + steps, nkit + kit
            print(f"hand-walk {path}:{a}-{b}: {steps} step lines, {kit} taken by `wrun`/`xa`/`winv`", file=out)
        for n, key in simp_lists(lines):
            lists[key].append((path, n, new is None or n in new))
    nsimp = 0
    for key, sites in sorted(lists.items(), key=lambda kv: -len(kv[1])):
        if len(sites) < min_repeat or not any(fresh for _, _, fresh in sites):
            continue
        nsimp += 1
        where = ", ".join(f"{p}:{n}" for p, n, _ in sites[:4]) + (" ..." if len(sites) > 4 else "")
        print(f"repeated-simp-list x{len(sites)} [{key}]: {where}", file=out)
    print(f"OK — walk-step report: {nruns} hand-walk runs ({nsteps} step lines, {nkit} taken by "
          f"`wrun`/`xa`/`winv`), {nsimp} repeated simp lists (report-only)", file=out)
    return nruns, nsimp


def changed(root: pathlib.Path, base: str, head: Optional[str]) -> Dict[str, Optional[Set[int]]]:
    args = ["diff", "--name-only", "--diff-filter=AM", base] + ([head] if head else [])
    files: Dict[str, Optional[Set[int]]] = {
        p: added_lines(root, base, head, p)
        for p in git(root, *args).split("\n") if p.endswith(".lean")}
    if head is WORKTREE:  # an untracked file is added whole
        for p in git(root, "ls-files", "--others", "--exclude-standard").split("\n"):
            if p.endswith(".lean"):
                files[p] = None
    return files


def self_test() -> int:
    walk = "\n".join(["theorem t : True := by"] + ["  xr (rx_push rfl (by hr) ·)"] * 6 +
                     ["  -- tree t_1", "  xr (rx_mul rfl (by hr) ·)",
                      "  xs 0x22 (.reg .pop) ri_pop", "  trivial"]) + "\n"
    simp = "".join(f"theorem s{i} : True := by simp only [a, b, c]\n" for i in range(3))
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp)
        git(root, "init", "-q")
        git(root, "config", "user.email", "t@t"); git(root, "config", "user.name", "t")
        (root / "A.lean").write_text("theorem a : True := trivial\n")
        git(root, "add", "."); git(root, "commit", "-qm", "base")
        base = git(root, "rev-parse", "HEAD").strip()
        sink = open("/dev/null", "w")
        checks = []
        # clean change: nothing reported
        (root / "A.lean").write_text("theorem a : True := trivial\ntheorem b : True := trivial\n")
        checks.append(("clean", report(root, changed(root, base, WORKTREE), WORKTREE, 8, 3, sink) == (0, 0)))
        # planted walk run and repeated list: both reported
        (root / "B.lean").write_text(walk + simp)
        checks.append(("planted", report(root, changed(root, base, WORKTREE), WORKTREE, 8, 3, sink) == (1, 1)))
        # threshold: a run of 8 is below a minimum of 9
        checks.append(("threshold", report(root, changed(root, base, WORKTREE), WORKTREE, 9, 4, sink) == (0, 0)))
        # base mode: committed plant is reported; an untouched old run is not
        git(root, "add", "."); git(root, "commit", "-qm", "plant")
        checks.append(("base", report(root, changed(root, base, "HEAD"), "HEAD", 8, 3, sink) == (1, 1)))
        head = git(root, "rev-parse", "HEAD").strip()
        (root / "B.lean").write_text(walk + simp + "theorem z : True := trivial\n")
        checks.append(("untouched", report(root, changed(root, head, WORKTREE), WORKTREE, 8, 3, sink) == (0, 0)))
    inv = (["  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd"] * 3 +
           ["  obtain ⟨d, hd, h⟩ := ric_nextP h", "  obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)",
            "  obtain ⟨_, h⟩ := ric_dest h", "  obtain ⟨_, _, h⟩ := ric_next h",
            "  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd"])
    checks.append(("inversion", walk_runs(inv, 8) == [(1, 8, 8, 7)]))
    for name, ok in checks:
        print(f"{'PASS' if ok else 'FAIL'} {name}")
    ok = all(c for _, c in checks)
    print(f"{'OK' if ok else 'FAIL'} — report-walk-steps self-test: {sum(c for _, c in checks)}/{len(checks)}")
    return 0 if ok else 1


def main(argv: List[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("revs", nargs="*")
    ap.add_argument("--worktree", action="store_true")
    ap.add_argument("--paths", nargs="+")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--min-run", type=int, default=8)
    ap.add_argument("--min-repeat", type=int, default=3)
    ap.add_argument("--at")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args(argv)
    if a.self_test:
        return self_test()
    root = pathlib.Path(git(pathlib.Path.cwd(), "rev-parse", "--show-toplevel").strip())
    try:
        if a.paths or a.all:
            at = a.at if a.at else WORKTREE
            listed = git(root, "ls-tree", "-r", "--name-only", a.at, "Blanc") if a.at else \
                git(root, "ls-files", "Blanc")
            paths = a.paths or [p for p in listed.split("\n") if p.endswith(".lean")]
            report(root, {p: None for p in paths}, at, a.min_run, a.min_repeat)
        elif len(a.revs) in (1, 2):
            head = WORKTREE if a.worktree else (a.revs[1] if len(a.revs) == 2 else "HEAD")
            report(root, changed(root, a.revs[0], head), head, a.min_run, a.min_repeat)
        else:
            ap.error("give BASE [HEAD], --paths, --all or --self-test")
    except ReportError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
