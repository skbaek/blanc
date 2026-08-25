#!/usr/bin/env python3
"""Measure what each gate actually reads, and diff it against its declaration.

WHY

`scripts/gate-registry.json` decides when a gate's verdict may be reused, and
every entry in it was derived by reading that gate's source.  That is the one
step in this design that is neither generated nor measured, and both
independent reviews named it as the likeliest place a remaining unsound skip
would hide -- not in the runner, which fails closed everywhere, but in a
declaration that missed a read.

Deriving is fallible here for a concrete reason: the checkers load helper
modules by path at run time, so a dependency can be real while appearing in no
wrapper, no import statement and no grep.  Two of them load each other.

This runs each gate once under an audit hook that records every file its whole
Python process tree opens, then asks the only question that matters: *did it
read something the registry does not fingerprint?*

BLIND SPOTS, STATED RATHER THAN IMPLIED

- Non-Python reads.  `grep` and `sed` in the shell wrappers are invisible here.
  They are few and named in the wrapper text.
- Everything `lake env lean` reads.  That channel is covered by Lake's own
  `depHash` rather than by a path list, which is the whole point of delegating
  it, so a `.olean` or `.trace` read is reported as `lake` and not as a hole.
- A read that only happens on a branch this run did not take.

A clean result therefore means "no undeclared read on the path this gate
actually took", which is a much stronger statement than "nobody spotted one",
and a weaker one than "there is none".

USE

    scripts/gate-read-audit.py                 # every cacheable gate
    scripts/gate-read-audit.py --only elab weth-fixtures

This is an instrument, not a gate.  It is not in the catalogue's ordered set,
it seeds no cache record, and it takes as long as a fresh full set because it
executes every gate body.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import importlib.util

_SPEC = importlib.util.spec_from_file_location(
    "gate_cache", Path(__file__).resolve().parent / "gate-cache.py"
)
assert _SPEC and _SPEC.loader
gc = importlib.util.module_from_spec(_SPEC)
sys.modules["gate_cache"] = gc
_SPEC.loader.exec_module(gc)

ROOT = gc.ROOT
HOOK_DIR = ROOT / "scripts/read-audit"
OUT_DIR = ROOT / ".lake/read-audit"

# Roots whose contents could plausibly change a verdict.  Anything outside them
# -- the Python installation, temporary directories -- is machinery, not input.
def interesting_roots() -> list[Path]:
    roots = [ROOT]
    for name in ("eels",):
        try:
            roots.append(gc.resolve_path(ROOT, f"@{name}"))
        except Exception:
            pass
    eest = Path(os.path.expanduser("~/eest-mainnet-v20.0.1"))
    if eest.is_dir():
        roots.append(eest)
    return roots


IGNORED_PARTS = ("__pycache__", "/.git/")
IGNORED_PREFIXES = (".lake/gate-", ".lake/read-audit", "scripts/report-elab.txt")


def classify(path: Path, roots: list[Path]) -> tuple[str, str] | None:
    """Return (root-label, repo-relative-ish name), or None if uninteresting."""

    try:
        resolved = path.resolve()
    except OSError:
        resolved = path
    for part in IGNORED_PARTS:
        if part in str(resolved):
            return None
    for root in roots:
        try:
            relative = resolved.relative_to(root.resolve())
        except ValueError:
            continue
        name = relative.as_posix()
        if root == ROOT and any(name.startswith(p) for p in IGNORED_PREFIXES):
            return None
        return ("repo" if root == ROOT else str(root), name)
    return None


def declared_coverage(gate: dict) -> tuple[set[Path], list[tuple[Path, str]]]:
    """Every path this gate's fingerprint would notice a change to.

    Returns exact paths plus (root, pattern-ish) subtrees that count as
    covered: a declared population's whole matched set, a pinned external
    checkout, and Lake's artifact tree.
    """

    inputs = gate.get("inputs", {})
    exact: set[Path] = set()
    subtrees: list[tuple[Path, str]] = []

    for given in inputs.get("files", []):
        try:
            exact.add(gc.resolve_path(ROOT, given).resolve())
        except Exception:
            pass

    for spec in inputs.get("populations", []):
        try:
            base = gc.resolve_path(ROOT, spec.get("root", ".")).resolve()
        except Exception:
            continue
        if spec.get("mode") == "traversable":
            # Contributes no digest, but the gate provably walks it, so a read
            # inside it is expected rather than undeclared.
            subtrees.append((base, "traversable"))
            continue
        try:
            for name in gc.glob_population(ROOT, spec):
                exact.add(gc.resolve_path(ROOT, name).resolve())
        except Exception:
            pass

    for given in inputs.get("lean_entries", []):
        path = (ROOT / given).resolve()
        exact.add(path)

    for spec in inputs.get("external", []):
        location = spec.get("path")
        env_name = spec.get("path_env")
        if isinstance(env_name, str) and os.environ.get(env_name):
            location = os.environ[env_name]
        if isinstance(location, str):
            directory = Path(os.path.expanduser(location))
            if not directory.is_absolute():
                directory = ROOT / directory
            subtrees.append((directory.resolve(), "external"))

    return exact, subtrees


LAKE_SUBTREES = (".lake/build", ".lake/packages")


def audit_gate(gate: dict, roots: list[Path]) -> dict:
    identifier = gate["id"]
    log = OUT_DIR / f"{identifier}.log"
    log.unlink(missing_ok=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    environment = dict(os.environ)
    environment["GATE_READ_AUDIT"] = str(log)
    existing = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = (
        f"{HOOK_DIR}{os.pathsep}{existing}" if existing else str(HOOK_DIR)
    )

    started = time.monotonic()
    result = subprocess.run(
        gate["command"], cwd=ROOT, env=environment,
        capture_output=True, text=True, check=False,
    )
    elapsed = time.monotonic() - started

    reads: set[str] = set()
    writes: set[str] = set()
    listings: set[str] = set()
    if log.is_file():
        for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
            kind, _, raw = line.partition("\t")
            if not raw:
                continue
            if kind == "R":
                reads.add(raw)
            elif kind == "W":
                writes.add(raw)
            elif kind == "L":
                listings.add(raw)
    # A gate's own scratch file is an output it happens to read back, not an
    # input: it did not exist before the run and cannot carry information from
    # one candidate to the next.
    reads -= writes
    # The audit hook fires on *attempted* opens, so a probe for a file that is
    # not there and an `open()` on a directory both arrive looking like reads.
    # Neither can carry content into a verdict.
    reads = {raw for raw in reads if Path(raw).is_file()}

    exact, subtrees = declared_coverage(gate)
    covered, lake, external, undeclared = 0, set(), set(), set()
    for raw in reads:
        seen = classify(Path(raw), roots)
        if seen is None:
            continue
        label, name = seen
        resolved = Path(raw).resolve()
        if resolved in exact:
            covered += 1
            continue
        if label == "repo" and any(name.startswith(p) for p in LAKE_SUBTREES):
            lake.add(name)
            continue
        if any(is_within(resolved, base) for base, _ in subtrees):
            external.add(name if label == "repo" else f"{label}/{name}")
            continue
        undeclared.add(name if label == "repo" else f"{label}::{name}")

    enumerated = set()
    for raw in listings:
        seen = classify(Path(raw), roots)
        if seen is None:
            continue
        label, name = seen
        resolved = Path(raw).resolve()
        if any(is_within(resolved, base) for base, _ in subtrees):
            continue
        if any(is_within(candidate, resolved) for candidate in exact):
            continue        # a directory holding declared files
        if label == "repo" and any(name.startswith(p) for p in LAKE_SUBTREES):
            continue
        enumerated.add(name if label == "repo" else f"{label}::{name}")

    return {
        "id": identifier,
        "command": " ".join(gate["command"]),
        "exit": result.returncode,
        "elapsed_s": round(elapsed, 1),
        "reads_observed": len(reads),
        "covered": covered,
        "lake_artifacts": sorted(lake),
        "in_declared_subtree": sorted(external),
        "undeclared": sorted(undeclared),
        "enumerated_undeclared": sorted(enumerated),
    }


def is_within(path: Path, base: Path) -> bool:
    try:
        path.relative_to(base)
        return True
    except ValueError:
        return False


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", nargs="*", help="audit just these gate ids")
    arguments = parser.parse_args(argv)

    registry = gc.load_registry(gc.registry_path(ROOT))
    gates = [g for g in registry["gates"] if g["kind"] == "cacheable"]
    if arguments.only:
        wanted = set(arguments.only)
        gates = [g for g in gates if g["id"] in wanted]

    roots = interesting_roots()
    results, failures, holes = [], [], []
    for gate in gates:
        outcome = audit_gate(gate, roots)
        results.append(outcome)
        flag = "    "
        if outcome["exit"] != 0:
            failures.append(outcome["id"])
            flag = "EXIT"
        if outcome["undeclared"]:
            holes.append(outcome["id"])
            flag = "HOLE"
        print(f"{flag} {outcome['id']:<26} {outcome['reads_observed']:>5} reads, "
              f"{outcome['covered']:>4} declared, {len(outcome['undeclared'])} undeclared "
              f"({outcome['elapsed_s']}s)")
        for name in outcome["undeclared"]:
            print(f"       UNDECLARED READ: {name}")
        for name in outcome["enumerated_undeclared"]:
            print(f"       enumerated directory, membership not declared: {name}")

    gc.atomic_json(OUT_DIR / "audit.json", {"gates": results})
    silent = [r["id"] for r in results if r["reads_observed"] == 0]
    print()
    print(f"gate read audit: {len(results)} gates executed, "
          f"{sum(r['reads_observed'] for r in results)} reads observed")
    if silent:
        print(f"  no Python reads observed (shell- or Lean-only): {', '.join(silent)}")
    if failures:
        print(f"  gates that did not exit 0: {', '.join(failures)}", file=sys.stderr)
    if holes:
        print(f"REGRESSION — gate read audit: {len(holes)} gate(s) read something "
              f"their registry entry does not fingerprint: {', '.join(holes)}",
              file=sys.stderr)
        return 1
    print("OK — gate read audit: every observed Python read is covered by its "
          "gate's declared inputs, the Lake artifact channel, or a declared "
          "external checkout")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
