#!/usr/bin/env python3
"""Generate `Blanc.lean`, the library root, from the live set.

The root imports every module that `scripts/check-layering.py` classifies
(shared, a live contract family, or a composition) and that is on disk, in
sorted order, except the modules in ROOT_EXCLUDED. It imports every such
module, not only the maximal ones, so removing a family never leaves the root
importing a missing module or missing a module that only the removed family
reached. Nothing in the output is typed by hand.

No Blanc module imports the root, so its import order changes no statement.
Only importers of `Blanc` (the scripts/*.lean drivers) see the root's order.

Usage:
  python3 scripts/generate-root.py --write [--root DIR]
  python3 scripts/generate-root.py --check [--root DIR]

`--check` byte-compares the committed root with a fresh rendering and exits 1
on any difference. `scripts/check-layering.sh` runs the same check, so the
layering gate fails when the root is stale.
"""

from __future__ import annotations

import importlib.util
import os
import sys

ROOT_FILE = "Blanc.lean"

# Modules kept off the root, each with its reason. They must exist and be
# classified SHARED.
ROOT_EXCLUDED = {
    "ProofRecipeTactic": "imported by scripts/AxiomCheck.lean directly; kept off the root so no proof depends on the recipe tactic",
    "ProofRecipesGenerated": "imported by scripts/AxiomCheck.lean directly; generated recipe controls, kept off the root",
}


def load_layering():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-layering.py")
    spec = importlib.util.spec_from_file_location("layering_for_root", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"REGRESSION — root: cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def render(root, layering, owner=None):
    """-> (text, failures). The text is the root this tree should have."""
    if owner is None:
        owner = layering.classify()
    found = layering.modules_on_disk(root)
    failures = []
    for mod, reason in sorted(ROOT_EXCLUDED.items()):
        if mod not in found:
            failures.append(f"ROOT_EXCLUDED names {mod}, which is not on disk")
        elif owner.get(mod) != "shared":
            failures.append(f"ROOT_EXCLUDED names {mod}, which is not classified SHARED")
        if not reason.strip():
            failures.append(f"ROOT_EXCLUDED entry {mod} has no reason")
    imported = sorted(
        mod for mod in found
        if owner.get(mod) not in (None, "root") and mod not in ROOT_EXCLUDED
    )
    text = "".join(f"import Blanc.{mod}\n" for mod in imported)
    return text, failures


def check(root, layering, owner=None):
    """-> failures, for the layering gate."""
    text, failures = render(root, layering, owner)
    path = os.path.join(root, ROOT_FILE)
    try:
        with open(path, encoding="utf-8") as handle:
            committed = handle.read()
    except OSError as exc:
        return failures + [f"cannot read {ROOT_FILE}: {exc}"]
    if committed != text:
        have = set(committed.splitlines())
        want = set(text.splitlines())
        extra = sorted(have - want)[:3]
        missing = sorted(want - have)[:3]
        detail = []
        if missing:
            detail.append("missing " + ", ".join(missing))
        if extra:
            detail.append("unexpected " + ", ".join(extra))
        if not detail:
            detail.append("order or spacing differs")
        failures.append(
            f"{ROOT_FILE} differs from its generator ({'; '.join(detail)}): "
            f"regenerate with `python3 scripts/generate-root.py --write`"
        )
    return failures


def main(argv):
    mode = None
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    args = list(argv[1:])
    while args:
        arg = args.pop(0)
        if arg in ("--write", "--check"):
            mode = arg
        elif arg == "--root" and args:
            root = args.pop(0)
        else:
            raise SystemExit(f"usage: {argv[0]} --write|--check [--root DIR]")
    if mode is None:
        raise SystemExit(f"usage: {argv[0]} --write|--check [--root DIR]")
    layering = load_layering()
    if mode == "--check":
        failures = check(root, layering)
        for line in failures:
            print(f"ROOT — {line}")
        if failures:
            print(f"REGRESSION — root: {len(failures)} failure(s)")
            return 1
        print(f"OK — root: {ROOT_FILE} matches its generator")
        return 0
    text, failures = render(root, layering)
    if failures:
        for line in failures:
            print(f"ROOT — {line}")
        print("REGRESSION — root: not written")
        return 1
    with open(os.path.join(root, ROOT_FILE), "w", encoding="utf-8") as handle:
        handle.write(text)
    print(f"wrote {ROOT_FILE}: {text.count(chr(10))} import(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
