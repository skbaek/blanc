#!/usr/bin/env python3
"""Print, from scripts/gate-registry.json, what a Jaune pin move must re-run.

A Jaune pin move (``lakefile.lean`` + ``lake-manifest.json``) is the one
change that can invalidate a Lean-free gate without touching any file that
gate is "about". The joint catalogue of 2026-10-31 went red on
``check-transient-settlement.sh --static-only`` because a hand-picked pin-move
gate selection left that row out while its owner manifest still recorded the
old pin files' digests. This report is derived mechanically from the registry
so the selection cannot be hand-picked again:

* **Lean-free rows.** Every catalogue row whose registered tools name neither
  ``lean`` nor ``lake`` and which is not ``lake build`` itself. A pin move runs
  all of them (``scripts/GATES.md``, the pinned-Jaune-revision row), never a
  subset; ``scripts/check-gates.sh`` does that automatically because both pin
  files are fingerprint inputs of the rows that read them.
* **Pin-file readers.** Every row that declares ``lakefile.lean`` or
  ``lake-manifest.json`` as an input, each with the registered writer (or the
  reviewed edit) that refreshes what it records about the pin. A writer run is
  an ordinary regeneration, not a baseline change.
* **Pinned-package readers.** Every row that reads a path under
  ``.lake/packages/jaune`` (the pinned checkout or its built ``jaune``
  runner); a pin move needs that checkout materialized at the new pin and the
  ``jaune/jaune`` target rebuilt through the owned build before these run.

``PIN_WRITERS`` below is the only hand-maintained part, and it is checked in
both directions against the registry on every run: a row that starts reading a
pin file without a writer entry, or an entry whose row no longer reads one,
fails (exit 1). ``--self-test`` shows both directions bite on a disposable
registry copy.

Usage: scripts/report-pin-readers.py [--root DIR] [--self-test]
"""

from __future__ import annotations

import argparse
import copy
import json
import pathlib
import sys
import tempfile
from typing import Dict, List, Sequence, Tuple

PIN_FILES = ("lakefile.lean", "lake-manifest.json")
PACKAGE_PREFIX = ".lake/packages/jaune"
REGISTRY_REL = pathlib.Path("scripts/gate-registry.json")

# Registry id -> what refreshes that row's record of the pin after a move.
# "none: ..." means the row records nothing about the pin and simply
# re-executes against it; that is still a deliberate, reviewed statement.
PIN_WRITERS: Dict[str, str] = {
    "deployed-claim-map": (
        "reviewed edit: the `Jaune revision` row of docs/DEPLOYED_BYTECODE_CLAIM_MAP.md "
        "(the gate checks it against both pin files)"
    ),
    "proof-recipes": (
        "reviewed constant: re-verify JAUNE_DISPATCH_SURFACE and update JAUNE_DISPATCH_PIN "
        "in scripts/generate-proof-recipes.py, then "
        "`python3 scripts/generate-proof-recipes.py --write`"
    ),
    "transient-settlement-static": (
        "`python3 scripts/check-transient-settlement.py --write-manifest` "
        "(jaunePinFiles digests in scripts/transient-settlement-owner-manifest.json)"
    ),
    "transient-settlement-self-test": (
        "same writer as transient-settlement-static "
        "(`python3 scripts/check-transient-settlement.py --write-manifest`)"
    ),
    "claim-hash": (
        "`scripts/check-claim-hash.sh --generate scripts/claim-pin-hash` "
        "(header.json records the dependency pins; adoption is a reviewed act)"
    ),
    "elab": "none: re-measures; the pin files are cache keys of its own selector",
}


class ReportError(RuntimeError):
    pass


def load_gates(path: pathlib.Path) -> List[dict]:
    try:
        registry = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReportError(f"cannot read {path}: {error}") from error
    gates = registry.get("gates") if isinstance(registry, dict) else None
    if not isinstance(gates, list) or not gates:
        raise ReportError(f"{path}: no gates list")
    return gates


def command_text(gate: dict) -> str:
    return " ".join(gate["command"])


def is_lean_free(gate: dict) -> bool:
    if gate["command"] == ["lake", "build"]:
        return False
    tools = gate.get("inputs", {}).get("tools", [])
    return not any(tool == "lean" or tool.startswith("lake") for tool in tools)


def declared_paths(gate: dict) -> List[str]:
    inputs = gate.get("inputs", {})
    paths = [p for p in inputs.get("files", []) if isinstance(p, str)]
    for population in inputs.get("populations", []):
        if isinstance(population, dict) and isinstance(population.get("root"), str):
            paths.append(population["root"])
    return paths


def classify(gates: Sequence[dict]) -> Tuple[List[dict], List[dict], List[dict]]:
    lean_free = [gate for gate in gates if is_lean_free(gate)]
    pin_readers = [
        gate for gate in gates if any(path in PIN_FILES for path in declared_paths(gate))
    ]
    package_readers = [
        gate for gate in gates
        if any(path.startswith(PACKAGE_PREFIX) for path in declared_paths(gate))
    ]
    return lean_free, pin_readers, package_readers


def writer_drift(pin_readers: Sequence[dict], writers: Dict[str, str]) -> List[str]:
    problems = []
    reading = {gate["id"] for gate in pin_readers}
    for gate in pin_readers:
        if gate["id"] not in writers:
            problems.append(
                f"row {gate['order']} `{command_text(gate)}` (id {gate['id']}) reads a pin "
                f"file but PIN_WRITERS names no writer for it"
            )
    for identifier in sorted(set(writers) - reading):
        problems.append(
            f"PIN_WRITERS names {identifier}, which no registry row with that id "
            f"declares as a pin-file reader; the table is stale"
        )
    return problems


def report(gates: Sequence[dict], writers: Dict[str, str]) -> int:
    lean_free, pin_readers, package_readers = classify(gates)
    problems = writer_drift(pin_readers, writers)
    print(f"Lean-free catalogue rows a pin move runs in full ({len(lean_free)}):")
    for gate in lean_free:
        print(f"  {gate['order']:>3} {command_text(gate)}")
    print(f"Pin-file readers and their writers ({len(pin_readers)}):")
    for gate in pin_readers:
        writer = writers.get(gate["id"], "MISSING")
        print(f"  {gate['order']:>3} {command_text(gate)} [{gate['id']}]")
        print(f"      writer: {writer}")
    print(f"Pinned-package readers ({len(package_readers)}; need {PACKAGE_PREFIX} at the "
          f"new pin and jaune/jaune rebuilt through the owned build):")
    for gate in package_readers:
        print(f"  {gate['order']:>3} {command_text(gate)}")
    for problem in problems:
        print(f"  DRIFT: {problem}", file=sys.stderr)
    if problems:
        print(f"REGRESSION — pin readers: {len(problems)} writer-table drift(s)")
        return 1
    print(
        f"OK — pin readers: {len(lean_free)} Lean-free row(s), {len(pin_readers)} "
        f"pin-file reader(s) each with a named writer, {len(package_readers)} "
        f"pinned-package reader(s) (report-only)"
    )
    return 0


def self_test(root: pathlib.Path) -> int:
    gates = load_gates(root / REGISTRY_REL)
    _lean_free, pin_readers, _package = classify(gates)
    if writer_drift(pin_readers, PIN_WRITERS):
        raise ReportError("self-test precondition: the committed registry already drifts")
    controls = 0
    with tempfile.TemporaryDirectory(prefix="pin-readers-") as directory:
        # Control 1: a Lean-free row that newly reads lake-manifest.json with no
        # writer entry must fail.
        planted = copy.deepcopy(gates)
        target = next(g for g in planted if is_lean_free(g) and g not in pin_readers
                      and "lake-manifest.json" not in declared_paths(g))
        target.setdefault("inputs", {}).setdefault("files", []).append("lake-manifest.json")
        path = pathlib.Path(directory) / "registry.json"
        path.write_text(json.dumps({"gates": planted}), encoding="utf-8")
        _, readers, _ = classify(load_gates(path))
        if not any(target["id"] in problem for problem in writer_drift(readers, PIN_WRITERS)):
            raise ReportError("self-test: an unwritten pin-file reader was not reported")
        controls += 1
        # Control 2: a writer entry whose row no longer reads a pin file must fail.
        stale = dict(PIN_WRITERS)
        stale["no-such-gate"] = "fixture writer"
        if not any("no-such-gate" in p for p in writer_drift(pin_readers, stale)):
            raise ReportError("self-test: a stale writer entry was not reported")
        controls += 1
        # Control 3: the Lean classifier keeps the build row and a lean-tool row out.
        if any(g["command"] == ["lake", "build"] for g in _lean_free):
            raise ReportError("self-test: lake build classified Lean-free")
        lean_row = copy.deepcopy(target)
        lean_row["inputs"]["tools"] = ["python3", "lean"]
        if is_lean_free(lean_row):
            raise ReportError("self-test: a lean-tool row classified Lean-free")
        controls += 1
    print(f"OK — pin readers self-test: {controls}/{controls} controls live")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parent.parent)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if args.self_test:
        return self_test(root)
    return report(load_gates(root / REGISTRY_REL), PIN_WRITERS)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except ReportError as error:
        print(f"REGRESSION — pin readers: {error}")
        sys.exit(1)
