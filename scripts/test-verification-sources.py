#!/usr/bin/env python3
"""Focused controls for scripts/verification_sources.py (synthetic trees only).

All fixtures live under one TemporaryDirectory that is removed on exit; no
host cleanup outside it.
"""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verification_sources import VerificationSourcesError, discover

PASS = 0
_SEQ = 0


def check(name: str, cond: bool) -> None:
    global PASS
    if not cond:
        raise AssertionError(f"FAIL: {name}")
    PASS += 1
    print(f"ok: {name}")


def expect_fail(name: str, root: Path, needle: str | None = None) -> None:
    try:
        discover(root)
    except VerificationSourcesError as error:
        check(name, needle is None or needle in str(error))
    else:
        check(name, False)


def make_tree(home: Path, extra_registry_gates=None, bad_registry=None) -> Path:
    global _SEQ
    _SEQ += 1
    tmp = home / f"tree-{_SEQ}"
    (tmp / "scripts" / "nested" / "deep").mkdir(parents=True)
    (tmp / "scripts" / "fixtures" / "demo").mkdir(parents=True)
    (tmp / "scripts" / "nested" / "deep" / "N.lean").write_bytes(b"def n := 1\n")
    (tmp / "scripts" / "Top.lean").write_bytes(b"-- top\n")
    (tmp / "scripts" / "T.lean.in").write_bytes(b"template {{x}}\n")
    (tmp / "scripts" / "fixtures" / "demo" / "F.lean").write_bytes(b"fixture\n")
    (tmp / "scripts" / "fixtures" / "demo" / "F.lean.bak").write_bytes(b"backup\n")
    (tmp / "scripts" / "Top.lean.bak").write_bytes(b"backup\n")
    (tmp / "scripts" / "T.lean.in.bak").write_bytes(b"backup\n")
    (tmp / "Root.lean").write_bytes(b"root\n")
    (tmp / "Main.lean").write_bytes(b"main\n")
    (tmp / "lakefile.lean").write_bytes(b"lake\n")
    (tmp / "Blanc.lean").write_bytes(b"library root: must stay out\n")
    (tmp / "Blanc").mkdir(exist_ok=True)
    (tmp / "Blanc" / "Lib.lean").write_bytes(b"library: must stay out\n")
    (tmp / ".lake" / "build").mkdir(parents=True)
    (tmp / ".lake" / "build" / "Skip.lean").write_bytes(b"lake output\n")
    (tmp / ".git" / "objects").mkdir(parents=True)
    (tmp / ".git" / "objects" / "Skip.lean").write_bytes(b"git object\n")
    (tmp / ".worktrees" / "w").mkdir(parents=True)
    (tmp / ".worktrees" / "w" / "Skip.lean").write_bytes(b"worktree\n")
    gates = [
        {"id": "g1", "inputs": {"files": ["scripts/Top.lean", "scripts/Top.lean"]}},
        {"id": "g2", "inputs": {"files": ["scripts/Top.lean", "Root.lean"]}},
        {"id": "g3", "inputs": {"files": ["README.md", "/bin/bash"]}},
    ]
    if extra_registry_gates:
        gates.extend(extra_registry_gates)
    if bad_registry is not None:
        (tmp / "scripts" / "gate-registry.json").write_bytes(bad_registry)
    else:
        (tmp / "scripts" / "gate-registry.json").write_text(json.dumps({"gates": gates}))
    return tmp


def by_path(records):
    return {r["path"]: r for r in records}


def run(home: Path) -> None:
    root = make_tree(home)
    recs = discover(root)
    m = by_path(recs)
    check("nested lean discovered as source", m["scripts/nested/deep/N.lean"]["role"] == "source")
    check("template role for .lean.in", m["scripts/T.lean.in"]["role"] == "template")
    check("fixture distinct role", m["scripts/fixtures/demo/F.lean"]["role"] == "fixture")
    check("root lean discovered", m["Root.lean"]["role"] == "source")
    check("Main.lean kept as source", m["Main.lean"]["role"] == "source")
    check("lakefile.lean kept as source", m["lakefile.lean"]["role"] == "source")
    check("Blanc.lean library root excluded", "Blanc.lean" not in m)
    check("nearby extensions not inventoried",
          "scripts/Top.lean.bak" not in m
          and "scripts/T.lean.in.bak" not in m
          and "scripts/fixtures/demo/F.lean.bak" not in m)
    check("omitted registry membership is empty", m["scripts/nested/deep/N.lean"]["declared_gate_inputs"] == [])
    check("duplicate registry membership deduped+sorted",
          m["scripts/Top.lean"]["declared_gate_inputs"] == ["g1", "g2"])
    check("root file gate membership", m["Root.lean"]["declared_gate_inputs"] == ["g2"])
    check("no Blanc library leakage", "Blanc/Lib.lean" not in m)
    check("no .lake/.git/.worktrees leakage",
          not any(p.startswith(d) for p in m for d in (".lake/", ".git/", ".worktrees/")))
    check("deterministic sorted order", [r["path"] for r in recs] == sorted(m))
    check("repeat run identical", discover(root) == recs)
    expected = hashlib.sha256(b"-- top\n").hexdigest()
    check("sha256 tracks exact bytes", m["scripts/Top.lean"]["sha256"] == expected)
    (root / "scripts" / "Top.lean").write_bytes(b"-- changed\n")
    check("hash changes with file bytes",
          by_path(discover(root))["scripts/Top.lean"]["sha256"] != expected)

    root_nofiles = make_tree(home, extra_registry_gates=[{"id": "nofiles", "inputs": {}}])
    check("gate without inputs.files declares nothing",
          by_path(discover(root_nofiles))["scripts/Top.lean"]["declared_gate_inputs"] == ["g1", "g2"])
    for label, blob in [
        ("malformed registry fail-closed", b"{not json"),
        ("missing gates fail-closed", json.dumps({"gates": "x"}).encode()),
        ("bad gate shape fail-closed", json.dumps({"gates": [{"id": 1}]}).encode()),
        ("non-list files fail-closed",
         json.dumps({"gates": [{"id": "g", "inputs": {"files": "x"}}]}).encode()),
    ]:
        expect_fail(label, make_tree(home, bad_registry=blob))

    for label, files in [
        ("traversal registry entry rejected", ["../outside.lean"]),
        ("absolute registry entry rejected", ["/etc/other.lean"]),
    ]:
        expect_fail(label, make_tree(
            home, extra_registry_gates=[{"id": "evil", "inputs": {"files": files}}]))

    outside = home / "outside"
    outside.mkdir()
    (outside / "Outside.lean").write_bytes(b"external: never read\n")

    evil_src = make_tree(home)
    (evil_src / "scripts" / "Evil.lean").symlink_to(outside / "Outside.lean")
    expect_fail("escaping source symlink fails naming path", evil_src, "scripts/Evil.lean")

    evil_reg = make_tree(home, extra_registry_gates=[
        {"id": "ext", "inputs": {"files": ["scripts/Ext.lean"]}}])
    (evil_reg / "scripts" / "Ext.lean").symlink_to(outside / "Outside.lean")
    expect_fail("registry Lean entry via external symlink rejected", evil_reg)

    evil_dir = make_tree(home)
    (evil_dir / "scripts" / "linkdir").symlink_to(outside, target_is_directory=True)
    expect_fail("symlink source directory unsupported", evil_dir, "linkdir")

    ext_scripts = home / "ext-scripts"
    ext_scripts.mkdir()
    (ext_scripts / "gate-registry.json").write_text(json.dumps({"gates": []}))
    (ext_scripts / "X.lean").write_bytes(b"external: never read\n")
    linked_root = home / "linked-root"
    linked_root.mkdir()
    (linked_root / "scripts").symlink_to(ext_scripts, target_is_directory=True)
    expect_fail("external scripts/ root rejected before enumeration", linked_root, "scripts")

    swapped_reg = make_tree(home)
    out_json = home / "outside-reg.json"
    out_json.write_text(json.dumps({"gates": []}))
    (swapped_reg / "scripts" / "gate-registry.json").unlink()
    (swapped_reg / "scripts" / "gate-registry.json").symlink_to(out_json)
    expect_fail("external registry symlink refused before reading",
                swapped_reg, "gate-registry.json")

    dangling = make_tree(home)
    (dangling / "Ghost.lean").symlink_to(dangling / "Nope.lean")
    expect_fail("dangling root symlink fails naming path", dangling, "Ghost.lean")

    lean_dir = make_tree(home)
    (lean_dir / "Dir.lean").mkdir()
    expect_fail("root directory named .lean fails as unreadable", lean_dir, "Dir.lean")

    cyc = make_tree(home, extra_registry_gates=[
        {"id": "c", "inputs": {"files": ["scripts/Loop.lean"]}}])
    (cyc / "scripts" / "Loop.lean").symlink_to(cyc / "scripts" / "Loop2.lean")
    (cyc / "scripts" / "Loop2.lean").symlink_to(cyc / "scripts" / "Loop.lean")
    expect_fail("registry symlink cycle yields named error", cyc, "scripts/Loop.lean")

    empty = home / "empty"
    (empty / "scripts").mkdir(parents=True)
    (empty / "scripts" / "gate-registry.json").write_text(json.dumps({"gates": []}))
    expect_fail("missing source population refuses all-clean", empty)


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="verif-src-") as home:
        run(Path(home))
    print(f"PASS: {PASS} controls")
    return 0


if __name__ == "__main__":
    sys.exit(main())
