#!/usr/bin/env python3
"""Closure hash for the ClaimCheck pins.

`scripts/ClaimCheck.lean` pins each public claim by definitional equality
against the *current* definitions of every constant the claim mentions, so a
change to a definition below the pinned layer leaves every pin green while the
meaning of the claim moves.  This gate content-hashes each pinned statement
down to a fixed boundary and compares the result with a committed manifest.

Pipeline (one run for all pins):

1. ``scripts/ClaimPinHash.lean`` (run with ``lake env lean --run``) elaborates
   ClaimCheck with every pin kept, walks the definitional closure of all pinned
   statements once with a visited set, and writes one record per reached
   constant: a canonical serialization (binder names, binder info and ``mdata``
   erased, universe parameters by position, subterms hash-consed) plus the
   ordered constants that serialization refers to.
2. This script computes a Merkle SHA-256 table bottom-up with its own in-run
   memo: a constant's digest is the SHA-256 of its kind, its serialization and
   the digests of the constants it refers to, so a referenced constant
   contributes its digest, never its name.  Boundary constants (defined outside
   ``Blanc``) contribute their name and the identity of the pinned dependency
   that owns them: ``lean-toolchain`` for Lean core and Std, the
   ``lake-manifest.json`` rev for every Lake package (Mathlib, Batteries,
   Jaune, ...).

Why the split: Lean ships no SHA-256, and a hand-written one would run in the
interpreter over ~10 MB of serialization; Python's ``hashlib`` is the reviewed
primitive.  Lean keeps the part that needs the elaborated environment (the
closure walk and the canonical serialization); Python keeps the digests and
the comparison.  Nothing persists between runs: both memo tables live for one
run only, so a stale cache cannot make a changed definition look unchanged.

A hash detects change, not weakening.  On a mismatch the gate names the
constants whose own content moved, the other constants that moved because of
them, and the pins whose roots they reach, and fails; the readable ``example``
pins in ClaimCheck stay the reviewed statement.

Modes:
  (default)          regenerate into a temporary directory and compare with
                     the committed manifest in scripts/claim-pin-hash/
  --generate DIR     regenerate and write the manifest files into DIR
  --records FILE     use an existing driver output instead of running Lean
  --self-test        in-memory controls of the Merkle and comparison logic
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import tempfile
import time
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_DIR = ROOT / "scripts" / "claim-pin-hash"
DRIVER = "scripts/ClaimPinHash.lean"
CLAIMCHECK = "scripts/ClaimCheck.lean"
SCHEMA = 1
DOMAIN = b"blanc-claim-pin-hash/v1\0"
PIN_REGEX = re.compile(r"^[ \t\r\v\f]*example([ \t\r\v\f]|$)")


class GateError(Exception):
    pass


# ---------------------------------------------------------------- inputs


def dependency_identities(root: Path) -> dict[str, str]:
    """`@toolchain` -> lean-toolchain; each Lake package -> name@rev."""
    toolchain = (root / "lean-toolchain").read_text().strip()
    manifest = json.loads((root / "lake-manifest.json").read_text())
    ids = {"@toolchain": toolchain}
    for package in manifest["packages"]:
        rev = package.get("rev")
        if not rev:
            raise GateError(f"lake-manifest.json package without a rev: {package.get('name')}")
        ids[package["name"]] = f"{package['name']}@{rev}"
    return ids


def expected_pin_count(root: Path) -> int:
    """The count `scripts/check-claims.sh` hardcodes; the two must agree."""
    text = (root / "scripts" / "check-claims.sh").read_text()
    match = re.search(r'"\$claim_count" -ne ([0-9]+)', text)
    if not match:
        raise GateError("cannot find the pin count in scripts/check-claims.sh")
    return int(match.group(1))


def regex_pin_count(root: Path) -> int:
    lines = (root / CLAIMCHECK).read_text().split("\n")
    return sum(1 for line in lines if PIN_REGEX.match(line))


def run_driver(root: Path, out: Path, log: Path) -> float:
    start = time.monotonic()
    with log.open("wb") as handle:
        status = subprocess.run(
            ["lake", "env", "lean", "--run", DRIVER, CLAIMCHECK, str(out)],
            cwd=root, stdout=handle, stderr=subprocess.STDOUT).returncode
    if status != 0:
        tail = log.read_text(errors="replace").splitlines()[-40:]
        raise GateError("closure driver failed (exit %d); log tail:\n%s" % (status, "\n".join(tail)))
    return time.monotonic() - start


def child_peak_rss_kib() -> int:
    return resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss


def load_records(path: Path) -> tuple[dict[str, dict], list[dict], dict]:
    records: dict[str, dict] = {}
    pins: list[dict] = []
    stats: dict = {}
    with path.open() as handle:
        for line in handle:
            row = json.loads(line)
            if row.get("k") == "stats":
                stats = row
                continue
            name = row["n"]
            if name in records:
                raise GateError(f"duplicate record {name}")
            records[name] = row
            if row["k"] == "pin":
                pins.append(row)
    if not stats:
        raise GateError("driver output has no stats line (truncated run?)")
    return records, pins, stats


# ---------------------------------------------------------------- Merkle


def sha(*parts: bytes) -> str:
    h = hashlib.sha256(DOMAIN)
    for part in parts:
        h.update(len(part).to_bytes(8, "big"))
        h.update(part)
    return h.hexdigest()


def merkle(records: dict[str, dict], deps: dict[str, str]) -> tuple[dict[str, str], dict]:
    """Digest every record bottom-up, memoized; fail closed on a cycle."""
    digest: dict[str, str] = {}
    stats = {"digests_computed": 0, "memo_hits": 0}
    for start in records:
        if start in digest:
            continue
        # iterative post-order: (name, state) with state 0 = enter, 1 = exit
        stack = [(start, 0)]
        on_path: set[str] = set()
        while stack:
            name, state = stack.pop()
            if state == 0:
                if name in digest:
                    continue
                if name in on_path:
                    raise GateError(f"reference cycle through {name}")
                rec = records.get(name)
                if rec is None:
                    raise GateError(f"reference to a constant with no record: {name}")
                on_path.add(name)
                stack.append((name, 1))
                for ref in reversed(rec["r"]):
                    if ref in digest:
                        continue
                    if ref in on_path:
                        raise GateError(f"reference cycle through {ref}")
                    stack.append((ref, 0))
            else:
                on_path.discard(name)
                if name in digest:
                    continue
                rec = records[name]
                if rec["k"] == "boundary":
                    package = rec["p"]
                    if package not in deps:
                        raise GateError(f"boundary package {package!r} of {name} is not pinned")
                    value = sha(b"boundary", name.encode(), deps[package].encode())
                else:
                    children = [digest[ref].encode() for ref in rec["r"]]
                    value = sha(rec["k"].encode(), rec["s"].encode(), *children)
                digest[name] = value
                stats["digests_computed"] += 1
    # Every referenced constant is computed once, on its first resolution; every
    # further resolution of it is answered from the table (a memo hit).
    total_edges = sum(len(r["r"]) for r in records.values() if r["k"] != "boundary")
    stats["child_resolutions"] = total_edges
    stats["memo_hits"] = total_edges - (stats["digests_computed"] - count_roots(records))
    return digest, stats


def count_roots(records: dict[str, dict]) -> int:
    referenced = set()
    for rec in records.values():
        referenced.update(rec["r"])
    return sum(1 for name in records if name not in referenced)


# ---------------------------------------------------------------- manifest


def manifest_rows(records: dict[str, dict], digest: dict[str, str]) -> list[str]:
    rows = []
    for name in sorted(records):
        rec = records[name]
        if rec["k"] == "pin":
            continue
        rows.append(f"{name}\t{rec['k']}\t{rec['m']}\t{digest[name]}")
    return rows


def root_rows(pins: list[dict], digest: dict[str, str]) -> list[str]:
    return [f"{p['n']}\t{p['line']}\t{p['ns']}\t{digest[p['n']]}" for p in pins]


def header(records: dict[str, dict], pins: list[dict], deps: dict[str, str]) -> dict:
    kinds: dict[str, int] = defaultdict(int)
    for rec in records.values():
        kinds[rec["k"]] += 1
    used = sorted({rec["p"] for rec in records.values() if rec["k"] == "boundary"})
    return {
        "schema": SCHEMA,
        "digest": "sha256",
        "pins": len(pins),
        "constants": sum(n for k, n in kinds.items() if k != "pin"),
        "kinds": dict(sorted(kinds.items())),
        "boundary_identities": {p: deps[p] for p in used},
    }


def write_manifest(out: Path, records, pins, digest, deps) -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out / "constants.tsv").write_text("\n".join(manifest_rows(records, digest)) + "\n")
    (out / "roots.tsv").write_text("\n".join(root_rows(pins, digest)) + "\n")
    (out / "header.json").write_text(json.dumps(header(records, pins, deps), indent=1) + "\n")


def read_manifest(directory: Path) -> tuple[dict[str, tuple[str, str, str]], dict[str, tuple[str, str]], dict]:
    constants = {}
    for line in (directory / "constants.tsv").read_text().splitlines():
        name, kind, module, value = line.split("\t")
        constants[name] = (kind, module, value)
    roots = {}
    for line in (directory / "roots.tsv").read_text().splitlines():
        pin, lineno, _ns, value = line.split("\t")
        roots[pin] = (lineno, value)
    head = json.loads((directory / "header.json").read_text())
    return constants, roots, head


# ---------------------------------------------------------------- compare


def compare(committed: Path, records, pins, digest, deps, limit: int = 40) -> tuple[list[str], list[str]]:
    """Return (failure lines, notes).  The verdict is the pin roots: every
    manifest constant is reachable from some pin, so a constant whose content
    moved moves a root too.  Differences that move no root (a constant renamed
    with its content unchanged) are notes, not failures."""
    old_constants, old_roots, old_head = read_manifest(committed)
    new_head = header(records, pins, deps)
    lines: list[str] = []
    if old_head.get("schema") != SCHEMA:
        lines.append(f"schema moved: {old_head.get('schema')} -> {SCHEMA}")
    if old_head.get("boundary_identities") != new_head["boundary_identities"]:
        lines.append("boundary identity moved (toolchain or a pinned package rev): "
                     f"{old_head.get('boundary_identities')} -> {new_head['boundary_identities']}")
    new_constants = {name: (rec["k"], rec["m"], digest[name])
                     for name, rec in records.items() if rec["k"] != "pin"}
    old_digests = {value for (_, _, value) in old_constants.values()}
    new_digests = {value for (_, _, value) in new_constants.values()}
    changed = {n for n in new_constants if n in old_constants and old_constants[n][2] != new_constants[n][2]}
    added = set(new_constants) - set(old_constants)
    removed = set(old_constants) - set(new_constants)
    renamed_in = {n for n in added if new_constants[n][2] in old_digests}
    renamed_out = {n for n in removed if old_constants[n][2] in new_digests}
    # A constant whose digest is new while every constant it refers to has a
    # digest the committed table already knew moved by its own content: those
    # are the origins to review.
    moved = (changed | added) - renamed_in
    origins = sorted(n for n in moved
                     if all(new_constants[ref][2] in old_digests for ref in records[n]["r"]))
    new_roots = {p["n"]: (str(p["line"]), digest[p["n"]]) for p in pins}
    pin_changed = [pin for pin in sorted(set(old_roots) | set(new_roots))
                   if old_roots.get(pin, (None, None))[1] != new_roots.get(pin, (None, None))[1]]
    notes: list[str] = []
    if not (pin_changed or lines):
        if changed or added or removed:
            notes.append(f"manifest names moved without moving any pin root: {len(renamed_in)} entered and "
                         f"{len(renamed_out)} left under a known digest, {len(moved)} new digest(s), "
                         f"{len(removed - renamed_out)} unmatched removal(s); a refresh is optional")
        return [], notes
    users: dict[str, list[str]] = defaultdict(list)
    for name, rec in records.items():
        for ref in rec["r"]:
            users[ref].append(name)

    def pins_reaching(name: str) -> list[str]:
        seen, stack, found = {name}, [name], []
        while stack:
            for user in users[stack.pop()]:
                if user not in seen:
                    seen.add(user)
                    stack.append(user)
                    if records[user]["k"] == "pin":
                        found.append(user)
        return sorted(found)

    lines.append(f"{len(origins)} constant(s) whose own content moved:")
    for name in origins[:limit]:
        kind, module, _ = new_constants[name]
        reached = pins_reaching(name)
        shown = ", ".join(f"{p} (line {records[p]['line']})" for p in reached[:8])
        more = f", +{len(reached) - 8} more" if len(reached) > 8 else ""
        state = "new" if name in added else "changed"
        lines.append(f"  {state} {kind} {name} [{module}] -> {len(reached)} pin(s): {shown}{more}")
    if len(origins) > limit:
        lines.append(f"  ... {len(origins) - limit} more")
    further = sorted(moved - set(origins))
    lines.append(f"{len(further)} further constant(s) moved through what they refer to"
                 + (": " + ", ".join(further[:limit]) + (" ..." if len(further) > limit else "") if further else ""))
    gone = sorted(removed - renamed_out)
    if gone:
        lines.append(f"{len(gone)} constant(s) left the closure: "
                     + ", ".join(gone[:limit]) + (" ..." if len(gone) > limit else ""))
    lines.append(f"{len(pin_changed)} pin root(s) moved: "
                 + ", ".join(f"{p} (line {new_roots.get(p, old_roots.get(p))[0]})" for p in pin_changed[:limit])
                 + (" ..." if len(pin_changed) > limit else ""))
    return lines, notes


# ---------------------------------------------------------------- self-test


def self_test() -> int:
    """In-memory controls for the Merkle table and the comparison."""
    deps = {"@toolchain": "lean4:test", "mathlib": "mathlib@abc"}

    def recs(leaf_ser: str = "def u=0 type=0 value=1\nC0{}\nN1", leaf_refs=("Nat",)) -> dict:
        rows = [
            {"n": "Nat", "k": "boundary", "m": "Init.Prelude", "p": "@toolchain", "s": "", "r": []},
            {"n": "Blanc.leaf", "k": "def", "m": "Blanc.A", "p": "", "s": leaf_ser, "r": list(leaf_refs)},
            {"n": "Blanc.mid", "k": "def", "m": "Blanc.B", "p": "", "s": "def u=0 type=0 value=1\nC0{}\nC1{}", "r": ["Nat", "Blanc.leaf"]},
            {"n": "Blanc.top", "k": "def", "m": "Blanc.C", "p": "", "s": "def u=0 type=0 value=1\nC0{}\nC1{}", "r": ["Nat", "Blanc.mid"]},
            {"n": "Blanc.thm", "k": "theorem", "m": "Blanc.C", "p": "", "s": "theorem u=0 type=0\nC0{}", "r": ["Blanc.top"]},
            {"n": "pin:0001", "k": "pin", "m": "scripts.ClaimCheck", "p": "", "s": "pin u=0 type=0\nC0{}", "r": ["Blanc.top"], "line": 10, "ns": "Blanc"},
            {"n": "pin:0002", "k": "pin", "m": "scripts.ClaimCheck", "p": "", "s": "pin u=0 type=0\nC0{}", "r": ["Nat"], "line": 20, "ns": "Blanc"},
        ]
        return {r["n"]: r for r in rows}

    failures = []

    def check(label: str, ok: bool) -> None:
        print(("PASS " if ok else "FAIL ") + label)
        if not ok:
            failures.append(label)

    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp) / "base"
        records = recs()
        pins = [records["pin:0001"], records["pin:0002"]]
        digest, stats = merkle(records, deps)
        write_manifest(base, records, pins, digest, deps)
        check("unchanged closure compares clean", compare(base, records, pins, digest, deps) == ([], []))
        check("memo answers repeated children", stats["memo_hits"] >= 1)

        # a semantic change two levels below the pinned constant
        bad = recs(leaf_ser="def u=0 type=0 value=1\nC0{}\nN2")
        bad_digest, _ = merkle(bad, deps)
        report, _ = compare(base, bad, [bad["pin:0001"], bad["pin:0002"]], bad_digest, deps)
        text = "\n".join(report)
        check("deep change fails", bool(report))
        check("deep change names the origin", "changed def Blanc.leaf" in text)
        check("deep change names the pin it reaches", "pin:0001 (line 10)" in text)
        check("deep change leaves the unrelated pin out", "pin:0002" not in text)
        check("deep change names constants moved through it", "Blanc.mid" in text and "Blanc.top" in text)

        # a dependency bump moves boundary digests and is reported as such
        bumped = dict(deps, **{"@toolchain": "lean4:other"})
        b_digest, _ = merkle(records, bumped)
        report, _ = compare(base, records, pins, b_digest, bumped)
        check("boundary identity move is reported", any("boundary identity moved" in l for l in report))

        # a reference cycle fails closed
        cyc = recs()
        cyc["Blanc.leaf"] = dict(cyc["Blanc.leaf"], r=["Blanc.top"])
        try:
            merkle(cyc, deps)
            check("cycle fails closed", False)
        except GateError:
            check("cycle fails closed", True)

        # an unpinned boundary package fails closed
        unpinned = recs()
        unpinned["Nat"] = dict(unpinned["Nat"], p="unknownpkg")
        try:
            merkle(unpinned, deps)
            check("unpinned boundary package fails closed", False)
        except GateError:
            check("unpinned boundary package fails closed", True)

        # names are not content: renaming a referenced Blanc constant keeps the root
        renamed = recs()
        leaf = dict(renamed.pop("Blanc.leaf"), n="Blanc.leaf2")
        renamed["Blanc.leaf2"] = leaf
        renamed["Blanc.mid"] = dict(renamed["Blanc.mid"], r=["Nat", "Blanc.leaf2"])
        r_digest, _ = merkle(renamed, deps)
        check("a renamed internal constant keeps the pin root", r_digest["pin:0001"] == digest["pin:0001"])
        r_fail, r_notes = compare(base, renamed, [renamed["pin:0001"], renamed["pin:0002"]], r_digest, deps)
        check("a rename alone is a note, not a failure", r_fail == [] and len(r_notes) == 1)

        # the verdict reads the committed roots: one flipped root digest fails
        lines = (base / "roots.tsv").read_text().splitlines()
        lines[0] = lines[0][:-1] + ("0" if lines[0][-1] != "0" else "1")
        (base / "roots.tsv").write_text("\n".join(lines) + "\n")
        check("a corrupted committed root fails", bool(compare(base, records, pins, digest, deps)[0]))

    if failures:
        print(f"FAIL — claim-hash self-test: {len(failures)} control(s) did not bite")
        return 1
    print("OK — claim-hash self-test: all controls bite")
    return 0


# ---------------------------------------------------------------- main


def generate(root: Path, work: Path, records_file: Path | None) -> tuple:
    expected = expected_pin_count(root)
    by_regex = regex_pin_count(root)
    if by_regex != expected:
        raise GateError(f"ClaimCheck has {by_regex} pin lines; scripts/check-claims.sh expects {expected}")
    deps = dependency_identities(root)
    lean_wall = None
    if records_file is None:
        records_file = work / "records.jsonl"
        lean_wall = run_driver(root, records_file, work / "driver.log")
    records, pins, lean_stats = load_records(records_file)
    if len(pins) != expected:
        raise GateError(f"driver hashed {len(pins)} pins; scripts/check-claims.sh expects {expected}")
    t0 = time.monotonic()
    digest, merkle_stats = merkle(records, deps)
    merkle_wall = time.monotonic() - t0
    return records, pins, digest, deps, lean_stats, merkle_stats, lean_wall, merkle_wall


def report_stats(pins, lean_stats, merkle_stats, lean_wall, merkle_wall, total_wall) -> str:
    peak = lean_stats.get("peak_rss_kib", 0)
    parts = [
        f"pins={len(pins)}",
        f"constants={lean_stats['constants']} (blanc={lean_stats['blanc']}, claimcheck-local={lean_stats['local']}, boundary={lean_stats['boundary']}, inductive-blocks={lean_stats['blocks']})",
        f"closure-walk visited-memo hits={lean_stats['visit_memo_hits']}",
        f"subterm memo hits={lean_stats['expr_memo_hits']}",
        f"digests computed={merkle_stats['digests_computed']}, digest memo hits={merkle_stats['memo_hits']}",
        f"serialized={lean_stats['serialized_bytes']} bytes",
        f"elaboration={lean_stats['elab_ms'] / 1000:.1f}s walk={lean_stats['walk_ms'] / 1000:.1f}s"
        + (f" driver-wall={lean_wall:.1f}s" if lean_wall is not None else "")
        + f" merkle={merkle_wall:.1f}s total={total_wall:.1f}s",
        f"driver peak RSS={peak / 1048576:.2f} GiB",
    ]
    if lean_wall is not None:
        walk_only = (lean_stats['walk_ms'] / 1000 + merkle_wall)
        parts.append(f"cost per pin: {total_wall / len(pins) * 1000:.0f} ms all-in, "
                     f"{walk_only / len(pins) * 1000:.1f} ms beyond elaborating ClaimCheck")
    return "; ".join(parts)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--generate", type=Path, metavar="DIR")
    parser.add_argument("--records", type=Path, metavar="FILE")
    parser.add_argument("--keep", type=Path, metavar="DIR", help="keep the fresh run's files here")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--stats-json", type=Path, metavar="FILE")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    start = time.monotonic()
    try:
        with tempfile.TemporaryDirectory(prefix="claim-hash-", dir=os.environ.get("CLAIM_HASH_TMPDIR")) as tmp:
            work = Path(tmp)
            records, pins, digest, deps, lean_stats, merkle_stats, lean_wall, merkle_wall = \
                generate(ROOT, work, args.records)
            fresh = args.generate or args.keep or (work / "fresh")
            write_manifest(fresh, records, pins, digest, deps)
            total = time.monotonic() - start
            summary = report_stats(pins, lean_stats, merkle_stats, lean_wall, merkle_wall, total)
            if args.stats_json:
                args.stats_json.write_text(json.dumps({
                    "lean": lean_stats, "merkle": merkle_stats, "driver_wall_s": lean_wall,
                    "merkle_wall_s": merkle_wall, "total_wall_s": total,
                    "children_peak_rss_kib": child_peak_rss_kib()}, indent=1) + "\n")
            if args.generate:
                print(f"GENERATED — claim closure hash: {args.generate}; {summary}")
                return 0
            if not (MANIFEST_DIR / "constants.tsv").exists():
                print("REGRESSION — claim closure hash: no committed manifest in scripts/claim-pin-hash/")
                return 1
            report, notes = compare(MANIFEST_DIR, records, pins, digest, deps)
            for note in notes:
                print(f"note: {note}")
            if report:
                print("\n".join(report))
                print("REGRESSION — claim closure hash: the meaning of pinned claims moved; "
                      "review the constants above (refreshing the manifest is a user decision)")
                return 1
            print(f"OK — claim closure hash: {len(pins)} pin roots and {len(digest) - len(pins)} manifest "
                  f"entries unchanged; {summary}")
            return 0
    except GateError as error:
        print(f"REGRESSION — claim closure hash: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
