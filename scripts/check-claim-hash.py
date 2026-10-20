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
   ordered constants that serialization refers to.  Generative constants
   (inductive types, constructors, recursors and their blocks) carry their full
   names; definitions are content-addressed.  It also serializes a fixture of
   declaration pairs that differ in exactly one feature.
2. This script computes a Merkle SHA-256 table bottom-up with its own in-run
   memo: a constant's digest is the SHA-256 of its kind, its serialization and
   the digests of the constants it refers to, so a referenced constant
   contributes its digest, never its name.  Constants of Blanc and of the
   pinned Jaune package are hashed in full (Jaune's EVM semantics are part of
   every claim's meaning; user decision 2026-10-20), so a Jaune bump moves
   exactly the roots whose meaning changed.  Boundary constants (the Lean
   toolchain, Mathlib, Batteries and any other package) contribute their name
   and the identity of the pinned dependency that owns them: ``lean-toolchain``
   for Lean core and Std, the ``lake-manifest.json`` rev otherwise.

Why the split: Lean ships no SHA-256, and a hand-written one would run in the
interpreter over ~10 MB of serialization; Python's ``hashlib`` is the reviewed
primitive.  Lean keeps the part that needs the elaborated environment (the
closure walk and the canonical serialization); Python keeps the digests and
the comparison.  Nothing persists between runs: both memo tables live for one
run only, so a stale cache cannot make a changed definition look unchanged.

What is verdict-bearing: the per-pin root digests in ``roots.tsv``, keyed by a
position-independent pin label, and nothing else.  Each root is a Merkle
commitment to the pin's whole closure, so any content change in any constant of
the manifest moves at least one root.  ``constants.tsv``, ``boundary.tsv`` and
the counts in ``header.json`` are diagnostics: they name what moved, and a
difference that moves no root (a definition renamed with its content unchanged)
is printed as a note.

Preconditions checked before hashing, each failing the run: the Lean artifacts
are certified current for the sources (the exact build certificate
``scripts/gate-cache.py`` keeps after an authoritative ``lake build``; this gate
reads it and never builds), every installed Lake package is at its
``lake-manifest.json`` rev, the running Lean is the ``lean-toolchain`` version,
the pin count equals the literal in ``scripts/check-claims.sh``, the in-memory
controls bite, and the Lean serializer fixture separates every pair.

A hash detects change, not weakening.  On a mismatch the gate names the
constants whose own content moved, the other constants that moved because of
them, and the pins whose roots they reach, and fails; the readable ``example``
pins in ClaimCheck stay the reviewed statement.

Modes:
  (default)          check the preconditions, regenerate into a temporary
                     directory and compare with scripts/claim-pin-hash/
  --generate DIR     check the preconditions, regenerate and write the
                     manifest files into DIR (adopting them is a reviewed act)
  --generate DIR --records FILE --fixture FILE
                     debug: build a manifest from an earlier driver output;
                     prints UNVERIFIED and never compares
  --self-test        in-memory controls of the Merkle and comparison logic
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
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
SCHEMA = 3
DOMAIN = b"blanc-claim-pin-hash/v2\0"
# Packages hashed in full (user decision 2026-10-20); the driver's list must agree.
FULLY_HASHED = ("jaune",)
PIN_REGEX = re.compile(r"^[ \t\r\v\f]*example([ \t\r\v\f]|$)")

# The fixture pairs the driver must emit, each with its expectation.
FIXTURE = {
    "level succ": "differ",
    "level max vs imax": "differ",
    "level param position": "differ",
    "universe parameter order": "differ",
    "proj index": "differ",
    "proj struct name (isomorphic structures)": "differ",
    "let value": "differ",
    "literal Nat vs String": "differ",
    "constructor order": "differ",
    "field order": "differ",
    "numParams vs numIndices": "differ",
    "definition value": "differ",
    "definition type": "differ",
    "opaque name": "differ",
    "inductive name (isomorphic types)": "differ",
    "constructor name": "differ",
    "use of isomorphic types in a definition": "differ",
    "universe arguments of a constant": "differ",
    "application argument order": "differ",
    "lambda vs forall": "differ",
    "theorem statement": "differ",
    "inductive unsafe flag": "differ",
    "theorem proof (must be equal)": "equal",
    "a Jaune constant is hashed by content": "differ",
    "binder name (must be equal)": "equal",
    "binder info (must be equal)": "equal",
    "metadata (must be equal)": "equal",
    "definition name (content-addressed, must be equal)": "equal",
}
SERIALIZER_CHECKS = 8


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


def check_installed_packages(root: Path) -> int:
    """Every installed `.lake/packages/<pkg>` is at its lake-manifest.json rev."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        directory = root / ".lake" / "packages" / package["name"]
        if not directory.is_dir():
            raise GateError(f"Lake package {package['name']} is not installed")
        head = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                              capture_output=True, text=True)
        if head.returncode != 0 or head.stdout.strip() != package["rev"]:
            raise GateError(f"Lake package {package['name']} is at {head.stdout.strip() or '?'}, "
                            f"lake-manifest.json pins {package['rev']}")
        dirt = subprocess.run(["git", "-C", str(directory), "status", "--porcelain"],
                              capture_output=True, text=True)
        if dirt.returncode != 0 or dirt.stdout.strip():
            raise GateError(f"Lake package {package['name']} has uncommitted or untracked changes")
    return len(manifest["packages"])


def check_lean_version(root: Path, version: str) -> None:
    toolchain = (root / "lean-toolchain").read_text().strip()
    if not toolchain.endswith(f":v{version}"):
        raise GateError(f"the running Lean is {version}; lean-toolchain pins {toolchain}")


def artifact_currency(root: Path) -> str:
    """Reuse the exact build certificate the selective runner keeps; never build."""
    path = root / "scripts" / "gate-cache.py"
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    if str(path.parent) not in sys.path:
        sys.path.insert(0, str(path.parent))
    try:
        spec = importlib.util.spec_from_file_location("blanc_gate_cache_for_claim_hash", path)
        if spec is None or spec.loader is None:
            raise GateError("cannot load scripts/gate-cache.py")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    current, reason, certificate = module.build_certificate_status(root)
    if not current:
        raise GateError(
            "the Lean artifacts are not certified current for these sources "
            f"({reason}); run the authoritative lake build through the owned build path, then "
            "scripts/certify-checked-build.sh, and rerun")
    return reason, certificate


def check_fully_hashed_currency(certificate: dict) -> dict[str, int]:
    """Hashing a package in full is only meaningful if its artifacts were proven
    current: every FULLY_HASHED package must be among the certificate's checked
    dependencies with a nonzero module count and have no unchecked modules."""
    currency = (certificate or {}).get("currency") or {}
    checked = currency.get("dependencies")
    unchecked = currency.get("unchecked")
    if not isinstance(checked, dict) or not isinstance(unchecked, dict):
        raise GateError("the build certificate records no dependency currency (schema v4 required)")
    counts = {}
    for package in FULLY_HASHED:
        if unchecked.get(package, 0):
            raise GateError(f"fully hashed package {package} has {unchecked[package]} module(s) the "
                            "build certificate does not prove current")
        if not checked.get(package, 0):
            raise GateError(f"fully hashed package {package} is not among the build certificate's "
                            "checked dependencies")
        counts[package] = checked[package]
    return counts


def check_pin_binding(expected: int, by_regex: int, by_driver: int | None = None) -> None:
    if by_regex != expected:
        raise GateError(f"ClaimCheck has {by_regex} pin lines; scripts/check-claims.sh expects {expected}")
    if by_driver is not None and by_driver != expected:
        raise GateError(f"driver hashed {by_driver} pins; scripts/check-claims.sh expects {expected}")


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


def run_driver(root: Path, out: Path, fixture: Path, log: Path) -> float:
    start = time.monotonic()
    with log.open("wb") as handle:
        status = subprocess.run(
            ["lake", "env", "lean", "--run", DRIVER, CLAIMCHECK, str(out), str(fixture)],
            cwd=root, stdout=handle, stderr=subprocess.STDOUT).returncode
    if status != 0:
        tail = log.read_text(errors="replace").splitlines()[-40:]
        raise GateError("closure driver failed (exit %d); log tail:\n%s" % (status, "\n".join(tail)))
    return time.monotonic() - start


def parse_records(lines) -> tuple[dict[str, dict], list[dict], dict]:
    records: dict[str, dict] = {}
    pins: list[dict] = []
    stats: dict = {}
    for line in lines:
        row = json.loads(line) if isinstance(line, str) else line
        if row.get("k") == "stats":
            stats = row
            continue
        name = row["n"]
        if name in records:
            raise GateError(f"duplicate record {name}")
        records[name] = row
        if row["k"] == "pin":
            pins.append(row)
    return records, pins, stats


def load_records(path: Path) -> tuple[dict[str, dict], list[dict], dict]:
    with path.open() as handle:
        records, pins, stats = parse_records(handle)
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
    for start in records:
        if start in digest:
            continue
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
    # Every referenced constant is computed once, on its first resolution; every
    # further resolution of it is answered from the table (a memo hit).
    edges = sum(len(r["r"]) for r in records.values())
    referenced = set()
    for rec in records.values():
        referenced.update(rec["r"])
    stats = {"digests_computed": len(digest), "child_resolutions": edges,
             "memo_hits": edges - len(referenced)}
    return digest, stats


def boundary_diagnostics(records: dict[str, dict]) -> dict[str, str]:
    """Shallow digests of boundary constants' own content (references by name).
    Diagnostic only: a dependency bump can be diffed constant by constant."""
    out = {}
    for name, rec in records.items():
        if rec["k"] == "boundary":
            if "d" in rec:
                out[name] = sha(b"shallow", rec["d"].encode(), *(r.encode() for r in rec["dr"]))
            else:
                out[name] = "unserializable"
    return out


# ---------------------------------------------------------------- fixture


def verify_fixture(path: Path, deps: dict[str, str]) -> int:
    seen: dict[str, str] = {}
    with path.open() as handle:
        for line in handle:
            row = json.loads(line)
            label, expect = row["label"], row["expect"]
            if label in seen:
                raise GateError(f"fixture pair repeated: {label}")
            sides = []
            for side in ("a", "b"):
                records, _, _ = parse_records(row[side]["records"])
                digest, _ = merkle(records, deps)
                sides.append(digest[row[side]["root"]])
            differ = sides[0] != sides[1]
            if differ != (expect == "differ"):
                raise GateError(f"serializer fixture failed: {label} "
                                f"({'digests collide' if expect == 'differ' else 'digests differ'})")
            seen[label] = expect
    if seen != FIXTURE:
        missing = sorted(set(FIXTURE) - set(seen))
        extra = sorted(set(seen) - set(FIXTURE))
        raise GateError(f"serializer fixture population moved: missing {missing}, unexpected {extra}")
    return len(seen)


# ---------------------------------------------------------------- manifest


def scope_of(rec: dict) -> str:
    if rec["k"] == "boundary":
        return "boundary"
    return rec.get("sc") or ("local" if rec["m"] == "scripts.ClaimCheck" else "blanc")


def manifest_rows(records: dict[str, dict], digest: dict[str, str]) -> list[str]:
    return [f"{name}\t{records[name]['k']}\t{records[name]['m']}\t{scope_of(records[name])}\t{digest[name]}"
            for name in sorted(records) if records[name]["k"] != "pin"]


def pin_keys(pins: list[dict], digest: dict[str, str]) -> dict[str, str]:
    """Pin record name -> stable key.  A label used by one pin is its key.  A
    repeated label is disambiguated by the pin's own statement digest (its root),
    so inserting or reordering pins moves no other key; pins whose label and
    statement are both equal are interchangeable and are numbered ~2, ~3 in file
    order, which cannot hide a change because their roots are equal."""
    by_label: dict[str, list[dict]] = defaultdict(list)
    for pin in sorted(pins, key=lambda p: p["ordinal"]):
        by_label[pin["label"]].append(pin)
    keys: dict[str, str] = {}
    for label, group in by_label.items():
        if len(group) == 1:
            keys[group[0]["n"]] = label
            continue
        seen: dict[str, int] = defaultdict(int)
        for pin in group:
            base = f"{label}#{digest[pin['n']][:16]}"
            seen[base] += 1
            keys[pin["n"]] = base if seen[base] == 1 else f"{base}~{seen[base]}"
    return keys


def root_rows(pins: list[dict], digest: dict[str, str]) -> list[str]:
    keys = pin_keys(pins, digest)
    return [f"{keys[p['n']]}\t{p['ordinal']}\t{p['line']}\t{p['ns']}\t{digest[p['n']]}"
            for p in sorted(pins, key=lambda p: keys[p["n"]])]


def boundary_rows(records: dict[str, dict], diag: dict[str, str]) -> list[str]:
    return [f"{name}\t{records[name]['p']}\t{diag[name]}" for name in sorted(diag)]


def header(records: dict[str, dict], pins: list[dict], deps: dict[str, str]) -> dict:
    kinds: dict[str, int] = defaultdict(int)
    modules: dict[str, int] = defaultdict(int)
    for rec in records.values():
        kinds[rec["k"]] += 1
        if rec["k"] not in ("pin", "boundary", "block"):
            modules[scope_of(rec)] += 1
    used = sorted({rec["p"] for rec in records.values() if rec["k"] == "boundary"})
    return {
        "schema": SCHEMA,
        "digest": "sha256",
        "verdict": "roots.tsv only; constants.tsv, boundary.tsv and these counts are diagnostic",
        "pin_key": "label (thm:/iff:/eq:/stmt:/uses:/anon); a repeated label gets #<statement digest prefix>",
        "pins": len(pins),
        "entries": sum(n for k, n in kinds.items() if k != "pin"),
        "kinds": dict(sorted(kinds.items())),
        "hashed_constants": dict(sorted(modules.items())),
        "boundary_identities": {p: deps[p] for p in used},
        "fully_hashed_provenance": {p: deps[p] for p in FULLY_HASHED if p in deps},
    }


def write_manifest(out: Path, records, pins, digest, deps) -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out / "constants.tsv").write_text("\n".join(manifest_rows(records, digest)) + "\n")
    (out / "roots.tsv").write_text("\n".join(root_rows(pins, digest)) + "\n")
    (out / "boundary.tsv").write_text(
        "\n".join(boundary_rows(records, boundary_diagnostics(records))) + "\n")
    (out / "header.json").write_text(json.dumps(header(records, pins, deps), indent=1) + "\n")


def read_manifest(directory: Path):
    constants = {}
    for line in (directory / "constants.tsv").read_text().splitlines():
        name, kind, module, _scope, value = line.split("\t")
        constants[name] = (kind, module, value)
    roots = {}
    for line in (directory / "roots.tsv").read_text().splitlines():
        label, ordinal, lineno, _ns, value = line.split("\t")
        roots[label] = (lineno, value)
    boundary = {}
    if (directory / "boundary.tsv").exists():
        for line in (directory / "boundary.tsv").read_text().splitlines():
            name, _pkg, value = line.split("\t")
            boundary[name] = value
    head = json.loads((directory / "header.json").read_text())
    return constants, roots, boundary, head


# ---------------------------------------------------------------- compare


def compare(committed: Path, records, pins, digest, deps, limit: int = 40) -> tuple[list[str], list[str]]:
    """Return (failure lines, notes).  Only the pin roots (and the schema) decide;
    everything else is diagnostic and reported as notes."""
    old_constants, old_roots, old_boundary, old_head = read_manifest(committed)
    new_head = header(records, pins, deps)
    lines: list[str] = []
    notes: list[str] = []
    if old_head.get("schema") != SCHEMA:
        lines.append(f"manifest schema moved: {old_head.get('schema')} -> {SCHEMA}")
    if old_head.get("boundary_identities") != new_head["boundary_identities"]:
        lines.append("boundary identity moved (toolchain or a pinned package rev): "
                     f"{old_head.get('boundary_identities')} -> {new_head['boundary_identities']}")
    for key in ("kinds", "hashed_constants", "entries", "fully_hashed_provenance"):
        if old_head.get(key) != new_head[key]:
            notes.append(f"header {key} moved: {old_head.get(key)} -> {new_head[key]}")
    new_boundary = boundary_diagnostics(records)
    moved_boundary = sorted(n for n in new_boundary if n in old_boundary and old_boundary[n] != new_boundary[n])
    if moved_boundary:
        notes.append(f"{len(moved_boundary)} boundary constant(s) whose own content moved (diagnostic): "
                     + ", ".join(moved_boundary[:limit]) + (" ..." if len(moved_boundary) > limit else ""))

    new_constants = {name: (rec["k"], rec["m"], digest[name])
                     for name, rec in records.items() if rec["k"] != "pin"}
    old_digests = {value for (_, _, value) in old_constants.values()}
    new_digests = {value for (_, _, value) in new_constants.values()}
    changed = {n for n in new_constants if n in old_constants and old_constants[n][2] != new_constants[n][2]}
    added = set(new_constants) - set(old_constants)
    removed = set(old_constants) - set(new_constants)
    renamed_in = {n for n in added if new_constants[n][2] in old_digests}
    renamed_out = {n for n in removed if old_constants[n][2] in new_digests}
    moved = (changed | added) - renamed_in
    origins = sorted(n for n in moved
                     if all(new_constants[ref][2] in old_digests for ref in records[n]["r"]))
    keys = pin_keys(pins, digest)
    new_roots = {keys[p["n"]]: (str(p["line"]), digest[p["n"]]) for p in pins}
    pins_added = sorted(set(new_roots) - set(old_roots))
    pins_removed = sorted(set(old_roots) - set(new_roots))
    pins_moved = sorted(l for l in set(new_roots) & set(old_roots) if new_roots[l][1] != old_roots[l][1])
    if not (pins_added or pins_removed or pins_moved or lines):
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

    if pins_added:
        lines.append(f"{len(pins_added)} pin(s) added: "
                     + ", ".join(f"{l} (line {new_roots[l][0]})" for l in pins_added[:limit]))
    if pins_removed:
        lines.append(f"{len(pins_removed)} pin(s) removed: "
                     + ", ".join(f"{l} (was line {old_roots[l][0]})" for l in pins_removed[:limit]))
    if pins_moved or moved:
        lines.append(f"{len(origins)} constant(s) whose own content moved:")
        for name in origins[:limit]:
            kind, module, _ = new_constants[name]
            reached = pins_reaching(name)
            shown = ", ".join(f"{keys[p]} (line {records[p]['line']})" for p in reached[:8])
            more = f", +{len(reached) - 8} more" if len(reached) > 8 else ""
            state = "new" if name in added else "changed"
            lines.append(f"  {state} {kind} {name} [{module}, scope {scope_of(records[name])}] -> {len(reached)} pin(s): {shown}{more}")
        if len(origins) > limit:
            lines.append(f"  ... {len(origins) - limit} more")
        further = sorted(moved - set(origins))
        lines.append(f"{len(further)} further constant(s) moved through what they refer to"
                     + (": " + ", ".join(further[:limit]) + (" ..." if len(further) > limit else "") if further else ""))
    gone = sorted(removed - renamed_out)
    if gone:
        lines.append(f"{len(gone)} constant(s) left the closure: "
                     + ", ".join(gone[:limit]) + (" ..." if len(gone) > limit else ""))
    if pins_moved:
        lines.append(f"{len(pins_moved)} pin root(s) moved: "
                     + ", ".join(f"{l} (line {new_roots[l][0]})" for l in pins_moved[:limit])
                     + (" ..." if len(pins_moved) > limit else ""))
    return lines, notes


# ---------------------------------------------------------------- guards on a real run


def check_fully_hashed(records: dict[str, dict], lean_stats: dict) -> dict[str, int]:
    """The driver's fully hashed package list equals FULLY_HASHED, every such
    package contributed hashed constants, and none of them appears as boundary."""
    driver = tuple(lean_stats.get("fully_hashed_packages", ()))
    if driver != FULLY_HASHED:
        raise GateError(f"fully hashed packages differ: driver {list(driver)}, checker {list(FULLY_HASHED)}")
    counts = {p: 0 for p in FULLY_HASHED}
    for name, rec in records.items():
        if rec["k"] == "boundary" and rec["p"] in counts:
            raise GateError(f"{name} of fully hashed package {rec['p']} was treated as boundary")
        if rec.get("sc") in counts and rec["k"] != "block":
            counts[rec["sc"]] += 1
    for package, n in counts.items():
        if n == 0:
            raise GateError(f"fully hashed package {package} contributed no hashed constant")
    return counts


def real_record_controls(records, pins, digest, deps, work: Path) -> dict[str, str]:
    """On the real driver output: perturb the serialization of one jaune-scoped
    and one blanc-scoped definition (the first by name), recompute the Merkle
    table, and require that some pin root moves and that the comparison names
    the perturbed constant with its scope."""
    base = work / "control-base"
    write_manifest(base, records, pins, digest, deps)
    results = {}
    for scope in ("jaune", "blanc"):
        candidates = sorted(n for n, r in records.items() if r.get("sc") == scope and r["k"] == "def")
        if not candidates:
            raise GateError(f"real-record control: no {scope}-scoped definition to perturb")
        name = candidates[0]
        perturbed = dict(records)
        perturbed[name] = dict(records[name], s=records[name]["s"] + "\nperturbed")
        p_digest, _ = merkle(perturbed, deps)
        moved = sum(1 for p in pins if p_digest[p["n"]] != digest[p["n"]])
        report, _ = compare(base, perturbed, pins, p_digest, deps)
        named = any(f"changed def {name} [" in l and f"scope {scope}]" in l for l in report)
        if moved == 0 or not named:
            raise GateError(f"real-record control did not bite for {scope} constant {name} "
                            f"({moved} roots moved, named={named})")
        results[scope] = f"{name} moved {moved} root(s)"
    return results


# ---------------------------------------------------------------- self-test


def self_test(quiet: bool = False) -> int:
    """In-memory controls for the Merkle table and the comparison."""
    deps = {"@toolchain": "lean4:test", "mathlib": "mathlib@abc"}

    def pin(label: str, refs, line: int, ordinal: int, ser: str = "pin u=0 type=0\nC0{}") -> dict:
        return {"n": f"pin:{label}@{line}", "k": "pin", "m": "scripts.ClaimCheck", "p": "", "label": label,
                "s": ser, "r": list(refs), "line": line, "ordinal": ordinal, "ns": "Blanc"}

    def recs(leaf_ser: str = "def u=0 type=0 value=1\nC0{}\nN1", leaf_refs=("Nat",)) -> dict:
        rows = [
            {"n": "Nat", "k": "boundary", "m": "Init.Prelude", "p": "@toolchain", "s": "", "r": [],
             "d": "inductive Nat", "dr": []},
            {"n": "Blanc.leaf", "k": "def", "m": "Blanc.A", "p": "", "s": leaf_ser, "r": list(leaf_refs)},
            {"n": "Blanc.mid", "k": "def", "m": "Blanc.B", "p": "", "s": "def u=0 type=0 value=1\nC0{}\nC1{}", "r": ["Nat", "Blanc.leaf"]},
            {"n": "Blanc.top", "k": "def", "m": "Blanc.C", "p": "", "s": "def u=0 type=0 value=1\nC0{}\nC1{}", "r": ["Nat", "Blanc.mid"]},
            {"n": "Blanc.thm", "k": "theorem", "m": "Blanc.C", "p": "", "s": "theorem u=0 type=0\nC0{}", "r": ["Blanc.top"]},
            pin("thm:Blanc.thm", ["Blanc.top"], 10, 1),
            pin("stmt:Nat", ["Nat"], 20, 2),
        ]
        return {r["n"]: r for r in rows}

    def pins_of(records: dict) -> list[dict]:
        return sorted((r for r in records.values() if r["k"] == "pin"), key=lambda r: r["ordinal"])

    failures = []

    def check(label: str, ok: bool) -> None:
        if not quiet or not ok:
            print(("PASS " if ok else "FAIL ") + label)
        if not ok:
            failures.append(label)

    def refuses(label: str, thunk) -> None:
        try:
            thunk()
            check(label, False)
        except GateError:
            check(label, True)

    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp) / "base"
        records = recs()
        pins = pins_of(records)
        digest, stats = merkle(records, deps)
        write_manifest(base, records, pins, digest, deps)
        check("unchanged closure compares clean", compare(base, records, pins, digest, deps) == ([], []))
        # Nat is resolved by leaf, mid, top and one pin (3 hits); top by thm and one pin (1 hit)
        check("memo answers exactly the repeated resolutions", stats["memo_hits"] == 4
              and stats["child_resolutions"] == 8 and stats["digests_computed"] == 7)

        bad = recs(leaf_ser="def u=0 type=0 value=1\nC0{}\nN2")
        bad_digest, _ = merkle(bad, deps)
        report, _ = compare(base, bad, pins_of(bad), bad_digest, deps)
        text = "\n".join(report)
        check("deep change fails", bool(report))
        check("deep change names the origin", "changed def Blanc.leaf" in text)
        check("deep change names the pin it reaches", "thm:Blanc.thm (line 10)" in text)
        check("deep change leaves the unrelated pin out", "stmt:Nat" not in text)
        check("deep change names constants moved through it", "Blanc.mid" in text and "Blanc.top" in text)

        more = recs()
        more["pin:thm:Blanc.mid@15"] = pin("thm:Blanc.mid", ["Blanc.mid"], 15, 2)
        more["pin:stmt:Nat@20"]["ordinal"] = 3
        m_digest, _ = merkle(more, deps)
        report, _ = compare(base, more, pins_of(more), m_digest, deps)
        text = "\n".join(report)
        check("an inserted pin fails as one added root and moves no other root",
              "1 pin(s) added: thm:Blanc.mid" in text and "pin root(s) moved" not in text)

        fewer = recs()
        del fewer["pin:stmt:Nat@20"]
        f_digest, _ = merkle(fewer, deps)
        report, _ = compare(base, fewer, pins_of(fewer), f_digest, deps)
        check("a removed pin fails as one removed root",
              any("1 pin(s) removed: stmt:Nat" in l for l in report)
              and not any("pin root(s) moved" in l for l in report))

        # a repeated label: keys come from the statement digest, not file order
        def dup_recs(extra: bool) -> dict:
            rows = recs()
            shift = 1 if extra else 0
            if extra:
                p0 = pin("thm:Blanc.dup", ["Nat"], 30, 3, "pin u=0 type=0\nC0{}\nN0")
                rows[p0["n"]] = p0
            for i, n in enumerate(("N1", "N2")):
                p1 = pin("thm:Blanc.dup", ["Nat"], 40 + i, 4 + i + shift, f"pin u=0 type=0\nC0{{}}\n{n}")
                rows[p1["n"]] = p1
            twin = pin("thm:Blanc.dup", ["Nat"], 50, 6 + shift, "pin u=0 type=0\nC0{}\nN2")
            rows[twin["n"]] = twin
            return rows
        base2 = Path(tmp) / "base2"
        d0 = dup_recs(False)
        d0_digest, _ = merkle(d0, deps)
        write_manifest(base2, d0, pins_of(d0), d0_digest, deps)
        d1 = dup_recs(True)
        d1_digest, _ = merkle(d1, deps)
        report, _ = compare(base2, d1, pins_of(d1), d1_digest, deps)
        text = "\n".join(report)
        check("a pin inserted ahead of a repeated-label group adds one root and moves no other",
              "1 pin(s) added: thm:Blanc.dup#" in text and "removed" not in text
              and "pin root(s) moved" not in text)
        keys = pin_keys(pins_of(d0), d0_digest)
        check("equal-statement pins of one label get distinct keys",
              len(set(keys.values())) == len(keys))

        bumped = dict(deps, **{"@toolchain": "lean4:other"})
        b_digest, _ = merkle(records, bumped)
        report, _ = compare(base, records, pins, b_digest, bumped)
        check("boundary identity move is reported", any("boundary identity moved" in l for l in report))

        cyc = recs()
        cyc["Blanc.leaf"] = dict(cyc["Blanc.leaf"], r=["Blanc.top"])
        refuses("cycle fails closed", lambda: merkle(cyc, deps))

        unpinned = recs()
        unpinned["Nat"] = dict(unpinned["Nat"], p="unknownpkg")
        refuses("unpinned boundary package fails closed", lambda: merkle(unpinned, deps))

        dangling = recs()
        dangling["Blanc.mid"] = dict(dangling["Blanc.mid"], r=["Nat", "Blanc.gone"])
        refuses("a reference with no record fails closed", lambda: merkle(dangling, deps))

        refuses("a duplicate record fails closed",
                lambda: parse_records([records["Nat"], records["Nat"]]))
        nostats = Path(tmp) / "nostats.jsonl"
        nostats.write_text(json.dumps(records["Nat"]) + "\n")
        refuses("a driver output without its stats line fails closed", lambda: load_records(nostats))

        refuses("a pin count that disagrees with check-claims.sh fails", lambda: check_pin_binding(961, 962))
        refuses("a driver pin count that disagrees fails", lambda: check_pin_binding(961, 961, 960))
        fake = Path(tmp) / "fake"
        (fake / "scripts").mkdir(parents=True)
        (fake / "scripts" / "check-claims.sh").write_text('if [[ "$claim_count" -ne  ]]; then\n')
        refuses("a check-claims.sh without its pin literal fails", lambda: expected_pin_count(fake))

        renamed = recs()
        leaf = dict(renamed.pop("Blanc.leaf"), n="Blanc.leaf2")
        renamed["Blanc.leaf2"] = leaf
        renamed["Blanc.mid"] = dict(renamed["Blanc.mid"], r=["Nat", "Blanc.leaf2"])
        r_digest, _ = merkle(renamed, deps)
        check("a renamed definition keeps the pin root",
              r_digest["pin:thm:Blanc.thm@10"] == digest["pin:thm:Blanc.thm@10"])
        r_fail, r_notes = compare(base, renamed, pins_of(renamed), r_digest, deps)
        check("a definition rename alone is a note, not a failure", r_fail == [] and len(r_notes) == 1)

        # check_installed_packages on a throwaway git repository
        pkgroot = Path(tmp) / "pkgroot"
        repo = pkgroot / ".lake" / "packages" / "p"
        repo.mkdir(parents=True)
        git = ["git", "-c", "user.name=t", "-c", "user.email=t@localhost", "-C", str(repo)]
        subprocess.run(git + ["init", "-q"], check=True)
        (repo / "f").write_text("x\n")
        subprocess.run(git + ["add", "f"], check=True)
        subprocess.run(git + ["commit", "-q", "-m", "c"], check=True)
        head = subprocess.run(git + ["rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()

        def manifest(rev: str) -> None:
            (pkgroot / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "p", "rev": rev}]}))

        manifest(head)
        check("an installed package at its rev and clean passes", check_installed_packages(pkgroot) == 1)
        manifest("0" * 40)
        refuses("an installed package at another rev than the manifest refuses",
                lambda: check_installed_packages(pkgroot))
        manifest(head)
        (repo / "f").write_text("y\n")
        refuses("a dirty installed package refuses", lambda: check_installed_packages(pkgroot))
        (repo / "f").write_text("x\n")
        (repo / "g").write_text("untracked\n")
        refuses("an untracked file in an installed package refuses", lambda: check_installed_packages(pkgroot))

        # fully hashed packages must be proven current by the certificate
        def cert(dependencies, unchecked):
            return {"currency": {"dependencies": dependencies, "unchecked": unchecked}}
        check("a certificate proving every fully hashed package current passes",
              check_fully_hashed_currency(cert({p: 3 for p in FULLY_HASHED}, {"proofwidgets": 10}))
              == {p: 3 for p in FULLY_HASHED})
        refuses("a fully hashed package with unchecked modules refuses",
                lambda: check_fully_hashed_currency(cert({p: 3 for p in FULLY_HASHED},
                                                         {p: 1 for p in FULLY_HASHED})))
        refuses("a fully hashed package missing from the checked dependencies refuses",
                lambda: check_fully_hashed_currency(cert({"mathlib": 9}, {})))
        refuses("a fully hashed package with zero checked modules refuses",
                lambda: check_fully_hashed_currency(cert({p: 0 for p in FULLY_HASHED}, {})))
        refuses("a certificate without dependency currency refuses",
                lambda: check_fully_hashed_currency({"currency": {}}))

        # the fully hashed guards
        refuses("a driver whose fully hashed list differs refuses",
                lambda: check_fully_hashed(records, {"fully_hashed_packages": []}))
        jrec = dict(records)
        jrec["Jaune.x"] = {"n": "Jaune.x", "k": "boundary", "m": "Jaune.X", "p": "jaune", "s": "", "r": []}
        refuses("a boundary record of a fully hashed package refuses",
                lambda: check_fully_hashed(jrec, {"fully_hashed_packages": list(FULLY_HASHED)}))
        refuses("a fully hashed package with no hashed constant refuses",
                lambda: check_fully_hashed(records, {"fully_hashed_packages": list(FULLY_HASHED)}))

        old_head = json.loads((base / "header.json").read_text())
        (base / "header.json").write_text(json.dumps(dict(old_head, schema=SCHEMA - 1)))
        check("a schema move fails", any("schema moved" in l for l in compare(base, records, pins, digest, deps)[0]))
        (base / "header.json").write_text(json.dumps(old_head))

        lines = (base / "roots.tsv").read_text().splitlines()
        lines[0] = lines[0][:-1] + ("0" if lines[0][-1] != "0" else "1")
        (base / "roots.tsv").write_text("\n".join(lines) + "\n")
        check("a corrupted committed root fails", bool(compare(base, records, pins, digest, deps)[0]))

    if failures:
        print(f"FAIL — claim-hash self-test: {len(failures)} control(s) did not bite")
        return 1
    if not quiet:
        print("OK — claim-hash self-test: all controls bite")
    return 0


# ---------------------------------------------------------------- main


def generate(root: Path, work: Path, records_file: Path | None, fixture_file: Path | None) -> dict:
    expected = expected_pin_count(root)
    check_pin_binding(expected, regex_pin_count(root))
    deps = dependency_identities(root)
    result: dict = {"deps": deps, "lean_wall": None, "verified": records_file is None}
    if records_file is None:
        result["currency"], certificate = artifact_currency(root)
        result["currency_counts"] = check_fully_hashed_currency(certificate)
        result["packages"] = check_installed_packages(root)
        records_file = work / "records.jsonl"
        fixture_file = work / "fixture.jsonl"
        result["lean_wall"] = run_driver(root, records_file, fixture_file, work / "driver.log")
    records, pins, lean_stats = load_records(records_file)
    check_pin_binding(expected, len(pins), len(pins))
    if result["verified"]:
        check_lean_version(root, lean_stats.get("lean_version", "?"))
    if lean_stats.get("serializer_checks") != SERIALIZER_CHECKS:
        raise GateError(f"serializer checks: {lean_stats.get('serializer_checks')} ran, {SERIALIZER_CHECKS} expected")
    result["fixture_pairs"] = verify_fixture(fixture_file, deps)
    t0 = time.monotonic()
    digest, merkle_stats = merkle(records, deps)
    result["fully_hashed_counts"] = check_fully_hashed(records, lean_stats)
    result["real_controls"] = real_record_controls(records, pins, digest, deps, work)
    result.update(records=records, pins=pins, digest=digest, lean_stats=lean_stats,
                  merkle_stats=merkle_stats, merkle_wall=time.monotonic() - t0)
    return result


def report_stats(r: dict, total_wall: float) -> str:
    s, m, pins = r["lean_stats"], r["merkle_stats"], r["pins"]
    parts = [
        f"pins={len(pins)}",
        f"constants={s['constants']} (blanc={s['blanc']}, jaune={s['jaune']}, claimcheck-local={s['local']}, boundary={s['boundary']}, inductive-blocks={s['blocks']})",
        f"closure-walk visited-memo hits={s['visit_memo_hits']}",
        f"subterm memo hits={s['expr_memo_hits']}",
        f"digests computed={m['digests_computed']}, digest memo hits={m['memo_hits']}",
        f"serializer fixture pairs={r['fixture_pairs']}, serializer checks={s['serializer_checks']}",
        "certificate-checked fully hashed modules=" + ",".join(f"{k}:{v}" for k, v in r.get("currency_counts", {}).items()),
        "fully hashed=" + ",".join(f"{k}:{v}" for k, v in r["fully_hashed_counts"].items()),
        "real-record controls: " + "; ".join(f"{k} {v}" for k, v in r["real_controls"].items()),
        f"serialized={s['serialized_bytes']} bytes",
        f"elaboration={s['elab_ms'] / 1000:.1f}s walk={s['walk_ms'] / 1000:.1f}s"
        + (f" driver-wall={r['lean_wall']:.1f}s" if r["lean_wall"] is not None else "")
        + f" merkle={r['merkle_wall']:.1f}s total={total_wall:.1f}s",
        f"driver peak RSS={s.get('peak_rss_kib', 0) / 1048576:.2f} GiB",
    ]
    if r["lean_wall"] is not None:
        walk_only = s["walk_ms"] / 1000 + r["merkle_wall"]
        parts.append(f"cost per pin: {total_wall / len(pins) * 1000:.0f} ms all-in, "
                     f"{walk_only / len(pins) * 1000:.1f} ms beyond elaborating ClaimCheck")
    return "; ".join(parts)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--generate", type=Path, metavar="DIR")
    parser.add_argument("--records", type=Path, metavar="FILE")
    parser.add_argument("--fixture", type=Path, metavar="FILE")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--stats-json", type=Path, metavar="FILE")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    if (args.records is None) != (args.fixture is None) or (args.records and not args.generate):
        print("UNVERIFIED — claim closure hash: --records and --fixture go together and only with "
              "--generate; a supplied driver output is never compared", file=sys.stderr)
        return 2
    start = time.monotonic()
    # Every run first executes the in-memory controls, so a comparison that has
    # stopped biting cannot report a pass.
    if self_test(quiet=True) != 0:
        print("REGRESSION — claim closure hash: the in-memory controls did not bite")
        return 1
    try:
        with tempfile.TemporaryDirectory(prefix="claim-hash-", dir=os.environ.get("CLAIM_HASH_TMPDIR")) as tmp:
            work = Path(tmp)
            r = generate(ROOT, work, args.records, args.fixture)
            fresh = args.generate or (work / "fresh")
            write_manifest(fresh, r["records"], r["pins"], r["digest"], r["deps"])
            total = time.monotonic() - start
            summary = report_stats(r, total)
            if args.stats_json:
                args.stats_json.write_text(json.dumps({
                    "lean": r["lean_stats"], "merkle": r["merkle_stats"], "driver_wall_s": r["lean_wall"],
                    "merkle_wall_s": r["merkle_wall"], "total_wall_s": total}, indent=1) + "\n")
            if args.generate:
                if not r["verified"]:
                    print(f"UNVERIFIED — claim closure hash: manifest written to {args.generate} from "
                          f"supplied records; preconditions not checked; {summary}")
                    return 2
                print(f"GENERATED — claim closure hash: {args.generate}; artifacts: {r['currency']}; {summary}")
                return 0
            if not (MANIFEST_DIR / "roots.tsv").exists():
                print("REGRESSION — claim closure hash: no committed manifest in scripts/claim-pin-hash/")
                return 1
            report, notes = compare(MANIFEST_DIR, r["records"], r["pins"], r["digest"], r["deps"])
            for note in notes:
                print(f"note: {note}")
            if report:
                print("\n".join(report))
                print("REGRESSION — claim closure hash: the meaning of pinned claims moved; "
                      "review the constants above (refreshing the manifest is a reviewed decision)")
                return 1
            print(f"OK — claim closure hash: {len(r['pins'])} pin roots unchanged; "
                  f"artifacts: {r['currency']}; {r['packages']} Lake packages at their pinned revs; "
                  f"{summary}")
            return 0
    except GateError as error:
        print(f"REGRESSION — claim closure hash: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
