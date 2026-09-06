#!/usr/bin/env python3
"""Replay every structurally verified DRIP fixture with the pinned Jaune runner.

No build, external runtime, command override, or fixture-writing mode exists.
Run under the host's registered contained workflow. The preceding build owns
binary freshness; this gate checks the package pin and records binary identity.
"""
from __future__ import annotations

import hashlib
import importlib.util
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "drip_replay_verifier", ROOT / "scripts/check-drip-fixtures.py")
assert SPEC and SPEC.loader
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)
ReplayError = VERIFIER.VerificationError


def require(value, message):
    VERIFIER.require(value, message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def population(directory):
    require(directory.is_dir(), "fixture directory missing")
    paths = sorted(directory.rglob("*.json"))
    require(paths, "fixture population empty")
    require(all(p.parent == directory and p.is_file() and not p.is_symlink()
                for p in paths), "fixture discovery: nested, symlink or non-file JSON")
    return {p.name: digest(p) for p in paths}


def pinned_runner():
    manifest = VERIFIER.read_json(ROOT / "lake-manifest.json")
    packages = [p for p in manifest["packages"] if p.get("name") == "jaune"]
    require(len(packages) == 1, "runner: missing/duplicate Jaune package")
    package = packages[0]
    pin = package.get("rev", "")
    require(package.get("type") == "git" and isinstance(pin, str)
            and re.fullmatch(r"[0-9a-f]{40}", pin), "runner: unsupported Jaune pin")
    directory = ROOT / ".lake/packages/jaune"
    require(not directory.is_symlink(), "runner: Jaune package is a symlink")
    runner = directory / ".lake/build/bin/jaune"
    require(runner.is_file() and not runner.is_symlink() and os.access(runner, os.X_OK),
            "runner: executable absent; build pinned jaune/jaune through the owned build capability")
    head = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                          check=True, capture_output=True, text=True).stdout.strip()
    require(head == pin, "runner: checkout differs from Lake Git pin")
    dirty = subprocess.run(["git", "-C", str(directory), "status", "--porcelain",
                            "--untracked-files=no"], check=True,
                           capture_output=True, text=True).stdout
    require(not dirty.strip(), "runner: tracked Jaune source is dirty")
    return runner, pin, digest(runner)


def replay(directory):
    directory = directory.absolute()
    initial = population(directory)
    count, steps = VERIFIER.verify(directory)
    manifest = VERIFIER.read_json(directory / "manifest.json")
    names = sorted(row["fixture"] for row in manifest["cases"])
    require(len(names) == count and len(set(names)) == count,
            "replay: duplicate or incomplete verified population")
    require(set(initial) == {"manifest.json", *names}, "replay: discovery mismatch")
    require(population(directory) == initial, "replay: fixture drift during verification")
    runner, pin, runner_hash = pinned_runner()
    print(f"DRIP replay identity: jaune={pin} binary-sha256={runner_hash}", flush=True)
    print(f"DRIP replay population: {count} fixtures, {steps} declared transactions", flush=True)
    for filename in names:
        require(population(directory) == initial, "replay: fixture drift before dispatch")
        path = directory / filename
        result = subprocess.run([str(runner), str(path), "--network", "BPO2"],
                                cwd=ROOT, capture_output=True, text=True, check=False)
        # Preserve complete runner diagnostics for each fixture in the gate log.
        print(result.stdout, end="", flush=True)
        print(result.stderr, end="", file=sys.stderr, flush=True)
        require(result.returncode == 0, f"{filename}: Jaune exit {result.returncode}")
        lines = result.stdout.splitlines()
        name = filename.removesuffix(".json")
        expected = f"TEST NAME : blanc/drip::{name}[fork_BPO2-blockchain_test]"
        require([x for x in lines if x.startswith("SELECTED CASES :")] == ["SELECTED CASES : 1"]
                and [x for x in lines if x.startswith("SKIPPED CASES :")] == ["SKIPPED CASES : 0"]
                and [x for x in lines if x.startswith("TEST NAME :")] == [expected],
                f"{filename}: Jaune case selection/verdict coverage differs")
        print(f"PASS — DRIP replay: {filename}; exit=0", flush=True)
    require(population(directory) == initial, "replay: fixture drift during execution")
    require(digest(runner) == runner_hash, "replay: runner binary drift during execution")
    print(f"OK — DRIP replay: {count}/{count} fixtures PASS, network BPO2", flush=True)
    return count, steps


def main(argv):
    if argv:
        print("usage: check-drip-replay.py (no arguments)", file=sys.stderr)
        return 2
    try:
        replay(ROOT / "scripts/fixtures/drip")
    except (ReplayError, OSError, ValueError, KeyError, TypeError,
            subprocess.SubprocessError) as exc:
        print(f"REGRESSION — DRIP replay: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
