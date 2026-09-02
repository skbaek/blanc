#!/usr/bin/env python3
"""Collect Lake cache entries unreferenced by any live Blanc worktree trace.

The default is a non-mutating dry run. Execution must be externally serialized
against every Lake process with Creme's exclusive semaphore; the explicit
acknowledgement flag makes that obligation visible at the command boundary.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ARTIFACT_RE = re.compile(r"^[0-9a-f]{16}(?:\.[A-Za-z0-9._-]+)?$")
HASH_RE = re.compile(r"^[0-9a-f]{16}$")
DECIMAL_HASH_RE = re.compile(r"^[0-9]{1,20}$")
OUTPUT_RE = re.compile(r"^[0-9a-f]{16}\.json$")
CACHE_TRUE_RE = re.compile(r"(?m)^\s*(enableArtifactCache|restoreAllArtifacts)\s*:=\s*true\s*$")


class Refusal(RuntimeError):
    """A fail-closed collection refusal."""


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise Refusal(f"command failed ({' '.join(command)}): {detail}")
    return result.stdout


def live_worktrees(repository: Path) -> list[Path]:
    output = run(["git", "worktree", "list", "--porcelain"], repository)
    paths: list[Path] = []
    for record in output.strip().split("\n\n"):
        lines = record.splitlines()
        worktree = next((line[9:] for line in lines if line.startswith("worktree ")), None)
        prunable = any(line.startswith("prunable") for line in lines)
        if worktree and not prunable:
            path = Path(worktree)
            if path.is_dir():
                paths.append(path.resolve())
    if not paths:
        raise Refusal("git reported no existing, non-prunable worktrees")
    return sorted(set(paths))


def artifact_names(value: object) -> set[str]:
    names: set[str] = set()
    if isinstance(value, str):
        if ARTIFACT_RE.fullmatch(value):
            names.add(value)
        elif HASH_RE.fullmatch(value):
            # Lake records a raw output hash for non-cacheable targets such as
            # linked executables. It names no file in cache/artifacts.
            pass
        else:
            raise Refusal(f"unrecognized artifact reference in trace: {value!r}")
    elif isinstance(value, list):
        for item in value:
            names.update(artifact_names(item))
    elif isinstance(value, dict):
        for item in value.values():
            names.update(artifact_names(item))
    elif value is not None and not isinstance(value, bool):
        raise Refusal(f"unrecognized artifact reference value: {value!r}")
    return names


def cache_participants(worktrees: list[Path]) -> tuple[list[Path], list[Path]]:
    participants: list[Path] = []
    nonparticipants: list[Path] = []
    for worktree in worktrees:
        lakefile = worktree / "lakefile.lean"
        try:
            text = lakefile.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise Refusal(f"cannot inspect cache configuration {lakefile}: {error}") from error
        enabled = set(CACHE_TRUE_RE.findall(text))
        if enabled == {"enableArtifactCache", "restoreAllArtifacts"}:
            participants.append(worktree)
        else:
            nonparticipants.append(worktree)
    return participants, nonparticipants


def normalize_hash(value: object, source: Path) -> str:
    if not isinstance(value, str):
        raise Refusal(f"invalid Lake hash in {source}: {value!r}")
    if HASH_RE.fullmatch(value):
        return value
    if DECIMAL_HASH_RE.fullmatch(value):
        number = int(value)
        if number <= (1 << 64) - 1:
            return f"{number:016x}"
    raise Refusal(f"invalid Lake hash in {source}: {value!r}")


def trace_references(worktrees: list[Path]) -> tuple[set[str], set[str], set[str], int]:
    artifacts: set[str] = set()
    materialized_hashes: set[str] = set()
    dep_hashes: set[str] = set()
    trace_count = 0
    for worktree in worktrees:
        lake = worktree / ".lake"
        if not lake.is_dir():
            continue
        build_roots = sorted(
            path for path in lake.rglob("build")
            if path.parent.name == ".lake" and path.is_dir()
        )
        for build_root in build_roots:
            if build_root.is_symlink():
                raise Refusal(f"Lake build root is a symlink: {build_root}")
            for trace in sorted(build_root.rglob("*.trace")):
                if trace.is_symlink() or not trace.is_file():
                    raise Refusal(f"trace is not a regular file: {trace}")
                try:
                    payload = json.loads(trace.read_text(encoding="utf-8"))
                except (OSError, UnicodeError, json.JSONDecodeError) as error:
                    raise Refusal(f"cannot parse trace {trace}: {error}") from error
                if not isinstance(payload, dict):
                    raise Refusal(f"trace is not an object: {trace}")
                raw_dep_hash = payload.get("depHash")
                dep_hash = normalize_hash(raw_dep_hash, trace)
                if isinstance(raw_dep_hash, str) and HASH_RE.fullmatch(raw_dep_hash):
                    if "outputs" not in payload:
                        raise Refusal(f"cache-era trace lacks outputs: {trace}")
                    artifacts.update(artifact_names(payload["outputs"]))
                elif not isinstance(raw_dep_hash, str) or not DECIMAL_HASH_RE.fullmatch(
                    raw_dep_hash
                ) or "log" not in payload or not set(payload) <= {
                    "synthetic", "outputs", "log", "inputs", "depHash"
                }:
                    raise Refusal(f"unrecognized trace without outputs: {trace}")
                dep_hashes.add(dep_hash)
                trace_count += 1
            for sidecar in sorted(build_root.rglob("*.hash")):
                if sidecar.is_symlink() or not sidecar.is_file():
                    raise Refusal(f"output hash sidecar is not a regular file: {sidecar}")
                try:
                    value = sidecar.read_text(encoding="utf-8").strip()
                except (OSError, UnicodeError) as error:
                    raise Refusal(f"cannot read output hash sidecar {sidecar}: {error}") from error
                materialized_hashes.add(normalize_hash(value, sidecar))
    return artifacts, materialized_hashes, dep_hashes, trace_count


def regular_files(directory: Path, pattern: re.Pattern[str], recursive: bool) -> list[Path]:
    iterator = directory.rglob("*") if recursive else directory.iterdir()
    files: list[Path] = []
    for path in iterator:
        if path.is_symlink():
            raise Refusal(f"cache entry is a symlink: {path}")
        if path.is_file():
            if not pattern.fullmatch(path.name):
                raise Refusal(f"unrecognized cache entry: {path}")
            files.append(path)
    return sorted(files)


def collect(cache: Path, worktrees: list[Path], execute: bool) -> dict[str, object]:
    cache = cache.resolve(strict=True)
    artifacts_dir = cache / "artifacts"
    outputs_dir = cache / "outputs"
    if cache.is_symlink() or not artifacts_dir.is_dir() or not outputs_dir.is_dir():
        raise Refusal(f"cache layout is missing or unsafe: {cache}")
    participants, nonparticipants = cache_participants(worktrees)
    if not participants:
        raise Refusal("no live worktree enables both artifact-cache settings")
    (
        referenced_artifacts,
        materialized_hashes,
        referenced_dep_hashes,
        trace_count,
    ) = trace_references(participants)
    cache_artifacts = regular_files(artifacts_dir, ARTIFACT_RE, recursive=False)
    cache_outputs = regular_files(outputs_dir, OUTPUT_RE, recursive=True)
    orphan_artifacts = [
        path for path in cache_artifacts
        if path.name not in referenced_artifacts
        and path.name.split(".", 1)[0] not in materialized_hashes
    ]
    orphan_outputs = [path for path in cache_outputs if path.stem not in referenced_dep_hashes]
    candidates = orphan_artifacts + orphan_outputs
    candidate_bytes = sum(path.stat().st_size for path in candidates)
    if execute:
        for path in candidates:
            path.unlink()
    return {
        "schema": 1,
        "mode": "execute" if execute else "dry-run",
        "cache": str(cache),
        "worktrees": [str(path) for path in worktrees],
        "cache_participants": [str(path) for path in participants],
        "nonparticipants": [str(path) for path in nonparticipants],
        "trace_count": trace_count,
        "referenced_artifact_count": len(referenced_artifacts),
        "materialized_hash_count": len(materialized_hashes),
        "referenced_dep_hash_count": len(referenced_dep_hashes),
        "cache_artifact_count": len(cache_artifacts),
        "cache_output_count": len(cache_outputs),
        "orphan_artifact_count": len(orphan_artifacts),
        "orphan_output_count": len(orphan_outputs),
        "candidate_bytes": candidate_bytes,
        "removed_count": len(candidates) if execute else 0,
        "candidates": [str(path.relative_to(cache)) for path in candidates],
    }


def default_cache(repository: Path) -> Path:
    printenv = shutil.which("printenv")
    if printenv is None:
        raise Refusal("printenv is unavailable; pass --cache explicitly")
    value = run(["lake", "env", printenv, "LAKE_CACHE_DIR"], repository).strip()
    if not value:
        raise Refusal("lake env did not report LAKE_CACHE_DIR")
    return Path(value)


def self_test() -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="blanc-cache-gc-") as temporary:
        root = Path(temporary)
        cache = root / "cache"
        artifacts = cache / "artifacts"
        outputs = cache / "outputs" / "blanc"
        worktree = root / "worktree"
        traces = worktree / ".lake" / "build"
        artifacts.mkdir(parents=True)
        outputs.mkdir(parents=True)
        traces.mkdir(parents=True)
        (worktree / "lakefile.lean").write_text(
            "package fixture where\n"
            "  enableArtifactCache := true\n"
            "  restoreAllArtifacts := true\n",
            encoding="utf-8",
        )
        kept_artifact = artifacts / "aaaaaaaaaaaaaaaa.olean"
        orphan_artifact = artifacts / "bbbbbbbbbbbbbbbb.olean"
        kept_output = outputs / "1111111111111111.json"
        orphan_output = outputs / "2222222222222222.json"
        for path in (kept_artifact, orphan_artifact, kept_output, orphan_output):
            path.write_text(path.name + "\n", encoding="utf-8")
        (traces / "materialized.olean.hash").write_text(
            kept_artifact.name.split(".", 1)[0] + "\n",
            encoding="utf-8",
        )
        trace = traces / "Live.trace"
        trace.write_text(json.dumps({
            "outputs": {
                "o": [kept_artifact.name],
                "m": False,
                "linked": "dddddddddddddddd",
            },
            "depHash": kept_output.stem,
        }), encoding="utf-8")

        dry_run = collect(cache, [worktree], execute=False)
        if not all(path.exists() for path in (kept_artifact, orphan_artifact, kept_output, orphan_output)):
            raise AssertionError("dry-run mutated its fixture")
        execution = collect(cache, [worktree], execute=True)
        if not kept_artifact.exists() or not kept_output.exists():
            raise AssertionError("collector removed a referenced entry")
        if orphan_artifact.exists() or orphan_output.exists():
            raise AssertionError("collector retained a deliberate orphan")

        refused_orphan = artifacts / "cccccccccccccccc.olean"
        refused_orphan.write_text("must survive refusal\n", encoding="utf-8")
        trace.write_text("{malformed", encoding="utf-8")
        refused = False
        try:
            collect(cache, [worktree], execute=True)
        except Refusal:
            refused = True
        if not refused or not refused_orphan.exists():
            raise AssertionError("malformed-trace refusal was not fail-closed")
        return {"schema": 1, "status": "OK", "dry_run": dry_run, "execution": execution}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--ack-exclusive-semaphore", action="store_true")
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--report", type=Path)
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    try:
        if arguments.self_test:
            result = self_test()
        else:
            repository = arguments.repository.resolve(strict=True)
            if arguments.execute and not arguments.ack_exclusive_semaphore:
                raise Refusal("--execute requires --ack-exclusive-semaphore")
            cache = arguments.cache or default_cache(repository)
            cache = cache.expanduser()
            worktrees = live_worktrees(repository)
            if arguments.execute:
                lock_path = cache / ".blanc-gc.lock"
                with lock_path.open("a+", encoding="utf-8") as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    result = collect(cache, worktrees, execute=True)
            else:
                result = collect(cache, worktrees, execute=False)
        rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if arguments.report:
            report = arguments.report.resolve()
            report.parent.mkdir(parents=True, exist_ok=True)
            report.write_text(rendered, encoding="utf-8")
        print(rendered, end="")
        return 0
    except (OSError, Refusal, subprocess.SubprocessError) as error:
        print(json.dumps({"schema": 1, "status": "REFUSED", "reason": str(error)}, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
