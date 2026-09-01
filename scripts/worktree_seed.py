#!/usr/bin/env python3
"""Preview and safely seed goal-local Lake state from an exact peer worktree."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import subprocess
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Callable


class SeedRefusal(RuntimeError):
    """A precondition or post-copy validation failed; no state was published."""


def load_gate_cache(script_dir: Path):
    path = script_dir / "gate-cache.py"
    spec = importlib.util.spec_from_file_location("blanc_gate_cache_for_seed", path)
    if spec is None or spec.loader is None:
        raise SeedRefusal(f"cannot load build-certificate authority: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments], cwd=root, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise SeedRefusal(
            f"git {' '.join(arguments)} failed in {root}: "
            f"{result.stderr.strip() or result.returncode}"
        )
    return result.stdout.strip()


def worktree_facts(root: Path) -> dict[str, str]:
    try:
        resolved = root.resolve(strict=True)
    except OSError as error:
        raise SeedRefusal(f"worktree is absent: {root}: {error}") from error
    top = Path(git(resolved, "rev-parse", "--show-toplevel")).resolve()
    if top != resolved:
        raise SeedRefusal(f"path must name a worktree root: {root}")
    common = Path(
        git(resolved, "rev-parse", "--path-format=absolute", "--git-common-dir")
    ).resolve()
    return {
        "root": str(resolved),
        "common": str(common),
        "head": git(resolved, "rev-parse", "HEAD"),
        "status": git(resolved, "status", "--porcelain"),
    }


def elab_baseline_identity(root: Path, path: Path, gate_cache) -> tuple[str, int, bytes]:
    """Validate an exact complete host-local elaboration baseline."""

    try:
        payload = path.read_bytes()
        text = payload.decode("utf-8")
    except (OSError, UnicodeError) as error:
        raise SeedRefusal(f"elaboration baseline is absent or unreadable: {path}: {error}") from error
    expected = [
        relative for relative in ("Blanc.lean", "Main.lean")
        if (root / relative).is_file()
    ]
    expected.extend(
        candidate.relative_to(root).as_posix()
        for candidate in sorted((root / "Blanc").rglob("*.lean"))
    )
    rows: dict[str, float] = {}
    for number, raw in enumerate(text.splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3 or fields[0] != "OK":
            raise SeedRefusal(f"malformed elaboration baseline row {number}: {path}")
        try:
            elapsed = float(fields[1])
        except ValueError as error:
            raise SeedRefusal(f"non-numeric elaboration baseline row {number}: {path}") from error
        relative = fields[2]
        if not math.isfinite(elapsed) or elapsed <= 0 or relative in rows:
            raise SeedRefusal(f"invalid elaboration baseline row {number}: {path}")
        rows[relative] = elapsed
    if set(rows) != set(expected):
        missing = sorted(set(expected) - set(rows))
        extra = sorted(set(rows) - set(expected))
        raise SeedRefusal(
            "elaboration baseline does not cover the exact Lean corpus "
            f"(missing={missing[:3]}, extra={extra[:3]})"
        )
    return gate_cache.sha256_bytes(payload), len(rows), payload


def default_copy(
    creme: Path, source: Path, destination: Path, execute: bool
) -> dict[str, Any]:
    command = [
        sys.executable,
        "-m",
        "creme",
        "cache-copy",
        str(source),
        str(destination),
    ]
    if execute:
        command.append("--execute")
    result = subprocess.run(
        command, cwd=creme, capture_output=True, text=True, check=False
    )
    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise SeedRefusal(
            f"Creme cache-copy returned no structured result: "
            f"{result.stderr.strip() or result.stdout.strip()}"
        ) from error
    if result.returncode != 0 or payload.get("status") not in {"OK", "PREVIEW"}:
        raise SeedRefusal(
            f"Creme cache-copy refused: {payload.get('status', result.returncode)} — "
            f"{payload.get('detail', result.stderr.strip())}"
        )
    return payload


def seed(
    source: Path,
    target: Path,
    creme: Path,
    execute: bool,
    *,
    copier: Callable[[Path, Path, Path, bool], dict[str, Any]] = default_copy,
) -> dict[str, Any]:
    source_facts = worktree_facts(source)
    target_facts = worktree_facts(target)
    source = Path(source_facts["root"])
    target = Path(target_facts["root"])

    if source == target:
        raise SeedRefusal("source and target must be distinct worktrees")
    if source_facts["common"] != target_facts["common"]:
        raise SeedRefusal("source and target are not worktrees of the same physical repository")
    if source_facts["head"] != target_facts["head"]:
        raise SeedRefusal("source and target do not have the exact same source base")
    if source_facts["status"] or target_facts["status"]:
        raise SeedRefusal("both source and target must be clean before Lake state is copied")
    source_lake = source / ".lake"
    target_lake = target / ".lake"
    if not source_lake.is_dir():
        raise SeedRefusal("source worktree has no Lake state")
    if target_lake.exists():
        raise SeedRefusal("target worktree already has .lake state")

    gate_cache = load_gate_cache(target / "scripts")
    baseline_digest, baseline_rows, baseline_payload = elab_baseline_identity(
        source, source / "scripts/baseline-elab.txt", gate_cache
    )
    target_baseline = target / "scripts/baseline-elab.txt"
    if target_baseline.exists():
        raise SeedRefusal("target worktree already has a host-local elaboration baseline")
    current, reason, source_certificate = gate_cache.build_certificate_status(source)
    if not current or source_certificate is None:
        raise SeedRefusal(f"source build state is not certifiable: {reason}")
    before_identity, _ = gate_cache.build_source_identity(source)

    if not execute:
        preview = copier(creme, source_lake, target_lake, False)
        return {
            "status": "PREVIEW",
            "detail": "exact peer worktree is eligible for an isolated Lake-state seed",
            "source": str(source),
            "target": str(target),
            "commit": source_facts["head"],
            "host": source_certificate["host"],
            "elab_baseline": {"digest": baseline_digest, "rows": baseline_rows},
            "copy": preview,
        }

    stage = target / f".lake.blanc-seed-{os.getpid()}-{uuid.uuid4().hex[:8]}"
    result = copier(creme, source_lake, stage, True)
    if result.get("status") != "OK" or not stage.is_dir():
        raise SeedRefusal(f"copy did not produce a complete staged directory: {stage}")

    # Reports and manifests describe the source candidate.  They are not build
    # state and must never appear as goal-local admissions in the new worktree.
    for relative in ("gate-report.md", "gate-manifest.json"):
        copied_admission = stage / relative
        if copied_admission.exists():
            copied_admission.unlink()
    staged_baseline = stage / "baseline-elab.txt"
    staged_baseline.write_bytes(baseline_payload)

    after_facts = worktree_facts(source)
    after_identity, _ = gate_cache.build_source_identity(source)
    if after_facts != source_facts or after_identity != before_identity:
        raise SeedRefusal(
            f"source moved during copy; staged state was retained for inspection: {stage}"
        )
    after_baseline_digest, after_baseline_rows, _ = elab_baseline_identity(
        source, source / "scripts/baseline-elab.txt", gate_cache
    )
    if (after_baseline_digest, after_baseline_rows) != (baseline_digest, baseline_rows):
        raise SeedRefusal(
            f"source elaboration baseline moved during copy; staged state was retained: {stage}"
        )
    source_current_after, source_reason_after, source_certificate_after = (
        gate_cache.build_certificate_status(source)
    )
    if not source_current_after or source_certificate_after != source_certificate:
        raise SeedRefusal(
            "source build state moved during copy "
            f"({source_reason_after}); staged state was retained for inspection: {stage}"
        )
    staged_current, staged_reason, staged_certificate = gate_cache.build_certificate_status(
        target, stage
    )
    if not staged_current or staged_certificate != source_certificate:
        raise SeedRefusal(
            f"staged state failed exact certificate validation ({staged_reason}); "
            f"it was retained for inspection: {stage}"
        )
    staged_baseline_digest, staged_baseline_rows, _ = elab_baseline_identity(
        target, staged_baseline, gate_cache
    )
    if (staged_baseline_digest, staged_baseline_rows) != (baseline_digest, baseline_rows):
        raise SeedRefusal(
            f"staged elaboration baseline failed exact validation; it was retained: {stage}"
        )
    if target_lake.exists():
        raise SeedRefusal(
            f"target .lake appeared during copy; staged state was retained: {stage}"
        )
    if target_baseline.exists():
        raise SeedRefusal(
            f"target elaboration baseline appeared during copy; staged state was retained: {stage}"
        )
    baseline_stage = target / "scripts" / (
        f".baseline-elab.blanc-seed-{os.getpid()}-{uuid.uuid4().hex[:8]}"
    )
    baseline_stage.parent.mkdir(parents=True, exist_ok=True)
    baseline_stage.write_bytes(baseline_payload)
    published_baseline_digest, published_baseline_rows, _ = elab_baseline_identity(
        target, baseline_stage, gate_cache
    )
    if (published_baseline_digest, published_baseline_rows) != (
        baseline_digest, baseline_rows
    ):
        raise SeedRefusal(
            f"candidate elaboration baseline failed exact validation: {baseline_stage}"
        )
    stage.rename(target_lake)
    baseline_stage.replace(target_baseline)
    gate_cache.atomic_json(
        target_lake / "blanc-seed-receipt.json",
        {
            "schema": 1,
            "source": str(source),
            "commit": source_facts["head"],
            "host": source_certificate["host"],
            "elab_baseline": {"digest": baseline_digest, "rows": baseline_rows},
            "method": (result.get("data") or {}).get("method", "unknown"),
            "recorded_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        },
    )
    return {
        "status": "OK",
        "detail": "isolated Lake state published after exact post-copy validation",
        "source": str(source),
        "target": str(target),
        "commit": source_facts["head"],
        "host": source_certificate["host"],
        "elab_baseline": {"digest": baseline_digest, "rows": baseline_rows},
        "method": (result.get("data") or {}).get("method", "unknown"),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--target", default=Path.cwd(), type=Path)
    parser.add_argument("--creme", default=Path.home() / "creme", type=Path)
    parser.add_argument("--execute", action="store_true")
    return parser


def main(argv: list[str]) -> int:
    arguments = build_parser().parse_args(argv)
    try:
        result = seed(
            arguments.source, arguments.target, arguments.creme, arguments.execute
        )
    except SeedRefusal as error:
        print(f"REFUSED — Blanc worktree seed: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
