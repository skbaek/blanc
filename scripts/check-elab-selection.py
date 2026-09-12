#!/usr/bin/env python3
"""Content-based invalidation for Blanc's per-module elaboration gate.

The timing gate intentionally invokes Lean once per selected source file.  This
helper decides which invocations are necessary.  A module's fingerprint covers
its own source, every transitive repository-local import, shared Lean/Lake
configuration, and Lake's own transitive imported-artifact dependency hash. A
cached successful measurement is reusable exactly when that fingerprint is
unchanged.

The cache is local build state under ``.lake``.  Missing, corrupt, or
incompatible state fails open to a full measurement; it can never cause a file
to be skipped. State is replaced atomically with successful, non-drifting
measurements only; a failing file is excluded so the next run retries it rather
than discarding independent green evidence.

The same module owns the calibration sampler.  Deciding *which* modules can
have moved is the fingerprint's job and is exact; deciding whether the host is
behaving normally while they are measured is a separate, statistical question,
and a seeded stratified sample of provably-unaffected modules answers it.

The same module also owns the shared same-host timing evidence below the
repository's Git common directory.  A new worktree must not repeat timing
solely because its worktree-local state is empty, so green runs publish their
per-module measurements keyed by the exact fingerprints above, and clean-tree
genesis/rebase runs publish their whole baseline document with its origin
commit.  A baseline-less worktree adopts a stored document only when that
origin predates the changes under test, and any module credits a stored
measurement only on exact environment/fingerprint/host match.  Every shared
failure costs measurement, never a credit.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Iterable


STATE_VERSION = 1
ROOT_MODULES = ("Blanc.lean", "Main.lean")
GLOBAL_INPUTS = (
    "lean-toolchain",
    "lakefile.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "scripts/check-elab.sh",
    "scripts/check-elab-selection.py",
)
IMPORT_LINE = re.compile(
    r"^(?:public[ \t]+)?import[ \t]+"
    r"([A-Za-z0-9_'.]+(?:[ \t]+[A-Za-z0-9_'.]+)*)[ \t]*$"
)


# --- calibration sampling ---------------------------------------------------
# The gate does two different jobs, and only one of them needs the whole tree.
# Regression detection is exact and already selective: the fingerprint above
# decides which modules *can* have moved. Calibration answers a different
# question — "is this host behaving normally right now" — which is a property
# of the environment, not of any particular module, and a sample answers it.
#
# The draw is pseudo-random with the seed derived from the candidate commit, so
# it is reproducible by anyone holding that commit, carries no design-time
# cherry-picking, ages with the library, and cannot be re-rolled without
# changing what is being measured.
CALIBRATION_DOMAIN = "blanc-elab-calibration-v1"

# (low, high, draw). `high` None means open. Boundaries are fixed; membership is
# recomputed from the current baseline every run, so the bands age with the
# library. Stratified rather than uniform because cost is heavily skewed: a
# uniform draw would almost never reach the expensive tail, which is where
# sustained throughput and thermal anomalies show. Two from the tail rather than
# one so that band can cross-check itself — with a single tail sample a deviant
# reading cannot be told apart from that one file being noisy.
CALIBRATION_BANDS = (
    (0.0, 1.5, 4),
    (1.5, 3.0, 4),
    (3.0, 10.0, 2),
    (10.0, None, 2),
)


class SelectionError(RuntimeError):
    """An import graph or cache operation is not safe to continue."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def discover_files(root: Path) -> list[str]:
    files = [name for name in ROOT_MODULES if (root / name).is_file()]
    source = root / "Blanc"
    if source.is_dir():
        files.extend(
            path.relative_to(root).as_posix()
            for path in source.rglob("*.lean")
            if path.is_file()
        )
    files = sorted(set(files))
    if not files:
        raise SelectionError(f"no Lean source files found under {root}")
    return files


def module_name(path: str) -> str:
    if path == "Blanc.lean":
        return "Blanc"
    if path == "Main.lean":
        return "Main"
    if path.startswith("Blanc/") and path.endswith(".lean"):
        return path[: -len(".lean")].replace("/", ".")
    raise SelectionError(f"cannot derive a module name from local source {path!r}")


def without_comments_and_strings(text: str) -> str:
    """Blank comments and strings while preserving newlines and line structure.

    Lean block comments nest.  Import commands cannot contain strings, so
    blanking strings also prevents an ``import``-shaped line inside a multiline
    string from becoming a false dependency.
    """

    out: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                out.append(char)
            else:
                out.append(" ")
            index += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            if char == "\n":
                out.append(char)
            else:
                out.append(" ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            in_line_comment = True
            out.extend("  ")
            index += 2
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1

    if block_depth:
        raise SelectionError("unterminated Lean block comment while reading imports")
    if in_string:
        raise SelectionError("unterminated Lean string while reading imports")
    return "".join(out)


def imports_in(path: Path) -> list[str]:
    cleaned = without_comments_and_strings(path.read_text(encoding="utf-8"))
    imports: list[str] = []
    for number, raw in enumerate(cleaned.splitlines(), start=1):
        line = raw.strip()
        if not line:
            continue
        looks_like_import = line.startswith("import ") or line.startswith("public import ")
        match = IMPORT_LINE.fullmatch(line)
        if looks_like_import and match is None:
            raise SelectionError(
                f"unsupported import syntax at {path}:{number}: {line!r}"
            )
        if match:
            imports.extend(match.group(1).split())
    return imports


def import_graph(root: Path, files: Iterable[str]) -> tuple[dict[str, str], dict[str, list[str]]]:
    module_to_path: dict[str, str] = {}
    for path in files:
        module = module_name(path)
        if module in module_to_path:
            raise SelectionError(
                f"duplicate local module {module}: {module_to_path[module]} and {path}"
            )
        module_to_path[module] = path

    graph: dict[str, list[str]] = {}
    for module, relative in sorted(module_to_path.items()):
        local: set[str] = set()
        for imported in imports_in(root / relative):
            if imported in module_to_path:
                local.add(imported)
            elif imported == "Blanc" or imported.startswith("Blanc."):
                raise SelectionError(
                    f"{relative} imports missing local module {imported}"
                )
        graph[module] = sorted(local)
    return module_to_path, graph


def lake_trace_hashes(root: Path, module_to_path: dict[str, str]) -> dict[str, str]:
    """Read Lake's authoritative elaboration dependency hash for each module.

    ``lake build <every local module>`` runs before selection.  Its trace hash
    covers the source, Lean version/options, and transitive imported artifacts,
    including external packages.  Missing or malformed traces therefore mean
    the build precondition was not met; guessing would make skipping unsound.
    """

    hashes: dict[str, str] = {}
    trace_root = root / ".lake/build/lib/lean"
    for module in sorted(module_to_path):
        trace_path = trace_root / (module.replace(".", "/") + ".trace")
        try:
            trace = json.loads(trace_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            raise SelectionError(
                f"missing or unreadable Lake trace for {module}: {trace_path}"
            ) from error
        dep_hash = trace.get("depHash") if isinstance(trace, dict) else None
        if not isinstance(dep_hash, str) or not dep_hash:
            raise SelectionError(f"Lake trace for {module} has no dependency hash")
        hashes[module] = dep_hash
    return hashes


def environment_fingerprint(root: Path, environment_id: str) -> str:
    digest = hashlib.sha256()
    digest.update(f"blanc-elab-state-v{STATE_VERSION}\0".encode())
    digest.update(environment_id.encode("utf-8"))
    digest.update(b"\0")
    for relative in GLOBAL_INPUTS:
        path = root / relative
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        if path.is_file():
            digest.update(path.read_bytes())
        else:
            digest.update(b"<absent>")
        digest.update(b"\0")
    return digest.hexdigest()


def module_fingerprints(
    root: Path,
    module_to_path: dict[str, str],
    graph: dict[str, list[str]],
    environment: str,
    trace_hashes: dict[str, str] | None = None,
) -> dict[str, str]:
    fingerprints: dict[str, str] = {}
    visiting: list[str] = []

    def visit(module: str) -> str:
        if module in fingerprints:
            return fingerprints[module]
        if module in visiting:
            cycle = " -> ".join(visiting[visiting.index(module) :] + [module])
            raise SelectionError(f"local import cycle: {cycle}")
        visiting.append(module)
        relative = module_to_path[module]
        digest = hashlib.sha256()
        digest.update(environment.encode("ascii"))
        digest.update(b"\0module\0")
        digest.update(module.encode("utf-8"))
        digest.update(b"\0source\0")
        digest.update((root / relative).read_bytes())
        if trace_hashes is not None:
            digest.update(b"\0lake-trace\0")
            digest.update(trace_hashes[module].encode("utf-8"))
        for imported in graph[module]:
            digest.update(b"\0import\0")
            digest.update(imported.encode("utf-8"))
            digest.update(b"\0")
            digest.update(visit(imported).encode("ascii"))
        visiting.pop()
        fingerprints[module] = digest.hexdigest()
        return fingerprints[module]

    for module in sorted(module_to_path):
        visit(module)
    return {
        path: fingerprints[module]
        for module, path in sorted(module_to_path.items(), key=lambda item: item[1])
    }


def valid_time(value: Any) -> bool:
    try:
        number = float(value)
    except (TypeError, ValueError):
        return False
    return math.isfinite(number) and number >= 0


def read_state(path: Path) -> tuple[dict[str, Any] | None, str | None]:
    if not path.is_file():
        return None, "no prior cache"
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(state, dict) or state.get("version") != STATE_VERSION:
            return None, "cache version missing or incompatible"
        if not isinstance(state.get("environment"), str):
            return None, "cache environment is invalid"
        entries = state.get("files")
        if not isinstance(entries, dict):
            return None, "cache file table is invalid"
        for relative, entry in entries.items():
            if (
                not isinstance(relative, str)
                or not isinstance(entry, dict)
                or not isinstance(entry.get("fingerprint"), str)
                or entry.get("status") != "OK"
                or not valid_time(entry.get("time"))
            ):
                return None, "cache contains an invalid file entry"
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None, "cache is unreadable or corrupt"
    return state, None



def read_baseline(path: Path) -> dict[str, float]:
    """Parse the host-local baseline into path -> seconds.

    The baseline is a provenance ledger with rows embedded: comment blocks sit
    between row groups, not only at the top, so comments are skipped wherever
    they appear — the same rule the shell gate applies.
    """
    if not path.is_file():
        raise SelectionError(f"baseline not found: {path}")
    times: dict[str, float] = {}
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) < 3:
            raise SelectionError(f"invalid baseline row {path}:{number}")
        status, elapsed, relative = fields[0], fields[1], fields[2]
        if status not in {"OK", "ERROR"} or not valid_time(elapsed):
            raise SelectionError(f"invalid baseline status/time at {path}:{number}")
        if relative in times:
            raise SelectionError(f"duplicate baseline row for {relative} at {path}:{number}")
        times[relative] = float(elapsed)
    if not times:
        raise SelectionError(f"baseline carries no rows: {path}")
    return times


def file_digest(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def source_set_digest(root: Path, files: Iterable[str]) -> str:
    """Digest every discovered source file, path and content together.

    The draw depends on the source set and on the baseline, not on the commit
    alone. Recording both digests is what lets a reviewer recompute the draw
    even when the measured tree was not exactly the seeding commit.
    """
    hasher = hashlib.sha256()
    for relative in files:
        hasher.update(relative.encode("utf-8"))
        hasher.update(b"\0")
        hasher.update(file_digest(root / relative).encode("ascii"))
        hasher.update(b"\n")
    return hasher.hexdigest()


def calibration_seed(commit: str) -> str:
    """Derive the draw's seed from the candidate commit.

    Domain-separated so the seed cannot collide with any other hash this gate
    computes, and so a future sampler revision can change the draw deliberately
    by changing the domain rather than silently by changing the algorithm.
    """
    if not commit:
        raise SelectionError("calibration needs a candidate commit to seed the draw")
    return sha256_bytes(f"{CALIBRATION_DOMAIN}|{commit}".encode("utf-8"))


def draw_calibration(
    baseline: dict[str, float],
    population: Iterable[str],
    commit: str,
    baseline_digest: str,
    source_digest: str,
) -> dict[str, Any]:
    """Draw the seeded stratified control sample.

    Within a band the candidates are ordered by sha256(seed|path) and the first
    k taken. Ordering rather than rejection sampling keeps the draw stable as
    the library grows: a new module inserts into that order and displaces at
    most one control, instead of reshuffling the whole band.
    """
    seed = calibration_seed(commit)
    members = sorted(population)
    bands: list[dict[str, Any]] = []
    selected: list[str] = []
    short: list[str] = []
    for low, high, want in CALIBRATION_BANDS:
        in_band = [
            relative
            for relative in members
            if baseline[relative] >= low and (high is None or baseline[relative] < high)
        ]
        ordered = sorted(
            in_band, key=lambda p: sha256_bytes(f"{seed}|{p}".encode("utf-8"))
        )
        take = sorted(ordered[:want])
        label = f"[{low:g}, {'inf' if high is None else format(high, 'g')})"
        if len(take) < want:
            short.append(label)
        bands.append(
            {
                "label": label,
                "low": low,
                "high": high,
                "want": want,
                "population": len(in_band),
                "selected": take,
            }
        )
        selected.extend(take)
    return {
        "domain": CALIBRATION_DOMAIN,
        "commit": commit,
        "seed": seed,
        # Required arguments, not defaulted keys: the block prints these as the
        # reviewer's means of recomputing the draw, so an absent digest must be
        # impossible to construct rather than silently rendered empty.
        "baseline_digest": baseline_digest,
        "source_digest": source_digest,
        "compared": [],
        "baseline_rows": len(baseline),
        "population": len(members),
        "bands": bands,
        "selected": sorted(selected),
        "short_bands": short,
        "candidates": [],
    }


def make_plan(
    root: Path,
    state_path: Path,
    environment_id: str,
    force_full: bool = False,
    full_reason: str = "explicit --full",
    require_lake_traces: bool = False,
    baseline_path: Path | None = None,
    calibration_commit: str | None = None,
) -> dict[str, Any]:
    root = root.resolve()
    files = discover_files(root)
    module_to_path, graph = import_graph(root, files)
    environment = environment_fingerprint(root, environment_id)
    trace_hashes = lake_trace_hashes(root, module_to_path) if require_lake_traces else None
    fingerprints = module_fingerprints(
        root, module_to_path, graph, environment, trace_hashes
    )
    state, state_error = read_state(state_path)

    cached: dict[str, dict[str, str]] = {}
    reason: str | None = None
    if force_full:
        reason = full_reason
    elif state_error:
        reason = state_error
    elif state is not None and state["environment"] != environment:
        reason = "shared Lean/Lake environment changed"

    affected: list[str] = []
    if reason is not None:
        affected = files
    else:
        assert state is not None
        for relative in files:
            entry = state["files"].get(relative)
            if entry is not None and entry["fingerprint"] == fingerprints[relative]:
                cached[relative] = {"status": "OK", "time": str(entry["time"])}
            else:
                affected.append(relative)

    # A local miss consults the shared same-host evidence: an exact
    # (environment, fingerprint) match credits the stored measurement.  An
    # explicit --full still measures everything -- it asks for fresh evidence.
    # Any shared failure leaves the module affected; it never breaks planning.
    shared_credited: list[str] = []
    shared_reason: str | None = None
    if not force_full:
        try:
            shared_path = shared_store_path(root)
            shared_host = load_shared_host_identity()
            shared_store, shared_error, _ = read_shared_store(
                shared_path, shared_host
            )
            if shared_error is not None:
                shared_reason = shared_error
            else:
                shared_table = lookup_shared_measurements(shared_store, environment)
                for relative in files:
                    if relative in cached:
                        continue
                    moment = shared_table.get(fingerprints[relative])
                    if moment is not None:
                        cached[relative] = {"status": "OK", "time": moment}
                        shared_credited.append(relative)
                affected = [relative for relative in files if relative not in cached]
        except SelectionError as error:
            shared_reason = str(error)
        except Exception as error:  # shared evidence must never break planning
            shared_reason = f"shared evidence unavailable: {error}"

    calibration: dict[str, Any] | None = None
    if calibration_commit is not None:
        if baseline_path is None:
            raise SelectionError("calibration needs the host-local baseline")
        baseline = read_baseline(baseline_path)
        # `affected` may alias `files` on a full run; never append through it.
        affected = list(affected)
        # A module with no local row is the measurement, not a control, so
        # it is measured whatever the cache believes about it.
        mandatory = [relative for relative in files if relative not in baseline]
        for relative in mandatory:
            if relative not in affected:
                affected.append(relative)
            cached.pop(relative, None)
        # Drawable means the fingerprint proves this file cannot have moved.
        # That is exactly the set this run is not measuring, which is why a
        # calibration run may not write to the cache: caching the module it just
        # measured would make that module drawable next time, so a retry of a
        # refused calibration would not agree on what it measured and the
        # refusal could be retried away. See commit_state's refusal.
        drawable = set(cached)
        calibration = draw_calibration(
            baseline,
            [
                relative
                for relative in files
                if relative in baseline and relative in drawable
            ],
            calibration_commit,
            file_digest(baseline_path),
            source_set_digest(root, files),
        )
        calibration["candidates"] = sorted(mandatory)
        # Rows this run measures and compares outright rather than drawing.
        # Recording them is what makes the drawable population checkable: a
        # reviewer can recompute the draw only if it is known what was held out
        # of it, and why.
        calibration["compared"] = sorted(
            relative
            for relative in affected
            if relative in baseline
        )
        for relative in calibration["selected"]:
            if relative not in affected:
                affected.append(relative)
            cached.pop(relative, None)
        affected.sort()

    return {
        "version": STATE_VERSION,
        "root": str(root),
        "environment": environment,
        "environment_id": environment_id,
        "uses_lake_traces": require_lake_traces,
        "files": files,
        "fingerprints": fingerprints,
        "affected": affected,
        "cached": cached,
        "reason": reason,
        "calibration": calibration,
        "shared_credited": sorted(shared_credited),
        "shared_reason": shared_reason,
    }


def atomic_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.", delete=False
    )
    temporary = Path(handle.name)
    try:
        with handle:
            json.dump(value, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def write_plan(path: Path, plan: dict[str, Any]) -> None:
    atomic_json(path, plan)


def read_plan(path: Path) -> dict[str, Any]:
    try:
        plan = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise SelectionError(f"cannot read selection plan {path}: {error}") from error
    required = {
        "version",
        "root",
        "environment",
        "environment_id",
        "uses_lake_traces",
        "files",
        "fingerprints",
        "affected",
        "cached",
    }
    if not isinstance(plan, dict) or plan.get("version") != STATE_VERSION or not required <= plan.keys():
        raise SelectionError(f"invalid selection plan {path}")
    return plan


def read_result_rows(path: Path) -> dict[str, dict[str, str]]:
    rows: dict[str, dict[str, str]] = {}
    if not path.is_file():
        raise SelectionError(f"result file not found: {path}")
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw:
            continue
        fields = raw.split("\t")
        if len(fields) < 3 or len(fields) > 4:
            raise SelectionError(f"invalid result row {path}:{number}")
        status, elapsed, relative = fields[:3]
        provenance = fields[3] if len(fields) == 4 else "MEASURED"
        if status not in {"OK", "ERROR"} or not valid_time(elapsed):
            raise SelectionError(f"invalid status/time at {path}:{number}")
        if provenance not in {"MEASURED", "CACHED"}:
            raise SelectionError(f"invalid result provenance at {path}:{number}")
        if relative in rows:
            raise SelectionError(f"duplicate result for {relative} at {path}:{number}")
        rows[relative] = {
            "status": status,
            "time": elapsed,
            "provenance": provenance,
        }
    return rows


def merge_results(plan: dict[str, Any], measured_path: Path, report_path: Path) -> None:
    measured = read_result_rows(measured_path)
    affected = set(plan["affected"])
    if set(measured) != affected:
        missing = sorted(affected - set(measured))
        extra = sorted(set(measured) - affected)
        raise SelectionError(f"measured-result set mismatch; missing={missing}, extra={extra}")

    lines: list[str] = []
    for relative in plan["files"]:
        if relative in measured:
            row = measured[relative]
            lines.append(
                f"{row['status']}\t{row['time']}\t{relative}\tMEASURED"
            )
        else:
            cached = plan["cached"].get(relative)
            if cached is None:
                raise SelectionError(f"no measured or cached result for {relative}")
            lines.append(f"OK\t{cached['time']}\t{relative}\tCACHED")
    report_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def validate_results(
    plan: dict[str, Any],
    report_path: Path,
    excluded: set[str] | None = None,
) -> dict[str, dict[str, str]]:
    excluded = excluded or set()
    rows = read_result_rows(report_path)
    files = set(plan["files"])
    if set(rows) != files:
        raise SelectionError("complete result set does not match the current Lean source set")
    if not excluded <= files:
        raise SelectionError(f"result exclusion names unknown files: {sorted(excluded - files)}")
    if any(
        row["status"] != "OK" and relative not in excluded
        for relative, row in rows.items()
    ):
        raise SelectionError("refusing a result set containing unexcluded elaboration errors")

    # Do not attach measurements to stale fingerprints if an editor changed a
    # source or configuration file while the sequential gate was running.
    root = Path(plan["root"])
    current_files = discover_files(root)
    module_to_path, graph = import_graph(root, current_files)
    current_environment = environment_fingerprint(root, plan["environment_id"])
    trace_hashes = (
        lake_trace_hashes(root, module_to_path)
        if plan["uses_lake_traces"]
        else None
    )
    current_fingerprints = module_fingerprints(
        root, module_to_path, graph, current_environment, trace_hashes
    )
    if (
        current_files != plan["files"]
        or current_environment != plan["environment"]
        or current_fingerprints != plan["fingerprints"]
    ):
        raise SelectionError(
            "Lean sources or shared configuration changed during measurement; "
            "refusing stale measurement results"
        )
    return rows


def commit_state(
    plan: dict[str, Any],
    report_path: Path,
    state_path: Path,
    excluded: set[str] | None = None,
) -> None:
    excluded = excluded or set()
    if plan.get("calibration") is not None:
        # The draw is a function of which files this run believes are unaffected,
        # and that belief comes from this cache. A calibration run that wrote to
        # it would move the ground under its own successors: the module it just
        # measured would become cache-valid, hence drawable, and a retry of the
        # same refused calibration would draw a different sample. A calibration
        # run therefore never advances the selection cache.
        raise SelectionError(
            "a calibration run must not advance the cache its own draw depends on"
        )
    rows = validate_results(plan, report_path, excluded)

    state = {
        "version": STATE_VERSION,
        "environment": plan["environment"],
        "files": {
            relative: {
                "fingerprint": plan["fingerprints"][relative],
                "status": "OK",
                "time": rows[relative]["time"],
            }
            for relative in plan["files"]
            if relative not in excluded
        },
    }
    atomic_json(state_path, state)


# --- shared same-host timing evidence --------------------------------------
#
# A new worktree on the same host and physical clone must not repeat timing
# solely because its worktree-local state is empty.  The shared store below
# the repository's Git common directory carries two evidence tables across
# worktrees of one physical clone on one host:
#
# * `measurements`: (environment, module fingerprint) -> measured seconds.
#   Fingerprints are content self-validating, so any green uncontended
#   non---force run may publish them, from a clean or dirty tree alike, and a
#   new worktree may credit them on exact (environment, fingerprint) match.
#   Only OK rows are ever published; violations and errors stay invalid.
# * `baselines`: whole rendered baseline documents with their origin commit.
#   Only genesis/`--rebase` full green runs on clean trees publish them, so
#   the origin commit exactly describes the measured content.  A
#   baseline-less worktree adopts one verbatim as its reference, but only
#   when that origin is at or before merge-base(HEAD, main): an on-main
#   clean tree may adopt its own commit (nothing is under test), while a
#   branch or dirty tree only ever receives a pre-change reference, never
#   its own reassuring baseline.  Adopted bytes are deterministic, so the
#   outer gate fingerprint can match.
#
# The trust boundary mirrors blanc-gate-evidence: same Git common directory,
# same host identity (whose single authority is gate-cache.host_identity,
# loaded below), runner-written only, atomically replaced, disposable.  Every
# read failure costs measurement, never a credit and never a crash.  An
# existing store file that belongs to a different host, or that this reader
# does not understand, is never overwritten: publication skips rather than
# destroying evidence it cannot use.
#
# All access happens inside scripts/check-elab.sh, which holds the
# host-global heavy gate lock from before planning through publication, so
# concurrent publishers are serialized and an interrupted write resolves to
# old-or-new via atomic replace.  No other caller may touch this store.
SHARED_EVIDENCE_DIRNAME = "blanc-elab-evidence"
SHARED_EVIDENCE_FILENAME = "evidence.json"
SHARED_EVIDENCE_SCHEMA = 1
SHARED_TRUST_DOMAIN = "same-git-common-directory"
SHARED_MAX_ENVS = 4
SHARED_MAX_PER_ENV = 4096
SHARED_MAX_BASELINES = 8
# Verdict-relevant Lean corpus for publish-time origin normalization: a clean
# branch commit touching none of these measured pre-change content, so its
# reference may carry the branch point as origin (baseline_origin_for_publish).
SHARED_LEAN_PATHSPECS = ("Blanc/", "Blanc.lean", "Main.lean")
SHARED_BASE_REF = "main"


def selector_script_dir() -> Path:
    return Path(__file__).resolve().parent


def load_shared_host_identity() -> str:
    """Host identity from its single authority, gate-cache.host_identity."""

    import importlib.util

    script_dir = str(selector_script_dir())
    if script_dir not in sys.path:
        sys.path.insert(0, script_dir)
    path = selector_script_dir() / "gate-cache.py"
    spec = importlib.util.spec_from_file_location("blanc_gate_cache_for_elab", path)
    if spec is None or spec.loader is None:
        raise SelectionError(f"cannot load host-identity authority: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    identity = module.host_identity()
    if not isinstance(identity, str) or not identity:
        raise SelectionError("host-identity authority returned no identity")
    return identity


def shared_git_common_dir(root: Path) -> Path:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--path-format=absolute", "--git-common-dir"],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        raise SelectionError(
            f"cannot resolve Git common directory: {error}"
        ) from error
    if result.returncode != 0 or not result.stdout.strip():
        raise SelectionError(
            "shared timing evidence requires a git worktree of one physical repository"
        )
    path = Path(result.stdout.strip())
    if not path.is_absolute():
        path = root / path
    try:
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise SelectionError(
            f"cannot resolve Git common directory {path}: {error}"
        ) from error
    if not resolved.is_dir():
        raise SelectionError(f"Git common directory is not a directory: {resolved}")
    return resolved


def shared_store_path(root: Path) -> Path:
    return (
        shared_git_common_dir(root) / SHARED_EVIDENCE_DIRNAME / SHARED_EVIDENCE_FILENAME
    )


def empty_shared_store(host: str) -> dict[str, Any]:
    return {
        "schema": SHARED_EVIDENCE_SCHEMA,
        "trust_domain": SHARED_TRUST_DOMAIN,
        "host": host,
        "measurements": {},
        "baselines": [],
    }


def valid_shared_record(record: Any) -> bool:
    return (
        isinstance(record, dict)
        and valid_time(record.get("time"))
        and isinstance(record.get("commit"), str)
        and isinstance(record.get("utc"), str)
    )


def valid_shared_baseline(entry: Any) -> bool:
    if not isinstance(entry, dict):
        return False
    if not isinstance(entry.get("origin"), str) or not entry["origin"]:
        return False
    if not isinstance(entry.get("environment"), str) or not entry["environment"]:
        return False
    payload = entry.get("payload")
    if not isinstance(payload, str) or not payload:
        return False
    if entry.get("digest") != sha256_bytes(payload.encode("utf-8")):
        return False
    if not isinstance(entry.get("rows"), int) or entry["rows"] <= 0:
        return False
    return isinstance(entry.get("utc"), str)


def read_shared_store(path: Path, host: str) -> tuple[dict[str, Any], str | None, bool]:
    """Load the shared store: (store, reason, writable).

    `reason` is None on success.  `writable` is False when an existing file
    must be preserved rather than replaced: a store belonging to a different
    host, or one this reader does not understand.  Corrupt files are
    replaceable -- they carry no usable evidence -- while foreign evidence is
    never destroyed to make room.
    """

    if not path.is_file():
        return empty_shared_store(host), "no prior shared timing evidence", True
    try:
        store = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        return (
            empty_shared_store(host),
            "shared timing evidence is unreadable or corrupt",
            True,
        )
    if not isinstance(store, dict):
        return empty_shared_store(host), "shared timing evidence is invalid", True
    if store.get("host") != host:
        return (
            empty_shared_store(host),
            "shared timing evidence belongs to a different host identity",
            False,
        )
    if store.get("schema") != SHARED_EVIDENCE_SCHEMA:
        return (
            empty_shared_store(host),
            "shared timing evidence schema is missing or incompatible",
            False,
        )
    if store.get("trust_domain") != SHARED_TRUST_DOMAIN:
        return (
            empty_shared_store(host),
            "shared timing evidence trust domain is missing or incompatible",
            False,
        )
    measurements = store.get("measurements")
    baselines = store.get("baselines")
    if not isinstance(measurements, dict) or not isinstance(baselines, list):
        return (
            empty_shared_store(host),
            "shared timing evidence tables are invalid",
            True,
        )
    for environment, table in measurements.items():
        if not isinstance(environment, str) or not isinstance(table, dict):
            return (
                empty_shared_store(host),
                "shared measurement table is invalid",
                True,
            )
        for fingerprint, record in table.items():
            if not isinstance(fingerprint, str) or not valid_shared_record(record):
                return (
                    empty_shared_store(host),
                    "shared measurement record is invalid",
                    True,
                )
    for entry in baselines:
        if not valid_shared_baseline(entry):
            return (
                empty_shared_store(host),
                "shared baseline record is invalid",
                True,
            )
    return store, None, True


def lookup_shared_measurements(
    store: dict[str, Any], environment: str
) -> dict[str, str]:
    table = store["measurements"].get(environment, {})
    return {
        fingerprint: record["time"] for fingerprint, record in table.items()
    }


def publish_shared_measurements(
    store: dict[str, Any],
    environment: str,
    entries: dict[str, dict[str, str]],
    utc: str,
) -> int:
    """Merge entries {fingerprint: {"time", "commit"}}; returns changed count.

    Eviction is a performance choice only: a pruned record simply causes a
    fresh measurement.
    """

    table = store["measurements"].setdefault(environment, {})
    changed = 0
    for fingerprint in sorted(entries):
        record = {
            "time": entries[fingerprint]["time"],
            "commit": entries[fingerprint]["commit"],
            "utc": utc,
        }
        if table.get(fingerprint) != record:
            changed += 1
        table[fingerprint] = record
    if len(table) > SHARED_MAX_PER_ENV:
        doomed = sorted(table, key=lambda name: table[name]["utc"])
        for fingerprint in doomed[: len(table) - SHARED_MAX_PER_ENV]:
            del table[fingerprint]
    while len(store["measurements"]) > SHARED_MAX_ENVS:
        oldest = min(
            store["measurements"],
            key=lambda name: max(
                (record["utc"] for record in store["measurements"][name].values()),
                default="",
            ),
        )
        del store["measurements"][oldest]
    return changed


def count_baseline_rows(text: str) -> int:
    return sum(
        1
        for raw in text.splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    )


def publish_shared_baseline(
    store: dict[str, Any],
    payload: bytes,
    origin: str,
    environment: str,
    utc: str,
) -> tuple[str, bool]:
    """Append a baseline document unless it is already retained under this environment.

    The key is (digest, environment): identical bytes re-measured under a new
    toolchain are a new reference, not a duplicate of the old one.
    """

    text = payload.decode("utf-8")
    digest = sha256_bytes(payload)
    if any(
        entry["digest"] == digest and entry["environment"] == environment
        for entry in store["baselines"]
    ):
        return digest, False
    store["baselines"].append(
        {
            "origin": origin,
            "environment": environment,
            "digest": digest,
            "rows": count_baseline_rows(text),
            "payload": text,
            "utc": utc,
        }
    )
    store["baselines"] = store["baselines"][-SHARED_MAX_BASELINES:]
    return digest, True


def git_output(root: Path, args: list[str]) -> str | None:
    try:
        result = subprocess.run(
            ["git", *args], cwd=root, capture_output=True, text=True, check=False
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def git_success(root: Path, args: list[str]) -> bool:
    try:
        result = subprocess.run(
            ["git", *args], cwd=root, capture_output=True, text=True, check=False
        )
    except OSError:
        return False
    return result.returncode == 0


def baseline_origin_for_publish(root: Path, head: str) -> str:
    """Normalize the origin of a reference measured on clean HEAD.

    A branch commit that touches no Lean source measured pre-change content,
    so its reference may carry the branch point as origin and stay adoptable
    on the branch it was measured for.  Anything else -- a Lean change, an
    unresolvable base, a failed comparison -- keeps HEAD, which adoption then
    judges strictly.
    """

    base = git_output(root, ["merge-base", head, SHARED_BASE_REF])
    if base is None or base == head:
        return head
    try:
        result = subprocess.run(
            ["git", "diff", "--quiet", base, head, "--", *SHARED_LEAN_PATHSPECS],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return head
    return base if result.returncode == 0 else head


def select_shared_baseline(
    store: dict[str, Any], environment: str, root: Path, head: str
) -> tuple[dict[str, Any] | None, str]:
    """Newest qualifying reference: same environment, origin at or before the branch point."""

    base = git_output(root, ["merge-base", head, SHARED_BASE_REF])
    if base is None:
        return None, f"cannot resolve merge-base({head[:12]}, {SHARED_BASE_REF})"
    candidates = [
        entry for entry in store["baselines"] if entry["environment"] == environment
    ]
    if not candidates:
        return None, "no shared baseline under this environment"
    qualifying: list[tuple[int, dict[str, Any]]] = []
    for entry in candidates:
        if not git_success(root, ["merge-base", "--is-ancestor", entry["origin"], base]):
            continue
        distance = git_output(root, ["rev-list", "--count", f"{entry['origin']}..{head}"])
        try:
            qualifying.append(
                (int(distance) if distance is not None else 10**9, entry)
            )
        except ValueError:
            qualifying.append((10**9, entry))
    if not qualifying:
        return None, "no shared baseline predates the changes under test"
    qualifying.sort(key=lambda item: item[0])
    return qualifying[0][1], ""


def validate_shared_baseline_payload(text: str) -> dict[str, float]:
    """Parse adopted rows strictly, minus the seeder's exact-corpus rule.

    Partial coverage is sound: paths without a row take the gate's existing
    first-measurement path, and rows for vanished paths are warnings.  Anything
    malformed refuses the adoption, never the gate.
    """

    rows: dict[str, float] = {}
    for number, raw in enumerate(text.splitlines(), start=1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3 or fields[0] != "OK":
            raise SelectionError(f"malformed shared baseline row {number}")
        try:
            elapsed = float(fields[1])
        except ValueError as error:
            raise SelectionError(f"non-numeric shared baseline row {number}") from error
        if not math.isfinite(elapsed) or elapsed <= 0 or fields[2] in rows:
            raise SelectionError(f"invalid shared baseline row {number}")
        rows[fields[2]] = elapsed
    if not rows:
        raise SelectionError("shared baseline carries no rows")
    return rows


def shared_utc_now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def fake_rows(plan: dict[str, Any], error: str | None = None) -> dict[str, dict[str, str]]:
    rows: dict[str, dict[str, str]] = {}
    for relative in plan["files"]:
        cached = plan["cached"].get(relative)
        rows[relative] = {
            "status": "OK",
            "time": cached["time"] if cached else "1.000",
            "provenance": "CACHED" if cached else "MEASURED",
        }
    if error is not None:
        rows[error]["status"] = "ERROR"
    return rows


def write_rows(path: Path, rows: dict[str, dict[str, str]]) -> None:
    path.write_text(
        "".join(
            f"{row['status']}\t{row['time']}\t{relative}\t{row['provenance']}\n"
            for relative, row in sorted(rows.items())
        ),
        encoding="utf-8",
    )


def self_test() -> int:
    controls = 0
    # The shell owns the environment-id capture because it also owns Lake's
    # setup diagnostics. Pin the two production call sites, then execute their
    # exact command-substitution shape against a stand-in that behaves like a
    # pristine first Lake invocation: a clean version on stdout and useful
    # setup chatter on stderr.
    shell_path = selector_script_dir() / "check-elab.sh"
    shell_source = shell_path.read_text(encoding="utf-8")
    assert 'if LEAN_ID_EARLY="$(lake env lean --version)"; then' in shell_source
    assert 'if ! LEAN_ID="$(lake env lean --version)"; then' in shell_source
    assert "lake env lean --version 2>&1" not in shell_source
    controls += 1  # both production captures keep stderr out of the identity

    with tempfile.TemporaryDirectory(prefix="blanc-elab-environment-capture-") as directory:
        fake_bin = Path(directory)
        fake_lake = fake_bin / "lake"
        fake_lake.write_text(
            """#!/bin/sh
if [ "$*" != "env lean --version" ]; then
  printf 'unexpected lake arguments: %s\n' "$*" >&2
  exit 97
fi
printf '%s\n' "${FAKE_LAKE_STDERR-}" >&2
printf '%s\n' "${FAKE_LAKE_STDOUT-}"
exit "${FAKE_LAKE_RC-0}"
""",
            encoding="utf-8",
        )
        fake_lake.chmod(0o755)
        capture_env = os.environ.copy()
        capture_env["PATH"] = f"{fake_bin}{os.pathsep}{os.defpath}"
        capture_env["FAKE_LAKE_STDOUT"] = "Lean (version 4.32.1, fake)"
        capture_env["FAKE_LAKE_STDERR"] = "info: cloning dependency"

        captured = subprocess.run(
            [
                "/bin/sh",
                "-c",
                'if LEAN_ID_EARLY="$(lake env lean --version)"; then '
                "printf 'identity=<%s>\\n' \"$LEAN_ID_EARLY\"; else exit 98; fi",
            ],
            env=capture_env,
            text=True,
            capture_output=True,
            check=False,
        )
        assert captured.returncode == 0
        assert captured.stdout == "identity=<Lean (version 4.32.1, fake)>\n"
        assert captured.stderr == "info: cloning dependency\n"
        controls += 1  # successful stdout is isolated while setup chatter remains visible

        capture_env["FAKE_LAKE_RC"] = "23"
        capture_env["FAKE_LAKE_STDERR"] = "toolchain lookup failed"
        refused = subprocess.run(
            [
                "/bin/sh",
                "-c",
                'if ! LEAN_ID="$(lake env lean --version)"; then '
                "printf 'REFUSED\\n'; exit 2; fi; exit 99",
            ],
            env=capture_env,
            text=True,
            capture_output=True,
            check=False,
        )
        assert refused.returncode == 2
        assert refused.stdout == "REFUSED\n"
        assert refused.stderr == "toolchain lookup failed\n"
        controls += 1  # a nonzero version command still refuses with its diagnostic

    with tempfile.TemporaryDirectory(prefix="blanc-elab-selection-") as directory:
        root = Path(directory)
        (root / "Blanc").mkdir()
        (root / "scripts").mkdir()
        for relative, text in {
            "lean-toolchain": "leanprover/lean4:v-test\n",
            "lakefile.lean": "import Lake\n",
            "lake-manifest.json": "{}\n",
            "scripts/check-elab.sh": "gate-v1\n",
            "scripts/check-elab-selection.py": "selector-v1\n",
            "Blanc/A.lean": "import Init\ndef a := 1\n",
            "Blanc/B.lean": "import Blanc.A\ndef b := a\n",
            "Blanc/C.lean": "import Init\ndef c := 3\n",
            "Blanc.lean": "import Blanc.B Blanc.C\n",
            "Main.lean": "import Blanc.C\n",
        }.items():
            (root / relative).write_text(text, encoding="utf-8")
        state_path = root / ".lake/check-elab-state.json"
        report_path = root / "report.tsv"

        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == plan["files"] and plan["reason"] == "no prior cache"
        controls += 1  # no cache is fail-open full
        write_rows(report_path, fake_rows(plan))
        commit_state(plan, report_path, state_path)

        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == [] and len(plan["cached"]) == 5
        controls += 1  # unchanged tree skips everything

        b_path = root / "Blanc/B.lean"
        original_b = b_path.read_text(encoding="utf-8")
        b_path.write_text(original_b + "\ntheorem leaf : True := by trivial\n", encoding="utf-8")
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == ["Blanc.lean", "Blanc/B.lean"]
        controls += 1  # a leaf edit reaches exactly its downstream closure
        b_path.write_text(original_b, encoding="utf-8")

        a_path = root / "Blanc/A.lean"
        original_a = a_path.read_text(encoding="utf-8")
        a_path.write_text(original_a.replace("1", "2"), encoding="utf-8")
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == ["Blanc.lean", "Blanc/A.lean", "Blanc/B.lean"]
        controls += 1  # an upstream edit reaches every downstream importer
        a_path.write_text(original_a, encoding="utf-8")

        c_path = root / "Blanc/C.lean"
        original_c = c_path.read_text(encoding="utf-8")
        c_path.write_text("/- import Blanc.Missing -/\npublic import Blanc.A\ndef c := 3\n", encoding="utf-8")
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == ["Blanc.lean", "Blanc/C.lean", "Main.lean"]
        controls += 1  # import-edge changes propagate; comments do not create edges
        c_path.write_text(original_c, encoding="utf-8")

        toolchain = root / "lean-toolchain"
        original_toolchain = toolchain.read_text(encoding="utf-8")
        toolchain.write_text("leanprover/lean4:v-other\n", encoding="utf-8")
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == plan["files"] and "environment changed" in plan["reason"]
        controls += 1  # shared configuration invalidates all modules
        toolchain.write_text(original_toolchain, encoding="utf-8")

        d_path = root / "Blanc/D.lean"
        d_path.write_text("import Init\n", encoding="utf-8")
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == ["Blanc/D.lean"]
        controls += 1  # an unimported new module alone is new
        write_rows(report_path, fake_rows(plan))
        commit_state(plan, report_path, state_path)
        d_path.unlink()
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == [] and "Blanc/D.lean" not in plan["files"]
        controls += 1  # an unimported deletion cannot affect remaining modules

        state_path.write_text("not json\n", encoding="utf-8")
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == plan["files"] and "corrupt" in plan["reason"]
        controls += 1  # corruption fails open to full
        write_rows(report_path, fake_rows(plan))
        commit_state(plan, report_path, state_path)

        before = state_path.read_bytes()
        plan = make_plan(root, state_path, "Lean test", force_full=True)
        rows = fake_rows(plan, error="Blanc/A.lean")
        write_rows(report_path, rows)
        try:
            commit_state(plan, report_path, state_path)
        except SelectionError:
            pass
        else:
            raise AssertionError("error result was cached")
        assert state_path.read_bytes() == before
        controls += 1  # a failed measurement cannot advance state

        partial_state = root / ".lake/partial-elab-state.json"
        commit_state(plan, report_path, partial_state, {"Blanc/A.lean"})
        partial_plan = make_plan(root, partial_state, "Lean test")
        assert partial_plan["affected"] == ["Blanc/A.lean"]
        controls += 1  # a failed file stays invalid while independent green rows persist

        plan = make_plan(root, state_path, "Lean test", force_full=True)
        write_rows(report_path, fake_rows(plan))
        c_path.write_text(original_c + "\n-- concurrent edit\n", encoding="utf-8")
        try:
            commit_state(plan, report_path, state_path)
        except SelectionError as error:
            assert "changed during measurement" in str(error)
        else:
            raise AssertionError("stale fingerprints were cached")
        assert state_path.read_bytes() == before
        c_path.write_text(original_c, encoding="utf-8")
        controls += 1  # concurrent source drift cannot be attached to stale state

        b_path.write_text("import Blanc.Missing\n", encoding="utf-8")
        try:
            make_plan(root, state_path, "Lean test")
        except SelectionError as error:
            assert "missing local module" in str(error)
        else:
            raise AssertionError("missing local import was accepted")
        controls += 1  # missing local dependencies fail closed

        b_path.write_text("import Blanc.A\n", encoding="utf-8")
        a_path.write_text("import Blanc.B\n", encoding="utf-8")
        try:
            make_plan(root, state_path, "Lean test")
        except SelectionError as error:
            assert "import cycle" in str(error)
        else:
            raise AssertionError("local import cycle was accepted")
        controls += 1  # cycles fail closed

    with tempfile.TemporaryDirectory(prefix="blanc-elab-lake-trace-") as directory:
        root = Path(directory)
        (root / "Blanc").mkdir()
        (root / "scripts").mkdir()
        for relative, text in {
            "lean-toolchain": "leanprover/lean4:v-test\n",
            "lakefile.lean": "import Lake\n",
            "lake-manifest.json": "{}\n",
            "scripts/check-elab.sh": "gate-v1\n",
            "scripts/check-elab-selection.py": "selector-v1\n",
            "Blanc/A.lean": "import Init\n",
            "Blanc/B.lean": "import Blanc.A\n",
            "Blanc.lean": "import Blanc.B\n",
        }.items():
            (root / relative).write_text(text, encoding="utf-8")
        for module, dep_hash in {
            "Blanc": "root-v1",
            "Blanc.A": "a-v1",
            "Blanc.B": "b-v1",
        }.items():
            trace = root / ".lake/build/lib/lean" / (
                module.replace(".", "/") + ".trace"
            )
            trace.parent.mkdir(parents=True, exist_ok=True)
            trace.write_text(json.dumps({"depHash": dep_hash}), encoding="utf-8")
        state_path = root / ".lake/check-elab-state.json"
        report_path = root / "report.tsv"

        plan = make_plan(
            root, state_path, "Lean test", require_lake_traces=True
        )
        write_rows(report_path, fake_rows(plan))
        commit_state(plan, report_path, state_path)
        plan = make_plan(
            root, state_path, "Lean test", require_lake_traces=True
        )
        assert plan["affected"] == []
        controls += 1  # stable Lake dependency hashes are reusable

        a_trace = root / ".lake/build/lib/lean/Blanc/A.trace"
        a_trace.write_text(json.dumps({"depHash": "a-v2"}), encoding="utf-8")
        plan = make_plan(
            root, state_path, "Lean test", require_lake_traces=True
        )
        assert plan["affected"] == ["Blanc.lean", "Blanc/A.lean", "Blanc/B.lean"]
        controls += 1  # external/transitive Lake drift propagates downstream

        (root / ".lake/build/lib/lean/Blanc/B.trace").unlink()
        try:
            make_plan(root, state_path, "Lean test", require_lake_traces=True)
        except SelectionError as error:
            assert "missing or unreadable Lake trace" in str(error)
        else:
            raise AssertionError("missing Lake trace was accepted")
        controls += 1  # absent build evidence fails closed


    # --- calibration sampler ------------------------------------------------
    # The sampler is pure, so most of its controls need no tree at all: a
    # synthetic baseline spread across all four bands exercises the draw, and a
    # synthetic result set exercises the tiers.
    commit_a = "a" * 40
    commit_b = "b" * 40
    baseline: dict[str, float] = {}
    for index in range(10):
        baseline[f"Blanc/Cheap{index:02d}.lean"] = 0.5 + 0.1 * index
    for index in range(12):
        baseline[f"Blanc/Mid{index:02d}.lean"] = 1.6 + 0.1 * index
    for index in range(8):
        baseline[f"Blanc/Dear{index:02d}.lean"] = 3.5 + 0.5 * index
    for index in range(6):
        baseline[f"Blanc/Tail{index:02d}.lean"] = 11.0 + index

    # The published table itself, not merely agreement with whatever it says.
    assert CALIBRATION_DOMAIN == "blanc-elab-calibration-v1"
    assert CALIBRATION_BANDS == (
        (0.0, 1.5, 4),
        (1.5, 3.0, 4),
        (3.0, 10.0, 2),
        (10.0, None, 2),
    )
    assert sum(want for _, _, want in CALIBRATION_BANDS) == 12
    assert CALIBRATION_BANDS[-1][2] == 2
    assert (
        calibration_seed("0" * 40)
        == "330e968af99ae87cb32b8c51ccf7c16bcdc2240afa87680291a92884f124c0a5"
    )
    controls += 1  # boundaries, the 4/4/2/2 draw, two from the tail, and the seed derivation are pinned

    draw = draw_calibration(baseline, list(baseline), commit_a, "base-v1", "src-v1")
    reversed_draw = draw_calibration(baseline, sorted(baseline, reverse=True), commit_a, "base-v1", "src-v1")
    assert draw["selected"] == reversed_draw["selected"]
    controls += 1  # the draw is reproducible from the commit and order-independent

    assert draw_calibration(baseline, list(baseline), commit_b, "base-v1", "src-v1")["selected"] != draw["selected"]
    controls += 1  # a different candidate commit draws a different sample

    assert len(draw["selected"]) == 12 and not draw["short_bands"]
    for band in draw["bands"]:
        assert len(band["selected"]) == band["want"]
        for relative in band["selected"]:
            assert baseline[relative] >= band["low"]
            assert band["high"] is None or baseline[relative] < band["high"]
    controls += 1  # every band draws its quota from inside its own boundaries

    thin = {path: time for path, time in baseline.items() if time < 10.0}
    thin["Blanc/Lonely.lean"] = 12.0
    thin_draw = draw_calibration(thin, list(thin), commit_a, "base-v1", "src-v1")
    assert thin_draw["bands"][3]["population"] == 1
    assert thin_draw["bands"][3]["selected"] == ["Blanc/Lonely.lean"]
    assert thin_draw["bands"][3]["label"] in thin_draw["short_bands"]
    controls += 1  # an under-populated band draws every member it has, and says so

    moved = dict(baseline)
    promoted = draw["bands"][0]["selected"][0]
    moved[promoted] = 20.0
    moved_draw = draw_calibration(moved, list(moved), commit_a, "base-v1", "src-v1")
    assert promoted not in moved_draw["bands"][0]["selected"]
    assert moved_draw["bands"][0]["population"] == draw["bands"][0]["population"] - 1
    assert moved_draw["bands"][3]["population"] == draw["bands"][3]["population"] + 1
    controls += 1  # bands are recomputed from the current baseline, never pinned

    grown = dict(baseline)
    grown["Blanc/Fresh.lean"] = 0.7
    grown_draw = draw_calibration(grown, list(grown), commit_a, "base-v1", "src-v1")
    assert len(set(draw["bands"][0]["selected"]) - set(grown_draw["bands"][0]["selected"])) <= 1
    for index in (1, 2, 3):
        assert grown_draw["bands"][index]["selected"] == draw["bands"][index]["selected"]
    controls += 1  # a new module displaces at most one control, in its own band only

    def measured(times: dict[str, float]) -> dict[str, dict[str, str]]:
        return {
            path: {"status": "OK", "time": f"{time:.3f}", "provenance": "MEASURED"}
            for path, time in times.items()
        }

    stub = {"calibration": draw}
    on_baseline = measured({path: baseline[path] for path in draw["selected"]})
    summary = calibration_verdict(stub, baseline, on_baseline, 2.0, 1.5, 1.0)
    assert not summary["refused"] and not summary["warned"]
    assert abs(summary["median"] - 1.0) < 1e-9
    controls += 1  # a host on its baseline produces no control finding

    tail = draw["bands"][3]["selected"][0]
    deviant = dict(on_baseline)
    deviant[tail] = {"status": "OK", "time": f"{baseline[tail] * 2.5:.3f}", "provenance": "MEASURED"}
    summary = calibration_verdict(stub, baseline, deviant, 2.0, 1.5, 1.0)
    assert [row["path"] for row in summary["refused"]] == [tail]
    assert "REFUSED" in calibration_block(draw, summary, deviant, 2.0, 1.5, 1.0)
    controls += 1  # a control at 2.5x refuses the run and is named in the evidence

    warned = dict(on_baseline)
    warned[tail] = {"status": "OK", "time": f"{baseline[tail] * 1.7:.3f}", "provenance": "MEASURED"}
    summary = calibration_verdict(stub, baseline, warned, 2.0, 1.5, 1.0)
    assert not summary["refused"] and [row["path"] for row in summary["warned"]] == [tail]
    controls += 1  # a control at 1.7x is annotated and the run still passes

    floor_baseline: dict[str, float] = {}
    floor_baseline.update({f"Blanc/Tiny{i}.lean": 0.4 for i in range(4)})
    floor_baseline.update({f"Blanc/Some{i}.lean": 2.0 for i in range(4)})
    floor_baseline.update({f"Blanc/More{i}.lean": 5.0 for i in range(2)})
    floor_baseline.update({f"Blanc/Most{i}.lean": 12.0 for i in range(2)})
    floor_draw = draw_calibration(floor_baseline, list(floor_baseline), commit_a, "base-v1", "src-v1")
    floor_stub = {"calibration": floor_draw}
    floor_rows = measured({path: floor_baseline[path] for path in floor_draw["selected"]})
    floor_rows["Blanc/Tiny0.lean"] = {"status": "OK", "time": "1.200", "provenance": "MEASURED"}
    summary = calibration_verdict(floor_stub, floor_baseline, floor_rows, 2.0, 1.5, 1.0)
    assert not summary["refused"] and not summary["warned"]
    floor_rows["Blanc/Tiny0.lean"] = {"status": "OK", "time": "1.500", "provenance": "MEASURED"}
    summary = calibration_verdict(floor_stub, floor_baseline, floor_rows, 2.0, 1.5, 1.0)
    assert [row["path"] for row in summary["refused"]] == ["Blanc/Tiny0.lean"]
    controls += 1  # the absolute floor absorbs sub-second noise but not a real move

    broken = dict(on_baseline)
    broken[tail] = {"status": "ERROR", "time": "0.0", "provenance": "MEASURED"}
    summary = calibration_verdict(stub, baseline, broken, 2.0, 1.5, 1.0)
    assert [row["path"] for row in summary["refused"]] == [tail]
    assert summary["refused"][0]["tier"] == "ERROR"
    controls += 1  # a control that stops elaborating refuses the run

    absent = {path: row for path, row in on_baseline.items() if path != tail}
    try:
        calibration_verdict(stub, baseline, absent, 2.0, 1.5, 1.0)
    except SelectionError as error:
        assert "was not measured" in str(error)
    else:
        raise AssertionError("an unmeasured control was accepted")
    controls += 1  # a control missing from the report fails closed

    reused = dict(on_baseline)
    reused[tail] = {"status": "OK", "time": f"{baseline[tail]:.3f}", "provenance": "CACHED"}
    try:
        calibration_verdict(stub, baseline, reused, 2.0, 1.5, 1.0)
    except SelectionError as error:
        assert "was not re-measured" in str(error)
    else:
        raise AssertionError("a cached control was accepted")
    controls += 1  # a control read back from the cache is not a measurement of this host

    with tempfile.TemporaryDirectory(prefix="blanc-elab-calibration-") as directory:
        root = Path(directory)
        (root / "Blanc").mkdir()
        (root / "scripts").mkdir()
        leaves = ["A", "B", "C", "D", "E", "F", "G", "H", "I"]
        sources = {
            "lean-toolchain": "leanprover/lean4:v-test\n",
            "lakefile.lean": "import Lake\n",
            "lake-manifest.json": "{}\n",
            "scripts/check-elab.sh": "gate-v1\n",
            "scripts/check-elab-selection.py": "selector-v1\n",
            "Blanc.lean": "import " + " ".join(f"Blanc.{n}" for n in leaves) + "\n",
            # Deliberately independent of Blanc.A, so that editing A leaves cheap
            # modules in the drawable population.
            "Main.lean": "import Init\n",
        }
        for index, name in enumerate(leaves):
            sources[f"Blanc/{name}.lean"] = f"import Init\ndef leaf{index} := {index}\n"
        for relative, body in sources.items():
            (root / relative).write_text(body, encoding="utf-8")

        # Blanc/D.lean is deliberately absent from the baseline: it is the
        # admission candidate. Blanc/Removed.lean is the opposite case, a row
        # whose file is gone.
        reference = {
            "Blanc.lean": 0.500, "Blanc/E.lean": 0.700, "Main.lean": 0.900,
            "Blanc/A.lean": 1.000, "Blanc/B.lean": 1.200, "Blanc/C.lean": 1.400,
            "Blanc/F.lean": 2.000, "Blanc/G.lean": 2.500,
            "Blanc/H.lean": 4.000, "Blanc/I.lean": 12.000,
            "Blanc/Removed.lean": 7.000,
        }
        baseline_path = root / "scripts/baseline-elab.txt"
        baseline_path.write_text(
            "# header\n"
            + "".join(
                ("# an interleaved provenance comment, as the real ledger carries\n"
                 if path == "Main.lean" else "")
                + f"OK\t{seconds:.3f}\t{path}\n"
                for path, seconds in reference.items()
            ),
            encoding="utf-8",
        )
        assert read_baseline(baseline_path) == reference
        controls += 1  # the ledger parses with comments interleaved among rows

        state_path = root / ".lake/check-elab-state.json"
        report_path = root / "report.tsv"
        warm = make_plan(root, state_path, "Lean test")
        write_rows(report_path, fake_rows(warm))
        commit_state(warm, report_path, state_path)

        (root / "Blanc/A.lean").write_text("import Init\ndef leaf0 := 99\n", encoding="utf-8")
        plan = make_plan(
            root, state_path, "Lean test",
            baseline_path=baseline_path, calibration_commit=commit_a,
        )
        calibration = plan["calibration"]
        assert calibration["candidates"] == ["Blanc/D.lean"]
        assert "Blanc/D.lean" in plan["affected"]
        assert "Blanc/D.lean" not in plan["cached"]
        assert "Blanc/D.lean" not in calibration["selected"]
        controls += 1  # a module with no local row is mandatory, and never a control

        assert {"Blanc/A.lean", "Blanc.lean"} <= set(plan["affected"])
        assert not {"Blanc/A.lean", "Blanc.lean"} & set(calibration["selected"])
        assert calibration["population"] == 8
        assert not set(plan["affected"]) & set(plan["cached"])
        controls += 1  # a module the edit can have reached is measured, never its own control

        assert "Blanc/Removed.lean" not in calibration["selected"]
        controls += 1  # a baseline row whose file is gone is never drawn

        # Two plans over the same unchanged state must agree: that is what makes
        # a refused calibration reproducible before any row is initialized.
        repeat = make_plan(
            root, state_path, "Lean test",
            baseline_path=baseline_path, calibration_commit=commit_a,
        )
        assert repeat["calibration"]["selected"] == calibration["selected"]
        assert repeat["calibration"]["population"] == calibration["population"]
        assert repeat["calibration"]["baseline_digest"] == calibration["baseline_digest"]
        assert repeat["calibration"]["source_digest"] == calibration["source_digest"]
        controls += 1  # a second run at the same commit and state draws the same sample

        assert calibration["compared"] == ["Blanc.lean", "Blanc/A.lean"]
        controls += 1  # rows measured instead of drawn are recorded, so the population is checkable

        write_rows(report_path, fake_rows(plan))
        validate_results(plan, report_path)
        try:
            commit_state(plan, report_path, state_path)
        except SelectionError as error:
            assert "must not advance the cache" in str(error)
        else:
            raise AssertionError("a calibration run advanced the cache")
        controls += 1  # a calibration run cannot move the state its own draw depends on

        # The verdict command end to end: its exit code, and that the block
        # records everything a reviewer needs to recompute and check the draw.
        plan_path = root / "plan.json"
        write_plan(plan_path, plan)
        loud = calibration["bands"][3]["selected"][0]
        control_rows = {
            relative: {
                "status": "OK",
                "time": f"{reference[relative] * (2.4 if relative == loud else 1.0):.3f}",
                "provenance": "MEASURED",
            }
            for relative in calibration["selected"]
        }
        control_rows[calibration["candidates"][0]] = {
            "status": "OK", "time": "1.000", "provenance": "MEASURED",
        }
        write_rows(report_path, control_rows)
        block_out = root / "block.txt"
        with io.StringIO() as sink, contextlib.redirect_stdout(sink):
            code = command_calibrate_verdict(
                argparse.Namespace(
                    plan=plan_path, report=report_path, baseline=baseline_path,
                    fail_factor=2.0, warn_factor=1.5, floor=1.0,
                    block_out=block_out,
                )
            )
        assert code == 1
        block = block_out.read_text(encoding="utf-8")
        for recorded in (
            calibration["seed"], calibration["commit"],
            calibration["baseline_digest"], calibration["source_digest"],
        ):
            assert recorded in block
        for band in calibration["bands"]:
            assert band["label"] in block
        for relative in calibration["selected"]:
            assert relative in block
        assert "2.40" in block and f"REFUSED: {loud}" in block
        controls += 1  # the verdict refuses, names the control, and records the whole draw

    # --- shared same-host timing evidence -----------------------------------
    # Every block below drives a scratch git repository, because origins and
    # adoption are commit-relative.  Git identity stays local to the scratch
    # invocation, and the shared store lands in the scratch common directory,
    # never in the repository under test.
    shared_tree = {
        ".gitignore": "scripts/baseline-elab.txt\n.lake/\n",
        "lean-toolchain": "leanprover/lean4:v-test\n",
        "lakefile.lean": "import Lake\n",
        "lake-manifest.json": "{}\n",
        "scripts/check-elab.sh": "gate-v1\n",
        "scripts/check-elab-selection.py": "selector-v1\n",
        "Blanc/A.lean": "import Init\ndef a := 1\n",
        "Blanc/B.lean": "import Blanc.A\ndef b := a\n",
        "Blanc.lean": "import Blanc.B\n",
    }

    def run_git(root: Path, *args: str) -> str:
        result = subprocess.run(
            [
                "git",
                "-c",
                "user.email=elab-test@local",
                "-c",
                "user.name=elab-test",
                *args,
            ],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 0, f"git {' '.join(args)}: {result.stderr}"
        return result.stdout.strip()

    def git_tree(directory: str) -> Path:
        root = Path(directory)
        (root / "Blanc").mkdir()
        (root / "scripts").mkdir()
        for relative, text in shared_tree.items():
            (root / relative).write_text(text, encoding="utf-8")
        run_git(root, "init", "-b", "main")
        run_git(root, "add", "-A")
        run_git(root, "commit", "-m", "genesis")
        return root

    def quiet_call(function, *args):
        sink = io.StringIO()
        with contextlib.redirect_stdout(sink):
            code = function(*args)
        return code, sink.getvalue()

    with tempfile.TemporaryDirectory(prefix="blanc-elab-shared-measure-") as directory:
        root = git_tree(directory)
        state_path = root / ".lake/check-elab-state.json"
        report_path = root / "report.tsv"
        plan_path = root / "plan.json"

        plan = make_plan(root, state_path, "Lean test")
        write_plan(plan_path, plan)
        write_rows(report_path, fake_rows(plan))
        commit_state(plan, report_path, state_path)
        code, out = quiet_call(
            command_publish,
            argparse.Namespace(plan=plan_path, report=report_path, exclude_file=None),
        )
        assert code == 0 and "measurement(s) recorded" in out
        store_file = shared_store_path(root)
        assert store_file.is_file()
        host = load_shared_host_identity()
        store, reason, writable = read_shared_store(store_file, host)
        assert reason is None and writable
        assert len(store["measurements"][plan["environment"]]) == len(plan["files"])

        # A new worktree with empty local state credits every shared row.
        state_path.unlink()
        fresh = make_plan(root, state_path, "Lean test")
        assert fresh["affected"] == []
        assert sorted(fresh["shared_credited"]) == sorted(plan["files"])
        assert len(fresh["cached"]) == len(plan["files"])
        controls += 1  # shared measurements credit an empty local cache on exact match

        # A fingerprint behind a credited measurement moves: only its real
        # downstream closure is measured; the rest stays credited.
        b_path = root / "Blanc/B.lean"
        original_b = b_path.read_text(encoding="utf-8")
        b_path.write_text(original_b.replace("a\n", "a + 1\n"), encoding="utf-8")
        moved = make_plan(root, state_path, "Lean test")
        assert moved["affected"] == ["Blanc.lean", "Blanc/B.lean"]
        assert moved["shared_credited"] == ["Blanc/A.lean"]
        b_path.write_text(original_b, encoding="utf-8")
        controls += 1  # changing an input behind a credit rejects the stale credit

        # Corruption fails open to full measurement, never to a credit.
        store_file.write_text("not json\n", encoding="utf-8")
        corrupt = make_plan(root, state_path, "Lean test")
        assert corrupt["affected"] == corrupt["files"]
        assert corrupt["shared_credited"] == []
        assert corrupt["shared_reason"] is not None and "corrupt" in corrupt["shared_reason"]
        controls += 1  # a corrupt shared store costs measurement, never a credit

        # An interrupted atomic write leaves only a temp file, which readers ignore.
        write_rows(report_path, fake_rows(plan))
        code, out = quiet_call(
            command_publish,
            argparse.Namespace(plan=plan_path, report=report_path, exclude_file=None),
        )
        assert code == 0 and "store reset" in out
        (store_file.parent / ".evidence.json.interrupted").write_text(
            "partial{", encoding="utf-8"
        )
        reread, reread_reason, _ = read_shared_store(store_file, host)
        assert reread_reason is None
        assert len(reread["measurements"][plan["environment"]]) == len(plan["files"])
        controls += 1  # an interrupted-write temp file is ignored by readers

    with tempfile.TemporaryDirectory(prefix="blanc-elab-shared-host-") as directory:
        root = git_tree(directory)
        host = load_shared_host_identity()
        store_file = shared_store_path(root)
        foreign = empty_shared_store("other-host-identity")
        foreign["measurements"] = {
            "env": {"fp": {"time": "1.0", "commit": "c", "utc": "u"}}
        }
        atomic_json(store_file, foreign)
        before = store_file.read_bytes()
        store, reason, writable = read_shared_store(store_file, host)
        assert reason is not None and "different host" in reason and not writable
        assert store["measurements"] == {}

        state_path = root / ".lake/check-elab-state.json"
        plan = make_plan(root, state_path, "Lean test")
        assert plan["affected"] == plan["files"] and plan["shared_credited"] == []
        plan_path = root / "plan.json"
        write_plan(plan_path, plan)
        report_path = root / "report.tsv"
        write_rows(report_path, fake_rows(plan))
        code, out = quiet_call(
            command_publish,
            argparse.Namespace(plan=plan_path, report=report_path, exclude_file=None),
        )
        assert code == 0 and "preserving existing store" in out
        assert store_file.read_bytes() == before
        controls += 1  # wrong-host evidence is never credited and never overwritten

        future = empty_shared_store(host)
        future["schema"] = 999
        atomic_json(store_file, future)
        _, reason, writable = read_shared_store(store_file, host)
        assert reason is not None and "incompatible" in reason and not writable
        controls += 1  # an unknown same-host schema is preserved, not replaced

    with tempfile.TemporaryDirectory(prefix="blanc-elab-shared-base-") as directory:
        root = git_tree(directory)
        host = load_shared_host_identity()
        store_file = shared_store_path(root)
        baseline_path = root / "scripts/baseline-elab.txt"
        env_id = "Lean test"

        def write_baseline(times: dict[str, float]) -> None:
            baseline_path.write_text(
                "# test reference\n"
                + "".join(
                    f"OK\t{seconds:.3f}\t{path}\n"
                    for path, seconds in sorted(times.items())
                ),
                encoding="utf-8",
            )

        files = discover_files(root)
        reference = {path: 1.0 + index * 0.5 for index, path in enumerate(files)}
        write_baseline(reference)
        head_a = run_git(root, "rev-parse", "HEAD")

        # A clean-tree genesis publishes its reference with its own origin.
        code, out = quiet_call(
            command_publish_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "recorded" in out
        store, _, _ = read_shared_store(store_file, host)
        assert len(store["baselines"]) == 1
        assert store["baselines"][0]["origin"] == head_a
        controls += 1  # a clean-tree genesis publishes its reference with its own origin

        # A dirty tree publishes measurements but never a reference.
        (root / "Blanc/A.lean").write_text(
            "import Init\ndef a := 99\n", encoding="utf-8"
        )
        code, out = quiet_call(
            command_publish_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "not clean" in out
        store, _, _ = read_shared_store(store_file, host)
        assert len(store["baselines"]) == 1
        run_git(root, "checkout", "--", "Blanc/A.lean")
        controls += 1  # baseline publication refuses a dirty tree

        # A scripts-only branch commit normalizes its origin to the branch point.
        run_git(root, "checkout", "-b", "scripts-only")
        (root / "scripts/check-elab.sh").write_text("gate-v2\n", encoding="utf-8")
        run_git(root, "commit", "-am", "scripts only")
        write_baseline(reference)
        code, out = quiet_call(
            command_publish_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "recorded" in out
        store, _, _ = read_shared_store(store_file, host)
        branch_environment = environment_fingerprint(root, env_id)
        branch_docs = [
            entry
            for entry in store["baselines"]
            if entry["environment"] == branch_environment
        ]
        assert len(branch_docs) == 1 and branch_docs[0]["origin"] == head_a
        controls += 1  # a branch commit touching no Lean source carries the branch point as origin

        # The branch adopts the pre-change reference verbatim.
        baseline_path.unlink()
        code, out = quiet_call(
            command_adopt_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "adopted" in out
        assert baseline_path.read_bytes() == branch_docs[0]["payload"].encode("utf-8")
        receipt = json.loads(
            (root / ".lake/blanc-elab-shared-receipt.json").read_text(encoding="utf-8")
        )
        assert receipt["origin"] == head_a
        assert receipt["digest"] == branch_docs[0]["digest"]
        controls += 1  # adoption restores the reference bytes verbatim with a provenance receipt

        # A Lean change keeps its own commit as origin ...
        run_git(root, "checkout", "main")
        run_git(root, "checkout", "-b", "lean-change")
        (root / "Blanc/A.lean").write_text(
            "import Init\ndef a := 7\n", encoding="utf-8"
        )
        run_git(root, "commit", "-am", "lean change")
        head_c = run_git(root, "rev-parse", "HEAD")
        write_baseline({path: 5.0 for path in discover_files(root)})
        code, out = quiet_call(
            command_publish_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "recorded" in out
        store, _, _ = read_shared_store(store_file, host)
        assert [entry for entry in store["baselines"] if entry["origin"] == head_c]
        controls += 1  # a branch commit touching Lean source keeps its own commit as origin

        # ... and a tree carrying that change adopts the pre-change reference,
        # never its own.
        baseline_path.unlink()
        code, out = quiet_call(
            command_adopt_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "adopted" in out
        assert head_a[:12] in out and head_c[:12] not in out
        selected_rows = validate_shared_baseline_payload(
            baseline_path.read_text(encoding="utf-8")
        )
        assert selected_rows == reference
        controls += 1  # the changed candidate cannot adopt its own reassuring baseline

        # With only its own origin stored, the changed tree is refused outright.
        store["baselines"] = [
            entry for entry in store["baselines"] if entry["origin"] == head_c
        ]
        atomic_json(store_file, store)
        baseline_path.unlink()
        code, out = quiet_call(
            command_adopt_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "predates the changes under test" in out
        assert not baseline_path.exists()
        controls += 1  # no qualifying reference refuses adoption instead of seeding self

        # A republished identical reference is deduplicated, not duplicated.
        write_baseline({path: 5.0 for path in discover_files(root)})
        before_count = len(read_shared_store(store_file, host)[0]["baselines"])
        code, out = quiet_call(
            command_publish_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "already retained" in out
        assert len(read_shared_store(store_file, host)[0]["baselines"]) == before_count
        controls += 1  # identical references deduplicate by digest

        # A toolchain move finds no reference under the new environment.
        (root / "lean-toolchain").write_text(
            "leanprover/lean4:v-other\n", encoding="utf-8"
        )
        baseline_path.unlink()
        code, out = quiet_call(
            command_adopt_baseline,
            argparse.Namespace(root=root, baseline=baseline_path, environment_id=env_id),
        )
        assert code == 0 and "no shared baseline under this environment" in out
        assert not baseline_path.exists()
        run_git(root, "checkout", "--", "lean-toolchain")
        controls += 1  # adoption refuses a reference measured under another environment

        # Retention evicts oldest-first and only costs re-measurement.
        saved_max = globals()["SHARED_MAX_BASELINES"]
        globals()["SHARED_MAX_BASELINES"] = 2
        try:
            trial = empty_shared_store(host)
            for index in range(3):
                payload = f"# {index}\nOK\t1.000\tBlanc/A.lean\n".encode()
                publish_shared_baseline(
                    trial, payload, f"origin-{index}", "env", f"utc-{index}"
                )
            assert [entry["origin"] for entry in trial["baselines"]] == [
                "origin-1",
                "origin-2",
            ]
        finally:
            globals()["SHARED_MAX_BASELINES"] = saved_max
        controls += 1  # baseline retention evicts oldest-first

        saved_per_env = globals()["SHARED_MAX_PER_ENV"]
        globals()["SHARED_MAX_PER_ENV"] = 2
        try:
            trial = empty_shared_store(host)
            publish_shared_measurements(
                trial,
                "env",
                {"fp-a": {"time": "1.0", "commit": "c"}},
                "2026-01-01T00:00:00Z",
            )
            publish_shared_measurements(
                trial,
                "env",
                {
                    "fp-b": {"time": "2.0", "commit": "c"},
                    "fp-c": {"time": "3.0", "commit": "c"},
                },
                "2026-01-02T00:00:00Z",
            )
            assert sorted(trial["measurements"]["env"]) == ["fp-b", "fp-c"]
        finally:
            globals()["SHARED_MAX_PER_ENV"] = saved_per_env
        controls += 1  # measurement retention evicts oldest-first

    with tempfile.TemporaryDirectory(prefix="blanc-elab-shared-exclude-") as directory:
        root = git_tree(directory)
        host = load_shared_host_identity()
        store_file = shared_store_path(root)
        state_path = root / ".lake/check-elab-state.json"
        plan = make_plan(root, state_path, "Lean test")
        plan_path = root / "plan.json"
        write_plan(plan_path, plan)
        report_path = root / "report.tsv"
        write_rows(report_path, fake_rows(plan, error="Blanc/A.lean"))
        exclude_path = root / "exclude.txt"
        exclude_path.write_text("Blanc/A.lean\n", encoding="utf-8")
        code, _ = quiet_call(
            command_publish,
            argparse.Namespace(
                plan=plan_path, report=report_path, exclude_file=exclude_path
            ),
        )
        assert code == 0
        store, _, _ = read_shared_store(store_file, host)
        table = store["measurements"][plan["environment"]]
        assert plan["fingerprints"]["Blanc/A.lean"] not in table
        assert plan["fingerprints"]["Blanc/B.lean"] in table
        controls += 1  # excluded violations are never published while green rows persist

        store_file.unlink()
        code, _ = quiet_call(
            command_publish,
            argparse.Namespace(plan=plan_path, report=report_path, exclude_file=None),
        )
        assert code == 0
        store, _, _ = read_shared_store(store_file, host)
        table = store["measurements"][plan["environment"]]
        assert plan["fingerprints"]["Blanc/A.lean"] not in table
        controls += 1  # an error row is refused publication even when unexcluded

    import importlib.util

    script_dir = str(selector_script_dir())
    if script_dir not in sys.path:
        sys.path.insert(0, script_dir)
    spec = importlib.util.spec_from_file_location(
        "blanc_gate_cache_probe", selector_script_dir() / "gate-cache.py"
    )
    assert spec is not None and spec.loader is not None
    probe = importlib.util.module_from_spec(spec)
    sys.modules["blanc_gate_cache_probe"] = probe
    spec.loader.exec_module(probe)
    assert load_shared_host_identity() == probe.host_identity()
    controls += 1  # the shared store uses the gate cache's host identity, not its own

    print(f"OK — elab selection: {controls} invalidation/cache controls passed")
    return 0



def calibration_verdict(
    plan: dict[str, Any],
    baseline: dict[str, float],
    rows: dict[str, dict[str, str]],
    fail_factor: float,
    warn_factor: float,
    floor: float,
) -> dict[str, Any]:
    """Adjudicate the drawn controls against their host-local baseline rows.

    A control carries the same factor and the same absolute floor as a row.
    Dropping the floor would make the cheapest band refuse on ordinary
    scheduler noise — a half-second blip on a sub-second file is a large ratio
    and no real change — and a gate that refuses on noise is a gate everyone
    learns to bypass. The one deliberate difference from the row rule is the
    boundary itself: a row fails *above* the factor, a control refuses *at or
    above* it, so a control is never the more permissive of the two.
    """
    calibration = plan.get("calibration")
    if not calibration:
        raise SelectionError("plan carries no calibration draw")
    for relative in calibration["candidates"]:
        row = rows.get(relative)
        if row is None or row["provenance"] != "MEASURED":
            raise SelectionError(
                f"admission candidate was not measured: {relative}"
            )
    controls: list[dict[str, Any]] = []
    for relative in calibration["selected"]:
        row = rows.get(relative)
        if row is None:
            raise SelectionError(f"drawn control was not measured: {relative}")
        if row["provenance"] != "MEASURED":
            raise SelectionError(f"drawn control was not re-measured: {relative}")
        if row["status"] != "OK":
            controls.append(
                {"path": relative, "measured": None, "baseline": baseline[relative],
                 "ratio": None, "tier": "ERROR"}
            )
            continue
        measured = float(row["time"])
        reference = baseline[relative]
        ratio = measured / reference if reference > 0 else float("inf")
        over_floor = measured > reference + floor
        if ratio >= fail_factor and over_floor:
            tier = "REFUSE"
        elif ratio >= warn_factor and over_floor:
            tier = "WARN"
        else:
            tier = "OK"
        controls.append(
            {"path": relative, "measured": measured, "baseline": reference,
             "ratio": ratio, "tier": tier}
        )
    ratios = sorted(c["ratio"] for c in controls if c["ratio"] is not None)
    summary: dict[str, Any] = {
        "controls": controls,
        "refused": [c for c in controls if c["tier"] in {"REFUSE", "ERROR"}],
        "warned": [c for c in controls if c["tier"] == "WARN"],
        "median": ratios[len(ratios) // 2] if ratios else None,
        "low": ratios[0] if ratios else None,
        "high": ratios[-1] if ratios else None,
    }
    return summary


def calibration_block(
    calibration: dict[str, Any],
    summary: dict[str, Any],
    rows: dict[str, dict[str, str]],
    fail_factor: float,
    warn_factor: float,
    floor: float,
) -> str:
    """Render the reviewable evidence block for a calibration run.

    Generated rather than transcribed, because a reviewer must be able to
    recompute the draw from the commit and check it was not gamed.
    """
    lines: list[str] = []
    add = lines.append
    add("Calibration control — scripts/check-elab.sh --calibrate")
    add("")
    add("Regression detection and calibration are different jobs. The content and")
    add("import-closure fingerprint has already established that every undrawn")
    add("module cannot have moved, so an undrawn file is not a coverage gap; the")
    add("sample only establishes that this host was behaving normally while the")
    add("mandatory rows below were measured.")
    add("")
    add(f"Seed domain {calibration['domain']}, candidate commit")
    add(f"  {calibration['commit']}")
    add("seed sha256(domain|commit)")
    add(f"  {calibration['seed']}")
    add("baseline sha256")
    add(f"  {calibration['baseline_digest']}")
    add("source-set sha256 (every discovered path and its content)")
    add(f"  {calibration['source_digest']}")
    add("")
    add(
        f"Drawn from the {calibration['population']} of "
        f"{calibration['baseline_rows']} baseline rows that this run's content and"
    )
    add("import-closure fingerprint proves unaffected; within a band, the first")
    add("k paths ordered by sha256(seed|path). Boundaries are fixed; membership")
    add("is recomputed from the baseline current at this commit.")
    add("")
    add(
        f"The remaining {len(calibration['compared'])} row(s) were not drawn"
        " because this run measured and"
    )
    add("compared them outright:")
    shown = calibration["compared"][:12]
    for relative in shown:
        add(f"    {relative}")
    if not shown:
        add("    (none)")
    elif len(calibration["compared"]) > len(shown):
        add(f"    ... and {len(calibration['compared']) - len(shown)} more")
    add("")
    add("  band            population  drawn")
    for band in calibration["bands"]:
        add(f"  {band['label']:<14}{band['population']:>12}{len(band['selected']):>7}")
    if calibration["short_bands"]:
        add("")
        add(
            "  under-populated band(s) drew every member available: "
            + ", ".join(calibration["short_bands"])
        )
    add("")
    if calibration["candidates"]:
        add("  mandatory (measured, never sampled)                     seconds")
        for relative in calibration["candidates"]:
            row = rows.get(relative)
            elapsed = "ERROR" if row is None or row["status"] != "OK" else row["time"]
            add(f"  {relative:<52}{elapsed:>10}")
        add("")
    add("  control                                              measured  baseline  ratio")
    for control in summary["controls"]:
        if control["ratio"] is None:
            add(f"  {control['path']:<52}{'ERROR':>10}{control['baseline']:>10.3f}{'--':>7}")
        else:
            add(
                f"  {control['path']:<52}{control['measured']:>10.3f}"
                f"{control['baseline']:>10.3f}{control['ratio']:>7.2f}"
            )
    add("")
    if summary["median"] is None:
        add("No control produced a ratio.")
    else:
        add(
            f"{len(summary['controls'])} controls, median ratio "
            f"{summary['median']:.3f}, spread {summary['low']:.2f}x-{summary['high']:.2f}x."
        )
        add(
            f"A control refuses the run at {fail_factor:.2f}x and is annotated at"
            f" {warn_factor:.2f}x,"
        )
        add(
            f"each also requiring the same {floor:.1f}s absolute excess the gate"
            " applies to"
        )
        add("the rows themselves.")
        if summary["refused"]:
            add("")
            for control in summary["refused"]:
                if control["ratio"] is None:
                    add(f"REFUSED: {control['path']} did not elaborate.")
                else:
                    add(
                        f"REFUSED: {control['path']} at {control['ratio']:.2f}x "
                        f"({control['measured']:.3f}s vs {control['baseline']:.3f}s)."
                    )
        elif summary["warned"]:
            add("")
            for control in summary["warned"]:
                add(
                    f"ANNOTATED: {control['path']} at {control['ratio']:.2f}x "
                    f"({control['measured']:.3f}s vs {control['baseline']:.3f}s)."
                )
        else:
            add(f"No control reached {warn_factor:.2f}x.")
    return "\n".join(lines)


def command_calibrate_verdict(args: argparse.Namespace) -> int:
    plan = read_plan(args.plan)
    calibration = plan.get("calibration")
    if not calibration:
        raise SelectionError("plan carries no calibration draw")
    baseline = read_baseline(args.baseline)
    rows = read_result_rows(args.report)
    summary = calibration_verdict(
        plan, baseline, rows, args.fail_factor, args.warn_factor, args.floor
    )
    block = calibration_block(
        calibration, summary, rows, args.fail_factor, args.warn_factor, args.floor
    )
    print("--- calibration evidence ---")
    for line in block.split("\n"):
        print(f"# {line}".rstrip())
    print("--- end calibration evidence ---")
    if args.block_out:
        args.block_out.write_text(block + "\n", encoding="utf-8")
    return 1 if summary["refused"] else 0


def command_adopt_baseline(args: argparse.Namespace) -> int:
    """Adopt a provenance-checked shared reference, or explain why not.

    Always returns 0: a refused adoption falls back to genesis, never to a
    gate failure.  The shell decides by testing whether the baseline appeared.
    """

    root = args.root.resolve()
    if args.baseline.is_file():
        print("NOTE — elab: local baseline already present; not adopting shared evidence")
        return 0
    try:
        environment = environment_fingerprint(root, args.environment_id)
        head = git_output(root, ["rev-parse", "HEAD"])
        if head is None:
            print("NOTE — elab: not adopting shared evidence: cannot resolve HEAD")
            return 0
        host = load_shared_host_identity()
        store, reason, _ = read_shared_store(shared_store_path(root), host)
        if reason is not None:
            print(f"NOTE — elab: not adopting shared evidence: {reason}")
            return 0
        selected, select_reason = select_shared_baseline(store, environment, root, head)
        if selected is None:
            print(f"NOTE — elab: not adopting shared evidence: {select_reason}")
            return 0
        rows = validate_shared_baseline_payload(selected["payload"])
    except SelectionError as error:
        print(f"NOTE — elab: not adopting shared evidence: {error}")
        return 0
    receipt = root / ".lake/blanc-elab-shared-receipt.json"
    try:
        atomic_json(
            receipt,
            {
                "schema": 1,
                "origin": selected["origin"],
                "environment": environment,
                "digest": selected["digest"],
                "rows": len(rows),
                "host": host,
                "recorded_utc": shared_utc_now(),
            },
        )
    except OSError as error:
        print(
            "NOTE — elab: not adopting shared evidence: "
            f"cannot record provenance ({error})"
        )
        return 0
    try:
        args.baseline.parent.mkdir(parents=True, exist_ok=True)
        args.baseline.write_bytes(selected["payload"].encode("utf-8"))
    except OSError as error:
        print(
            "NOTE — elab: not adopting shared evidence: "
            f"cannot write baseline ({error})"
        )
        return 0
    print(
        f"elab shared baseline: adopted origin {selected['origin'][:12]} "
        f"({len(rows)} rows, digest {selected['digest'][:16]})"
    )
    return 0


def command_publish(args: argparse.Namespace) -> int:
    """Publish this run's OK measurements to the shared store.

    Best-effort and loud: publication must never turn a green run red, and a
    skip always says why.  Only non-excluded OK rows are published, so
    violations and errors can never enter the store.
    """

    try:
        plan = read_plan(args.plan)
        rows = read_result_rows(args.report)
    except SelectionError as error:
        print(f"NOTE — elab: shared publication skipped: {error}")
        return 0
    excluded = (
        set(args.exclude_file.read_text(encoding="utf-8").splitlines())
        if args.exclude_file
        else set()
    )
    root = Path(plan["root"])
    entries: dict[str, dict[str, str]] = {}
    for relative in plan["files"]:
        if relative in excluded:
            continue
        row = rows.get(relative)
        if row is None or row["status"] != "OK":
            continue
        fingerprint = plan["fingerprints"].get(relative)
        if not isinstance(fingerprint, str):
            continue
        entries[fingerprint] = {"time": row["time"], "commit": "unknown"}
    if not entries:
        print("NOTE — elab: shared publication skipped: no publishable measurements")
        return 0
    head = git_output(root, ["rev-parse", "HEAD"]) or "unknown"
    for record in entries.values():
        record["commit"] = head
    try:
        host = load_shared_host_identity()
        path = shared_store_path(root)
        store, reason, writable = read_shared_store(path, host)
        if not writable:
            print(
                "NOTE — elab: shared publication skipped: "
                f"preserving existing store ({reason})"
            )
            return 0
        if reason is not None and reason != "no prior shared timing evidence":
            print(f"NOTE — elab: shared store reset: {reason}")
        changed = publish_shared_measurements(
            store, plan["environment"], entries, shared_utc_now()
        )
        atomic_json(path, store)
    except SelectionError as error:
        print(f"NOTE — elab: shared publication skipped: {error}")
        return 0
    except OSError as error:
        print(f"NOTE — elab: shared publication skipped: cannot write store ({error})")
        return 0
    print(
        f"elab shared publish: {changed} measurement(s) recorded "
        f"({len(entries)} presented)"
    )
    return 0


def command_publish_baseline(args: argparse.Namespace) -> int:
    """Publish a genesis/rebase reference with the origin it measured.

    The shell calls this only after writing a full green baseline.  The tree
    must be clean, so the origin commit exactly describes the measured
    content; anything else skips loudly rather than publishing a reference
    whose provenance it cannot state.
    """

    root = args.root.resolve()
    try:
        rows = read_baseline(args.baseline)
    except SelectionError as error:
        print(f"NOTE — elab: baseline publication skipped: {error}")
        return 0
    try:
        files = discover_files(root)
    except SelectionError as error:
        print(f"NOTE — elab: baseline publication skipped: {error}")
        return 0
    if set(rows) != set(files):
        print(
            "NOTE — elab: baseline publication skipped: "
            "rows do not cover the exact Lean corpus"
        )
        return 0
    try:
        baseline_text = args.baseline.read_text(encoding="utf-8")
    except OSError as error:
        print(f"NOTE — elab: baseline publication skipped: cannot read baseline ({error})")
        return 0
    for raw in baseline_text.splitlines():
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        if raw.startswith("ERROR\t"):
            print(
                "NOTE — elab: baseline publication skipped: "
                "reference carries failures"
            )
            return 0
    status = git_output(root, ["status", "--porcelain"])
    if status is None:
        print("NOTE — elab: baseline publication skipped: cannot verify a clean tree")
        return 0
    if status:
        print("NOTE — elab: baseline publication skipped: tree is not clean")
        return 0
    head = git_output(root, ["rev-parse", "HEAD"])
    if head is None:
        print("NOTE — elab: baseline publication skipped: cannot resolve HEAD")
        return 0
    try:
        environment = environment_fingerprint(root, args.environment_id)
        payload = args.baseline.read_bytes()
        payload.decode("utf-8")
        host = load_shared_host_identity()
        path = shared_store_path(root)
        store, reason, writable = read_shared_store(path, host)
        if not writable:
            print(
                "NOTE — elab: baseline publication skipped: "
                f"preserving existing store ({reason})"
            )
            return 0
        origin = baseline_origin_for_publish(root, head)
        digest, added = publish_shared_baseline(
            store, payload, origin, environment, shared_utc_now()
        )
        atomic_json(path, store)
    except (SelectionError, OSError, UnicodeError) as error:
        print(f"NOTE — elab: baseline publication skipped: {error}")
        return 0
    print(
        f"elab shared publish: baseline {digest[:16]} "
        f"{'recorded' if added else 'already retained'} (origin {origin[:12]})"
    )
    return 0


def command_files(args: argparse.Namespace) -> int:
    plan = read_plan(args.plan)
    if args.shared:
        print("\n".join(plan.get("shared_credited", [])))
        return 0
    if args.controls or args.candidates:
        calibration = plan.get("calibration")
        if not calibration:
            raise SelectionError("plan carries no calibration draw")
        key = "selected" if args.controls else "candidates"
        print("\n".join(calibration[key]))
        return 0
    print("\n".join(plan["affected" if args.affected else "files"]))
    return 0


def command_plan(args: argparse.Namespace) -> int:
    plan = make_plan(
        args.root,
        args.state,
        args.environment_id,
        force_full=args.full,
        full_reason=args.full_reason,
        require_lake_traces=True,
        baseline_path=args.baseline,
        calibration_commit=args.commit,
    )
    write_plan(args.plan, plan)
    affected = len(plan["affected"])
    cached = len(plan["files"]) - affected
    shared = len(plan.get("shared_credited", []))
    shared_note = f", {shared} from shared same-host evidence" if shared else ""
    if plan["reason"]:
        print(
            f"elab selection: {affected} measured, {cached} cache-valid "
            f"({plan['reason']}{shared_note})"
        )
    else:
        print(
            f"elab selection: {affected} measured, {cached} provably unaffected "
            f"by content/import-closure fingerprint{shared_note}"
        )
    calibration = plan["calibration"]
    if calibration is not None:
        print(
            f"elab calibration: {len(calibration['candidates'])} mandatory, "
            f"{len(calibration['selected'])} drawn from {calibration['population']} "
            f"provably-unaffected control(s), seed {calibration['seed'][:12]} "
            f"from commit {calibration['commit'][:12]}"
        )
    return 0


def command_validate(args: argparse.Namespace) -> int:
    validate_results(
        read_plan(args.plan),
        args.report,
        set(args.exclude_file.read_text(encoding="utf-8").splitlines())
        if args.exclude_file
        else None,
    )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    plan = subparsers.add_parser("plan")
    plan.add_argument("--root", type=Path, required=True)
    plan.add_argument("--state", type=Path, required=True)
    plan.add_argument("--plan", type=Path, required=True)
    plan.add_argument("--environment-id", required=True)
    plan.add_argument("--full", action="store_true")
    plan.add_argument("--full-reason", default="explicit --full")
    plan.add_argument("--baseline", type=Path)
    plan.add_argument("--commit")
    plan.set_defaults(function=command_plan)

    files = subparsers.add_parser("files")
    files.add_argument("--plan", type=Path, required=True)
    group = files.add_mutually_exclusive_group()
    group.add_argument("--affected", action="store_true")
    group.add_argument("--controls", action="store_true")
    group.add_argument("--candidates", action="store_true")
    group.add_argument("--shared", action="store_true")
    files.set_defaults(function=command_files)

    modules = subparsers.add_parser("modules")
    modules.add_argument("--root", type=Path, required=True)
    modules.set_defaults(
        function=lambda args: print(
            "\n".join(module_name(path) for path in discover_files(args.root.resolve()))
        )
    )

    merge = subparsers.add_parser("merge")
    merge.add_argument("--plan", type=Path, required=True)
    merge.add_argument("--measured", type=Path, required=True)
    merge.add_argument("--report", type=Path, required=True)
    merge.set_defaults(
        function=lambda args: merge_results(
            read_plan(args.plan), args.measured, args.report
        )
    )

    commit = subparsers.add_parser("commit")
    commit.add_argument("--plan", type=Path, required=True)
    commit.add_argument("--report", type=Path, required=True)
    commit.add_argument("--state", type=Path, required=True)
    commit.add_argument("--exclude-file", type=Path)
    commit.set_defaults(
        function=lambda args: commit_state(
            read_plan(args.plan),
            args.report,
            args.state,
            set(args.exclude_file.read_text(encoding="utf-8").splitlines())
            if args.exclude_file
            else None,
        )
    )

    validate = subparsers.add_parser("validate")
    validate.add_argument("--plan", type=Path, required=True)
    validate.add_argument("--report", type=Path, required=True)
    validate.add_argument("--exclude-file", type=Path)
    validate.set_defaults(function=command_validate)

    verdict = subparsers.add_parser("calibrate-verdict")
    verdict.add_argument("--plan", type=Path, required=True)
    verdict.add_argument("--report", type=Path, required=True)
    verdict.add_argument("--baseline", type=Path, required=True)
    verdict.add_argument("--fail-factor", type=float, required=True)
    verdict.add_argument("--warn-factor", type=float, required=True)
    verdict.add_argument("--floor", type=float, required=True)
    verdict.add_argument("--block-out", type=Path)
    verdict.set_defaults(function=command_calibrate_verdict)

    adopt = subparsers.add_parser("adopt-baseline")
    adopt.add_argument("--root", type=Path, required=True)
    adopt.add_argument("--baseline", type=Path, required=True)
    adopt.add_argument("--environment-id", required=True)
    adopt.set_defaults(function=command_adopt_baseline)

    publish = subparsers.add_parser("publish")
    publish.add_argument("--plan", type=Path, required=True)
    publish.add_argument("--report", type=Path, required=True)
    publish.add_argument("--exclude-file", type=Path)
    publish.set_defaults(function=command_publish)

    publish_baseline = subparsers.add_parser("publish-baseline")
    publish_baseline.add_argument("--root", type=Path, required=True)
    publish_baseline.add_argument("--baseline", type=Path, required=True)
    publish_baseline.add_argument("--environment-id", required=True)
    publish_baseline.set_defaults(function=command_publish_baseline)

    test = subparsers.add_parser("self-test")
    test.set_defaults(function=lambda _args: self_test())
    return parser


def main(argv: list[str]) -> int:
    parser = build_parser()
    args = parser.parse_args(argv[1:])
    try:
        result = args.function(args)
        return 0 if result is None else result
    except SelectionError as error:
        print(f"REGRESSION — elab selection: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
