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
import sys
import tempfile
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
    """Parse the committed baseline into path -> seconds.

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

    calibration: dict[str, Any] | None = None
    if calibration_commit is not None:
        if baseline_path is None:
            raise SelectionError("calibration needs the committed baseline")
        baseline = read_baseline(baseline_path)
        # `affected` may alias `files` on a full run; never append through it.
        affected = list(affected)
        # A module with no committed row is the measurement, not a control, so
        # it is measured whatever the cache believes about it.
        mandatory = [relative for relative in files if relative not in baseline]
        for relative in mandatory:
            if relative not in affected:
                affected.append(relative)
            cached.pop(relative, None)
        # Drawable means the fingerprint proves this file cannot have moved.
        # That is exactly the set this run is not measuring, which is why a
        # calibration run may not write to the cache: caching the module it just
        # measured would make that module drawable next time, so the runs of a
        # measurement triple would not agree on what they measured and a refusal
        # could be retried away. See commit_state's refusal.
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
        # measured would become cache-valid, hence drawable, and the next run of
        # the same measurement triple would draw a different sample — so a triple
        # would not measure one set and a refusal could be retried away. A
        # calibration run therefore measures, reports, and records nothing.
        raise SelectionError(
            "a calibration run must not advance the cache its own draw depends on"
        )
    rows = read_result_rows(report_path)
    files = set(plan["files"])
    if set(rows) != files:
        raise SelectionError("complete result set does not match the current Lean source set")
    if not excluded <= files:
        raise SelectionError(f"cache exclusion names unknown files: {sorted(excluded - files)}")
    if any(
        row["status"] != "OK" and relative not in excluded
        for relative, row in rows.items()
    ):
        raise SelectionError("refusing to cache a result containing elaboration errors")

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
            "refusing stale cache state"
        )

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
        controls += 1  # a module with no committed row is mandatory, and never a control

        assert {"Blanc/A.lean", "Blanc.lean"} <= set(plan["affected"])
        assert not {"Blanc/A.lean", "Blanc.lean"} & set(calibration["selected"])
        assert calibration["population"] == 8
        assert not set(plan["affected"]) & set(plan["cached"])
        controls += 1  # a module the edit can have reached is measured, never its own control

        assert "Blanc/Removed.lean" not in calibration["selected"]
        controls += 1  # a baseline row whose file is gone is never drawn

        # Two plans over the same unchanged state must agree: that is what
        # makes the runs of a measurement triple measure one set.
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
    """Adjudicate the drawn controls against their committed baseline rows.

    A control is held to the same rule the gate enforces on the rows
    themselves: the factor *and* the absolute floor. Dropping the floor would
    make the smallest band refuse on ordinary scheduler noise — a half-second
    blip on a sub-second file is a large ratio and no real change — and a gate
    that refuses on noise is a gate everyone learns to bypass.
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
    """Render the paste-ready evidence block for the baseline comment.

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
    print("--- calibration evidence (paste into the baseline comment) ---")
    for line in block.split("\n"):
        print(f"# {line}".rstrip())
    print("--- end calibration evidence ---")
    if args.block_out:
        args.block_out.write_text(block + "\n", encoding="utf-8")
    return 1 if summary["refused"] else 0


def command_files(args: argparse.Namespace) -> int:
    plan = read_plan(args.plan)
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
    if plan["reason"]:
        print(
            f"elab selection: {affected} measured, {cached} cache-valid "
            f"({plan['reason']})"
        )
    else:
        print(
            f"elab selection: {affected} measured, {cached} provably unaffected "
            "by content/import-closure fingerprint"
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

    verdict = subparsers.add_parser("calibrate-verdict")
    verdict.add_argument("--plan", type=Path, required=True)
    verdict.add_argument("--report", type=Path, required=True)
    verdict.add_argument("--baseline", type=Path, required=True)
    verdict.add_argument("--fail-factor", type=float, required=True)
    verdict.add_argument("--warn-factor", type=float, required=True)
    verdict.add_argument("--floor", type=float, required=True)
    verdict.add_argument("--block-out", type=Path)
    verdict.set_defaults(function=command_calibrate_verdict)

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
