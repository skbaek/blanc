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
"""

from __future__ import annotations

import argparse
import hashlib
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


def make_plan(
    root: Path,
    state_path: Path,
    environment_id: str,
    force_full: bool = False,
    full_reason: str = "explicit --full",
    require_lake_traces: bool = False,
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

    print(f"OK — elab selection: {controls} invalidation/cache controls passed")
    return 0


def command_plan(args: argparse.Namespace) -> int:
    plan = make_plan(
        args.root,
        args.state,
        args.environment_id,
        force_full=args.full,
        full_reason=args.full_reason,
        require_lake_traces=True,
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
    plan.set_defaults(function=command_plan)

    files = subparsers.add_parser("files")
    files.add_argument("--plan", type=Path, required=True)
    files.add_argument("--affected", action="store_true")
    files.set_defaults(
        function=lambda args: print(
            "\n".join(
                read_plan(args.plan)["affected" if args.affected else "files"]
            )
        )
    )

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
