#!/usr/bin/env python3
"""Compare two validated shared elaboration baselines without changing them.

This is deliberately separate from ``check-elab.sh``.  That gate owns
measurement, host-local cache state, baseline adoption and publication.  This
reader consumes two *explicitly named* shared-baseline records only after it
can reconstruct their Git/object and runtime identities.  It writes one
receipt outside the source worktree and never writes the shared store, a
baseline, or ``.lake`` state.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


COMPARATOR_SCHEMA = 1
STATE_VERSION = 1
STORE_SCHEMA = 1
STORE_DIRECTORY = "blanc-elab-evidence"
STORE_PREFIX = "evidence-stable-host-v2"
TRUST_DOMAIN = "same-git-common-directory"
GLOBAL_INPUTS = (
    "lean-toolchain",
    "lakefile.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "scripts/check-elab.sh",
    "scripts/check-elab-selection.py",
)
REQUIRED_INPUTS = {
    "lean-toolchain",
    "lakefile.lean",
    "lake-manifest.json",
    "scripts/check-elab.sh",
    "scripts/check-elab-selection.py",
}
LEAN_PATHSPECS = ("Blanc/", "Blanc.lean", "Main.lean")
BASE_REF = "main"
SHA256 = re.compile(r"^[0-9a-f]{64}$")
GIT_SHA = re.compile(r"^[0-9a-f]{40}$")
LEAN_VERSION = re.compile(r"Lean \(version ([0-9]+(?:\.[0-9]+)+)(?:[ ,])")
TOOLCHAIN_VERSION = re.compile(r"lean4:v([0-9]+(?:\.[0-9]+)+)")


class CompareError(RuntimeError):
    """The requested comparison has no safe interpretation."""


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def command(root: Path, args: list[str], *, binary: bool = False) -> bytes | str:
    try:
        result = subprocess.run(
            args,
            cwd=root,
            capture_output=True,
            text=not binary,
            check=False,
        )
    except OSError as error:
        raise CompareError(f"cannot run {' '.join(args)}: {error}") from error
    if result.returncode != 0:
        stderr = result.stderr if not binary else result.stderr.decode("utf-8", "replace")
        raise CompareError(
            f"{' '.join(args)} failed: {stderr.strip() or 'no diagnostic'}"
        )
    return result.stdout if binary else result.stdout.strip()


def git(root: Path, args: list[str], *, binary: bool = False) -> bytes | str:
    return command(root, ["git", *args], binary=binary)


def resolve_commit(root: Path, requested: str, label: str) -> str:
    if not GIT_SHA.fullmatch(requested):
        raise CompareError(f"{label} must be a full 40-character Git commit identity")
    resolved = str(git(root, ["rev-parse", "--verify", f"{requested}^{{commit}}"]))
    if resolved != requested:
        raise CompareError(f"{label} does not resolve to its exact requested identity")
    return resolved


def blob(root: Path, commit: str, relative: str) -> bytes | None:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode == 0:
        return result.stdout
    if result.returncode == 128 and b"does not exist" in result.stderr:
        return None
    raise CompareError(
        f"cannot read immutable input {relative} at {commit[:12]}: "
        f"{result.stderr.decode('utf-8', 'replace').strip() or 'no diagnostic'}"
    )


def source_tree(root: Path, commit: str) -> dict[str, str]:
    raw = git(root, ["ls-tree", "-r", "-z", commit], binary=True)
    assert isinstance(raw, bytes)
    result: dict[str, str] = {}
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        try:
            metadata, encoded_path = entry.split(b"\t", 1)
            _mode, kind, object_id = metadata.split(b" ", 2)
            relative = encoded_path.decode("utf-8")
        except (ValueError, UnicodeDecodeError) as error:
            raise CompareError(f"cannot parse Git tree entry at {commit[:12]}") from error
        included = (
            relative in {"Blanc.lean", "Main.lean"}
            or (relative.startswith("Blanc/") and relative.endswith(".lean"))
        )
        if not included:
            continue
        if kind != b"blob" or not re.fullmatch(r"[0-9a-f]{40}", object_id.decode("ascii")):
            raise CompareError(f"Lean corpus entry is not an ordinary blob: {relative}")
        if relative in result:
            raise CompareError(f"duplicate Lean corpus path in Git tree: {relative}")
        result[relative] = object_id.decode("ascii")
    if not result:
        raise CompareError(f"immutable source {commit[:12]} contains no Blanc Lean corpus")
    return result


def inputs_at(root: Path, commit: str) -> dict[str, bytes | None]:
    values = {relative: blob(root, commit, relative) for relative in GLOBAL_INPUTS}
    missing = sorted(relative for relative in REQUIRED_INPUTS if values[relative] is None)
    if missing:
        raise CompareError(
            f"immutable source {commit[:12]} lacks required measurement input(s): "
            + ", ".join(missing)
        )
    return values


def environment_fingerprint(inputs: dict[str, bytes | None], lean_stdout: str) -> str:
    digest = hashlib.sha256()
    digest.update(f"blanc-elab-state-v{STATE_VERSION}\0".encode("utf-8"))
    digest.update(lean_stdout.encode("utf-8"))
    digest.update(b"\0")
    for relative in GLOBAL_INPUTS:
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(inputs[relative] if inputs[relative] is not None else b"<absent>")
        digest.update(b"\0")
    return digest.hexdigest()


def load_host_identity(root: Path) -> str:
    """Use the existing gate-cache host authority, never an option override."""

    script = root / "scripts/gate-cache.py"
    if not script.is_file():
        raise CompareError("registered stable-host identity provider is absent")
    script_directory = str(script.parent)
    if script_directory not in sys.path:
        sys.path.insert(0, script_directory)
    spec = importlib.util.spec_from_file_location("blanc_elab_migration_host", script)
    if spec is None or spec.loader is None:
        raise CompareError("cannot load registered stable-host identity provider")
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
        identity = module.host_identity()
    except Exception as error:  # provider failures cannot receive a default identity
        raise CompareError(f"registered stable-host identity provider failed: {error}") from error
    if not isinstance(identity, str) or not identity:
        raise CompareError("registered stable-host identity provider returned no identity")
    return identity


def runtime_lean_stdout(root: Path) -> str:
    """Read the active runtime identity with the same command the gate uses."""

    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--version"],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        raise CompareError(f"cannot obtain active Lean runtime identity: {error}") from error
    stdout = result.stdout.rstrip("\r\n")
    if result.returncode != 0 or not stdout:
        raise CompareError(
            "cannot obtain active Lean runtime identity: "
            + (result.stderr.strip() or "lake env lean --version failed")
        )
    if not LEAN_VERSION.search(stdout):
        raise CompareError("active Lean runtime identity is not recognizable version stdout")
    return stdout


def require_runtime_matches_toolchain(toolchain: bytes, lean_stdout: str) -> None:
    try:
        declared = toolchain.decode("utf-8")
    except UnicodeDecodeError as error:
        raise CompareError("lean-toolchain is not UTF-8") from error
    declared_match = TOOLCHAIN_VERSION.search(declared)
    actual_match = LEAN_VERSION.search(lean_stdout)
    if declared_match is None or actual_match is None:
        raise CompareError("cannot compare declared Lean toolchain with active version stdout")
    if declared_match.group(1) != actual_match.group(1):
        raise CompareError(
            "active Lean version stdout does not match immutable lean-toolchain "
            f"({actual_match.group(1)} != {declared_match.group(1)})"
        )


def valid_number(value: Any, *, positive: bool = False) -> bool:
    try:
        number = float(value)
    except (TypeError, ValueError):
        return False
    return math.isfinite(number) and (number > 0 if positive else number >= 0)


def validate_record(record: Any) -> None:
    if not isinstance(record, dict) or set(record) != {
        "origin", "environment", "digest", "rows", "payload", "utc"
    }:
        raise CompareError("shared baseline record has an incompatible schema")
    if not GIT_SHA.fullmatch(record["origin"]):
        raise CompareError("shared baseline record has an invalid origin")
    if not SHA256.fullmatch(record["environment"]):
        raise CompareError("shared baseline record has an invalid environment")
    if not SHA256.fullmatch(record["digest"]):
        raise CompareError("shared baseline record has an invalid payload digest")
    if not isinstance(record["rows"], int) or record["rows"] <= 0:
        raise CompareError("shared baseline record has an invalid row count")
    if not isinstance(record["payload"], str) or not record["payload"]:
        raise CompareError("shared baseline record has no payload")
    if not isinstance(record["utc"], str) or not record["utc"]:
        raise CompareError("shared baseline record has an invalid UTC field")
    if sha256_bytes(record["payload"].encode("utf-8")) != record["digest"]:
        raise CompareError("shared baseline record payload digest mismatch")


def validate_store(value: Any, host: str) -> list[dict[str, Any]]:
    if not isinstance(value, dict) or set(value) != {
        "schema", "trust_domain", "host", "measurements", "baselines"
    }:
        raise CompareError("shared timing store has an incompatible schema")
    if value["schema"] != STORE_SCHEMA or value["trust_domain"] != TRUST_DOMAIN:
        raise CompareError("shared timing store schema/trust domain is incompatible")
    if value["host"] != host:
        raise CompareError("shared timing store does not match registered stable-host identity")
    if not isinstance(value["measurements"], dict) or not isinstance(value["baselines"], list):
        raise CompareError("shared timing store tables are invalid")
    for environment, table in value["measurements"].items():
        if not SHA256.fullmatch(environment) or not isinstance(table, dict):
            raise CompareError("shared measurement table is invalid")
        for fingerprint, row in table.items():
            if (
                not SHA256.fullmatch(fingerprint)
                or not isinstance(row, dict)
                or set(row) != {"time", "commit", "utc"}
                or not valid_number(row["time"])
                or not isinstance(row["commit"], str)
                or not isinstance(row["utc"], str)
            ):
                raise CompareError("shared measurement record is invalid")
    for record in value["baselines"]:
        validate_record(record)
    return value["baselines"]


def shared_store(root: Path, host: str) -> tuple[Path, list[dict[str, Any]]]:
    common_raw = str(git(root, ["rev-parse", "--path-format=absolute", "--git-common-dir"]))
    common = Path(common_raw).resolve()
    path = common / STORE_DIRECTORY / f"{STORE_PREFIX}-{host}.json"
    if not path.is_file():
        raise CompareError(f"shared stable-host timing store is absent: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CompareError(f"cannot read shared stable-host timing store: {error}") from error
    return path, validate_store(value, host)


def select_record(
    records: list[dict[str, Any]], origin: str, digest: str, environment: str, label: str
) -> dict[str, Any]:
    if not GIT_SHA.fullmatch(origin) or not SHA256.fullmatch(digest) or not SHA256.fullmatch(environment):
        raise CompareError(f"{label} record selector must use full origin, digest and environment identities")
    selected = [
        record
        for record in records
        if record["origin"] == origin
        and record["digest"] == digest
        and record["environment"] == environment
    ]
    if len(selected) != 1:
        raise CompareError(
            f"{label} shared baseline selector matched {len(selected)} records; expected exactly one"
        )
    return selected[0]


def parse_baseline(record: dict[str, Any], corpus: dict[str, str], label: str) -> dict[str, float]:
    rows: dict[str, float] = {}
    for line_number, raw in enumerate(record["payload"].splitlines(), start=1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3 or fields[0] != "OK":
            raise CompareError(f"{label} baseline has malformed/non-green row {line_number}")
        path = fields[2]
        if not path or path.startswith("/") or "\\" in path or any(part == ".." for part in path.split("/")):
            raise CompareError(f"{label} baseline has unsafe source path at row {line_number}")
        if path in rows:
            raise CompareError(f"{label} baseline has duplicate row for {path}")
        if not valid_number(fields[1], positive=True):
            raise CompareError(f"{label} baseline has non-finite/non-positive time at row {line_number}")
        rows[path] = float(fields[1])
    if len(rows) != record["rows"]:
        raise CompareError(f"{label} baseline row count does not match its record")
    if set(rows) != set(corpus):
        missing = sorted(set(corpus) - set(rows))
        extra = sorted(set(rows) - set(corpus))
        raise CompareError(
            f"{label} baseline does not cover its exact complete Lean corpus "
            f"(missing={missing}, extra={extra})"
        )
    return rows


def jaune_from_lakefile(contents: bytes, label: str) -> str:
    try:
        text = contents.decode("utf-8")
    except UnicodeDecodeError as error:
        raise CompareError(f"{label} lakefile.lean is not UTF-8") from error
    marker = re.search(r"(?m)^require[ \t]+jaune[ \t]+from[ \t]+git[ \t]*\n", text)
    if marker is None:
        raise CompareError(f"{label} lakefile.lean has no Git jaune requirement")
    next_requirement = re.search(r"(?m)^require[ \t]+", text[marker.end() :])
    stanza_end = marker.end() + (next_requirement.start() if next_requirement else len(text))
    revisions = re.findall(r'@\s*"([0-9a-f]{40})"', text[marker.end() : stanza_end])
    if len(revisions) != 1:
        raise CompareError(f"{label} lakefile.lean has no unique full jaune revision")
    return revisions[0]


def jaune_from_manifest(contents: bytes, label: str) -> tuple[str, dict[str, Any]]:
    try:
        value = json.loads(contents.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CompareError(f"{label} lake-manifest.json is invalid JSON") from error
    if not isinstance(value, dict) or not isinstance(value.get("packages"), list):
        raise CompareError(f"{label} lake-manifest.json has no package list")
    matches = [entry for entry in value["packages"] if isinstance(entry, dict) and entry.get("name") == "jaune"]
    if len(matches) != 1:
        raise CompareError(f"{label} lake-manifest.json has no unique jaune package")
    package = matches[0]
    revision = package.get("rev")
    input_revision = package.get("inputRev")
    if not isinstance(revision, str) or not GIT_SHA.fullmatch(revision) or revision != input_revision:
        raise CompareError(f"{label} lake-manifest.json has inconsistent jaune revisions")
    return revision, value


def require_only_jaune_transition(
    old: dict[str, bytes | None], new: dict[str, bytes | None], old_jaune: str, new_jaune: str
) -> None:
    for relative in ("lean-toolchain", "lakefile.toml", "scripts/check-elab.sh", "scripts/check-elab-selection.py"):
        if old[relative] != new[relative]:
            raise CompareError(f"measurement protocol/configuration input changed: {relative}")
    old_lakefile = old["lakefile.lean"]
    new_lakefile = new["lakefile.lean"]
    old_manifest = old["lake-manifest.json"]
    new_manifest = new["lake-manifest.json"]
    assert old_lakefile is not None and new_lakefile is not None
    assert old_manifest is not None and new_manifest is not None
    if jaune_from_lakefile(old_lakefile, "reference") != old_jaune:
        raise CompareError("reference lakefile does not carry the declared old Jaune identity")
    if jaune_from_lakefile(new_lakefile, "candidate") != new_jaune:
        raise CompareError("candidate lakefile does not carry the declared new Jaune identity")
    old_manifest_jaune, _ = jaune_from_manifest(old_manifest, "reference")
    new_manifest_jaune, _ = jaune_from_manifest(new_manifest, "candidate")
    if old_manifest_jaune != old_jaune or new_manifest_jaune != new_jaune:
        raise CompareError("lake manifests do not carry the declared old/new Jaune transition")
    if old_lakefile.count(old_jaune.encode("ascii")) != 1 or new_lakefile.count(new_jaune.encode("ascii")) != 1:
        raise CompareError("lakefile Jaune transition is not unique")
    if old_lakefile.replace(old_jaune.encode("ascii"), new_jaune.encode("ascii")) != new_lakefile:
        raise CompareError("lakefile carries undeclared configuration changes beyond Jaune")
    if old_manifest.replace(old_jaune.encode("ascii"), new_jaune.encode("ascii")) != new_manifest:
        raise CompareError("lake manifest carries undeclared configuration changes beyond Jaune")


def timing_thresholds(protocol: bytes) -> tuple[float, float]:
    """Read the exact regression rule from the immutable gate protocol.

    The reference and candidate protocol blobs were already required to be
    byte-identical. Reading the constants rather than carrying a second pair
    here prevents an unchanged future protocol from being reported under an
    obsolete comparator label.
    """

    try:
        text = protocol.decode("utf-8")
    except UnicodeDecodeError as error:
        raise CompareError("timing protocol is not UTF-8") from error
    values: dict[str, float] = {}
    for name in ("DRIFT_FACTOR", "DRIFT_FLOOR"):
        matches = re.findall(rf'(?m)^{name}="([^"\r\n]+)"$', text)
        if len(matches) != 1 or not valid_number(matches[0], positive=True):
            raise CompareError(f"timing protocol has no unique finite positive {name}")
        values[name] = float(matches[0])
    return values["DRIFT_FACTOR"], values["DRIFT_FLOOR"]


def git_is_ancestor(root: Path, older: str, newer: str) -> bool:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", older, newer],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode not in {0, 1}:
        raise CompareError("cannot determine source ancestry")
    return result.returncode == 0


def normalized_origin(root: Path, candidate: str) -> str:
    base = str(git(root, ["merge-base", candidate, BASE_REF]))
    result = subprocess.run(
        ["git", "diff", "--quiet", base, candidate, "--", *LEAN_PATHSPECS],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode == 0:
        return base
    if result.returncode == 1:
        return candidate
    raise CompareError("cannot reproduce registered baseline-origin normalization")


def validate_candidate_origin(
    root: Path, candidate: str, origin: str, candidate_corpus: dict[str, str], candidate_inputs: dict[str, bytes | None]
) -> bool:
    if origin == candidate:
        return False
    if normalized_origin(root, candidate) != origin:
        raise CompareError("candidate record origin is neither exact HEAD nor registered normalization")
    origin_corpus = source_tree(root, origin)
    origin_inputs = inputs_at(root, origin)
    if origin_corpus != candidate_corpus:
        raise CompareError("normalized candidate origin does not have the exact complete Lean corpus/blob identity")
    if origin_inputs != candidate_inputs:
        raise CompareError("normalized candidate origin does not preserve GLOBAL_INPUTS byte equality")
    return True


def outside_root(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return False
    except ValueError:
        return True


def atomic_json(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise CompareError(f"receipt already exists: {path}")
    if not path.parent.is_dir():
        raise CompareError(f"receipt parent directory does not exist: {path.parent}")
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


def compare_rows(
    old_rows: dict[str, float],
    new_rows: dict[str, float],
    old_corpus: dict[str, str],
    new_corpus: dict[str, str],
    factor: float,
    floor: float,
) -> tuple[list[dict[str, Any]], list[str]]:
    rows: list[dict[str, Any]] = []
    regressions: list[str] = []
    for path in sorted(set(old_rows) & set(new_rows)):
        old_seconds = old_rows[path]
        new_seconds = new_rows[path]
        regression = new_seconds > old_seconds * factor and new_seconds > old_seconds + floor
        if regression:
            regressions.append(path)
        rows.append(
            {
                "path": path,
                "source_unit": "CHANGED" if old_corpus[path] != new_corpus[path] else "UNCHANGED",
                "old_seconds": old_seconds,
                "candidate_seconds": new_seconds,
                "delta_seconds": new_seconds - old_seconds,
                "ratio": new_seconds / old_seconds,
                "comparison": "REGRESSION" if regression else "WITHIN_EXISTING_THRESHOLD",
            }
        )
    for path in sorted(set(new_rows) - set(old_rows)):
        rows.append(
            {
                "path": path,
                "source_unit": "ADDED",
                "candidate_seconds": new_rows[path],
                "comparison": "FIRST_MEASUREMENT_UNREFERENCED",
            }
        )
    for path in sorted(set(old_rows) - set(new_rows)):
        rows.append(
            {
                "path": path,
                "source_unit": "REMOVED",
                "old_seconds": old_rows[path],
                "comparison": "REMOVED_UNREFERENCED",
            }
        )
    return rows, regressions


def compare(args: argparse.Namespace) -> int:
    root = args.root.resolve()
    if not root.is_dir():
        raise CompareError(f"candidate root does not exist: {root}")
    if not outside_root(args.receipt, root):
        raise CompareError("receipt must be outside the candidate source worktree")
    if str(git(root, ["status", "--porcelain"])):
        raise CompareError("candidate tree is not clean")
    candidate = resolve_commit(root, args.candidate, "candidate")
    head = str(git(root, ["rev-parse", "HEAD"]))
    if head != candidate:
        raise CompareError("candidate identity is not the clean worktree HEAD")
    host = load_host_identity(root)
    store_path, records = shared_store(root, host)
    reference = select_record(
        records, args.reference_origin, args.reference_digest, args.reference_environment, "reference"
    )
    candidate_record = select_record(
        records, args.candidate_origin, args.candidate_digest, args.candidate_environment, "candidate"
    )
    reference_origin = resolve_commit(root, reference["origin"], "reference record origin")
    candidate_origin = resolve_commit(root, candidate_record["origin"], "candidate record origin")
    if not git_is_ancestor(root, reference_origin, candidate):
        raise CompareError("reference source identity is not an ancestor of the candidate")
    if not GIT_SHA.fullmatch(args.old_jaune) or not GIT_SHA.fullmatch(args.new_jaune) or args.old_jaune == args.new_jaune:
        raise CompareError("old/new Jaune identities must be distinct full Git revisions")
    old_inputs = inputs_at(root, reference_origin)
    candidate_inputs = inputs_at(root, candidate)
    require_only_jaune_transition(old_inputs, candidate_inputs, args.old_jaune, args.new_jaune)
    assert candidate_inputs["scripts/check-elab.sh"] is not None
    factor, floor = timing_thresholds(candidate_inputs["scripts/check-elab.sh"])
    lean_stdout = runtime_lean_stdout(root)
    assert old_inputs["lean-toolchain"] is not None
    require_runtime_matches_toolchain(old_inputs["lean-toolchain"], lean_stdout)
    if old_inputs["lean-toolchain"] != candidate_inputs["lean-toolchain"]:
        raise CompareError("immutable lean-toolchain differs across the comparison")
    old_environment = environment_fingerprint(old_inputs, lean_stdout)
    candidate_environment = environment_fingerprint(candidate_inputs, lean_stdout)
    if old_environment != reference["environment"]:
        raise CompareError("reference stored environment cannot be reproduced from immutable Git inputs and active Lean stdout")
    if candidate_environment != candidate_record["environment"]:
        raise CompareError("candidate stored environment cannot be reproduced from immutable Git inputs and active Lean stdout")
    if old_environment == candidate_environment:
        raise CompareError("Jaune transition did not produce distinct environment identities")
    old_corpus = source_tree(root, reference_origin)
    candidate_corpus = source_tree(root, candidate)
    normalized = validate_candidate_origin(
        root, candidate, candidate_origin, candidate_corpus, candidate_inputs
    )
    old_rows = parse_baseline(reference, old_corpus, "reference")
    candidate_rows = parse_baseline(candidate_record, candidate_corpus, "candidate")
    comparison_rows, regressions = compare_rows(
        old_rows, candidate_rows, old_corpus, candidate_corpus, factor, floor
    )
    common_count = len(set(old_rows) & set(candidate_rows))
    candidate_only_count = len(set(candidate_rows) - set(old_rows))
    reference_only_count = len(set(old_rows) - set(candidate_rows))
    assert candidate_inputs["lean-toolchain"] is not None
    assert candidate_inputs["scripts/check-elab.sh"] is not None
    assert candidate_inputs["scripts/check-elab-selection.py"] is not None
    receipt = {
        "schema": COMPARATOR_SCHEMA,
        "kind": "blanc-elab-migration-comparison",
        "result": "REGRESSION" if regressions else "PASS",
        "threshold": {"factor_strictly_greater_than": factor, "seconds_strictly_greater_than": floor},
        "store": {"path": str(store_path), "host": host, "trust_domain": TRUST_DOMAIN},
        "runtime": {"lean_stdout": lean_stdout, "lean_stdout_sha256": sha256_bytes(lean_stdout.encode("utf-8"))},
        "protocol": {
            "lean_toolchain_sha256": sha256_bytes(candidate_inputs["lean-toolchain"]),
            "check_elab_sha256": sha256_bytes(candidate_inputs["scripts/check-elab.sh"]),
            "selection_sha256": sha256_bytes(candidate_inputs["scripts/check-elab-selection.py"]),
        },
        "reference": {
            "origin": reference_origin,
            "digest": reference["digest"],
            "environment": reference["environment"],
            "rows": len(old_rows),
            "jaune": args.old_jaune,
        },
        "candidate": {
            "head": candidate,
            "published_origin": candidate_origin,
            "normalized_origin": normalized,
            "digest": candidate_record["digest"],
            "environment": candidate_record["environment"],
            "rows": len(candidate_rows),
            "jaune": args.new_jaune,
        },
        "counts": {
            "common": common_count,
            "candidate_only_unreferenced": candidate_only_count,
            "reference_only_removed": reference_only_count,
            "regressions": len(regressions),
        },
        "rows": comparison_rows,
        "limitations": [
            "Shared records establish clean/full/green publication and exact stored identities.",
            "They do not distinguish genesis from rebase or retain a rich cache/runtime transcript.",
            "The normal-genesis command transcript remains separate final-B evidence.",
        ],
    }
    atomic_json(args.receipt, receipt)
    if regressions:
        print(
            "REGRESSION — elaboration migration comparison: "
            f"{len(regressions)} common row(s) exceeded both existing thresholds; receipt {args.receipt}"
        )
        return 1
    print(
        "OK — elaboration migration comparison: "
        f"{common_count} common rows, {candidate_only_count} candidate-only unreferenced, "
        f"{reference_only_count} reference-only removed; receipt {args.receipt}"
    )
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--root", type=Path, required=True, help="clean Blanc candidate worktree")
    result.add_argument("--candidate", required=True, help="full candidate HEAD SHA")
    result.add_argument("--reference-origin", required=True)
    result.add_argument("--reference-digest", required=True)
    result.add_argument("--reference-environment", required=True)
    result.add_argument("--candidate-origin", required=True)
    result.add_argument("--candidate-digest", required=True)
    result.add_argument("--candidate-environment", required=True)
    result.add_argument("--old-jaune", required=True)
    result.add_argument("--new-jaune", required=True)
    result.add_argument("--receipt", type=Path, required=True, help="new receipt outside the worktree")
    return result


def main(argv: list[str]) -> int:
    try:
        return compare(parser().parse_args(argv))
    except CompareError as error:
        print(f"SETUP — elaboration migration comparison: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
