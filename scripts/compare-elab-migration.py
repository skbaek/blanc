#!/usr/bin/env python3
"""Compare two validated shared elaboration baselines without changing them.

This is deliberately separate from ``check-elab.sh``.  That gate owns
measurement, host-local cache state, baseline adoption and publication.  This
reader consumes two *explicitly named* shared-baseline records only after it
can reconstruct their Git/object and runtime identities.  It writes one
receipt outside the source worktree and never writes the shared store, a
baseline, or ``.lake`` state.

ONE READER

There is one read-only evidence reader and identity implementation for the
timing store, and it is the timing gate's own selector,
``scripts/check-elab-selection.py``: its store path and constants, its store,
record and baseline validation, its baseline-payload parser, its environment
fingerprint recipe and its origin normalization.  This comparator imports
that module and consumes those functions; it implements none of them a
second time.  What it adds is *comparison policy*, which is different from
the gate's *reuse policy*: any reader refusal is a refusal here (the gate
would fall back to measuring), the two records are selected by exact
identity, both payloads must cover their exact Lean corpus, and only the
Jaune pin may differ between the two measurement environments.

The environment identity of an immutable record is reproduced by staging the
record's Git blobs into a scratch directory and calling the selector's own
``environment_fingerprint`` on it, so the recipe cannot drift from the one
that wrote the record without this reader noticing.  The selector's bytes are
themselves one of the fingerprinted inputs, so a selector edit is a protocol
change that makes records incomparable; this comparator therefore leaves the
selector untouched and only reads it.

The stable-host identity provider is loaded from the *candidate* root, not
from this reader's own directory: the records under comparison were written
by that candidate's provider, and a fixture may supply its own.
"""

from __future__ import annotations

import argparse
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

# Reading provenance must never leave bytecode in a candidate worktree; the
# process-local policy covers the selector and provider imports below.
sys.dont_write_bytecode = True

COMPARATOR_SCHEMA = 1
HERE = Path(__file__).resolve().parent
REQUIRED_INPUTS = {
    "lean-toolchain",
    "lakefile.lean",
    "lake-manifest.json",
    "scripts/check-elab.sh",
    "scripts/check-elab-selection.py",
}
SHA256 = re.compile(r"^[0-9a-f]{64}$")
GIT_SHA = re.compile(r"^[0-9a-f]{40}$")
LEAN_VERSION = re.compile(r"Lean \(version ([0-9]+(?:\.[0-9]+)+)(?:[ ,])")
TOOLCHAIN_VERSION = re.compile(r"lean4:v([0-9]+(?:\.[0-9]+)+)")


class CompareError(RuntimeError):
    """The requested comparison has no safe interpretation."""


def load_reader() -> Any:
    """Import the timing gate's selector as the one evidence reader."""

    path = HERE / "check-elab-selection.py"
    if not path.is_file():
        raise CompareError(f"timing evidence reader is absent: {path}")
    spec = importlib.util.spec_from_file_location("blanc_elab_selection_reader", path)
    if spec is None or spec.loader is None:
        raise CompareError("cannot load the timing evidence reader")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    try:
        spec.loader.exec_module(module)
    except Exception as error:  # a broken reader cannot receive a default
        raise CompareError(f"timing evidence reader failed to load: {error}") from error
    return module


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


def inputs_at(reader: Any, root: Path, commit: str) -> dict[str, bytes | None]:
    values = {relative: blob(root, commit, relative) for relative in reader.GLOBAL_INPUTS}
    missing = sorted(relative for relative in REQUIRED_INPUTS if values.get(relative) is None)
    if missing:
        raise CompareError(
            f"immutable source {commit[:12]} lacks required measurement input(s): "
            + ", ".join(missing)
        )
    return values


def environment_from_blobs(
    reader: Any, inputs: dict[str, bytes | None], lean_stdout: str
) -> str:
    """Reproduce a record's environment with the selector's own recipe.

    The immutable blobs are staged into a scratch directory laid out like a
    checkout and handed to `environment_fingerprint`, the function that wrote
    the record's environment field in the first place.  An absent input is
    simply not staged, which is what the recipe hashes as absent.
    """

    with tempfile.TemporaryDirectory(prefix="blanc-elab-compare-inputs-") as staged:
        base = Path(staged)
        for relative, contents in inputs.items():
            if contents is None:
                continue
            target = base / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(contents)
        return reader.environment_fingerprint(base, lean_stdout)


def load_host_identity(root: Path) -> str:
    """Use the candidate's registered gate-cache host authority, never an option."""

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


def shared_records(reader: Any, root: Path, host: str) -> tuple[Path, list[dict[str, Any]]]:
    """The store's baseline records, through the one reader, refusing on any reason.

    The gate treats a reader reason as "measure instead"; a comparison has
    nothing to fall back to, so every reason is a refusal here.
    """

    path = reader.shared_git_common_dir(root) / reader.SHARED_EVIDENCE_DIRNAME / (
        f"{reader.SHARED_EVIDENCE_FILENAME_PREFIX}-{host}.json"
    )
    try:
        store, reason, _writable = reader.read_shared_store(path, host)
    except reader.SelectionError as error:
        raise CompareError(f"shared stable-host timing store refused: {error}") from error
    if reason is not None:
        raise CompareError(f"shared stable-host timing store refused: {reason} ({path})")
    return path, list(store["baselines"])


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


def parse_baseline(
    reader: Any, record: dict[str, Any], corpus: dict[str, str], label: str
) -> dict[str, float]:
    """The reader parses the rows; comparison policy then holds them to the corpus."""

    try:
        rows = reader.validate_shared_baseline_payload(record["payload"])
    except reader.SelectionError as error:
        raise CompareError(f"{label} baseline payload refused: {error}") from error
    for path in rows:
        if not path or path.startswith("/") or "\\" in path or any(part == ".." for part in path.split("/")):
            raise CompareError(f"{label} baseline has unsafe source path {path!r}")
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


def validate_candidate_origin(
    reader: Any,
    root: Path,
    candidate: str,
    origin: str,
    candidate_corpus: dict[str, str],
    candidate_inputs: dict[str, bytes | None],
) -> bool:
    """A published origin is exact HEAD or the selector's own normalization."""

    if origin == candidate:
        return False
    if reader.baseline_origin_for_publish(root, candidate) != origin:
        raise CompareError("candidate record origin is neither exact HEAD nor registered normalization")
    origin_corpus = source_tree(root, origin)
    origin_inputs = inputs_at(reader, root, origin)
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


def write_receipt(path: Path, value: dict[str, Any]) -> None:
    """The one write: a new receipt outside the worktree, never a replacement."""

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
    reader = load_reader()
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
    store_path, records = shared_records(reader, root, host)
    reference = select_record(
        records, args.reference_origin, args.reference_digest, args.reference_environment, "reference"
    )
    candidate_record = select_record(
        records, args.candidate_origin, args.candidate_digest, args.candidate_environment, "candidate"
    )
    reference_origin = resolve_commit(root, reference["origin"], "reference record origin")
    candidate_origin = resolve_commit(root, candidate_record["origin"], "candidate record origin")
    if not reader.git_success(root, ["merge-base", "--is-ancestor", reference_origin, candidate]):
        raise CompareError("reference source identity is not an ancestor of the candidate")
    if not GIT_SHA.fullmatch(args.old_jaune) or not GIT_SHA.fullmatch(args.new_jaune) or args.old_jaune == args.new_jaune:
        raise CompareError("old/new Jaune identities must be distinct full Git revisions")
    old_inputs = inputs_at(reader, root, reference_origin)
    candidate_inputs = inputs_at(reader, root, candidate)
    require_only_jaune_transition(old_inputs, candidate_inputs, args.old_jaune, args.new_jaune)
    assert candidate_inputs["scripts/check-elab.sh"] is not None
    factor, floor = timing_thresholds(candidate_inputs["scripts/check-elab.sh"])
    lean_stdout = runtime_lean_stdout(root)
    assert old_inputs["lean-toolchain"] is not None
    require_runtime_matches_toolchain(old_inputs["lean-toolchain"], lean_stdout)
    if old_inputs["lean-toolchain"] != candidate_inputs["lean-toolchain"]:
        raise CompareError("immutable lean-toolchain differs across the comparison")
    old_environment = environment_from_blobs(reader, old_inputs, lean_stdout)
    candidate_environment = environment_from_blobs(reader, candidate_inputs, lean_stdout)
    if old_environment != reference["environment"]:
        raise CompareError("reference stored environment cannot be reproduced from immutable Git inputs and active Lean stdout")
    if candidate_environment != candidate_record["environment"]:
        raise CompareError("candidate stored environment cannot be reproduced from immutable Git inputs and active Lean stdout")
    if old_environment == candidate_environment:
        raise CompareError("Jaune transition did not produce distinct environment identities")
    old_corpus = source_tree(root, reference_origin)
    candidate_corpus = source_tree(root, candidate)
    normalized = validate_candidate_origin(
        reader, root, candidate, candidate_origin, candidate_corpus, candidate_inputs
    )
    old_rows = parse_baseline(reader, reference, old_corpus, "reference")
    candidate_rows = parse_baseline(reader, candidate_record, candidate_corpus, "candidate")
    comparison_rows, regressions = compare_rows(
        old_rows, candidate_rows, old_corpus, candidate_corpus, factor, floor
    )
    common_count = len(set(old_rows) & set(candidate_rows))
    candidate_only_count = len(set(candidate_rows) - set(old_rows))
    reference_only_count = len(set(old_rows) - set(candidate_rows))
    assert candidate_inputs["lean-toolchain"] is not None
    assert candidate_inputs["scripts/check-elab.sh"] is not None
    assert candidate_inputs["scripts/check-elab-selection.py"] is not None
    sha256 = reader.sha256_bytes
    receipt = {
        "schema": COMPARATOR_SCHEMA,
        "kind": "blanc-elab-migration-comparison",
        "result": "REGRESSION" if regressions else "PASS",
        "threshold": {"factor_strictly_greater_than": factor, "seconds_strictly_greater_than": floor},
        "store": {"path": str(store_path), "host": host, "trust_domain": reader.SHARED_TRUST_DOMAIN},
        "runtime": {"lean_stdout": lean_stdout, "lean_stdout_sha256": sha256(lean_stdout.encode("utf-8"))},
        "protocol": {
            "lean_toolchain_sha256": sha256(candidate_inputs["lean-toolchain"]),
            "check_elab_sha256": sha256(candidate_inputs["scripts/check-elab.sh"]),
            "selection_sha256": sha256(candidate_inputs["scripts/check-elab-selection.py"]),
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
    write_receipt(args.receipt, receipt)
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
