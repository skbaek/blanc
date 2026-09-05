#!/usr/bin/env python3
"""Content-valid verdict reuse for Blanc's verification gates.

WHY
---

`scripts/GATES.md` used to say that a gate's verdict is inherited only by
*commit identity*.  That rule is safe but blunt: correcting a count in a
comment moved the commit, so the WETH, Lido, occurrence, settlement and
fixture evidence produced ten minutes earlier stopped counting even though not
one input any of those gates reads had moved.  The cost recurs on every
checkpoint and grows with the catalogue.

This module replaces commit identity with **gate-relevant content identity**.
A gate's verdict may be credited to a candidate without re-executing it only
when every mutable input that gate actually consumes hashes to exactly what it
hashed during an earlier successful, non-drifting execution.  Commit and
timestamp become provenance; they are validity inputs only for a gate that
semantically consumes them (`--base main`, an expiring exception).

WHAT MAKES IT SOUND
-------------------

*Lean closure is delegated, not duplicated.*  Blanc has 150 modules and no
hand-maintained import graph could be trusted to stay right.  After `lake
build` brings a target current, Lake's own trace records a `depHash` covering
that module's source, the Lean version and options, and every transitive
imported artifact including external packages.  A gate that elaborates Lean
therefore fingerprints `depHash`, not an import walk of our own invention.  A
gate that reads `.lean` files as *text* fingerprints the text, because that is
a different claim channel and an `.olean` cannot witness it.

*Unknown means run.*  Every component computation either produces a digest or
raises `Unresolvable`.  There is no default, no "assume unchanged", and no
whole-repository escape hash.  An unresolvable component means the gate has no
fingerprint at all, so it cannot match any record and must execute.

*Only completed successful evidence is reusable.*  A record is written only
after the gate exits zero, printed each of its declared terminal summary lines
exactly once, and the fingerprint recomputed *after* execution still equals
the one planned before it.

*No bypass.*  There is deliberately no `--force`.  `--fresh` adds execution;
nothing removes it.

Verdict evidence lives below Git's common directory, so it is shared only by
worktrees of one physical clone.  It is disposable, is never committed, and
may be deleted at any time: deleting it costs time and cannot cost correctness.
Dirty worktrees may consume matching evidence but never admit fresh verdicts
to the shared store. Candidate reports and exact build certificates remain
worktree-local under `.lake/`.

What the cache validation does and does not do.  `read_cache` rejects any state
whose *shape* is wrong -- a foreign schema, a malformed table, a record with no
fingerprint, a record claiming a failing verdict -- and an empty cache costs a
run.  It does not distinguish an earned record from a well-formed one somebody
wrote by hand, and it is not trying to: signing the cache against its own
author is out of scope here, and the file is local, gitignored, and read only
by this runner.  The rule is therefore that nothing but this runner may write
it -- not that a forgery would be detected.
"""

from __future__ import annotations

import argparse
import ast
import datetime as dt
import fnmatch
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Iterable

from gate_cache_lock import acquire_lock, read_lock_pid, release_lock
from gate_cache_t8n_root import (
    T8N_TARGET_ROOT,
    T8nPythonBaseError,
    resolve_eels_python_base,
    resolve_t8n_python_base,
)

SCHEMA_VERSION = 1
EVIDENCE_SCHEMA_VERSION = 2

ROOT = Path(__file__).resolve().parent.parent

# Every path is derived from a root the caller passes, so the control suite can
# drive the whole engine against a scratch repository instead of asserting on a
# reimplementation of it.
REGISTRY_RELATIVE = "scripts/gate-registry.json"
REPORT_RELATIVE = ".lake/gate-report.md"
MANIFEST_RELATIVE = ".lake/gate-manifest.json"
BUILD_CERTIFICATE_RELATIVE = ".lake/blanc-build-certificate.json"
SHARED_STATE_RELATIVE = "blanc-gate-evidence"
BUILD_CERTIFICATE_SCHEMA = 2


def registry_path(root: Path) -> Path:
    return root / REGISTRY_RELATIVE


def git_common_dir(root: Path) -> Path:
    """Resolve the physical repository identity shared by all its worktrees."""

    result = subprocess.run(
        ["git", "rev-parse", "--path-format=absolute", "--git-common-dir"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        raise GateCacheError(
            "cannot resolve Git's common directory; shared evidence requires a worktree "
            "of one physical repository"
        )
    path = Path(result.stdout.strip())
    if not path.is_absolute():
        path = root / path
    try:
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise GateCacheError(f"cannot resolve Git common directory {path}: {error}") from error
    if not resolved.is_dir():
        raise GateCacheError(f"Git common directory is not a directory: {resolved}")
    return resolved


def shared_state_path(root: Path) -> Path:
    return git_common_dir(root) / SHARED_STATE_RELATIVE


def cache_path(root: Path) -> Path:
    return shared_state_path(root) / "evidence.json"


def report_path(root: Path) -> Path:
    return root / REPORT_RELATIVE


def manifest_path(root: Path) -> Path:
    return root / MANIFEST_RELATIVE


def build_certificate_path(root: Path, lake_root: Path | None = None) -> Path:
    return (lake_root or root / ".lake") / "blanc-build-certificate.json"


def lock_path(root: Path) -> Path:
    return shared_state_path(root) / "run.lock"

# How many historical successful records to retain per gate.  Eviction is a
# performance choice only: a pruned record simply causes a fresh run.
RECORDS_PER_GATE = 12

LEAN_TRACE_ROOTS = (
    ".lake/build/lib/lean",
    ".lake/packages/jaune/.lake/build/lib/lean",
)
JAUNE_RUNNER_RELATIVE = "packages/jaune/.lake/build/bin/jaune"

# Lean 4.32 spells an import with any run of modifiers before the keyword and
# an optional `all` after it.  In this toolchain's own packages there are
# 25,377 `public import`, 734 `public meta import`, 10 `meta import` and 64
# `import all` lines, so "public or nothing" is not the grammar.
IMPORT_MODIFIERS = r"(?:(?:public|private|protected|meta)[ \t]+)*"
IMPORT_LINE = re.compile(
    rf"^{IMPORT_MODIFIERS}import[ \t]+(?:all[ \t]+)?"
    r"([A-Za-z0-9_'.]+(?:[ \t]+[A-Za-z0-9_'.]+)*)[ \t]*$"
)
# Deliberately broader than the parser: anything that is *plainly* an import
# must be understood or refused.  A guard that enumerates spellings is one
# toolchain idiom away from silently dropping a dependency, which is the whole
# failure this raises on.
IMPORT_LIKE = re.compile(rf"^[ \t]*{IMPORT_MODIFIERS}import\b")

INPUT_KINDS = (
    "files",
    "populations",
    "lean_modules",
    "lean_entries",
    "git_refs",
    "external",
    "env",
    "tools",
    "clock",
    "material_output",
)

GATE_KINDS = ("cacheable", "composition", "always-fresh")

TOOL_COMMANDS = {
    "lean": ["lake", "env", "lean", "--version"],
    "lake": ["lake", "--version"],
    "python3": ["python3", "--version"],
    "git": ["git", "--version"],
    "bash": ["bash", "--version"],
}


class GateCacheError(RuntimeError):
    """A fault in the registry, cache or runner itself."""


class Unresolvable(RuntimeError):
    """An input could not be identified, so the gate must run.

    Never caught anywhere that could turn it into reuse: the planner records
    the reason and schedules execution.
    """


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


_DIGEST_MEMO: dict[tuple[str, int, int], str] = {}


def file_digest(path: Path) -> str:
    """Content digest, memoised on (path, mtime, size) within one process.

    Several gates read the same 113 MB Jaune binary and the same 147-module
    corpus.  Hashing each once per run keeps planning in the seconds where it
    belongs; the memo is per-process, so it can never outlive the run whose
    drift check depends on re-reading.
    """

    try:
        status = path.stat()
    except OSError as error:
        raise Unresolvable(f"cannot stat {path}: {error}") from error
    key = (str(path), status.st_mtime_ns, status.st_size)
    memo = _DIGEST_MEMO.get(key)
    if memo is not None:
        return memo
    try:
        digest = sha256_bytes(path.read_bytes())
    except OSError as error:
        raise Unresolvable(f"cannot read {path}: {error}") from error
    _DIGEST_MEMO[key] = digest
    return digest


def file_identity(path: Path) -> str:
    """Fingerprint both a file's bytes and any symlink that selects them.

    Virtual-environment interpreters are commonly absolute symlinks.  Hashing
    only the dereferenced bytes would let a retargeted interpreter reuse prior
    evidence whenever the replacement happened to have identical launcher
    bytes.  The link text is therefore part of the identity, while ordinary
    files retain their historical digest shape.
    """

    if path.is_symlink():
        try:
            target = os.readlink(path)
        except OSError as error:
            raise Unresolvable(f"cannot read symlink {path}: {error}") from error
        if not path.exists():
            raise Unresolvable(f"declared file is a dangling symlink: {path}")
        if path.is_file():
            return digest_of({"symlink": target, "content": file_digest(path)})
        if path.is_dir():
            # A separately declared population owns directory contents.  This
            # row owns which directory the stable alias selects.
            return digest_of({"symlink": target, "kind": "directory"})
        raise Unresolvable(f"declared symlink has unsupported target type: {path}")
    return file_digest(path)


_TOOL_MEMO: dict[str, str] = {}


def forget_digests() -> None:
    """Drop the memos so a post-execution fingerprint really re-reads."""

    _DIGEST_MEMO.clear()
    _TOOL_MEMO.clear()


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def digest_of(value: Any) -> str:
    return sha256_bytes(canonical(value))


def atomic_write(path: Path, data: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.", delete=False
    )
    temporary = Path(handle.name)
    try:
        with handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def atomic_json(path: Path, value: Any) -> None:
    atomic_write(path, json.dumps(value, indent=2, sort_keys=True) + "\n")


# --- registry ---------------------------------------------------------------


def load_registry(path: Path) -> dict[str, Any]:
    """Read and fully validate the committed gate registry.

    Validation is strict on purpose.  An unrecognised input kind, a gate
    without an order, a duplicate id and a malformed verdict declaration are
    all faults rather than things to route around: a registry the runner only
    half understands cannot be the basis of a skip.
    """

    try:
        registry = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise GateCacheError(f"cannot read gate registry {path}: {error}") from error
    if not isinstance(registry, dict) or registry.get("schema") != SCHEMA_VERSION:
        raise GateCacheError(f"gate registry schema is missing or not {SCHEMA_VERSION}")
    gates = registry.get("gates")
    if not isinstance(gates, list) or not gates:
        raise GateCacheError("gate registry carries no gates")

    seen_ids: set[str] = set()
    seen_orders: set[int] = set()
    seen_commands: set[tuple[str, ...]] = set()
    for gate in gates:
        if not isinstance(gate, dict):
            raise GateCacheError("gate registry entry is not an object")
        identifier = gate.get("id")
        if not isinstance(identifier, str) or not identifier:
            raise GateCacheError("gate registry entry has no id")
        if identifier in seen_ids:
            raise GateCacheError(f"duplicate gate id: {identifier}")
        seen_ids.add(identifier)

        order = gate.get("order")
        if not isinstance(order, int):
            raise GateCacheError(f"gate {identifier} has no integer order")
        if order in seen_orders:
            raise GateCacheError(f"duplicate gate order {order} at {identifier}")
        seen_orders.add(order)

        command = gate.get("command")
        if (
            not isinstance(command, list)
            or not command
            or not all(isinstance(word, str) for word in command)
        ):
            raise GateCacheError(f"gate {identifier} has no string command")
        key = tuple(command)
        if key in seen_commands:
            raise GateCacheError(f"duplicate command instance: {' '.join(command)}")
        seen_commands.add(key)

        kind = gate.get("kind")
        if kind not in GATE_KINDS:
            raise GateCacheError(f"gate {identifier} has unknown kind {kind!r}")
        if kind != "cacheable" and not gate.get("reason"):
            raise GateCacheError(f"gate {identifier} is {kind} without a recorded reason")
        if gate.get("prerequisite") and kind == "cacheable":
            raise GateCacheError(
                f"gate {identifier} is a prerequisite refresh and cannot be cacheable"
            )
        unknown_keys = sorted(
            set(gate)
            - {"id", "order", "command", "kind", "reason", "note", "inputs",
               "verdict", "prerequisite", "ci_only", "depends_on"}
        )
        if unknown_keys:
            raise GateCacheError(
                f"gate {identifier} carries unknown key(s): {', '.join(unknown_keys)}"
            )

        inputs = gate.get("inputs", {})
        if not isinstance(inputs, dict):
            raise GateCacheError(f"gate {identifier} has a malformed inputs object")
        unknown = sorted(set(inputs) - set(INPUT_KINDS))
        if unknown:
            raise GateCacheError(
                f"gate {identifier} declares unknown input kind(s): {', '.join(unknown)}"
            )
        if kind == "cacheable" and not inputs:
            raise GateCacheError(f"cacheable gate {identifier} declares no inputs")
        clock = inputs.get("clock")
        if clock is not None:
            if (
                not isinstance(clock, dict)
                or set(clock) != {"kind", "files"}
                or clock.get("kind") != "expiry-transitions"
                or not isinstance(clock.get("files"), list)
                or not clock["files"]
                or not all(isinstance(item, str) and item for item in clock["files"])
            ):
                raise GateCacheError(f"gate {identifier} has a malformed clock contract")
        material = inputs.get("material_output", [])
        if not isinstance(material, list):
            raise GateCacheError(f"gate {identifier} has malformed material-output inputs")
        for spec in material:
            if (
                not isinstance(spec, dict)
                or set(spec) != {"id", "command", "authority"}
                or not isinstance(spec.get("id"), str)
                or not spec["id"]
                or not isinstance(spec.get("command"), list)
                or not spec["command"]
                or not all(isinstance(item, str) and item for item in spec["command"])
                or not isinstance(spec.get("authority"), list)
                or not spec["authority"]
                or not all(isinstance(item, str) and item for item in spec["authority"])
            ):
                raise GateCacheError(
                    f"gate {identifier} has a malformed material-output certificate"
                )
        external = inputs.get("external", [])
        if not isinstance(external, list):
            raise GateCacheError(f"gate {identifier} has malformed external inputs")
        for spec in external:
            if not isinstance(spec, dict):
                raise GateCacheError(f"gate {identifier} has malformed external input")
            pin = spec.get("pin")
            if not isinstance(pin, str) or re.fullmatch(r"[0-9a-f]{40}", pin) is None:
                raise GateCacheError(
                    f"gate {identifier} external {spec.get('id', '?')} must carry an "
                    "exact lowercase 40-hex pin"
                )

        verdict = gate.get("verdict")
        if kind == "composition":
            if verdict is not None and not isinstance(verdict, dict):
                raise GateCacheError(f"gate {identifier} has a malformed verdict object")
        elif not isinstance(verdict, dict):
            raise GateCacheError(f"gate {identifier} declares no verdict contract")
        if isinstance(verdict, dict):
            patterns = verdict.get("summary_patterns", [])
            if not isinstance(patterns, list) or not all(
                isinstance(pattern, str) for pattern in patterns
            ):
                raise GateCacheError(f"gate {identifier} has malformed summary patterns")
            for pattern in patterns:
                try:
                    re.compile(pattern)
                except re.error as error:
                    raise GateCacheError(
                        f"gate {identifier} summary pattern is not a regex: {error}"
                    ) from error
            if kind == "cacheable" and not patterns:
                raise GateCacheError(
                    f"cacheable gate {identifier} declares no terminal summary pattern"
                )
            if verdict.get("expect_exit", 0) != 0:
                # `read_cache` treats any stored record with a non-zero exit as
                # cache corruption, so a gate registered to expect one would
                # store a legal record that empties the whole cache on the next
                # read -- silent, total loss of reuse with no diagnosis. The
                # catalogue's own pass criteria say `OK — …` and exit zero are
                # the only passing verdict, so refuse the declaration instead.
                raise GateCacheError(
                    f"gate {identifier} expects a non-zero exit; only exit 0 passes"
                )

    _validate_oracle_lanes(gates)
    gates.sort(key=lambda gate: gate["order"])
    position = {gate["id"]: index for index, gate in enumerate(gates)}
    for gate in gates:
        dependencies = gate.get("depends_on", [])
        if (
            not isinstance(dependencies, list)
            or not all(isinstance(item, str) and item for item in dependencies)
            or len(dependencies) != len(set(dependencies))
        ):
            raise GateCacheError(f"gate {gate['id']} has malformed dependencies")
        for dependency in dependencies:
            if dependency not in position:
                raise GateCacheError(
                    f"gate {gate['id']} depends on absent gate {dependency}"
                )
            if position[dependency] >= position[gate["id"]]:
                raise GateCacheError(
                    f"gate {gate['id']} dependency {dependency} is not earlier in the catalogue"
                )
    return registry


LEGACY_EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
CURRENT_T8N_PIN = "827a1cad9c9c8528512f90a06888c8bd9171d9ae"


def _input_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [item for child in value for item in _input_strings(child)]
    if isinstance(value, dict):
        return [item for child in value.values() for item in _input_strings(child)]
    return []


def _validate_oracle_lanes(gates: list[dict[str, Any]]) -> None:
    """Keep the frozen Prague oracle and current-mainnet target disjoint.

    This is registry validation, not an optional audit, so planning and cached
    reuse both refuse a gate whose root or pin was cross-wired.
    """

    for gate in gates:
        identifier = gate["id"]
        inputs = gate.get("inputs", {})
        strings = _input_strings(inputs)
        external = inputs.get("external", [])
        external_ids = {
            spec.get("id") for spec in external if isinstance(spec, dict)
        }
        legacy = (
            "eels" in external_ids
            or "EELS_ROOT" in strings
            or any(value.startswith("@eels/") for value in strings)
            or any(value.startswith("@eels_python_base/") for value in strings)
        )
        current = (
            "t8n_target" in external_ids
            or "JAUNE_T8N_TARGET" in strings
            or any(value.startswith("@t8n_target/") for value in strings)
            or any(value.startswith("@t8n_python_base/") for value in strings)
        )
        if legacy and current:
            raise GateCacheError(
                f"gate {identifier} mixes the legacy EELS and current-mainnet roots"
            )
        if not legacy and not current:
            continue

        if legacy:
            expected = {
                "id": "eels",
                "path": "~/execution-specs",
                "path_env": "EELS_ROOT",
                "pin": LEGACY_EELS_PIN,
            }
            matches = [spec for spec in external if spec == expected]
            if len(matches) != 1 or len(external) != 1:
                raise GateCacheError(
                    f"legacy EELS gate {identifier} must use only the frozen "
                    f"EELS_ROOT checkout at {LEGACY_EELS_PIN}"
                )
            env = inputs.get("env", [])
            if "EELS_ROOT" not in env or "JAUNE_T8N_TARGET" in env:
                raise GateCacheError(
                    f"legacy EELS gate {identifier} has the wrong root environment"
                )
            if any(
                value.startswith(("@t8n_target/", "@t8n_python_base/"))
                for value in strings
            ):
                raise GateCacheError(
                    f"legacy EELS gate {identifier} reads the current-mainnet root"
                )
            if any(value.startswith("@eels_python_base/") for value in strings) \
                    and not any(value.startswith("@eels/") for value in strings):
                raise GateCacheError(
                    f"legacy EELS gate {identifier} names a Python base without "
                    "its selecting checkout"
                )
            continue

        expected = {
            "id": "t8n_target",
            "path": "~/execution-specs-t8n-amsterdam",
            "path_env": "JAUNE_T8N_TARGET",
            "pin": CURRENT_T8N_PIN,
        }
        matches = [spec for spec in external if spec == expected]
        if len(matches) != 1 or len(external) != 1:
            raise GateCacheError(
                f"current-mainnet gate {identifier} must use only the isolated "
                f"JAUNE_T8N_TARGET checkout at {CURRENT_T8N_PIN}"
            )
        env = inputs.get("env", [])
        if "JAUNE_T8N_TARGET" not in env or "EELS_ROOT" in env:
            raise GateCacheError(
                f"current-mainnet gate {identifier} has the wrong root environment"
            )
        if any(value.startswith("@eels/") for value in strings):
            raise GateCacheError(
                f"current-mainnet gate {identifier} reads the legacy EELS root"
            )
        required = {"scripts/current-mainnet-target.json", "scripts/current_mainnet.py"}
        required.add("scripts/current-mainnet-runtime-lock.json")
        if not required.issubset(set(inputs.get("files", []))):
            raise GateCacheError(
                f"current-mainnet gate {identifier} does not fingerprint its shared "
                "profile and helper"
            )


def command_text(gate: dict[str, Any]) -> str:
    return " ".join(gate["command"])


RUNNER_SOUNDNESS_SOURCE = "gate-cache.py"
RUNNER_T8N_SOURCE = "gate_cache_t8n_root.py"

# Top-level authorities whose semantics can change whether an earlier verdict
# is valid for a candidate.  The AST digest deliberately excludes comments,
# CLI help, report/inventory rendering, and cache-retention policy.  Those can
# change how evidence is displayed or retained; they cannot change whether the
# substantive verdict recorded in that evidence was true.
SOUNDNESS_AUTHORITY_NAMES = frozenset({
    "EVIDENCE_SCHEMA_VERSION", "LEAN_TRACE_ROOTS", "IMPORT_MODIFIERS",
    "IMPORT_LINE", "IMPORT_LIKE", "INPUT_KINDS", "GATE_KINDS",
    "TOOL_COMMANDS", "LEGACY_EELS_PIN", "CURRENT_T8N_PIN", "NAMED_ROOTS",
    "SHARED_STATE_RELATIVE", "BUILD_CERTIFICATE_RELATIVE",
    "BUILD_CERTIFICATE_SCHEMA", "GateCacheError", "Unresolvable",
    "git_common_dir", "shared_state_path", "cache_path", "build_certificate_path",
    "sha256_bytes",
    "file_digest", "file_identity", "forget_digests", "canonical", "digest_of",
    "load_registry", "_input_strings", "_validate_oracle_lanes",
    "gate_uses_t8n_resolver", "semantic_authority_digest", "runner_identity",
    "resolve_path", "component_files", "glob_population", "traversable_population",
    "component_populations", "trace_path_for", "module_dep_hash",
    "component_lean_modules", "imports_of", "component_lean_entries", "git_output",
    "component_git_refs", "component_external", "component_env", "component_tools",
    "component_clock", "component_material_output", "fingerprint", "empty_cache", "read_cache", "lookup",
    "store", "prune_details", "tree_identity", "plan", "capture_verdict",
    "execute", "host_identity", "build_source_identity", "build_trace_state",
    "read_build_certificate", "write_build_certificate",
    "build_certificate_status", "run", "main",
})


def gate_uses_t8n_resolver(gate: dict[str, Any]) -> bool:
    strings = _input_strings(gate.get("inputs", {}))
    return any(
        value in {"t8n_target", "JAUNE_T8N_TARGET"}
        or value.startswith("@t8n_target/")
        or value.startswith("@t8n_python_base/")
        or value.startswith("@eels_python_base/")
        for value in strings
    )


def runner_identity_sources(gate: dict[str, Any]) -> tuple[str, ...]:
    """Soundness code relevant to this gate, excluding pure serialization.

    The common engine owns fingerprint construction, verdict validation,
    drift checks, and cache admission. The native Python-base resolver is
    relevant only to Prague/current-mainnet EELS consumers.
    `gate_cache_lock.py` is intentionally absent: it serializes writes but
    cannot make evidence reusable.
    """

    sources = [f"{RUNNER_SOUNDNESS_SOURCE}#soundness"]
    if gate_uses_t8n_resolver(gate):
        sources.append(RUNNER_T8N_SOURCE)
    return tuple(sources)


def semantic_authority_digest(path: Path) -> str:
    """Digest only verdict-validity authorities in the runner source."""

    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except (OSError, UnicodeError, SyntaxError) as error:
        raise Unresolvable(f"cannot parse runner soundness authority {path}: {error}") from error
    found: dict[str, str] = {}
    for node in tree.body:
        names: list[str] = []
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names = [node.name]
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            names = [target.id for target in targets if isinstance(target, ast.Name)]
        for name in names:
            if name in SOUNDNESS_AUTHORITY_NAMES:
                found[name] = ast.dump(node, annotate_fields=True, include_attributes=False)
    missing = sorted(SOUNDNESS_AUTHORITY_NAMES - set(found))
    if missing:
        raise Unresolvable(f"runner soundness authority is missing: {', '.join(missing)}")
    return digest_of(found)


def runner_identity(gate: dict[str, Any]) -> tuple[str, dict[str, str]]:
    here = Path(__file__).resolve().parent
    detail = {
        f"scripts/{RUNNER_SOUNDNESS_SOURCE}#soundness":
            semantic_authority_digest(here / RUNNER_SOUNDNESS_SOURCE)
    }
    if gate_uses_t8n_resolver(gate):
        detail[f"scripts/{RUNNER_T8N_SOURCE}"] = file_digest(here / RUNNER_T8N_SOURCE)
    return digest_of({"schema": SCHEMA_VERSION, "sources": detail}), detail


# --- input components -------------------------------------------------------
#
# Every component returns (digest, detail).  `detail` is a path -> digest map
# where per-path attribution is available, and None otherwise; it is what lets
# `plan --explain` name the file that moved rather than only the component.


# Roots the gates themselves resolve from the environment.  Declaring a path
# as `@eels/...` makes the registry resolve it the same way the gate does, so a
# run with `EELS_ROOT` pointed elsewhere fingerprints the checkout it actually
# used rather than the default one it did not.
NAMED_ROOTS = {
    "eels": ("EELS_ROOT", "~/execution-specs"),
    "t8n_target": T8N_TARGET_ROOT,
    "weth10ref": ("WETH10_REFERENCE_DIR", "scripts/reference/weth10"),
    "weth10lock": ("WETH10_REFERENCE_LOCK", "scripts/weth10-reference.json"),
    "weth10doc": ("WETH10_COMPATIBILITY_DOC", "WETH10_COMPATIBILITY.md"),
    "lidoref": ("LIDO_CIRCUIT_BREAKER_REFERENCE_DIR",
                "scripts/reference/lido-circuit-breaker"),
    "lidolock": ("LIDO_CIRCUIT_BREAKER_REFERENCE_LOCK",
                 "scripts/lido-circuit-breaker-reference.json"),
    "twgref": ("LIDO_TWG_REFERENCE_DIR", "scripts/reference/lido-twg"),
    "twglock": ("LIDO_TWG_REFERENCE_LOCK",
                "scripts/lido-twg-reference.json"),
    "ossifiableref": ("LIDO_OSSIFIABLE_PROXY_REFERENCE_DIR",
                       "scripts/reference/lido-ossifiable-proxy"),
    "ossifiablelock": ("LIDO_OSSIFIABLE_PROXY_REFERENCE_LOCK",
                        "scripts/lido-ossifiable-proxy-reference.json"),
    "ossifiabledoc": ("LIDO_OSSIFIABLE_PROXY_COMPATIBILITY_DOC",
                       "OSSIFIABLE_PROXY_COMPATIBILITY.md"),
    "ossifiableperfroot": ("LIDO_OSSIFIABLE_PROXY_PERFORMANCE_ROOT", "."),
    "ossifiableperfmanifest": (
        "LIDO_OSSIFIABLE_PROXY_PERFORMANCE_MANIFEST",
        "scripts/fixtures/lido-ossifiable-proxy/performance-manifest.json"),
}


def resolve_path(root: Path, given: str) -> Path:
    """Repository-relative by default; `@name/`, `~` and absolute kept as given.

    Real inputs live outside the tree: pinned checkout virtualenvs, the native
    CPython root selected by the current-mainnet venv, and fixture templates a
    generator reads from `~`. Pretending any is a repository path would
    silently fingerprint nothing.
    """

    if given.startswith("@"):
        name, _, rest = given[1:].partition("/")
        if name == "t8n_python_base":
            try:
                base = resolve_t8n_python_base(root)
            except T8nPythonBaseError as error:
                raise Unresolvable(str(error)) from error
            return base / rest if rest else base
        if name == "eels_python_base":
            try:
                base = resolve_eels_python_base(root)
            except T8nPythonBaseError as error:
                raise Unresolvable(str(error)) from error
            return base / rest if rest else base
        entry = NAMED_ROOTS.get(name)
        if entry is None:
            raise GateCacheError(f"unknown named root: @{name}")
        variable, default = entry
        base = Path(os.path.expanduser(os.environ.get(variable) or default))
        if not base.is_absolute():
            # A relative override would otherwise resolve against the process's
            # working directory, which is not the repository and which nothing
            # in this runner sets.
            base = root / base
        return base / rest if rest else base
    expanded = Path(os.path.expanduser(given))
    return expanded if expanded.is_absolute() else root / given


def component_files(root: Path, paths: list[str]) -> tuple[str, dict[str, str]]:
    detail: dict[str, str] = {}
    for given in sorted(set(paths)):
        path = resolve_path(root, given)
        detail[given] = file_identity(path) if path.is_file() or path.is_symlink() else "<absent>"
    return digest_of(detail), detail


def glob_population(root: Path, spec: dict[str, Any]) -> list[str]:
    base = spec.get("root", ".")
    pattern = spec.get("pattern")
    if not isinstance(base, str) or not isinstance(pattern, str):
        raise GateCacheError(f"malformed population specification: {spec!r}")
    excludes = spec.get("exclude", [])
    if not isinstance(excludes, list) or not all(isinstance(e, str) for e in excludes):
        raise GateCacheError(f"malformed population exclusions: {spec!r}")
    directory = resolve_path(root, base)
    if not directory.is_dir():
        raise Unresolvable(f"population root is not a directory: {base}")
    if "**" in pattern:
        # `Path.glob` does not descend into symlinked directories, so a file
        # reachable only through one would be elaborated by Lean and read by
        # the gate while staying invisible to this population. Refuse rather
        # than fingerprint a corpus that is quietly smaller than the gate's.
        for parent, directories, _ in os.walk(directory, followlinks=False):
            for name in directories:
                if Path(parent, name).is_symlink():
                    raise Unresolvable(
                        f"population root {base} contains a symlinked directory "
                        f"({Path(parent, name)}); its contents cannot be enumerated"
                    )
    prefix = "" if base in (".", "") else base.rstrip("/") + "/"
    found: list[str] = []
    for path in directory.glob(pattern):
        if not path.is_file():
            continue
        # Keyed relative to the declared root, so a population outside the
        # repository — the pinned EELS venv, an external fixture tree — names
        # itself the same way a repository one does.
        name = prefix + path.relative_to(directory).as_posix()
        if any(fnmatch.fnmatch(name, exclude) for exclude in excludes):
            continue
        found.append(name)
    return sorted(found)


def traversable_population(root: Path, spec: dict[str, Any]) -> None:
    """Refuse a population containing something a tree walk cannot read.

    One gate's verdict depends on the whole worktree being *copyable*: its
    negative controls make one seed copy and nine case copies through ten
    unguarded `shutil.copytree` calls, so a
    dangling symlink or an unreadable file anywhere makes it fail.  Neither of
    the two obvious declarations catches that.  Content hashing the tree
    invalidates the gate on every unrelated edit; membership invalidates it on
    every unrelated *addition* and still misses the case entirely, because a
    dangling symlink is not `is_file()` and never enters the digest -- measured,
    not assumed.

    So this mode declares the hazard rather than a corpus: it enumerates, raises
    on anything it cannot read, and contributes a constant to the fingerprint.
    Fail-closed where it matters, invisible where it does not.
    """

    base = spec.get("root", ".")
    directory = resolve_path(root, base)
    if not directory.is_dir():
        raise Unresolvable(f"population root is not a directory: {base}")
    excludes = spec.get("exclude", [])
    prefix = "" if base in (".", "") else base.rstrip("/") + "/"
    for path in directory.glob(spec["pattern"]):
        name = prefix + path.relative_to(directory).as_posix()
        if any(fnmatch.fnmatch(name, exclude) for exclude in excludes):
            continue
        if not path.exists():
            raise Unresolvable(f"{name} is a dangling symlink; the tree cannot be copied")
        if path.is_file() and not os.access(path, os.R_OK):
            raise Unresolvable(f"{name} is unreadable; the tree cannot be copied")


def component_populations(
    root: Path, specs: list[dict[str, Any]]
) -> tuple[str, dict[str, str]]:
    """Membership *and* content.

    Paths are part of the digested structure, so adding or deleting a file in
    a scanned corpus or a fixture directory invalidates the gate exactly as an
    edit to one of its files does.  A gate that asserts an absence depends on
    membership far more than on content.
    """

    detail: dict[str, str] = {}
    for spec in specs:
        mode = spec.get("mode", "content")
        if mode not in ("content", "membership", "traversable"):
            raise GateCacheError(f"unknown population mode: {mode!r}")
        if mode == "traversable":
            traversable_population(root, spec)
            detail["traversable\x00" + spec.get("root", ".") + "/" + spec["pattern"]] = "<ok>"
            continue
        for name in glob_population(root, spec):
            # Namespaced by mode, so a path declared under both a content and a
            # membership population cannot have one reading silently overwrite
            # the other depending on declaration order.
            # NUL separates the mode from the path because it is the one byte
            # a POSIX filename cannot contain; a `membership:` prefix would be
            # imitable by a file actually named `membership:foo`.
            if mode == "content":
                detail[name] = file_identity(resolve_path(root, name))
            else:
                detail["membership\x00" + name] = "<member>"
    return digest_of(detail), detail


def trace_path_for(root: Path, module: str) -> Path:
    relative = module.replace(".", "/") + ".trace"
    for trace_root in LEAN_TRACE_ROOTS:
        candidate = root / trace_root / relative
        if candidate.is_file():
            return candidate
    raise Unresolvable(
        f"no Lake trace for module {module}; run `lake build` before selection"
    )


def module_dep_hash(root: Path, module: str) -> str:
    """Lake's own transitive dependency summary for one module.

    This is the whole reason no per-gate import graph exists here.  A missing
    or malformed trace means the build precondition was not met, and guessing
    would make the skip unsound, so it raises.
    """

    path = trace_path_for(root, module)
    try:
        trace = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise Unresolvable(f"unreadable Lake trace for {module}: {error}") from error
    dep_hash = trace.get("depHash") if isinstance(trace, dict) else None
    if not isinstance(dep_hash, str) or not dep_hash:
        raise Unresolvable(f"Lake trace for {module} carries no depHash")
    return dep_hash


def component_lean_modules(root: Path, modules: list[str]) -> tuple[str, dict[str, str]]:
    detail = {module: module_dep_hash(root, module) for module in sorted(set(modules))}
    return digest_of(detail), detail


def imports_of(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise Unresolvable(f"cannot read Lean entry {path}: {error}") from error
    modules: list[str] = []
    for number, line in enumerate(text.splitlines(), start=1):
        match = IMPORT_LINE.match(line)
        if match:
            modules.extend(match.group(1).split())
        elif IMPORT_LIKE.match(line):
            # A line that is plainly an import but does not fit the shape this
            # parser understands -- a trailing comment, an unusual spelling --
            # would otherwise drop that module's depHash from the fingerprint
            # silently, which is the exact shape of an unsound skip.
            raise Unresolvable(
                f"unparsable import at {path}:{number}: {line.strip()!r}"
            )
    return modules


def component_lean_entries(root: Path, entries: list[str]) -> tuple[str, dict[str, str]]:
    """Ad-hoc Lean evaluators that Lake has no registered target for.

    `scripts/AxiomCheck.lean` and its siblings are run with `lake env lean`, so
    Lake never records a trace for them.  Their identity is their own source
    plus the `depHash` of every module they import: `depHash` already covers
    each import's own transitive closure, so the union over direct imports
    covers everything the elaborator will see.  An import that resolves to no
    trace raises rather than being skipped.
    """

    detail: dict[str, str] = {}
    for relative in sorted(set(entries)):
        path = root / relative
        detail[relative] = file_digest(path)
        for module in imports_of(path):
            detail[f"{relative}::import::{module}"] = module_dep_hash(root, module)
    return digest_of(detail), detail


def git_output(root: Path, arguments: list[str]) -> str:
    result = subprocess.run(
        ["git", *arguments], cwd=root, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise Unresolvable(
            f"git {' '.join(arguments)} failed: {result.stderr.strip() or result.returncode}"
        )
    return result.stdout.strip()


def component_git_refs(root: Path, refs: list[str]) -> tuple[str, dict[str, str]]:
    detail = {
        ref: git_output(root, ["rev-parse", "--verify", f"{ref}^{{commit}}"])
        for ref in sorted(set(refs))
    }
    return digest_of(detail), detail


def component_external(root: Path, specs: list[dict[str, Any]]) -> tuple[str, dict[str, str]]:
    """Identity of a pinned checkout outside this repository.

    A clean checkout at a known commit can be fingerprinted.  A dirty one
    cannot: its content is not summarised by its commit, so it raises and the
    owning gate runs.
    """

    detail: dict[str, str] = {}
    for spec in specs:
        identifier = spec.get("id")
        if not isinstance(identifier, str):
            raise GateCacheError(f"malformed external specification: {spec!r}")
        location = spec.get("path")
        env_name = spec.get("path_env")
        if isinstance(env_name, str) and os.environ.get(env_name):
            location = os.environ[env_name]
        if not isinstance(location, str):
            raise GateCacheError(f"external {identifier} declares no path")
        directory = Path(os.path.expanduser(location))
        if not directory.is_absolute():
            directory = root / directory
        if not directory.is_dir():
            raise Unresolvable(f"external checkout {identifier} is absent: {directory}")
        head = git_output(directory, ["rev-parse", "--verify", "HEAD"])
        dirt = git_output(directory, ["status", "--porcelain"])
        if dirt:
            raise Unresolvable(
                f"external checkout {identifier} is dirty; its commit does not "
                f"summarise its content"
            )
        pin = spec.get("pin")
        if not isinstance(pin, str) or re.fullmatch(r"[0-9a-f]{40}", pin) is None:
            raise Unresolvable(
                f"external checkout {identifier} has no exact lowercase 40-hex pin"
            )
        if head != pin:
            raise Unresolvable(
                f"external checkout {identifier} is at {head}, not the pinned {pin}"
            )
        detail[identifier] = head
    return digest_of(detail), detail


def component_env(names: list[str]) -> tuple[str, dict[str, str]]:
    """Presence encoded apart from value, so a variable cannot be *set* to the
    string that means unset."""

    detail: dict[str, str] = {}
    for name in sorted(set(names)):
        value = os.environ.get(name)
        detail[name] = "<unset>" if value is None else "set\x00" + value
    return digest_of(detail), detail


def component_tools(root: Path, tools: list[str]) -> tuple[str, dict[str, str]]:
    detail: dict[str, str] = {}
    for tool in sorted(set(tools)):
        arguments = TOOL_COMMANDS.get(tool)
        if arguments is None:
            raise GateCacheError(f"unknown tool identity requested: {tool}")
        memo = _TOOL_MEMO.get(tool)
        if memo is None:
            # `lake env lean --version` costs about half a second and twenty
            # gates declare it.  Asking once per run rather than once per gate
            # is the difference between planning in seconds and in tens of them.
            result = subprocess.run(
                arguments, cwd=root, capture_output=True, text=True, check=False
            )
            if result.returncode != 0:
                raise Unresolvable(f"cannot identify tool {tool}")
            memo = (result.stdout + result.stderr).strip()
            _TOOL_MEMO[tool] = memo
        detail[tool] = memo
    return digest_of(detail), detail


def component_clock(
    root: Path,
    spec: dict[str, Any],
    now: dt.datetime | None = None,
) -> tuple[str, dict[str, str]]:
    """Identity changes only when an exception can change gate semantics.

    All four checkers accept an exception through its `expires` local civil
    date and reject it on the following local date.  Empty registries therefore
    have no clock input at all; a future exception contributes a stable
    before/after boundary rather than invalidating at every midnight.
    """

    if spec.get("kind") != "expiry-transitions":
        raise GateCacheError(f"unknown clock contract: {spec!r}")
    instant = now or dt.datetime.now().astimezone()
    if instant.tzinfo is None:
        raise GateCacheError("injected clock must carry an explicit timezone")
    today = instant.date()
    detail: dict[str, str] = {}
    for relative in spec["files"]:
        path = resolve_path(root, relative)
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            raise Unresolvable(f"cannot read expiry registry {relative}: {error}") from error
        rows = payload.get("exceptions") if isinstance(payload, dict) else None
        if not isinstance(rows, list):
            raise Unresolvable(f"expiry registry {relative} has no exception list")
        for index, row in enumerate(rows):
            if not isinstance(row, dict) or not isinstance(row.get("expires"), str):
                raise Unresolvable(f"expiry registry {relative} row {index} has no expiry")
            raw = row["expires"]
            try:
                expiry = dt.date.fromisoformat(raw)
            except ValueError as error:
                raise Unresolvable(
                    f"expiry registry {relative} row {index} has invalid expiry"
                ) from error
            if expiry.isoformat() != raw:
                raise Unresolvable(
                    f"expiry registry {relative} row {index} has noncanonical expiry"
                )
            state = "active-through" if today <= expiry else "expired-after"
            detail[f"{relative}#{index}"] = f"{state}:{raw}"
    if not detail:
        detail["expiry-transitions"] = "none"
    return digest_of(detail), detail


def component_material_output(
    root: Path, specs: list[dict[str, Any]]
) -> tuple[str, dict[str, str]]:
    """Cheap deterministic projection of bytes an expensive gate consumes.

    The output-producing authority is bound independently of its stdout.  A
    checker edit that starts printing a constant therefore invalidates rather
    than laundering changed compiled bytes into an old certificate.
    """

    detail: dict[str, str] = {}
    seen: set[str] = set()
    for spec in specs:
        identifier = spec["id"]
        if identifier in seen:
            raise GateCacheError(f"duplicate material-output id: {identifier}")
        seen.add(identifier)
        authority = {
            relative: file_identity(resolve_path(root, relative))
            for relative in sorted(set(spec["authority"]))
        }
        try:
            result = subprocess.run(
                spec["command"], cwd=root, capture_output=True, check=False, timeout=180
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise Unresolvable(f"material output {identifier} could not run: {error}") from error
        if result.returncode != 0:
            diagnostic = result.stderr.decode("utf-8", "replace").strip()
            raise Unresolvable(
                f"material output {identifier} failed: {diagnostic or result.returncode}"
            )
        if not result.stdout:
            raise Unresolvable(f"material output {identifier} was empty")
        detail[f"{identifier}::output"] = sha256_bytes(result.stdout)
        detail[f"{identifier}::authority"] = digest_of(authority)
        detail[f"{identifier}::command"] = digest_of(spec["command"])
    return digest_of(detail), detail


# --- fingerprints -----------------------------------------------------------


def fingerprint(root: Path, gate: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    """The complete declared mutable-input identity of one gate command.

    Raises `Unresolvable` if any declared component cannot be identified.  The
    caller must then execute the gate: there is no fingerprint to match, which
    is exactly how "unknown means run" is enforced rather than remembered.
    """

    inputs = gate.get("inputs", {})
    components: dict[str, Any] = {}

    # The command itself, the registry entry that describes it, and this
    # module's own source.  Changing how a gate is invoked, what it declares,
    # or how selection works must invalidate the gate's evidence.
    components["command"] = {
        "digest": digest_of(gate["command"]),
        "detail": {"argv": " ".join(gate["command"])},
    }
    components["registry"] = {
        "digest": digest_of(
            {
                "kind": gate["kind"],
                "inputs": inputs,
                "verdict": gate.get("verdict"),
            }
        ),
        "detail": None,
    }
    runner_digest, runner_detail = runner_identity(gate)
    components["runner"] = {
        "digest": runner_digest,
        "detail": runner_detail,
    }

    if "files" in inputs:
        digest, detail = component_files(root, inputs["files"])
        components["files"] = {"digest": digest, "detail": detail}
    if "populations" in inputs:
        digest, detail = component_populations(root, inputs["populations"])
        components["populations"] = {"digest": digest, "detail": detail}
    if "lean_modules" in inputs:
        digest, detail = component_lean_modules(root, inputs["lean_modules"])
        components["lean_modules"] = {"digest": digest, "detail": detail}
    if "lean_entries" in inputs:
        digest, detail = component_lean_entries(root, inputs["lean_entries"])
        components["lean_entries"] = {"digest": digest, "detail": detail}
    if "git_refs" in inputs:
        digest, detail = component_git_refs(root, inputs["git_refs"])
        components["git_refs"] = {"digest": digest, "detail": detail}
    if "external" in inputs:
        digest, detail = component_external(root, inputs["external"])
        components["external"] = {"digest": digest, "detail": detail}
    if "env" in inputs:
        digest, detail = component_env(inputs["env"])
        components["env"] = {"digest": digest, "detail": detail}
    if "tools" in inputs:
        digest, detail = component_tools(root, inputs["tools"])
        components["tools"] = {"digest": digest, "detail": detail}
    if "clock" in inputs:
        digest, detail = component_clock(root, inputs["clock"])
        components["clock"] = {"digest": digest, "detail": detail}
    if "material_output" in inputs:
        digest, detail = component_material_output(root, inputs["material_output"])
        components["material_output"] = {"digest": digest, "detail": detail}

    overall = digest_of(
        {name: entry["digest"] for name, entry in sorted(components.items())}
    )
    return overall, components


# --- authoritative build certificate ---------------------------------------


def host_identity() -> str:
    system = platform.system().lower()
    machine = platform.machine().lower()
    # The readable platform prefix makes diagnostics useful; the hashed node
    # component prevents a shared/NFS common directory from laundering local
    # evidence between two hosts without publishing the hostname itself.
    node = sha256_bytes(platform.node().encode("utf-8"))[:16]
    return f"{system}-{machine}-{node}"


def build_source_identity(
    root: Path, lake_root: Path | None = None
) -> tuple[str, dict[str, Any]]:
    """Exact source/config/toolchain/dependency identity credited by `lake build`."""

    files = ["lean-toolchain", "lakefile.lean", "lake-manifest.json", "Blanc.lean"]
    if (root / "Main.lean").is_file():
        files.append("Main.lean")
    files.extend(
        path.relative_to(root).as_posix()
        for path in sorted((root / "Blanc").rglob("*.lean"))
    )
    file_print, file_detail = component_files(root, files)
    tool_print, tool_detail = component_tools(root, ["lake", "lean"])

    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest.get("packages") if isinstance(manifest, dict) else None
    if not isinstance(packages, list):
        raise Unresolvable("lake-manifest.json has no package population")
    package_detail: dict[str, str] = {}
    for package in packages:
        if not isinstance(package, dict) or not isinstance(package.get("name"), str):
            raise Unresolvable("lake-manifest.json has a malformed package row")
        name = package["name"]
        expected = package.get("rev")
        directory = (lake_root or root / ".lake") / "packages" / name
        if not directory.is_dir():
            raise Unresolvable(f"Lake package {name} is absent")
        head = git_output(directory, ["rev-parse", "HEAD"])
        dirt = git_output(directory, ["status", "--porcelain"])
        if dirt:
            raise Unresolvable(f"Lake package {name} is dirty")
        if isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{40}", expected):
            if head != expected:
                raise Unresolvable(f"Lake package {name} is at {head}, expected {expected}")
        package_detail[name] = head
    package_print = digest_of(package_detail)
    runner_path = (lake_root or root / ".lake") / JAUNE_RUNNER_RELATIVE
    runner_detail = {JAUNE_RUNNER_RELATIVE: file_identity(runner_path)}
    runner_print = digest_of(runner_detail)
    detail = {
        "files": {"digest": file_print, "detail": file_detail},
        "tools": {"digest": tool_print, "detail": tool_detail},
        "packages": {"digest": package_print, "detail": package_detail},
        "runtime_artifacts": {"digest": runner_print, "detail": runner_detail},
    }
    return digest_of({name: item["digest"] for name, item in detail.items()}), detail


def build_trace_state(root: Path, lake_root: Path | None = None) -> dict[str, str]:
    modules = ["Blanc"]
    modules.extend(
        path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
        for path in sorted((root / "Blanc").rglob("*.lean"))
    )
    trace_root = (lake_root or root / ".lake") / "build/lib/lean"
    detail: dict[str, str] = {}
    for module in sorted(set(modules)):
        path = trace_root / (module.replace(".", "/") + ".trace")
        try:
            trace = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            raise Unresolvable(f"unreadable Lake trace for {module}: {error}") from error
        dep_hash = trace.get("depHash") if isinstance(trace, dict) else None
        if not isinstance(dep_hash, str) or not dep_hash:
            raise Unresolvable(f"Lake trace for {module} carries no depHash")
        detail[module] = dep_hash
    return detail


def read_build_certificate(
    root: Path, lake_root: Path | None = None
) -> dict[str, Any]:
    path = build_certificate_path(root, lake_root)
    try:
        certificate = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise Unresolvable(f"build certificate is missing or corrupt: {error}") from error
    required = {"schema", "host", "identity", "components", "traces", "provenance"}
    if not isinstance(certificate, dict) or set(certificate) != required:
        raise Unresolvable("build certificate shape is incompatible")
    if certificate.get("schema") != BUILD_CERTIFICATE_SCHEMA:
        raise Unresolvable("build certificate schema is incompatible")
    if certificate.get("host") != host_identity():
        raise Unresolvable("build certificate belongs to a different host identity")
    if not isinstance(certificate.get("identity"), str):
        raise Unresolvable("build certificate has no identity")
    if not isinstance(certificate.get("components"), dict):
        raise Unresolvable("build certificate has no component map")
    traces = certificate.get("traces")
    if not isinstance(traces, dict) or not all(
        isinstance(name, str) and isinstance(value, str) for name, value in traces.items()
    ):
        raise Unresolvable("build certificate has no trace map")
    return certificate


def write_build_certificate(root: Path) -> dict[str, Any]:
    identity, components = build_source_identity(root)
    traces = build_trace_state(root)
    certificate = {
        "schema": BUILD_CERTIFICATE_SCHEMA,
        "host": host_identity(),
        "identity": identity,
        "components": {
            name: item["digest"] for name, item in components.items()
        },
        "traces": traces,
        "provenance": {
            "commit": git_output(root, ["rev-parse", "HEAD"]),
            "recorded_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        },
    }
    atomic_json(build_certificate_path(root), certificate)
    return certificate


def build_certificate_status(
    root: Path, lake_root: Path | None = None
) -> tuple[bool, str, dict[str, Any] | None]:
    try:
        certificate = read_build_certificate(root, lake_root)
        identity, _ = build_source_identity(root, lake_root)
        if certificate["identity"] != identity:
            return False, "source/config/toolchain/dependency identity moved", certificate
        traces = build_trace_state(root, lake_root)
        if certificate["traces"] != traces:
            return False, "Lake trace population or depHash moved", certificate
    except (GateCacheError, Unresolvable, OSError, UnicodeError, json.JSONDecodeError) as error:
        return False, str(error), None
    return True, "exact build certificate matches", certificate


# --- cache ------------------------------------------------------------------
#
# Layout:
#
#   {"schema": 2, "trust_domain": "same-git-common-directory", "host": "...",
#    "gates":  {"<id>": [ {"fingerprint", "components", "verdict",
#                          "provenance"}, ... newest last ... ]},
#    "details": {"<component-digest>": {"<path>": "<digest>"}}}
#
# Per-path detail is interned by component digest because the same corpus is
# an input to many gates; without interning, one 149-file population would be
# copied into every record that reads it.


def empty_cache() -> dict[str, Any]:
    return {
        "schema": EVIDENCE_SCHEMA_VERSION,
        "trust_domain": "same-git-common-directory",
        "host": host_identity(),
        "gates": {},
        "details": {},
    }


def read_cache(path: Path) -> tuple[dict[str, Any], str | None]:
    """Load the cache, or explain why there is none.

    Every malformed shape returns an empty cache with a reason rather than
    raising: a corrupt cache must cost a fresh run, never a crash and never a
    credited pass.
    """

    if not path.is_file():
        return empty_cache(), "no prior cache"
    try:
        cache = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        return empty_cache(), "cache is unreadable or corrupt"
    if not isinstance(cache, dict) or cache.get("schema") != EVIDENCE_SCHEMA_VERSION:
        return empty_cache(), "cache schema is missing or incompatible"
    if cache.get("trust_domain") != "same-git-common-directory":
        return empty_cache(), "cache trust domain is missing or incompatible"
    if cache.get("host") != host_identity():
        return empty_cache(), "cache belongs to a different host identity"
    gates = cache.get("gates")
    details = cache.get("details")
    if not isinstance(gates, dict) or not isinstance(details, dict):
        return empty_cache(), "cache tables are invalid"
    for identifier, records in gates.items():
        if not isinstance(identifier, str) or not isinstance(records, list):
            return empty_cache(), "cache gate table is invalid"
        for record in records:
            if not isinstance(record, dict):
                return empty_cache(), "cache record is invalid"
            if not isinstance(record.get("fingerprint"), str) or not record["fingerprint"]:
                return empty_cache(), "cache record has no fingerprint"
            verdict = record.get("verdict")
            if not isinstance(verdict, dict) or verdict.get("exit") != 0:
                return empty_cache(), "cache record does not carry a passing verdict"
            if not isinstance(verdict.get("summary"), list):
                return empty_cache(), "cache record has no terminal summary"
            if not isinstance(record.get("components"), dict):
                return empty_cache(), "cache record has no component map"
            if not isinstance(record.get("provenance"), dict):
                return empty_cache(), "cache record has no provenance"
    return cache, None


def lookup(cache: dict[str, Any], identifier: str, print_: str) -> dict[str, Any] | None:
    """Any retained record with this exact fingerprint, newest first.

    Lookup is content-addressed, not "last result": returning to an earlier
    tree finds the evidence produced for it before the excursion.
    """

    for record in reversed(cache["gates"].get(identifier, [])):
        if record["fingerprint"] == print_:
            return record
    return None


def store(
    cache: dict[str, Any],
    identifier: str,
    print_: str,
    components: dict[str, Any],
    verdict: dict[str, Any],
    provenance: dict[str, Any],
) -> None:
    records = [
        record
        for record in cache["gates"].get(identifier, [])
        if record["fingerprint"] != print_
    ]
    records.append(
        {
            "fingerprint": print_,
            "components": {name: entry["digest"] for name, entry in components.items()},
            "verdict": verdict,
            "provenance": provenance,
        }
    )
    cache["gates"][identifier] = records[-RECORDS_PER_GATE:]
    for entry in components.values():
        if entry.get("detail") is not None:
            cache["details"][entry["digest"]] = entry["detail"]


def prune_details(cache: dict[str, Any]) -> None:
    live = {
        digest
        for records in cache["gates"].values()
        for record in records
        for digest in record["components"].values()
    }
    cache["details"] = {
        digest: detail for digest, detail in cache["details"].items() if digest in live
    }


# Locking lives in `gate_cache_lock.py`, imported above. It is kept outside the
# evidence engine so changing serialization cannot invalidate gate verdicts.


# --- planning ---------------------------------------------------------------


def tree_identity(root: Path) -> dict[str, str]:
    """Provenance, never validity.

    Recorded so a reviewer can see which tree produced a verdict.  Nothing in
    the reuse decision consults it: that is the whole point of the change.
    """

    identity: dict[str, str] = {}
    try:
        identity["commit"] = git_output(root, ["rev-parse", "HEAD"])
    except Unresolvable:
        identity["commit"] = "<unresolved>"
    try:
        status = git_output(root, ["status", "--porcelain"])
        identity["worktree"] = "clean" if not status else sha256_bytes(status.encode())
    except Unresolvable:
        identity["worktree"] = "<unresolved>"
    return identity


def plan(
    root: Path, registry: dict[str, Any], cache: dict[str, Any], fresh: bool
) -> list[dict[str, Any]]:
    has_build_row = any(gate["id"] == "lake-build" for gate in registry["gates"])
    build_current, build_reason, _ = (
        build_certificate_status(root) if has_build_row else (True, "not required", None)
    )
    rows: list[dict[str, Any]] = []
    for gate in registry["gates"]:
        row: dict[str, Any] = {
            "id": gate["id"],
            "order": gate["order"],
            "command": gate["command"],
            "kind": gate["kind"],
            "gate": gate,
            "fingerprint": None,
            "components": None,
            "record": None,
        }
        if gate["id"] == "lake-build" and not fresh and build_current:
            row["disposition"] = "certified"
            row["reason"] = build_reason
            rows.append(row)
            continue
        if gate["kind"] != "cacheable":
            row["disposition"] = "fresh"
            row["reason"] = gate["reason"]
            rows.append(row)
            continue
        if (
            has_build_row
            and not build_current
            and any(kind in gate.get("inputs", {}) for kind in ("lean_modules", "lean_entries"))
        ):
            row["disposition"] = "fresh"
            row["reason"] = f"authoritative build refresh required: {build_reason}"
            rows.append(row)
            continue
        try:
            print_, components = fingerprint(root, gate)
        except Unresolvable as error:
            row["disposition"] = "fresh"
            row["reason"] = f"input not identifiable: {error}"
            rows.append(row)
            continue
        row["fingerprint"] = print_
        row["components"] = components
        if fresh:
            row["disposition"] = "fresh"
            row["reason"] = "fresh mode requested"
            rows.append(row)
            continue
        record = lookup(cache, gate["id"], print_)
        if record is None:
            row["disposition"] = "fresh"
            row["reason"] = "no successful record for this fingerprint"
        else:
            row["disposition"] = "reused"
            row["reason"] = "fingerprint matches a successful record"
            row["record"] = record
        rows.append(row)
    return rows


def explain_row(cache: dict[str, Any], row: dict[str, Any]) -> list[str]:
    """Name what moved, at component and then at path granularity."""

    lines: list[str] = []
    if row["disposition"] == "reused" or row["kind"] != "cacheable":
        # A composition or always-fresh row has no fingerprint to diff; its
        # reason has already been printed and repeating it reads as a finding.
        return lines
    if row["components"] is None:
        lines.append(f"    {row['reason']}")
        return lines
    records = cache["gates"].get(row["id"], [])
    if not records:
        lines.append("    no retained record for this gate")
        return lines
    previous = records[-1]
    current = {name: entry["digest"] for name, entry in row["components"].items()}
    names = sorted(set(previous["components"]) | set(current))
    for name in names:
        was = previous["components"].get(name, "<absent>")
        now = current.get(name, "<absent>")
        if was == now:
            continue
        lines.append(f"    component {name}: {was[:16]} -> {now[:16]}")
        old_detail = cache["details"].get(was)
        new_detail = row["components"].get(name, {}).get("detail")
        if isinstance(old_detail, dict) and isinstance(new_detail, dict):
            for key in sorted(set(old_detail) | set(new_detail)):
                before = old_detail.get(key, "<absent>")
                after = new_detail.get(key, "<absent>")
                if before != after:
                    lines.append(f"      {key}: {before[:16]} -> {after[:16]}")
    if not lines:
        lines.append("    newest record differs in no declared component (different record)")
    return lines


# --- execution --------------------------------------------------------------


def capture_verdict(gate: dict[str, Any], result: subprocess.CompletedProcess) -> dict[str, Any]:
    """Turn a completed process into a verdict, or into a refusal to cache it.

    A pass is not "exit zero".  It is exit zero *and* each declared terminal
    summary line present exactly once.  A gate that was killed mid-stream, or
    whose harness printed its summary twice because two runs interleaved into
    one report, exits this function as a failure and can never seed a record.
    """

    contract = gate.get("verdict") or {}
    expected = contract.get("expect_exit", 0)
    output = result.stdout + result.stderr
    summary: list[str] = []
    problems: list[str] = []
    if result.returncode != expected:
        problems.append(f"exit {result.returncode}, expected {expected}")
    for pattern in contract.get("summary_patterns", []):
        matches = [line for line in output.splitlines() if re.search(pattern, line)]
        if len(matches) != 1:
            problems.append(f"{len(matches)} lines match /{pattern}/, expected exactly 1")
        summary.extend(matches)
    return {
        "exit": result.returncode,
        "summary": summary,
        "problems": problems,
        "output_digest": sha256_bytes(output.encode("utf-8", "replace")),
        "passed": not problems,
    }


def execute(root: Path, gate: dict[str, Any], echo: bool) -> tuple[dict[str, Any], float]:
    started = time.monotonic()
    result = subprocess.run(
        gate["command"], cwd=root, capture_output=True, text=True, check=False
    )
    elapsed = time.monotonic() - started
    if echo:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        sys.stdout.flush()
    return capture_verdict(gate, result), elapsed


def run(root: Path, arguments: argparse.Namespace) -> int:
    # Reconcile the registry against the catalogue *before* planning anything.
    # Without this, deleting a registry entry silently shrinks the audited
    # population: the run reports a smaller row count, every remaining row is
    # green, and the gate that vanished is indistinguishable from one that
    # passed. That is the cheapest possible attack on this design -- it needs
    # no forged fingerprint -- and an audit nobody is required to run is no
    # defence at all.
    if audit(root, quiet=True) != 0:
        print(
            "check-gates: the registry does not reconcile with the catalogue; "
            "run scripts/check-gates.sh --audit",
            file=sys.stderr,
        )
        return 2

    registry = load_registry(registry_path(root))
    cache, cache_reason = read_cache(cache_path(root))
    if cache_reason:
        print(f"check-gates: {cache_reason}; every gate will execute", file=sys.stderr)

    identity = tree_identity(root)
    shared_admission = (
        identity["commit"] == "<unresolved>" or identity["worktree"] == "clean"
    )
    if not shared_admission:
        print(
            "check-gates: dirty worktree; successful fresh verdicts will not seed "
            "shared evidence",
            file=sys.stderr,
        )
    started_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    wall_started = time.monotonic()
    failures: list[str] = []

    # Prerequisites run before planning, not at their catalogue position.
    # Every Lean-dependent fingerprint in this registry reads a Lake trace, and
    # a trace is only evidence once `lake build` has brought its target current;
    # planning against stale traces would fail closed and rerun the whole set
    # for no reason.  The row keeps its catalogue order in the report.
    prerequisites: dict[str, dict[str, Any]] = {}
    for gate in registry["gates"]:
        if not gate.get("prerequisite"):
            continue
        if gate["id"] == "lake-build" and not arguments.fresh:
            current, reason, certificate = build_certificate_status(root)
            if current:
                print(f"[cert  ] {command_text(gate)}   ({reason})")
                prerequisites[gate["id"]] = {
                    "disposition": "certified",
                    "verdict": {
                        "exit": 0,
                        "summary": ["OK — lake build certificate: exact identity and traces"],
                        "problems": [],
                        "output_digest": digest_of(certificate),
                        "passed": True,
                    },
                    "elapsed": 0.0,
                }
                continue
        print(f"[fresh ] {command_text(gate)}   (prerequisite refresh)")
        verdict, elapsed = execute(root, gate, echo=arguments.echo)
        prerequisites[gate["id"]] = {
            "disposition": "fresh", "verdict": verdict, "elapsed": elapsed
        }
        if not verdict["passed"]:
            problem = "; ".join(verdict["problems"])
            print(f"         FAILED: {problem}", file=sys.stderr)
            failures.append(f"{command_text(gate)}: {problem}")
        elif gate["id"] == "lake-build":
            try:
                write_build_certificate(root)
            except (GateCacheError, Unresolvable, OSError, UnicodeError) as error:
                failures.append(f"{command_text(gate)}: could not certify build: {error}")

    if failures:
        # Without a current build there is no sound dependency identity for any
        # Lean-dependent gate, so there is nothing to plan.
        print("GATES FAILED: prerequisite refresh failed; nothing was planned",
              file=sys.stderr)
        for line in failures:
            print(f"  {line}", file=sys.stderr)
        return 1

    forget_digests()
    rows = plan(root, registry, cache, fresh=arguments.fresh)
    planned = {row["id"]: row["fingerprint"] for row in rows}

    for row in rows:
        label = command_text(row["gate"])
        done = prerequisites.get(row["id"])
        if done is not None:
            row["disposition"] = done["disposition"]
            row["reason"] = (
                "exact build certificate matched"
                if done["disposition"] == "certified"
                else row["gate"]["reason"]
            )
            row["verdict"] = done["verdict"]
            row["elapsed"] = done["elapsed"]
            row["cached"] = False
            row["cache_reason"] = (
                "exact local build certificate"
                if done["disposition"] == "certified"
                else "prerequisite refresh, never credited from a record"
            )
            continue
        dependencies = row["gate"].get("depends_on", [])
        unmet = []
        for dependency in dependencies:
            prior = next((item for item in rows if item["id"] == dependency), None)
            prior_green = prior is not None and (
                prior.get("disposition") in {"reused", "certified"}
                or prior.get("verdict", {}).get("passed") is True
            )
            if not prior_green:
                unmet.append(dependency)
        if unmet:
            row["disposition"] = "blocked"
            row["reason"] = "required evidence absent or red: " + ", ".join(unmet)
            row["elapsed"] = 0.0
            row["verdict"] = {
                "exit": 1,
                "summary": [],
                "problems": [row["reason"]],
                "output_digest": digest_of(row["reason"]),
                "passed": False,
            }
            row["cached"] = False
            row["cache_reason"] = row["reason"]
            failures.append(f"{label}: {row['reason']}")
            print(f"[block ] {label}   ({row['reason']})", file=sys.stderr)
            continue
        if row["disposition"] == "reused":
            record = row["record"]
            row["elapsed"] = 0.0
            row["verdict"] = record["verdict"]
            print(f"[reused] {label}")
            for line in record["verdict"]["summary"]:
                print(f"         {line}   (from {record['provenance'].get('commit', '?')[:12]}"
                      f" at {record['provenance'].get('recorded_utc', '?')})")
            continue

        print(f"[fresh ] {label}")
        verdict, elapsed = execute(root, row["gate"], echo=arguments.echo)
        row["elapsed"] = elapsed
        row["verdict"] = verdict
        for line in verdict["summary"]:
            print(f"         {line}")
        if not verdict["passed"]:
            row["cached"] = False
            row["cache_reason"] = "; ".join(verdict["problems"])
            failures.append(f"{label}: {row['cache_reason']}")
            print(f"         FAILED: {row['cache_reason']}", file=sys.stderr)
            continue

        if row["kind"] != "cacheable" or row["fingerprint"] is None:
            row["cached"] = False
            row["cache_reason"] = row.get("reason", "not cacheable")
            continue
        if not shared_admission:
            row["cached"] = False
            row["cache_reason"] = (
                "dirty worktree: verdict is candidate-local and was not admitted "
                "to shared evidence"
            )
            continue

        # Re-derive the fingerprint now that the gate has finished.  An edit
        # landing between planning and completion would otherwise attach this
        # verdict to inputs it never saw.
        forget_digests()
        try:
            after, components = fingerprint(root, row["gate"])
        except Unresolvable as error:
            row["cached"] = False
            row["cache_reason"] = f"inputs became unidentifiable during the run: {error}"
            continue
        if after != row["fingerprint"]:
            row["cached"] = False
            row["cache_reason"] = "inputs changed during the run; verdict not cached"
            print(f"         {row['cache_reason']}", file=sys.stderr)
            continue
        store(
            cache,
            row["id"],
            after,
            components,
            {"exit": verdict["exit"], "summary": verdict["summary"],
             "output_digest": verdict["output_digest"]},
            {
                "commit": identity["commit"],
                "worktree": identity["worktree"],
                "recorded_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "duration_s": round(elapsed, 3),
            },
        )
        row["cached"] = True

    # Revalidate every reused row against the tree as it stands now.  A row
    # credited from a record is only credited to *this* candidate if the
    # candidate still hashes the way it did when the row was planned.
    drifted: list[str] = []
    forget_digests()
    for row in rows:
        if row["disposition"] != "reused":
            continue
        try:
            after, _ = fingerprint(root, row["gate"])
        except Unresolvable as error:
            drifted.append(f"{command_text(row['gate'])}: {error}")
            continue
        if after != planned[row["id"]]:
            drifted.append(f"{command_text(row['gate'])}: inputs changed during the run")

    wall = time.monotonic() - wall_started
    if not drifted:
        prune_details(cache)
        atomic_json(cache_path(root), cache)

    write_report(root, rows, identity, started_utc, wall, failures, drifted)

    if drifted:
        print("DRIFT: reused evidence no longer describes this tree:", file=sys.stderr)
        for line in drifted:
            print(f"  {line}", file=sys.stderr)
        print("DRIFT: cache not advanced; re-run on a settled tree", file=sys.stderr)
        return 1
    if failures:
        print(f"GATES FAILED: {len(failures)} of {len(rows)} rows", file=sys.stderr)
        for line in failures:
            print(f"  {line}", file=sys.stderr)
        return 1

    executed = sum(1 for row in rows if row["disposition"] == "fresh")
    reused = sum(1 for row in rows if row["disposition"] == "reused")
    certified = sum(1 for row in rows if row["disposition"] == "certified")
    print(
        f"GATES OK: {len(rows)} rows, {executed} executed, {reused} reused, "
        f"{certified} build-certified "
        f"from valid evidence, {wall:.1f}s"
    )
    print(f"check-gates: report {REPORT_RELATIVE}, manifest {MANIFEST_RELATIVE}")
    return 0


# --- evidence ---------------------------------------------------------------


def write_report(
    root: Path,
    rows: list[dict[str, Any]],
    identity: dict[str, str],
    started_utc: str,
    wall: float,
    failures: list[str],
    drifted: list[str],
) -> None:
    """Candidate-level evidence a reviewer can check without the transcript.

    Every row says whether it executed here or was credited from earlier
    evidence, and a credited row names the commit and time of the execution it
    is credited from.  The summary is never allowed to imply that a reused
    gate's body ran.
    """

    lines = [
        "# Blanc selective gate checkpoint",
        "",
        f"- started: {started_utc}",
        f"- commit: {identity['commit']}",
        f"- worktree: {identity['worktree']}",
        f"- wall: {wall:.1f}s",
        f"- rows: {len(rows)}",
        f"- executed: {sum(1 for r in rows if r['disposition'] == 'fresh')}",
        f"- reused: {sum(1 for r in rows if r['disposition'] == 'reused')}",
        f"- build-certified: {sum(1 for r in rows if r['disposition'] == 'certified')}",
        f"- blocked: {sum(1 for r in rows if r['disposition'] == 'blocked')}",
        "",
        "| # | command | disposition | verdict | evidence from |",
        "|---|---|---|---|---|",
    ]
    manifest_rows = []
    for row in rows:
        verdict = row.get("verdict", {})
        summary = " / ".join(verdict.get("summary", [])) or "(no summary captured)"
        if row["disposition"] == "reused":
            provenance = row["record"]["provenance"]
            source = f"{provenance.get('commit', '?')[:12]} @ {provenance.get('recorded_utc', '?')}"
            disposition = "reused successful evidence"
        elif row["disposition"] == "certified":
            source = BUILD_CERTIFICATE_RELATIVE
            disposition = "exact build certificate"
        elif row["disposition"] == "blocked":
            source = row.get("reason", "required evidence absent or red")
            disposition = "blocked"
        else:
            source = "executed now"
            disposition = "executed now"
        escaped = summary.replace("|", "\\|")
        lines.append(
            f"| {row['order']} | `{command_text(row['gate'])}` | {disposition} | "
            f"{escaped} | {source} |"
        )
        manifest_rows.append(
            {
                "order": row["order"],
                "id": row["id"],
                "command": row["command"],
                "kind": row["kind"],
                "disposition": row["disposition"],
                "reason": row.get("reason"),
                "depends_on": row["gate"].get("depends_on", []),
                "fingerprint": row["fingerprint"],
                "components": (
                    {name: entry["digest"] for name, entry in row["components"].items()}
                    if row["components"]
                    else None
                ),
                "verdict": verdict,
                "elapsed_s": round(row.get("elapsed", 0.0), 3),
                "cached": row.get("cached"),
                "cache_reason": row.get("cache_reason"),
                "evidence_from": (
                    row["record"]["provenance"]
                    if row["disposition"] == "reused"
                    else (
                        {"kind": "build-certificate", "path": BUILD_CERTIFICATE_RELATIVE}
                        if row["disposition"] == "certified"
                        else None
                    )
                ),
            }
        )

    always_fresh = [row for row in rows if row["kind"] != "cacheable"]
    if always_fresh:
        lines += ["", "## Always fresh", ""]
        for row in always_fresh:
            lines.append(f"- `{command_text(row['gate'])}` — {row['gate']['reason']}")
    if failures:
        lines += ["", "## Failures", ""] + [f"- {line}" for line in failures]
    if drifted:
        lines += ["", "## Drift", ""] + [f"- {line}" for line in drifted]
    lines.append("")

    atomic_write(report_path(root), "\n".join(lines))
    atomic_json(
        manifest_path(root),
        {
            "schema": SCHEMA_VERSION,
            "started_utc": started_utc,
            "wall_s": round(wall, 3),
            "tree": identity,
            "green": not failures and not drifted,
            "rows": manifest_rows,
        },
    )


# --- registry audit ---------------------------------------------------------


FULL_SET_BLOCK = re.compile(
    r"\*\*The full set, in order\.\*\*.*?\n```\n(.*?)\n```", re.DOTALL
)


def catalogue_commands(root: Path) -> list[list[str]]:
    """Derive the authoritative population from the catalogue itself.

    The registry is not allowed to be its own authority for what exists.  This
    reads `scripts/GATES.md`'s full ordered block, so adding, deleting,
    renaming or re-arguing a catalogued command makes the audit fail until the
    registry is reconciled.
    """

    text = (root / "scripts/GATES.md").read_text(encoding="utf-8")
    match = FULL_SET_BLOCK.search(text)
    if match is None:
        raise GateCacheError("scripts/GATES.md has no full ordered command block")
    commands: list[list[str]] = []
    for raw in match.group(1).splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        commands.append(line.split())
    if not commands:
        raise GateCacheError("the catalogue's full ordered block is empty")
    return commands


def ci_commands(root: Path) -> list[list[str]]:
    """Every gate command CI invokes, whatever YAML shape it is written in.

    Deliberately not a single `run:` regex.  The first version here matched
    only `run: scripts/check-x.sh` at the start of a line, so `- run: ...` and
    anything inside a `run: |` block would have slipped past the audit
    unregistered -- and an unregistered CI command is exactly the case this
    audit exists to catch.  Peeling the list dash and the `run:` key and then
    asking whether what remains *is* a gate command covers all three shapes,
    and errs toward finding more rather than fewer.
    """

    path = root / ".github/workflows/ci.yml"
    if not path.is_file():
        raise GateCacheError("no CI workflow to audit")
    commands: list[list[str]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("#"):
            continue
        if line.startswith("- "):
            line = line[2:].strip()
        if line.startswith("run:"):
            line = line[4:].strip()
        words = line.split()
        if (
            words
            and words[0].startswith("scripts/check")
            and words[0].endswith(".sh")
        ):
            commands.append(words)
    return commands


def audit(root: Path, quiet: bool = False) -> int:
    registry = load_registry(registry_path(root))
    registered = {tuple(gate["command"]): gate for gate in registry["gates"]}
    catalogue = [tuple(command) for command in catalogue_commands(root)]
    ci = [tuple(command) for command in ci_commands(root)]

    problems: list[str] = []
    for position, command in enumerate(catalogue, start=1):
        gate = registered.get(command)
        if gate is None:
            problems.append(f"catalogued command has no registry entry: {' '.join(command)}")
        elif gate["order"] != position:
            problems.append(
                f"registry order {gate['order']} does not match catalogue position "
                f"{position} for {' '.join(command)}"
            )
    for command in sorted(set(registered) - set(catalogue)):
        if not registered[command].get("ci_only"):
            problems.append(f"registry entry is not in the catalogue: {' '.join(command)}")
    for command in sorted(set(ci) - set(registered)):
        problems.append(f"CI runs an unregistered command: {' '.join(command)}")

    inventory = root / INVENTORY_RELATIVE
    current = inventory.read_text(encoding="utf-8") if inventory.is_file() else None
    if current != render_inventory(root):
        problems.append(
            f"{INVENTORY_RELATIVE} is not what its generator produces; "
            f"run scripts/check-gates.sh --inventory"
        )

    if registry.get("economy_inventory"):
        policy_checks = (
            ([sys.executable, "scripts/gate-economy.py", "--check"],
             "economic inventory does not reconcile"),
            ([sys.executable, "scripts/gate_sampling.py", "--check"],
             "campaign sampling policy does not reconcile"),
            ([sys.executable, "scripts/ci_gate_policy.py", "--self-test"],
             "CI trust-policy controls failed"),
            ([sys.executable, "scripts/ci_gate_policy.py", "--audit"],
             "CI gate policy does not reconcile"),
        )
        for command, label in policy_checks:
            result = subprocess.run(
                command,
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            if result.returncode != 0:
                detail = (result.stderr or result.stdout).strip()
                problems.append(f"{label}: {detail}")

    duplicates = [
        " ".join(command)
        for command in set(catalogue)
        if catalogue.count(command) > 1
    ]
    for duplicate in sorted(duplicates):
        problems.append(f"catalogue lists a command instance twice: {duplicate}")

    if not quiet:
        print(f"gate registry audit: {len(catalogue)} catalogued command instances, "
              f"{len(registry['gates'])} registry entries, {len(set(ci))} CI commands")
        kinds: dict[str, int] = {}
        for gate in registry["gates"]:
            kinds[gate["kind"]] = kinds.get(gate["kind"], 0) + 1
        print("  dispositions: " + ", ".join(f"{k}={v}" for k, v in sorted(kinds.items())))
        for gate in registry["gates"]:
            if gate["kind"] != "cacheable":
                print(f"  always fresh: {command_text(gate)} — {gate['reason']}")
    if problems:
        for problem in problems:
            print(f"  MISMATCH: {problem}", file=sys.stderr)
        print(f"REGISTRY AUDIT FAILED: {len(problems)} mismatches", file=sys.stderr)
        return 1
    if not quiet:
        print("REGISTRY AUDIT OK: every catalogued and CI command instance "
              "is registered exactly once")
    return 0


# --- plan / explain ---------------------------------------------------------


def show_plan(root: Path, arguments: argparse.Namespace) -> int:
    registry = load_registry(registry_path(root))
    cache, cache_reason = read_cache(cache_path(root))
    if cache_reason:
        print(f"cache: {cache_reason}")
    rows = plan(root, registry, cache, fresh=arguments.fresh)
    executed = sum(1 for row in rows if row["disposition"] == "fresh")
    reused = sum(1 for row in rows if row["disposition"] == "reused")
    certified = sum(1 for row in rows if row["disposition"] == "certified")
    for row in rows:
        marker = {
            "reused": "reuse ",
            "certified": "cert  ",
        }.get(row["disposition"], "RUN   ")
        print(f"{row['order']:>3} {marker} {command_text(row['gate'])}")
        if row["disposition"] == "fresh":
            print(f"    reason: {row['reason']}")
            if arguments.explain:
                for line in explain_row(cache, row):
                    print(line)
    print(
        f"PLAN: {len(rows)} rows, {executed} would execute, {reused} would reuse, "
        f"{certified} build-certified"
    )
    return 0


def render_inventory(root: Path) -> str:
    """Human-readable generated inventory of every gate's declared inputs.

    A function of the registry alone, never of the current tree, so the audit
    can hold the committed copy to its generator the way rule 5 holds every
    other generated artifact.
    """

    registry = load_registry(registry_path(root))
    lines = [
        "# Blanc gate input inventory",
        "",
        "Generated by `scripts/gate-cache.py inventory` from",
        "`scripts/gate-registry.json`. Do not edit by hand.",
        "",
    ]
    for gate in registry["gates"]:
        lines.append(f"## {gate['order']}. `{command_text(gate)}`")
        lines.append("")
        lines.append(f"- disposition: **{gate['kind']}**")
        if gate.get("reason"):
            lines.append(f"- reason: {gate['reason']}")
        if gate.get("note"):
            lines.append(f"- note: {gate['note']}")
        verdict = gate.get("verdict") or {}
        for pattern in verdict.get("summary_patterns", []):
            lines.append(f"- terminal summary must match `{pattern}` exactly once")
        inputs = gate.get("inputs", {})
        for kind in INPUT_KINDS:
            if kind not in inputs:
                continue
            value = inputs[kind]
            if kind == "populations":
                for spec in value:
                    excluded = spec.get("exclude", [])
                    suffix = f" excluding {', '.join(excluded)}" if excluded else ""
                    mode = spec.get("mode", "content")
                    where = {
                        "membership": "membership only",
                        "traversable": "readable, contributes no digest",
                    }.get(mode, "path and content")
                    lines.append(
                        f"- population: `{spec.get('root', '.')}/{spec['pattern']}`"
                        f"{suffix} ({where})"
                    )
            elif kind == "external":
                for spec in value:
                    lines.append(
                        f"- external: `{spec['id']}` at "
                        f"`{spec.get('path_env') or spec.get('path')}`"
                        + (f" pinned {spec['pin']}" if spec.get("pin") else "")
                    )
            elif kind == "clock":
                lines.append(
                    f"- clock: {value['kind']} from "
                    + ", ".join(f"`{item}`" for item in value["files"])
                )
            else:
                lines.append(f"- {kind}: " + ", ".join(f"`{item}`" for item in value))
        lines.append("")
    return "\n".join(lines)


INVENTORY_RELATIVE = "docs/GATE_INPUTS.md"


def show_inventory(root: Path, arguments: argparse.Namespace) -> int:
    text = render_inventory(root)
    if arguments.output:
        atomic_write(root / arguments.output, text)
        print(f"wrote {arguments.output}")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Selective execution and content-valid verdict reuse for Blanc's gates"
    )
    commands = parser.add_subparsers(dest="mode", required=True)

    runner = commands.add_parser("run", help="evaluate the registered full set")
    runner.add_argument(
        "--fresh",
        action="store_true",
        help="execute every row and refresh its record; adds work, never removes it",
    )
    runner.add_argument(
        "--echo", action="store_true", help="stream each executed gate's own output"
    )

    planner = commands.add_parser("plan", help="report what would run, without running it")
    planner.add_argument("--explain", action="store_true", help="name the inputs that moved")
    planner.add_argument("--fresh", action="store_true", help=argparse.SUPPRESS)

    commands.add_parser("audit", help="check the registry against the catalogue and CI")

    inventory = commands.add_parser("inventory", help="generate the readable input inventory")
    inventory.add_argument("--output", help="write to this path instead of stdout")

    commands.add_parser(
        "certify-build",
        help="record exact state immediately after a successful authoritative lake build",
    )
    commands.add_parser("self-test", help="run the fail-closed control suite")
    return parser


def main(argv: list[str]) -> int:
    arguments = build_parser().parse_args(argv)
    root = ROOT
    try:
        if arguments.mode == "plan":
            return show_plan(root, arguments)
        if arguments.mode == "audit":
            return audit(root)
        if arguments.mode == "inventory":
            return show_inventory(root, arguments)
        if arguments.mode == "self-test":
            from gate_cache_selftest import self_test  # noqa: PLC0415

            return self_test()
        if not acquire_lock(lock_path(root)):
            return 2
        try:
            if arguments.mode == "certify-build":
                certificate = write_build_certificate(root)
                print(
                    "OK — lake build certificate: "
                    f"{certificate['identity'][:16]} on {certificate['host']}"
                )
                return 0
            return run(root, arguments)
        finally:
            release_lock(lock_path(root))
    except GateCacheError as error:
        print(f"check-gates: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    raise SystemExit(main(sys.argv[1:]))
