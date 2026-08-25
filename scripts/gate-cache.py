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

*Lean closure is delegated, not duplicated.*  Blanc has 149 modules and no
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

Cache state lives under `.lake/`, is disposable, is never committed, and may
be deleted at any time: deleting it costs time and cannot cost correctness.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Iterable

SCHEMA_VERSION = 1

ROOT = Path(__file__).resolve().parent.parent

# Every path is derived from a root the caller passes, so the control suite can
# drive the whole engine against a scratch repository instead of asserting on a
# reimplementation of it.
REGISTRY_RELATIVE = "scripts/gate-registry.json"
CACHE_RELATIVE = ".lake/gate-cache.json"
REPORT_RELATIVE = ".lake/gate-report.md"
MANIFEST_RELATIVE = ".lake/gate-manifest.json"
LOCK_RELATIVE = ".lake/check-gates.lock"


def registry_path(root: Path) -> Path:
    return root / REGISTRY_RELATIVE


def cache_path(root: Path) -> Path:
    return root / CACHE_RELATIVE


def report_path(root: Path) -> Path:
    return root / REPORT_RELATIVE


def manifest_path(root: Path) -> Path:
    return root / MANIFEST_RELATIVE


def lock_path(root: Path) -> Path:
    return root / LOCK_RELATIVE

# How many historical successful records to retain per gate.  Eviction is a
# performance choice only: a pruned record simply causes a fresh run.
RECORDS_PER_GATE = 12

LEAN_TRACE_ROOTS = (
    ".lake/build/lib/lean",
    ".lake/packages/jaune/.lake/build/lib/lean",
)

IMPORT_LINE = re.compile(
    r"^(?:public[ \t]+)?import[ \t]+"
    r"([A-Za-z0-9_'.]+(?:[ \t]+[A-Za-z0-9_'.]+)*)[ \t]*$"
)

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
               "verdict", "prerequisite", "ci_only"}
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

    gates.sort(key=lambda gate: gate["order"])
    return registry


def command_text(gate: dict[str, Any]) -> str:
    return " ".join(gate["command"])


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
}


def resolve_path(root: Path, given: str) -> Path:
    """Repository-relative by default; `@name/`, `~` and absolute kept as given.

    Real inputs live outside the tree: the pinned EELS checkout's virtualenv,
    which is gitignored inside that checkout and so is invisible to its commit
    identity, and an EEST fixture template a WETH10 generator reads from `~`.
    Pretending either is a repository path would silently fingerprint nothing.
    """

    if given.startswith("@"):
        name, _, rest = given[1:].partition("/")
        entry = NAMED_ROOTS.get(name)
        if entry is None:
            raise GateCacheError(f"unknown named root: @{name}")
        variable, default = entry
        base = Path(os.path.expanduser(os.environ.get(variable) or default))
        return base / rest if rest else base
    expanded = Path(os.path.expanduser(given))
    return expanded if expanded.is_absolute() else root / given


def component_files(root: Path, paths: list[str]) -> tuple[str, dict[str, str]]:
    detail: dict[str, str] = {}
    for given in sorted(set(paths)):
        path = resolve_path(root, given)
        detail[given] = file_digest(path) if path.is_file() else "<absent>"
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
        if mode not in ("content", "membership"):
            raise GateCacheError(f"unknown population mode: {mode!r}")
        for name in glob_population(root, spec):
            # Namespaced by mode, so a path declared under both a content and a
            # membership population cannot have one reading silently overwrite
            # the other depending on declaration order.
            if mode == "content":
                detail[name] = file_digest(resolve_path(root, name))
            else:
                detail[f"membership:{name}"] = "<member>"
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
        elif line.lstrip().startswith(("import ", "import\t", "public import")):
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
        if isinstance(pin, str) and pin and not head.startswith(pin) and not pin.startswith(head):
            raise Unresolvable(
                f"external checkout {identifier} is at {head}, not the pinned {pin}"
            )
        detail[identifier] = head
    return digest_of(detail), detail


def component_env(names: list[str]) -> tuple[str, dict[str, str]]:
    detail = {name: os.environ.get(name, "<unset>") for name in sorted(set(names))}
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


def component_clock(kind: str) -> tuple[str, dict[str, str]]:
    """The current date, for gates whose exceptions expire.

    A gate holding an exception that expires on a date reads the clock whether
    it says so or not, so its verdict can change with no file changing at all.
    Declaring the clock makes yesterday's pass stop counting tomorrow.
    """

    if kind != "utc-date":
        raise GateCacheError(f"unknown clock kind: {kind}")
    detail = {"utc-date": time.strftime("%Y-%m-%d", time.gmtime())}
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
        "digest": digest_of({"kind": gate["kind"], "inputs": inputs, "verdict": gate.get("verdict")}),
        "detail": None,
    }
    here = Path(__file__).resolve().parent
    components["runner"] = {
        "digest": digest_of(
            {
                "schema": SCHEMA_VERSION,
                "gate-cache.py": file_digest(here / "gate-cache.py"),
                "check-gates.sh": file_digest(here / "check-gates.sh"),
            }
        ),
        "detail": None,
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
        digest, detail = component_clock(inputs["clock"])
        components["clock"] = {"digest": digest, "detail": detail}

    overall = digest_of(
        {name: entry["digest"] for name, entry in sorted(components.items())}
    )
    return overall, components


# --- cache ------------------------------------------------------------------
#
# Layout:
#
#   {"schema": 1,
#    "gates":  {"<id>": [ {"fingerprint", "components", "verdict",
#                          "provenance"}, ... newest last ... ]},
#    "details": {"<component-digest>": {"<path>": "<digest>"}}}
#
# Per-path detail is interned by component digest because the same corpus is
# an input to many gates; without interning, one 149-file population would be
# copied into every record that reads it.


def empty_cache() -> dict[str, Any]:
    return {"schema": SCHEMA_VERSION, "gates": {}, "details": {}}


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
    if not isinstance(cache, dict) or cache.get("schema") != SCHEMA_VERSION:
        return empty_cache(), "cache schema is missing or incompatible"
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


# --- locking ----------------------------------------------------------------
#
# `mkdir` because macOS has no flock(1); the same reason `gate-lock.sh` gives.
# Two concurrent selective runs would interleave their cache writes and their
# report, so a contending run is refused with the holder named rather than
# queued.


def acquire_lock(path: Path) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        path.mkdir()
    except FileExistsError:
        owner = path / "pid"
        try:
            pid = int(owner.read_text(encoding="utf-8").strip())
        except (OSError, ValueError):
            pid = None
        if pid is not None:
            try:
                os.kill(pid, 0)
            except OSError:
                print(
                    f"check-gates: reclaiming lock left by dead process {pid}",
                    file=sys.stderr,
                )
                shutil.rmtree(path, ignore_errors=True)
                return acquire_lock(path)
            print(
                f"REFUSED: another selective gate run holds {path} (pid {pid})",
                file=sys.stderr,
            )
            return False
        print(f"REFUSED: another selective gate run holds {path}", file=sys.stderr)
        return False
    (path / "pid").write_text(f"{os.getpid()}\n", encoding="utf-8")
    return True


def release_lock(path: Path) -> None:
    shutil.rmtree(path, ignore_errors=True)


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
        if gate["kind"] != "cacheable":
            row["disposition"] = "fresh"
            row["reason"] = gate["reason"]
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
    registry = load_registry(registry_path(root))
    cache, cache_reason = read_cache(cache_path(root))
    if cache_reason:
        print(f"check-gates: {cache_reason}; every gate will execute", file=sys.stderr)

    identity = tree_identity(root)
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
        print(f"[fresh ] {command_text(gate)}   (prerequisite refresh)")
        verdict, elapsed = execute(root, gate, echo=arguments.echo)
        prerequisites[gate["id"]] = {"verdict": verdict, "elapsed": elapsed}
        if not verdict["passed"]:
            problem = "; ".join(verdict["problems"])
            print(f"         FAILED: {problem}", file=sys.stderr)
            failures.append(f"{command_text(gate)}: {problem}")

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
            row["disposition"] = "fresh"
            row["reason"] = row["gate"]["reason"]
            row["verdict"] = done["verdict"]
            row["elapsed"] = done["elapsed"]
            row["cached"] = False
            row["cache_reason"] = "prerequisite refresh, never credited from a record"
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
    print(
        f"GATES OK: {len(rows)} rows, {executed} executed, {reused} reused "
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
                    row["record"]["provenance"] if row["disposition"] == "reused" else None
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
        if line.startswith("scripts/check-") and ".sh" in line:
            commands.append(line.split())
    return commands


def audit(root: Path) -> int:
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

    duplicates = [
        " ".join(command)
        for command in set(catalogue)
        if catalogue.count(command) > 1
    ]
    for duplicate in sorted(duplicates):
        problems.append(f"catalogue lists a command instance twice: {duplicate}")

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
    print("REGISTRY AUDIT OK: every catalogued and CI command instance is registered exactly once")
    return 0


# --- plan / explain ---------------------------------------------------------


def show_plan(root: Path, arguments: argparse.Namespace) -> int:
    registry = load_registry(registry_path(root))
    cache, cache_reason = read_cache(cache_path(root))
    if cache_reason:
        print(f"cache: {cache_reason}")
    rows = plan(root, registry, cache, fresh=arguments.fresh)
    executed = sum(1 for row in rows if row["disposition"] == "fresh")
    reused = len(rows) - executed
    for row in rows:
        marker = "reuse " if row["disposition"] == "reused" else "RUN   "
        print(f"{row['order']:>3} {marker} {command_text(row['gate'])}")
        if row["disposition"] == "fresh":
            print(f"    reason: {row['reason']}")
            if arguments.explain:
                for line in explain_row(cache, row):
                    print(line)
    print(f"PLAN: {len(rows)} rows, {executed} would execute, {reused} would reuse")
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
                    where = "membership only" if mode == "membership" else "path and content"
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
                lines.append(f"- clock: {value}")
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
            return run(root, arguments)
        finally:
            release_lock(lock_path(root))
    except GateCacheError as error:
        print(f"check-gates: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    raise SystemExit(main(sys.argv[1:]))
