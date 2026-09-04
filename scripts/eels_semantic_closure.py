#!/usr/bin/env python3
"""Derive and verify the semantic dependency closure of a pinned EELS target.

Blanc executes two independently pinned EELS references: the historical Prague
differential lane and the contract-neutral current-mainnet lane.  Both compare
Blanc against a Python program, so both need an answer to "which installed
software could have changed this result".

A Git commit does not answer it.  EELS declares its dependencies as ranges, and
those ranges cover keccak-256, secp256k1 recovery, the BN254/BLS/KZG
precompiles, RLP encoding — hence every transaction, receipt and trie root —
and U256 arithmetic.  Two checkouts at the same commit can disagree.

Hashing the whole installed environment answers it too loosely.  A digest over
every file under ``site-packages`` verifies an environment but never describes
one: it cannot say what to install, what changed, or whether the change could
matter, and it fails on documentation tooling that no transition ever imports.

This module answers it by *derivation*.  The package half of the semantic
closure is the set of installed distributions that provide a module imported
when the pinned transition code is imported — the specification package and,
where the lane drives it through a tool, that tool's entry module.  The Python
standard library is a different ownership domain: it has no ``dist-info``
record, so each generated platform row also inventories and hashes the
file-backed standard-library modules actually loaded by the isolated semantic
probe.  Nothing here is curated: the policy names the entry points, the target
interpreter names its standard-library roots, the probe reports what Python
actually loaded, and the checker re-derives both halves on every run.  A future
revision that reaches for a new distribution or standard-library module grows
the closure and reddens the lock until it is regenerated; a changed recorded
standard-library file reddens the platform row directly.

Distributions loaded only through a package's ``__init__`` chain — test
frameworks, HTTP clients, Git bindings pulled in by importing a test-support
package — are recorded separately with their versions, for attribution, and are
not content-pinned.  They cannot reach a transition.

Two digests fall out of the closure, and they are deliberately separate:

``versionsSha256``
    over ``name==version`` alone.  Platform-independent, because a wheel's
    version is.  Every platform enforces it.

``contentSha256``
    over the exact installed bytes of those distributions.  Platform-specific,
    because compiled extension modules are.  A platform enforces it once its
    row has been generated there, and fails closed until then.

The version digest is what a future tester reproduces from; the content digest
is what makes the reproduction tamper-evident.
"""

from __future__ import annotations

import hashlib
import json
import os
import py_compile
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable, Mapping, NoReturn


class ClosureError(RuntimeError):
    """A semantic-closure derivation or verification failed."""


def fail(message: str) -> NoReturn:
    raise ClosureError(message)


# Installer-owned metadata varies with *how* a wheel was installed — `uv` and
# `pip` disagree on all of these — while the wheel's own payload does not.
# Excluding them is what lets one recorded digest survive two provisioning
# recipes; including them would reintroduce the churn this module exists to
# remove.  Everything the wheel itself ships (METADATA, WHEEL, entry_points,
# licences, top_level) stays inside the digest.
INSTALLER_METADATA = (
    "INSTALLER",
    "REQUESTED",
    "RECORD",
    "direct_url.json",
    "uv_cache.json",
    "uv_build.json",
)

# Byte-compiled output is excluded only because every accepted oracle process
# is forced onto an impossible cache root.  ``-B`` alone is insufficient: it
# prevents writes but still reads a timestamp-valid adjacent cache.
CONTENT_EXCLUDES = ("**/__pycache__/**", "**/*.pyc", "**/*.pyo")

BYTECODE_POLICY = {
    "dontWriteBytecode": True,
    "pycachePrefix": "/dev/null",
}

PYTHON_ISOLATION_ARGS = (
    "-I", "-s", "-B", "-X", "pycache_prefix=/dev/null",
)

# The standard library has no RECORD owner.  Its configured roots come from
# the target interpreter itself and the isolated probe selects only loaded,
# file-backed modules.  This policy is recorded in both pins so that a future
# writer cannot silently return to distribution-only measurement.
STANDARD_LIBRARY_POLICY = {
    "roots": ["stdlib", "platstdlib"],
    "selection": "loadedModuleFiles",
    "excludes": [
        "**/site-packages/**",
        "**/dist-packages/**",
    ],
}

# The Mach-O/ELF launcher is not necessarily the interpreter implementation.
# Generated native rows therefore bind every loaded image owned by the target
# interpreter base but outside the separately inventoried standard library.
INTERPRETER_RUNTIME_POLICY = {
    "root": "basePrefix",
    "selection": "loadedNativeImagesOutsideStandardLibraryAndExecutable",
}


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def _digest(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def is_sha256(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(
        character in "0123456789abcdef" for character in value
    )


def versions_digest(distributions: Iterable[dict[str, Any]]) -> str:
    """Digest the platform-independent identity: what to install."""

    return _digest(
        sorted(f"{entry['name']}=={entry['version']}" for entry in distributions)
    )


def content_digest(distributions: Iterable[dict[str, Any]]) -> str:
    """Digest the platform-specific identity: the exact installed bytes."""

    return _digest(
        sorted([entry["name"], entry["contentSha256"]] for entry in distributions)
    )


def standard_library_digest(files: Iterable[dict[str, Any]]) -> str:
    """Digest an attributable standard-library file inventory."""

    return _digest(
        sorted([entry["path"], entry["sha256"]] for entry in files)
    )


def interpreter_runtime_digest(files: Iterable[dict[str, Any]]) -> str:
    """Digest the loaded native components behind the Python launcher."""

    return _digest(sorted([entry["path"], entry["sha256"]] for entry in files))


def environment_content_digest(
    distributions: Iterable[dict[str, Any]], standard_library: dict[str, Any],
    interpreter_runtime: dict[str, Any],
) -> str:
    """Digest all byte-owning domains behind one platform row."""

    return _digest(
        {
            "distributions": sorted(
                [entry["name"], entry["contentSha256"]]
                for entry in distributions
            ),
            "standardLibrary": standard_library["contentSha256"],
            "interpreterRuntime": interpreter_runtime["contentSha256"],
        }
    )


def _is_under(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def assert_bytecode_policy(fail_with: Any, *, label: str) -> None:
    """Refuse an oracle process that could read or create a bytecode cache."""

    if sys.dont_write_bytecode is not True:
        fail_with(f"{label} must run with bytecode writes disabled")
    if sys.pycache_prefix != BYTECODE_POLICY["pycachePrefix"]:
        fail_with(
            f"{label} must run with sys.pycache_prefix="
            f"{BYTECODE_POLICY['pycachePrefix']!r}; found {sys.pycache_prefix!r}"
        )


def loaded_native_images() -> list[str]:
    """Return native images actually mapped into the running interpreter."""

    if sys.platform == "darwin":
        import ctypes

        process = ctypes.CDLL(None)
        count = process._dyld_image_count
        count.argtypes = []
        count.restype = ctypes.c_uint32
        image_name = process._dyld_get_image_name
        image_name.argtypes = [ctypes.c_uint32]
        image_name.restype = ctypes.c_char_p
        result = []
        for index in range(count()):
            raw = image_name(index)
            if raw:
                result.append(os.path.realpath(os.fsdecode(raw)))
        return sorted(set(result))
    if sys.platform.startswith("linux"):
        try:
            lines = Path("/proc/self/maps").read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            fail(f"cannot inventory loaded Linux interpreter images: {exc}")
        result = []
        for line in lines:
            path = line.split(maxsplit=5)[-1]
            if path.startswith("/"):
                result.append(os.path.realpath(path.removesuffix(" (deleted)")))
        return sorted(set(result))
    fail(f"cannot inventory loaded interpreter images on {sys.platform}")


def measure_interpreter_runtime(
    base_prefix: str | Path,
    *,
    loaded_images: Iterable[str | Path],
    python_executable: str | Path,
    standard_library_roots: Iterable[str | Path],
) -> dict[str, Any]:
    """Inventory loaded native interpreter components outside the stdlib."""

    base = Path(base_prefix).resolve()
    if not base.is_dir():
        fail(f"target interpreter base prefix is absent: {base}")
    executable = Path(python_executable).resolve()
    excluded = [Path(path).resolve() for path in standard_library_roots]
    records: list[dict[str, str]] = []
    seen: set[Path] = set()
    for supplied in sorted(Path(path) for path in loaded_images):
        # dyld may report system-cache image names that have no standalone
        # filesystem entry.  They are outside this policy's basePrefix owner,
        # so reject/measure only after a non-strict normalization proves the
        # candidate belongs to the interpreter installation.
        candidate = supplied.resolve()
        if not _is_under(candidate, base):
            continue
        try:
            resolved = candidate.resolve(strict=True)
        except OSError as exc:
            fail(f"cannot resolve loaded interpreter image {supplied}: {exc}")
        if resolved == executable or resolved in seen:
            continue
        if any(_is_under(resolved, root) for root in excluded):
            continue
        seen.add(resolved)
        try:
            sha256 = hashlib.sha256(resolved.read_bytes()).hexdigest()
        except OSError as exc:
            fail(f"cannot fingerprint interpreter runtime component {resolved}: {exc}")
        records.append({
            "path": f"basePrefix/{resolved.relative_to(base).as_posix()}",
            "sha256": sha256,
        })
    records.sort(key=lambda entry: entry["path"])
    return {
        "fileRecords": len(records),
        "contentSha256": interpreter_runtime_digest(records),
        "files": records,
    }


def validate_interpreter_runtime(
    document: Any, fail_with: Any, *, label: str
) -> dict[str, Any]:
    """Validate a root-relative loaded-native-image inventory."""

    expected = {"fileRecords", "contentSha256", "files"}
    if not isinstance(document, dict) or set(document) != expected:
        actual = set(document) if isinstance(document, dict) else set()
        fail_with(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )
    if not is_sha256(document["contentSha256"]):
        fail_with(f"{label} content digest is malformed")
    files = document["files"]
    if not isinstance(files, list):
        fail_with(f"{label} files are malformed")
    seen: set[str] = set()
    for entry in files:
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256"}:
            fail_with(f"{label} file row is malformed")
        path = entry["path"]
        root, separator, relative = path.partition("/") if isinstance(path, str) else ("", "", "")
        if root != INTERPRETER_RUNTIME_POLICY["root"] or not separator \
                or not relative or Path(relative).is_absolute() \
                or ".." in Path(relative).parts:
            fail_with(f"{label} path is outside the interpreter base: {path!r}")
        if path in seen:
            fail_with(f"{label} names {path} twice")
        seen.add(path)
        if not is_sha256(entry["sha256"]):
            fail_with(f"{label} {path} digest is malformed")
    if type(document["fileRecords"]) is not int \
            or document["fileRecords"] != len(files):
        fail_with(f"{label} file-record count does not match its list")
    if document["contentSha256"] != interpreter_runtime_digest(files):
        fail_with(f"{label} content digest does not match its file rows")
    return document


def measure_standard_library(
    roots: Mapping[str, str | Path],
    *,
    loaded_files: Iterable[str | Path],
    implementation: str,
    version: str,
    site_packages: Iterable[str | Path] = (),
) -> dict[str, Any]:
    """Inventory the target interpreter's loaded standard-library bytes.

    Paths in the committed inventory are relative to the logical sysconfig
    root, never host-absolute.  Resolved files are de-duplicated when stdlib and
    platstdlib name the same tree.  Site-package roots are excluded because the
    distribution closure owns those bytes separately.  Built-in and frozen
    modules have no file to add; their code is part of the interpreter.
    """

    expected_roots = STANDARD_LIBRARY_POLICY["roots"]
    if set(roots) != set(expected_roots):
        fail(
            "standard-library roots differ: "
            f"missing={sorted(set(expected_roots) - set(roots))}, "
            f"extra={sorted(set(roots) - set(expected_roots))}"
        )
    excluded_roots = [Path(path).resolve() for path in site_packages]
    resolved_roots = [
        (label, Path(roots[label]).resolve()) for label in expected_roots
    ]
    for label, root in resolved_roots:
        if not root.is_dir():
            fail(f"target {label} standard-library root is absent: {root}")
    seen_files: set[Path] = set()
    records: list[dict[str, str]] = []
    for supplied in sorted(Path(path) for path in loaded_files):
        try:
            resolved = supplied.resolve(strict=True)
        except OSError as exc:
            fail(f"cannot resolve loaded module file {supplied}: {exc}")
        if any(_is_under(resolved, excluded) for excluded in excluded_roots):
            continue
        selected = next(
            (
                (label, root, resolved.relative_to(root))
                for label, root in resolved_roots
                if _is_under(resolved, root)
            ),
            None,
        )
        if selected is None or resolved in seen_files:
            continue
        label, _root, relative = selected
        if "site-packages" in relative.parts or "dist-packages" in relative.parts:
            continue
        seen_files.add(resolved)
        try:
            sha256 = hashlib.sha256(resolved.read_bytes()).hexdigest()
        except OSError as exc:
            fail(f"cannot fingerprint standard-library file {resolved}: {exc}")
        records.append({"path": f"{label}/{relative.as_posix()}", "sha256": sha256})
    records.sort(key=lambda entry: entry["path"])
    if not records:
        fail("target standard-library inventory is empty")
    return {
        "implementation": implementation,
        "version": version,
        "fileRecords": len(records),
        "contentSha256": standard_library_digest(records),
        "files": records,
    }


def validate_standard_library(
    document: Any, fail_with: Any, *, label: str
) -> dict[str, Any]:
    """Validate a content-addressed loaded-stdlib inventory."""

    expected = {
        "implementation", "version", "fileRecords", "contentSha256", "files",
    }
    if not isinstance(document, dict) or set(document) != expected:
        actual = set(document) if isinstance(document, dict) else set()
        fail_with(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )
    for field in ("implementation", "version"):
        if not isinstance(document[field], str) or not document[field]:
            fail_with(f"{label} {field} is malformed")
    if not is_sha256(document["contentSha256"]):
        fail_with(f"{label} content digest is malformed")
    files = document["files"]
    if not isinstance(files, list) or not files:
        fail_with(f"{label} names no loaded standard-library file")
    seen: set[str] = set()
    for entry in files:
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256"}:
            fail_with(f"{label} file row is malformed")
        path = entry["path"]
        sha256 = entry["sha256"]
        if not isinstance(path, str) or not path:
            fail_with(f"{label} file path is malformed")
        root, separator, relative = path.partition("/")
        if not separator or root not in STANDARD_LIBRARY_POLICY["roots"] \
                or not relative or Path(relative).is_absolute() \
                or ".." in Path(relative).parts:
            fail_with(f"{label} file path is outside its configured roots: {path!r}")
        if path in seen:
            fail_with(f"{label} names {path} twice")
        seen.add(path)
        if not is_sha256(sha256):
            fail_with(f"{label} {path} digest is malformed")
    if type(document["fileRecords"]) is not int \
            or document["fileRecords"] != len(files):
        fail_with(f"{label} file-record count does not match its list")
    if document["contentSha256"] != standard_library_digest(files):
        fail_with(f"{label} content digest does not match its file rows")
    return document


def file_records(distributions: Iterable[dict[str, Any]]) -> int:
    return sum(int(entry["files"]) for entry in distributions)


def validate_policy(policy: Any) -> dict[str, Any]:
    if not isinstance(policy, dict):
        fail("closure policy is not an object")
    expected = {"transitionModules", "transitionPackages", "runtimePackages"}
    if set(policy) != expected:
        fail(
            "closure policy keys differ: "
            f"missing={sorted(expected - set(policy))}, "
            f"extra={sorted(set(policy) - expected)}"
        )
    for key in sorted(expected):
        value = policy[key]
        if not isinstance(value, list) or any(
            not isinstance(item, str) or not item for item in value
        ):
            fail(f"closure policy {key} is not a list of module names")
    if not policy["transitionPackages"] and not policy["transitionModules"]:
        fail("closure policy names no transition entry point")
    return {key: list(policy[key]) for key in sorted(expected)}


_PROBE = r'''
"""Report the semantic closure from inside the pinned target interpreter."""

import hashlib
import importlib
import json
import os
import pkgutil
import sys
import sysconfig
from pathlib import Path

request = json.loads(sys.argv[1])
site_packages = Path(request["sitePackages"]).resolve()
installer_metadata = set(request["installerMetadata"])

if sys.dont_write_bytecode is not request["bytecodePolicy"]["dontWriteBytecode"]:
    raise RuntimeError("semantic-closure probe can write bytecode")
if sys.pycache_prefix != request["bytecodePolicy"]["pycachePrefix"]:
    raise RuntimeError(
        f"semantic-closure probe pycache prefix is {sys.pycache_prefix!r}, "
        f"expected {request['bytecodePolicy']['pycachePrefix']!r}"
    )

# A lane may resolve the specification from the checkout's source tree rather
# than from an install.  Those paths are admitted here, by name, instead of
# through PYTHONPATH, so the probe keeps running under -I with no ambient
# environment reaching it.  Source under the pinned checkout is covered by the
# commit pin and never enters the closure: nothing in site-packages owns it.
for entry in request["sourcePaths"]:
    sys.path.insert(0, entry)


def loaded_files():
    found = set()
    for module in list(sys.modules.values()):
        value = getattr(module, "__file__", None)
        if value:
            try:
                found.add(os.path.realpath(value))
            except OSError:
                pass
    return found


def loaded_native_images():
    if sys.platform == "darwin":
        import ctypes

        process = ctypes.CDLL(None)
        count = process._dyld_image_count
        count.argtypes = []
        count.restype = ctypes.c_uint32
        image_name = process._dyld_get_image_name
        image_name.argtypes = [ctypes.c_uint32]
        image_name.restype = ctypes.c_char_p
        return sorted({
            os.path.realpath(os.fsdecode(image_name(index)))
            for index in range(count()) if image_name(index)
        })
    if sys.platform.startswith("linux"):
        paths = set()
        for line in Path("/proc/self/maps").read_text(encoding="utf-8").splitlines():
            path = line.split(maxsplit=5)[-1]
            if path.startswith("/"):
                paths.add(os.path.realpath(path.removesuffix(" (deleted)")))
        return sorted(paths)
    raise RuntimeError(f"cannot inventory native images on {sys.platform}")


def import_all(modules, packages):
    skipped = []
    for name in modules:
        importlib.import_module(name)
    for name in packages:
        package = importlib.import_module(name)
        paths = getattr(package, "__path__", None)
        if paths is None:
            continue
        for found in pkgutil.walk_packages(paths, package.__name__ + "."):
            try:
                importlib.import_module(found.name)
            except Exception as exc:  # a fork may gate on optional tooling
                skipped.append({"module": found.name, "reason": repr(exc)})
    return skipped


# --- installed distributions, and which files each one owns -------------------

def read_record(info):
    record = info / "RECORD"
    if not record.exists():
        return None
    owned = []
    for line in record.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        relative = line.rsplit(",", 2)[0]
        if relative.startswith('"') and relative.endswith('"'):
            relative = relative[1:-1]
        parts = relative.split("/")
        if "__pycache__" in parts or relative.endswith((".pyc", ".pyo")):
            continue
        if len(parts) == 2 and parts[0] == info.name and parts[1] in installer_metadata:
            continue
        owned.append(relative)
    return sorted(set(owned))


distributions = {}
owner_of = {}
for info in sorted(site_packages.glob("*.dist-info")):
    name, _, version = info.name[: -len(".dist-info")].rpartition("-")
    owned = read_record(info)
    if owned is None:
        continue
    distributions[name] = {"version": version, "info": info.name, "files": owned}
    for relative in owned:
        try:
            resolved = os.path.realpath(site_packages / relative)
        except OSError:
            continue
        owner_of[resolved] = name

# --- tier one: the code that computes a transition ----------------------------

before = loaded_files()
skipped = import_all(request["transitionModules"], request["transitionPackages"])
transition_files = loaded_files() - before

# --- tier two: whatever a package __init__ chain drags in afterwards ----------

runtime_skipped = []
for name in request["runtimePackages"]:
    try:
        importlib.import_module(name)
    except Exception as exc:
        runtime_skipped.append({"module": name, "reason": repr(exc)})
runtime_files = loaded_files() - before - transition_files


def hit_distributions(files):
    hits = {}
    for path in files:
        owner = owner_of.get(path)
        if owner is None:
            continue
        try:
            relative = Path(path).relative_to(site_packages).parts[0]
        except ValueError:
            relative = Path(path).name
        # Report the importable name, not the file.  A compiled extension is
        # installed as `_cffi_backend.cpython-311-darwin.so` here and
        # `_cffi_backend.cpython-311-x86_64-linux-gnu.so` elsewhere, and this
        # list is pinned in the platform-*independent* half of the document,
        # where a per-platform filename would redden the other platform for a
        # reason that has nothing to do with the pin.
        hits.setdefault(owner, set()).add(relative.split(".")[0])
    return hits


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def content(name):
    """Digest the exact installed bytes this distribution owns."""

    records = []
    for relative in distributions[name]["files"]:
        path = site_packages / relative
        if not path.exists() or path.is_dir():
            # A RECORD entry with no file is a broken install, not a digest
            # input; surface it rather than hashing around it.
            return None, relative
        records.append({"path": relative, "sha256": sha256_file(path)})
    encoded = json.dumps(
        records, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return {
        "files": len(records),
        "contentSha256": hashlib.sha256(encoded).hexdigest(),
    }, None


transition_hits = hit_distributions(transition_files)
runtime_hits = hit_distributions(runtime_files)

closure = []
for name in sorted(transition_hits):
    measured, missing = content(name)
    if measured is None:
        raise RuntimeError(
            f"distribution {name} lists {missing} in its RECORD but the file is absent"
        )
    closure.append({
        "name": name,
        "version": distributions[name]["version"],
        "modules": sorted(transition_hits[name]),
        "files": measured["files"],
        "contentSha256": measured["contentSha256"],
    })

runtime_only = [
    {"name": name, "version": distributions[name]["version"]}
    for name in sorted(set(runtime_hits) - set(transition_hits))
]

print(json.dumps({
    "distributions": closure,
    "runtimeOnly": runtime_only,
    "skipped": sorted(skipped, key=lambda item: item["module"]),
    "runtimeSkipped": runtime_skipped,
    "interpreter": {
        "implementation": sys.implementation.name,
        "version": ".".join(str(part) for part in sys.version_info[:3]),
        "basePrefix": os.path.realpath(sys.base_prefix),
    },
    "bytecodePolicy": {
        "dontWriteBytecode": sys.dont_write_bytecode,
        "pycachePrefix": sys.pycache_prefix,
    },
    # Inventorying images imports ctypes; put it before loaded_files() so the
    # resulting stdlib extension is itself included in the file-backed half.
    "interpreterRuntimeImages": loaded_native_images(),
    "standardLibraryRoots": {
        "stdlib": sysconfig.get_path("stdlib"),
        "platstdlib": sysconfig.get_path("platstdlib"),
    },
    "standardLibraryFiles": sorted(loaded_files()),
    "sitePackages": str(site_packages),
}, sort_keys=True))
'''


def derive(
    python: Path,
    site_packages: Path,
    policy: dict[str, Any],
    *,
    cwd: Path,
    env: dict[str, str],
    source_paths: Iterable[Path] = (),
    timeout: int = 300,
) -> dict[str, Any]:
    """Run the probe in the target interpreter and assemble a closure document."""

    checked = validate_policy(policy)
    request = dict(checked)
    request["sitePackages"] = str(site_packages)
    request["installerMetadata"] = list(INSTALLER_METADATA)
    request["sourcePaths"] = [str(path) for path in source_paths]
    request["bytecodePolicy"] = dict(BYTECODE_POLICY)
    try:
        result = subprocess.run(
            [str(python), *PYTHON_ISOLATION_ARGS, "-c", _PROBE,
             json.dumps(request)],
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        fail(f"cannot run the semantic-closure probe: {exc}")
    if result.returncode != 0:
        fail(f"semantic-closure probe failed: {result.stderr.strip()}")
    try:
        observed = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        fail(f"semantic-closure probe emitted non-JSON: {exc}")

    distributions = observed["distributions"]
    if not distributions:
        fail("semantic closure is empty; the probe imported no pinned dependency")
    standard_library = measure_standard_library(
        observed["standardLibraryRoots"],
        loaded_files=observed["standardLibraryFiles"],
        implementation=observed["interpreter"]["implementation"],
        version=observed["interpreter"]["version"],
        site_packages=[site_packages],
    )
    interpreter_runtime = measure_interpreter_runtime(
        observed["interpreter"]["basePrefix"],
        loaded_images=observed["interpreterRuntimeImages"],
        python_executable=python,
        standard_library_roots=observed["standardLibraryRoots"].values(),
    )
    try:
        python_executable_sha256 = hashlib.sha256(python.read_bytes()).hexdigest()
    except OSError as exc:
        fail(f"cannot fingerprint target interpreter {python}: {exc}")
    return {
        "policy": checked,
        "interpreter": observed["interpreter"],
        "bytecodePolicy": observed["bytecodePolicy"],
        "pythonExecutableSha256": python_executable_sha256,
        "distributions": distributions,
        "count": len(distributions),
        "fileRecords": file_records(distributions),
        "versionsSha256": versions_digest(distributions),
        "contentSha256": environment_content_digest(
            distributions, standard_library, interpreter_runtime
        ),
        "standardLibrary": standard_library,
        "interpreterRuntime": interpreter_runtime,
        "runtimeOnly": observed["runtimeOnly"],
        "skipped": observed["skipped"],
    }


def versions_of(document: dict[str, Any]) -> list[str]:
    return sorted(
        f"{entry['name']}=={entry['version']}" for entry in document["distributions"]
    )


def compare_versions(recorded: dict[str, Any], observed: dict[str, Any]) -> list[str]:
    """Name every difference in the platform-independent identity."""

    problems: list[str] = []
    if recorded["policy"] != observed["policy"]:
        problems.append(
            "closure policy differs: recorded "
            f"{json.dumps(recorded['policy'], sort_keys=True)}, observed "
            f"{json.dumps(observed['policy'], sort_keys=True)}"
        )
    was = {entry["name"]: entry["version"] for entry in recorded["distributions"]}
    now = {entry["name"]: entry["version"] for entry in observed["distributions"]}
    for name in sorted(set(now) - set(was)):
        problems.append(
            f"{name} {now[name]} entered the semantic closure; the pinned "
            "reference reached for a dependency it did not previously import"
        )
    for name in sorted(set(was) - set(now)):
        problems.append(
            f"{name} {was[name]} left the semantic closure; it is pinned but "
            "no longer imported by the pinned transition code"
        )
    for name in sorted(set(was) & set(now)):
        if was[name] != now[name]:
            problems.append(
                f"{name} is {now[name]}, pinned at {was[name]}"
            )
    if not problems and recorded["versionsSha256"] != observed["versionsSha256"]:
        problems.append("semantic-closure version digest differs with no named cause")
    return problems


def compare_content(recorded: dict[str, Any], observed: dict[str, Any]) -> list[str]:
    """Name every difference in the exact installed bytes."""

    problems: list[str] = []
    was = {entry["name"]: entry for entry in recorded["distributions"]}
    now = {entry["name"]: entry for entry in observed["distributions"]}
    for name in sorted(set(was) & set(now)):
        if "contentSha256" not in was[name]:
            continue
        if was[name]["contentSha256"] != now[name]["contentSha256"]:
            problems.append(
                f"{name} {now[name]['version']} is installed at the pinned version "
                f"but its {now[name]['files']} files do not match the pinned bytes"
            )
        elif was[name].get("files") != now[name]["files"]:
            problems.append(
                f"{name} file count is {now[name]['files']}, pinned at "
                f"{was[name].get('files')}"
            )
    recorded_stdlib = recorded.get("standardLibrary")
    observed_stdlib = observed.get("standardLibrary")
    if recorded_stdlib is None and observed_stdlib is not None:
        problems.append("the pinned platform row does not bind the Python standard library")
    elif recorded_stdlib is not None and observed_stdlib is None:
        problems.append("the observed environment did not measure the Python standard library")
    elif recorded_stdlib is not None and observed_stdlib is not None:
        stdlib_problems: list[str] = []
        for field in ("implementation", "version"):
            if recorded_stdlib.get(field) != observed_stdlib.get(field):
                stdlib_problems.append(
                    f"standard library {field} is {observed_stdlib.get(field)!r}, "
                    f"pinned at {recorded_stdlib.get(field)!r}"
                )
        old_files = {
            entry["path"]: entry["sha256"] for entry in recorded_stdlib.get("files", [])
        }
        new_files = {
            entry["path"]: entry["sha256"] for entry in observed_stdlib.get("files", [])
        }
        for path in sorted(set(new_files) - set(old_files)):
            stdlib_problems.append(f"standard-library file {path} is newly present")
        for path in sorted(set(old_files) - set(new_files)):
            stdlib_problems.append(f"standard-library file {path} is missing")
        for path in sorted(set(old_files) & set(new_files)):
            if old_files[path] != new_files[path]:
                stdlib_problems.append(
                    f"standard-library file {path} does not match the pinned bytes"
                )
        if not stdlib_problems and (
            recorded_stdlib.get("fileRecords") != observed_stdlib.get("fileRecords")
            or recorded_stdlib.get("contentSha256") != observed_stdlib.get("contentSha256")
        ):
            stdlib_problems.append(
                "standard-library digest differs with no named file cause"
            )
        problems.extend(stdlib_problems)
    recorded_runtime = recorded.get("interpreterRuntime")
    observed_runtime = observed.get("interpreterRuntime")
    if recorded_runtime is None and observed_runtime is not None:
        problems.append("the pinned platform row does not bind interpreter runtime images")
    elif recorded_runtime is not None and observed_runtime is None:
        problems.append("the observed environment did not measure interpreter runtime images")
    elif recorded_runtime is not None and observed_runtime is not None:
        runtime_problems: list[str] = []
        old_files = {
            entry["path"]: entry["sha256"]
            for entry in recorded_runtime.get("files", [])
        }
        new_files = {
            entry["path"]: entry["sha256"]
            for entry in observed_runtime.get("files", [])
        }
        for path in sorted(set(new_files) - set(old_files)):
            runtime_problems.append(f"interpreter runtime image {path} is newly present")
        for path in sorted(set(old_files) - set(new_files)):
            runtime_problems.append(f"interpreter runtime image {path} is missing")
        for path in sorted(set(old_files) & set(new_files)):
            if old_files[path] != new_files[path]:
                runtime_problems.append(
                    f"interpreter runtime image {path} does not match the pinned bytes"
                )
        if not runtime_problems and (
            recorded_runtime.get("fileRecords") != observed_runtime.get("fileRecords")
            or recorded_runtime.get("contentSha256")
                != observed_runtime.get("contentSha256")
        ):
            runtime_problems.append(
                "interpreter runtime digest differs with no named image cause"
            )
        problems.extend(runtime_problems)
    return problems


def platform_key(system: str, machine: str) -> str:
    """The canonical row name for a native platform, or a fail-closed refusal."""

    canonical_machine = {
        "arm64": "arm64",
        "aarch64": "arm64",
        "x86_64": "x86_64",
        "amd64": "x86_64",
    }.get(machine.lower())
    canonical_system = {"darwin": "macos", "linux": "linux"}.get(system.lower())
    if canonical_system is None or canonical_machine is None:
        fail(f"unsupported platform for a semantic-closure row: {system}/{machine}")
    return f"{canonical_system}-{canonical_machine}"


def assert_pinned_versions(pin: dict[str, Any], fail_with: Any, *, label: str) -> str:
    """Hold the running interpreter against a pin, in process and in microseconds.

    This is the cheap half of the contract, and it is the half that has to run
    everywhere: every differential already executes inside the target
    interpreter, so it can answer "are the pinned distributions the ones I am
    about to compute with" without spawning anything.  Deriving the closure —
    asking which distributions *should* be pinned — is the expensive half and
    belongs to the lane's own registered gate.
    """

    from importlib.metadata import PackageNotFoundError, version as installed_version

    section = pin["semanticClosure"]
    problems: list[str] = []
    for entry in section["distributions"]:
        try:
            found = installed_version(entry["name"])
        except PackageNotFoundError:
            problems.append(f"{entry['name']} is pinned at {entry['version']} but absent")
            continue
        if found != entry["version"]:
            problems.append(f"{entry['name']} is {found}, pinned at {entry['version']}")
    if problems:
        fail_with(
            f"{label} does not match its pin — a differential run here would not "
            "be reproducible: " + "; ".join(problems)
        )
    return (
        f"{len(section['distributions'])} pinned distributions at "
        f"{section['versionsSha256'][:12]}"
    )


PRAGUE_PIN_PATH = Path(__file__).resolve().parent / "eels-prague-closure.json"


def load_pin(path: Path | None = None) -> dict[str, Any]:
    target = PRAGUE_PIN_PATH if path is None else path
    try:
        return json.loads(target.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read the semantic-closure pin {target}: {exc}")


def assert_prague_environment(fail_with: Any) -> str:
    """The one line every Prague differential runs before it trusts an oracle.

    A Git commit pins the specification's source; this pins what that source
    imports.  Both have to hold before a comparison against EELS means anything.
    """

    assert_bytecode_policy(fail_with, label="pinned EELS Prague environment")
    pin = load_pin()
    versions = assert_pinned_versions(
        pin, fail_with, label="pinned EELS Prague environment"
    )
    import platform
    import sys
    import sysconfig

    native = platform_key(platform.system(), platform.machine())
    row = pin.get("platforms", {}).get(native)
    if row is None:
        return f"{versions}; standard-library bytes unrecorded on {native}"
    try:
        roots = {
            "stdlib": sysconfig.get_path("stdlib"),
            "platstdlib": sysconfig.get_path("platstdlib"),
        }
        recorded = row.get("standardLibrary")
        if not isinstance(recorded, dict):
            fail_with("pinned EELS Prague platform row does not bind stdlib bytes")
        loaded_files = []
        for entry in recorded.get("files", []):
            label, separator, relative = entry.get("path", "").partition("/")
            if not separator or label not in roots or not relative:
                fail_with("pinned EELS Prague standard-library path is invalid")
            loaded_files.append(Path(roots[label]) / relative)
        observed = measure_standard_library(
            roots,
            loaded_files=loaded_files,
            implementation=sys.implementation.name,
            version=".".join(str(part) for part in sys.version_info[:3]),
        )
        runtime = measure_interpreter_runtime(
            sys.base_prefix,
            loaded_images=loaded_native_images(),
            python_executable=sys.executable,
            standard_library_roots=roots.values(),
        )
        executable_sha256 = hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest()
    except ClosureError as exc:
        fail_with(f"pinned EELS Prague environment cannot measure stdlib: {exc}")
    except OSError as exc:
        fail_with(f"pinned EELS Prague environment cannot fingerprint Python: {exc}")
    if executable_sha256 != row.get("pythonExecutableSha256"):
        fail_with("pinned EELS Prague Python executable does not match its native row")
    problems = compare_content(
        {
            "distributions": [],
            "standardLibrary": row.get("standardLibrary"),
            "interpreterRuntime": row.get("interpreterRuntime"),
        },
        {
            "distributions": [],
            "standardLibrary": observed,
            "interpreterRuntime": runtime,
        },
    )
    if problems:
        fail_with(
            "pinned EELS Prague native runtime does not match its pin: "
            + "; ".join(problems)
        )
    return (
        f"{versions}; {observed['fileRecords']} pinned standard-library files "
        f"at {observed['contentSha256'][:12]}; "
        f"{runtime['fileRecords']} loaded interpreter runtime images at "
        f"{runtime['contentSha256'][:12]}"
    )


def render_constraints(document: dict[str, Any], *, header: Iterable[str] = ()) -> str:
    """Render the closure as a pip constraints file a provisioner can consume."""

    lines = [f"# {line}" if line else "#" for line in header]
    lines.extend(versions_of(document))
    return "\n".join(lines) + "\n"


def report(document: dict[str, Any], *, label: str) -> str:
    lines = [
        f"{label}: {document['count']} distributions, "
        f"{document['fileRecords']} files, versions {document['versionsSha256'][:12]}"
    ]
    if document.get("standardLibrary"):
        stdlib = document["standardLibrary"]
        lines.append(
            f"  standard library: {stdlib['implementation']} {stdlib['version']}, "
            f"{stdlib['fileRecords']} files, content {stdlib['contentSha256'][:12]}"
        )
    for entry in document["distributions"]:
        lines.append(
            f"  {entry['name']}=={entry['version']}"
            f"  ({', '.join(entry['modules'])})"
        )
    if document.get("runtimeOnly"):
        names = ", ".join(
            f"{entry['name']}=={entry['version']}" for entry in document["runtimeOnly"]
        )
        lines.append(
            f"  not on the transition path ({len(document['runtimeOnly'])}): {names}"
        )
    return "\n".join(lines)


def self_check() -> int:
    """Prove the comparators reject each way a closure can silently drift."""

    def closure(distributions):
        stdlib_files = [{"path": "stdlib/hashlib.py", "sha256": "e" * 64}]
        standard_library = {
            "implementation": "cpython",
            "version": "3.11.9",
            "fileRecords": len(stdlib_files),
            "contentSha256": standard_library_digest(stdlib_files),
            "files": stdlib_files,
        }
        runtime_files = [
            {"path": "basePrefix/lib/libpython3.11.dylib", "sha256": "c" * 64}
        ]
        interpreter_runtime = {
            "fileRecords": len(runtime_files),
            "contentSha256": interpreter_runtime_digest(runtime_files),
            "files": runtime_files,
        }
        return {
            "policy": {
                "transitionModules": [],
                "transitionPackages": ["ethereum"],
                "runtimePackages": [],
            },
            "distributions": distributions,
            "count": len(distributions),
            "fileRecords": file_records(distributions),
            "versionsSha256": versions_digest(distributions),
            "contentSha256": environment_content_digest(
                distributions, standard_library, interpreter_runtime
            ),
            "standardLibrary": standard_library,
            "interpreterRuntime": interpreter_runtime,
            "runtimeOnly": [],
        }

    def entry(name, version, sha, files=3):
        return {
            "name": name,
            "version": version,
            "modules": [name],
            "files": files,
            "contentSha256": sha,
        }

    base = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                    entry("pycryptodome", "3.23.0", "b" * 64)])
    if compare_versions(base, base) or compare_content(base, base):
        fail("semantic-closure self-check rejected an identical closure")

    mutants: list[tuple[str, dict[str, Any], bool]] = []

    bumped = closure([entry("ethereum_rlp", "0.1.5", "a" * 64),
                      entry("pycryptodome", "3.23.0", "b" * 64)])
    mutants.append(("in-range version bump", bumped, True))

    added = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                     entry("pycryptodome", "3.23.0", "b" * 64),
                     entry("ckzg", "2.1.5", "c" * 64)])
    mutants.append(("closure grew a new dependency", added, True))

    dropped = closure([entry("ethereum_rlp", "0.1.6", "a" * 64)])
    mutants.append(("closure lost a dependency", dropped, True))

    repacked = closure([entry("ethereum_rlp", "0.1.6", "d" * 64),
                        entry("pycryptodome", "3.23.0", "b" * 64)])
    mutants.append(("same version, different bytes", repacked, False))

    recounted = closure([entry("ethereum_rlp", "0.1.6", "a" * 64, files=4),
                         entry("pycryptodome", "3.23.0", "b" * 64)])
    mutants.append(("same digest, different file count", recounted, False))

    stdlib_repacked = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                               entry("pycryptodome", "3.23.0", "b" * 64)])
    stdlib_repacked["standardLibrary"]["files"][0]["sha256"] = "f" * 64
    mutants.append(("same interpreter, changed stdlib byte", stdlib_repacked, False))

    stdlib_grew = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                           entry("pycryptodome", "3.23.0", "b" * 64)])
    stdlib_grew["standardLibrary"]["files"].append(
        {"path": "stdlib/json/__init__.py", "sha256": "1" * 64}
    )
    stdlib_grew["standardLibrary"]["fileRecords"] = 2
    stdlib_grew["standardLibrary"]["contentSha256"] = standard_library_digest(
        stdlib_grew["standardLibrary"]["files"]
    )
    mutants.append(("closure loaded a new stdlib module", stdlib_grew, False))

    runtime_repacked = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                                entry("pycryptodome", "3.23.0", "b" * 64)])
    runtime_repacked["interpreterRuntime"]["files"][0]["sha256"] = "d" * 64
    mutants.append(("loaded libpython bytes changed", runtime_repacked, False))

    widened = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                       entry("pycryptodome", "3.23.0", "b" * 64)])
    widened["policy"]["transitionPackages"] = []
    widened["policy"]["transitionModules"] = ["ethereum"]
    mutants.append(("closure policy was rewritten", widened, True))

    for label, mutant, by_version in mutants:
        problems = (
            compare_versions(base, mutant) if by_version
            else compare_content(base, mutant)
        )
        if not problems:
            fail(f"semantic-closure self-check accepted {label}")

    # File-level control: an actual byte change in a libpython-shaped runtime
    # component is rejected; reverting only that byte restores equality.
    with tempfile.TemporaryDirectory(prefix="blanc-runtime-image-control-") as raw:
        root = Path(raw)
        (root / "bin").mkdir()
        (root / "lib" / "python3.11").mkdir(parents=True)
        executable = root / "bin" / "python3.11"
        executable.write_bytes(b"launcher")
        runtime_file = root / "lib" / "libpython3.11.dylib"
        original = b"runtime-library-control"
        runtime_file.write_bytes(original)
        stable = measure_interpreter_runtime(
            root,
            loaded_images=[runtime_file],
            python_executable=executable,
            standard_library_roots=[root / "lib" / "python3.11"],
        )
        runtime_file.write_bytes(original[:-1] + b"X")
        changed = measure_interpreter_runtime(
            root,
            loaded_images=[runtime_file],
            python_executable=executable,
            standard_library_roots=[root / "lib" / "python3.11"],
        )
        if not compare_content(
            {"distributions": [], "interpreterRuntime": stable},
            {"distributions": [], "interpreterRuntime": changed},
        ):
            fail("semantic-closure self-check accepted changed libpython bytes")
        runtime_file.write_bytes(original)
        restored = measure_interpreter_runtime(
            root,
            loaded_images=[runtime_file],
            python_executable=executable,
            standard_library_roots=[root / "lib" / "python3.11"],
        )
        if compare_content(
            {"distributions": [], "interpreterRuntime": stable},
            {"distributions": [], "interpreterRuntime": restored},
        ):
            fail("semantic-closure self-check rejected restored libpython bytes")

    # Hostile valid-pyc control.  The timestamp/size-valid cache executes the
    # evil value under the former -B-only command, while the production
    # isolation arguments force the unchanged good source.
    with tempfile.TemporaryDirectory(prefix="blanc-pyc-control-") as raw:
        root = Path(raw)
        source = root / "probe_mod.py"
        evil = "VALUE = 'evil'\n"
        good = "VALUE = 'good'\n"
        source.write_text(evil, encoding="utf-8")
        stamp = source.stat()
        cache_dir = root / "__pycache__"
        cache_dir.mkdir()
        cache = cache_dir / f"probe_mod.{sys.implementation.cache_tag}.pyc"
        # Name the adjacent cache explicitly: this self-control itself runs
        # under the production unreachable prefix and must still construct
        # the old attack shape without trying to write below /dev/null.
        py_compile.compile(str(source), cfile=str(cache), doraise=True)
        source.write_text(good, encoding="utf-8")
        os.utime(source, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        program = (
            "import sys; sys.path.insert(0, sys.argv[1]); "
            "import probe_mod; print(probe_mod.VALUE); "
            "print(sys.dont_write_bytecode); print(sys.pycache_prefix)"
        )
        vulnerable = subprocess.run(
            [sys.executable, "-I", "-s", "-B", "-c", program, str(root)],
            capture_output=True, text=True, check=True,
        ).stdout.splitlines()
        hardened = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", program, str(root)],
            capture_output=True, text=True, check=True,
        ).stdout.splitlines()
        if vulnerable[:1] != ["evil"]:
            fail("semantic-closure hostile pyc control did not exercise cached code")
        if hardened != ["good", "True", BYTECODE_POLICY["pycachePrefix"]]:
            fail("semantic-closure bytecode isolation accepted hostile cached code")

    return len(mutants) + 2
