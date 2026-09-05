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
record, so each generated platform row inventories and hashes the complete
executable file tree below the target interpreter's standard-library roots.
Nothing here is curated: the policy names the entry points, the target
interpreter names its standard-library roots, and the checker re-derives both
ownership populations on every run.  A future revision that reaches for a new
distribution grows the package closure and reddens the lock until it is
regenerated; any added, removed, or changed executable standard-library file
reddens the platform row directly.

Distributions loaded only through an oracle tool package's ``__init__`` chain
are marked separately for attribution, but remain in the version and content
closure.  Executed loader bytes cannot be exempted merely because the current
transition call graph is believed not to reach them.

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
import importlib.machinery
import json
import os
import py_compile
import re
import shutil
import subprocess
import sys
import tempfile
import types
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
    "isolated": True,
    "noUserSite": True,
    "pycachePrefix": "/dev/null",
}

# Executed module code must have an ownership channel represented by the lock.
# Source and extension loaders are admitted because their bytes are owned by a
# distribution RECORD, the pinned checkout, or the measured standard library.
# Built-in/frozen code belongs to the pinned interpreter.  Namespace packages
# execute no module body.  Sourceless bytecode and every other loader are
# rejected because neither has a sound byte owner in the closure today.
EXECUTED_LOADER_POLICY = {
    "builtin": "interpreterRuntime",
    "entrypoint": "trustedRepositorySource",
    "frozen": "interpreterRuntime",
    "namespace": "nonExecutable",
    "registryProxy": "pinnedInterpreterStandardLibraryOrGuardedImportSideEffect",
    "runtimeCreated": "onlyAfterGuardedImport",
    "source": "recordOrPinnedCheckoutOrStandardLibraryOrPlatformFileRecord",
    "extension": "recordOrStandardLibraryOrInterpreterRuntimeOrPlatformFileRecord",
    "sourcelessBytecode": "reject",
    "unsupported": "reject",
}

PYTHON_ISOLATION_ARGS = (
    "-I", "-s", "-B", "-X", "pycache_prefix=/dev/null",
)

# The standard library has no RECORD owner. Its configured roots come from the
# target interpreter itself, and generated rows bind every executable file the
# standard import machinery can reach below those roots. This policy is
# recorded in both pins so a future writer cannot silently return to partial or
# distribution-only measurement.
STANDARD_LIBRARY_POLICY = {
    "roots": ["stdlib", "platstdlib"],
    "selection": "completeImportableFileTree",
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


def unowned_site_packages_digest(files: Iterable[dict[str, Any]]) -> str:
    """Digest executed site-packages files that have no distribution RECORD."""

    return _digest(sorted([entry["path"], entry["sha256"]] for entry in files))


def environment_content_digest(
    distributions: Iterable[dict[str, Any]], standard_library: dict[str, Any],
    interpreter_runtime: dict[str, Any], unowned_site_packages: dict[str, Any],
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
            "unownedSitePackages": unowned_site_packages["contentSha256"],
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

    if sys.flags.isolated != 1:
        fail_with(f"{label} must run in isolated mode (-I)")
    if sys.flags.no_user_site != 1:
        fail_with(f"{label} must disable the user site (-s)")
    if sys.dont_write_bytecode is not True:
        fail_with(f"{label} must run with bytecode writes disabled")
    if sys.pycache_prefix != BYTECODE_POLICY["pycachePrefix"]:
        fail_with(
            f"{label} must run with sys.pycache_prefix="
            f"{BYTECODE_POLICY['pycachePrefix']!r}; found {sys.pycache_prefix!r}"
        )


def _canonical_distribution_name(name: str) -> str:
    return re.sub(r"[-_.]+", "_", name).lower()


def _is_interpreter_registry_proxy(name: str, value: Any) -> bool:
    """Recognize CPython's two stdlib-owned ``typing`` registry aliases."""

    if name not in {"typing.io", "typing.re"}:
        return False
    typing_module = sys.modules.get("typing")
    alias = name.removeprefix("typing.")
    if typing_module is None or value is not getattr(typing_module, alias, None):
        return False
    value_type = type(value)
    return (
        (value_type.__module__ == "typing"
         and value_type.__qualname__ == "_DeprecatedType")
        or (
            isinstance(value, type)
            and value.__module__ == "typing"
            and value.__qualname__ == alias
        )
    )


def _record_owners(
    site_packages: Iterable[str | Path],
    allowed_distributions: Iterable[str],
) -> tuple[list[Path], set[Path]]:
    """Return files owned by the lock's distributions, never every install."""

    import csv

    roots = sorted({Path(path).resolve() for path in site_packages})
    allowed = {
        _canonical_distribution_name(name) for name in allowed_distributions
    }
    found: set[str] = set()
    owners: set[Path] = set()
    for root in roots:
        if not root.is_dir():
            fail(f"site-packages root is absent: {root}")
        for info in sorted(root.glob("*.dist-info")):
            metadata = info / "METADATA"
            try:
                distribution_name = next(
                    line.removeprefix("Name:").strip()
                    for line in metadata.read_text(encoding="utf-8").splitlines()
                    if line.startswith("Name:")
                )
            except (OSError, StopIteration) as exc:
                fail(f"cannot identify distribution owner {info}: {exc}")
            canonical_name = _canonical_distribution_name(distribution_name)
            if canonical_name not in allowed:
                continue
            if canonical_name in found:
                fail(
                    f"pinned distribution {distribution_name!r} has more than one "
                    f"ownership record below {root}"
                )
            found.add(canonical_name)
            record = info / "RECORD"
            if not record.is_file():
                continue
            try:
                rows = csv.reader(record.read_text(encoding="utf-8").splitlines())
            except OSError as exc:
                fail(f"cannot read distribution ownership record {record}: {exc}")
            for row in rows:
                if not row or not row[0]:
                    continue
                candidate = (root / row[0]).resolve()
                if _is_under(candidate, root) and candidate.is_file():
                    owners.add(candidate)
    missing = sorted(allowed - found)
    if missing:
        fail(f"pinned distribution ownership records are absent: {missing}")
    return roots, owners


def _validate_executed_spec(
    name: str,
    spec: Any,
    *,
    site_roots: Iterable[Path],
    record_owners: set[Path],
    unowned_file_records: Mapping[str, str],
    source_roots: Iterable[Path],
    trusted_source_roots: Iterable[Path],
    standard_library_roots: Iterable[Path],
    standard_library_file_records: Mapping[Path, str],
    allow_unmeasured_standard_library: bool,
    fail_with: Any,
    label: str,
) -> None:
    """Accept only loader kinds whose executed bytes have a pinned owner."""

    if spec is None:
        fail_with(f"{label} module {name} has no attributable loader spec")
    loader = getattr(spec, "loader", None)
    origin = getattr(spec, "origin", None)
    machinery = importlib.machinery
    if loader is machinery.BuiltinImporter and origin == "built-in":
        return
    if loader is machinery.FrozenImporter and origin == "frozen":
        return
    namespace_loader = getattr(machinery, "NamespaceLoader", None)
    if (
        (loader is None or (namespace_loader is not None and type(loader) is namespace_loader))
        and getattr(spec, "submodule_search_locations", None) is not None
        and origin in (None, "namespace")
    ):
        return
    if not isinstance(origin, str) or not origin:
        fail_with(f"{label} module {name} has no attributable loader origin")
    resolved = Path(origin).resolve()
    if resolved.suffix in {".pyc", ".pyo"} or "__pycache__" in resolved.parts:
        fail_with(
            f"{label} module {name} executes excluded bytecode at {resolved}"
        )
    allowed_file_loader = type(loader) in {
        machinery.SourceFileLoader,
        machinery.ExtensionFileLoader,
    }
    if not allowed_file_loader:
        fail_with(
            f"{label} module {name} uses unsupported loader "
            f"{type(loader).__module__}.{type(loader).__qualname__}"
        )
    owning_root = next(
        (root for root in site_roots if _is_under(resolved, root)), None
    )
    if owning_root is not None:
        if resolved in record_owners:
            return
        logical = f"sitePackages/{resolved.relative_to(owning_root).as_posix()}"
        expected = unowned_file_records.get(logical)
        if expected is None:
            fail_with(
                f"{label} module {name} executes unrecorded site-packages file "
                f"{resolved}"
            )
        try:
            observed = hashlib.sha256(resolved.read_bytes()).hexdigest()
        except OSError as exc:
            fail_with(f"{label} cannot fingerprint {resolved}: {exc}")
        if observed != expected:
            fail_with(
                f"{label} module {name} site-packages bytes differ from the "
                f"platform record: {resolved}"
            )
        return
    if any(_is_under(resolved, root) for root in source_roots):
        return
    if any(_is_under(resolved, root) for root in trusted_source_roots):
        return
    standard_root = next(
        (root for root in standard_library_roots if _is_under(resolved, root)),
        None,
    )
    if standard_root is not None:
        expected = standard_library_file_records.get(resolved)
        if expected is None:
            if allow_unmeasured_standard_library:
                return
            fail_with(
                f"{label} module {name} executes unrecorded standard-library "
                f"file {resolved}"
            )
        try:
            observed = hashlib.sha256(resolved.read_bytes()).hexdigest()
        except OSError as exc:
            fail_with(f"{label} cannot fingerprint {resolved}: {exc}")
        if observed != expected:
            fail_with(
                f"{label} module {name} standard-library bytes differ from "
                f"the platform record: {resolved}"
            )
        return
    fail_with(
        f"{label} module {name} executes source outside every recorded owner: "
        f"{resolved}"
    )


class _ExecutedLoaderGuard:
    """Validate each future import spec before its loader can execute it."""

    _blanc_executed_loader_guard = True

    def __init__(
        self, roots: list[Path], owners: set[Path], unowned: Mapping[str, str],
        source_roots: list[Path], trusted_source_roots: list[Path],
        standard_library_roots: list[Path],
        standard_library_file_records: Mapping[Path, str],
        allow_unmeasured_standard_library: bool,
        installed_modules: frozenset[str], fail_with: Any, label: str
    ) -> None:
        self.roots = roots
        self.owners = owners
        self.unowned = unowned
        self.source_roots = source_roots
        self.trusted_source_roots = trusted_source_roots
        self.standard_library_roots = standard_library_roots
        self.standard_library_file_records = standard_library_file_records
        self.allow_unmeasured_standard_library = allow_unmeasured_standard_library
        # A later assertion may legitimately see target modules that this
        # guard admitted.  Retain the installation boundary so it can still
        # reject target modules that were already live before the guard.
        self.installed_modules = installed_modules
        self.fail_with = fail_with
        self.label = label

    def matches_contract(
        self, roots: list[Path], owners: set[Path], unowned: Mapping[str, str],
        source_roots: list[Path], trusted_source_roots: list[Path],
        standard_library_roots: list[Path],
        standard_library_file_records: Mapping[Path, str],
        allow_unmeasured_standard_library: bool,
    ) -> bool:
        """Say whether a repeated assertion names this exact live policy."""

        return (
            self.roots == roots
            and self.owners == owners
            and self.unowned == unowned
            and self.source_roots == source_roots
            and self.trusted_source_roots == trusted_source_roots
            and self.standard_library_roots == standard_library_roots
            and self.standard_library_file_records == standard_library_file_records
            and self.allow_unmeasured_standard_library
            == allow_unmeasured_standard_library
        )

    def find_spec(self, fullname: str, path: Any = None, target: Any = None) -> Any:
        for finder in list(sys.meta_path):
            if finder is self:
                continue
            method = getattr(finder, "find_spec", None)
            if method is None:
                continue
            spec = method(fullname, path, target)
            if spec is None:
                continue
            _validate_executed_spec(
                fullname,
                spec,
                site_roots=self.roots,
                record_owners=self.owners,
                unowned_file_records=self.unowned,
                source_roots=self.source_roots,
                trusted_source_roots=self.trusted_source_roots,
                standard_library_roots=self.standard_library_roots,
                standard_library_file_records=self.standard_library_file_records,
                allow_unmeasured_standard_library=(
                    self.allow_unmeasured_standard_library
                ),
                fail_with=self.fail_with,
                label=self.label,
            )
            return spec
        return None


def _loader_guards(fail_with: Any, *, label: str) -> list[_ExecutedLoaderGuard]:
    """Return the sole exact guard, rejecting marker lookalikes and stacking."""

    marked = [
        finder for finder in sys.meta_path
        if getattr(finder, "_blanc_executed_loader_guard", False)
    ]
    guards = [finder for finder in marked if isinstance(finder, _ExecutedLoaderGuard)]
    if len(marked) != len(guards):
        fail_with(f"{label} found a noncanonical executed-loader guard marker")
    if len(guards) > 1:
        fail_with(f"{label} found {len(guards)} stacked executed-loader guards")
    return guards


def assert_loader_guard_installed(fail_with: Any, *, label: str) -> None:
    """Require this exact module's live guard before importing oracle code."""

    guards = _loader_guards(fail_with, label=label)
    if len(guards) != 1:
        fail_with(
            f"{label} requires exactly one installed executed-loader guard; "
            f"found {len(guards)}"
        )


def assert_executed_loader_policy(
    fail_with: Any,
    *,
    label: str,
    site_packages: Iterable[str | Path],
    allowed_distributions: Iterable[str],
    source_roots: Iterable[str | Path],
    trusted_source_roots: Iterable[str | Path],
    standard_library: Any | None,
    unowned_site_packages: Any,
    install_guard: bool = True,
) -> str:
    """Audit loaded modules and guard every later import before execution."""

    try:
        roots, owners = _record_owners(site_packages, allowed_distributions)
        unowned_document = validate_unowned_site_packages(
            unowned_site_packages, fail,
            label=f"{label} unowned site-packages record",
        )
    except ClosureError as exc:
        fail_with(f"{label} cannot derive loader ownership: {exc}")
    unowned = {
        entry["path"]: entry["sha256"] for entry in unowned_document["files"]
    }
    import sysconfig

    configured_standard_roots = {
        label: Path(sysconfig.get_path(label)).resolve()
        for label in STANDARD_LIBRARY_POLICY["roots"]
    }
    standard_records: dict[Path, str] = {}
    if standard_library is not None:
        standard_document = validate_standard_library(
            standard_library, fail,
            label=f"{label} standard-library record",
        )
        for entry in standard_document["files"]:
            root_label, _, relative = entry["path"].partition("/")
            standard_records[
                (configured_standard_roots[root_label] / relative).resolve()
            ] = entry["sha256"]
    checked_source_roots = [Path(path).resolve() for path in source_roots]
    checked_trusted_roots = [
        Path(path).resolve() for path in trusted_source_roots
    ]
    # A repeated assertion in one interpreter may find this module's live
    # guard already installed with this exact contract. Every import after
    # that guard's boundary passed its `find_spec` validation, so an admitted
    # extension may since have registered runtime-created registry objects
    # that own no import spec of their own (`_cython_<version>` and
    # `cython_runtime` from a Cython-built extension, a CFFI `<name>.lib`
    # object). Those are attributed to the validated extension that created
    # them (`EXECUTED_LOADER_POLICY["runtimeCreated"]`); objects that predate
    # the guard, or that claim a file or loader, keep the pre-guard rule.
    live_guard = None
    for candidate in _loader_guards(fail_with, label=label):
        if candidate.matches_contract(
            roots, owners, unowned, checked_source_roots,
            checked_trusted_roots, list(configured_standard_roots.values()),
            standard_records, standard_library is None,
        ):
            live_guard = candidate
    for name, module in sorted(sys.modules.items()):
        if module is None:
            continue
        spec = getattr(module, "__spec__", None)
        # `__main__` is the trusted repository-owned `-c` entrypoint. CPython
        # CPython's `typing` module publishes two non-module registry proxies;
        # their implementation is covered by the pinned stdlib. Every other
        # pre-guard object must retain an attributable import spec.
        if spec is None:
            if name == "__main__":
                main_file = getattr(module, "__file__", None)
                if main_file is None and sys.argv[0] == "-c":
                    continue
                if isinstance(main_file, str):
                    resolved_main = Path(main_file).resolve()
                    if any(
                        _is_under(resolved_main, root)
                        for root in checked_source_roots + checked_trusted_roots
                    ):
                        continue
                fail_with(f"{label} __main__ entrypoint is outside trusted source")
            if _is_interpreter_registry_proxy(name, module):
                continue
            if (
                live_guard is not None
                and name not in live_guard.installed_modules
                and getattr(module, "__file__", None) is None
                and getattr(module, "__loader__", None) is None
            ):
                continue
            if not isinstance(module, types.ModuleType):
                fail_with(f"{label} registry object {name} has no attributable owner")
        _validate_executed_spec(
            name,
            spec,
            site_roots=roots,
            record_owners=owners,
            unowned_file_records=unowned,
            source_roots=checked_source_roots,
            trusted_source_roots=checked_trusted_roots,
            standard_library_roots=list(configured_standard_roots.values()),
            standard_library_file_records=standard_records,
            allow_unmeasured_standard_library=standard_library is None,
            fail_with=fail_with,
            label=label,
        )
    if install_guard:
        standard_roots = list(configured_standard_roots.values())
        guards = _loader_guards(fail_with, label=label)
        if guards:
            if not guards[0].matches_contract(
                roots, owners, unowned, checked_source_roots,
                checked_trusted_roots, standard_roots, standard_records,
                standard_library is None,
            ):
                fail_with(
                    f"{label} existing executed-loader guard has a different contract"
                )
        else:
            sys.meta_path.insert(
                0, _ExecutedLoaderGuard(
                    roots, owners, unowned, checked_source_roots,
                    checked_trusted_roots, standard_roots, standard_records,
                    standard_library is None, frozenset(sys.modules), fail_with, label,
                )
            )
    return (
        f"{len(owners)} RECORD-owned and {len(unowned)} platform-recorded "
        "site-packages files; executed loaders guarded"
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


def validate_unowned_site_packages(
    document: Any, fail_with: Any, *, label: str
) -> dict[str, Any]:
    """Validate platform rows for executed files with no RECORD owner."""

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
        prefix, separator, relative = (
            path.partition("/") if isinstance(path, str) else ("", "", "")
        )
        if prefix != "sitePackages" or not separator or not relative \
                or Path(relative).is_absolute() or ".." in Path(relative).parts:
            fail_with(f"{label} path is outside site-packages: {path!r}")
        if path in seen:
            fail_with(f"{label} names {path} twice")
        seen.add(path)
        if not is_sha256(entry["sha256"]):
            fail_with(f"{label} {path} digest is malformed")
    if type(document["fileRecords"]) is not int \
            or document["fileRecords"] != len(files):
        fail_with(f"{label} file-record count does not match its list")
    if document["contentSha256"] != unowned_site_packages_digest(files):
        fail_with(f"{label} content digest does not match its file rows")
    return document


def measure_standard_library(
    roots: Mapping[str, str | Path],
    *,
    executable_files: Iterable[str | Path],
    implementation: str,
    version: str,
    site_packages: Iterable[str | Path] = (),
) -> dict[str, Any]:
    """Inventory the selected target-interpreter standard-library bytes.

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
    for supplied in sorted(Path(path) for path in executable_files):
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


def complete_standard_library_files(
    roots: Mapping[str, str | Path]
) -> list[Path]:
    """Enumerate every file the standard import machinery can execute.

    Distribution locks own every executable file in each admitted RECORD, not
    only the files one probe happened to load. The stdlib needs the same rule:
    once the live guard admits a stdlib root, every source or extension file
    below it must have a byte record. Bytecode stays excluded by the mandatory
    ``-B``/unreachable-cache policy.
    """

    expected_roots = STANDARD_LIBRARY_POLICY["roots"]
    if set(roots) != set(expected_roots):
        fail("cannot enumerate standard library with unexpected roots")
    executable_suffixes = {".py", ".so", ".dylib", ".pyd"}
    found: set[Path] = set()
    for label in expected_roots:
        root = Path(roots[label]).resolve()
        if not root.is_dir():
            fail(f"target {label} standard-library root is absent: {root}")
        try:
            candidates = root.rglob("*")
            for candidate in candidates:
                relative = candidate.relative_to(root)
                if "site-packages" in relative.parts \
                        or "dist-packages" in relative.parts \
                        or "__pycache__" in relative.parts \
                        or candidate.suffix not in executable_suffixes:
                    continue
                if candidate.is_file() or candidate.is_symlink():
                    found.add(candidate)
        except OSError as exc:
            fail(f"cannot enumerate target {label} standard library: {exc}")
    if not found:
        fail("target standard-library executable-file inventory is empty")
    return sorted(found)


def validate_standard_library(
    document: Any, fail_with: Any, *, label: str
) -> dict[str, Any]:
    """Validate a content-addressed executable-stdlib inventory."""

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
        fail_with(f"{label} names no executable standard-library file")
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
import importlib.machinery
import json
import os
import pkgutil
import sys
import sysconfig
import types
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

# The live executor imports this guard before it accepts an oracle result.  Its
# own standard-library imports are therefore part of the executed closure and
# must be present in every generated native standard-library inventory.
guard_spec = importlib.util.spec_from_file_location(
    "_blanc_loader_guard_inventory", request["guardPath"]
)
if guard_spec is None or guard_spec.loader is None:
    raise RuntimeError("cannot load the executed-loader guard for inventory")
guard_module = importlib.util.module_from_spec(guard_spec)
sys.modules[guard_spec.name] = guard_module
guard_spec.loader.exec_module(guard_module)


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


def validate_executed_loaders():
    """Reject code whose loader or site-packages owner is outside the lock."""

    machinery = importlib.machinery
    namespace_loader = getattr(machinery, "NamespaceLoader", None)
    admitted_source_roots = [Path(path).resolve() for path in request["sourcePaths"]]
    admitted_standard_roots = [
        Path(sysconfig.get_path(label)).resolve()
        for label in ("stdlib", "platstdlib")
    ]
    admitted_guard = Path(request["guardPath"]).resolve()
    unowned = {}
    for module_name, module in sorted(sys.modules.items()):
        if module is None:
            continue
        spec = getattr(module, "__spec__", None)
        if spec is None:
            value_type = type(module)
            if module_name == "__main__":
                main_file = getattr(module, "__file__", None)
                if main_file is None and sys.argv[0] == "-c":
                    continue
                if isinstance(main_file, str):
                    resolved_main = Path(main_file).resolve()
                    if resolved_main == admitted_guard or any(
                        resolved_main.is_relative_to(root)
                        for root in admitted_source_roots
                    ):
                        continue
                raise RuntimeError(
                    "semantic-closure __main__ entrypoint is outside trusted source"
                )
            if module_name in {"typing.io", "typing.re"}:
                typing_module = sys.modules.get("typing")
                alias = module_name.removeprefix("typing.")
                if (
                    typing_module is not None
                    and module is getattr(typing_module, alias, None)
                    and (
                        (value_type.__module__ == "typing"
                         and value_type.__qualname__ == "_DeprecatedType")
                        or (
                            isinstance(module, type)
                            and module.__module__ == "typing"
                            and module.__qualname__ == alias
                        )
                    )
                ):
                    continue
            # Once the live guard is installed, an admitted extension may
            # register runtime-created module objects with no separate loader
            # (`_cython_*`, `cython_runtime`, CFFI namespaces).  Their bytes
            # were checked at the extension's import spec before its body ran.
            if any(
                getattr(finder, "_blanc_executed_loader_guard", False)
                for finder in sys.meta_path
            ):
                continue
            if not isinstance(module, types.ModuleType):
                raise RuntimeError(
                    f"semantic-closure registry object {module_name} has no "
                    "attributable owner"
                )
            raise RuntimeError(
                f"semantic-closure module {module_name} has no attributable loader spec"
            )
        loader = getattr(spec, "loader", None)
        origin = getattr(spec, "origin", None)
        if loader is machinery.BuiltinImporter and origin == "built-in":
            continue
        if loader is machinery.FrozenImporter and origin == "frozen":
            continue
        if (
            (loader is None or
             (namespace_loader is not None and type(loader) is namespace_loader))
            and getattr(spec, "submodule_search_locations", None) is not None
            and origin in (None, "namespace")
        ):
            continue
        if not isinstance(origin, str) or not origin:
            raise RuntimeError(
                f"semantic-closure module {module_name} has no attributable loader origin"
            )
        resolved = Path(origin).resolve()
        if resolved.suffix in {".pyc", ".pyo"} or "__pycache__" in resolved.parts:
            raise RuntimeError(
                f"semantic-closure module {module_name} executes excluded bytecode "
                f"at {resolved}"
            )
        if type(loader) not in {
            machinery.SourceFileLoader,
            machinery.ExtensionFileLoader,
        }:
            raise RuntimeError(
                f"semantic-closure module {module_name} uses unsupported loader "
                f"{type(loader).__module__}.{type(loader).__qualname__}"
            )
        try:
            relative = resolved.relative_to(site_packages)
        except ValueError:
            if resolved == admitted_guard \
                    or any(resolved.is_relative_to(root)
                           for root in admitted_source_roots) \
                    or any(resolved.is_relative_to(root)
                           for root in admitted_standard_roots):
                continue
            raise RuntimeError(
                f"semantic-closure module {module_name} executes source outside "
                f"the pinned checkout, standard library, guard, and site-packages: "
                f"{resolved}"
            )
        if os.path.realpath(resolved) not in owner_of:
            logical = f"sitePackages/{relative.as_posix()}"
            digest = hashlib.sha256(resolved.read_bytes()).hexdigest()
            previous = unowned.get(logical)
            if previous is not None and previous != digest:
                raise RuntimeError(
                    f"semantic-closure unowned file changed while loaded: {resolved}"
                )
            unowned[logical] = digest
    files = [
        {"path": path, "sha256": digest}
        for path, digest in sorted(unowned.items())
    ]
    encoded = json.dumps(
        sorted([entry["path"], entry["sha256"]] for entry in files),
        sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode()
    return {
        "fileRecords": len(files),
        "contentSha256": hashlib.sha256(encoded).hexdigest(),
        "files": files,
    }

# Audit interpreter-startup imports first, then put the live guard in front of
# every transition/runtime import.  At derivation time every installed RECORD
# is provisionally admitted so the import population can be discovered; only
# distributions actually hit enter the produced lock.  Unowned startup source
# is admitted solely by its exact measured byte record.  No newly imported
# unowned file, sourceless bytecode, custom loader, or external source can run
# even once and then erase its own spec before the final census.
startup_unowned_site_packages = validate_executed_loaders()
guard_module.assert_executed_loader_policy(
    lambda message: (_ for _ in ()).throw(RuntimeError(message)),
    label="semantic-closure probe",
    site_packages=[site_packages],
    allowed_distributions=list(distributions),
    source_roots=[Path(path).resolve() for path in request["sourcePaths"]],
    trusted_source_roots=[Path(request["guardPath"]).resolve().parent],
    standard_library=None,
    unowned_site_packages=startup_unowned_site_packages,
)

# --- tier one: the code that computes a transition ----------------------------

before = loaded_files()
skipped = import_all(request["transitionModules"], request["transitionPackages"])
transition_files = loaded_files() - before

# --- tier two: whatever a package __init__ chain drags in afterwards ----------

for name in request["runtimePackages"]:
    # A named runtime tool is executable closure, not optional discovery.  If
    # it cannot import, deriving a smaller lock would silently turn absence or
    # broken initialization into an approved environment.
    importlib.import_module(name)
runtime_files = loaded_files() - before - transition_files

# Validate after both tiers.  Runtime-tool imports execute just as surely as
# transition imports do; postponing this complete scan keeps a sourceless or
# otherwise unowned loader in that second tier from escaping the policy.
unowned_site_packages = validate_executed_loaders()


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
closure_hits = {name: set(modules) for name, modules in transition_hits.items()}
for name, modules in runtime_hits.items():
    closure_hits.setdefault(name, set()).update(modules)

closure = []
for name in sorted(closure_hits):
    measured, missing = content(name)
    if measured is None:
        raise RuntimeError(
            f"distribution {name} lists {missing} in its RECORD but the file is absent"
        )
    closure.append({
        "name": name,
        "version": distributions[name]["version"],
        "modules": sorted(closure_hits[name]),
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
    "interpreter": {
        "implementation": sys.implementation.name,
        "version": ".".join(str(part) for part in sys.version_info[:3]),
        "basePrefix": os.path.realpath(sys.base_prefix),
    },
    "bytecodePolicy": {
        "dontWriteBytecode": sys.dont_write_bytecode,
        "pycachePrefix": sys.pycache_prefix,
    },
    # Runtime-image inventory imports ctypes only after package attribution is
    # complete; the complete stdlib tree is inventoried by the parent process.
    "interpreterRuntimeImages": loaded_native_images(),
    "standardLibraryRoots": {
        "stdlib": sysconfig.get_path("stdlib"),
        "platstdlib": sysconfig.get_path("platstdlib"),
    },
    "sitePackages": str(site_packages),
    "unownedSitePackages": unowned_site_packages,
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
    request["guardPath"] = str(Path(__file__).resolve())
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
        executable_files=complete_standard_library_files(
            observed["standardLibraryRoots"]
        ),
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
    unowned_site_packages = validate_unowned_site_packages(
        observed["unownedSitePackages"], fail,
        label="observed unowned site-packages",
    )
    try:
        python_executable_sha256 = hashlib.sha256(python.read_bytes()).hexdigest()
    except OSError as exc:
        fail(f"cannot fingerprint target interpreter {python}: {exc}")
    return {
        "policy": checked,
        "interpreter": observed["interpreter"],
        "bytecodePolicy": observed["bytecodePolicy"],
        "executedLoaderPolicy": dict(EXECUTED_LOADER_POLICY),
        "pythonExecutableSha256": python_executable_sha256,
        "distributions": distributions,
        "count": len(distributions),
        "fileRecords": file_records(distributions),
        "versionsSha256": versions_digest(distributions),
        "contentSha256": environment_content_digest(
            distributions, standard_library, interpreter_runtime,
            unowned_site_packages,
        ),
        "standardLibrary": standard_library,
        "interpreterRuntime": interpreter_runtime,
        "unownedSitePackages": unowned_site_packages,
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
    recorded_unowned = recorded.get("unownedSitePackages")
    observed_unowned = observed.get("unownedSitePackages")
    if recorded_unowned is None and observed_unowned is not None:
        problems.append("the pinned platform row does not bind unowned site-packages files")
    elif recorded_unowned is not None and observed_unowned is None:
        problems.append("the observed environment did not measure unowned site-packages files")
    elif recorded_unowned is not None and observed_unowned is not None:
        old_files = {
            entry["path"]: entry["sha256"]
            for entry in recorded_unowned.get("files", [])
        }
        new_files = {
            entry["path"]: entry["sha256"]
            for entry in observed_unowned.get("files", [])
        }
        for path in sorted(set(new_files) - set(old_files)):
            problems.append(f"unowned site-packages file {path} is newly executed")
        for path in sorted(set(old_files) - set(new_files)):
            problems.append(f"unowned site-packages file {path} is no longer executed")
        for path in sorted(set(old_files) & set(new_files)):
            if old_files[path] != new_files[path]:
                problems.append(
                    f"unowned site-packages file {path} does not match pinned bytes"
                )
        if old_files == new_files and (
            recorded_unowned.get("fileRecords") != observed_unowned.get("fileRecords")
            or recorded_unowned.get("contentSha256")
                != observed_unowned.get("contentSha256")
        ):
            problems.append("unowned site-packages digest differs with no named file cause")
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


def assert_prague_environment(
    fail_with: Any, *, checkout_root: str | Path
) -> str:
    """The one line every Prague differential runs before it trusts an oracle.

    A Git commit pins the specification's source; this pins what that source
    imports.  Both have to hold before a comparison against EELS means anything.
    """

    assert_bytecode_policy(fail_with, label="pinned EELS Prague environment")
    pin = load_pin()
    if pin.get("semanticClosure", {}).get("executedLoaderPolicy") != \
            dict(EXECUTED_LOADER_POLICY):
        fail_with("pinned EELS Prague executed-loader policy differs")
    versions = assert_pinned_versions(
        pin, fail_with, label="pinned EELS Prague environment"
    )
    import sys
    import sysconfig

    checkout = Path(checkout_root).resolve()
    expected_commit = pin.get("checkout", {}).get("commit")
    try:
        actual_commit = subprocess.run(
            ["git", "-C", str(checkout), "rev-parse", "HEAD"],
            text=True, capture_output=True, check=True,
        ).stdout.strip()
        dirty = subprocess.run(
            ["git", "-C", str(checkout), "status", "--porcelain"],
            text=True, capture_output=True, check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        fail_with(f"pinned EELS Prague cannot inspect its checkout: {exc}")
    if actual_commit != expected_commit or dirty:
        fail_with(
            "pinned EELS Prague checkout differs: "
            f"expected {expected_commit}, found {actual_commit}, dirty={bool(dirty)}"
        )
    source_relative = pin.get("checkout", {}).get("sourceRoot")
    if not isinstance(source_relative, str) or not source_relative \
            or Path(source_relative).is_absolute() \
            or ".." in Path(source_relative).parts:
        fail_with("pinned EELS Prague source root is invalid")
    source_root = (checkout / source_relative).resolve()
    if not source_root.is_dir() or not _is_under(source_root, checkout):
        fail_with("pinned EELS Prague source root is absent or outside its checkout")
    # `-I` deliberately ignores PYTHONPATH. Re-introduce only the source root
    # derived from the clean pinned checkout, and put it before every installed
    # package so the target name cannot resolve to a RECORD-owned impostor.
    sys.path[:] = [
        str(source_root),
        *(entry for entry in sys.path if Path(entry or ".").resolve() != source_root),
    ]
    guards = _loader_guards(
        fail_with, label="pinned EELS Prague environment"
    )
    transition_packages = pin["semanticClosure"]["policy"]["transitionPackages"]
    for package_name in transition_packages:
        already_loaded = sorted(
            name for name in sys.modules
            if name == package_name or name.startswith(package_name + ".")
        )
        # A repeated assertion may run after the exact guard admitted target
        # modules.  It must still reject any target module that was already
        # present at the guard's installation boundary.
        pre_guard = (
            not guards
            or any(name in guards[0].installed_modules for name in already_loaded)
        )
        if already_loaded and pre_guard:
            fail_with(
                "pinned EELS Prague target code was imported before the loader "
                f"guard: {', '.join(already_loaded[:5])}"
            )
        spec = importlib.machinery.PathFinder.find_spec(package_name)
        origin = getattr(spec, "origin", None) if spec is not None else None
        if not isinstance(origin, str) or not origin:
            fail_with(
                f"pinned EELS Prague cannot resolve source package {package_name}"
            )
        resolved_origin = Path(origin).resolve()
        if not _is_under(resolved_origin, source_root):
            fail_with(
                f"pinned EELS Prague source package {package_name} resolves outside "
                f"the pinned checkout: {resolved_origin}"
            )

    native = platform_key(sys.platform, os.uname().machine)
    row = pin.get("platforms", {}).get(native)
    site_roots = sorted({
        Path(entry).resolve()
        for entry in sys.path
        if entry and Path(entry).name in {"site-packages", "dist-packages"}
        and Path(entry).is_dir()
    })
    if not site_roots:
        fail_with("pinned EELS Prague environment has no active site-packages root")
    empty_unowned = {
        "fileRecords": 0,
        "contentSha256": unowned_site_packages_digest([]),
        "files": [],
    }
    loaders = assert_executed_loader_policy(
        fail_with,
        label="pinned EELS Prague environment",
        site_packages=site_roots,
        allowed_distributions=[
            entry["name"] for entry in pin["semanticClosure"]["distributions"]
        ],
        source_roots=[source_root],
        trusted_source_roots=[Path(__file__).resolve().parent],
        standard_library=(
            row.get("standardLibrary") if isinstance(row, dict) else None
        ),
        unowned_site_packages=(
            row.get("unownedSitePackages", empty_unowned)
            if isinstance(row, dict) else empty_unowned
        ),
    )
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
        executable_files = []
        for entry in recorded.get("files", []):
            label, separator, relative = entry.get("path", "").partition("/")
            if not separator or label not in roots or not relative:
                fail_with("pinned EELS Prague standard-library path is invalid")
            executable_files.append(Path(roots[label]) / relative)
        observed = measure_standard_library(
            roots,
            executable_files=executable_files,
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
            "unownedSitePackages": row.get("unownedSitePackages"),
        },
        {
            "distributions": [],
            "standardLibrary": observed,
            "interpreterRuntime": runtime,
            "unownedSitePackages": row.get("unownedSitePackages"),
        },
    )
    if problems:
        fail_with(
            "pinned EELS Prague native runtime does not match its pin: "
            + "; ".join(problems)
        )
    return (
        f"{versions}; {loaders}; {observed['fileRecords']} pinned standard-library files "
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
        unowned_files = [
            {"path": "sitePackages/_virtualenv.py", "sha256": "9" * 64}
        ]
        unowned_site_packages = {
            "fileRecords": len(unowned_files),
            "contentSha256": unowned_site_packages_digest(unowned_files),
            "files": unowned_files,
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
                distributions, standard_library, interpreter_runtime,
                unowned_site_packages,
            ),
            "standardLibrary": standard_library,
            "interpreterRuntime": interpreter_runtime,
            "unownedSitePackages": unowned_site_packages,
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
    mutants.append(("closure gained a new executable stdlib file", stdlib_grew, False))

    runtime_repacked = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                                entry("pycryptodome", "3.23.0", "b" * 64)])
    runtime_repacked["interpreterRuntime"]["files"][0]["sha256"] = "d" * 64
    mutants.append(("loaded libpython bytes changed", runtime_repacked, False))

    unowned_repacked = closure([entry("ethereum_rlp", "0.1.6", "a" * 64),
                                entry("pycryptodome", "3.23.0", "b" * 64)])
    unowned_repacked["unownedSitePackages"]["files"][0]["sha256"] = "2" * 64
    mutants.append(("unowned site-packages bytes changed", unowned_repacked, False))

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

    # Sourceless-package control.  A legacy package-level __init__.pyc shadows
    # a RECORD-owned module even under the unreachable cache prefix.  The live
    # loader guard must reject the spec before its body runs; removing only the
    # unowned bytecode package restores the RECORD-owned source import.
    with tempfile.TemporaryDirectory(prefix="blanc-sourceless-loader-") as raw:
        root = Path(raw)
        semdep = root / "semdep"
        semdep.mkdir()
        (semdep / "__init__.py").write_text("", encoding="utf-8")
        (semdep / "codec.py").write_text("VALUE = 'good'\n", encoding="utf-8")
        attack = semdep / "codec"
        attack.mkdir()
        marker = root / "executed-marker"
        evil_source = attack / "__init__.py"
        evil_source.write_text(
            f"from pathlib import Path\nPath({str(marker)!r}).write_text('ran')\n"
            "VALUE = 'evil'\n",
            encoding="utf-8",
        )
        py_compile.compile(
            str(evil_source), cfile=str(attack / "__init__.pyc"), doraise=True
        )
        evil_source.unlink()
        info = root / "semdep-1.0.dist-info"
        info.mkdir()
        (info / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: semdep\nVersion: 1.0\n",
            encoding="utf-8",
        )
        (info / "RECORD").write_text(
            "semdep/__init__.py,,\nsemdep/codec.py,,\n"
            "semdep-1.0.dist-info/RECORD,,\n",
            encoding="utf-8",
        )
        vulnerable_program = (
            "import sys; sys.path.insert(0, sys.argv[1]); "
            "import semdep.codec; print(semdep.codec.VALUE)"
        )
        vulnerable = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", vulnerable_program,
             str(root)],
            capture_output=True, text=True, check=True,
        )
        if vulnerable.stdout.strip() != "evil" or marker.read_text() != "ran":
            fail("sourceless-loader control did not execute the shadow package")
        marker.unlink()
        guard_path = Path(__file__).resolve()
        audit_program = r'''
import importlib.util
import pathlib
import sys

guard_path = pathlib.Path(sys.argv[1])
root = pathlib.Path(sys.argv[2])
spec = importlib.util.spec_from_file_location("loader_guard", guard_path)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
sys.path.insert(0, str(root))
import semdep
import semdep.codec
module.assert_executed_loader_policy(
    lambda message: (_ for _ in ()).throw(RuntimeError(message)),
    label="second-tier loader audit control",
    site_packages=[root],
    allowed_distributions=["semdep"],
    source_roots=[],
    trusted_source_roots=[guard_path.parent],
    standard_library=None,
    unowned_site_packages={
        "fileRecords": 0,
        "contentSha256": module.unowned_site_packages_digest([]),
        "files": [],
    },
)
'''
        audited = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", audit_program,
             str(guard_path), str(root)],
            capture_output=True, text=True,
        )
        if audited.returncode == 0 \
                or "executes excluded bytecode" not in audited.stderr \
                or marker.read_text() != "ran":
            fail("complete second-tier audit accepted the sourceless runtime import")
        marker.unlink()
        guarded_program = r'''
import importlib.util
import pathlib
import sys

guard_path = pathlib.Path(sys.argv[1])
root = pathlib.Path(sys.argv[2])
spec = importlib.util.spec_from_file_location("loader_guard", guard_path)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
module.assert_executed_loader_policy(
    lambda message: (_ for _ in ()).throw(RuntimeError(message)),
    label="sourceless-loader control",
    site_packages=[root],
    allowed_distributions=["semdep"],
    source_roots=[],
    trusted_source_roots=[guard_path.parent],
    standard_library=None,
    unowned_site_packages={
        "fileRecords": 0,
        "contentSha256": module.unowned_site_packages_digest([]),
        "files": [],
    },
)
sys.path.insert(0, str(root))
import semdep.codec
print(semdep.codec.VALUE)
'''
        rejected = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", guarded_program,
             str(guard_path), str(root)],
            capture_output=True, text=True,
        )
        if rejected.returncode == 0 \
                or "executes excluded bytecode" not in rejected.stderr \
                or marker.exists():
            fail(
                "executed-loader guard accepted the sourceless shadow package: "
                f"exit={rejected.returncode}; stderr={rejected.stderr.strip()}"
            )
        shutil.rmtree(attack)
        restored = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", guarded_program,
             str(guard_path), str(root)],
            capture_output=True, text=True, check=True,
        )
        if restored.stdout.strip() != "good":
            fail("executed-loader guard rejected the restored owned source module")

    # Runtime policy entries are mandatory executable inputs.  A failed
    # second-tier import must abort derivation instead of shrinking the lock
    # and recording the error as an ignored note.
    with tempfile.TemporaryDirectory(prefix="blanc-runtime-import-control-") as raw:
        root = Path(raw)
        (root / "semdep.py").write_text("VALUE = 'good'\n", encoding="utf-8")
        info = root / "semdep-1.0.dist-info"
        info.mkdir()
        (info / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: semdep\nVersion: 1.0\n",
            encoding="utf-8",
        )
        (info / "RECORD").write_text("semdep.py,,\n", encoding="utf-8")
        missing_runtime = "blanc_runtime_package_that_does_not_exist"
        request = {
            "transitionModules": ["semdep"],
            "transitionPackages": [],
            "runtimePackages": [missing_runtime],
            "sitePackages": str(root),
            "installerMetadata": list(INSTALLER_METADATA),
            "sourcePaths": [str(root)],
            "guardPath": str(Path(__file__).resolve()),
            "bytecodePolicy": dict(BYTECODE_POLICY),
        }
        interpreter = Path(
            getattr(sys, "_base_executable", None) or sys.executable
        )
        refused = subprocess.run(
            [str(interpreter), *PYTHON_ISOLATION_ARGS, "-c", _PROBE,
             json.dumps(request)],
            cwd=str(root), capture_output=True, text=True,
        )
        if refused.returncode == 0 or missing_runtime not in refused.stderr:
            fail("semantic-closure probe ignored an unavailable runtime package")

    # Domain controls for the other rejection arms: a RECORD from a
    # distribution outside the semantic closure, source outside every admitted
    # root, and a custom loader all fail at the loader-policy boundary.
    with tempfile.TemporaryDirectory(prefix="blanc-loader-domain-control-") as raw:
        root = Path(raw)
        site_root = root / "site-packages"
        site_root.mkdir()
        allowed_info = site_root / "allowed-1.0.dist-info"
        allowed_info.mkdir()
        (allowed_info / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: allowed\nVersion: 1.0\n",
            encoding="utf-8",
        )
        allowed_source = site_root / "allowed.py"
        allowed_source.write_text("VALUE = 1\n", encoding="utf-8")
        (allowed_info / "RECORD").write_text("allowed.py,,\n", encoding="utf-8")
        unpinned_info = site_root / "unpinned-1.0.dist-info"
        unpinned_info.mkdir()
        (unpinned_info / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: unpinned\nVersion: 1.0\n",
            encoding="utf-8",
        )
        unpinned_source = site_root / "unpinned.py"
        unpinned_source.write_text("VALUE = 2\n", encoding="utf-8")
        (unpinned_info / "RECORD").write_text("unpinned.py,,\n", encoding="utf-8")
        roots, owners = _record_owners([site_root], ["allowed"])
        import importlib.util
        import sysconfig

        standard_roots = [
            Path(sysconfig.get_path(label)).resolve()
            for label in STANDARD_LIBRARY_POLICY["roots"]
        ]

        def expect_rejection(name: str, spec: Any, expected: str) -> None:
            try:
                _validate_executed_spec(
                    name, spec, site_roots=roots, record_owners=owners,
                    unowned_file_records={}, source_roots=[],
                    trusted_source_roots=[],
                    standard_library_roots=standard_roots,
                    standard_library_file_records={},
                    allow_unmeasured_standard_library=True,
                    fail_with=fail, label="loader-domain control",
                )
            except ClosureError as exc:
                if expected not in str(exc):
                    fail(f"loader-domain control rejected {name} for wrong reason: {exc}")
                return
            fail(f"loader-domain control accepted {name}")

        expect_rejection(
            "unpinned",
            importlib.util.spec_from_file_location("unpinned", unpinned_source),
            "unrecorded site-packages file",
        )
        outside_source = root / "outside.py"
        outside_source.write_text("VALUE = 3\n", encoding="utf-8")
        expect_rejection(
            "outside",
            importlib.util.spec_from_file_location("outside", outside_source),
            "outside every recorded owner",
        )

        class UnsupportedLoader:
            pass

        expect_rejection(
            "custom",
            importlib.machinery.ModuleSpec(
                "custom", UnsupportedLoader(), origin=str(outside_source)
            ),
            "uses unsupported loader",
        )
        expect_rejection(
            "missing-spec",
            None,
            "has no attributable loader spec",
        )
        duplicate_info = site_root / "spoof-9.0.dist-info"
        duplicate_info.mkdir()
        (duplicate_info / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: allowed\nVersion: 9.0\n",
            encoding="utf-8",
        )
        (duplicate_info / "RECORD").write_text("unpinned.py,,\n", encoding="utf-8")
        try:
            _record_owners([site_root], ["allowed"])
        except ClosureError as exc:
            if "more than one ownership record" not in str(exc):
                fail(f"duplicate-owner control refused for wrong reason: {exc}")
        else:
            fail("loader ownership accepted a duplicate allowed distribution name")

    # Runtime-created registry objects.  An admitted extension may register
    # module objects that own no import spec (`_cython_<version>`,
    # `cython_runtime`, a CFFI `<name>.lib`).  A repeated assertion behind the
    # live guard attributes them to the validated import that created them;
    # the same objects registered before any guard, or a spec-less object
    # that claims a file, are still refused at the loader-policy boundary.
    with tempfile.TemporaryDirectory(prefix="blanc-runtime-registry-") as raw:
        root = Path(raw)
        package = root / "regdep"
        package.mkdir()
        (package / "__init__.py").write_text(
            "import sys\n"
            "import types\n"
            "sys.modules['_cython_0_0_0'] = types.ModuleType('_cython_0_0_0')\n"
            "class _Lib:\n"
            "    pass\n"
            "sys.modules['regdep.lib'] = _Lib()\n"
            "VALUE = 'registered'\n",
            encoding="utf-8",
        )
        info = root / "regdep-1.0.dist-info"
        info.mkdir()
        (info / "METADATA").write_text(
            "Metadata-Version: 2.1\nName: regdep\nVersion: 1.0\n",
            encoding="utf-8",
        )
        (info / "RECORD").write_text(
            "regdep/__init__.py,,\nregdep-1.0.dist-info/RECORD,,\n",
            encoding="utf-8",
        )
        guard_path = Path(__file__).resolve()
        prologue = r'''
import importlib.util
import pathlib
import sys
import types

guard_path = pathlib.Path(sys.argv[1])
root = pathlib.Path(sys.argv[2])
spec = importlib.util.spec_from_file_location("loader_guard", guard_path)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)


def assert_policy(label):
    module.assert_executed_loader_policy(
        lambda message: (_ for _ in ()).throw(RuntimeError(message)),
        label=label,
        site_packages=[root],
        allowed_distributions=["regdep"],
        source_roots=[],
        trusted_source_roots=[guard_path.parent],
        standard_library=None,
        unowned_site_packages={
            "fileRecords": 0,
            "contentSha256": module.unowned_site_packages_digest([]),
            "files": [],
        },
    )
'''
        admitted_program = prologue + r'''
assert_policy("runtime-registry control: guard")
sys.path.insert(0, str(root))
import regdep
assert_policy("runtime-registry control: repeated")
print(regdep.VALUE)
'''
        admitted = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", admitted_program,
             str(guard_path), str(root)],
            capture_output=True, text=True,
        )
        if admitted.returncode != 0 or admitted.stdout.strip() != "registered":
            fail(
                "repeated loader audit refused guarded runtime-created registry "
                f"objects: exit={admitted.returncode}; "
                f"stderr={admitted.stderr.strip()}"
            )
        pre_guard_program = prologue + r'''
sys.path.insert(0, str(root))
import regdep
assert_policy("runtime-registry control: pre-guard")
print(regdep.VALUE)
'''
        pre_guard = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", pre_guard_program,
             str(guard_path), str(root)],
            capture_output=True, text=True,
        )
        if pre_guard.returncode == 0 \
                or "_cython_0_0_0 has no attributable loader spec" \
                not in pre_guard.stderr:
            fail(
                "loader audit accepted a runtime-created registry object that "
                f"predates the guard: exit={pre_guard.returncode}; "
                f"stderr={pre_guard.stderr.strip()}"
            )
        file_claim_program = prologue + r'''
assert_policy("runtime-registry control: guard")
ghost = types.ModuleType("ghost_mod")
ghost.__file__ = str(root / "ghost_mod.py")
sys.modules["ghost_mod"] = ghost
assert_policy("runtime-registry control: file claim")
print("accepted")
'''
        file_claim = subprocess.run(
            [sys.executable, *PYTHON_ISOLATION_ARGS, "-c", file_claim_program,
             str(guard_path), str(root)],
            capture_output=True, text=True,
        )
        if file_claim.returncode == 0 \
                or "ghost_mod has no attributable loader spec" \
                not in file_claim.stderr:
            fail(
                "loader audit accepted a spec-less post-guard module that "
                f"claims a file: exit={file_claim.returncode}; "
                f"stderr={file_claim.stderr.strip()}"
            )

    return len(mutants) + 14
