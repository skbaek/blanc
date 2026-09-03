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

This module answers it by *derivation*.  The semantic closure is the set of
installed distributions that provide a module imported when the pinned
transition code is imported — the specification package and, where the lane
drives it through a tool, that tool's entry module.  Nothing here is curated:
the policy names the entry points, the probe reports what Python actually
loaded, and the checker re-derives the closure on every run.  A future revision
that reaches for a new library grows the closure and reddens the lock until it
is regenerated, so the narrowness cannot rot silently.

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
import subprocess
from pathlib import Path
from typing import Any, Iterable, NoReturn


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

# Byte-compiled output is a cache of source already inside the digest.
CONTENT_EXCLUDES = ("**/__pycache__/**", "**/*.pyc", "**/*.pyo")


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def _digest(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


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
from pathlib import Path

request = json.loads(sys.argv[1])
site_packages = Path(request["sitePackages"]).resolve()
installer_metadata = set(request["installerMetadata"])

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
    },
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
    try:
        result = subprocess.run(
            [str(python), "-I", "-s", "-B", "-c", _PROBE, json.dumps(request)],
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
    return {
        "policy": checked,
        "interpreter": observed["interpreter"],
        "distributions": distributions,
        "count": len(distributions),
        "fileRecords": file_records(distributions),
        "versionsSha256": versions_digest(distributions),
        "contentSha256": content_digest(distributions),
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

    return assert_pinned_versions(
        load_pin(), fail_with, label="pinned EELS Prague environment"
    )


def render_constraints(document: dict[str, Any], *, header: Iterable[str] = ()) -> str:
    """Render the closure as a pip constraints file a provisioner can consume."""

    lines = [f"# {line}" for line in header]
    lines.extend(versions_of(document))
    return "\n".join(lines) + "\n"


def report(document: dict[str, Any], *, label: str) -> str:
    lines = [
        f"{label}: {document['count']} distributions, "
        f"{document['fileRecords']} files, versions {document['versionsSha256'][:12]}"
    ]
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
            "contentSha256": content_digest(distributions),
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
    return len(mutants)
