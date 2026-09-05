#!/usr/bin/env python3
"""Generate the current-mainnet runtime lock from the target's semantic closure.

The lock has two halves and they are refreshed on different schedules.

The *semantic closure* — which distributions the pinned transition code imports,
and at which versions — is platform-independent, because a wheel's version is.
It is rewritten whenever this generator runs, and it binds on every platform.

The *platform rows* record the exact installed bytes behind those versions,
the complete executable standard-library tree, and the native images actually mapped from
the interpreter's base prefix.  Every accepted process also uses an unreachable
bytecode-cache prefix.  Only the executing platform's row can be measured.  The
other platform's row is carried forward when the pinned semantic closure did
not move, and reset to
`generated: false` when they did: a content measurement of a closure that no
longer exists is not evidence, and carrying it would be a lie the file tells on
every future read.

There is no legacy-manifest import.  It existed to migrate evidence produced
before the lock was split from the portable Beacon manifest, and it validated
the retired whole-site-packages shape, which this lock no longer has.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any, NoReturn

import current_mainnet as lane
import eels_semantic_closure as closure


def fail(message: str) -> NoReturn:
    raise lane.CurrentMainnetError(message)


def read_json(path: Path, label: str) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read {label} {path}: {exc}")


def canonical(document: Any) -> str:
    return json.dumps(document, indent=2, sort_keys=True) + "\n"


def existing_document(path: Path, profile: dict[str, Any]) -> dict[str, Any] | None:
    """The committed lock, when it is one this generator can still read.

    A document in a retired shape carries no row this generator may carry
    forward — its platform rows measured something that is no longer pinned —
    so it is treated as absent rather than repaired in place.
    """

    if not path.exists():
        return None
    try:
        return lane._validate_runtime_lock_document(
            profile, read_json(path, "current-mainnet runtime lock")
        )
    except lane.CurrentMainnetError:
        return None


def generate(profile: dict[str, Any], root: str | None) -> tuple[dict[str, Any], dict[str, Any], list[str]]:
    lane.verify_target(root, profile)
    paths = lane.target_paths(root, profile)
    evidence = lane._python_preflight(paths, profile, verify_runtime=False)
    key = evidence["platformKey"]

    observed = lane._derive_closure(paths)
    section = lane._closure_document(observed)

    output_path = lane._runtime_lock_path(profile)
    previous = existing_document(output_path, profile)

    notes: list[str] = []
    platforms: dict[str, Any] = {}
    for other in sorted(profile["target"]["pythonIdentity"]["platforms"]):
        if other == key:
            continue
        carried = (
            previous["platforms"].get(other) if previous is not None else None
        )
        moved = (
            previous is None
            or previous["semanticClosure"]["versionsSha256"] != section["versionsSha256"]
        )
        if carried is not None and carried.get("generated") is True and not moved:
            platforms[other] = copy.deepcopy(carried)
        else:
            if carried is not None and carried.get("generated") is True and moved:
                notes.append(
                    f"reset the {other} row: the pinned closure moved, so its "
                    "recorded bytes no longer describe it"
                )
            platforms[other] = lane._ungenerated_entry()
    platforms[key] = lane._runtime_entry(paths, observed)

    document = {
        "schema": 5,
        "target": lane._runtime_target_document(paths),
        "semanticClosure": section,
        "platforms": platforms,
    }
    return lane._validate_runtime_lock_document(profile, document), observed, notes


def self_check(profile: dict[str, Any]) -> int:
    """Prove the validator rejects every way this lock can be quietly weakened."""

    names = ("ethereum_rlp", "pycryptodome")
    distributions = [
        {"name": "ethereum_rlp", "version": "0.1.6", "modules": ["ethereum_rlp"]},
        {"name": "pycryptodome", "version": "3.23.0", "modules": ["Crypto"]},
    ]
    measured = [
        {"name": "ethereum_rlp", "files": 11, "contentSha256": "a" * 64},
        {"name": "pycryptodome", "files": 22, "contentSha256": "b" * 64},
    ]
    standard_library_files = [
        {"path": "stdlib/hashlib.py", "sha256": "4" * 64},
        {"path": "stdlib/json/__init__.py", "sha256": "5" * 64},
    ]
    standard_library = {
        "implementation": lane._EXPECTED["pythonImplementation"].lower(),
        "version": lane._EXPECTED["pythonVersion"],
        "fileRecords": len(standard_library_files),
        "contentSha256": closure.standard_library_digest(standard_library_files),
        "files": standard_library_files,
    }
    runtime_files = [
        {"path": "basePrefix/lib/libpython3.11.dylib", "sha256": "6" * 64}
    ]
    interpreter_runtime = {
        "fileRecords": len(runtime_files),
        "contentSha256": closure.interpreter_runtime_digest(runtime_files),
        "files": runtime_files,
    }
    unowned_site_packages = {
        "fileRecords": 1,
        "contentSha256": closure.unowned_site_packages_digest([
            {"path": "sitePackages/_virtualenv.py", "sha256": "8" * 64}
        ]),
        "files": [
            {"path": "sitePackages/_virtualenv.py", "sha256": "8" * 64}
        ],
    }
    platform_keys = sorted(profile["target"]["pythonIdentity"]["platforms"])
    native = platform_keys[0]
    document = {
        "schema": 5,
        "target": {
            "checkoutCommit": lane._EXPECTED["checkoutCommit"],
            "pythonImplementation": lane._EXPECTED["pythonImplementation"],
            "pythonVersion": lane._EXPECTED["pythonVersion"],
            "entrypointBodySha256": "2" * 64,
            "provisioning": dict(lane._PROVISIONING),
        },
        "semanticClosure": {
            "policy": copy.deepcopy(lane._CLOSURE_POLICY),
            "contentExcludes": list(closure.CONTENT_EXCLUDES),
            "bytecodePolicy": dict(closure.BYTECODE_POLICY),
            "executedLoaderPolicy": dict(closure.EXECUTED_LOADER_POLICY),
            "installerMetadataExcludes": list(closure.INSTALLER_METADATA),
            "standardLibraryPolicy": dict(closure.STANDARD_LIBRARY_POLICY),
            "interpreterRuntimePolicy": dict(closure.INTERPRETER_RUNTIME_POLICY),
            "distributions": copy.deepcopy(distributions),
            "count": len(distributions),
            "versionsSha256": closure.versions_digest(distributions),
        },
        "platforms": {
            key: (
                {
                    "generated": True,
                    "pythonExecutableSha256": "3" * 64,
                    "fileRecords": 33,
                    "contentSha256": closure.environment_content_digest(
                        measured, standard_library, interpreter_runtime,
                        unowned_site_packages,
                    ),
                    "standardLibrary": copy.deepcopy(standard_library),
                    "interpreterRuntime": copy.deepcopy(interpreter_runtime),
                    "unownedSitePackages": copy.deepcopy(unowned_site_packages),
                    "distributions": copy.deepcopy(measured),
                }
                if key == native
                else {"generated": False}
            )
            for key in platform_keys
        },
    }
    lane._validate_runtime_lock_document(profile, document)

    mutants: list[tuple[str, dict[str, Any]]] = []

    missing = copy.deepcopy(document)
    del missing["platforms"][native]
    mutants.append(("missing-platform", missing))

    # The closure is the whole pin now, so an emptied or shrunken policy is the
    # sharpest available weakening: it would derive a smaller closure next run.
    unpolicied = copy.deepcopy(document)
    unpolicied["semanticClosure"]["policy"]["transitionPackages"] = []
    mutants.append(("emptied-closure-policy", unpolicied))

    widened = copy.deepcopy(document)
    widened["semanticClosure"]["installerMetadataExcludes"] = []
    mutants.append(("widened-installer-metadata", widened))

    unbounded_stdlib = copy.deepcopy(document)
    del unbounded_stdlib["semanticClosure"]["standardLibraryPolicy"]
    mutants.append(("standard-library-policy-dropped", unbounded_stdlib))

    bytecode_readable = copy.deepcopy(document)
    bytecode_readable["semanticClosure"]["bytecodePolicy"]["pycachePrefix"] = None
    mutants.append(("bytecode-cache-made-readable", bytecode_readable))

    loader_unbound = copy.deepcopy(document)
    del loader_unbound["semanticClosure"]["executedLoaderPolicy"]
    mutants.append(("executed-loader-policy-dropped", loader_unbound))

    unbound_runtime = copy.deepcopy(document)
    del unbound_runtime["semanticClosure"]["interpreterRuntimePolicy"]
    mutants.append(("interpreter-runtime-policy-dropped", unbound_runtime))

    unweighed = copy.deepcopy(document)
    unweighed["semanticClosure"]["distributions"].append(
        {"name": "ckzg", "version": "2.1.5", "modules": ["ckzg"]}
    )
    unweighed["semanticClosure"]["count"] = 3
    unweighed["semanticClosure"]["versionsSha256"] = closure.versions_digest(
        unweighed["semanticClosure"]["distributions"]
    )
    mutants.append(("named-but-never-weighed", unweighed))

    restated = copy.deepcopy(document)
    restated["semanticClosure"]["distributions"][0]["version"] = "0.1.5"
    mutants.append(("version-restated-without-redigest", restated))

    recounted = copy.deepcopy(document)
    recounted["platforms"][native]["fileRecords"] = 34
    mutants.append(("file-total-disagrees-with-rows", recounted))

    repacked = copy.deepcopy(document)
    repacked["platforms"][native]["distributions"][0]["contentSha256"] = "c" * 64
    mutants.append(("row-digest-disagrees-with-total", repacked))

    changed_stdlib = copy.deepcopy(document)
    changed_stdlib["platforms"][native]["standardLibrary"]["files"][0][
        "sha256"
    ] = "6" * 64
    mutants.append(("changed-stdlib-byte", changed_stdlib))

    changed_runtime = copy.deepcopy(document)
    changed_runtime["platforms"][native]["interpreterRuntime"]["files"][0][
        "sha256"
    ] = "7" * 64
    mutants.append(("changed-interpreter-runtime-byte", changed_runtime))

    changed_unowned = copy.deepcopy(document)
    changed_unowned["platforms"][native]["unownedSitePackages"]["files"][0][
        "sha256"
    ] = "9" * 64
    mutants.append(("changed-unowned-site-packages-byte", changed_unowned))

    ungenerated = copy.deepcopy(document)
    for key in platform_keys:
        ungenerated["platforms"][key] = {"generated": False}
    mutants.append(("no-platform-measured", ungenerated))

    duplicated = copy.deepcopy(document)
    duplicated["semanticClosure"]["distributions"].append(
        copy.deepcopy(distributions[0])
    )
    duplicated["semanticClosure"]["count"] = 3
    duplicated["semanticClosure"]["versionsSha256"] = closure.versions_digest(
        duplicated["semanticClosure"]["distributions"]
    )
    mutants.append(("duplicated-distribution", duplicated))

    legacy = copy.deepcopy(document)
    legacy["schema"] = 4
    mutants.append(("legacy-schema", legacy))

    for label, mutant in mutants:
        try:
            lane._validate_runtime_lock_document(profile, mutant)
        except lane.CurrentMainnetError:
            continue
        fail(f"runtime-lock self-check accepted {label}")
    return len(mutants) + closure.self_check()


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    mode = result.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--self-check", action="store_true")
    result.add_argument("--root", help="explicit current-mainnet target root")
    return result


def main() -> int:
    args = parser().parse_args()
    profile = lane.load_profile()
    if args.self_check:
        count = self_check(profile)
        print(f"OK — current-mainnet runtime-lock self-check: {count} mutants rejected")
        return 0
    document, observed, notes = generate(profile, args.root)
    output_path = lane._runtime_lock_path(profile)
    rendered = canonical(document)
    if args.write:
        output_path.write_text(rendered, encoding="utf-8")
        for note in notes:
            print(f"NOTE — {note}")
        print(closure.report(observed, label="semantic closure"))
        print(f"OK — wrote current-mainnet runtime lock: {output_path}")
        return 0
    try:
        committed = output_path.read_text(encoding="utf-8")
    except OSError as exc:
        fail(f"cannot read committed current-mainnet runtime lock: {exc}")
    if committed != rendered:
        fail(
            "committed current-mainnet runtime lock does not describe this target; "
            "run --write on this platform to record it"
        )
    print(
        "OK — current-mainnet runtime lock matches the native platform: "
        f"{document['semanticClosure']['count']} pinned distributions, "
        f"{observed['fileRecords']} distribution files and "
        f"{observed['standardLibrary']['fileRecords']} pinned executable standard-library files, "
        f"plus {observed['interpreterRuntime']['fileRecords']} loaded interpreter runtime "
        f"image record(s)"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (lane.CurrentMainnetError, closure.ClosureError) as exc:
        print(f"REGRESSION — current-mainnet runtime lock: {exc}", file=sys.stderr)
        raise SystemExit(1)
