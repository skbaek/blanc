#!/usr/bin/env python3
"""Generate the native two-platform runtime lock for current-mainnet gates.

Ordinary writes refresh only the platform executing this generator and preserve
the other validated row.  The legacy-import option exists for the one-time
migration of evidence generated before the lock was split from the portable
Beacon manifest.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any, NoReturn

import current_mainnet as lane


def fail(message: str) -> NoReturn:
    raise lane.CurrentMainnetError(message)


def read_json(path: Path, label: str) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read {label} {path}: {exc}")


def canonical(document: Any) -> str:
    return json.dumps(document, indent=2, sort_keys=True) + "\n"


def legacy_pyvenv_version(digest: str, home: Path) -> str:
    """Recover and validate the semantic uv field behind a legacy raw digest."""

    matches: list[str] = []
    for minor in range(50):
        for patch in range(1000):
            uv = f"0.{minor}.{patch}"
            for version_info in ("3.11", lane._EXPECTED["pythonVersion"]):
                text = "\n".join((
                    f"home = {home}",
                    f"implementation = {lane._EXPECTED['pythonImplementation']}",
                    f"uv = {uv}",
                    f"version_info = {version_info}",
                    "include-system-site-packages = false",
                    "prompt = ethereum-execution",
                    "",
                ))
                if hashlib.sha256(text.encode()).hexdigest() == digest:
                    matches.append(uv)
    if len(matches) != 1:
        fail(
            "legacy pyvenv.cfg digest does not identify exactly one supported "
            f"semantic uv configuration, got {matches}"
        )
    return matches[0]


def legacy_platform_entry(
    manifest_path: Path,
    platform_key: str,
    profile: dict[str, Any],
    live_paths: lane.TargetPaths,
) -> dict[str, Any]:
    manifest = read_json(manifest_path, "legacy current-mainnet manifest")
    if not isinstance(manifest, dict):
        fail("legacy current-mainnet manifest is not an object")
    cache = manifest.get("cacheInputs")
    if not isinstance(cache, dict):
        fail("legacy current-mainnet manifest has no cacheInputs object")
    target_files = cache.get("targetFiles")
    site = cache.get("targetSitePackages")
    if not isinstance(target_files, dict) or not isinstance(site, dict):
        fail("legacy current-mainnet cache evidence is incomplete")
    if set(target_files) != {"pyvenvConfig", "pythonExecutable", "t8nEntrypoint"}:
        fail("legacy current-mainnet target-file set differs")

    platforms = profile["target"]["pythonIdentity"]["platforms"]
    if platform_key not in platforms:
        fail(f"legacy import names unsupported platform {platform_key!r}")
    row = platforms[platform_key]
    python = target_files["pythonExecutable"]
    pyvenv = target_files["pyvenvConfig"]
    t8n = target_files["t8nEntrypoint"]
    if not isinstance(python, dict) or not isinstance(pyvenv, dict) \
            or not isinstance(t8n, dict):
        fail("legacy target-file fingerprints are malformed")
    if set(python) != {"relativePath", "isSymlink", "sha256", "symlinkTarget"}:
        fail("legacy Python fingerprint shape differs")
    if python["relativePath"] != ".venv/bin/python" or python["isSymlink"] is not True:
        fail("legacy Python fingerprint is not the selected venv symlink")
    if not lane._is_sha256(python["sha256"]):
        fail("legacy Python executable digest is malformed")
    symlink_target = python["symlinkTarget"]
    if not isinstance(symlink_target, str) or not Path(symlink_target).is_absolute():
        fail("legacy Python symlink target is not absolute")
    alias_suffix = row["uvAliasPrefix"][2:] + "/bin/python3.11"
    normalized_target = Path(symlink_target).as_posix()
    if not normalized_target.endswith("/" + alias_suffix):
        fail("legacy Python symlink does not select the named native uv alias")
    legacy_home = Path(normalized_target[: -len(alias_suffix)]).as_posix().rstrip("/")
    if not legacy_home:
        fail("legacy Python symlink does not reveal an absolute home")
    if set(pyvenv) != {"relativePath", "isSymlink", "sha256"} \
            or pyvenv["relativePath"] != ".venv/pyvenv.cfg" \
            or pyvenv["isSymlink"] is not False \
            or not lane._is_sha256(pyvenv["sha256"]):
        fail("legacy pyvenv.cfg fingerprint differs")
    legacy_pyvenv_version(pyvenv["sha256"], Path(symlink_target).parent)

    if set(t8n) != {"relativePath", "isSymlink", "sha256"}:
        fail("legacy t8n fingerprint shape differs")
    if t8n["relativePath"] != ".venv/bin/ethereum-spec-evm" \
            or t8n["isSymlink"] is not False \
            or not lane._is_sha256(t8n["sha256"]):
        fail("legacy t8n fingerprint differs")
    try:
        live_raw = live_paths.t8n.read_bytes()
    except OSError as exc:
        fail(f"cannot read live t8n entrypoint for legacy validation: {exc}")
    _, separator, body = live_raw.partition(b"\n")
    if not separator:
        fail("live t8n entrypoint has no shebang-delimited body")
    default_root = profile["target"]["defaultRoot"]
    if not default_root.startswith("~/"):
        fail("profile default root is not home-relative")
    legacy_python = (
        Path(legacy_home)
        / default_root[2:]
        / profile["target"]["venv"]
        / profile["target"]["python"]
    )
    reconstructed = b"#!" + os.fspath(legacy_python).encode() + b"\n" + body
    if hashlib.sha256(reconstructed).hexdigest() != t8n["sha256"]:
        fail("legacy t8n fingerprint does not share the live pinned entrypoint body")

    expected_site_keys = {"relativeRoot", "fileRecords", "sha256", "excludes"}
    if set(site) != expected_site_keys:
        fail("legacy site-packages fingerprint shape differs")
    candidate = {
        "pythonExecutableSha256": python["sha256"],
        "targetSitePackages": copy.deepcopy(site),
    }
    probe = {
        "schema": 1,
        "target": lane._runtime_target_document(live_paths),
        "platforms": {
            key: copy.deepcopy(candidate)
            for key in profile["target"]["pythonIdentity"]["platforms"]
        },
    }
    lane._validate_runtime_lock_document(profile, probe)
    return candidate


def existing_platforms(
    path: Path, profile: dict[str, Any]
) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    document = lane._validate_runtime_lock_document(
        profile, read_json(path, "current-mainnet runtime lock")
    )
    return copy.deepcopy(document["platforms"])


def generate(
    profile: dict[str, Any],
    root: str | None,
    legacy_manifest: Path | None,
    legacy_platform: str | None,
) -> dict[str, Any]:
    lane.verify_target(root, profile)
    paths = lane.target_paths(root, profile)
    evidence = lane._python_preflight(paths, profile, verify_runtime=False)
    key = evidence["platformKey"]
    output_path = lane._runtime_lock_path(profile)
    platforms = existing_platforms(output_path, profile)
    if legacy_manifest is not None:
        if legacy_platform is None:
            fail("--import-legacy-platform is required with --import-legacy-manifest")
        if legacy_platform == key:
            fail("legacy import must name the non-native platform row")
        platforms[legacy_platform] = legacy_platform_entry(
            legacy_manifest, legacy_platform, profile, paths
        )
    elif legacy_platform is not None:
        fail("--import-legacy-platform requires --import-legacy-manifest")
    platforms[key] = lane._runtime_entry(paths)
    document = {
        "schema": 1,
        "target": lane._runtime_target_document(paths),
        "platforms": platforms,
    }
    return lane._validate_runtime_lock_document(profile, document)


def self_check(profile: dict[str, Any]) -> int:
    sample_site = {
        "relativeRoot": ".venv/lib/python3.11/site-packages",
        "fileRecords": 1,
        "sha256": "1" * 64,
        "excludes": list(lane._RUNTIME_EXCLUDES),
    }
    document = {
        "schema": 1,
        "target": {
            "checkoutCommit": lane._EXPECTED["checkoutCommit"],
            "pythonImplementation": lane._EXPECTED["pythonImplementation"],
            "pythonVersion": lane._EXPECTED["pythonVersion"],
            "entrypointBodySha256": "2" * 64,
            "sitePackagesExcludes": list(lane._RUNTIME_EXCLUDES),
        },
        "platforms": {
            key: {
                "pythonExecutableSha256": "3" * 64,
                "targetSitePackages": copy.deepcopy(sample_site),
            }
            for key in profile["target"]["pythonIdentity"]["platforms"]
        },
    }
    lane._validate_runtime_lock_document(profile, document)
    mutants: list[tuple[str, dict[str, Any]]] = []
    missing = copy.deepcopy(document)
    del missing["platforms"]["macos-arm64"]
    mutants.append(("missing-platform", missing))
    weakened = copy.deepcopy(document)
    weakened["platforms"]["linux-x86_64"]["targetSitePackages"]["excludes"] = []
    mutants.append(("weakened-excludes", weakened))
    malformed = copy.deepcopy(document)
    malformed["target"]["entrypointBodySha256"] = "not-a-digest"
    mutants.append(("malformed-digest", malformed))
    for label, mutant in mutants:
        try:
            lane._validate_runtime_lock_document(profile, mutant)
        except lane.CurrentMainnetError:
            continue
        fail(f"runtime-lock self-check accepted {label}")
    return len(mutants)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    mode = result.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--self-check", action="store_true")
    result.add_argument("--root", help="explicit current-mainnet target root")
    result.add_argument("--import-legacy-manifest", type=Path)
    result.add_argument("--import-legacy-platform")
    return result


def main() -> int:
    args = parser().parse_args()
    profile = lane.load_profile()
    if args.self_check:
        if args.import_legacy_manifest is not None or args.import_legacy_platform is not None:
            fail("legacy import options are valid only with --write")
        count = self_check(profile)
        print(f"OK — current-mainnet runtime-lock self-check: {count} mutants rejected")
        return 0
    if args.check and (args.import_legacy_manifest is not None or args.import_legacy_platform is not None):
        fail("legacy import options are valid only with --write")
    document = generate(
        profile,
        args.root,
        args.import_legacy_manifest,
        args.import_legacy_platform,
    )
    output_path = lane._runtime_lock_path(profile)
    rendered = canonical(document)
    if args.write:
        output_path.write_text(rendered, encoding="utf-8")
        print(f"OK — wrote current-mainnet runtime lock: {output_path}")
        return 0
    try:
        committed = output_path.read_text(encoding="utf-8")
    except OSError as exc:
        fail(f"cannot read committed current-mainnet runtime lock: {exc}")
    if committed != rendered:
        fail("committed current-mainnet runtime lock is stale for this native platform")
    print("OK — current-mainnet runtime lock matches the native platform")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except lane.CurrentMainnetError as exc:
        print(f"REGRESSION — current-mainnet runtime lock: {exc}", file=sys.stderr)
        raise SystemExit(1)
