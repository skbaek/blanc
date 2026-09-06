#!/usr/bin/env python3
"""Construct a new pinned current-mainnet environment; never repair one in place."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import urllib.request

import current_mainnet as lane

HERE = Path(__file__).resolve().parent
RECIPE = HERE / "current-mainnet-runtime-recipe.json"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fail(message: str) -> None:
    raise lane.CurrentMainnetError(message)


def artifact(row: dict, cache: Path, offline: bool) -> Path:
    path = cache / row["sha256"]
    if path.exists():
        if path.is_symlink() or not path.is_file() or sha(path.read_bytes()) != row["sha256"]:
            fail(f"artifact cache mismatch: {path}; preserve it for diagnosis and use a fresh cache")
        return path
    if offline:
        fail(f"offline artifact absent: {row['url']} sha256={row['sha256']}; populate a fresh cache online")
    with urllib.request.urlopen(row["url"], timeout=60) as response:
        data = response.read()
    if sha(data) != row["sha256"]:
        fail(f"download digest mismatch: {row['url']}")
    with path.open("xb") as output:
        output.write(data)
    return path


def archive_executable(row: dict, cache: Path, offline: bool) -> tuple[Path, bytes]:
    archive = artifact(row, cache, offline)
    [(member, expected)] = row["executables"].items()
    with tarfile.open(archive) as source:
        info = source.getmember(member)
        if not info.isfile():
            fail(f"archive executable is not a regular file: {member}")
        data = source.extractfile(info).read()
    if sha(data) != expected:
        fail(f"archive executable digest mismatch: {member}")
    return archive, data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True, help="new absolute checkout path; must not exist")
    parser.add_argument("--cache", type=Path, default=HERE.parent / ".lake/current-mainnet-artifacts")
    parser.add_argument("--source-cache", type=Path, help="optional local Git object source; all source identities still verified")
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--install-python", action="store_true", help="bootstrap missing pinned uv Python; never replace an existing base/alias")
    args = parser.parse_args()
    root = args.root
    if not root.is_absolute() or root != root.resolve() or os.path.lexists(root):
        fail("setup destination must be a new, absolute, non-aliased path; existing environments are never modified")
    cache = args.cache.absolute()
    if cache != cache.resolve():
        fail("artifact cache must not be aliased")
    cache.mkdir(parents=True, exist_ok=True)
    recipe = json.loads(RECIPE.read_text())
    profile = lane.load_profile()
    lane._literal(recipe["schema"], 1, "construction recipe schema")
    lane._literal(recipe["checkoutCommit"], profile["target"]["checkoutCommit"], "construction checkout")
    key, platform = lane._selected_platform(profile)
    native = recipe["platforms"][key]
    _, uv_bytes = archive_executable(native["uv"], cache, args.offline)
    _, python_bytes = archive_executable(native["python"], cache, args.offline)
    uv = cache / ("uv-" + sha(uv_bytes))
    if not uv.exists():
        with uv.open("xb") as output:
            output.write(uv_bytes)
        uv.chmod(0o755)
    if uv.is_symlink() or sha(uv.read_bytes()) != sha(uv_bytes):
        fail("selected installer executable is corrupt")
    env = {"HOME": os.environ["HOME"], "PATH": f"{cache}:/usr/bin:/bin:/usr/sbin:/sbin",
           "UV_CACHE_DIR": str(cache / "uv-cache"), "UV_LINK_MODE": "copy",
           "UV_CONCURRENT_BUILDS": "1", "PYTHONNOUSERSITE": "1"}
    if "TMPDIR" in os.environ:
        env["TMPDIR"] = os.environ["TMPDIR"]
    commands = []

    def run(argv: list[str], cwd: Path | None = None, data: bytes | None = None) -> bytes:
        commands.append({"argv": argv, "cwd": str(cwd) if cwd else None})
        result = subprocess.run(argv, cwd=cwd, env=env, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode:
            fail(f"construction command failed ({result.returncode}): {argv}\n{result.stderr.decode(errors='replace')}")
        return result.stdout

    base = lane._expanded_home_path(platform["uvBasePrefix"], "Python base")
    alias = lane._expanded_home_path(platform["uvAliasPrefix"], "Python alias")
    python = alias / "bin/python3.11"
    if not python.exists():
        if not args.install_python or args.offline or os.path.lexists(base) or os.path.lexists(alias):
            fail(f"pinned Python absent: {python}; on a fresh host use --install-python; preserve any partial base/alias")
        run([str(uv), "python", "install", lane._EXPECTED["pythonVersion"]])
    if python.resolve() != (base / "bin/python3.11").resolve() or sha(python.read_bytes()) != sha(python_bytes):
        fail("installed Python differs from the pinned distribution; preserve it and provision the documented exact base")
    patch = (HERE / "reference/current-mainnet/target-overlay.patch").read_bytes()
    commit = (HERE / "reference/current-mainnet/target-commit.txt").read_bytes()
    lane._literal(sha(patch), recipe["overlaySha256"], "construction overlay")
    lane._literal(sha(commit), recipe["commitObjectSha256"], "construction commit object")
    lane._literal(sha(patch), profile["target"]["overlay"]["diffSha256"], "profile overlay")
    git = profile["target"]["git"]
    run([git, "init", str(root)])
    run([git, "remote", "add", "origin", profile["target"]["repository"]], root)
    source = str(args.source_cache) if args.source_cache else profile["target"]["repository"]
    if args.offline and args.source_cache is None:
        fail("offline reconstruction requires --source-cache with the pinned upstream object")
    run([git, "fetch", "--depth=1", source, profile["target"]["upstreamCommit"]], root)
    run([git, "checkout", "--detach", profile["target"]["upstreamCommit"]], root)
    run([git, "apply", "--index", "-"], root, patch)
    tree = run([git, "write-tree"], root).decode().strip()
    lane._literal(commit.splitlines()[0], f"tree {tree}".encode(), "reconstructed commit tree")
    object_id = run([git, "hash-object", "-t", "commit", "-w", "--stdin"], root, commit).decode().strip()
    lane._literal(object_id, recipe["checkoutCommit"], "reconstructed commit object")
    run([git, "reset", "--hard", object_id], root)
    for name, expected in recipe["sourceFiles"].items():
        lane._literal(sha((root / name).read_bytes()), expected, f"construction source {name}")
    exported = run([str(uv), "export", *recipe["exportArgs"]], root)
    lane._literal(sha(exported), recipe["exportSha256"], "locked dependency export")
    requirements = exported
    for row in recipe["buildRequirements"]:
        artifact(row, cache, args.offline)
        requirements += f"\n{row['name']}=={row['version']} --hash=sha256:{row['sha256']}\n".encode()
    requirement_path = cache / (sha(requirements) + ".txt")
    if not requirement_path.exists():
        with requirement_path.open("xb") as output:
            output.write(requirements)
    lane._literal(sha(requirement_path.read_bytes()), sha(requirements), "construction requirements")
    run([str(uv), "venv", "--python", str(python), "--prompt", "ethereum-execution", str(root / ".venv")])
    selected = root / ".venv/bin/python"
    flags = ["--offline"] if args.offline else []
    run([str(uv), "pip", "sync", "--python", str(selected), "--require-hashes", "--only-binary", ":all:", *flags, str(requirement_path)])
    run([str(uv), "pip", "install", "--python", str(selected), "--offline", "--no-deps", "--no-build-isolation", "--editable", str(root), "--editable", str(root / "packages/testing")])
    lane.verify_target(root, profile)
    paths = lane.target_paths(root, profile)
    lane._python_preflight(paths, profile, verify_runtime=False)
    print(json.dumps({"status": "CONSTRUCTED", "recipeSha256": sha(RECIPE.read_bytes()),
                      "root": str(root), "platform": key, "commands": commands,
                      "nativeClosure": lane._runtime_entry(paths)}, indent=2), flush=True)
    lane._python_preflight(paths, profile)
    print("OK — current-mainnet setup: exact reconstructed source and runtime accepted")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (lane.CurrentMainnetError, OSError, ValueError, KeyError) as error:
        print(f"SETUP FAILED — current-mainnet: {error}\nSee docs/CURRENT_MAINNET_SETUP.md; do not refresh the runtime lock to accept a failed installation.", file=sys.stderr)
        raise SystemExit(1)
