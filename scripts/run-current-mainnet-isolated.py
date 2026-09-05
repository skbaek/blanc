#!/usr/bin/env python3
"""Guard and run one current-mainnet repository Python entrypoint.

The target interpreter starts under ``-I -s -B -X pycache_prefix=/dev/null``.
This trusted bootstrap restores only Blanc's ``scripts/`` directory, verifies
the exact current-mainnet checkout and complete native runtime lock, installs
the live executed-loader guard, and only then imports the selected entrypoint.
"""

from __future__ import annotations

import runpy
import sys
from pathlib import Path


def refuse(message: str) -> None:
    raise RuntimeError(message)


def main() -> None:
    if len(sys.argv) < 3:
        raise SystemExit(
            "usage: run-current-mainnet-isolated.py TARGET_ROOT ENTRYPOINT.py "
            "[ARG ...]"
        )
    scripts = Path(__file__).resolve().parent
    requested = Path(sys.argv[2])
    if requested.is_absolute() or requested.name != str(requested) \
            or requested.suffix != ".py":
        raise SystemExit(
            "current-mainnet entrypoint must name one sibling .py file"
        )
    target = (scripts / requested).resolve()
    if target.parent != scripts or not target.is_file():
        raise SystemExit(
            "current-mainnet entrypoint is absent or outside scripts/"
        )

    sys.path.insert(0, str(scripts))
    import current_mainnet as lane

    lane.closure.assert_bytecode_policy(
        refuse, label="current-mainnet bootstrap"
    )
    profile = lane.load_profile()
    checkout = Path(sys.argv[1]).expanduser().resolve()
    lane.verify_target(checkout, profile)
    paths = lane.target_paths(checkout, profile)
    if Path(sys.executable).resolve() != paths.python.resolve() \
            or Path(sys.prefix).resolve() != paths.venv.resolve():
        refuse("current-mainnet bootstrap is not running in the selected venv")

    lock = lane._load_runtime_lock(profile)
    package_roots = {
        name.split(".", 1)[0]
        for key in ("transitionModules", "transitionPackages", "runtimePackages")
        for name in lock["semanticClosure"]["policy"][key]
    }
    preloaded = sorted(
        name for name in sys.modules
        if name.split(".", 1)[0] in package_roots
    )
    if preloaded:
        refuse(
            "current-mainnet target code was imported before the loader guard: "
            + ", ".join(preloaded[:5])
        )

    # The guarded child probe derives and byte-compares the complete native
    # closure before this process trusts the lock as an import policy.
    lane._python_preflight(paths, profile)
    contract = lane._native_loader_contract(profile, paths)
    lane.closure.assert_executed_loader_policy(
        refuse,
        label="current-mainnet bootstrap",
        site_packages=[lane._site_packages_root(paths)],
        allowed_distributions=contract["allowedDistributions"],
        source_roots=contract["sourceRoots"],
        trusted_source_roots=contract["trustedSourceRoots"],
        standard_library=contract["standardLibrary"],
        unowned_site_packages=contract["unownedSitePackages"],
    )
    sys.argv = [str(target), *sys.argv[3:]]
    runpy.run_path(str(target), run_name="__main__")


if __name__ == "__main__":
    main()
