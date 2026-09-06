"""Fixed DRIP Lean transports and immutable dependency metadata.

Requires an owned import build and checked artifact integrity before real use.
Lake depHash describes the built import closure; neither it nor this snapshot
authenticates restored artifact bytes. This module never builds or certifies.
The caller owns semantic validation and any additional input-population check.
"""
from __future__ import annotations

import hashlib
import importlib.util
import os
from pathlib import Path
import re
import subprocess
from typing import Callable, Iterable


class HelperError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise HelperError(message)


EVALUATORS = {
    "scripts/eval-drip-receipts.lean": ("--run",),
    "scripts/eval-drip-arithmetic.lean": (),
}
SHARED_SOURCES = (
    "scripts/drip_evaluator.py", "scripts/gate-cache.py",
    "scripts/gate_cache_lock.py", "scripts/gate_cache_t8n_root.py",
    "lean-toolchain", "lakefile.lean", "lake-manifest.json",
)

_spec = importlib.util.spec_from_file_location(
    "drip_evaluator_gate_cache", Path(__file__).with_name("gate-cache.py"))
assert _spec and _spec.loader
GATE_CACHE = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(GATE_CACHE)


def _entry(root: Path, evaluator: str) -> Path:
    require(type(evaluator) is str and evaluator in EVALUATORS,
            "unsupported DRIP evaluator")
    path = root / evaluator
    require(path.is_file() and not path.is_symlink(),
            "DRIP evaluator missing or nonregular: owned implementation/build required")
    return path


def _digest(path: Path) -> str:
    require(path.is_file() and not path.is_symlink(), f"regular file required: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compiler_files(root: Path) -> tuple[Path, ...]:
    """Fingerprint the actual pinned binaries selected by absolute dispatch."""
    toolchain = (root / "lean-toolchain").read_text().strip()
    require(re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+", toolchain),
            "unsupported pinned compiler toolchain")
    directory = Path.home() / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---")
    libraries = tuple(sorted(path for path in (directory / "lib/lean").glob("*shared*")
                             if path.suffix in (".so", ".dylib")))
    require(libraries, "pinned compiler shared libraries missing")
    paths = (directory / "bin/lake", directory / "bin/lean", *libraries)
    require(all(path.is_file() and not path.is_symlink() for path in paths),
            "pinned compiler files missing or nonregular")
    require(all(os.access(path, os.X_OK) for path in paths[:2]),
            "pinned compiler binaries are not executable")
    return paths


def evaluator_environment(root: Path) -> dict[str, str]:
    """Preserve only the reviewed wrapper's explicit shared-cache selection."""
    raw = os.environ.get("LAKE_CACHE_DIR", "")
    require(raw and Path(raw).is_absolute(), "absolute LAKE_CACHE_DIR is required")
    cache = Path(raw).resolve(strict=True)
    require(cache.is_dir(), "LAKE_CACHE_DIR is not a directory")
    artifacts = cache / "artifacts"
    require(artifacts.is_dir() and any(path.is_file() and not path.is_symlink()
                                     for path in artifacts.iterdir()),
            "LAKE_CACHE_DIR has no regular cache artifacts (presence, not integrity)")
    toolchain_bin = compiler_files(root)[0].parent
    return {
        "HOME": str(Path.home().resolve(strict=True)),
        "PATH": str(toolchain_bin) + os.pathsep + os.defpath,
        "LANG": "C.UTF-8",
        "LAKE_CACHE_DIR": str(cache),
    }


def snapshot(root: Path, evaluator: str,
             source_files: Iterable[str]) -> tuple[tuple[str, str], ...]:
    """Source/compiler/environment bytes and existing Lake import metadata.

    Missing or malformed import traces fail closed. The integrating gate owns
    prior build/artifact-integrity/certificate prerequisites; a current depHash
    alone is not a content-integrity check and does not certify fresh sources.
    """
    _entry(root, evaluator)
    require(not isinstance(source_files, (str, bytes)), "source files must be a collection")
    names = tuple(source_files)
    require(all(type(name) is str and name and not Path(name).is_absolute()
                and ".." not in Path(name).parts and str(Path(name)) == name
                for name in names), "source paths must be normalized repository relatives")
    # Both fixed evaluators consume the pinned Jaune package. Preserve the
    # drivers' pre-existing current-source/discovery guard independently of
    # Lake's built closure metadata: an unrebuilt source edit need not move a
    # trace. This concrete package inventory is not an import/artifact walker.
    package = root / ".lake/packages/jaune"
    require(package.is_dir() and not package.is_symlink(),
            "pinned Jaune package missing or symlink")
    jaune_sources = tuple(path.relative_to(root).as_posix()
                          for path in sorted(package.rglob("*.lean")))
    require(jaune_sources, "pinned Jaune sources missing")
    detail = {}
    for name in sorted(set((*SHARED_SOURCES, evaluator, *names, *jaune_sources))):
        detail["source:" + name] = _digest(root / name)
    for path in compiler_files(root):
        detail["compiler:" + str(path)] = _digest(path)
    for name, value in evaluator_environment(root).items():
        detail["environment:" + name] = value
    try:
        closure_digest, closure = GATE_CACHE.component_lean_entries(root, [evaluator])
    except (GATE_CACHE.GateCacheError, GATE_CACHE.Unresolvable) as exc:
        raise HelperError(f"DRIP evaluator import metadata unavailable: {exc}") from exc
    detail["lean-entry-digest"] = closure_digest
    for name, value in closure.items():
        detail["lean-entry:" + name] = value
    return tuple(sorted(detail.items()))


def assert_unchanged(root: Path, evaluator: str, source_files: Iterable[str],
                     expected_snapshot: tuple[tuple[str, str], ...]) -> None:
    require(snapshot(root, evaluator, source_files) == expected_snapshot,
            "DRIP evaluator source/compiler/environment/import snapshot drift")


def evaluate(root: Path, evaluator: str, request_text: str | None,
             before_after_check: Callable[[], None]) -> str:
    """One of two fixed subprocesses; no executable, mode, or argv override.

    Receipts use --run and one input JSON line; arithmetic uses its fixed
    #eval script and no input payload. All subprocesses must remain inside the
    already admitted workflow; this function does not obtain host admission.
    """
    _entry(root, evaluator)
    require((evaluator == "scripts/eval-drip-arithmetic.lean" and request_text is None)
            or (evaluator == "scripts/eval-drip-receipts.lean" and type(request_text) is str),
            "DRIP evaluator input mode differs")
    identity = snapshot(root, evaluator, ())
    before_after_check()
    lake, lean, *_ = compiler_files(root)
    command = [str(lake), "env", str(lean), *EVALUATORS[evaluator], evaluator]
    options = dict(cwd=root, capture_output=True, text=True, check=False,
                   env=evaluator_environment(root))
    if request_text is not None:
        options["input"] = request_text + "\n"
    try:
        result = subprocess.run(command, **options)
    finally:
        # A failing child or a launch exception still cannot certify a prefix.
        assert_unchanged(root, evaluator, (), identity)
        before_after_check()
    require(result.returncode == 0,
            f"DRIP evaluator exit {result.returncode}: {result.stderr}")
    require(result.stderr == "", "unexpected DRIP evaluator diagnostics")
    require(type(result.stdout) is str, "DRIP evaluator stdout is not text")
    return result.stdout
