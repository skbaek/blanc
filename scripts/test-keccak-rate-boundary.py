#!/usr/bin/env python3
"""Check every in-repo Keccak-256 implementation against independent vectors.

Blanc keeps one Keccak-256 implementation per evidence surface on purpose.
This control enumerates them all and holds each to the rate-boundary vectors in
`keccak_rate_boundary_vectors`, which come from the pinned execution-specs
oracle rather than from anything in this repository.  A surface that grows a
new implementation, or loses one, fails here rather than silently escaping the
control: the enumeration below is compared against a static scan of
`scripts/**/*.py` for sponge implementations.

Run: `python3 scripts/test-keccak-rate-boundary.py`
"""

from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path
from types import ModuleType
from typing import Callable, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))

import keccak_rate_boundary_vectors as vectors  # noqa: E402

# (script file, attribute) for every independent Keccak-256 sponge in Blanc.
IMPLEMENTATIONS: Tuple[Tuple[str, str], ...] = (
    ("gen-beacon-deposit-vectors.py", "keccak256"),
    ("gen-beacon-deposit-current-mainnet.py", "keccak256"),
    ("check-lido-twg-census.py", "keccak256"),
    ("lido_circuit_breaker_reference_schema.py", "keccak_bytes"),
    ("lido_twg_reference_schema.py", "keccak_bytes"),
    ("lido_ossifiable_proxy_reference_schema.py", "keccak256"),
    ("lido_ossifiable_proxy_performance_schema.py", "keccak256"),
    ("weth10_reference_schema.py", "keccak256"),
    ("weth10-reference.py", "keccak256"),
)

# A sponge is identifiable by its absorb loop over the rate.  Any file that
# grows one must be added to IMPLEMENTATIONS above.
SPONGE = re.compile(r"padded\s*=\s*bytearray\(")


def load(filename: str) -> ModuleType:
    path = SCRIPTS / filename
    name = "keccak_probe_" + re.sub(r"[^0-9A-Za-z_]", "_", filename)
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AssertionError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def enumerate_sponges() -> List[str]:
    found = []
    for path in sorted(SCRIPTS.rglob("*.py")):
        if path.name in ("keccak_rate_boundary_vectors.py", Path(__file__).name):
            continue
        if SPONGE.search(path.read_text(encoding="utf-8", errors="replace")):
            found.append(str(path.relative_to(SCRIPTS)))
    return found


def main() -> int:
    failures: List[str] = []

    declared = {name for name, _ in IMPLEMENTATIONS}
    scanned = set(enumerate_sponges())
    for missing in sorted(scanned - declared):
        failures.append(
            f"{missing} contains a Keccak sponge but is not in IMPLEMENTATIONS")
    for stale in sorted(declared - scanned):
        failures.append(
            f"{stale} is declared but no longer contains a Keccak sponge")

    checked: Dict[str, int] = {}
    for filename, attribute in IMPLEMENTATIONS:
        try:
            module = load(filename)
        except Exception as exc:  # pragma: no cover - loader diagnostics
            failures.append(f"{filename}: cannot load ({exc})")
            continue
        keccak: Callable[[bytes], object] | None = getattr(
            module, attribute, None)
        if not callable(keccak):
            failures.append(f"{filename}: no callable {attribute}")
            continue
        bad = vectors.failures(keccak)
        if bad:
            failures.extend(f"{filename}.{attribute} {line}" for line in bad)
        checked[filename] = len(vectors.VECTORS) + len(vectors.SELECTORS)

    if failures:
        for line in failures:
            print(f"FAIL {line}", file=sys.stderr)
        print(f"FAIL keccak rate-boundary control: {len(failures)} failure(s)",
              file=sys.stderr)
        return 1

    total = sum(checked.values())
    print(f"OK keccak rate-boundary control: {len(checked)} implementations"
          f" x {len(vectors.VECTORS)} lengths + {len(vectors.SELECTORS)}"
          f" selectors = {total} comparisons against {vectors.ORACLE}"
          f" @ {vectors.ORACLE_PIN}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
