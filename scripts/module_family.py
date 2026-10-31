"""One definition of a Lean module *family*, shared by the growth ledger
(`scripts/report-growth.py`) and the elaboration gate's family totals
(`scripts/check-elab-selection.py family-totals`).

A family is the unit that a consolidation moves text within, so a per-file
number read alone can mislead: folding 30 shards into one file makes that file
slower and larger while the family gets smaller and faster.

* A module nested below `Blanc/<dir>/...` belongs to its parent directory:
  `Blanc/Lift/Usdc/ImplV2Creation/CheckPart0.lean` -> `Blanc/Lift/Usdc/ImplV2Creation/`.
* A top-level `Blanc/<Name>.lean` belongs to its shard stem: a trailing
  `Part<n>` or `_<n>` is stripped, so `Blanc/FooPart2.lean` and
  `Blanc/Foo.lean` are both `Blanc/Foo*`. Bare trailing digits are kept
  (`Weth10` is not a shard of `Weth`).
* Any other path is grouped by its first two components (`scripts/lift/`,
  `docs/`), which is only used for the growth ledger's non-Lean rows.
"""

from __future__ import annotations

import posixpath
import re

TOP_SHARD_SUFFIX = re.compile(r"(?:Part|_)[0-9]+$")
SHARD_STEM_DIGITS = re.compile(r"(?:Part|_)?[0-9]+$")


def module_family(path: str) -> str:
    path = path.replace("\\", "/")
    parts = path.split("/")
    if parts[0] == "Blanc" and len(parts) >= 3:
        return posixpath.dirname(path) + "/"
    if parts[0] == "Blanc" and len(parts) == 2 and path.endswith(".lean"):
        stem = parts[1][: -len(".lean")]
        trimmed = TOP_SHARD_SUFFIX.sub("", stem) or stem
        return f"Blanc/{trimmed}*"
    if path == "Blanc.lean":
        return "Blanc.lean"
    if len(parts) >= 3:
        return "/".join(parts[:2]) + "/"
    if len(parts) == 2:
        return parts[0] + "/"
    return path


def shard_stem(path: str) -> str:
    """The file stem with any trailing shard number removed (`SigningRounds28`
    -> `SigningRounds`). Several files of one family sharing a stem are a shard
    group; one file alone never is."""
    name = posixpath.basename(path)
    stem = name[: -len(".lean")] if name.endswith(".lean") else name
    return SHARD_STEM_DIGITS.sub("", stem) or stem


def self_test() -> int:
    cases = {
        "Blanc/Lift/Usdc/ImplV2Creation/CheckPart0.lean": "Blanc/Lift/Usdc/ImplV2Creation/",
        "Blanc/FooStaging_2.lean": "Blanc/FooStaging*",
        "Blanc/FooStaging.lean": "Blanc/FooStaging*",
        "Blanc/Weth10.lean": "Blanc/Weth10*",
        "Blanc/FooPart3.lean": "Blanc/Foo*",
        "Blanc.lean": "Blanc.lean",
        "scripts/lift/lift.py": "scripts/lift/",
        "docs/COMMON_API.md": "docs/",
    }
    for path, expected in cases.items():
        actual = module_family(path)
        if actual != expected:
            raise AssertionError(f"module_family({path!r}) = {actual!r}, expected {expected!r}")
    if shard_stem("Blanc/X/SigningRounds28.lean") != "SigningRounds" or (
        shard_stem("Blanc/X/Check.lean") != "Check"
    ):
        raise AssertionError("shard_stem misclassifies")
    return len(cases) + 1
