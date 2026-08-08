#!/usr/bin/env python3
"""Verify the Solidity borrower's committed source hash independently.

`gen-fmint-borrower-solc.py` records a Keccak-256 of the Solidity source in
`fmint-borrower-solc.json` while regenerating the compiled runtime.  This
checker does not run that generator or trust the artifact to choose its input:
it pins the repository source path and recomputes the digest with the existing
pure-Python Keccak implementation used by Blanc's WETH10 reference checks.

This is source/artifact provenance only.  It deliberately does not claim to
recompile Solidity or prove that the artifact runtime was produced by this
source; changing compiler inputs remains a reviewed regeneration operation.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "scripts" / "fmint-borrower-solc.json"
SOURCE = ROOT / "scripts" / "fmint-borrower-solc.sol"
SOURCE_REF = "scripts/fmint-borrower-solc.sol"
SOURCE_UNIT = "fmint-borrower-solc.sol"
HASH = re.compile(r"0x[0-9a-f]{64}\Z")


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def strict_json(path: Path) -> Any:
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            require(key not in result, f"{path}: duplicate JSON key {key!r}")
            result[key] = value
        return result

    def invalid_constant(value: str) -> None:
        raise CheckError(f"{path}: non-finite JSON value {value}")

    try:
        data = path.read_text(encoding="utf-8")
        return json.loads(data, object_pairs_hook=object_pairs,
                          parse_constant=invalid_constant)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CheckError(f"cannot read artifact {path}: {exc}") from exc


def load_keccak() -> ModuleType:
    path = ROOT / "scripts" / "weth10-reference.py"
    spec = importlib.util.spec_from_file_location("weth10_reference", path)
    require(spec is not None and spec.loader is not None,
            f"cannot load independent Keccak implementation from {path}")
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
    except (ImportError, OSError) as exc:
        raise CheckError(
            f"cannot load independent Keccak implementation from {path}: {exc}") from exc
    require(callable(getattr(module, "keccak256", None)),
            f"{path}: no callable keccak256 implementation")
    return module


def check(artifact_path: Path, source_path: Path) -> str:
    artifact = strict_json(artifact_path)
    require(isinstance(artifact, dict), f"{artifact_path}: top level is not an object")
    provenance = artifact.get("provenance")
    require(isinstance(provenance, dict),
            f"{artifact_path}: provenance is missing or not an object")

    # These identities are checker-owned constants.  In particular, the
    # artifact cannot redirect this check to a different source that happens
    # to hash to its own committed value.
    require(provenance.get("source") == SOURCE_REF,
            f"{artifact_path}: provenance.source must be {SOURCE_REF!r}")
    require(provenance.get("sourceUnit") == SOURCE_UNIT,
            f"{artifact_path}: provenance.sourceUnit must be {SOURCE_UNIT!r}")
    expected = provenance.get("sourceKeccak256")
    require(isinstance(expected, str) and HASH.fullmatch(expected) is not None,
            f"{artifact_path}: provenance.sourceKeccak256 is not canonical lowercase 0x hex")

    try:
        source = source_path.read_bytes()
    except OSError as exc:
        raise CheckError(f"cannot read pinned borrower source {source_path}: {exc}") from exc
    require(bool(source), f"pinned borrower source {source_path} is empty")

    actual = "0x" + load_keccak().keccak256(source)
    require(actual == expected,
            f"{source_path}: Keccak-256 mismatch; artifact records {expected}, "
            f"independent recomputation is {actual}")
    return (f"OK — fmint borrower source hash: {len(source)} source bytes match "
            f"artifact provenance ({actual})")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    parser.add_argument("--source", type=Path, default=SOURCE)
    args = parser.parse_args(argv)
    try:
        print(check(args.artifact, args.source))
        return 0
    except CheckError as exc:
        print(f"REGRESSION — fmint borrower source hash: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
