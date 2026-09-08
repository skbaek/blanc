#!/usr/bin/env python3
"""Verify the Solidity borrower's committed source hash independently.

`gen-fmint-borrower-solc.py` records a Keccak-256 of the Solidity source in
`fmint-borrower-solc.json` while regenerating the compiled runtime.  This
checker does not run that generator or trust the artifact to choose its input:
it pins the repository source path and recomputes the digest with the existing
shared pure-Python Keccak implementation. The generator uses external EELS.

This is source/artifact provenance only.  It deliberately does not claim to
recompile Solidity or prove that the artifact runtime was produced by this
source; changing compiler inputs remains a reviewed regeneration operation.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

from keccak import keccak256_hex

from strict_json import DuplicateKeyError, NonFiniteNumberError, loads as strict_json_loads


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
    try:
        data = path.read_text(encoding="utf-8")
        return strict_json_loads(data)
    except DuplicateKeyError as exc:
        raise CheckError(f"{path}: duplicate JSON key {exc.key!r}") from exc
    except NonFiniteNumberError as exc:
        raise CheckError(f"{path}: non-finite JSON value {exc.value}") from exc
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CheckError(f"cannot read artifact {path}: {exc}") from exc


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

    actual = keccak256_hex(source)
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
