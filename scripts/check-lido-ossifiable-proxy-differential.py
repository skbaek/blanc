#!/usr/bin/env python3
"""Validate one immutable OssifiableProxy differential result offline."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

from lido_ossifiable_proxy_differential_schema import (
    CASE_COUNT,
    MANIFEST_DIGEST,
    load_and_validate_campaign,
    load_json,
    validate_result,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("result", type=Path)
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument("--require-all-matched", action="store_true")
    args = parser.parse_args()
    root = args.repo_root.expanduser().resolve()
    manifest, performance, _ = load_and_validate_campaign(root)
    result = load_json(args.result.expanduser().resolve())
    validate_result(
        result,
        manifest,
        performance=performance,
        repo_root=root,
        require_all_matched=args.require_all_matched,
    )
    head = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
    ).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(root), "status", "--porcelain"], text=True
    ).strip()
    if result["identity"]["blanc"]["commit"] != head or dirty:
        raise RuntimeError(
            "result Blanc commit must equal this clean checkout: "
            f"result={result['identity']['blanc']['commit']}, head={head}, dirty={bool(dirty)}"
        )
    matched = result["summary"]["matchedCaseCount"]
    print(
        f"OK — OssifiableProxy differential result: {matched}/{CASE_COUNT} rows match; "
        f"zero skipped; manifest {MANIFEST_DIGEST}; "
        f"result {result['identity']['resultDigest']['value']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(
            "REGRESSION — OssifiableProxy differential result: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
