#!/usr/bin/env python3
"""Static checker for the frozen OssifiableProxy performance contract.

This checker never imports EELS, executes EVM code, or records a scalar.  It
validates the result-free campaign, resolves all frozen reference inputs, and
optionally validates already-produced immutable result ledgers.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import lido_ossifiable_proxy_performance_schema as schema


def _default_manifest(root: Path) -> Path:
    return root / schema.MANIFEST_RELATIVE


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check the static OssifiableProxy performance contract without measuring it",
    )
    parser.add_argument("--root", type=Path, default=schema.DEFAULT_ROOT)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument(
        "--result", type=Path, action="append", default=[],
        help="optional immutable baseline/final result ledger; may be repeated",
    )
    parser.add_argument(
        "--require-final-threshold", action="store_true",
        help="require one supplied final ledger to meet the 13-strict-win threshold",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    manifest_path = (args.manifest or _default_manifest(root)).resolve()

    try:
        _, manifest_value = schema.load_json(manifest_path, "performance manifest")
        manifest = schema.validate_manifest_schema(
            manifest_value,
            root=root,
            enforce_frozen_digest=True,
            validate_external=True,
        )

        results: list[dict] = []
        for path in args.result:
            _, result_value = schema.load_json(path.resolve(), f"performance result {path}")
            results.append(schema.validate_result_schema(
                result_value,
                manifest,
                root=root,
                enforce_self_digest=True,
                validate_external=True,
            ))

        stages = [result["result"]["stage"] for result in results]
        schema.require(len(stages) == len(set(stages)),
                       "performance results: at most one baseline and one final are allowed")
        if "baseline" in stages and "final" in stages:
            baseline = results[stages.index("baseline")]
            final = results[stages.index("final")]
            schema.require(
                final["result"]["predecessorResultSha256"]
                == baseline["result"]["digest"]["value"],
                "final result: predecessor does not equal the baseline canonical self-digest",
            )

        if args.require_final_threshold:
            schema.require("final" in stages,
                           "--require-final-threshold needs a supplied final result")
            schema.require_final_threshold(results[stages.index("final")])
    except (OSError, schema.SchemaError) as exc:
        print(f"REGRESSION — OssifiableProxy static performance contract: {exc}", file=sys.stderr)
        return 1

    suffix = "manifest only" if not results else f"manifest + {len(results)} result ledger(s)"
    print(
        "OK — OssifiableProxy static performance contract: "
        f"{suffix}; 25 ordered cells; denominator 25; threshold 13 strict wins; no measurements run"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
