#!/usr/bin/env python3
"""Generate/check the ProxyPair v1 stack table from compiler-emitted bytes."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import time

import gate_semaphore
import stack_certificate as producer


ROOT = Path(__file__).resolve().parents[1]
EVALUATOR = "scripts/eval-proxy-pair-stack-bytes.lean"
OUTPUT = ROOT / "Blanc/ProxyPairUpgradeStackSafetyData.lean"
MAXIMUM = 3
ROW = re.compile(r"^v1 ([0-9]+) ([0-9a-f]+)$")


def compiler_bytes() -> bytes:
    gate_semaphore.guard("the ProxyPair stack-certificate byte extractor")
    result = subprocess.run(
        ["lake", "env", "lean", EVALUATOR],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    producer.require(result.returncode == 0, f"byte extractor exited {result.returncode}: {result.stdout.strip()}")
    rows = [match for line in result.stdout.splitlines() if (match := ROW.fullmatch(line.strip()))]
    producer.require(len(rows) == 1, "expected exactly one compiler byte row")
    declared, payload = rows[0].groups()
    raw = bytes.fromhex(payload)
    producer.require(len(raw) == int(declared), "compiler byte length disagrees with payload")
    return raw


def produce() -> tuple[str, dict[str, float | int]]:
    started = time.perf_counter()
    raw = compiler_bytes()
    extracted = time.perf_counter()
    states = producer.analyze(raw, MAXIMUM)
    analyzed = time.perf_counter()
    parts = producer.packs(states)
    packed = time.perf_counter()
    output = producer.render_module(
        raw,
        states,
        MAXIMUM,
        "Blanc.ProxyPair.Upgrade.StackSafetyData",
        "table",
        "pack",
        "Blanc.ProxyPair.Upgrade.v1Bytes (actual Prog.compile result)",
        "python3 scripts/gen-proxy-pair-stack-certificate.py --write",
    )
    rendered = time.perf_counter()
    return output, {
        "bytes": len(raw),
        "rows": len(states),
        "packs": len(parts),
        "extraction_seconds": extracted - started,
        "analysis_seconds": analyzed - extracted,
        "packing_seconds": packed - analyzed,
        "render_including_packing_seconds": rendered - packed,
    }


def expected_output() -> str:
    return produce()[0]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--metrics", action="store_true")
    args = parser.parse_args()
    try:
        expected, metrics = produce()
        if args.write:
            OUTPUT.write_text(expected, encoding="utf-8")
            print("OK — wrote Blanc/ProxyPairUpgradeStackSafetyData.lean")
        else:
            try:
                producer.check_output(OUTPUT, expected)
            except producer.Rejected as error:
                raise producer.Rejected(
                    f"{error}; run the registered writer --write"
                ) from error
            print("OK — ProxyPair stack data matches the actual compiler result")
        if args.metrics:
            print(json.dumps(metrics, sort_keys=True))
        return 0
    except (OSError, producer.Rejected) as error:
        print(f"FAIL — ProxyPair stack data: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
