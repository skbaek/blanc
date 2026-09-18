#!/usr/bin/env python3
"""Non-elaborating identity for fixed DRIP evaluator gate reuse.

This is metadata, not arithmetic/receipt authentication or artifact integrity.
The integrating gate still owns the build, certification and fixture census.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

import drip_evaluator as HELPER

ROOT = Path(__file__).resolve().parents[1]
SELF = "scripts/drip-evaluator-identity.py"
MODES = {
    "arithmetic": "scripts/check-drip-arithmetic.py",
    "receipts": "scripts/check-drip-receipts.py",
}


def load_driver(mode):
    path = ROOT / MODES[mode]
    HELPER.require(path.is_file() and not path.is_symlink(), "regular driver required")
    spec = importlib.util.spec_from_file_location("drip_identity_" + mode, path)
    HELPER.require(spec is not None and spec.loader is not None, "driver loader missing")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def project(mode):
    HELPER.require(type(mode) is str and mode in MODES, "unsupported identity mode")
    # Bind the imported authority before loading the driver as well as in the
    # shared snapshot, so a driver edit during import cannot certify new bytes
    # using the old driver's constants.
    driver_hash = HELPER._digest(ROOT / MODES[mode])
    driver = load_driver(mode)
    entry = driver.EVALUATOR
    HELPER.require(entry == "scripts/eval-drip-" + mode + ".lean",
                   "driver evaluator differs from fixed mode")
    files = (*driver.SOURCE_FILES, MODES[mode], SELF)
    identity = HELPER.snapshot(ROOT, entry, files)
    HELPER.require(dict(identity)["source:" + MODES[mode]] == driver_hash,
                   "driver changed during identity preparation")
    result = json.dumps({"schema": 1, "kind": "drip-evaluator-identity",
                         "mode": mode, "evaluator": entry,
                         "identity": dict(identity)},
                        sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    HELPER.assert_unchanged(ROOT, entry, files, identity)
    return result


def main(argv):
    if len(argv) != 1 or argv[0] not in MODES:
        print("usage: drip-evaluator-identity.py arithmetic|receipts", file=sys.stderr)
        return 2
    try:
        output = project(argv[0])
    except (OSError, ValueError, KeyError, TypeError, AttributeError, ImportError) as exc:
        print(f"REGRESSION — DRIP evaluator identity: {exc}", file=sys.stderr)
        return 1
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
