#!/usr/bin/env python3
"""Controls for the fail-closed discharge trace reader."""
from __future__ import annotations

import importlib.util
import io
import sys
from pathlib import Path

path = Path(__file__).with_name("read-discharge-trace.py")
spec = importlib.util.spec_from_file_location("reader", path)
assert spec and spec.loader
reader = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = reader
spec.loader.exec_module(reader)

GOOD = "BLANC_DISCHARGE_V1|kind=gas|outer=Eq|subject=Devm.gasLeft|out=tactic|idx=0|attempts=1|elapsed_ns=9\n"
assert len(reader.read(io.StringIO("noise\n" + GOOD))) == 1
assert "frequency\ttotal_elapsed_ns\tmedian_elapsed_ns\toutcome_mix" in reader.render(reader.read(io.StringIO(GOOD)))

for label, bad in (
    ("unknown schema", GOOD.replace("V1", "V2")),
    ("missing field", GOOD.replace("|attempts=1", "")),
    ("malformed value", GOOD.replace("elapsed_ns=9", "elapsed_ns=nope")),
):
    try:
        reader.read(io.StringIO(bad))
    except reader.TraceError as exc:
        message = str(exc)
        if label == "unknown schema":
            assert "schema" in message
        else:
            assert "field '" in message
    else:
        raise AssertionError(f"{label} was accepted")
print("PASS — discharge reader controls (unknown schema, missing field, malformed value)")
