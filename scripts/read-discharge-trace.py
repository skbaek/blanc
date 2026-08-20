#!/usr/bin/env python3
"""Read and aggregate Blanc.Forward discharge trace records.

Ordinary compiler output may surround trace records. Every line containing
the marker is parsed strictly; malformed marked lines are never dropped.
"""
from __future__ import annotations

import argparse
import statistics
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

SCHEMA = "BLANC_DISCHARGE_V1"
REQUIRED = ("kind", "outer", "subject", "out", "idx", "attempts", "elapsed_ns")
OUTCOMES = {"assigned", "exactLocal", "tactic", "residual"}
KINDS = {"gas", "room", "value"}


class TraceError(ValueError):
    pass


@dataclass(frozen=True)
class Record:
    kind: str
    outer: str
    subject: str
    outcome: str
    idx: str
    attempts: int
    elapsed_ns: int


def _decimal(value: str, field: str, line_no: int) -> int:
    if not value or not value.isascii() or not value.isdecimal():
        raise TraceError(f"record {line_no} field '{field}': expected a non-negative decimal")
    return int(value)


def parse_line(line: str, line_no: int) -> Record | None:
    if "BLANC_DISCHARGE_" not in line:
        return None
    payload = line[line.find("BLANC_DISCHARGE_"):].strip()
    fields = payload.split("|")
    schema = fields[0]
    if schema != SCHEMA:
        raise TraceError(f"record {line_no} schema: unknown schema '{schema}' (expected {SCHEMA})")
    values: dict[str, str] = {}
    for field in fields[1:]:
        if "=" not in field:
            raise TraceError(f"record {line_no} field '<record>': malformed field '{field}'")
        name, value = field.split("=", 1)
        if name not in REQUIRED:
            raise TraceError(f"record {line_no} field '{name}': unknown field")
        if name in values:
            raise TraceError(f"record {line_no} field '{name}': duplicate field")
        if not value or "|" in value or any(c.isspace() for c in value):
            raise TraceError(f"record {line_no} field '{name}': malformed value")
        values[name] = value
    for name in REQUIRED:
        if name not in values:
            raise TraceError(f"record {line_no} field '{name}': missing field")
    kind = values["kind"]
    if kind not in KINDS:
        raise TraceError(f"record {line_no} field 'kind': unknown value '{kind}'")
    outcome = values["out"]
    if outcome not in OUTCOMES:
        raise TraceError(f"record {line_no} field 'out': unknown value '{outcome}'")
    for name in ("outer", "subject"):
        if not values[name]:
            raise TraceError(f"record {line_no} field '{name}': empty value")
    idx = values["idx"]
    if idx != "na":
        _decimal(idx, "idx", line_no)
    return Record(kind, values["outer"], values["subject"], outcome, idx,
                  _decimal(values["attempts"], "attempts", line_no),
                  _decimal(values["elapsed_ns"], "elapsed_ns", line_no))


def read(stream) -> list[Record]:
    records: list[Record] = []
    for line_no, line in enumerate(stream, 1):
        record = parse_line(line.rstrip("\n"), line_no)
        if record is not None:
            records.append(record)
    return records


def render(records: list[Record]) -> str:
    groups: dict[tuple[str, str, str], list[Record]] = defaultdict(list)
    for record in records:
        groups[(record.kind, record.outer, record.subject)].append(record)
    lines = ["kind\touter\tsubject\tfrequency\ttotal_elapsed_ns\tmedian_elapsed_ns\toutcome_mix"]
    for (kind, outer, subject), rows in sorted(groups.items()):
        times = sorted(row.elapsed_ns for row in rows)
        median = statistics.median(times)
        median_text = str(int(median)) if median == int(median) else str(median)
        mix = ",".join(f"{name}={sum(row.outcome == name for row in rows)}"
                        for name in sorted(OUTCOMES))
        lines.append(f"{kind}\t{outer}\t{subject}\t{len(rows)}\t{sum(times)}\t{median_text}\t{mix}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", nargs="?", default="-", help="trace file, or - for stdin")
    args = parser.parse_args()
    try:
        if args.trace == "-":
            records = read(sys.stdin)
        else:
            with Path(args.trace).open(encoding="utf-8") as stream:
                records = read(stream)
        print(render(records))
        return 0
    except (OSError, UnicodeError, TraceError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
