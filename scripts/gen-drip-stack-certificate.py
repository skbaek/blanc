#!/usr/bin/env python3
"""Generate data for the Lean-checked DRIP operand-stack certificate.

Default mode compares without writing. Only --write replaces the generated
Lean data owner. Analysis is conservative (both JUMPI arms, exact full-stack
joins); its result supplies no trusted Lean premise. The shared Lean checker
independently reads the actual bytecode decoder and checks every table row.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re

import stack_certificate as producer


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Blanc/DripCode.lean"
OUTPUT = ROOT / "Blanc/DripStackSafetyData.lean"
MAXIMUM = 8
# A representation boundary, not a bound on program/table size or proof resources.
SUBTREE_ROWS = 15
Pattern = producer.Pattern
Instruction = producer.Instruction
Rejected = producer.Rejected
require = producer.require


def runtime_bytes(source: str) -> bytes:
    matches = list(re.finditer(r"\bdef code\s*:\s*Bytes\s*:=\s*\[(.*?)\]", source, re.S))
    require(len(matches) == 1, "expected exactly one DRIP runtime literal")
    body = matches[0].group(1)
    require(re.fullmatch(r"\s*(?:0x[0-9a-fA-F]{2}\s*,\s*)*0x[0-9a-fA-F]{2}\s*,?\s*", body)
            is not None, "runtime must be a nonempty exact byte list")
    return bytes(int(word, 16) for word in re.findall(r"0x[0-9a-fA-F]{2}", body))


def decode(raw: bytes) -> dict[int, Instruction]:
    return producer.decode(raw)


def covers(actual: Pattern, expected: Pattern) -> bool:
    return producer.covers(actual, expected)


def transfer(decoded: dict[int, Instruction], pc: int, pattern: Pattern,
             maximum: int = MAXIMUM) -> list[tuple[int, Pattern]]:
    return producer.transfer(decoded, pc, pattern, maximum)


def validate(decoded: dict[int, Instruction], states: dict[int, Pattern]) -> None:
    require(states.get(0) == (), "entry must be PC zero and empty stack")
    require(set(states) == set(decoded), "table must cover exactly all decoded instructions")
    producer.validate(decoded, states, MAXIMUM)


def analyze(raw: bytes) -> dict[int, Pattern]:
    decoded = producer.decode(raw)
    states = producer.analyze(raw, MAXIMUM)
    validate(decoded, states)
    return dict(sorted(states.items()))


@dataclass(frozen=True)
class Subtree:
    """A named piece of the original balanced tree, in dependency order."""

    rows: tuple[tuple[int, Pattern], ...]
    left: Subtree | None = None
    right: Subtree | None = None

    @property
    def root(self) -> tuple[int, Pattern]:
        return self.rows[len(self.rows) // 2]

    @property
    def name(self) -> str:
        return f"subtree{self.root[0]}"


def subtrees(states: dict[int, Pattern]) -> list[Subtree]:
    """Name small leaves and every composing node without changing any row."""
    parts: list[Subtree] = []
    converted: dict[int, Subtree] = {}
    for packed in producer.packs(states, SUBTREE_ROWS):
        part = Subtree(
            packed.rows,
            None if packed.left is None else converted[packed.left.root[0]],
            None if packed.right is None else converted[packed.right.root[0]],
        )
        parts.append(part)
        converted[part.root[0]] = part
    return parts


def render(raw: bytes, states: dict[int, Pattern]) -> str:
    parts = subtrees(states)

    def pattern(words: Pattern) -> str:
        return "[" + ", ".join("none" if word is None else f"some {word}" for word in words) + "]"

    def tree(entries: tuple[tuple[int, Pattern], ...], indent: int) -> list[str]:
        prefix = " " * indent
        if not entries:
            return [prefix + ".empty"]
        middle = len(entries) // 2
        pc, words = entries[middle]
        lines = [prefix + f"(.node {pc} {pattern(words)}"]
        lines.extend(tree(entries[:middle], indent + 2))
        lines.extend(tree(entries[middle + 1:], indent + 2))
        lines[-1] += ")"
        return lines

    header = [
        "-- GENERATED FILE — do not edit by hand.",
        "-- Regenerate: python3 scripts/gen-drip-stack-certificate.py --write",
        f"-- Runtime SHA-256: {hashlib.sha256(raw).hexdigest()}",
        f"-- {len(states)} decoded instructions across {len(raw)} bytes; abstract maximum {MAXIMUM}.",
        "-- Data only: semantic validity is checked against actual Drip.code in Lean.",
        "", "import Blanc.AbstractStackCertificate", "", "namespace Blanc.Drip.StackSafety",
        "", "open AbstractStackSafety", "",
    ]
    for part in parts:
        first, last = part.rows[0][0], part.rows[-1][0]
        header.extend([f"/-- Exact balanced subtree: {len(part.rows)} rows, PCs {first} through {last}. -/",
                       f"def {part.name} : Table :="])
        if part.left is None:
            header.extend(tree(part.rows, 2))
        else:
            pc, words = part.root
            header.append(f"  .node {pc} {pattern(words)} {part.left.name} {part.right.name}")
        header.append("")
    header.extend(["/-- Conservative whole-stack patterns, including both conditional arms.",
                   "Every successor check uses this complete table across named subtrees. -/",
                   "def table : Table := " + parts[-1].name])
    return "\n".join(header + ["", "end Blanc.Drip.StackSafety", ""])


def expected_output(source: Path = SOURCE) -> str:
    raw = runtime_bytes(source.read_text())
    return render(raw, analyze(raw))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="replace the generated Lean data owner")
    args = parser.parse_args()
    try:
        expected = expected_output()
        if args.write:
            OUTPUT.write_text(expected)
            print("OK — wrote Blanc/DripStackSafetyData.lean")
        else:
            require(OUTPUT.is_file() and OUTPUT.read_text() == expected,
                    "stale/missing Blanc/DripStackSafetyData.lean; run the registered writer --write")
            print("OK — DRIP stack table data exactly matches current runtime analysis")
        return 0
    except (OSError, Rejected) as error:
        print(f"FAIL — DRIP stack table: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
