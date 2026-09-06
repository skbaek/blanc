#!/usr/bin/env python3
"""Generate data for the Lean-checked DRIP operand-stack certificate.

Default mode compares without writing. Only --write replaces the generated
Lean data owner. Analysis is conservative (both JUMPI arms, exact full-stack
joins); its result supplies no trusted Lean premise. The shared Lean checker
independently reads the actual bytecode decoder and checks every table row.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
from typing import Optional


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Blanc/DripCode.lean"
OUTPUT = ROOT / "Blanc/DripStackSafetyData.lean"
MAXIMUM = 8
WORD_LIMIT = 1 << 256
Pattern = tuple[Optional[int], ...]
BINARY = {0x01, 0x02, 0x03, 0x04, 0x10, 0x11, 0x14, 0x16, 0x1C}
UNARY = {0x15, 0x35, 0x51, 0x54}
UNKNOWN = {0x33, 0x34, 0x36, 0x42, 0x5A}
OTHER = {0x00, 0x50, 0x52, 0x55, 0x56, 0x57, 0x5B, 0xF1, 0xF3, 0xFD}


class Rejected(ValueError):
    """A malformed source or unsupported/inconsistent abstract execution."""


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise Rejected(reason)


def runtime_bytes(source: str) -> bytes:
    matches = list(re.finditer(r"\bdef code\s*:\s*Bytes\s*:=\s*\[(.*?)\]", source, re.S))
    require(len(matches) == 1, "expected exactly one DRIP runtime literal")
    body = matches[0].group(1)
    require(re.fullmatch(r"\s*(?:0x[0-9a-fA-F]{2}\s*,\s*)*0x[0-9a-fA-F]{2}\s*,?\s*", body)
            is not None, "runtime must be a nonempty exact byte list")
    return bytes(int(word, 16) for word in re.findall(r"0x[0-9a-fA-F]{2}", body))


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    width: int
    immediate: int | None


def decode(raw: bytes) -> dict[int, Instruction]:
    decoded: dict[int, Instruction] = {}
    pc = 0
    while pc < len(raw):
        opcode = raw[pc]
        size = opcode - 95 if 0x60 <= opcode <= 0x7F else 0
        require(pc + size < len(raw), f"truncated PUSH at {pc}")
        require(opcode in BINARY | UNARY | UNKNOWN | OTHER or 0x5F <= opcode <= 0x9F,
                f"unsupported opcode at {pc}: {opcode:#x}")
        immediate = int.from_bytes(raw[pc + 1:pc + 1 + size], "big") if 0x5F <= opcode <= 0x7F else None
        decoded[pc] = Instruction(pc, opcode, size + 1, immediate)
        pc += size + 1
    require(bool(decoded), "empty code")
    return decoded


def covers(actual: Pattern, expected: Pattern) -> bool:
    return len(actual) == len(expected) and all(
        wanted is None or wanted == word for word, wanted in zip(actual, expected))


def transfer(decoded: dict[int, Instruction], pc: int, pattern: Pattern,
             maximum: int = MAXIMUM) -> list[tuple[int, Pattern]]:
    require(pc in decoded, f"unknown instruction boundary {pc}")
    require(len(pattern) <= maximum, f"input bound at {pc}")
    require(all(word is None or type(word) is int and 0 <= word < WORD_LIMIT for word in pattern),
            f"invalid abstract literal at {pc}")
    instruction = decoded[pc]
    opcode = instruction.opcode
    stack = list(pattern)

    def pop(count: int) -> list[int | None]:
        require(len(stack) >= count, f"operand underflow at {pc}")
        words = stack[:count]
        del stack[:count]
        return words

    def push(word: int | None) -> None:
        stack.insert(0, word)

    def edge(target: int) -> tuple[int, Pattern]:
        require(target in decoded, f"unknown successor boundary {target} from {pc}")
        require(len(stack) <= maximum, f"outgoing bound at {pc}")
        return target, tuple(stack)

    def destination(word: int | None) -> int:
        require(word is not None, f"unknown jump destination at {pc}")
        require(word in decoded and decoded[word].opcode == 0x5B,
                f"invalid jump destination {word} at {pc}")
        return word

    if 0x5F <= opcode <= 0x7F:
        push(instruction.immediate)
    elif 0x80 <= opcode <= 0x8F:
        index = opcode - 0x80
        require(index < len(stack), f"DUP underflow at {pc}")
        push(stack[index])
    elif 0x90 <= opcode <= 0x9F:
        index = opcode - 0x8F
        require(index < len(stack), f"SWAP underflow at {pc}")
        stack[0], stack[index] = stack[index], stack[0]
    elif opcode in BINARY:
        pop(2)
        push(None)
    elif opcode in UNARY:
        pop(1)
        push(None)
    elif opcode in UNKNOWN:
        push(None)
    elif opcode == 0x50:
        pop(1)
    elif opcode in {0x52, 0x55}:
        pop(2)
    elif opcode == 0x5B:
        pass
    elif opcode in {0x00, 0xF3, 0xFD}:
        if opcode != 0:
            pop(2)
        return []
    elif opcode == 0x56:
        target = destination(pop(1)[0])
        return [edge(target)]
    elif opcode == 0x57:
        target = destination(pop(2)[0])
        # Never prune either branch, even for a literal condition.
        return [edge(target), edge(pc + instruction.width)]
    elif opcode == 0xF1:
        pop(7)
        push(None)  # immediate failure or every ordinary child settlement
    else:
        raise Rejected(f"unsupported transfer at {pc}")
    return [edge(pc + instruction.width)]


def validate(decoded: dict[int, Instruction], states: dict[int, Pattern]) -> None:
    require(states.get(0) == (), "entry must be PC zero and empty stack")
    require(set(states) == set(decoded), "table must cover exactly all decoded instructions")
    for pc, pattern in states.items():
        for target, outgoing in transfer(decoded, pc, pattern):
            require(target in states, f"missing successor row {target}")
            require(len(states[target]) <= MAXIMUM, f"successor bound at {target}")
            require(covers(outgoing, states[target]), f"successor pattern at {target} from {pc}")


def analyze(raw: bytes) -> dict[int, Pattern]:
    decoded = decode(raw)
    states: dict[int, Pattern] = {0: ()}
    pending = deque([0])
    while pending:
        pc = pending.popleft()
        for target, outgoing in transfer(decoded, pc, states[pc]):
            if target not in states:
                states[target] = outgoing
                pending.append(target)
                continue
            old = states[target]
            require(len(old) == len(outgoing), f"inconsistent join height at {target}")
            joined = tuple(word if word == prior else None for word, prior in zip(outgoing, old))
            if old != joined:
                states[target] = joined
                pending.append(target)
    validate(decoded, states)
    return dict(sorted(states.items()))


def render(raw: bytes, states: dict[int, Pattern]) -> str:
    rows = list(states.items())

    def tree(entries: list[tuple[int, Pattern]], indent: int) -> list[str]:
        prefix = " " * indent
        if not entries:
            return [prefix + ".empty"]
        middle = len(entries) // 2
        pc, words = entries[middle]
        pattern = "[" + ", ".join("none" if word is None else f"some {word}" for word in words) + "]"
        lines = [prefix + f"(.node {pc} {pattern}"]
        lines.extend(tree(entries[:middle], indent + 2))
        lines.extend(tree(entries[middle + 1:], indent + 2))
        lines[-1] += ")"
        return lines

    header = [
        "-- GENERATED FILE — do not edit by hand.",
        "-- Regenerate: python3 scripts/gen-drip-stack-certificate.py --write",
        f"-- Runtime SHA-256: {hashlib.sha256(raw).hexdigest()}",
        f"-- {len(rows)} decoded instructions across {len(raw)} bytes; abstract maximum {MAXIMUM}.",
        "-- Data only: semantic validity is checked against actual Drip.code in Lean.",
        "", "import Blanc.AbstractStackCertificate", "", "namespace Blanc.Drip.StackSafety",
        "", "open AbstractStackSafety", "",
        "/-- Conservative whole-stack patterns, including both conditional arms. -/",
        "def table : Table :=",
    ]
    return "\n".join(header + tree(rows, 2) + ["", "end Blanc.Drip.StackSafety", ""])


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
