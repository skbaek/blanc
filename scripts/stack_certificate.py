#!/usr/bin/env python3
"""Untrusted producer for Lean-checked operand-stack certificate tables.

The producer accepts bytecode and an explicit maximum, computes a conservative
whole-stack fixpoint, and renders deterministic balanced table packs.  Its
output is data only: Blanc's unchanged ``checkTable`` validates every row
against the actual decoder before ``checkTable_certificate`` may consume it.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import Optional


PACK_ROWS = 15
WORD_LIMIT = 1 << 256
Pattern = tuple[Optional[int], ...]
BINARY = {0x01, 0x02, 0x03, 0x04, 0x10, 0x11, 0x14, 0x16, 0x1C}
UNARY = {0x15, 0x35, 0x51, 0x54}
UNKNOWN = {0x33, 0x34, 0x36, 0x42, 0x5A}
OTHER = {0x00, 0x50, 0x52, 0x55, 0x56, 0x57, 0x5B, 0xF1, 0xF3, 0xFD}


class Rejected(ValueError):
    """Malformed bytes or an unsupported/inconsistent abstract execution."""


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise Rejected(reason)


def check_output(path: Path, expected: str) -> None:
    require(path.is_file() and path.read_text(encoding="utf-8") == expected,
            f"stale/missing {path}")


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
        require(
            opcode in BINARY | UNARY | UNKNOWN | OTHER or 0x5F <= opcode <= 0x9F,
            f"unsupported opcode at {pc}: {opcode:#x}",
        )
        immediate = (
            int.from_bytes(raw[pc + 1 : pc + 1 + size], "big")
            if 0x5F <= opcode <= 0x7F
            else None
        )
        decoded[pc] = Instruction(pc, opcode, size + 1, immediate)
        pc += size + 1
    require(bool(decoded), "empty code")
    return decoded


def covers(actual: Pattern, expected: Pattern) -> bool:
    return len(actual) == len(expected) and all(
        wanted is None or wanted == word
        for word, wanted in zip(actual, expected)
    )


def transfer(
    decoded: dict[int, Instruction], pc: int, pattern: Pattern, maximum: int
) -> list[tuple[int, Pattern]]:
    require(0 <= maximum <= 8, "maximum must be between zero and eight")
    require(pc in decoded, f"unknown instruction boundary {pc}")
    require(len(pattern) <= maximum, f"input bound at {pc}")
    require(
        all(
            word is None
            or type(word) is int and 0 <= word < WORD_LIMIT
            for word in pattern
        ),
        f"invalid abstract literal at {pc}",
    )
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
        require(
            word in decoded and decoded[word].opcode == 0x5B,
            f"invalid jump destination {word} at {pc}",
        )
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
        return [edge(destination(pop(1)[0]))]
    elif opcode == 0x57:
        target = destination(pop(2)[0])
        return [edge(target), edge(pc + instruction.width)]
    elif opcode == 0xF1:
        pop(7)
        push(None)
    else:
        raise Rejected(f"unsupported transfer at {pc}")
    return [edge(pc + instruction.width)]


def validate(
    decoded: dict[int, Instruction], states: dict[int, Pattern], maximum: int
) -> None:
    require(states.get(0) == (), "entry must be PC zero and empty stack")
    require(set(states) <= set(decoded), "table contains a non-instruction row")
    for pc, pattern in states.items():
        for target, outgoing in transfer(decoded, pc, pattern, maximum):
            require(target in states, f"missing successor row {target}")
            require(
                covers(outgoing, states[target]),
                f"successor pattern at {target} from {pc}",
            )


def analyze(raw: bytes, maximum: int) -> dict[int, Pattern]:
    require(0 <= maximum <= 8, "maximum must be between zero and eight")
    decoded = decode(raw)
    states: dict[int, Pattern] = {0: ()}
    pending = deque([0])
    while pending:
        pc = pending.popleft()
        for target, outgoing in transfer(decoded, pc, states[pc], maximum):
            if target not in states:
                states[target] = outgoing
                pending.append(target)
                continue
            old = states[target]
            require(
                len(old) == len(outgoing),
                f"inconsistent join height at {target}",
            )
            joined = tuple(
                word if word == prior else None
                for word, prior in zip(outgoing, old)
            )
            if old != joined:
                states[target] = joined
                pending.append(target)
    ordered = dict(sorted(states.items()))
    validate(decoded, ordered, maximum)
    return ordered


@dataclass(frozen=True)
class Pack:
    """A named balanced piece, returned in dependency order."""

    rows: tuple[tuple[int, Pattern], ...]
    left: "Pack | None" = None
    right: "Pack | None" = None

    @property
    def root(self) -> tuple[int, Pattern]:
        return self.rows[len(self.rows) // 2]


def packs(states: dict[int, Pattern], pack_rows: int = PACK_ROWS) -> list[Pack]:
    require(pack_rows > 0, "pack_rows must be positive")
    rows = tuple(sorted(states.items()))
    require(bool(rows), "empty table")
    parts: list[Pack] = []

    def visit(entries: tuple[tuple[int, Pattern], ...]) -> Pack:
        if len(entries) <= pack_rows:
            part = Pack(entries)
        else:
            middle = len(entries) // 2
            part = Pack(
                entries,
                visit(entries[:middle]),
                visit(entries[middle + 1 :]),
            )
        parts.append(part)
        return part

    visit(rows)
    return parts


def render_module(
    raw: bytes,
    states: dict[int, Pattern],
    maximum: int,
    namespace: str,
    table_name: str,
    pack_prefix: str,
    source_label: str,
    regenerate_command: str,
) -> str:
    parts = packs(states)

    def pattern(words: Pattern) -> str:
        return "[" + ", ".join(
            "none" if word is None else f"some {word}" for word in words
        ) + "]"

    def name(part: Pack) -> str:
        return f"{pack_prefix}{part.root[0]}"

    def tree(entries: tuple[tuple[int, Pattern], ...], indent: int) -> list[str]:
        prefix = " " * indent
        if not entries:
            return [prefix + ".empty"]
        middle = len(entries) // 2
        pc, words = entries[middle]
        lines = [prefix + f"(.node {pc} {pattern(words)}"]
        lines.extend(tree(entries[:middle], indent + 2))
        lines.extend(tree(entries[middle + 1 :], indent + 2))
        lines[-1] += ")"
        return lines

    output = [
        "-- GENERATED FILE — do not edit by hand.",
        f"-- Regenerate: {regenerate_command}",
        f"-- Compiler bytes SHA-256: {hashlib.sha256(raw).hexdigest()}",
        f"-- {len(states)} reachable instructions across {len(raw)} bytes; maximum {maximum}.",
        f"-- Source: {source_label}.",
        "-- Untrusted data only: Lean checks it against the actual compiler result.",
        "",
        "import Blanc.AbstractStackCertificate",
        "",
        f"namespace {namespace}",
        "",
        "open AbstractStackSafety",
        "",
    ]
    for part in parts:
        first, last = part.rows[0][0], part.rows[-1][0]
        output.extend(
            [
                f"/-- Balanced pack: {len(part.rows)} rows, PCs {first} through {last}. -/",
                f"def {name(part)} : Table :=",
            ]
        )
        if part.left is None:
            output.extend(tree(part.rows, 2))
        else:
            pc, words = part.root
            output.append(
                f"  .node {pc} {pattern(words)} {name(part.left)} {name(part.right)}"
            )
        output.append("")
    output.extend(
        [
            "/-- Complete generated candidate. Every pack checks successors in this table. -/",
            f"def {table_name} : Table := {name(parts[-1])}",
            "",
        ]
    )
    without_entry = tuple(
        (pc, words) for pc, words in sorted(states.items()) if pc != 0
    )
    output.extend(
        [
            "/-- Negative-control data: the same rows with only entry row zero removed. -/",
            f"def {table_name}WithoutEntry : Table :=",
        ]
    )
    output.extend(tree(without_entry, 2))
    output.extend(["", f"end {namespace}", ""])
    return "\n".join(output)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bytes-hex", required=True)
    parser.add_argument("--maximum", required=True, type=int)
    parser.add_argument("--namespace", default="Generated.StackCertificate")
    parser.add_argument("--table-name", default="table")
    parser.add_argument("--pack-prefix", default="pack")
    parser.add_argument("--source-label", default="explicit CLI bytes")
    args = parser.parse_args()
    try:
        raw = bytes.fromhex(args.bytes_hex)
        states = analyze(raw, args.maximum)
        print(
            render_module(
                raw,
                states,
                args.maximum,
                args.namespace,
                args.table_name,
                args.pack_prefix,
                args.source_label,
                "python3 scripts/stack_certificate.py --bytes-hex HEX --maximum N",
            ),
            end="",
        )
        return 0
    except (ValueError, Rejected) as error:
        print(f"FAIL — stack certificate producer: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
