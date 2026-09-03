#!/usr/bin/env python3
"""Independent structural and executable checks for DRIP byte artifacts.

This checker reads the committed Lean literals without running Lean, verifies
the exact prefix/runtime split, and executes the constructor with a deliberately
small independent interpreter.  Only the constructor opcode vocabulary is
implemented; an unexpected opcode fails closed.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RUNTIME_SOURCE = ROOT / "Blanc" / "DripCode.lean"
CREATION_SOURCE = ROOT / "Blanc" / "DripCreationCode.lean"
PARSER_SOURCE = ROOT / "scripts" / "check-runtime-bytes.py"

WORD_MODULUS = 1 << 256
SCALE = 10**27
CHI_SLOT = WORD_MODULUS - 1
RHO_SLOT = WORD_MODULUS - 2
TOTAL_UNITS_SLOT = WORD_MODULUS - 3
RUNTIME_SIZE = 1917
PREFIX_SIZE = 239
CREATION_SIZE = 2156
INITCODE_LIMIT = 49152


class ArtifactError(Exception):
    """A committed artifact or constructor execution violated its contract."""


def literal_parser():
    spec = importlib.util.spec_from_file_location(
        "drip_runtime_literal_parser", PARSER_SOURCE
    )
    if spec is None or spec.loader is None:
        raise ArtifactError(f"cannot load literal parser {PARSER_SOURCE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_artifacts() -> tuple[bytes, bytes]:
    parser = literal_parser()
    try:
        runtime = parser.parse_lean_literal(RUNTIME_SOURCE, "code")
        creation = parser.parse_lean_literal(
            CREATION_SOURCE, "creationCodeLiteral"
        )
    except Exception as exc:  # parser exposes its own loud failure class
        raise ArtifactError(str(exc)) from exc
    return runtime, creation


@dataclass(frozen=True)
class ConstructorResult:
    status: str
    output: bytes
    storage: dict[int, int]
    writes: tuple[tuple[int, int], ...]
    executed: tuple[int, ...]


def execute_constructor(
    code: bytes, *, callvalue: int, timestamp: int
) -> ConstructorResult:
    if not 0 <= callvalue < WORD_MODULUS:
        raise ArtifactError("callvalue is not a word")
    if not 0 <= timestamp < WORD_MODULUS:
        raise ArtifactError("timestamp is not a word")

    stack: list[int] = []
    memory = bytearray()
    storage: dict[int, int] = {}
    writes: list[tuple[int, int]] = []
    executed: list[int] = []
    pc = 0

    def push(value: int) -> None:
        stack.append(value % WORD_MODULUS)

    def pop() -> int:
        if not stack:
            raise ArtifactError(f"constructor stack underflow at pc {pc}")
        return stack.pop()

    def ensure_memory(end: int) -> None:
        if end < 0 or end > 1 << 24:
            raise ArtifactError(f"unreasonable constructor memory bound {end}")
        if len(memory) < end:
            memory.extend(b"\x00" * (end - len(memory)))

    for _step in range(256):
        if pc >= PREFIX_SIZE or pc >= len(code):
            raise ArtifactError(
                f"constructor escaped its {PREFIX_SIZE}-byte prefix at pc {pc}"
            )
        here = pc
        op = code[pc]
        pc += 1
        executed.append(here)

        if op == 0x5B:  # JUMPDEST
            continue
        if op == 0x5F:  # PUSH0
            push(0)
            continue
        if 0x60 <= op <= 0x7F:  # PUSH1 ... PUSH32
            width = op - 0x5F
            if pc + width > len(code):
                raise ArtifactError(f"truncated PUSH{width} at pc {here}")
            push(int.from_bytes(code[pc : pc + width], "big"))
            pc += width
            continue
        if op == 0x14:  # EQ
            left, right = pop(), pop()
            push(1 if left == right else 0)
            continue
        if op == 0x15:  # ISZERO
            push(1 if pop() == 0 else 0)
            continue
        if op == 0x34:  # CALLVALUE
            push(callvalue)
            continue
        if op == 0x38:  # CODESIZE
            push(len(code))
            continue
        if op == 0x39:  # CODECOPY
            destination, source, size = pop(), pop(), pop()
            ensure_memory(destination + size)
            copied = code[source : source + size]
            copied += b"\x00" * (size - len(copied))
            memory[destination : destination + size] = copied
            continue
        if op == 0x42:  # TIMESTAMP
            push(timestamp)
            continue
        if op == 0x55:  # SSTORE
            key, value = pop(), pop()
            storage[key] = value
            writes.append((key, value))
            continue
        if op == 0x56:  # JUMP
            destination = pop()
            if destination >= len(code) or code[destination] != 0x5B:
                raise ArtifactError(f"invalid JUMP destination {destination}")
            pc = destination
            continue
        if op == 0x57:  # JUMPI
            destination, condition = pop(), pop()
            if condition:
                if destination >= len(code) or code[destination] != 0x5B:
                    raise ArtifactError(
                        f"invalid JUMPI destination {destination}"
                    )
                pc = destination
            continue
        if op in (0xF3, 0xFD):  # RETURN / REVERT
            offset, size = pop(), pop()
            ensure_memory(offset + size)
            output = bytes(memory[offset : offset + size])
            return ConstructorResult(
                "return" if op == 0xF3 else "revert",
                output,
                storage,
                tuple(writes),
                tuple(executed),
            )
        raise ArtifactError(f"unsupported constructor opcode 0x{op:02x} at pc {here}")

    raise ArtifactError("constructor exceeded the independent 256-step bound")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArtifactError(message)


def validate(runtime: bytes, creation: bytes) -> None:
    require(len(runtime) == RUNTIME_SIZE, "runtime length drift")
    require(len(creation) == CREATION_SIZE, "creation length drift")
    require(PREFIX_SIZE + RUNTIME_SIZE == CREATION_SIZE, "size partition drift")
    require(creation[PREFIX_SIZE:] == runtime, "creation runtime suffix drift")
    require(len(creation) <= INITCODE_LIMIT, "EIP-3860 limit exceeded")

    for timestamp in (0, 1, 1_767_747_671, (1 << 64) - 1):
        result = execute_constructor(creation, callvalue=0, timestamp=timestamp)
        require(result.status == "return", "valid constructor did not return")
        require(result.output == runtime, "constructor returned wrong runtime")
        require(
            result.writes == ((CHI_SLOT, SCALE), (RHO_SLOT, timestamp)),
            "constructor storage-write order/value drift",
        )
        require(
            result.storage == {CHI_SLOT: SCALE, RHO_SLOT: timestamp},
            "constructor wrote outside chi/rho",
        )
        require(TOTAL_UNITS_SLOT not in result.storage, "constructor wrote Pie")

    nonpayable = execute_constructor(creation, callvalue=1, timestamp=7)
    require(nonpayable.status == "revert", "nonzero-value constructor succeeded")
    require(not nonpayable.writes, "nonpayable failure wrote storage")
    require(nonpayable.output == b"", "nonpayable failure returned data")

    for malformed in (creation[:-1], creation + b"\x00"):
        rejected = execute_constructor(malformed, callvalue=0, timestamp=7)
        require(rejected.status == "revert", "nonexact creation length succeeded")
        require(not rejected.writes, "length rejection occurred after storage write")
        require(rejected.output == b"", "length rejection returned data")


def self_test(runtime: bytes, creation: bytes) -> int:
    prefix = creation[:PREFIX_SIZE]
    chi_push = b"\x7f" + CHI_SLOT.to_bytes(32, "big")
    cases: list[tuple[str, bytes, bytes]] = []

    baseline = execute_constructor(creation, callvalue=0, timestamp=7)

    def executed_opcode(opcode: int) -> int:
        matches = [pc for pc in baseline.executed if creation[pc] == opcode]
        require(
            len(matches) == 1,
            f"self-test expected one executed 0x{opcode:02x}, found {matches}",
        )
        return matches[0]

    changed_runtime = bytearray(runtime)
    changed_runtime[-1] ^= 1
    cases.append(("runtime-literal", bytes(changed_runtime), creation))

    changed_tail = bytearray(creation)
    changed_tail[-1] ^= 1
    cases.append(("creation-runtime-tail", runtime, bytes(changed_tail)))
    cases.append(("creation-length", runtime, creation + b"\x00"))

    callvalue_pc = executed_opcode(0x34)
    changed_guard = bytearray(creation)
    changed_guard[callvalue_pc] = 0x5F
    cases.append(("nonpayable-guard", runtime, bytes(changed_guard)))

    chi_pc = prefix.find(chi_push)
    require(chi_pc >= 0, "self-test cannot locate chi-slot PUSH32")
    changed_slot = bytearray(creation)
    changed_slot[chi_pc + 32] ^= 1
    cases.append(("chi-slot", runtime, bytes(changed_slot)))

    return_pc = executed_opcode(0xF3)
    changed_return = bytearray(creation)
    changed_return[return_pc] = 0xFD
    cases.append(("constructor-return", runtime, bytes(changed_return)))

    rejected = 0
    for name, candidate_runtime, candidate_creation in cases:
        try:
            validate(candidate_runtime, candidate_creation)
        except ArtifactError:
            rejected += 1
        else:
            raise ArtifactError(f"self-test mutation {name!r} was accepted")
    return rejected


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    try:
        runtime, creation = load_artifacts()
        validate(runtime, creation)
        if args.self_test:
            rejected = self_test(runtime, creation)
            print(f"OK — DRIP artifact self-test: {rejected}/6 corruptions rejected")
        else:
            print(
                "OK — DRIP artifacts: runtime=1917, prefix=239, creation=2156, "
                "EIP-3860 headroom=46996; constructor semantics exact"
            )
        return 0
    except ArtifactError as exc:
        print(f"REGRESSION — DRIP artifacts: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
