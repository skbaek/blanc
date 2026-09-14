#!/usr/bin/env python3
"""Identity-bound opcode/basic-block census for a TWG candidate and referent."""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
from pathlib import Path
from typing import Iterable


OPNAMES = {
    0x00: "STOP", 0x01: "ADD", 0x02: "MUL", 0x03: "SUB", 0x04: "DIV",
    0x06: "MOD", 0x10: "LT", 0x11: "GT", 0x14: "EQ", 0x15: "ISZERO",
    0x16: "AND", 0x17: "OR", 0x18: "XOR", 0x19: "NOT", 0x1B: "SHL",
    0x1C: "SHR", 0x20: "KECCAK256", 0x30: "ADDRESS", 0x31: "BALANCE",
    0x33: "CALLER", 0x34: "CALLVALUE", 0x35: "CALLDATALOAD",
    0x36: "CALLDATASIZE", 0x37: "CALLDATACOPY", 0x38: "CODESIZE",
    0x39: "CODECOPY", 0x3B: "EXTCODESIZE", 0x3D: "RETURNDATASIZE",
    0x3E: "RETURNDATACOPY", 0x3F: "EXTCODEHASH", 0x42: "TIMESTAMP",
    0x47: "SELFBALANCE", 0x50: "POP", 0x51: "MLOAD", 0x52: "MSTORE",
    0x53: "MSTORE8", 0x54: "SLOAD", 0x55: "SSTORE", 0x56: "JUMP",
    0x57: "JUMPI", 0x58: "PC", 0x59: "MSIZE", 0x5A: "GAS",
    0x5B: "JUMPDEST", 0x5F: "PUSH0", 0xF1: "CALL", 0xF3: "RETURN",
    0xFA: "STATICCALL", 0xFD: "REVERT", 0xFE: "INVALID",
    0xFF: "SELFDESTRUCT",
}

FOCUS = (
    "PUSH", "JUMP", "JUMPI", "JUMPDEST", "SLOAD", "SSTORE", "MLOAD",
    "MSTORE", "CALLDATALOAD", "CALLDATACOPY", "KECCAK256", "CALL",
    "STATICCALL", "RETURNDATASIZE", "RETURNDATACOPY", "RETURN", "REVERT",
    "LOG0", "LOG1", "LOG2", "LOG3", "LOG4",
)
TERMINATORS = {"STOP", "JUMP", "JUMPI", "RETURN", "REVERT", "INVALID",
               "SELFDESTRUCT"}


def disassemble(code: bytes) -> list[tuple[int, str, int]]:
    pc = 0
    rows = []
    while pc < len(code):
        opcode = code[pc]
        immediate = opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0
        width = 1 + immediate
        if pc + width > len(code):
            raise ValueError(f"truncated PUSH at byte {pc}")
        if immediate:
            name = f"PUSH{immediate}"
        elif 0x80 <= opcode <= 0x8F:
            name = f"DUP{opcode - 0x7F}"
        elif 0x90 <= opcode <= 0x9F:
            name = f"SWAP{opcode - 0x8F}"
        elif 0xA0 <= opcode <= 0xA4:
            name = f"LOG{opcode - 0xA0}"
        else:
            name = OPNAMES.get(opcode, f"OP_{opcode:02x}")
        rows.append((pc, name, width))
        pc += width
    return rows


def summarize(code: bytes) -> dict[str, object]:
    rows = disassemble(code)
    counts = collections.Counter(name for _, name, _ in rows)
    starts = {0}
    for index, (pc, name, _) in enumerate(rows):
        if name == "JUMPDEST":
            starts.add(pc)
        if name in TERMINATORS and index + 1 < len(rows):
            starts.add(rows[index + 1][0])
    push_names: Iterable[tuple[str, int]] = (
        (name, count) for name, count in counts.items() if name.startswith("PUSH")
    )
    push_instructions = sum(count for _, count in push_names)
    push_bytes = sum(width for _, name, width in rows if name.startswith("PUSH"))
    return {
        "sha256": hashlib.sha256(code).hexdigest(),
        "bytes": len(code),
        "instructions": len(rows),
        "basicBlocks": len(starts),
        "pushInstructions": push_instructions,
        "pushEncodedBytes": push_bytes,
        "opcodes": {
            name: (sum(value for key, value in counts.items()
                       if key.startswith("PUSH")) if name == "PUSH" else counts[name])
            for name in FOCUS
        },
        "topOpcodes": dict(counts.most_common(25)),
    }


def candidate_runtime(path: Path) -> bytes:
    for line in path.read_text().splitlines():
        parts = line.split()
        if parts and parts[0] == "primary-runtime":
            code = bytes.fromhex(parts[2])
            if len(code) != int(parts[1]):
                raise ValueError("primary-runtime length does not match evaluator output")
            return code
    raise ValueError("evaluator output has no primary-runtime row")


def reference_runtime(path: Path, world_name: str) -> bytes:
    lock = json.loads(path.read_text())
    worlds = lock["artifacts"]["worlds"]
    matches = [world for world in worlds if world["name"] == world_name]
    if len(matches) != 1:
        raise ValueError(f"expected one reference world named {world_name!r}")
    artifact = matches[0]["returnedRuntime"]
    code = bytes.fromhex(artifact["hex"].removeprefix("0x"))
    if len(code) != artifact["byteLength"]:
        raise ValueError("reference runtime length does not match its lock")
    if hashlib.sha256(code).hexdigest() != artifact["sha256"]:
        raise ValueError("reference runtime SHA-256 does not match its lock")
    return code


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifacts", required=True, type=Path,
                        help="output of scripts/eval-lido-twg-artifacts.lean")
    parser.add_argument("--reference-lock", type=Path,
                        default=Path(__file__).with_name("lido-twg-reference.json"))
    parser.add_argument("--reference-world", default="differential-corpus")
    args = parser.parse_args()
    result = {
        "candidate": summarize(candidate_runtime(args.artifacts)),
        "reference": summarize(reference_runtime(args.reference_lock,
                                                 args.reference_world)),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (KeyError, OSError, TypeError, ValueError) as exc:
        print(f"REGRESSION — Lido TWG opcode census: {exc}")
        raise SystemExit(1)
