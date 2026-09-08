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
REGION576_OUTPUT = ROOT / "Blanc/DripStackSafetyRegion576.lean"
REGION1022_OUTPUT = ROOT / "Blanc/DripStackSafetyRegion1022.lean"
REGION1459_OUTPUT = ROOT / "Blanc/DripStackSafetyRegion1459.lean"
CERTIFICATE_OUTPUT = ROOT / "Blanc/DripStackSafetyCertificate.lean"
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


@dataclass(frozen=True)
class RowWitness:
    name: str
    pc: int
    external_successor: int
    comment: str
    local_root: str | None = None


@dataclass(frozen=True)
class RegionSpec:
    root: str
    rows: int
    start: int
    stop: int
    module_doc: tuple[str, ...]
    internal_theorem_prefix: str = ""
    witnesses: tuple[RowWitness, ...] = ()


REGION576 = RegionSpec(
    root="subtree576",
    rows=183,
    start=372,
    stop=839,
    module_doc=(
        "Checked second 183-row region of the DRIP stack table. Every successor check",
        "uses the complete 735-row table, including the conditional jump from PC 686",
        "to PC 947 outside this region.",
    ),
    witnesses=(RowWitness(
        name="row686_cross_region_checked",
        pc=686,
        external_successor=947,
        comment="PC 686 lies in subtree716; its taken successor PC 947 is outside subtree576.",
    ),),
)

REGION1022 = RegionSpec(
    root="subtree1022",
    rows=183,
    start=840,
    stop=1182,
    module_doc=(
        "Checked third 183-row region of the DRIP stack table. Every successor check",
        "uses the complete 735-row table, including the conditional jump from PC 1165",
        "to PC 1212 outside this region.",
    ),
    internal_theorem_prefix="region1022_",
    witnesses=(RowWitness(
        name="row1165_cross_region_checked",
        pc=1165,
        external_successor=1212,
        comment="PC 1165 lies in subtree1022; its taken successor PC 1212 is outside subtree1022.",
    ),),
)

REGION1459 = RegionSpec(
    root="subtree1459",
    rows=183,
    start=1199,
    stop=1762,
    module_doc=(
        "Checked fourth 183-row region of the DRIP stack table. Every successor check",
        "uses the complete 735-row table, including the conditional jump from PC 1227",
        "in subtree1221 to PC 1735 in subtree1730.",
    ),
    internal_theorem_prefix="region1459_",
    witnesses=(RowWitness(
        name="row1227_cross_pack_checked",
        pc=1227,
        external_successor=1735,
        comment="PC 1227 lies in subtree1221; its taken successor PC 1735 lies in subtree1730.",
        local_root="subtree1221",
    ),),
)

PROOF_OUTPUTS = {
    REGION576: REGION576_OUTPUT,
    REGION1022: REGION1022_OUTPUT,
    REGION1459: REGION1459_OUTPUT,
}


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


def pattern(words: Pattern) -> str:
    return "[" + ", ".join("none" if word is None else f"some {word}" for word in words) + "]"


def region_parts(parts: list[Subtree], root: str) -> list[Subtree]:
    by_name = {part.name: part for part in parts}
    require(root in by_name, f"unknown proof region {root}")
    ordered: list[Subtree] = []

    def visit(part: Subtree) -> None:
        if part.left is not None:
            require(part.right is not None, f"one-sided subtree {part.name}")
            visit(part.left)
            visit(part.right)
        else:
            require(part.right is None, f"one-sided subtree {part.name}")
        ordered.append(part)

    visit(by_name[root])
    require(len({part.name for part in ordered}) == len(ordered),
            f"duplicate dependency in proof region {root}")
    return ordered


def render_proof_region(raw: bytes, states: dict[int, Pattern], spec: RegionSpec) -> str:
    decoded = decode(raw)
    parts = region_parts(subtrees(states), spec.root)
    root = parts[-1]
    require(len(root.rows) == spec.rows, f"wrong row count for {spec.root}")
    require(root.rows[0][0] == spec.start, f"wrong start for {spec.root}")
    last_pc = root.rows[-1][0]
    require(last_pc in decoded, f"missing final instruction for {spec.root}")
    require(last_pc + decoded[last_pc].width == spec.stop, f"wrong stop for {spec.root}")
    region_pcs = {pc for pc, _ in root.rows}
    by_name = {part.name: part for part in subtrees(states)}

    def theorem_stem(part: Subtree) -> str:
        if part is root:
            return part.name
        return f"{spec.internal_theorem_prefix}{part.name}"

    output = ["import Blanc.DripStackSafety", "", "/-!", *spec.module_doc, "-/", "",
              "namespace Blanc.Drip.StackSafety", "", "open Jaune AbstractStackSafety", ""]
    for part in parts:
        stem = theorem_stem(part)
        start = part.rows[0][0]
        final_pc = part.rows[-1][0]
        require(final_pc in decoded, f"missing final instruction for {part.name}")
        stop = final_pc + decoded[final_pc].width
        output.extend([
            f"theorem {stem}_rows_checked :",
            f"    {part.name}.all (checkRow code.toByteArray table {MAXIMUM}) = true := by",
        ])
        if part.left is None:
            output.append("  decide +kernel")
        else:
            require(part.right is not None, f"one-sided subtree {part.name}")
            output.extend([
                "  apply Table.all_node",
                "  · decide +kernel",
                f"  · exact {theorem_stem(part.left)}_rows_checked",
                f"  · exact {theorem_stem(part.right)}_rows_checked",
            ])
        output.extend(["", f"theorem {stem}_layout_checked :",
                       f"    {part.name}.checkLayout code.toByteArray {start} {stop} = true := by"])
        if part.left is None:
            output.append("  decide +kernel")
        else:
            next_pc = part.right.rows[0][0]
            output.extend([
                f"  apply Table.checkLayout_node (next := {next_pc})",
                "  · decide +kernel",
                f"  · exact {theorem_stem(part.left)}_layout_checked",
                f"  · exact {theorem_stem(part.right)}_layout_checked",
                "  · decide +kernel",
            ])
        output.append("")

    for witness in spec.witnesses:
        require(witness.pc in region_pcs, f"witness PC outside {spec.root}")
        successors = transfer(decoded, witness.pc, states[witness.pc])
        require(any(pc == witness.external_successor for pc, _ in successors),
                f"missing witness successor {witness.external_successor} from {witness.pc}")
        local_root = spec.root if witness.local_root is None else witness.local_root
        require(local_root in by_name, f"unknown witness boundary {local_root}")
        local_pcs = {pc for pc, _ in by_name[local_root].rows}
        require(witness.pc in local_pcs, f"witness PC outside {local_root}")
        require(witness.external_successor not in local_pcs,
                f"witness successor is local to {local_root}")
        output.extend([
            f"/-- {witness.comment} -/",
            f"theorem {witness.name} :",
            f"    checkRow code.toByteArray table {MAXIMUM} {witness.pc} {pattern(states[witness.pc])} = true := by",
            "  decide +kernel",
            "",
        ])

    output.extend([
        "/-- Strict ordering and the exact region population are checked independently. -/",
        f"theorem {spec.root}_order_and_size_checked :",
        f"    {spec.root}.checkOrder = true ∧ {spec.root}.size = {spec.rows} := by",
        "  decide +kernel",
        "",
        "end Blanc.Drip.StackSafety",
        "",
    ])
    return "\n".join(output)


def render_certificate_facade(raw: bytes, states: dict[int, Pattern]) -> str:
    decoded = decode(raw)
    by_name = {part.name: part for part in subtrees(states)}
    expected = {
        "subtree214": (183, 0, 371),
        "subtree576": (183, 372, 839),
        "subtree1022": (183, 840, 1182),
        "subtree1459": (183, 1199, 1762),
        "subtree371": (367, 0, 839),
        "subtree1182": (367, 840, 1762),
        "subtree839": (735, 0, 1762),
    }
    for name, (rows, start, stop) in expected.items():
        require(name in by_name, f"missing facade subtree {name}")
        part = by_name[name]
        require(len(part.rows) == rows, f"wrong facade row count for {name}")
        require(part.rows[0][0] == start, f"wrong facade start for {name}")
        final_pc = part.rows[-1][0]
        require(final_pc + decoded[final_pc].width == stop,
                f"wrong facade stop for {name}")
    require(states.get(0) == (), "facade entry must be PC zero and empty stack")

    return "\n".join([
        "import Blanc.DripStackSafetyRegion214",
        "import Blanc.DripStackSafetyRegion576",
        "import Blanc.DripStackSafetyRegion1022",
        "import Blanc.DripStackSafetyRegion1459",
        "",
        "/-!",
        "Complete 735-row DRIP stack certificate and its actual same-frame entry theorem.",
        "The conclusion follows only along an actual `Exec.Deriv.ParentPrefix`; entered child",
        "frames require their own certificate before their parent continuation resumes.",
        "-/",
        "",
        "namespace Blanc.Drip.StackSafety",
        "",
        "open Jaune AbstractStackSafety CompiledStackSafety",
        "",
        "theorem subtree371_rows_checked :",
        "    subtree371.all (checkRow code.toByteArray table 8) = true := by",
        "  apply Table.all_node",
        "  · decide +kernel",
        "  · exact subtree214_rows_checked",
        "  · exact subtree576_rows_checked",
        "",
        "theorem subtree371_layout_checked :",
        "    subtree371.checkLayout code.toByteArray 0 839 = true := by",
        "  apply Table.checkLayout_node (next := 372)",
        "  · decide +kernel",
        "  · exact subtree214_layout_checked",
        "  · exact subtree576_layout_checked",
        "  · decide +kernel",
        "",
        "theorem subtree1182_rows_checked :",
        "    subtree1182.all (checkRow code.toByteArray table 8) = true := by",
        "  apply Table.all_node",
        "  · decide +kernel",
        "  · exact subtree1022_rows_checked",
        "  · exact subtree1459_rows_checked",
        "",
        "theorem subtree1182_layout_checked :",
        "    subtree1182.checkLayout code.toByteArray 840 1762 = true := by",
        "  apply Table.checkLayout_node (next := 1199)",
        "  · decide +kernel",
        "  · exact subtree1022_layout_checked",
        "  · exact subtree1459_layout_checked",
        "  · decide +kernel",
        "",
        "theorem subtree839_rows_checked :",
        "    subtree839.all (checkRow code.toByteArray table 8) = true := by",
        "  apply Table.all_node",
        "  · decide +kernel",
        "  · exact subtree371_rows_checked",
        "  · exact subtree1182_rows_checked",
        "",
        "theorem subtree839_layout_checked :",
        "    subtree839.checkLayout code.toByteArray 0 1762 = true := by",
        "  apply Table.checkLayout_node (next := 840)",
        "  · decide +kernel",
        "  · exact subtree371_layout_checked",
        "  · exact subtree1182_layout_checked",
        "  · decide +kernel",
        "",
        "theorem table_rows_checked :",
        "    table.all (checkRow code.toByteArray table 8) = true := by",
        "  exact subtree839_rows_checked",
        "",
        "theorem table_layout_checked :",
        "    table.checkLayout code.toByteArray 0 1762 = true := by",
        "  exact subtree839_layout_checked",
        "",
        "/-- Strict ordering and the exact whole-table population are checked independently. -/",
        "theorem table_order_and_size_checked :",
        "    table.checkOrder = true ∧ table.size = 735 := by",
        "  decide +kernel",
        "",
        "/-- The actual runtime, complete ordered table, and all 735 transfer rows agree. -/",
        "theorem table_checked : checkTable code.toByteArray table 8 = true := by",
        "  unfold checkTable",
        "  rw [show decide (8 ≤ 8) = true by decide]",
        "  rw [table_order_and_size_checked.1, table_rows_checked]",
        "  rfl",
        "",
        "/-- The exact runtime entry row is PC zero with the complete empty operand stack. -/",
        "theorem entry_invariant (pre : Devm) (entryStack : pre.stack = []) :",
        "    table.Invariant 0 pre := by",
        "  refine ⟨[], ?_, ?_⟩",
        "  · decide +kernel",
        "  · rw [entryStack]",
        "    exact matches_nil",
        "",
        "/-- Every node on an actual same-frame path from the concrete DRIP entry is locally",
        "stack-safe and remains within the certified eight-word bound. -/",
        "theorem actual_entry_safe {root node : Exec.Deriv}",
        "    (hprefix : Exec.Deriv.ParentPrefix root node)",
        "    (codeFrame : root.sevm.code = code.toByteArray)",
        "    (entryPc : root.pc = 0)",
        "    (entryStack : root.devm.stack = []) :",
        "    node.devm.stack.length ≤ 8 ∧",
        "      CompiledStackSafety.StepSafe table.Invariant",
        "        (Evm.step ⟨node.pc, node.sevm, node.devm⟩) := by",
        "  have checked : checkTable root.sevm.code table 8 = true := by",
        "    rw [codeFrame]",
        "    exact table_checked",
        "  apply (checkTable_certificate checked).at_parentPrefix hprefix rfl",
        "  rw [entryPc]",
        "  exact entry_invariant root.devm entryStack",
        "",
        "end Blanc.Drip.StackSafety",
        "",
    ])


def render(raw: bytes, states: dict[int, Pattern]) -> str:
    parts = subtrees(states)

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


def expected_proof_outputs(source: Path = SOURCE) -> dict[Path, str]:
    raw = runtime_bytes(source.read_text())
    states = analyze(raw)
    outputs = {path: render_proof_region(raw, states, spec) for spec, path in PROOF_OUTPUTS.items()}
    outputs[CERTIFICATE_OUTPUT] = render_certificate_facade(raw, states)
    return outputs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    writes = parser.add_mutually_exclusive_group()
    writes.add_argument("--write", action="store_true", help="replace the generated Lean data owner")
    writes.add_argument("--write-proofs", action="store_true",
                        help="replace the fixed generated Lean proof-module set")
    args = parser.parse_args()
    try:
        expected = expected_output()
        if args.write:
            OUTPUT.write_text(expected)
            print("OK — wrote Blanc/DripStackSafetyData.lean")
        elif args.write_proofs:
            proofs = expected_proof_outputs()
            require(REGION576_OUTPUT.is_file() and REGION576_OUTPUT.read_text() == proofs[REGION576_OUTPUT],
                    "renderer does not reproduce accepted Blanc/DripStackSafetyRegion576.lean")
            for path, proof in proofs.items():
                path.write_text(proof)
            print("OK — wrote fixed DRIP stack proof modules: Region576, Region1022, Region1459 and Certificate")
        else:
            require(OUTPUT.is_file() and OUTPUT.read_text() == expected,
                    "stale/missing Blanc/DripStackSafetyData.lean; run the registered writer --write")
            for path, proof in expected_proof_outputs().items():
                require(path.is_file() and path.read_text() == proof,
                        f"stale/missing {path.relative_to(ROOT)}; run the registered writer --write-proofs")
            print("OK — DRIP stack table data and proof text exactly match current runtime analysis")
        return 0
    except (OSError, Rejected) as error:
        print(f"FAIL — DRIP stack table: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
