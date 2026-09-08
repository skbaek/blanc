#!/usr/bin/env python3
"""Deterministic, non-elaborating generator controls using disposable inputs."""

import importlib.util
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("drip_stack_generator", ROOT / "scripts/gen-drip-stack-certificate.py")
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class StackCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = GEN.SOURCE.read_text()
        cls.raw = GEN.runtime_bytes(cls.source)
        cls.decoded = GEN.decode(cls.raw)
        cls.states = GEN.analyze(cls.raw)
        cls.rendered = GEN.render(cls.raw, cls.states)
        cls.parts = GEN.subtrees(cls.states)
        cls.proofs = GEN.expected_proof_outputs()

    def restore(self):
        self.assertEqual(GEN.analyze(self.raw), self.states)
        GEN.validate(self.decoded, self.states)

    def test_current_whole_stack_candidate(self):
        self.assertEqual(len(self.raw), 1762)
        self.assertEqual(len(self.states), 735)
        self.assertEqual(self.states[0], ())
        self.assertEqual([pc for pc, words in self.states.items() if len(words) == 8], [1720])
        self.assertEqual(self.states[1720], (None, None, None, 0, 0, 0, 0, None))
        self.assertEqual(GEN.transfer(self.decoded, 1720, self.states[1720]), [(1721, (None, None))])
        self.assertEqual(GEN.transfer(self.decoded, 1140, self.states[1140]), [(951, self.states[951])])

    def test_producer_adapter_preserves_stronger_drip_contract(self):
        self.assertIs(GEN.Instruction, GEN.producer.Instruction)
        self.assertEqual(self.states, GEN.producer.analyze(self.raw, GEN.MAXIMUM))
        self.assertEqual(
            [part.root for part in GEN.subtrees(self.states)],
            [part.root for part in GEN.producer.packs(self.states, GEN.SUBTREE_ROWS)],
        )
        decoded = GEN.decode(bytes([0x00, 0x00]))
        reachable = GEN.producer.analyze(bytes([0x00, 0x00]), GEN.MAXIMUM)
        with self.assertRaisesRegex(GEN.Rejected, "exactly all decoded"):
            GEN.validate(decoded, reachable)

    def test_both_conditional_arms(self):
        decoded = GEN.decode(bytes([0x57, 0x00, 0x5B, 0x00]))
        for condition in (None, 0, 1):
            self.assertEqual(GEN.transfer(decoded, 0, (2, condition)), [(2, ()), (1, ())])

    def test_full_stack_subsumption(self):
        self.assertTrue(GEN.covers((3, None), (None, None)))
        self.assertFalse(GEN.covers((3, None), (4, None)))
        self.assertFalse(GEN.covers((3, None), (3,)))
        self.assertFalse(GEN.covers((None,), (3,)))

    def test_named_subtrees_preserve_every_balanced_row(self):
        parts = GEN.subtrees(self.states)
        seen = set()

        def expanded(part):
            if part.left is None:
                self.assertIsNone(part.right)
                self.assertLessEqual(len(part.rows), GEN.SUBTREE_ROWS)
                return list(part.rows)
            self.assertIn(part.left.name, seen)
            self.assertIn(part.right.name, seen)
            return expanded(part.left) + [part.root] + expanded(part.right)

        for part in parts:
            self.assertNotIn(part.name, seen)
            self.assertEqual(expanded(part), list(part.rows))
            seen.add(part.name)
        self.assertEqual(expanded(parts[-1]), list(self.states.items()))
        self.assertEqual(sum(len(part.rows) if part.left is None else 1 for part in parts), 735)
        self.assertEqual(len(seen), len(parts))
        self.assertEqual(GEN.render(self.raw, dict(reversed(list(self.states.items())))), self.rendered)

    def test_exact_distinct_row_reconciliation(self):
        by_name = {part.name: part for part in self.parts}
        pcs = lambda name: {pc for pc, _ in by_name[name].rows}
        accepted = ["subtree214", "subtree576", "subtree1022", "subtree1148", "subtree1717"]
        accepted_sets = [pcs(name) for name in accepted]
        self.assertEqual([len(rows) for rows in accepted_sets], [183, 183, 183, 11, 10])
        self.assertEqual(accepted_sets[2] & accepted_sets[3], {
            1140, 1141, 1142, 1144, 1145, 1148, 1149, 1150, 1151, 1154, 1155,
        })
        self.assertEqual(accepted_sets[4] & pcs("subtree1459"), {
            1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721,
        })
        accepted_union = set().union(*accepted_sets)
        self.assertEqual(len(accepted_union), 559)
        missing = set(self.states) - accepted_union
        self.assertEqual(len(missing), 176)
        self.assertEqual(missing, (pcs("subtree1459") - pcs("subtree1717")) | {371, 839, 1182})

    def assert_proof_structure(self, text, spec):
        by_name = {part.name: part for part in self.parts}
        parts = []

        def visit(part):
            if part.left is not None:
                self.assertIsNotNone(part.right)
                visit(part.left)
                visit(part.right)
            else:
                self.assertIsNone(part.right)
            parts.append(part)

        visit(by_name[spec.root])
        root_rows = by_name[spec.root].rows

        def theorem_stem(part):
            if part.name == spec.root:
                return part.name
            return f"{spec.internal_theorem_prefix}{part.name}"
        root_pcs = [pc for pc, _ in root_rows]
        self.assertEqual(len(root_rows), spec.rows)
        self.assertEqual(root_pcs, sorted(set(root_pcs)))
        self.assertEqual(root_pcs[0], spec.start)
        self.assertEqual(root_pcs[-1] + self.decoded[root_pcs[-1]].width, spec.stop)
        expected_names = []
        for part in parts:
            stem = theorem_stem(part)
            expected_names.extend([f"{stem}_rows_checked", f"{stem}_layout_checked"])
        expected_names.extend(witness.name for witness in spec.witnesses)
        expected_names.append(f"{spec.root}_order_and_size_checked")
        self.assertEqual(re.findall(r"^theorem (\w+)\s*:", text, re.M), expected_names)
        for witness in spec.witnesses:
            self.assertIn(
                f"checkRow code.toByteArray table 8 {witness.pc} {GEN.pattern(self.states[witness.pc])}",
                text,
                "witness must use the complete table",
            )

        tables = re.findall(
            r"^    subtree\d+\.all \(checkRow code\.toByteArray (\w+) 8\) = true := by$",
            text,
            re.M,
        )
        self.assertEqual(len(tables), len(parts))
        self.assertEqual(tables, ["table"] * len(parts),
                         "every emitted row proof must use the complete table")

        layouts = {
            name: (int(start), int(stop))
            for name, start, stop in re.findall(
                r"^theorem (\w+)_layout_checked :\n"
                r"    subtree\d+\.checkLayout code\.toByteArray (\d+) (\d+) = true := by$",
                text,
                re.M,
            )
        }
        expected_layouts = {
            theorem_stem(part): (
                part.rows[0][0],
                part.rows[-1][0] + self.decoded[part.rows[-1][0]].width,
            )
            for part in parts
        }
        self.assertEqual(layouts, expected_layouts)

        for part in parts:
            stem = theorem_stem(part)
            if part.left is None:
                self.assertIn(
                    f"theorem {stem}_rows_checked :\n"
                    f"    {part.name}.all (checkRow code.toByteArray table 8) = true := by\n"
                    "  decide +kernel",
                    text,
                )
            else:
                self.assertIn(f"  · exact {theorem_stem(part.left)}_rows_checked\n"
                              f"  · exact {theorem_stem(part.right)}_rows_checked", text)
                self.assertIn(f"  · exact {theorem_stem(part.left)}_layout_checked\n"
                              f"  · exact {theorem_stem(part.right)}_layout_checked", text)

        self.assertIn(
            f"theorem {spec.root}_order_and_size_checked :\n"
            f"    {spec.root}.checkOrder = true ∧ {spec.root}.size = {spec.rows} := by",
            text,
        )
        self.assertEqual(text.count("import Blanc.DripStackSafety"), 1)

    def test_region_proof_renderer_reproduces_and_extends_structure(self):
        accepted = GEN.REGION576_OUTPUT.read_text()
        self.assertEqual(self.proofs[GEN.REGION576_OUTPUT], accepted)
        self.assert_proof_structure(accepted, GEN.REGION576)
        region1022 = self.proofs[GEN.REGION1022_OUTPUT]
        self.assert_proof_structure(region1022, GEN.REGION1022)
        self.assertIn("row1165_cross_region_checked", region1022)
        self.assertIn("checkRow code.toByteArray table 8 1165 [some 1212, none, none]", region1022)
        region1459 = self.proofs[GEN.REGION1459_OUTPUT]
        self.assert_proof_structure(region1459, GEN.REGION1459)
        self.assertIn("row1227_cross_pack_checked", region1459)
        self.assertIn("checkRow code.toByteArray table 8 1227 [some 1735, none, none, none]", region1459)
        by_name = {part.name: part for part in self.parts}
        self.assertNotIn(1735, {pc for pc, _ in by_name["subtree1221"].rows})
        self.assertIn(1735, {pc for pc, _ in by_name["subtree1730"].rows})

    def test_certificate_facade_is_complete_and_same_frame(self):
        facade = self.proofs[GEN.CERTIFICATE_OUTPUT]
        self.assertEqual(re.findall(r"^import (\S+)$", facade, re.M), [
            "Blanc.DripStackSafetyRegion214",
            "Blanc.DripStackSafetyRegion576",
            "Blanc.DripStackSafetyRegion1022",
            "Blanc.DripStackSafetyRegion1459",
        ])
        self.assertEqual(re.findall(r"^theorem (\w+)", facade, re.M), [
            "subtree371_rows_checked", "subtree371_layout_checked",
            "subtree1182_rows_checked", "subtree1182_layout_checked",
            "subtree839_rows_checked", "subtree839_layout_checked",
            "table_rows_checked", "table_layout_checked", "table_order_and_size_checked",
            "table_checked", "entry_invariant", "actual_entry_safe",
        ])
        self.assertIn("table.size = 735", facade)
        self.assertIn("table.checkLayout code.toByteArray 0 1762 = true", facade)
        self.assertIn("checkTable code.toByteArray table 8 = true", facade)
        self.assertIn("(hprefix : Exec.Deriv.ParentPrefix root node)", facade)
        self.assertIn("(entryPc : root.pc = 0)", facade)
        self.assertIn("(entryStack : root.devm.stack = [])", facade)
        self.assertIn("(checkTable_certificate checked).at_parentPrefix hprefix rfl", facade)

    def test_proof_renderer_rejects_local_table_substitution(self):
        rendered = self.proofs[GEN.REGION1022_OUTPUT]
        mutated = rendered.replace(
            "checkRow code.toByteArray table 8",
            "checkRow code.toByteArray subtree1022 8",
            1,
        )
        with self.assertRaisesRegex(AssertionError, "complete table"):
            self.assert_proof_structure(mutated, GEN.REGION1022)
        self.assert_proof_structure(rendered, GEN.REGION1022)

    def test_cross_pack_witness_rejects_local_table_substitution(self):
        rendered = self.proofs[GEN.REGION1459_OUTPUT]
        mutated = rendered.replace(
            "checkRow code.toByteArray table 8 1227",
            "checkRow code.toByteArray subtree1221 8 1227",
            1,
        )
        with self.assertRaisesRegex(AssertionError, "complete table"):
            self.assert_proof_structure(mutated, GEN.REGION1459)
        self.assert_proof_structure(rendered, GEN.REGION1459)

    def test_runtime_underflow_mutation_and_restore(self):
        raw = bytearray(self.raw)
        raw[0] = 0x50
        with self.assertRaisesRegex(GEN.Rejected, "operand underflow at 0"):
            GEN.analyze(bytes(raw))
        self.restore()

    def test_branch_to_push_data_and_restore(self):
        raw = bytearray(self.raw)
        raw[4] = 8
        with self.assertRaisesRegex(GEN.Rejected, "invalid jump destination"):
            GEN.analyze(bytes(raw))
        self.restore()

    def test_branch_to_wrong_height_and_restore(self):
        raw = bytearray(self.raw)
        raw[1225:1227] = (1216).to_bytes(2, "big")
        with self.assertRaisesRegex(GEN.Rejected, "inconsistent join height"):
            GEN.analyze(bytes(raw))
        self.restore()

    def test_unknown_branch_and_restore(self):
        pc = next(pc for pc, instruction in self.decoded.items() if instruction.opcode == 0x56)
        with self.assertRaisesRegex(GEN.Rejected, "unknown jump destination"):
            GEN.transfer(self.decoded, pc, (None,))
        self.restore()

    def test_corrupt_row_pattern_and_restore(self):
        states = dict(self.states)
        states[1721] = (1, None)
        with self.assertRaisesRegex(GEN.Rejected, "successor pattern at 1721"):
            GEN.validate(self.decoded, states)
        self.restore()

    def test_corrupt_row_height_and_restore(self):
        states = dict(self.states)
        states[1721] += (None,)
        with self.assertRaisesRegex(GEN.Rejected, "successor pattern at 1721"):
            GEN.validate(self.decoded, states)
        self.restore()

    def test_missing_row_and_restore(self):
        states = dict(self.states)
        del states[1721]
        with self.assertRaisesRegex(GEN.Rejected, "exactly all decoded"):
            GEN.validate(self.decoded, states)
        self.restore()

    def test_independent_outgoing_bound(self):
        decoded = GEN.decode(bytes([0x33, 0x00]))
        with self.assertRaisesRegex(GEN.Rejected, "outgoing bound at 0"):
            GEN.transfer(decoded, 0, (None,) * 8)
        self.assertEqual(GEN.transfer(decoded, 0, (None,) * 7), [(1, (None,) * 8)])

    def test_high_dup_swap_indices(self):
        for opcode in range(0x80, 0xA0):
            decoded = GEN.decode(bytes([opcode, 0]))
            index = opcode - 0x80 if opcode < 0x90 else opcode - 0x8F
            if index >= 8:
                with self.assertRaisesRegex(GEN.Rejected, "underflow"):
                    GEN.transfer(decoded, 0, (None,) * 8)
            elif opcode < 0x90:
                with self.assertRaisesRegex(GEN.Rejected, "outgoing bound"):
                    GEN.transfer(decoded, 0, (None,) * 8)
            else:
                self.assertEqual(len(GEN.transfer(decoded, 0, (None,) * 8)[0][1]), 8)

    def test_decoder_rejects_truncation_and_unsupported(self):
        for raw in (bytes([0x61, 0]), bytes([0xFE]), bytes([0xFF]), b""):
            with self.assertRaises(GEN.Rejected):
                GEN.decode(raw)
        self.restore()

    def test_literals_are_exact_words(self):
        decoded = GEN.decode(bytes([0x50, 0]))
        for word in (-1, 1 << 256, True):
            with self.assertRaisesRegex(GEN.Rejected, "invalid abstract literal"):
                GEN.transfer(decoded, 0, (word,))

    def test_source_literal_parser(self):
        for source in ("", self.source + self.source,
                       "def code : Bytes := [0x100]", "def code : Bytes := [1]"):
            with self.assertRaises(GEN.Rejected):
                GEN.runtime_bytes(source)

    def test_bytes_identify_data_even_when_patterns_do_not_change(self):
        raw = bytearray(self.raw)
        pc = next(pc for pc, instruction in self.decoded.items() if instruction.opcode == 0x11)
        raw[pc] = 0x10
        self.assertEqual(GEN.analyze(bytes(raw)), self.states)
        self.assertNotEqual(GEN.render(bytes(raw), self.states), self.rendered)
        self.restore()

    def test_compare_default_write_explicit_and_restore(self):
        with tempfile.TemporaryDirectory(prefix="drip-stack-certificate-") as temporary:
            root = Path(temporary)
            (root / "scripts").mkdir()
            (root / "Blanc").mkdir()
            script = root / "scripts/gen-drip-stack-certificate.py"
            script.write_bytes((ROOT / "scripts/gen-drip-stack-certificate.py").read_bytes())
            producer = root / "scripts/stack_certificate.py"
            producer.write_bytes((ROOT / "scripts/stack_certificate.py").read_bytes())
            source = root / "Blanc/DripCode.lean"
            source.write_text(self.source)
            output = root / "Blanc/DripStackSafetyData.lean"
            region576 = root / "Blanc/DripStackSafetyRegion576.lean"
            region576.write_bytes(GEN.REGION576_OUTPUT.read_bytes())
            region1022 = root / "Blanc/DripStackSafetyRegion1022.lean"
            region1459 = root / "Blanc/DripStackSafetyRegion1459.lean"
            certificate = root / "Blanc/DripStackSafetyCertificate.lean"

            def run(*args):
                return subprocess.run([sys.executable, str(script), *args], capture_output=True, text=True)

            self.assertEqual(run().returncode, 1)
            self.assertFalse(output.exists())
            self.assertFalse(region1022.exists())
            self.assertFalse(region1459.exists())
            self.assertFalse(certificate.exists())
            self.assertEqual(run("--write").returncode, 0)
            self.assertEqual(output.read_text(), self.rendered)
            self.assertFalse(region1022.exists())
            self.assertFalse(region1459.exists())
            self.assertFalse(certificate.exists())
            before576 = region576.read_bytes()
            self.assertEqual(run("--write-proofs").returncode, 0)
            self.assertEqual(region576.read_bytes(), before576)
            self.assertEqual(region1022.read_text(), self.proofs[GEN.REGION1022_OUTPUT])
            self.assertEqual(region1459.read_text(), self.proofs[GEN.REGION1459_OUTPUT])
            self.assertEqual(certificate.read_text(), self.proofs[GEN.CERTIFICATE_OUTPUT])
            self.assertEqual(run("--write-proofs", str(root / "escape.lean")).returncode, 2)
            self.assertFalse((root / "escape.lean").exists())
            before = {path: path.stat().st_mtime_ns
                      for path in (output, region576, region1022, region1459, certificate)}
            self.assertEqual(run().returncode, 0)
            self.assertEqual({path: path.stat().st_mtime_ns for path in before}, before)
            output.write_text(self.rendered.replace(".node 1720", ".node 1721"))
            mutated = output.read_bytes()
            self.assertEqual(run().returncode, 1)
            self.assertEqual(output.read_bytes(), mutated)
            output.write_text(self.rendered)
            region1022.write_text(region1022.read_text().replace(
                "checkRow code.toByteArray table 8",
                "checkRow code.toByteArray subtree1022 8",
                1,
            ))
            mutated_proof = region1022.read_bytes()
            self.assertEqual(run().returncode, 1)
            self.assertEqual(region1022.read_bytes(), mutated_proof)
            region1022.write_text(self.proofs[GEN.REGION1022_OUTPUT])
            self.assertEqual(run().returncode, 0)
            certificate.write_text(certificate.read_text().replace("table.size = 735", "table.size = 734"))
            mutated_facade = certificate.read_bytes()
            self.assertEqual(run().returncode, 1)
            self.assertEqual(certificate.read_bytes(), mutated_facade)
            certificate.write_text(self.proofs[GEN.CERTIFICATE_OUTPUT])
            self.assertEqual(run().returncode, 0)
            source.write_text(self.source.replace("[0x5b,", "[0x50,", 1))
            self.assertEqual(run().returncode, 1)
            source.write_text(self.source)
            self.assertEqual(run().returncode, 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
