#!/usr/bin/env python3
"""Deterministic, non-elaborating generator controls using disposable inputs."""

import importlib.util
from pathlib import Path
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

    def test_both_conditional_arms(self):
        decoded = GEN.decode(bytes([0x57, 0x00, 0x5B, 0x00]))
        for condition in (None, 0, 1):
            self.assertEqual(GEN.transfer(decoded, 0, (2, condition)), [(2, ()), (1, ())])

    def test_full_stack_subsumption(self):
        self.assertTrue(GEN.covers((3, None), (None, None)))
        self.assertFalse(GEN.covers((3, None), (4, None)))
        self.assertFalse(GEN.covers((3, None), (3,)))
        self.assertFalse(GEN.covers((None,), (3,)))

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
            source = root / "Blanc/DripCode.lean"
            source.write_text(self.source)
            output = root / "Blanc/DripStackSafetyData.lean"

            def run(*args):
                return subprocess.run([sys.executable, str(script), *args], capture_output=True, text=True)

            self.assertEqual(run().returncode, 1)
            self.assertFalse(output.exists())
            self.assertEqual(run("--write").returncode, 0)
            self.assertEqual(output.read_text(), self.rendered)
            before = output.stat().st_mtime_ns
            self.assertEqual(run().returncode, 0)
            self.assertEqual(output.stat().st_mtime_ns, before)
            output.write_text(self.rendered.replace(".node 1720", ".node 1721"))
            mutated = output.read_bytes()
            self.assertEqual(run().returncode, 1)
            self.assertEqual(output.read_bytes(), mutated)
            output.write_text(self.rendered)
            self.assertEqual(run().returncode, 0)
            source.write_text(self.source.replace("[0x5b,", "[0x50,", 1))
            self.assertEqual(run().returncode, 1)
            source.write_text(self.source)
            self.assertEqual(run().returncode, 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
