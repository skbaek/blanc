#!/usr/bin/env python3
"""Focused non-elaborating controls for the untrusted table producer."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "stack_certificate", ROOT / "scripts/stack_certificate.py"
)
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class StackCertificateTests(unittest.TestCase):
    def test_cross_pack_cycle_and_balanced_determinism(self):
        raw = bytes([0x5B, 0x60, 0x00, 0x56])
        states = GEN.analyze(raw, 1)
        self.assertEqual(states, {0: (), 1: (), 3: (0,)})
        first = GEN.render_module(
            raw, states, 1, "T", "table", "pack", "test", "test command"
        )
        second = GEN.render_module(
            raw,
            dict(reversed(list(states.items()))),
            1,
            "T",
            "table",
            "pack",
            "test",
            "test command",
        )
        self.assertEqual(first, second)
        self.assertIn("tableWithoutEntry", first)

    def test_both_conditional_arms_even_for_literal_condition(self):
        decoded = GEN.decode(bytes([0x57, 0x00, 0x5B, 0x00]))
        for condition in (None, 0, 1):
            self.assertEqual(
                GEN.transfer(decoded, 0, (2, condition), 2),
                [(2, ()), (1, ())],
            )

    def test_full_stack_subsumption(self):
        self.assertTrue(GEN.covers((3, None), (None, None)))
        self.assertFalse(GEN.covers((3, None), (4, None)))
        self.assertFalse(GEN.covers((3, None), (3,)))
        self.assertFalse(GEN.covers((None,), (3,)))

    def test_fail_closed_boundaries(self):
        for raw in (bytes([0x61, 0]), bytes([0xFE]), bytes([0xFF]), b""):
            with self.assertRaises(GEN.Rejected):
                GEN.decode(raw)
        with self.assertRaisesRegex(GEN.Rejected, "maximum"):
            GEN.analyze(bytes([0x00]), 9)
        with self.assertRaisesRegex(GEN.Rejected, "operand underflow"):
            GEN.analyze(bytes([0x50]), 1)

    def test_named_packs_preserve_every_row(self):
        states = {pc: () for pc in range(47)}
        parts = GEN.packs(states)
        seen = set()

        def expanded(part):
            if part.left is None:
                self.assertIsNone(part.right)
                self.assertLessEqual(len(part.rows), GEN.PACK_ROWS)
                return list(part.rows)
            self.assertIn(part.left.root[0], seen)
            self.assertIn(part.right.root[0], seen)
            return expanded(part.left) + [part.root] + expanded(part.right)

        for part in parts:
            self.assertNotIn(part.root[0], seen)
            self.assertEqual(expanded(part), list(part.rows))
            seen.add(part.root[0])
        self.assertEqual(expanded(parts[-1]), list(states.items()))
        self.assertEqual(
            sum(len(part.rows) if part.left is None else 1 for part in parts),
            len(states),
        )

    def test_generated_output_check_rejects_missing_and_stale(self):
        with tempfile.TemporaryDirectory(prefix="stack-certificate-") as raw:
            path = Path(raw) / "Data.lean"
            with self.assertRaisesRegex(GEN.Rejected, "stale/missing"):
                GEN.check_output(path, "expected")
            path.write_text("wrong", encoding="utf-8")
            with self.assertRaisesRegex(GEN.Rejected, "stale/missing"):
                GEN.check_output(path, "expected")
            path.write_text("expected", encoding="utf-8")
            GEN.check_output(path, "expected")


if __name__ == "__main__":
    unittest.main(verbosity=2)
