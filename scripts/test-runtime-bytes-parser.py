#!/usr/bin/env python3
"""Complete-expression controls for the compiler-owned byte parser."""
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "runtime_bytes", Path(__file__).with_name("check-runtime-bytes.py"))
parser = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(parser)


class LiteralParserTests(unittest.TestCase):
    def parse(self, source, name="runtime"):
        with tempfile.NamedTemporaryFile("w", suffix=".lean") as stream:
            stream.write(source)
            stream.flush()
            return parser.parse_lean_literal(stream.name, name)

    def test_literal_and_following_declaration(self):
        self.assertEqual(self.parse("def runtime : Bytes := [0x01, 0x02]\n"
                                    "theorem witness : True := by trivial\n"), b"\x01\x02")

    def test_alias_join_and_repeated_chunk(self):
        self.assertEqual(self.parse("private def a : Bytes := [0x01]\n"
                                    "private def b : Bytes :=\n a\n"
                                    "def runtime : Bytes :=\n a ++\n b\nend Blanc\n"),
                         b"\x01\x01")

    def test_cycles_fail(self):
        for source in ["def runtime : Bytes :=\n runtime\n",
                       "def runtime : Bytes :=\n a\ndef a : Bytes :=\n runtime\n"]:
            with self.subTest(source=source), self.assertRaisesRegex(parser.ParseError, "cycle"):
                self.parse(source)

    def test_suffix_rejected_and_exact_restoration(self):
        prefixes = ["def runtime : Bytes := [0x01]",
                    "def a : Bytes := [0x01]\ndef runtime : Bytes :=\n a"]
        for prefix in prefixes:
            for suffix in [" ++ [0x02]", "\n ++ [0x02]", "\n  |>.reverse",
                           "\n  garbage", "\n  ++"]:
                with self.subTest(prefix=prefix, suffix=suffix):
                    self.assertEqual(self.parse(prefix + "\n"), b"\x01")
                    with self.assertRaises(parser.ParseError):
                        self.parse(prefix + suffix + "\n")
                    self.assertEqual(self.parse(prefix + "\n"), b"\x01")

    def test_inert_fake_definition_and_duplicates(self):
        real = "def runtime : Bytes := [0x02]\n"
        self.assertEqual(self.parse("/- nested /- comment -/\n"
                                    "def runtime : Bytes := [0x01]\n-/\n" + real), b"\x02")
        self.assertEqual(self.parse('def s := "def runtime : Bytes := [0x01]"\n' + real), b"\x02")
        with self.assertRaises(parser.ParseError):
            self.parse(real + real)

    def test_raw_string_spoof_is_unsupported(self):
        source = ('def s := r#"embedded quote "\n'
                  'def runtime : Bytes := [0x01]\n"#\n'
                  'def runtime : Bytes := [0x02]\n')
        with self.assertRaisesRegex(parser.ParseError, "raw Lean strings"):
            self.parse(source)

    def test_unknown_chunk_and_non_bytes_fail(self):
        for expression in ["missing", "[]", "[0x100]", "[0x01] ++ []", '"x"',
                           "[0x01, bogus]", "List.replicate 2 0"]:
            with self.subTest(expression=expression), self.assertRaises(parser.ParseError):
                self.parse("def runtime : Bytes := " + expression + "\n")

    def test_production_literals(self):
        root = Path(__file__).resolve().parent.parent
        for module, name, count in [("FmintCode", "fmintCode", 1257),
                                    ("WethCode", "wethCode", 988),
                                    ("ProrataWethVaultCode", "prorataWethVaultCode", 17481)]:
            with self.subTest(module=module):
                self.assertEqual(len(parser.parse_lean_literal(root / "Blanc" / (module + ".lean"), name)), count)

    def test_vault_fixed_owner_controls(self):
        root = Path(__file__).resolve().parent.parent
        facade_text = (root / "Blanc/ProrataWethVaultCode.lean").read_text()
        data_text = (root / "Blanc/ProrataWethVaultCodeData.lean").read_text()
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory) / "Blanc"
            folder.mkdir()
            facade = folder / "ProrataWethVaultCode.lean"
            owner = folder / "ProrataWethVaultCodeData.lean"
            facade.write_text(facade_text)
            owner.write_text(data_text)
            self.assertEqual(len(parser.parse_lean_literal(facade, "prorataWethVaultCode")), 17481)
            mutants = [
                (facade, facade_text.replace("import Blanc.ProrataWethVaultCodeData", "import Blanc.Other"), "imports differ"),
                (facade, facade_text.replace("import Blanc.ProrataWethVaultCodeData", "-- import Blanc.ProrataWethVaultCodeData"), "imports differ"),
                (facade, facade_text.replace("namespace Blanc", "namespace Blanc\ndef prorataWethVaultCodeChunk0 : Bytes := [0x00]"), "shadows"),
                (facade, facade_text.replace("namespace Blanc", "namespace Other"), "ownership context"),
                (facade, facade_text.replace("  prorataWethVaultCodeChunk0 ++", "  prorataWethVaultCodeChunk1 ++"), "69 owned chunks"),
                (owner, data_text.replace("namespace Blanc", "namespace Other"), "ownership context"),
                (owner, data_text.replace("import Blanc.ProrataWethVault", "import Blanc.Other"), "ownership context"),
                (owner, data_text.replace("end GeneratedByteChunks", "  ++ [0x00]\nend GeneratedByteChunks"), "not a plain comma-separated list"),
            ]
            for path, mutant, diagnostic in mutants:
                with self.subTest(diagnostic=diagnostic):
                    original = path.read_bytes()
                    path.write_text(mutant)
                    with self.assertRaisesRegex(parser.ParseError, diagnostic):
                        parser.parse_lean_literal(facade, "prorataWethVaultCode")
                    path.write_bytes(original)
                    self.assertEqual(path.read_bytes(), original)
            original = owner.read_bytes()
            other = folder / "Other.lean"
            owner.rename(other)
            with self.assertRaisesRegex(parser.ParseError, "exact regular file"):
                parser.parse_lean_literal(facade, "prorataWethVaultCode")
            for alias in (lambda: owner.symlink_to(other), lambda: os.link(other, owner)):
                alias()
                with self.assertRaisesRegex(parser.ParseError, "exact regular file"):
                    parser.parse_lean_literal(facade, "prorataWethVaultCode")
                owner.unlink()
            other.rename(owner)
            self.assertEqual(owner.read_bytes(), original)
            self.assertEqual(facade.read_text(), facade_text)


if __name__ == "__main__":
    unittest.main()
