#!/usr/bin/env python3
"""Focused table controls and unit tests for explicit simp inventory and checker.

Covers:
1. Simp registrations in declaration attributes and attribute commands:
   - Grouped attributes: @[simp, inline], @[inline, simp]
   - Modifiers & priority: @[simp high], @[simp low], @[simp default], @[simp 1000]
   - Inverse/down forms: @[simp ↓], @[↓ simp], @[simp ←], @[simp <-], @[← simp], @[<- simp]
   - Local and scoped uses: @[scoped simp], @[local simp], attribute [local simp] foo,
     scoped attribute [simp] foo, local attribute [simp] foo
   - Attribute commands with multiple names and priority
2. Implicit simp/simpa/simp_all/dsimp tactics and suggestion variants:
   - simp, simp [foo], simp at h, simp (config := ...) [foo]
   - simp +zeta, simp -zeta, simp +zeta [foo], simp -zeta [foo]
   - simpa, simpa [foo], simpa using h, simpa [foo] using h, simpa (config := ...) [foo] using h
   - simpa +zeta using h, simp_all +zeta, dsimp +zeta
   - simp_all, simp_all [foo]
   - dsimp, dsimp [foo], dsimp at h
   - Suggestion variants: simp?, simpa?, simp_all?, dsimp?, simp? [foo]
   - Macro quotation bodies: `(tactic| simp), `(tactic| simp [foo])
3. Safe ordinary explicit forms:
   - simp only, simp only [], simp only [foo, bar]
   - simp (config := ...) only [foo] at h
   - simp +zeta only, simp +zeta only [foo], simp -zeta only [foo], simp +zeta -zeta only [foo]
   - simp (config := ...) +zeta only [foo]
   - simpa only using h, simpa (config := ...) only [foo] using h, simpa +zeta only using h
   - dsimp only [foo], dsimp (config := ...) only [foo] at h, dsimp +zeta only [foo]
   - simp_all only [foo], simp_all (config := ...) only [foo], simp_all +zeta only [foo]
   - simp? (config := ...) only [foo]
   - Macro quotation bodies: `(tactic| simp only [foo])
4. Nearby tricky syntax (false-positive prevention):
   - Attribute negation: attribute [-simp] foo (unregistration)
   - Other attributes: @[nolint simpNF], @[simps], @[simproc], @[simple]
   - Quoted syntax keyword declarations: syntax "simp" : tactic, syntax "simp" "[" ident "]" : tactic
   - Qualified declaration and projection references: Lean.Meta.simp, Lean.Elab.Tactic.simp, ctx.simp, simp.foo
   - Longer tactic identifiers: simp_rw [a, b], simp_arith, simp_intro, simple_call
   - Comments: line comments `-- simp`, block comments `/- simp -/`, nested comments
   - String and char literals: "simp [foo]", 's'
   - Import and namespace: import Blanc.Simp, namespace Simp
5. Bite and restore controls by byte identity:
   Each mutant injected into a clean reference file must bite (produce named diagnostic),
   and reverting to exact original bytes establishes restoration by byte-for-byte SHA-256
   identity to the verified-green baseline without redundant reruns.
6. CLI contract and error handling:
   - `inventory` returns exit code 0
   - `check` returns exit code 1 on violations and 0 when clean
   - Deterministic JSON output
   - Read/parse errors and missing source tree fail closed with exit code 2
"""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple, Optional

# Add scripts directory to path to import explicit_simp
SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

import explicit_simp  # noqa: E402
from explicit_simp import (  # noqa: E402
    ExplicitSimpError,
    Finding,
    aggregate_report,
    discover_lean_files,
    scan_source,
)


class TestCase(NamedTuple):
    label: str
    code: str
    expected_bites: bool
    expected_kind: Optional[str] = None
    expected_category: Optional[str] = None


# ---------------------------------------------------------------------------
# Test Tables
# ---------------------------------------------------------------------------

REGISTRATION_TESTS = [
    TestCase("decl_simp_bare", "@[simp] theorem t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_grouped_first", "@[simp, inline] def f : Nat := 0", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_grouped_second", "@[inline, simp] def f : Nat := 0", True, "simp-attr-decl", "registration"),
    TestCase("decl_scoped_simp", "@[scoped simp] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_local_simp", "@[local simp] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_high", "@[simp high] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_low", "@[simp low] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_default", "@[simp default] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_prio_num", "@[simp 1000] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_down_after", "@[simp ↓] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_down_before", "@[↓ simp] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_left_arrow_unicode_after", "@[simp ←] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_left_arrow_unicode_before", "@[← simp] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_left_arrow_ascii_after", "@[simp <-] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_simp_left_arrow_ascii_before", "@[<- simp] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("decl_scoped_simp_high", "@[scoped simp high] lemma t : True := trivial", True, "simp-attr-decl", "registration"),
    TestCase("cmd_simp_bare", "attribute [simp] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_local_simp", "attribute [local simp] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_scoped_simp", "attribute [scoped simp] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_local_prefix_attribute", "local attribute [simp] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_scoped_prefix_attribute", "scoped attribute [simp] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_simp_grouped", "attribute [simp, inline] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_simp_high", "attribute [simp high] foo bar", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_simp_down", "attribute [simp ↓] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_simp_arrow", "attribute [simp ←] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_arrow_simp", "attribute [← simp] foo", True, "simp-attr-cmd", "registration"),
    TestCase("cmd_down_simp", "attribute [↓ simp] foo", True, "simp-attr-cmd", "registration"),
]

IMPLICIT_TACTIC_TESTS = [
    TestCase("tactic_simp_bare", "example : True := by simp", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_semicolon", "example : True := by simp; done", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_list", "example : True := by simp [foo, bar]", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_at", "example (h : True) : True := by simp at h", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_star_at_star", "example : True := by simp [*] at *", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_config_list", "example : True := by simp (config := { failIfUnchanged := false }) [foo]", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simpa_bare", "example : True := by simpa", True, "implicit-simpa", "implicit-tactic"),
    TestCase("tactic_simpa_using", "example (h : True) : True := by simpa using h", True, "implicit-simpa", "implicit-tactic"),
    TestCase("tactic_simpa_list_using", "example (h : True) : True := by simpa [foo] using h", True, "implicit-simpa", "implicit-tactic"),
    TestCase("tactic_simpa_config_list", "example (h : True) : True := by simpa (config := ...) [foo] using h", True, "implicit-simpa", "implicit-tactic"),
    TestCase("tactic_simp_all_bare", "example : True := by simp_all", True, "implicit-simp_all", "implicit-tactic"),
    TestCase("tactic_simp_all_list", "example : True := by simp_all [foo]", True, "implicit-simp_all", "implicit-tactic"),
    TestCase("tactic_dsimp_bare", "example : True := by dsimp", True, "implicit-dsimp", "implicit-tactic"),
    TestCase("tactic_dsimp_list", "example : True := by dsimp [foo]", True, "implicit-dsimp", "implicit-tactic"),
    TestCase("tactic_dsimp_at", "example (h : True) : True := by dsimp at h", True, "implicit-dsimp", "implicit-tactic"),
    TestCase("tactic_simp_question", "example : True := by simp?", True, "implicit-simp?", "implicit-tactic"),
    TestCase("tactic_simp_question_list", "example : True := by simp? [foo]", True, "implicit-simp?", "implicit-tactic"),
    TestCase("tactic_simpa_question", "example (h : True) : True := by simpa? using h", True, "implicit-simpa?", "implicit-tactic"),
    TestCase("tactic_simp_all_question", "example : True := by simp_all?", True, "implicit-simp_all?", "implicit-tactic"),
    TestCase("tactic_dsimp_question", "example : True := by dsimp?", True, "implicit-dsimp?", "implicit-tactic"),
    TestCase("tactic_macro_quote_simp", "macro \"t\" : tactic => `(tactic| simp)", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_macro_quote_simp_list", "macro \"t\" : tactic => `(tactic| simp [foo])", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_zeta", "example : True := by simp +zeta", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_zeta_list", "example : True := by simp +zeta [foo]", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_minus_zeta", "example : True := by simp -zeta", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simp_minus_zeta_list", "example : True := by simp -zeta [foo]", True, "implicit-simp", "implicit-tactic"),
    TestCase("tactic_simpa_zeta", "example (h : True) : True := by simpa +zeta using h", True, "implicit-simpa", "implicit-tactic"),
    TestCase("tactic_dsimp_zeta", "example : True := by dsimp +zeta", True, "implicit-dsimp", "implicit-tactic"),
    TestCase("tactic_simp_all_zeta", "example : True := by simp_all +zeta", True, "implicit-simp_all", "implicit-tactic"),
]

SAFE_EXPLICIT_TESTS = [
    TestCase("explicit_simp_only_bare", "example : True := by simp only", False),
    TestCase("explicit_simp_only_empty_list", "example : True := by simp only []", False),
    TestCase("explicit_simp_only_list", "example : True := by simp only [foo, bar]", False),
    TestCase("explicit_simp_config_only_list", "example : True := by simp (config := { failIfUnchanged := false }) only [foo]", False),
    TestCase("explicit_simp_only_list_at", "example (h : True) : True := by simp only [foo] at h", False),
    TestCase("explicit_simp_config_only_list_at", "example (h : True) : True := by simp (config := ...) only [foo] at h |-", False),
    TestCase("explicit_simpa_only_using", "example (h : True) : True := by simpa only using h", False),
    TestCase("explicit_simpa_only_list_using", "example (h : True) : True := by simpa only [foo] using h", False),
    TestCase("explicit_simpa_config_only_list_using", "example (h : True) : True := by simpa (config := ...) only [foo] using h", False),
    TestCase("explicit_dsimp_only_bare", "example : True := by dsimp only", False),
    TestCase("explicit_dsimp_only_list", "example : True := by dsimp only [foo]", False),
    TestCase("explicit_dsimp_config_only_list_at", "example (h : True) : True := by dsimp (config := ...) only [foo] at h", False),
    TestCase("explicit_simp_all_only_list", "example : True := by simp_all only [foo]", False),
    TestCase("explicit_simp_all_config_only_list", "example : True := by simp_all (config := ...) only [foo]", False),
    TestCase("explicit_simp_question_config_only_list", "example : True := by simp? (config := ...) only [foo]", False),
    TestCase("explicit_macro_quote_simp_only", "macro \"t\" : tactic => `(tactic| simp only [foo])", False),
    TestCase("explicit_simp_zeta_only", "example : True := by simp +zeta only", False),
    TestCase("explicit_simp_zeta_only_list", "example : True := by simp +zeta only [foo]", False),
    TestCase("explicit_simp_minus_zeta_only_list", "example : True := by simp -zeta only [foo]", False),
    TestCase("explicit_simp_zeta_minus_zeta_only_list", "example : True := by simp +zeta -zeta only [foo]", False),
    TestCase("explicit_simp_config_zeta_only_list", "example : True := by simp (config := ...) +zeta only [foo]", False),
    TestCase("explicit_simpa_zeta_only_using", "example (h : True) : True := by simpa +zeta only using h", False),
    TestCase("explicit_dsimp_zeta_only_list", "example : True := by dsimp +zeta only [foo]", False),
    TestCase("explicit_simp_all_zeta_only_list", "example : True := by simp_all +zeta only [foo]", False),
]

AESOP_TESTS = [
    TestCase("aesop_bare", "example : True := by aesop", True, "implicit-aesop-simp", "implicit-tactic"),
    TestCase("aesop_question", "example : True := by aesop?", True, "implicit-aesop-simp", "implicit-tactic"),
    TestCase("aesop_terminal", "example : True := by aesop!", True, "implicit-aesop-simp", "implicit-tactic"),
    TestCase("aesop_true", "example : True := by aesop (config := { enableSimp := true })", True, "implicit-aesop-simp"),
    TestCase("aesop_other_field", "example : True := by aesop (config := { maxRuleApplications := 200 })", True, "implicit-aesop-simp"),
    TestCase("aesop_config_variable", "example : True := by aesop (config := cfg)", True, "implicit-aesop-simp"),
    TestCase("aesop_nested_false", "example : True := by aesop (config := { other := { enableSimp := false } })", True, "implicit-aesop-simp"),
    TestCase("aesop_false_expression", "example : True := by aesop (config := { enableSimp := false || true })", True, "implicit-aesop-simp"),
    TestCase("aesop_duplicate_field", "example : True := by aesop (config := { enableSimp := false, enableSimp := true })", True, "implicit-aesop-simp"),
    TestCase("aesop_later_override", "example : True := by aesop (config := { enableSimp := false }) (config := { enableSimp := true })", True, "implicit-aesop-simp"),
    TestCase("aesop_parenthesized_false", "example : True := by aesop (config := { enableSimp := (false) })", True, "implicit-aesop-simp"),
    TestCase("aesop_quote", "macro \"t\" : tactic => `(tactic| aesop)", True, "implicit-aesop-simp"),
    TestCase("aesop_literal_false", "example : True := by aesop (config := { enableSimp := false })", False),
    TestCase("aesop_false_with_fields", "example : True := by aesop (config := { maxRuleApplications := 200, enableSimp := false, terminal := true })", False),
    TestCase("aesop_false_newline_fields", "example : True := by aesop (config := { enableSimp := false\n maxRuleApplications := 200 })", False),
    TestCase("aesop_false_rules", "example : True := by aesop (config := { enableSimp := false }) (add safe apply h)", False),
    TestCase("aesop_false_comments", "example : True := by aesop (config := { enableSimp /- flag -/ := false })", False),
    TestCase("aesop_false_quote", "macro \"t\" : tactic => `(tactic| aesop (config := { enableSimp := false }))", False),
    TestCase("aesop_comments_strings", '-- aesop\ndef text : String := \"aesop\"', False),
    TestCase("aesop_qualified", "def value := Aesop.aesop", False),
    TestCase("aesop_attribute", "@[aesop safe] theorem t : True := trivial", False),
    TestCase("aesop_namespace", "namespace aesop\ndef t := 0\nend aesop", False),
]



NORM_NUM_TESTS = [
    TestCase("norm_num_bare", "example : 1 + 1 = 2 := by norm_num", True, "implicit-norm_num", "implicit-tactic"),
    TestCase("norm_num_args", "example : P := by norm_num [foo]", True, "implicit-norm_num"),
    TestCase("norm_num_config", "example : P := by norm_num (config := { zeta := false }) [foo]", True, "implicit-norm_num"),
    TestCase("norm_num_quote", 'macro "t" : tactic => `(tactic| norm_num)', True, "implicit-norm_num"),
    TestCase("norm_num_at", "example : P := by norm_num at *", True, "implicit-norm_num"),
    TestCase("norm_num_only", "example : 1 + 1 = 2 := by norm_num only", False),
    TestCase("norm_num_only_args", "example : P := by norm_num only [foo]", False),
    TestCase("norm_num_config_only", "example : P := by norm_num (config := { zeta := false }) only [foo]", False),
    TestCase("norm_num_only_at", "example : P := by norm_num only [foo] at h", False),
    TestCase("norm_num_only_quote", 'macro "t" : tactic => `(tactic| norm_num only [foo])', False),
    TestCase("norm_num1_structural", "example : 1 + 1 = 2 := by norm_num1", False),
    TestCase("norm_num_longer", "def norm_num_custom := 0", False),
    TestCase("norm_num_qualified", "def t := Foo.norm_num", False),
    TestCase("norm_num_attribute", "@[norm_num] def t := 0", False),
    TestCase("norm_num_comments_strings", '-- norm_num\ndef text : String := "norm_num"', False),
    TestCase("norm_num_namespace", "namespace norm_num\ndef t := 0\nend norm_num", False),
]


NEARBY_TRICKY_TESTS = [
    TestCase("negated_attr_cmd", "attribute [-simp] foo", False),
    TestCase("other_decl_attr_inline", "@[inline] def f : Nat := 0", False),
    TestCase("other_decl_attr_ext", "@[ext] structure S where x : Nat", False),
    TestCase("decl_attr_nolint_simpNF", "@[nolint simpNF] lemma t : True := trivial", False),
    TestCase("decl_attr_simps", "@[simps] structure Point where x : Nat", False),
    TestCase("decl_attr_simproc", "@[simproc] def myProc : SimpProc := id", False),
    TestCase("decl_attr_simple", "@[simple] def g : Nat := 1", False),
    TestCase("longer_tactic_simp_rw", "example : True := by simp_rw [foo, bar]", False),
    TestCase("longer_tactic_simp_arith", "example : True := by simp_arith", False),
    TestCase("longer_tactic_simp_intro", "example : True := by simp_intro x", False),
    TestCase("longer_tactic_simple_name", "example : True := by simple_tactic", False),
    TestCase("longer_tactic_my_simp", "example : True := by my_simp", False),
    TestCase("longer_tactic_simpa_foo", "example : True := by simpa_foo", False),
    TestCase("longer_tactic_dsimp_bar", "example : True := by dsimp_bar", False),
    TestCase("line_comment_simp", "-- simp [foo] in line comment", False),
    TestCase("block_comment_simp", "/- simp [foo] in block comment -/", False),
    TestCase("nested_block_comment_simp", "/- /- simp [foo] in nested block -/ -/", False),
    TestCase("string_literal_simp", 'def msg : String := "call simp [foo] here"', False),
    TestCase("char_literal_simp", "def c : Char := 's'", False),
    TestCase("import_line_simp", "import Blanc.Simp\nimport Mathlib.Tactic.Simp", False),
    TestCase("namespace_line_simp", "namespace Simp\ndef x := 1\nend Simp", False),
    TestCase("syntax_decl_quoted_simp", 'syntax "simp" : tactic', False),
    TestCase("syntax_decl_quoted_simp_args", 'syntax "simp" "[" ident "]" : tactic', False),
    TestCase("qualified_decl_meta_simp", "def runSimp := Lean.Meta.simp", False),
    TestCase("qualified_decl_tactic_simp", "def elabSimp := Lean.Elab.Tactic.simp", False),
    TestCase("field_proj_ctx_simp", "def callSimp (ctx : Context) := ctx.simp", False),
    TestCase("field_proj_simp_target", "def simpTarget (cfg : SimpConfig) := cfg.simp.target", False),
    TestCase("ident_simp_dot_foo", "def x := simp.foo", False),
]


# ---------------------------------------------------------------------------
# Runner functions
# ---------------------------------------------------------------------------

def test_suite_tables() -> None:
    """Run table controls for registrations, implicit calls, explicit forms, and tricky syntax."""
    all_tests = (
        ("Registrations", REGISTRATION_TESTS),
        ("Implicit Tactics", IMPLICIT_TACTIC_TESTS),
        ("Safe Explicit Forms", SAFE_EXPLICIT_TESTS),
        ("Aesop Normalization", AESOP_TESTS),
        ("Numeric Simplification", NORM_NUM_TESTS),
        ("Nearby Tricky Syntax", NEARBY_TRICKY_TESTS),
    )

    total = 0
    passed = 0

    for suite_name, table in all_tests:
        print(f"--- Running test suite: {suite_name} ({len(table)} cases) ---")
        for tc in table:
            total += 1
            findings = scan_source(tc.code, "Test.lean")
            if tc.expected_bites:
                if not findings:
                    raise AssertionError(f"FAIL [{tc.label}]: expected detector to BITE, but got 0 findings. Code: {tc.code!r}")
                f = findings[0]
                if tc.expected_kind and f.kind != tc.expected_kind:
                    raise AssertionError(f"FAIL [{tc.label}]: expected kind {tc.expected_kind!r}, got {f.kind!r}")
                if tc.expected_category and f.category != tc.expected_category:
                    raise AssertionError(f"FAIL [{tc.label}]: expected category {tc.expected_category!r}, got {f.category!r}")
            else:
                if findings:
                    raise AssertionError(f"FAIL [{tc.label}]: expected SAFE (no findings), but detector BIT with: {findings}. Code: {tc.code!r}")
            passed += 1

    print(f"Table controls OK: {passed}/{total} tests passed.\n")


# Clean reference baseline for byte-identity restore tests
CLEAN_REFERENCE_LEAN = """-- Clean baseline Lean module for bite-and-restore control
import Blanc.CommonProofs

namespace Blanc

def testIncrement (n : Nat) : Nat := n + 1

theorem testIncrement_eq (n : Nat) : testIncrement n = n + 1 := by
  simp (config := { failIfUnchanged := false }) only [testIncrement]

end Blanc
"""


def test_bite_and_restore_by_byte_identity() -> None:
    """Demonstrate that every detector mutant bites and restoring baseline matches byte-for-byte SHA-256."""
    print("--- Running Bite-and-Restore Controls by Byte Identity ---")
    baseline_bytes = CLEAN_REFERENCE_LEAN.encode("utf-8")
    baseline_sha = hashlib.sha256(baseline_bytes).hexdigest()

    # Verify baseline is completely clean
    baseline_findings = scan_source(CLEAN_REFERENCE_LEAN, "Reference.lean")
    assert not baseline_findings, f"Baseline reference must have 0 findings, got {baseline_findings}"

    # Mutants table to inject into baseline
    mutants = [
        ("mutant_attr_simp_decl", "@[simp] theorem t1 : True := trivial\n", "simp-attr-decl"),
        ("mutant_attr_scoped_simp", "@[scoped simp] theorem t2 : True := trivial\n", "simp-attr-decl"),
        ("mutant_attr_simp_arrow", "@[simp ←] theorem t3 : True := trivial\n", "simp-attr-decl"),
        ("mutant_attr_cmd", "attribute [simp] testIncrement\n", "simp-attr-cmd"),
        ("mutant_implicit_simp", "  have : True := by simp\n", "implicit-simp"),
        ("mutant_implicit_simp_list", "  have : True := by simp [testIncrement]\n", "implicit-simp"),
        ("mutant_implicit_simp_zeta", "  have : True := by simp +zeta\n", "implicit-simp"),
        ("mutant_implicit_simp_minus_zeta_list", "  have : True := by simp -zeta [testIncrement]\n", "implicit-simp"),
        ("mutant_implicit_simpa", "  have : True := by simpa using trivial\n", "implicit-simpa"),
        ("mutant_implicit_simp_all", "  have : True := by simp_all\n", "implicit-simp_all"),
        ("mutant_implicit_dsimp", "  have : True := by dsimp [testIncrement]\n", "implicit-dsimp"),
        ("mutant_implicit_simp_question", "  have : True := by simp?\n", "implicit-simp?"),
        ("mutant_implicit_aesop", "  have : True := by aesop\n", "implicit-aesop-simp"),
        ("mutant_implicit_norm_num", "  have : True := by norm_num\n", "implicit-norm_num"),
    ]

    for label, injection, expected_kind in mutants:
        # Step 1: Inject mutant
        mutated_text = injection + CLEAN_REFERENCE_LEAN

        # Step 2: Verify mutant BITES
        findings = scan_source(mutated_text, "Reference.lean")
        if not findings:
            raise AssertionError(f"Mutant {label} failed to bite!")
        if findings[0].kind != expected_kind:
            raise AssertionError(f"Mutant {label} bit with kind {findings[0].kind!r}, expected {expected_kind!r}")

        # Step 3: Restore to exact original text
        restored_text = mutated_text[len(injection):]
        restored_bytes = restored_text.encode("utf-8")
        restored_sha = hashlib.sha256(restored_bytes).hexdigest()

        # Step 4: Verify byte-for-byte identity to green reference (restoration established by byte identity)
        if restored_sha != baseline_sha:
            raise AssertionError(f"Restored file SHA-256 mismatch for {label}: expected {baseline_sha}, got {restored_sha}")

    print(f"Bite-and-restore OK: {len(mutants)} mutants bit and restored to byte-identical baseline ({baseline_sha[:12]}...).\n")


def test_cli_and_errors() -> None:
    """Test CLI commands: inventory, check, JSON output, and parse error handling."""
    print("--- Running CLI and Error Handling Tests ---")

    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_path = Path(tmp_dir)
        blanc_dir = tmp_path / "Blanc"
        blanc_dir.mkdir()

        # Clean file
        clean_file = blanc_dir / "Clean.lean"
        clean_file.write_text(CLEAN_REFERENCE_LEAN, encoding="utf-8")

        # Dirty file with violations
        dirty_file = blanc_dir / "Dirty.lean"
        dirty_file.write_text(
            "@[simp] def d1 : Nat := 0\nlemma d2 : True := by simp\n",
            encoding="utf-8"
        )

        # 1. Test inventory mode on clean file: exit 0
        code = explicit_simp.main(["inventory", "Blanc/Clean.lean", "--root", str(tmp_path)])
        assert code == 0, f"Expected inventory on clean file to exit 0, got {code}"

        # 2. Test inventory mode on dirty file: exits 0 (inventory never fails current population)
        code = explicit_simp.main(["inventory", "Blanc/Dirty.lean", "--root", str(tmp_path)])
        assert code == 0, f"Expected inventory on dirty file to exit 0, got {code}"

        # 3. Test inventory mode with --json
        code = explicit_simp.main(["inventory", "Blanc/Dirty.lean", "--root", str(tmp_path), "--json"])
        assert code == 0, f"Expected inventory --json to exit 0, got {code}"

        # 4. Test check mode on clean file: exits 0
        code = explicit_simp.main(["check", "Blanc/Clean.lean", "--root", str(tmp_path)])
        assert code == 0, f"Expected check on clean file to exit 0, got {code}"

        # 5. Test check mode on dirty file: exits 1 (fails on violation)
        code = explicit_simp.main(["check", "Blanc/Dirty.lean", "--root", str(tmp_path)])
        assert code == 1, f"Expected check on dirty file to exit 1, got {code}"

        # 6. Test parse error handling: unterminated block comment
        bad_comment_file = blanc_dir / "BadComment.lean"
        bad_comment_file.write_text("/- unterminated comment\n", encoding="utf-8")
        code = explicit_simp.main(["check", "Blanc/BadComment.lean", "--root", str(tmp_path)])
        assert code == 2, f"Expected parse error on unterminated comment to exit 2, got {code}"

        # 7. Test missing file error
        code = explicit_simp.main(["check", "Blanc/NonExistent.lean", "--root", str(tmp_path)])
        assert code == 2, f"Expected missing file error to exit 2, got {code}"

        # 8. Test missing source tree fails closed with exit code 2
        empty_dir = tmp_path / "EmptyRoot"
        empty_dir.mkdir()
        code = explicit_simp.main(["check", "--root", str(empty_dir)])
        assert code == 2, f"Expected check on empty tree to fail closed with exit 2, got {code}"
        code = explicit_simp.main(["inventory", "--root", str(empty_dir)])
        assert code == 2, f"Expected inventory on empty tree to fail closed with exit 2, got {code}"

    print("CLI and error handling tests OK.\n")


def test_exact_population_and_paths() -> None:
    """Required populations and raw/filesystem aliases fail at discovery."""
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory).resolve()
        (root / "Blanc").mkdir()
        root_file = root / "Blanc.lean"
        root_file.write_text("import Blanc.Clean\n", encoding="utf-8")
        source = root / "Blanc/Clean.lean"
        baseline = b"example : True := by simp only [True.intro]\n"
        source.write_bytes(baseline)
        refuses_untracked = False
        try:
            discover_lean_files(root)
        except ExplicitSimpError:
            refuses_untracked = True
        assert refuses_untracked, "population without Git must fail closed"
        for exempt in explicit_simp.EXEMPT_FIXTURES:
            (root / exempt).parent.mkdir(parents=True, exist_ok=True)
            (root / exempt).write_text("example : True := by simp\n", encoding="utf-8")
        git_init(root, *explicit_simp.EXEMPT_FIXTURES)
        assert discover_lean_files(root) == sorted([root_file, source])
        assert discover_lean_files(root, ["Blanc/Clean.lean"]) == [source]

        def refuses(targets=None):
            try:
                discover_lean_files(root, targets)
            except ExplicitSimpError:
                return
            raise AssertionError(f"unsafe/incomplete discovery passed: {targets}")

        for raw in ("Blanc//Clean.lean", "Blanc/../Blanc/Clean.lean", "Blanc\\Clean.lean",
                    "blanc/Clean.lean", str(source), "Blanc/Clean.txt"):
            refuses([raw])
        root_file.unlink()
        refuses()
        root_file.write_text("import Blanc.Clean\n", encoding="utf-8")
        source.unlink()
        refuses()
        source.write_bytes(baseline)
        target = root / "Blanc/Real.lean"
        source.rename(target)
        source.symlink_to(target)
        refuses()
        refuses(["Blanc/Clean.lean"])
        source.unlink()
        target.rename(source)
        assert source.read_bytes() == baseline
    print("Exact population/path controls OK; green bytes restored by identity.\n")


def git_init(root: Path, *paths: str) -> None:
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    if paths:
        subprocess.run(["git", "-C", str(root), "add", "--", *paths], check=True)


def test_tracked_population_and_exemptions() -> None:
    """Tracked Lean outside Blanc/ is scanned; named fixtures are exempt; stale exemptions refuse."""
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory).resolve()
        (root / "Blanc").mkdir()
        (root / "scripts" / "fixtures" / "leaf-audit").mkdir(parents=True)
        (root / ".lake" / "packages" / "dep").mkdir(parents=True)
        (root / "Blanc.lean").write_text("import Blanc.Clean\n", encoding="utf-8")
        (root / "Blanc" / "Clean.lean").write_text(CLEAN_REFERENCE_LEAN, encoding="utf-8")
        script = root / "scripts" / "Regression.lean"
        clean_script = "example : True := by simp only [True.intro]\n"
        script.write_text(clean_script, encoding="utf-8")
        main_file = root / "Main.lean"
        main_file.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
        for exempt in explicit_simp.EXEMPT_FIXTURES:
            path = root / exempt
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("@[simp] theorem f : True := trivial\nexample : True := by simp\n", encoding="utf-8")
        (root / ".lake" / "packages" / "dep" / "Dep.lean").write_text("example : True := by simp\n", encoding="utf-8")
        git_init(root, "Blanc.lean", "Blanc/Clean.lean", "scripts/Regression.lean", "Main.lean",
                 *explicit_simp.EXEMPT_FIXTURES)
        found = discover_lean_files(root)
        rels = sorted(str(p.relative_to(root)) for p in found)
        assert rels == ["Blanc.lean", "Blanc/Clean.lean", "Main.lean", "scripts/Regression.lean"], rels
        assert explicit_simp.main(["check", "--root", str(root)]) == 0
        # Control: an implicit call in a tracked script bites through the default population.
        script.write_text("example : True := by simp\n", encoding="utf-8")
        assert explicit_simp.main(["check", "--root", str(root)]) == 1
        script.write_text(clean_script, encoding="utf-8")
        assert explicit_simp.main(["check", "--root", str(root)]) == 0
        # Control: a registration in Main.lean bites.
        original_main = main_file.read_bytes()
        main_file.write_text("@[simp] theorem g : True := trivial\n", encoding="utf-8")
        assert explicit_simp.main(["check", "--root", str(root)]) == 1
        main_file.write_bytes(original_main)
        assert explicit_simp.main(["check", "--root", str(root)]) == 0
        # Control: a stale exemption (file no longer tracked) refuses the population.
        first = next(iter(explicit_simp.EXEMPT_FIXTURES))
        subprocess.run(["git", "-C", str(root), "rm", "-q", "--cached", "--", first], check=True)
        assert explicit_simp.main(["check", "--root", str(root)]) == 2
        subprocess.run(["git", "-C", str(root), "add", "--", first], check=True)
        assert explicit_simp.main(["check", "--root", str(root)]) == 0
        # Control: an exemption naming a production module refuses.
        saved = dict(explicit_simp.EXEMPT_FIXTURES)
        try:
            explicit_simp.EXEMPT_FIXTURES["Blanc/Clean.lean"] = "not allowed"
            assert explicit_simp.main(["check", "--root", str(root)]) == 2
        finally:
            explicit_simp.EXEMPT_FIXTURES.clear()
            explicit_simp.EXEMPT_FIXTURES.update(saved)
        assert explicit_simp.main(["check", "--root", str(root)]) == 0
    print("Tracked population/exemption controls OK; clean bytes restored.\n")


def main() -> int:
    print("=================================================================")
    print("Running explicit simp syntax controls and self-tests")
    print("=================================================================")
    test_suite_tables()
    test_bite_and_restore_by_byte_identity()
    test_cli_and_errors()
    test_exact_population_and_paths()
    test_tracked_population_and_exemptions()
    print("ALL TESTS PASSED SUCCESSFULLY.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
