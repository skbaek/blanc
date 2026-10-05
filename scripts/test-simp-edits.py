#!/usr/bin/env python3
"""Comprehensive test suite for Lean LSP TryThisInfo preview applier.

Focused controls:
1. synthetic three-edit ASCII suggestion preview;
2. UTF16 astral and ordinary Unicode offsets;
3. CRLF and trailing newline/EOF;
4. duplicate identical edits;
5. divergent same-span and partial-overlap refusal;
6. hash mismatch;
7. malformed positions/UTF8/payload;
8. wrong original macro/by range;
9. wrong replacement family/implicit replacement refusal;
10. source input stays byte-identical regardless of success/failure.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import traceback
from pathlib import Path
from typing import Any, Dict

# Shared library first: import preview applier
sys.path.insert(0, str(Path(__file__).resolve().parent))
from simp_edits import PreviewResult, SimpEditError, preview


def _make_payload(source_bytes: bytes, edits: list, schema: Any = 1, sha: Any = None) -> Dict[str, Any]:
    return {
        "schema": schema,
        "source_sha256": sha if sha is not None else hashlib.sha256(source_bytes).hexdigest(),
        "edits": edits,
    }


# ---------------------------------------------------------------------------
# Control 1: Synthetic three-edit ASCII suggestion preview
# ---------------------------------------------------------------------------
def test_synthetic_three_edit_ascii_preview() -> None:
    src = (
        "import Blanc\n"
        "theorem t1 : True := by\n"
        "  simp?\n"
        "theorem t2 : True := by\n"
        "  simpa?\n"
        "theorem t3 : True := by\n"
        "  dsimp?\n"
    ).encode("utf-8")

    edits = [
        {
            "range": {"start": {"line": 2, "character": 2}, "end": {"line": 2, "character": 7}},
            "newText": "simp only []",
        },
        {
            "range": {"start": {"line": 4, "character": 2}, "end": {"line": 4, "character": 8}},
            "newText": "simpa (config := {zeta := false}) +zeta only [h]",
        },
        {
            "range": {"start": {"line": 6, "character": 2}, "end": {"line": 6, "character": 8}},
            "newText": "dsimp only",
        },
    ]

    payload = _make_payload(src, edits)
    res = preview(src, payload)
    assert isinstance(res, PreviewResult)
    assert res.applied_edits == 3

    cand_text = res.candidate_bytes.decode("utf-8")
    assert "  simp only []\n" in cand_text
    assert "  simpa (config := {zeta := false}) +zeta only [h]\n" in cand_text
    assert "  dsimp only\n" in cand_text
    assert "simp?" not in cand_text
    assert "simpa?" not in cand_text
    assert "dsimp?" not in cand_text

    # Also verify CLI execution with temporary files
    with tempfile.NamedTemporaryFile("wb", suffix=".lean", delete=False) as f_src:
        f_src.write(src)
        src_path = Path(f_src.name)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f_edits:
        json.dump(payload, f_edits)
        edits_path = Path(f_edits.name)

    try:
        proc = subprocess.run(
            [sys.executable, str(Path(__file__).resolve().parent / "simp_edits.py"), str(src_path), str(edits_path)],
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc.returncode == 0, f"CLI failed: {proc.stderr}"
        cli_out = json.loads(proc.stdout)
        assert cli_out["applied_edits"] == 3
        assert cli_out["candidate_source"] == cand_text
        assert cli_out["candidate_sha256"] == hashlib.sha256(res.candidate_bytes).hexdigest()
    finally:
        src_path.unlink(missing_ok=True)
        edits_path.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Control 2: UTF16 astral and ordinary Unicode offsets
# ---------------------------------------------------------------------------
def test_utf16_astral_and_ordinary_unicode() -> None:
    # 2a: Ordinary BMP Unicode: 'α' (2 bytes), '≤' (3 bytes), 'β' (2 bytes)
    # Line: "  α ≤ β simp?\n"
    # Codepoints: ' ' (0), ' ' (1), 'α' (2), ' ' (3), '≤' (4), ' ' (5), 'β' (6), ' ' (7), 's' (8)
    # Each BMP char takes 1 UTF-16 code unit.
    src_bmp = "  α ≤ β simp?\n".encode("utf-8")
    edits_bmp = [
        {
            "range": {"start": {"line": 0, "character": 8}, "end": {"line": 0, "character": 13}},
            "newText": "simp only [h]",
        }
    ]
    res_bmp = preview(src_bmp, _make_payload(src_bmp, edits_bmp))
    assert res_bmp.applied_edits == 1
    assert res_bmp.candidate_bytes.decode("utf-8") == "  α ≤ β simp only [h]\n"

    # 2b: Astral characters: '𝄞' (U+1D11E) and '𝔽' (U+1D53D)
    # Line: "  𝄞 𝔽 simp?\n"
    # Codepoints:
    # 0: ' ' (u16: 0)
    # 1: ' ' (u16: 1)
    # 2: '𝄞' (u16: 2, 3 - astral, 2 code units)
    # 3: ' ' (u16: 4)
    # 4: '𝔽' (u16: 5, 6 - astral, 2 code units)
    # 5: ' ' (u16: 7)
    # 6: 's' (u16: 8!)
    # UTF-16 start character for 'simp?' is 8, end is 8 + 5 = 13.
    src_astral = "  𝄞 𝔽 simp?\n".encode("utf-8")
    edits_astral = [
        {
            "range": {"start": {"line": 0, "character": 8}, "end": {"line": 0, "character": 13}},
            "newText": "simp only [x]",
        }
    ]
    res_astral = preview(src_astral, _make_payload(src_astral, edits_astral))
    assert res_astral.applied_edits == 1
    assert res_astral.candidate_bytes.decode("utf-8") == "  𝄞 𝔽 simp only [x]\n"

    # 2c: Half-surrogate failure: character 3 lands on the low surrogate of '𝄞'
    bad_half_surrogate = [
        {
            "range": {"start": {"line": 0, "character": 3}, "end": {"line": 0, "character": 13}},
            "newText": "simp only [x]",
        }
    ]
    failed = False
    try:
        preview(src_astral, _make_payload(src_astral, bad_half_surrogate))
    except SimpEditError as exc:
        failed = True
        assert "half-surrogate" in str(exc).lower()
    assert failed, "Expected half-surrogate rejection"

    # character 6 lands on the low surrogate of '𝔽'
    failed = False
    try:
        preview(src_astral, _make_payload(src_astral, [
            {"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 6}},
             "newText": "simp only [x]"}
        ]))
    except SimpEditError as exc:
        failed = True
        assert "half-surrogate" in str(exc).lower()
    assert failed, "Expected half-surrogate rejection"


# ---------------------------------------------------------------------------
# Control 3: CRLF and trailing newline/EOF
# ---------------------------------------------------------------------------
def test_crlf_and_eof() -> None:
    # 3a: CRLF file line endings preserved
    src_crlf = b"import Blanc\r\ntheorem t : True := by\r\n  simp?\r\n"
    edits_crlf = [
        {
            "range": {"start": {"line": 2, "character": 2}, "end": {"line": 2, "character": 7}},
            "newText": "simp only []",
        }
    ]
    res_crlf = preview(src_crlf, _make_payload(src_crlf, edits_crlf))
    assert res_crlf.applied_edits == 1
    cand_bytes = res_crlf.candidate_bytes
    assert cand_bytes == b"import Blanc\r\ntheorem t : True := by\r\n  simp only []\r\n"
    assert b"\r\n" in cand_bytes
    assert b"\n" not in cand_bytes.replace(b"\r\n", b"")  # no bare LF

    # 3b: EOF without trailing newline
    src_no_nl = b"  simp?"
    edits_no_nl = [
        {
            "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}},
            "newText": "simp only []",
        }
    ]
    res_no_nl = preview(src_no_nl, _make_payload(src_no_nl, edits_no_nl))
    assert res_no_nl.applied_edits == 1
    assert res_no_nl.candidate_bytes == b"  simp only []"

    # 3c: EOF with trailing newline
    src_nl = b"  simp?\n"
    res_nl = preview(src_nl, _make_payload(src_nl, edits_no_nl))
    assert res_nl.applied_edits == 1
    assert res_nl.candidate_bytes == b"  simp only []\n"


# ---------------------------------------------------------------------------
# Control 4: Duplicate identical edits
# ---------------------------------------------------------------------------
def test_duplicate_identical_edits() -> None:
    src = b"  simp?\n"
    single_edit = {
        "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}},
        "newText": "simp only []",
    }
    # Duplicate identical edits
    payload = _make_payload(src, [single_edit, single_edit, single_edit])
    res = preview(src, payload)
    assert res.applied_edits == 1
    assert res.candidate_bytes == b"  simp only []\n"


# ---------------------------------------------------------------------------
# Control 5: Divergent same-span and partial-overlap refusal
# ---------------------------------------------------------------------------
def test_divergent_same_span_and_partial_overlap() -> None:
    src = b"  simp?\n"
    # 5a: Same span, divergent replacement text
    divergent_edits = [
        {
            "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}},
            "newText": "simp only [a]",
        },
        {
            "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}},
            "newText": "simp only [b]",
        },
    ]
    failed = False
    try:
        preview(src, _make_payload(src, divergent_edits))
    except SimpEditError as exc:
        failed = True
        assert "divergent" in str(exc).lower()
    assert failed, "Expected divergent same-span refusal"

    # 5b: Partially overlapping edits
    src_two = b"  simp? simp?\n"
    # span 1: char 2 to 9 ("simp? s")
    # span 2: char 8 to 13 ("simp?")
    overlap_edits = [
        {
            "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 9}},
            "newText": "simp only [x]",
        },
        {
            "range": {"start": {"line": 0, "character": 8}, "end": {"line": 0, "character": 13}},
            "newText": "simp only [y]",
        },
    ]
    failed = False
    try:
        preview(src_two, _make_payload(src_two, overlap_edits))
    except SimpEditError as exc:
        failed = True
        assert "overlapping" in str(exc).lower() or "question-family" in str(exc).lower()
    assert failed, "Expected partial overlap refusal"


# ---------------------------------------------------------------------------
# Control 6: Hash mismatch
# ---------------------------------------------------------------------------
def test_hash_mismatch() -> None:
    src = b"  simp?\n"
    edit = {
        "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}},
        "newText": "simp only []",
    }
    payload = _make_payload(src, [edit], sha="a" * 64)
    failed = False
    try:
        preview(src, payload)
    except SimpEditError as exc:
        failed = True
        assert "mismatch" in str(exc).lower()
    assert failed, "Expected hash mismatch error"


# ---------------------------------------------------------------------------
# Control 7: Malformed positions / UTF8
# ---------------------------------------------------------------------------
def test_malformed_positions_and_utf8() -> None:
    src = b"  simp?\n"
    valid_range = {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}}

    # 7a: Invalid UTF-8 source bytes
    bad_bytes = b"\xff\xfe\x00\x12"
    failed = False
    try:
        preview(bad_bytes, _make_payload(bad_bytes, []))
    except SimpEditError as exc:
        failed = True
        assert "utf-8" in str(exc).lower()
    assert failed, "Expected invalid UTF-8 refusal"

    # 7b: Bool isn't int
    for bad_pos in [
        {"start": {"line": True, "character": 2}, "end": {"line": 0, "character": 7}},
        {"start": {"line": 0, "character": False}, "end": {"line": 0, "character": 7}},
        {"start": {"line": 0, "character": 2}, "end": {"line": True, "character": 7}},
        {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": True}},
    ]:
        failed = False
        try:
            preview(src, _make_payload(src, [{"range": bad_pos, "newText": "simp only []"}]))
        except SimpEditError as exc:
            failed = True
            assert "invalid integer position" in str(exc).lower()
        assert failed, f"Expected bool refusal for {bad_pos}"

    # 7c: Float / string / negative position
    for bad_pos in [
        {"start": {"line": 1.5, "character": 2}, "end": {"line": 0, "character": 7}},
        {"start": {"line": "0", "character": 2}, "end": {"line": 0, "character": 7}},
        {"start": {"line": -1, "character": 2}, "end": {"line": 0, "character": 7}},
    ]:
        failed = False
        try:
            preview(src, _make_payload(src, [{"range": bad_pos, "newText": "simp only []"}]))
        except SimpEditError as exc:
            failed = True
            assert "invalid integer position" in str(exc).lower()
        assert failed, f"Expected invalid int refusal for {bad_pos}"

    # 7d: Schema != 1 or bool
    for bad_schema in [2, "1", True, False, None]:
        failed = False
        try:
            preview(src, _make_payload(src, [], schema=bad_schema))
        except SimpEditError as exc:
            failed = True
            assert "schema" in str(exc).lower()
        assert failed, f"Expected schema refusal for {bad_schema}"

    # 7e: Out of bounds line / character
    for bad_pos in [
        {"start": {"line": 99, "character": 0}, "end": {"line": 99, "character": 5}},
        {"start": {"line": 0, "character": 99}, "end": {"line": 0, "character": 105}},
    ]:
        failed = False
        try:
            preview(src, _make_payload(src, [{"range": bad_pos, "newText": "simp only []"}]))
        except SimpEditError as exc:
            failed = True
            assert "out of bounds" in str(exc).lower()
        assert failed, f"Expected out of bounds refusal for {bad_pos}"

    # 7f: Non-object top levels rejected with named SimpEditError (no AttributeError)
    for bad_json_top in [
        b"[]",
        b"null",
        b"123",
        b'"string"',
        b"true",
        b"false",
        "[]",
        "null",
        "123",
    ]:
        failed = False
        try:
            preview(src, bad_json_top)
        except SimpEditError as exc:
            failed = True
            assert "json object" in str(exc).lower()
        assert failed, f"Expected non-object top-level refusal for JSON {bad_json_top!r}"

    for bad_direct_payload in [[], None, 123, "not json", True]:
        failed = False
        try:
            preview(src, bad_direct_payload)
        except SimpEditError as exc:
            failed = True
            assert "json object" in str(exc).lower() or "malformed json" in str(exc).lower()
        assert failed, f"Expected non-object refusal for direct payload {bad_direct_payload!r}"

    # 7g: Invalid surrogate-containing replacement text rejected before applying edits
    for bad_surrogate_text in ["simp only [\ud800]", "simp only [\udfff]"]:
        failed = False
        try:
            preview(src, _make_payload(src, [{"range": valid_range, "newText": bad_surrogate_text}]))
        except SimpEditError as exc:
            failed = True
            assert "unencodable" in str(exc).lower() or "surrogate" in str(exc).lower()
        assert failed, f"Expected surrogate rejection for {bad_surrogate_text!r}"


# ---------------------------------------------------------------------------
# Control 8: Wrong original macro / by range
# ---------------------------------------------------------------------------
def test_wrong_original_macro_or_by_range() -> None:
    src = (
        "theorem t : True := by\n"
        "  simp?\n"
    ).encode("utf-8")

    # 8a: Enclosing by-block range
    # Replaced span: "by\n  simp?"
    by_edit = {
        "range": {"start": {"line": 0, "character": 20}, "end": {"line": 1, "character": 7}},
        "newText": "simp only []",
    }
    failed = False
    try:
        preview(src, _make_payload(src, [by_edit]))
    except SimpEditError as exc:
        failed = True
        assert "question-family" in str(exc).lower()
    assert failed, "Expected enclosing by-block refusal"

    # 8b: Zero-length range (insertion)
    zero_edit = {
        "range": {"start": {"line": 1, "character": 2}, "end": {"line": 1, "character": 2}},
        "newText": "simp only []",
    }
    failed = False
    try:
        preview(src, _make_payload(src, [zero_edit]))
    except SimpEditError as exc:
        failed = True
        assert "zero-length" in str(exc).lower()
    assert failed, "Expected zero-length range refusal"

    # 8c: Backwards range
    back_edit = {
        "range": {"start": {"line": 1, "character": 7}, "end": {"line": 1, "character": 2}},
        "newText": "simp only []",
    }
    failed = False
    try:
        preview(src, _make_payload(src, [back_edit]))
    except SimpEditError as exc:
        failed = True
        assert "backwards" in str(exc).lower()
    assert failed, "Expected backwards range refusal"

    # 8d: Non-question tactic replaced: "simp [h]"
    src_non_q = b"  simp [h]\n"
    edit_non_q = {
        "range": {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 10}},
        "newText": "simp only [h]",
    }
    failed = False
    try:
        preview(src_non_q, _make_payload(src_non_q, [edit_non_q]))
    except SimpEditError as exc:
        failed = True
        assert "question-family" in str(exc).lower()
    assert failed, "Expected non-question tactic refusal"


# ---------------------------------------------------------------------------
# Control 9: Wrong replacement family / implicit replacement refusal
# ---------------------------------------------------------------------------
def test_wrong_replacement_family_or_implicit() -> None:
    src = b"  simp?\n"
    r = {"start": {"line": 0, "character": 2}, "end": {"line": 0, "character": 7}}

    # 9a: Mismatched family (dsimp replacing simp?)
    failed = False
    try:
        preview(src, _make_payload(src, [{"range": r, "newText": "dsimp only []"}]))
    except SimpEditError as exc:
        failed = True
        assert "family" in str(exc).lower()
    assert failed, "Expected family mismatch refusal"

    # 9b: Implicit replacement (missing 'only')
    failed = False
    try:
        preview(src, _make_payload(src, [{"range": r, "newText": "simp [foo]"}]))
    except SimpEditError as exc:
        failed = True
        assert "only" in str(exc).lower()
    assert failed, "Expected implicit replacement refusal (missing 'only')"

    # 9c: Malformed config flag / missing explicit only refusal
    failed = False
    try:
        preview(src, _make_payload(src, [{"range": r, "newText": "simp + only []"}]))
    except SimpEditError as exc:
        failed = True
        msg = str(exc).lower()
        assert "only" in msg or "config flag" in msg
    assert failed, "Expected refusal for malformed flag or missing explicit only"

    # Also verify non-identifier config flag syntax
    failed = False
    try:
        preview(src, _make_payload(src, [{"range": r, "newText": "simp +* only []"}]))
    except SimpEditError as exc:
        failed = True
        assert "config flag" in str(exc).lower()
    assert failed, "Expected invalid flag syntax refusal"

    # 9d: Unterminated configuration parenthesis
    failed = False
    try:
        preview(src, _make_payload(src, [{"range": r, "newText": "simp (config := {zeta := false} only []"}]))
    except SimpEditError as exc:
        failed = True
        assert "parenthesis" in str(exc).lower()
    assert failed, "Expected unterminated paren refusal"

    # 9e: Replacement tactic head still contains question mark
    failed = False
    try:
        preview(src, _make_payload(src, [{"range": r, "newText": "simp? only []"}]))
    except SimpEditError as exc:
        failed = True
        assert "recognized simp-family" in str(exc).lower() or "only" in str(exc).lower()
    assert failed, "Expected question-mark replacement refusal"


# ---------------------------------------------------------------------------
# Control 10: Source input stays byte-identical regardless of success/failure
# ---------------------------------------------------------------------------
def test_source_input_stays_byte_identical() -> None:
    src_content = b"import Blanc\r\ntheorem t : True := by\r\n  simp?\r\n"
    initial_sha = hashlib.sha256(src_content).hexdigest()

    with tempfile.NamedTemporaryFile("wb", suffix=".lean", delete=False) as f_src:
        f_src.write(src_content)
        src_path = Path(f_src.name)

    valid_payload = _make_payload(src_content, [
        {"range": {"start": {"line": 2, "character": 2}, "end": {"line": 2, "character": 7}},
         "newText": "simp only []"}
    ])
    invalid_payload = _make_payload(src_content, [
        {"range": {"start": {"line": 2, "character": 2}, "end": {"line": 2, "character": 7}},
         "newText": "dsimp only []"}  # Wrong family failure
    ])

    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f_val:
        json.dump(valid_payload, f_val)
        val_path = Path(f_val.name)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f_inval:
        json.dump(invalid_payload, f_inval)
        inval_path = Path(f_inval.name)

    cli_script = str(Path(__file__).resolve().parent / "simp_edits.py")

    try:
        # Run preview success
        preview(src_content, valid_payload)
        assert src_path.read_bytes() == src_content
        assert hashlib.sha256(src_path.read_bytes()).hexdigest() == initial_sha

        # Run CLI success
        p1 = subprocess.run([sys.executable, cli_script, str(src_path), str(val_path)], capture_output=True)
        assert p1.returncode == 0
        assert src_path.read_bytes() == src_content
        assert hashlib.sha256(src_path.read_bytes()).hexdigest() == initial_sha

        # Run preview failure
        try:
            preview(src_content, invalid_payload)
        except SimpEditError:
            pass
        assert src_path.read_bytes() == src_content
        assert hashlib.sha256(src_path.read_bytes()).hexdigest() == initial_sha

        # Run CLI failure
        p2 = subprocess.run([sys.executable, cli_script, str(src_path), str(inval_path)], capture_output=True)
        assert p2.returncode == 1
        assert src_path.read_bytes() == src_content
        assert hashlib.sha256(src_path.read_bytes()).hexdigest() == initial_sha
    finally:
        src_path.unlink(missing_ok=True)
        val_path.unlink(missing_ok=True)
        inval_path.unlink(missing_ok=True)


def main() -> int:
    tests = [
        ("Control 1: synthetic three-edit ASCII preview", test_synthetic_three_edit_ascii_preview),
        ("Control 2: UTF16 astral and ordinary Unicode offsets", test_utf16_astral_and_ordinary_unicode),
        ("Control 3: CRLF and trailing newline/EOF", test_crlf_and_eof),
        ("Control 4: duplicate identical edits", test_duplicate_identical_edits),
        ("Control 5: divergent same-span and partial-overlap refusal", test_divergent_same_span_and_partial_overlap),
        ("Control 6: hash mismatch", test_hash_mismatch),
        ("Control 7: malformed positions/UTF8/payload", test_malformed_positions_and_utf8),
        ("Control 8: wrong original macro/by range", test_wrong_original_macro_or_by_range),
        ("Control 9: wrong replacement family/implicit replacement refusal", test_wrong_replacement_family_or_implicit),
        ("Control 10: source input byte-identical stability", test_source_input_stays_byte_identical),
    ]

    print("=== Running Lean TryThisInfo Simp Edits Preview Test Suite ===")
    passed = 0
    for name, test_fn in tests:
        try:
            test_fn()
            print(f"PASS: {name}")
            passed += 1
        except Exception as exc:
            print(f"FAIL: {name}: {exc}")
            traceback.print_exc()

    print(f"\nResult: {passed}/{len(tests)} tests passed.")
    if passed == len(tests):
        print("OK: All simp-edits focused controls passed.")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
