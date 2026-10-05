#!/usr/bin/env python3
"""Table-driven test suite for pure-Python simplification planner and reconciliation.

Tests:
1. Real three-site Basic shape (synthetic bytes labelled synthetic).
2. Unicode/CRLF and earlier head insertions shifting later ranges.
3. Preserved at*/using/tails across tactic families.
4. Only-sites unchanged and uninstrumented.
5. Malformed payloads, invalid schema, ranges, bounds, and hash mismatches fail closed.
6. Unrelated TryThis suggestions separated as unresolved rows.
7. Missing/dormant sites separated as unresolved rows.
8. Same-span identical duplicate deduplication vs divergent alternatives.
9. Wrong command and reference range ownership rejection.
10. Quoted dormant site unresolved.
11. Unavailable/unproven bang heads produce explicit unsupported diagnostic.
12. Existing question forms handled faithfully.
13. Overlapping site ranges rejected.
14. CLI execution for instrument and reconcile.
15. Explicit per-site observed unions preserve native alternatives and reject
    malformed selections, complex terms, and wrong ownership.

Run with: PYTHONDONTWRITEBYTECODE=1 python3 scripts/test-simp-migration.py
"""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Tuple

from simp_edits import parse_lean_lines
from simp_migration import (
    MigrationError,
    codepoint_to_lsp_pos,
    instrument,
    main as migration_main,
    reconcile,
)


def make_site(
    text: str, sub: str, head: str, family: str = "simp", only: bool = False, cmd_lines: Tuple[int, int] = None
) -> Dict[str, Any]:
    lines = parse_lean_lines(text)
    s_cp = text.index(sub)
    l_idx = codepoint_to_lsp_pos(lines, s_cp)["line"]
    c_s_l, c_e_l = cmd_lines if cmd_lines else (l_idx, l_idx)
    return {
        "family": family, "head": head, "only": only,
        "range": {"start": codepoint_to_lsp_pos(lines, s_cp), "end": codepoint_to_lsp_pos(lines, s_cp + len(sub))},
        "headRange": {"start": codepoint_to_lsp_pos(lines, s_cp), "end": codepoint_to_lsp_pos(lines, s_cp + len(head))},
        "commandRange": {
            "start": {"line": c_s_l, "character": 0},
            "end": {"line": c_e_l, "character": lines[c_e_l].u16_length},
        },
        "source": sub,
    }


def make_baseline(source_bytes: bytes, sites: List[Dict[str, Any]], module: str = "Blanc.Basic") -> Dict[str, Any]:
    sha = hashlib.sha256(source_bytes).hexdigest()
    return {
        "schema": 1, "source_sha256": sha, "original_sha256": sha,
        "setup_sha256": hashlib.sha256(b"dummy_setup").hexdigest(),
        "module": module, "original_path": "Blanc/Basic.lean", "setup_path": "lake-setup.json",
        "inventory": sites, "edits": [],
    }


def make_q_col(plan: Dict[str, Any], inv: List[Dict[str, Any]] = None, edits: List[Dict[str, Any]] = None) -> Dict[str, Any]:
    if inv is None:
        inv = [
            {
                "family": s["family"], "head": s["instrumented_head"], "only": s["only"],
                "range": s["mapped_range"], "headRange": s["mapped_head_range"],
                "commandRange": s["mapped_command_range"], "source": s["mapped_source"],
            }
            for s in plan["sites"]
        ]
    return {
        "schema": 1, "source_sha256": plan["source_sha256"], "original_sha256": plan["original_sha256"],
        "setup_sha256": plan["setup_sha256"], "module": plan["module"],
        "original_path": plan.get("original_path", ""), "setup_path": plan.get("setup_path", ""),
        "inventory": inv, "edits": edits if edits is not None else [],
    }


def make_edit(s_plan: Dict[str, Any], new_text: str, decl: str = None) -> Dict[str, Any]:
    ed = {
        "range": s_plan["mapped_range"], "newText": new_text,
        "referenceRange": s_plan["mapped_range"], "commandRange": s_plan["mapped_command_range"],
    }
    if decl:
        ed["parentDeclaration"] = decl
    return ed


# --- Test 1: Real three-site Basic shape (synthetic bytes labelled synthetic)
def test_basic_shape_synthetic() -> None:
    text = (
        "-- SYNTHETIC: Basic shape test\n"
        "theorem pref_trans : (x <<+ xy) → (xy <<+ xyz) → (x <<+ xyz) := by\n"
        "  simp [pref_iff_isPrefix]; apply List.IsPrefix.trans\n\n"
        "theorem append_split (h : x <++ xyz ++> yz) : (x ++ y) <++ xyz ++> z := by\n"
        "  simp [Split, List.append_assoc] at *; rw [h]\n\n"
        "theorem of_append_split (h : x <++ xyz ++> yz) : (y <++ yz ++> z) := by\n"
        "  simp only [Split, List.append_assoc] at *; rfl\n"
    )
    b = text.encode("utf-8")
    s0 = make_site(text, "simp [pref_iff_isPrefix]", "simp", cmd_lines=(1, 2))
    s1 = make_site(text, "simp [Split, List.append_assoc] at *", "simp", cmd_lines=(4, 5))
    s2 = make_site(text, "simp only [Split, List.append_assoc] at *", "simp", only=True, cmd_lines=(7, 8))
    inst = instrument(b, make_baseline(b, [s0, s1, s2]))
    assert inst.plan["target_count"] == 2 and inst.plan["only_count"] == 1
    ed0 = make_edit(inst.plan["sites"][0], "simp only [pref_iff_isPrefix]", "Blanc.pref_trans")
    ed1 = make_edit(inst.plan["sites"][1], "simp only [Split, List.append_assoc] at *", "Blanc.append_split")
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[ed0, ed1]))
    assert rec.complete and rec.applied_edits == 2 and "rfl" in rec.candidate_source


# --- Test 2: Unicode/CRLF and earlier head insertions shifting later ranges
def test_unicode_crlf_and_earlier_head_insertions() -> None:
    text = "theorem thm (𝔸 : Type) : True := by simp; simp\r\n"
    b = text.encode("utf-8")
    lines = parse_lean_lines(text)
    s0_cp, s1_cp = text.index("simp"), text.index("simp", text.index("simp") + 4)
    cmd = {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": lines[0].u16_length}}
    s0 = {"family": "simp", "head": "simp", "only": False, "range": {"start": codepoint_to_lsp_pos(lines, s0_cp), "end": codepoint_to_lsp_pos(lines, s0_cp + 4)}, "headRange": {"start": codepoint_to_lsp_pos(lines, s0_cp), "end": codepoint_to_lsp_pos(lines, s0_cp + 4)}, "commandRange": cmd, "source": "simp"}
    s1 = {"family": "simp", "head": "simp", "only": False, "range": {"start": codepoint_to_lsp_pos(lines, s1_cp), "end": codepoint_to_lsp_pos(lines, s1_cp + 4)}, "headRange": {"start": codepoint_to_lsp_pos(lines, s1_cp), "end": codepoint_to_lsp_pos(lines, s1_cp + 4)}, "commandRange": cmd, "source": "simp"}
    inst = instrument(b, make_baseline(b, [s0, s1]))
    assert inst.plan["sites"][1]["mapped_range"]["start"]["character"] == 44
    ed0, ed1 = make_edit(inst.plan["sites"][0], "simp only [h1]"), make_edit(inst.plan["sites"][1], "simp only [h2]")
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[ed0, ed1]))
    assert rec.complete and rec.applied_edits == 2 and "by simp only [h1]; simp only [h2]\r\n" in rec.candidate_source


# --- Test 3: Preserved tails, at*, using across families
def test_preserved_tails_at_using() -> None:
    text = (
        "theorem t1 : True := by simp at *\n"
        "theorem t2 : True := by simpa using h\n"
        "theorem t3 : True := by dsimp [a, b]\n"
        "theorem t4 : True := by simp_all [c] at h1 h2\n"
    )
    b = text.encode("utf-8")
    s1, s2 = make_site(text, "simp at *", "simp"), make_site(text, "simpa using h", "simpa", family="simpa")
    s3, s4 = make_site(text, "dsimp [a, b]", "dsimp", family="dsimp"), make_site(text, "simp_all [c] at h1 h2", "simp_all", family="simp_all")
    inst = instrument(b, make_baseline(b, [s1, s2, s3, s4]))
    src = inst.instrumented_bytes.decode("utf-8")
    assert "simp? at *" in src and "simpa? using h" in src and "dsimp? [a, b]" in src and "simp_all? [c] at h1 h2" in src


# --- Test 4: Only-sites unchanged
def test_only_sites_unchanged() -> None:
    text = "theorem t : True := by simp only [h]; simpa only using h\n"
    b = text.encode("utf-8")
    s1, s2 = make_site(text, "simp only [h]", "simp", only=True), make_site(text, "simpa only using h", "simpa", family="simpa", only=True)
    inst = instrument(b, make_baseline(b, [s1, s2]))
    assert inst.instrumented_bytes == b and inst.plan["target_count"] == 0 and inst.plan["only_count"] == 2
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[]))
    assert rec.complete and rec.applied_edits == 0 and rec.candidate_bytes == b


# --- Test 5: Table-driven malformed payloads, ranges, bounds, hashes, and tampering
def test_malformed_payloads_ranges_hashes() -> None:
    text = "theorem t : True := by simp [h]\n"
    b = text.encode("utf-8")
    s = make_site(text, "simp [h]", "simp")
    inst = instrument(b, make_baseline(b, [s]))
    s_plan = inst.plan["sites"][0]

    # Baseline & instrument validation controls
    inst_cases = [
        ("non-utf8 bytes", b"\xff\xfe", lambda c: c, "not valid utf-8"),
        ("bad schema version", b, lambda c: {**c, "schema": 2}, "invalid schema"),
        ("bool schema version", b, lambda c: {**c, "schema": True}, "invalid schema"),
        ("orig sha mismatch", b, lambda c: {**c, "original_sha256": "0" * 64}, "original sha256 mismatch"),
        ("src sha mismatch in baseline", b, lambda c: {**c, "source_sha256": "1" * 64}, "baseline source sha256 mismatch"),
        ("missing module", b, lambda c: {**c, "module": ""}, "invalid or missing 'module'"),
        ("null character in range", b, lambda c: {**c, "inventory": [{**s, "range": {"start": {"line": 0, "character": None}, "end": {"line": 0, "character": 27}}}]}, "invalid integer position"),
        ("bool line in range", b, lambda c: {**c, "inventory": [{**s, "range": {"start": {"line": True, "character": 23}, "end": {"line": 0, "character": 27}}}]}, "invalid integer position"),
        ("backwards range", b, lambda c: {**c, "inventory": [{**s, "range": {"start": {"line": 0, "character": 27}, "end": {"line": 0, "character": 23}}}]}, "backwards range"),
        ("zero length range", b, lambda c: {**c, "inventory": [{**s, "range": {"start": {"line": 0, "character": 23}, "end": {"line": 0, "character": 23}}}]}, "zero-length"),
        ("source mismatch", b, lambda c: {**c, "inventory": [{**s, "source": "wrong"}]}, "source mismatch"),
        ("head mismatch", b, lambda c: {**c, "inventory": [{**s, "head": "simp?"}]}, "head mismatch"),
        ("inconsistent family and head", b, lambda c: {**c, "inventory": [{**s, "family": "dsimp", "head": "simp"}]}, "inconsistent with family"),
        ("falsely marking bare simp as only", b, lambda c: {**c, "inventory": [{**s, "only": True}]}, "disagrees with source explicit-only syntax"),
    ]
    for name, sb, mod_fn, err_sub in inst_cases:
        try:
            instrument(sb, mod_fn(make_baseline(sb, [s])))
            assert False, f"Expected MigrationError for {name}"
        except MigrationError as exc:
            assert err_sub in str(exc).lower(), f"{name}: expected {err_sub!r} in {str(exc)!r}"

    # Plan tampering & question collector controls (reconcile failures)
    rec_err_cases = [
        ("integer plan target", lambda p: {**p, "sites": [{**p["sites"][0], "target": 1}]}, None, "does not match deterministically derived plan"),
        ("bool target_count", lambda p: {**p, "target_count": True}, None, "does not match deterministically derived plan"),
        ("altered plan target", lambda p: {**p, "sites": [{**p["sites"][0], "target": False}]}, None, "does not match deterministically derived plan"),
        ("altered plan only", lambda p: {**p, "sites": [{**p["sites"][0], "only": True}]}, None, "disagrees with source explicit-only syntax"),
        ("altered plan only_count", lambda p: {**p, "only_count": 99}, None, "does not match deterministically derived plan"),
        ("altered mapped_range", lambda p: {**p, "sites": [{**p["sites"][0], "mapped_range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}}}]}, None, "does not match deterministically derived plan"),
        ("altered target_count", lambda p: {**p, "target_count": 99}, None, "does not match deterministically derived plan"),
        ("duplicate site_id in plan", lambda p: {**p, "sites": [p["sites"][0], {**p["sites"][0], "site_id": p["sites"][0]["site_id"]}]}, None, "duplicate site_id"),
        ("missing field in plan site", lambda p: {**p, "sites": [{"site_id": "site_0"}]}, None, "missing required field"),
        ("invalid Unicode newText", lambda p: p, lambda q: {**q, "edits": [{**make_edit(s_plan, "simp only [h]"), "newText": "simp only [\ud800]"}]}, "invalid unicode"),
        ("non-string newText", lambda p: p, lambda q: {**q, "edits": [{**make_edit(s_plan, "simp only [h]"), "newText": 123}]}, "must be a string"),
        ("q_col bool schema", lambda p: p, lambda q: {**q, "schema": True}, "invalid question collector schema"),
        ("q_col source_sha mismatch", lambda p: p, lambda q: {**q, "source_sha256": "0" * 64}, "source_sha256 mismatch"),
    ]
    for name, p_mod, q_mod, err_sub in rec_err_cases:
        p = p_mod(copy.deepcopy(inst.plan))
        q = q_mod(make_q_col(inst.plan, edits=[make_edit(s_plan, "simp only [h]")])) if q_mod else make_q_col(inst.plan, edits=[make_edit(s_plan, "simp only [h]")])
        try:
            reconcile(b, p, q)
            assert False, f"Expected MigrationError for {name}"
        except MigrationError as exc:
            assert err_sub in str(exc).lower(), f"{name}: expected {err_sub!r} in {str(exc)!r}"

    # Question inventory comparison controls (unresolved)
    q_inv_cases = [
        ("duplicate range in q_inv", lambda inv: inv + [copy.deepcopy(inv[0])], "inventory_mismatch"),
        ("unexpected extra site in q_inv", lambda inv: inv + [{**copy.deepcopy(inv[0]), "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 5}}}], "inventory_mismatch"),
        ("headRange mismatch in q_inv", lambda inv: [{**inv[0], "headRange": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 4}}}], "inventory_mismatch"),
        ("commandRange mismatch in q_inv", lambda inv: [{**inv[0], "commandRange": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 10}}}], "inventory_mismatch"),
        ("source mismatch in q_inv", lambda inv: [{**inv[0], "source": "wrong_src"}], "inventory_mismatch"),
        ("only bool mismatch in q_inv", lambda inv: [{**inv[0], "only": True}], "inventory_mismatch"),
    ]
    for name, inv_mod, reason in q_inv_cases:
        base_inv = [{
            "family": s_plan["family"], "head": s_plan["instrumented_head"], "only": s_plan["only"],
            "range": s_plan["mapped_range"], "headRange": s_plan["mapped_head_range"],
            "commandRange": s_plan["mapped_command_range"], "source": s_plan["mapped_source"],
        }]
        q = make_q_col(inst.plan, inv=inv_mod(base_inv), edits=[make_edit(s_plan, "simp only [h]")])
        rec = reconcile(b, inst.plan, q)
        assert not rec.complete and any(u["reason"] == reason for u in rec.unresolved)


# --- Test 6: Unrelated action separated as unresolved
def test_unrelated_action() -> None:
    text = "theorem t : True := by simp\n"
    b = text.encode("utf-8")
    inst = instrument(b, make_baseline(b, [make_site(text, "simp", "simp")]))
    bad_ed = {**make_edit(inst.plan["sites"][0], "simp only"), "newText": "exact trivial"}
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[bad_ed]))
    assert not rec.complete and rec.candidate_source is None and any(u["reason"] == "unrelated_suggestion" for u in rec.unresolved)


# --- Test 7: Missing / dormant site
def test_missing_site() -> None:
    text = "theorem t : True := by simp\n"
    b = text.encode("utf-8")
    inst = instrument(b, make_baseline(b, [make_site(text, "simp", "simp")]))
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[]))
    assert not rec.complete and rec.candidate_source is None and any(u["reason"] == "missing_site" for u in rec.unresolved)


# --- Test 8: Same-span identical duplicate vs divergent alternatives
def test_same_span_duplicate_vs_alternative() -> None:
    text = "theorem t : True := by simp\n"
    b = text.encode("utf-8")
    inst = instrument(b, make_baseline(b, [make_site(text, "simp", "simp")]))
    s0 = inst.plan["sites"][0]
    ed1, ed2 = make_edit(s0, "simp only [h]", "declA"), make_edit(s0, "simp only [h]", "declB")
    rec_dup = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[ed1, ed2]))
    assert rec_dup.complete and rec_dup.resolved[0]["duplicate_count"] == 2 and len(rec_dup.resolved[0]["attributions"]) == 2
    ed_alt1, ed_alt2 = make_edit(s0, "simp only [h1]"), make_edit(s0, "simp only [h2]")
    rec_alt = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[ed_alt1, ed_alt2]))
    assert not rec_alt.complete and any(u["reason"] == "divergent_alternatives" for u in rec_alt.unresolved)


def test_observed_per_site_union() -> None:
    text = 'theorem t : True := by simp_all\n'
    original = text.encode()
    inst = instrument(original, make_baseline(original, [make_site(text, 'simp_all', 'simp_all', family='simp_all')]))
    site = inst.plan['sites'][0]
    edits = [make_edit(site, s) for s in ['simp_all only', 'simp_all only [A, B]', 'simp_all only [B, C]']]
    collector = make_q_col(inst.plan, edits=edits)
    assert not reconcile(original, inst.plan, collector).complete
    result = reconcile(original, inst.plan, collector, observed_union_sites=['site_0'])
    assert result.complete and result.candidate_source.endswith('simp_all only [A, B, C]\n')
    resolved = result.resolved[0]
    assert resolved['used_lemma_union'] == ['A', 'B', 'C']
    assert resolved['alternatives'] == [e['newText'] for e in edits]
    assert resolved['replay_required'] is True and len(resolved['attributions']) == 3
    for bad_text in ['simp_all only [*]', 'simp_all only [f x]', 'simp_all (config := {}) only [A]']:
        bad = make_q_col(inst.plan, edits=[edits[0], make_edit(site, bad_text)])
        try:
            reconcile(original, inst.plan, bad, observed_union_sites=['site_0'])
        except MigrationError:
            pass
        else:
            raise AssertionError('Union accepted non-simple-name alternatives')
    for request in [['site_99'], ['site_0', 'site_0'], [True], 'site_0']:
        try:
            reconcile(original, inst.plan, collector, observed_union_sites=request)
        except MigrationError:
            pass
        else:
            raise AssertionError('Union accepted malformed/unknown site selection')
    wrong_owner = copy.deepcopy(collector)
    wrong_owner['edits'][1]['referenceRange'] = {'start': {'line': 0, 'character': 0}, 'end': {'line': 0, 'character': 3}}
    assert not reconcile(original, inst.plan, wrong_owner, observed_union_sites=['site_0']).complete
    from simp_migration import _observed_union
    text, names = _observed_union('simp', [
        {'newText':'simp only [A,\n  B] at h ⊢'},
        {'newText':'simp only [B,C] at\n h   ⊢'}])
    assert text == 'simp only [A, B, C] at h ⊢' and names == ['A','B','C']
    for alternatives in [
        ['simp only [A] at h','simp only [B] at k'],
        ['simp only [A] at h','simp only [B]'],
        ['simp only [A] at h; trivial','simp only [B] at h'],
        ['simp only [A,]','simp only [B]'],
        ['simpa only [A] using h','simpa only [B] using h'],
        ['simp only [↓↓A]','simp only [B]'],
        ['simp only [↓(A)]','simp only [B]'],
        ['simp only [←A]','simp only [B]']]:
        try: _observed_union(alternatives[0].split()[0],[{'newText':t} for t in alternatives])
        except MigrationError: pass
        else: raise AssertionError('Union accepted incompatible tail or non-name')
    text,names=_observed_union('simp_all',[{'newText':'simp_all only [↓reduceIte, getElem?_pos]'},
                                        {'newText':'simp_all only [head?_nil,\n getElem?_pos]'}])
    assert names==['↓reduceIte','getElem?_pos','head?_nil']
    assert text=='simp_all only [↓reduceIte, getElem?_pos, head?_nil]'


# --- Test 9: Wrong command and reference range ownership
def test_wrong_command_reference_ownership() -> None:
    text = "theorem t1 : True := by simp\ntheorem t2 : True := by simp\n"
    b = text.encode("utf-8")
    lines = parse_lean_lines(text)
    cmd1 = {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": lines[0].u16_length}}
    cmd2 = {"start": {"line": 1, "character": 0}, "end": {"line": 1, "character": lines[1].u16_length}}
    s1 = {"family": "simp", "head": "simp", "only": False, "range": {"start": {"line": 0, "character": 24}, "end": {"line": 0, "character": 28}}, "headRange": {"start": {"line": 0, "character": 24}, "end": {"line": 0, "character": 28}}, "commandRange": cmd1, "source": "simp"}
    s2 = {"family": "simp", "head": "simp", "only": False, "range": {"start": {"line": 1, "character": 24}, "end": {"line": 1, "character": 28}}, "headRange": {"start": {"line": 1, "character": 24}, "end": {"line": 1, "character": 28}}, "commandRange": cmd2, "source": "simp"}
    inst = instrument(b, make_baseline(b, [s1, s2]))
    m_rng1 = inst.plan["sites"][0]["mapped_range"]
    m_cmd1, m_cmd2 = inst.plan["sites"][0]["mapped_command_range"], inst.plan["sites"][1]["mapped_command_range"]

    # Wrong commandRange:
    bad_cmd = {"range": m_rng1, "newText": "simp only [h]", "referenceRange": m_rng1, "commandRange": m_cmd2}
    assert not reconcile(b, inst.plan, make_q_col(inst.plan, edits=[bad_cmd])).complete
    # Wrong referenceRange with RIGHT edit range:
    bad_ref = {"range": m_rng1, "newText": "simp only [h]", "referenceRange": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 5}}, "commandRange": m_cmd1}
    assert not reconcile(b, inst.plan, make_q_col(inst.plan, edits=[bad_ref])).complete
    # Null referenceRange with RIGHT edit range:
    none_ref = {"range": m_rng1, "newText": "simp only [h]", "referenceRange": None, "commandRange": m_cmd1}
    assert not reconcile(b, inst.plan, make_q_col(inst.plan, edits=[none_ref])).complete
    good = [make_edit(s, "simp only [h]") for s in inst.plan["sites"]]
    assert reconcile(b, inst.plan, make_q_col(inst.plan, edits=good)).complete
    for field in ("range", "referenceRange", "commandRange"):
        bad = copy.deepcopy(good)
        bad[0][field]["start"]["line"] = False  # Equals 0 in Python, invalid in LSP.
        assert not reconcile(b, inst.plan, make_q_col(inst.plan, edits=bad)).complete
    q = make_q_col(inst.plan, edits=good)
    for field in ("headRange", "commandRange"):
        bad = copy.deepcopy(q)
        bad["inventory"][0][field]["start"]["line"] = False
        assert not reconcile(b, inst.plan, bad).complete


# --- Test 10: Quoted dormant site unresolved
def test_quoted_dormant_site_unresolved() -> None:
    text = 'macro "my_tac" : tactic => `(tactic| simp)\n'
    b = text.encode("utf-8")
    inst = instrument(b, make_baseline(b, [make_site(text, "simp", "simp")]))
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[]))
    assert not rec.complete and any(u["reason"] == "missing_site" for u in rec.unresolved)


# --- Test 11: Unavailable/unproven bang heads produce explicit unsupported diagnostic
def test_unsupported_bang_heads() -> None:
    text = "theorem t : True := by simp!\n"
    b = text.encode("utf-8")
    try:
        instrument(b, make_baseline(b, [make_site(text, "simp!", "simp!")]))
        assert False, "Expected MigrationError for simp!"
    except MigrationError as exc:
        assert "unavailable/unproven bang heads are not supported" in str(exc)


# --- Test 12: Existing question forms handled faithfully
def test_existing_question_forms() -> None:
    text = "theorem t : True := by simp? [h]\n"
    b = text.encode("utf-8")
    s = make_site(text, "simp? [h]", "simp?")
    inst = instrument(b, make_baseline(b, [s]))
    assert inst.plan["target_count"] == 1 and inst.plan["sites"][0]["instrumented_head"] == "simp?"
    assert inst.instrumented_bytes == b
    ed = make_edit(inst.plan["sites"][0], "simp only [h]")
    rec = reconcile(b, inst.plan, make_q_col(inst.plan, edits=[ed]))
    assert rec.complete and "simp only [h]" in rec.candidate_source


# --- Test 13: Overlapping site ranges rejected
def test_overlapping_site_ranges() -> None:
    text = "theorem t : True := by simp; simp\n"
    b = text.encode("utf-8")
    lines = parse_lean_lines(text)
    cmd = {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": lines[0].u16_length}}
    s1 = {"family": "simp", "head": "simp", "only": False, "range": {"start": {"line": 0, "character": 23}, "end": {"line": 0, "character": 30}}, "headRange": {"start": {"line": 0, "character": 23}, "end": {"line": 0, "character": 27}}, "commandRange": cmd, "source": "simp; s"}
    s2 = {"family": "simp", "head": "simp", "only": False, "range": {"start": {"line": 0, "character": 29}, "end": {"line": 0, "character": 33}}, "headRange": {"start": {"line": 0, "character": 29}, "end": {"line": 0, "character": 33}}, "commandRange": cmd, "source": "simp"}
    try:
        instrument(b, make_baseline(b, [s1, s2]))
        assert False, "Expected MigrationError for overlapping ranges"
    except MigrationError as exc:
        assert "overlapping" in str(exc).lower()
    try: instrument(b, make_baseline(b, [s1, s2]),preserve_nested=True)
    except MigrationError: pass
    else: raise AssertionError('Crossing ranges accepted')
    text='example : True := by simp only [if_neg (by simp)]\nexample : True := by simp\n'
    outer=make_site(text,'simp only [if_neg (by simp)]','simp',only=True)
    inner=make_site(text,'simp)','simp'); inner['source']='simp'; inner['range']['end']['character']-=1
    other=make_site(text,'simp\n','simp'); other['source']='simp'; other['range']['end']={'line':1,'character':25}
    original=text.encode()
    inst=instrument(original,make_baseline(original,[outer,inner,other]),preserve_nested=True)
    assert inst.instrumented_bytes == original[:-5]+b'simp?\n'
    assert inst.plan['target_count']==1
    rec=reconcile(original,inst,make_q_col(inst.plan,edits=[make_edit(inst.plan['sites'][2],'simp only')]))
    assert rec['resolved_count']==1 and rec['unresolved'][0]['reason']=='preserved_nested_group'


# --- Test 14: CLI execution for instrument and reconcile
def test_cli() -> None:
    text = "theorem t : True := by simp [h]\n"
    b = text.encode("utf-8")
    s = make_site(text, "simp [h]", "simp")
    base = make_baseline(b, [s])
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp = Path(tmp_dir)
        sf, bf, pf, qf = tmp / "S.lean", tmp / "base.json", tmp / "plan.json", tmp / "q.json"
        sf.write_bytes(b)
        bf.write_text(json.dumps(base))
        assert migration_main(["instrument", str(sf), str(bf)]) == 0
        inst = instrument(b, base)
        pf.write_text(json.dumps(inst.plan))
        ed = make_edit(inst.plan["sites"][0], "simp only [h]")
        qf.write_text(json.dumps(make_q_col(inst.plan, edits=[ed])))
        assert migration_main(["reconcile", str(sf), str(pf), str(qf)]) == 0


def nested_fixture(outer_only=True):
    """Synthetic native-shaped inventory; no claim of Lean elaboration."""
    outer=('simpa only [outer]' if outer_only else 'simpa [outer]') + ' using (by simpa [middle] using (by simp [leaf]); simp [sibling])'
    text='example (𝔸 : Type) : True := by '+outer+'\r\n'
    bodies=[outer,'simpa [middle] using (by simp [leaf])','simp [leaf]','simp [sibling]']
    sites=[make_site(text,body,'simpa' if i<2 else 'simp',
                     family='simpa' if i<2 else 'simp',only=outer_only and i==0)
           for i,body in enumerate(bodies)]
    return text.encode(),make_baseline(text.encode(),sites)


def test_innermost_selection() -> None:
    for outer_only in (True,False):
        original,baseline=nested_fixture(outer_only)
        legacy=instrument(original,baseline,preserve_nested=True)
        assert legacy.plan['target_count']==0
        inst=instrument(original,baseline,preserve_nested=True,innermost_nested=True)
        assert [s['target'] for s in inst.plan['sites']]==[False,False,True,True]
        assert inst.plan['innermost_nested'] is True
        assert inst.instrumented_bytes==original.replace(b'simp [leaf]',b'simp? [leaf]').replace(b'simp [sibling]',b'simp? [sibling]')
        edits=[make_edit(inst.plan['sites'][i], 'simp only ['+name+']','Fixture.nested')
               for i,name in ((2,'leaf'),(3,'sibling'))]
        result=reconcile(original,inst,make_q_col(inst.plan,edits=edits))
        assert [e['site_id'] for e in result['resolved']]==['site_2','site_3']
        assert {u['site_id'] for u in result['unresolved']}==({'site_1'} if outer_only else {'site_0','site_1'})


def test_innermost_plan_and_owner_refusal() -> None:
    original,baseline=nested_fixture()
    inst=instrument(original,baseline,preserve_nested=True,innermost_nested=True)
    q=make_q_col(inst.plan,edits=[make_edit(inst.plan['sites'][2],'simp only [leaf]')])
    for change in ('target','container','mode','count'):
        p=copy.deepcopy(inst.plan)
        if change=='target':p['sites'][1]['target']=True
        elif change=='container':p['sites'][1].pop('nested_container')
        elif change=='mode':p['innermost_nested']=1
        else:p['target_count']=3
        try:reconcile(original,p,q)
        except MigrationError:pass
        else:raise AssertionError('innermost plan mutation admitted: '+change)
    for owner in ('range','referenceRange','commandRange'):
        bad=copy.deepcopy(q);bad['edits'][0][owner]=inst.plan['sites'][3]['mapped_range']
        assert not reconcile(original,inst,bad)['resolved']
    for mode,preserve in ((True,False),(1,True),('true',True)):
        try:instrument(original,baseline,preserve_nested=preserve,innermost_nested=mode)
        except MigrationError:pass
        else:raise AssertionError('invalid innermost mode admitted')
    bad=copy.deepcopy(baseline)
    bad['inventory'][2]['commandRange']=bad['inventory'][2]['range']
    try:instrument(original,bad,preserve_nested=True,innermost_nested=True)
    except MigrationError as exc:assert 'command owner' in str(exc)
    else:raise AssertionError('nested command owner drift admitted')
    bad=copy.deepcopy(baseline);bad['inventory'].append(copy.deepcopy(bad['inventory'][0]))
    try:instrument(original,bad,preserve_nested=True,innermost_nested=True)
    except MigrationError as exc:assert 'Overlapping' in str(exc)
    else:raise AssertionError('equal-start nested range admitted')


def test_innermost_quotation_refusal() -> None:
    for text in ('macro "quoted" : tactic => `(tactic| simp only [outer (by simp [leaf])])\n',
                 'def quoted := s!"{(← `(tactic| simp only [outer (by simp [leaf])]))}"\n',
                 'def «/-escaped» := `(tactic| simp only [outer (by simp [leaf])])\n'):
        original=text.encode();outer='simp only [outer (by simp [leaf])]';inner='simp [leaf]'
        baseline=make_baseline(original,[make_site(text,outer,'simp',only=True),make_site(text,inner,'simp')])
        inst=instrument(original,baseline,preserve_nested=True,innermost_nested=True)
        assert inst.instrumented_bytes==original and inst.plan['target_count']==0
        q=make_q_col(inst.plan,edits=[make_edit(inst.plan['sites'][1],'simp only [leaf]','Fixture.expansion')])
        res=reconcile(original,inst,q)
        assert not res['resolved'] and any(u['reason']=='quotation_owner_requires_expansion_evidence' for u in res['unresolved'])
    # Literal bytes are never masked, and raw comment backticks conservatively
    # over-refuse. These are named unresolved owners, not completeness credit.
    text='/- `conservative` -/ example : True := by simp only [outer (by simp [leaf])]\n'
    original=text.encode();baseline=make_baseline(original,[make_site(text,'simp only [outer (by simp [leaf])]','simp',only=True),make_site(text,'simp [leaf]','simp')])
    assert instrument(original,baseline,preserve_nested=True,innermost_nested=True).plan['target_count']==0


def run_all_tests() -> int:
    tests = [
        ("test_basic_shape_synthetic", test_basic_shape_synthetic),
        ("test_unicode_crlf_and_earlier_head_insertions", test_unicode_crlf_and_earlier_head_insertions),
        ("test_preserved_tails_at_using", test_preserved_tails_at_using),
        ("test_only_sites_unchanged", test_only_sites_unchanged),
        ("test_malformed_payloads_ranges_hashes", test_malformed_payloads_ranges_hashes),
        ("test_unrelated_action", test_unrelated_action),
        ("test_missing_site", test_missing_site),
        ("test_same_span_duplicate_vs_alternative", test_same_span_duplicate_vs_alternative),
        ("test_observed_per_site_union", test_observed_per_site_union),
        ("test_wrong_command_reference_ownership", test_wrong_command_reference_ownership),
        ("test_quoted_dormant_site_unresolved", test_quoted_dormant_site_unresolved),
        ("test_unsupported_bang_heads", test_unsupported_bang_heads),
        ("test_existing_question_forms", test_existing_question_forms),
        ("test_overlapping_site_ranges", test_overlapping_site_ranges),
        ("test_cli", test_cli),
        ("test_innermost_selection", test_innermost_selection),
        ("test_innermost_plan_and_owner_refusal", test_innermost_plan_and_owner_refusal),
        ("test_innermost_quotation_refusal", test_innermost_quotation_refusal),
    ]

    passed, failed = 0, 0
    print(f"Running {len(tests)} test batteries for simp_migration...")
    for name, test_fn in tests:
        try:
            test_fn()
            print(f"  [PASS] {name}")
            passed += 1
        except Exception as exc:
            print(f"  [FAIL] {name}: {exc}")
            import traceback
            traceback.print_exc()
            failed += 1

    print(f"\nVerdict: {passed} passed, {failed} failed out of {len(tests)} batteries.")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    import sys
    sys.exit(run_all_tests())
