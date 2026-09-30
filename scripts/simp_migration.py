#!/usr/bin/env python3
"""Pure-Python simplification planner and reconciliation for Lean 4 TryThis edits.

Offline two-stage planner:
1. `instrument(original_bytes, baseline_collector)`: Validates schema 1, UTF-8, hashes,
   faithful ranges/heads, instruments non-only simp heads to question forms, returns InstrumentResult.
2. `reconcile(original_bytes, plan, question_collector)`: Reconstructs baseline from plan, re-runs
   instrument for deterministic equivalence, compares all mapped inventory metadata, associates
   TryThis edits by exact tactic/command/ref ownership, applies preview if complete, returns ReconcileResult.

An explicitly requested observed per-site union can reconcile divergent simple-name
alternatives. It preserves all native rows/attributions and remains a proposal
requiring whole-file Lean replay before source application.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Sequence, Tuple, Union

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    from simp_edits import (
        LineInfo,
        PreviewResult,
        REPLACEMENT_HEAD_RE,
        SimpEditError,
        _is_strict_int,
        _resolve_position,
        parse_lean_lines,
        preview,
    )
    from explicit_simp import CONFIG_FLAG_RE, ONLY_RE, balanced_end
except ImportError as exc:
    raise ImportError(f"simp_migration requires simp_edits and explicit_simp: {exc}") from exc


class MigrationError(Exception):
    """Named diagnostic failure during instrumentation, plan validation, or reconciliation."""


class InstrumentResult(NamedTuple):
    instrumented_bytes: bytes
    source_sha256: str
    plan: Dict[str, Any]


class ReconcileResult(dict):
    """Result of Stage 2 reconciliation supporting dict and attribute access."""

    def __getattr__(self, name: str) -> Any:
        try:
            return self[name]
        except KeyError:
            return None


SUPPORTED_FAMILIES = {"simp", "simp_all", "dsimp", "simpa"}
PLAIN_TO_QUESTION_HEAD = {f: f"{f}?" for f in SUPPORTED_FAMILIES}
EXISTING_QUESTION_HEADS = {f"{f}?" for f in SUPPORTED_FAMILIES}
EXPECTED_FAMILY_FOR_HEAD = {f: f for f in SUPPORTED_FAMILIES} | {f"{f}?": f for f in SUPPORTED_FAMILIES}
TACTIC_HEAD_RE = re.compile(r"^(simp_all|simpa|dsimp|simp)(?:[!]+)?(?:\?)?(?![\w.'!?])")


def codepoint_to_lsp_pos(lines: List[LineInfo], cp: int) -> Dict[str, int]:
    """Convert an absolute codepoint offset to an LSP {line, character} dict (UTF-16)."""
    if not lines:
        return {"line": 0, "character": 0}
    lo, hi, best = 0, len(lines) - 1, 0
    while lo <= hi:
        mid = (lo + hi) // 2
        if lines[mid].start_cp <= cp:
            best, lo = mid, mid + 1
        else:
            hi = mid - 1
    li = lines[best]
    rel_cp = max(0, cp - li.start_cp)
    u16_char = li.u16_length if rel_cp >= len(li.content) else sum(2 if ord(c) >= 0x10000 else 1 for c in li.content[:rel_cp])
    return {"line": li.line_index, "character": u16_char}


def _validate_lsp_range(rng: Any, role: str, lines: List[LineInfo]) -> Tuple[int, int]:
    """Strictly validate an LSP range object and return (start_cp, end_cp)."""
    if not isinstance(rng, dict):
        raise MigrationError(f"{role} must be a JSON object")
    start, end = rng.get("start"), rng.get("end")
    if not isinstance(start, dict) or not isinstance(end, dict):
        raise MigrationError(f"{role} missing 'start' or 'end' object")
    for name, val in [
        (f"{role}.start.line", start.get("line")), (f"{role}.start.character", start.get("character")),
        (f"{role}.end.line", end.get("line")), (f"{role}.end.character", end.get("character")),
    ]:
        if not _is_strict_int(val) or val < 0:
            raise MigrationError(f"Invalid integer position for {name}: {val!r}")
    try:
        start_cp = _resolve_position(lines, start["line"], start["character"], f"{role} start")
        end_cp = _resolve_position(lines, end["line"], end["character"], f"{role} end")
    except SimpEditError as exc:
        raise MigrationError(f"{role} position resolution error: {exc}") from exc
    if start_cp > end_cp: raise MigrationError(f"{role} has backwards range (start {start_cp} > end {end_cp})")
    if start_cp == end_cp: raise MigrationError(f"{role} has zero-length synthetic range (start == end == {start_cp})")
    return start_cp, end_cp


def _validate_sha256_hex(val: Any, role: str) -> str:
    """Strictly validate a 64-character lowercase hex SHA256 string."""
    if not isinstance(val, str) or len(val) != 64 or not re.fullmatch(r"[0-9a-fA-F]{64}", val):
        raise MigrationError(f"Invalid SHA256 hex string for {role}: {val!r}")
    return val.lower()


def _parse_json_dict(payload: Any, role: str) -> Dict[str, Any]:
    """Parse JSON string, bytes, or dict into a native Python dictionary."""
    if isinstance(payload, (str, bytes)):
        try:
            val = json.loads(payload)
        except Exception as exc:
            raise MigrationError(f"Malformed JSON payload for {role}: {exc}") from exc
    elif isinstance(payload, dict):
        val = payload
    else:
        raise MigrationError(f"{role} must be a JSON object, string, or bytes (got {type(payload).__name__})")
    if not isinstance(val, dict):
        raise MigrationError(f"{role} top level must be a JSON object")
    return val


def _json_equal(left: Any, right: Any) -> bool:
    """Compare JSON metadata without Python's True == 1 coercion."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return (all(type(k) is str for k in left) and left.keys() == right.keys()
                and all(_json_equal(left[k], right[k]) for k in left))
    if isinstance(left, list):
        return len(left) == len(right) and all(_json_equal(a, b) for a, b in zip(left, right))
    return left == right


def _has_explicit_only(text: str) -> bool:
    """Check if tactic text begins with recognized simp tactic and uses explicit 'only'."""
    stripped = text.lstrip()
    m = TACTIC_HEAD_RE.match(stripped)
    if not m:
        return False
    pos, n = m.end(), len(stripped)
    while pos < n:
        while pos < n and stripped[pos].isspace(): pos += 1
        if pos >= n: break
        if stripped[pos] == "(":
            close = balanced_end(stripped, pos, "(", ")")
            if close < 0: return False
            pos = close + 1
        elif stripped[pos] in ("+", "-"):
            fm = CONFIG_FLAG_RE.match(stripped, pos)
            if not fm: return False
            pos = fm.end()
        else: break
    while pos < n and stripped[pos].isspace(): pos += 1
    return pos < n and bool(ONLY_RE.match(stripped, pos))


def _rng_key(rng: Any) -> Optional[Tuple[int, int, int, int]]:
    """Extract strict integer 4-tuple from LSP range for exact comparison."""
    if isinstance(rng, dict) and isinstance(rng.get("start"), dict) and isinstance(rng.get("end"), dict):
        sl, sc = rng["start"].get("line"), rng["start"].get("character")
        el, ec = rng["end"].get("line"), rng["end"].get("character")
        if _is_strict_int(sl) and _is_strict_int(sc) and _is_strict_int(el) and _is_strict_int(ec):
            return (sl, sc, el, ec)
    return None


def _observed_union(family: str, suggestions: List[Dict[str, Any]]) -> Tuple[str, List[str]]:
    """Propose a per-span union of actual simple-name suggestions, never a global set.

    This narrow shape deliberately rejects configs, local terms, erasures, stars,
    and more elaborate suggestions. A successful preview still needs Lean replay.
    """
    names: List[str] = []
    shape = re.compile(rf"{re.escape(family)} only(?: \[([^\[\]\n]+)\])?")
    identifier = re.compile(r"[A-Za-z_][A-Za-z_0-9'.]*")
    for suggestion in suggestions:
        match = shape.fullmatch(suggestion['newText'])
        if match is None:
            raise MigrationError('Observed union requires plain explicit simple-name suggestions')
        for name in (match.group(1).split(', ') if match.group(1) else []):
            if identifier.fullmatch(name) is None:
                raise MigrationError(f'Observed union rejects non-name simplifier {name!r}')
            if name not in names:
                names.append(name)
    return family + ' only' + (' [' + ', '.join(names) + ']' if names else ''), names


def instrument(
    original_bytes: bytes,
    baseline_collector: Union[Dict[str, Any], str, bytes],
) -> InstrumentResult:
    """Stage 1: Validate baseline and instrument unproven implicit simp heads to question heads."""
    if not isinstance(original_bytes, bytes):
        raise MigrationError("original_bytes must be raw bytes")
    try:
        original_text = original_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MigrationError(f"original_bytes is not valid UTF-8: {exc}") from exc

    actual_original_sha = hashlib.sha256(original_bytes).hexdigest()
    lines = parse_lean_lines(original_text)
    collector = _parse_json_dict(baseline_collector, "baseline_collector")

    schema_val = collector.get("schema")
    if not _is_strict_int(schema_val) or schema_val != 1:
        raise MigrationError(f"Invalid schema version: {schema_val!r} (expected integer 1)")

    orig_sha = _validate_sha256_hex(collector.get("original_sha256"), "baseline original_sha256")
    src_sha = _validate_sha256_hex(collector.get("source_sha256"), "baseline source_sha256")
    if orig_sha != actual_original_sha: raise MigrationError(f"Original SHA256 mismatch: recorded {orig_sha}, actual is {actual_original_sha}")
    if src_sha != actual_original_sha: raise MigrationError(f"Baseline source SHA256 mismatch: expected original {actual_original_sha}, got {src_sha}")

    setup_sha = _validate_sha256_hex(collector.get("setup_sha256"), "baseline setup_sha256")
    module_name = collector.get("module")
    if not isinstance(module_name, str) or not module_name:
        raise MigrationError(f"Invalid or missing 'module' in baseline collector: {module_name!r}")

    original_path, setup_path = collector.get("original_path", ""), collector.get("setup_path", "")
    if not isinstance(original_path, str) or not isinstance(setup_path, str):
        raise MigrationError("baseline 'original_path' and 'setup_path' must be strings")

    raw_inventory = collector.get("inventory")
    if not isinstance(raw_inventory, list):
        raise MigrationError("Missing or non-list 'inventory' in baseline collector")

    parsed_sites: List[Dict[str, Any]] = []
    for idx, item in enumerate(raw_inventory):
        if not isinstance(item, dict):
            raise MigrationError(f"Inventory site {idx} is not an object")
        family = item.get("family")
        if not isinstance(family, str) or family not in SUPPORTED_FAMILIES:
            raise MigrationError(f"Inventory site {idx} has unsupported family: {family!r}")
        head = item.get("head")
        if not isinstance(head, str):
            raise MigrationError(f"Inventory site {idx} has missing or non-string 'head'")
        if "!" in head:
            raise MigrationError(f"Unsupported bang head '{head}' at site {idx}: unavailable/unproven bang heads are not supported")
        if EXPECTED_FAMILY_FOR_HEAD.get(head) != family:
            raise MigrationError(f"Inventory site {idx} head '{head}' is inconsistent with family '{family}'")

        only_val = item.get("only")
        if not isinstance(only_val, bool):
            raise MigrationError(f"Inventory site {idx} 'only' must be a strict boolean (got {type(only_val).__name__})")

        s_cp, e_cp = _validate_lsp_range(item.get("range"), f"Site {idx} range", lines)
        h_s, h_e = _validate_lsp_range(item.get("headRange"), f"Site {idx} headRange", lines)
        c_s, c_e = _validate_lsp_range(item.get("commandRange"), f"Site {idx} commandRange", lines)

        if h_s != s_cp: raise MigrationError(f"Site {idx} headRange start {h_s} does not align with site start {s_cp}")
        if h_e > e_cp: raise MigrationError(f"Site {idx} headRange end {h_e} exceeds site end {e_cp}")
        if not (c_s <= s_cp and e_cp <= c_e): raise MigrationError(f"Site {idx} range [{s_cp}, {e_cp}] is not enclosed within commandRange [{c_s}, {c_e}]")

        src_text = item.get("source")
        if not isinstance(src_text, str): raise MigrationError(f"Site {idx} has missing or non-string 'source'")
        if original_text[s_cp:e_cp] != src_text: raise MigrationError(f"Site {idx} source mismatch: expected {src_text!r}, actual is {original_text[s_cp:e_cp]!r}")
        if original_text[h_s:h_e] != head: raise MigrationError(f"Site {idx} head mismatch: expected {head!r}, actual is {original_text[h_s:h_e]!r}")
        if only_val != _has_explicit_only(src_text): raise MigrationError(f"Site {idx} 'only' flag ({only_val}) disagrees with source explicit-only syntax")

        parsed_sites.append({
            "family": family, "head": head, "only": only_val,
            "range": item["range"], "headRange": item["headRange"], "commandRange": item["commandRange"],
            "source": src_text, "s_cp": s_cp, "e_cp": e_cp, "h_s": h_s, "h_e": h_e, "c_s": c_s, "c_e": c_e,
        })

    parsed_sites.sort(key=lambda s: s["s_cp"])
    for i in range(len(parsed_sites) - 1):
        if parsed_sites[i]["e_cp"] > parsed_sites[i + 1]["s_cp"]:
            raise MigrationError(f"Overlapping site ranges between [{parsed_sites[i]['s_cp']}, {parsed_sites[i]['e_cp']}] and [{parsed_sites[i+1]['s_cp']}, {parsed_sites[i+1]['e_cp']}]")

    for s in parsed_sites:
        if s["only"]:
            s["target"], s["instr_head"] = False, s["head"]
        else:
            s["target"] = True
            s["instr_head"] = s["head"] if s["head"] in EXISTING_QUESTION_HEADS else PLAIN_TO_QUESTION_HEAD[s["head"]]

    pieces, last_cp = [], 0
    for s in parsed_sites:
        pieces.extend([original_text[last_cp:s["h_s"]], s["instr_head"]])
        last_cp = s["h_e"]
    pieces.append(original_text[last_cp:])
    instr_text = "".join(pieces)
    instr_bytes = instr_text.encode("utf-8")
    instr_sha = hashlib.sha256(instr_bytes).hexdigest()
    instr_lines = parse_lean_lines(instr_text)

    def map_cp(cp: int) -> int:
        shift = 0
        for s in parsed_sites:
            delta = len(s["instr_head"]) - (s["h_e"] - s["h_s"])
            if cp <= s["h_s"]: break
            elif cp >= s["h_e"]: shift += delta
            else: return s["h_s"] + shift + len(s["instr_head"])
        return cp + shift

    site_plans = [
        {
            "site_id": f"site_{idx}", "family": s["family"], "head": s["head"], "instrumented_head": s["instr_head"],
            "only": s["only"], "target": s["target"],
            "original_range": s["range"], "original_head_range": s["headRange"], "original_command_range": s["commandRange"], "original_source": s["source"],
            "mapped_range": {"start": codepoint_to_lsp_pos(instr_lines, map_cp(s["s_cp"])), "end": codepoint_to_lsp_pos(instr_lines, map_cp(s["e_cp"]))},
            "mapped_head_range": {"start": codepoint_to_lsp_pos(instr_lines, map_cp(s["h_s"])), "end": codepoint_to_lsp_pos(instr_lines, map_cp(s["h_e"]))},
            "mapped_command_range": {"start": codepoint_to_lsp_pos(instr_lines, map_cp(s["c_s"])), "end": codepoint_to_lsp_pos(instr_lines, map_cp(s["c_e"]))},
            "mapped_source": instr_text[map_cp(s["s_cp"]):map_cp(s["e_cp"])],
        }
        for idx, s in enumerate(parsed_sites)
    ]

    plan: Dict[str, Any] = {
        "schema": 1, "original_sha256": actual_original_sha, "source_sha256": instr_sha, "setup_sha256": setup_sha,
        "module": module_name, "original_path": original_path, "setup_path": setup_path,
        "target_count": sum(1 for s in site_plans if s["target"]), "only_count": sum(1 for s in site_plans if s["only"]),
        "sites": site_plans,
    }
    return InstrumentResult(instr_bytes, instr_sha, plan)


def reconcile(
    original_bytes: bytes,
    plan: Union[Dict[str, Any], InstrumentResult, str, bytes],
    question_collector: Union[Dict[str, Any], str, bytes],
    *, observed_union_sites: Sequence[str] = (),
) -> ReconcileResult:
    """Stage 2: Reconstruct baseline from plan, verify determinism and inventory, reconcile edits."""
    if not isinstance(original_bytes, bytes):
        raise MigrationError("original_bytes must be raw bytes")
    try:
        original_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MigrationError(f"original_bytes is not valid UTF-8: {exc}") from exc

    plan_dict = plan.plan if isinstance(plan, InstrumentResult) else _parse_json_dict(plan, "plan")
    p_schema = plan_dict.get("schema")
    if not _is_strict_int(p_schema) or p_schema != 1:
        raise MigrationError(f"Invalid plan schema version: {p_schema!r} (expected 1)")

    plan_sites = plan_dict.get("sites")
    if not isinstance(plan_sites, list):
        raise MigrationError("Missing or non-list 'sites' in plan")

    seen_site_ids, reconstructed_inv = set(), []
    req_fields = ("family", "head", "only", "original_range", "original_head_range", "original_command_range", "original_source")
    for s in plan_sites:
        if not isinstance(s, dict): raise MigrationError("Plan site entry is not an object")
        sid = s.get("site_id")
        if not isinstance(sid, str) or sid in seen_site_ids: raise MigrationError(f"Invalid or duplicate site_id in plan: {sid!r}")
        seen_site_ids.add(sid)
        if any(k not in s for k in req_fields): raise MigrationError(f"Plan site {sid} missing required fields")
        reconstructed_inv.append({
            "family": s["family"], "head": s["head"], "only": s["only"],
            "range": s["original_range"], "headRange": s["original_head_range"],
            "commandRange": s["original_command_range"], "source": s["original_source"],
        })

    reconstructed_baseline = {
        "schema": 1, "original_sha256": plan_dict.get("original_sha256"), "source_sha256": plan_dict.get("original_sha256"),
        "setup_sha256": plan_dict.get("setup_sha256"), "module": plan_dict.get("module"),
        "original_path": plan_dict.get("original_path", ""), "setup_path": plan_dict.get("setup_path", ""),
        "inventory": reconstructed_inv,
    }

    derived_res = instrument(original_bytes, reconstructed_baseline)
    if not _json_equal(derived_res.plan, plan_dict):
        raise MigrationError("Supplied plan does not match deterministically derived plan")

    q_dict = _parse_json_dict(question_collector, "question_collector")
    q_schema = q_dict.get("schema")
    if not _is_strict_int(q_schema) or q_schema != 1:
        raise MigrationError(f"Invalid question collector schema version: {q_schema!r} (expected 1)")

    for k, exp in [("original_sha256", derived_res.plan["original_sha256"]), ("source_sha256", derived_res.source_sha256), ("setup_sha256", derived_res.plan["setup_sha256"])]:
        if _validate_sha256_hex(q_dict.get(k), f"q_col {k}") != exp:
            raise MigrationError(f"Question collector {k} mismatch")
    if q_dict.get("module") != derived_res.plan["module"]:
        raise MigrationError("Question collector module mismatch")

    q_inventory, q_edits = q_dict.get("inventory"), q_dict.get("edits")
    if not isinstance(q_inventory, list) or not isinstance(q_edits, list):
        raise MigrationError("Missing or non-list 'inventory' or 'edits' in question collector")

    unresolved: List[Dict[str, Any]] = []

    if len(q_inventory) != len(derived_res.plan["sites"]):
        unresolved.append({"reason": "inventory_mismatch", "details": f"Question collector inventory count ({len(q_inventory)}) != plan sites ({len(derived_res.plan['sites'])})"})

    seen_q_ranges, q_inv_by_range = set(), {}
    for idx, item in enumerate(q_inventory):
        if not isinstance(item, dict):
            unresolved.append({"reason": "inventory_mismatch", "details": f"Question inventory entry {idx} is not an object"})
            continue
        rk = _rng_key(item.get("range"))
        if rk is None:
            unresolved.append({"reason": "inventory_mismatch", "details": f"Question inventory entry {idx} has invalid range"})
            continue
        if rk in seen_q_ranges:
            unresolved.append({"reason": "inventory_mismatch", "details": f"Duplicate range in question inventory: {rk}"})
        seen_q_ranges.add(rk)
        q_inv_by_range[rk] = item

    for s in derived_res.plan["sites"]:
        rk = _rng_key(s["mapped_range"])
        match = q_inv_by_range.get(rk)
        if not match:
            unresolved.append({"reason": "inventory_mismatch", "site_id": s["site_id"], "details": f"Planned site {s['site_id']} missing from question inventory"})
            continue
        for k, expected in [
            ("headRange", s["mapped_head_range"]), ("commandRange", s["mapped_command_range"]),
            ("source", s["mapped_source"]), ("family", s["family"]), ("head", s["instrumented_head"]),
        ]:
            if not _json_equal(match.get(k), expected):
                unresolved.append({"reason": "inventory_mismatch", "site_id": s["site_id"], "details": f"{k} mismatch"})
        if not isinstance(match.get("only"), bool) or match.get("only") is not s["only"]:
            unresolved.append({"reason": "inventory_mismatch", "site_id": s["site_id"], "details": "only bool mismatch"})

    plan_site_ranges = {_rng_key(s["mapped_range"]) for s in derived_res.plan["sites"]}
    for rk in seen_q_ranges:
        if rk not in plan_site_ranges:
            unresolved.append({"reason": "inventory_mismatch", "details": f"Unexpected inventory item at range {rk}"})

    target_sites = [s for s in derived_res.plan["sites"] if s["target"]]
    if (isinstance(observed_union_sites, (str, bytes)) or
            any(type(site) is not str for site in observed_union_sites) or
            len(set(observed_union_sites)) != len(observed_union_sites)):
        raise MigrationError('Observed union site IDs must be distinct strings')
    union_sites = set(observed_union_sites)
    if not union_sites <= {s['site_id'] for s in target_sites}:
        raise MigrationError('Observed union names an unknown or already explicit site')
    suggs_by_target: Dict[str, List[Dict[str, Any]]] = {s["site_id"]: [] for s in target_sites}

    for edit_idx, ed in enumerate(q_edits):
        if not isinstance(ed, dict):
            unresolved.append({"reason": "unrelated_suggestion", "details": f"Edit {edit_idx} is not an object", "edit_index": edit_idx})
            continue
        new_text = ed.get("newText")
        if not isinstance(new_text, str): raise MigrationError(f"Edit {edit_idx} newText must be a string")
        try: new_text.encode("utf-8")
        except UnicodeEncodeError as exc: raise MigrationError(f"Edit {edit_idx} newText has invalid Unicode: {exc}") from exc

        rng, ref_rng, cmd_rng = ed.get("range"), ed.get("referenceRange"), ed.get("commandRange")
        m_head = REPLACEMENT_HEAD_RE.match(new_text.lstrip())
        if not m_head:
            unresolved.append({"reason": "unrelated_suggestion", "details": f"Edit {edit_idx} newText does not begin with simp-family tactic", "edit_index": edit_idx})
            continue

        matching = [
            t for t in target_sites
            if t["family"] == m_head.group(1) and _json_equal(t["mapped_command_range"], cmd_rng)
            and _json_equal(t["mapped_range"], rng)
            and (_json_equal(ref_rng, t["mapped_head_range"]) or _json_equal(ref_rng, t["mapped_range"]))
        ]
        if not matching:
            unresolved.append({"reason": "unrelated_suggestion", "details": f"Edit at index {edit_idx} does not associate with any target site", "edit_index": edit_idx, "range": rng, "commandRange": cmd_rng})
            continue
        if not _has_explicit_only(new_text):
            unresolved.append({"reason": "incompatible_range", "site_id": matching[0]["site_id"], "details": f"Edit at index {edit_idx} replacement does not use explicit 'only': {new_text[:40]!r}", "edit_index": edit_idx})
            continue
        suggs_by_target[matching[0]["site_id"]].append(ed)

    resolved_edits, preview_edits_payload = [], []
    for t in target_sites:
        s_id, s_list = t["site_id"], suggs_by_target[t["site_id"]]
        if not s_list:
            unresolved.append({"reason": "missing_site", "site_id": s_id, "details": f"Target site {s_id} received 0 suggestions", "range": t["mapped_range"]})
            continue
        first_text, first_rng = s_list[0]["newText"], s_list[0]["range"]
        divergent = any(e["newText"] != first_text or e["range"] != first_rng for e in s_list)
        union_metadata = {}
        if divergent:
            if s_id not in union_sites:
                unresolved.append({"reason": "divergent_alternatives", "site_id": s_id, "details": f"Target site {s_id} received divergent suggestions", "alternatives": [e["newText"] for e in s_list]})
                continue
            first_text, union_names = _observed_union(t['family'], s_list)
            union_metadata = {
                'resolution': 'observed_per_site_union', 'used_lemma_union': union_names,
                'alternatives': [e['newText'] for e in s_list], 'replay_required': True,
            }
        elif s_id in union_sites:
            raise MigrationError('Observed union requested for a nondivergent site')
        attributions = [{"parentDeclaration": e.get("parentDeclaration"), "referenceRange": e.get("referenceRange"), "commandRange": e.get("commandRange")} for e in s_list]
        resolved_edits.append({"site_id": s_id, "range": first_rng, "newText": first_text, "original_range": t["original_range"], "mapped_range": t["mapped_range"], "attributions": attributions, "duplicate_count": len(s_list), **union_metadata})
        preview_edits_payload.append({"range": first_rng, "newText": first_text})

    is_complete = (len(unresolved) == 0)
    candidate_source, candidate_sha256, candidate_bytes, applied_count = None, None, None, 0

    if is_complete:
        try:
            prev_res: PreviewResult = preview(derived_res.instrumented_bytes, {"schema": 1, "source_sha256": derived_res.source_sha256, "edits": preview_edits_payload})
        except SimpEditError as exc:
            raise MigrationError(f"Preview applier failed: {exc}") from exc
        candidate_bytes, candidate_sha256 = prev_res.candidate_bytes, hashlib.sha256(prev_res.candidate_bytes).hexdigest()
        candidate_source, applied_count = prev_res.candidate_bytes.decode("utf-8"), prev_res.applied_edits

    return ReconcileResult({
        "complete": is_complete, "candidate_source": candidate_source, "candidate_sha256": candidate_sha256,
        "candidate_bytes": candidate_bytes, "applied_edits": applied_count,
        "resolved_count": len(resolved_edits), "unresolved_count": len(unresolved),
        "resolved": resolved_edits, "unresolved": unresolved,
        "original_sha256": derived_res.plan["original_sha256"], "source_sha256": derived_res.source_sha256,
    })


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Pure-Python two-stage simplification planner and reconciliation.")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    p_inst = subparsers.add_parser("instrument", help="Generate instrumented source and plan.")
    p_inst.add_argument("source", type=Path, help="Path to original Lean source file.")
    p_inst.add_argument("baseline", type=Path, help="Path to baseline collector JSON file.")

    p_rec = subparsers.add_parser("reconcile", help="Reconcile question collector edits into preview candidate.")
    p_rec.add_argument("source", type=Path, help="Path to original Lean source file.")
    p_rec.add_argument("plan", type=Path, help="Path to migration plan JSON file.")
    p_rec.add_argument("collector", type=Path, help="Path to question collector JSON file.")
    p_rec.add_argument('--observed-union', action='append', default=[], metavar='SITE_ID',
                       help='Propose a union of actual simple-name alternatives at this span; requires Lean replay.')

    args = parser.parse_args(argv if argv is not None else sys.argv[1:])

    try:
        if args.subcommand == "instrument":
            orig_bytes, base_bytes = args.source.read_bytes(), args.baseline.read_bytes()
            res = instrument(orig_bytes, base_bytes)
            print(json.dumps({
                "source_sha256": res.source_sha256, "original_sha256": res.plan["original_sha256"],
                "instrumented_source": res.instrumented_bytes.decode("utf-8"), "plan": res.plan,
            }, indent=2))
            return 0
        elif args.subcommand == "reconcile":
            orig_b, plan_b, col_b = args.source.read_bytes(), args.plan.read_bytes(), args.collector.read_bytes()
            res = reconcile(orig_b, plan_b, col_b, observed_union_sites=args.observed_union)
            print(json.dumps({k: v for k, v in res.items() if k != "candidate_bytes"}, indent=2))
            return 0 if res["complete"] else 1
    except MigrationError as exc:
        print(json.dumps({"error": str(exc)}, indent=2))
        return 1
    except OSError as exc:
        print(json.dumps({"error": f"File I/O error: {exc}"}, indent=2))
        return 2

    return 0


if __name__ == "__main__":
    sys.exit(main())
