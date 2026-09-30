#!/usr/bin/env python3
"""Hash-bound resolved-reference transport and immutable historical reconciliation.

No Lean elaboration, lexical name resolution, static script execution, published
count generation, or semantic value judgement occurs here. See interface-v1.md.
"""
from __future__ import annotations

import hashlib
from pathlib import Path

from module_path_policy import resolve_bound_file

SCHEMA = "blanc-resolved-usage-v1"
KINDS = {"term-reference", "rewrite-positive", "rewrite-remove", "checked-name",
         "checked-type", "checked-axioms", "macro-reference", "script-check"}


class UsageEvidenceError(ValueError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise UsageEvidenceError(message)


def _read(root: Path, path: str) -> bytes:
    try:
        return resolve_bound_file(root, path, allow_missing=False,
                                  site="usage-evidence-candidate-input").read_bytes()
    except (OSError, ValueError, RuntimeError) as error:
        raise UsageEvidenceError(f"unsafe/unreadable evidence input {path}: {error}") from error


def _span(value: object, size: int) -> tuple[int, int]:
    _require(isinstance(value, list) and len(value) == 2
             and all(type(x) is int for x in value), "invalid UTF-8 byte span")
    start, end = value
    _require(0 <= start < end <= size, "reference/command span outside captured source")
    return start, end


def declaration_index(rows: list[dict]) -> dict[str, dict]:
    _require(isinstance(rows, list) and bool(rows), "empty/malformed declaration identities")
    indexed = {}
    for row in rows:
        _require(isinstance(row, dict), "malformed declaration row")
        name = row.get("name")
        _require(isinstance(name, str) and bool(name) and name not in indexed,
                 "empty/duplicate kernel declaration identity")
        _require(all(isinstance(row.get(k), str) and row[k] for k in ("display_name", "module"))
                 and type(row.get("private")) is bool and type(row.get("theorem")) is bool
                 and row.get("kind") in {"theorem", "def", "opaque", "axiom", "constructor", "recursor", "inductive", "instance"},
                 f"malformed declaration metadata: {name}")
        _require("owner" in row and (row["owner"] is None or isinstance(row["owner"], str)),
                 f"missing declaration owner: {name}")
        indexed[name] = row
    for name, row in indexed.items():
        owner = row["owner"]
        _require(owner is None or owner in indexed, f"unknown canonical owner of {name}")
        if owner is not None:
            _require(indexed[owner]["owner"] == owner, f"noncanonical owner of {name}")
    return indexed


def validate_and_index(root: Path, receipt: dict, expected_sources: dict[str, str],
                       expected_bindings: dict[str, str], requests: list[dict] = ()) -> dict:
    """Reject incomplete/stale receipts and index theorem references by kernel owner.

    Expected inventories are authoritative inputs captured by the runtime launcher.
    Native controls must independently establish their parser/adapter completeness.
    """
    root = root.resolve(strict=True)
    _require(receipt.get("schema") == SCHEMA, "unsupported usage evidence schema")
    _require(bool(expected_sources) and bool(expected_bindings), "empty candidate inventories")
    _require(receipt.get("source_hashes") == expected_sources, "source coverage/hash mismatch")
    _require(receipt.get("bindings") == expected_bindings, "candidate setup/import binding mismatch")
    _require(receipt.get("errors") == [] and receipt.get("sorry") is False
             and receipt.get("unresolved") == [], "failed/sorry/unresolved usage evidence")
    raw = {}
    for path, digest in {**expected_bindings, **expected_sources}.items():
        _require(path not in expected_bindings or path not in expected_sources
                 or expected_bindings[path] == expected_sources[path], "conflicting input hashes")
        data = _read(root, path)
        _require(hashlib.sha256(data).hexdigest() == digest, f"stale candidate bytes: {path}")
        raw[path] = data
    declarations = declaration_index(receipt.get("declarations"))
    sources = receipt.get("sources")
    _require(isinstance(sources, list), "missing resolved source records")
    _require(len(sources) == len(expected_sources)
             and {r.get("path") for r in sources} == set(expected_sources),
             "incomplete/duplicate resolved source coverage")
    uses: dict[str, list[dict]] = {}
    for source in sources:
        path = source["path"]
        commands = source.get("commands")
        _require(isinstance(commands, list) and bool(commands), f"missing parsed commands: {path}")
        command_index = {}
        for command in commands:
            cid = command.get("id")
            _require(isinstance(cid, str) and cid and cid not in command_index,
                     f"invalid/duplicate command identity: {path}")
            start, end = _span(command.get("span"), len(raw[path]))
            _require(command.get("mode") in {"elaborated", "reference-adapter"},
                     f"unresolved command execution role: {path}:{cid}")
            if command["mode"] == "reference-adapter":
                adapter = command.get("adapter")
                _require(isinstance(adapter, str) and adapter in expected_bindings,
                         f"unbound command adapter: {path}:{cid}")
            command_index[cid] = (start, end)
        references = source.get("references")
        _require(isinstance(references, list), f"missing reference collection: {path}")
        for reference in references:
            cid, target = reference.get("command"), reference.get("resolved_name")
            _require(cid in command_index and target in declarations,
                     f"unknown command/resolved declaration: {path}")
            start, end = _span(reference.get("span"), len(raw[path]))
            lo, hi = command_index[cid]
            _require(lo <= start < end <= hi, f"reference outside owner command: {path}")
            _require(reference.get("kind") in KINDS, f"unknown reference kind: {path}")
            _require("parent" in reference, f"missing explicit parent attribution: {path}")
            parent = reference["parent"]
            _require(parent is None or parent in declarations, f"unknown parent identity: {path}")
            owner = declarations[target]["owner"]
            if owner is not None and declarations[owner]["theorem"]:
                if parent is None or declarations[parent]["owner"] != owner:
                    uses.setdefault(owner, []).append({"path": path, **reference})
    request_index = {r["id"]: r for r in requests}
    _require(len(request_index) == len(requests), "duplicate static consumer request ID")
    responses = receipt.get("static_resolutions")
    _require(isinstance(responses, list) and len(responses) == len(request_index)
             and {r.get("id") for r in responses} == set(request_index),
             "unanswered/duplicate static consumer requests")
    for response in responses:
        request = request_index[response["id"]]
        _require(request["path"] in expected_bindings
                 and request["source_sha256"] == expected_bindings[request["path"]]
                 and request["target_source"] in expected_sources,
                 "unbound static consumer source/context")
        target = response.get("resolved_name")
        _require(target in declarations and response.get("requested_name") == request["name"]
                 and response.get("target_source") == request["target_source"],
                 "unresolved/mismatched static consumer")
        owner = declarations[target]["owner"]
        if owner is not None and declarations[owner]["theorem"]:
            uses.setdefault(owner, []).append({"kind": request["kind"], **request,
                                              "resolved_name": target})
    return {"declarations": declarations, "uses": uses}


def reconcile_historical(original_keys: list[str], aliases: dict[str, dict],
                         declarations: dict[str, dict], used: set[str]) -> list[dict]:
    """Keep every historical row, including distinct spellings of one declaration."""
    _require(len(set(original_keys)) == len(original_keys), "duplicate original historical row")
    _require(set(aliases) == set(original_keys), "missing/extra historical identity accounting")
    current = [r for r in declarations.values() if r["theorem"] and r["owner"] == r["name"]]
    rows = []
    for key in original_keys:
        old = aliases[key]
        exact = declarations.get(old["name"])
        matches = [exact] if exact is not None else [r for r in current if
            (r["display_name"], r["module"], r["private"]) ==
            (old["display_name"], old["module"], old["private"])]
        _require(len(matches) <= 1, f"ambiguous current historical identity: {key}")
        if matches:
            actual = matches[0]["name"]
            _require(matches[0]["theorem"] and matches[0]["owner"] == actual,
                     f"historical theorem changed declaration kind: {key}")
            rows.append({"original": key, "historical_name": old["name"],
                         "current_name": actual, "status": "used" if actual in used else "unused"})
        else:
            rows.append({"original": key, "historical_name": old["name"],
                         "current_name": None, "status": "absent"})
    return rows
